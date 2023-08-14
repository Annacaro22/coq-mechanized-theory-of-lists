From Coq Require Import Lia.
From Coq Require Import Strings.Ascii.


(*SECTION 0: HELPER NAT FUNCTIONS AND NAT LEMMAS*)


Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

  Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Definition neq (n m : nat) : bool :=
  if n =? m then false else true.

Lemma plus1_Succ_Equal : forall (n : nat),
n + 1 = S n.
Proof. intros n. induction n.
  -simpl. reflexivity.
  -simpl. rewrite IHn. reflexivity. Qed.

  Fixpoint leb (n m : nat) : bool :=
    match n with
    | O => true
    | S n' =>
        match m with
        | O => false
        | S m' => leb n' m'
        end
    end.
  
  Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
  
  Lemma leq_transitive : forall (a b c : nat),
  (a <= b) -> (b <= c) -> (a <= c).
  Proof.
    intros a b c H1 H2.
    lia. Qed.
  

  Fixpoint plus (n : nat) (m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.


  Fixpoint mult (n m : nat) : nat :=
    match n with
    | O => O
    | S n' => plus m (mult n' m)
    end.


  Fixpoint minus (n m:nat) : nat :=
    match n, m with
    | O   , _    => O
    | S _ , O    => n
    | S n', S m' => minus n' m'
    end.
    


Definition smaller (n m : nat) : nat :=
  match leb n m with
  |true => n
  |false => m
  end.

  
Definition bigger (n m : nat) : nat :=
  match leb n m with
  |true => m
  |false => n
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.


(*SECTION 0.5 : HELPER FUNCTIONS FOR FUNCTIONS AND LEMMAS ABOUT FUNCTIONS*)

(*all functions that are involutions are also injective*)
Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
  intros f n n1 n2 H.
  rewrite n. rewrite <- H. rewrite <- n. reflexivity. Qed.


(*function composition definition and notation*)
Definition compose {A B C} (g : B -> C) (f : A -> B) :=
    fun x : A => g (f x).


Lemma compose_notation: forall {A B C: Type} (g : B -> C) (f : A -> B) (x : A),
compose g f x = g (f x).
Proof.
  intros A B C g f x. reflexivity. Qed.



(*a definition for what it means for two functions to be inverses of each other*)
Definition inverses {X Y: Type} (f: X -> Y) (g: Y -> X) : Prop :=
forall (a: X) (b : Y), (f a = b) <-> (g b = a).

(*a type class for invertible elements*)
Class invertible {X Y : Type} (f : X -> Y) :=
  { g : Y -> X ;
    f_g_inverse : inverses f g
  }.

(*test of the invertible class*)
Goal forall {X Y : Type} (f : X -> Y) `{invertible X Y f}, 
  exists g, inverses f g.
Proof.
  intros. exists g. apply f_g_inverse. Qed.

(*if f is invertible, than f and its inverses undo each other*)
Theorem invertible_undo: forall {X Y : Type} (f : X -> Y) `{invertible X Y f},
(((forall (a : X), g (f a) = a) /\ (forall (b : Y), f (g b) = b) )).
Proof.
  intros X Y f H.
  split.
  -intros a. apply f_g_inverse. reflexivity.
  -intros b. apply f_g_inverse. reflexivity. Qed.

(*If f and g are inverses, then f and g undo each other; g f x = x and f g y = y*)
Theorem inverses_undo: forall (X Y: Type) (f: X -> Y) (g: Y -> X),
((inverses f g) -> ((forall (a : X), g (f a) = a) /\ (forall (b : Y), f (g b) = b) )).
Proof.
  intros X Y f g. intros H.
  split.
  -intros a. apply H. reflexivity.
  -intros b. apply H. reflexivity. Qed.


Definition associative {X : Type} (f : X -> X -> X) : Prop :=
    forall (a b c : X), f a (f b c) = f (f a b) c.

Definition injective {X Y : Type} (f : X -> Y) : Prop :=
 forall (x x' : X), f(x) = f(x') <-> x = x'.


Theorem inverses_undo_backwards: forall (X Y: Type) (f: X -> Y) (g: Y -> X),
(((forall (a : X), g (f a) = a) /\ (forall (b : Y), f (g b) = b) )) -> (inverses f g).
Proof.
  intros X Y f g. intros H.
  destruct H.
  unfold inverses. intros a b.
  split.
  -intros H2. rewrite <- H. f_equal. rewrite H2. reflexivity.
  -intros H2. rewrite <- H0. f_equal. rewrite H2. reflexivity. Qed.


(*SECTION 1: LIST DEFINITION AND BASIC LIST FUNCTIONS: APPEND, REVERSE, LENGTH*)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X}.


(*Definitions: append, reverse, length:*)

  Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.
  

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).


(*custom tactic to break down a list and get rid of any
cases that are immediately solvable, usually the base case*)
Ltac simples l := induction l; simpl; try reflexivity.


(*custom tactic to destruct an inductive, usually an NElist,
generalize the first element, and then do induction on the
remaining inductive, usually a list*)
Ltac geninduction l := destruct l as [a l']; generalize dependent a; induction l'.

            

(*[] is the identity of append:*)
Theorem app_nil_r : forall (X:Type), forall l:list X,
 l ++ [] = l.
 Proof.
 intros X l. simples l. rewrite IHl. reflexivity. Qed.

Theorem app_nil_l : forall (X:Type), forall l:list X,
 [] ++ l = l.
 Proof.
  intros X l. simpl. reflexivity. Qed.


(*append is associative:*)
Theorem app_assoc : forall A (l m n:list A),
 l ++ m ++ n = (l ++ m) ++ n.
 Proof.
  intros A l m n. simples l. rewrite IHl. reflexivity. Qed.

(*append and length are distributive*)   
Lemma app_length : forall (X:Type) (l1 l2 : list X),
length (l1 ++ l2) = length l1 + length l2.
Proof.
 intros X l1 l2. simples l1. rewrite IHl1. reflexivity. Qed.

(*cons and append are associative*)
 Theorem cons_app_assoc : forall {A : Type} (a : A) (l1 l2 : list A),
 a :: l1 ++ l2 = a :: (l1 ++ l2).
 Proof.
   intros A a l1 l2.
   reflexivity. Qed.

(*append and reverse are distributive*)
Theorem rev_app_distr: forall X (l1 l2 : list X),
 rev (l1 ++ l2) = rev l2 ++ rev l1.
  Proof.
  intros X l1 l2. simples l1.
  -rewrite app_nil_r. reflexivity.
  -rewrite IHl1. simpl. rewrite app_assoc. reflexivity. Qed.
                   
(*reverse is involutive*)
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
  Proof.
  intros X l. simples l. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity. Qed.

Theorem rev_length : forall {X : Type} (l : list X),
length (rev l) = length l.
Proof.
  intros X l.
  induction l.
  -simpl. reflexivity.
  -simpl. rewrite app_length. rewrite IHl. simpl.
  destruct (length l).
    +simpl. reflexivity.
    +simpl. f_equal. rewrite plus1_Succ_Equal. reflexivity. Qed.

Theorem rev_injective : forall {X : Type} (l1 l2 : list X),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H.
  rewrite <- rev_involutive. rewrite <- H. rewrite rev_involutive. reflexivity. Qed.



(*SECTION 2-- MORE BASIC LIST FUNTIONS. MAP, FILTER, FOLD.*)


(*Definition: map*)
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.


Theorem map_id_is_id: forall {X : Type} (l : list X),
map id l = id l.
Proof.
  intros X l.
  simples l. rewrite IHl. unfold id. reflexivity. Qed.


(*map and append are distributive*)
Theorem map_f_app_dist: forall {X Y : Type} (f : X -> Y) (a b : list X),
map f (a ++ b) = map f(a) ++ map f(b).
Proof.
  intros X Y f a b.
  simples a. rewrite IHa. reflexivity. Qed.

(*map and function composition are distributive*)
Theorem map_func_comp_dist: forall (X Y Z: Type) (f : X -> Y) (g : Z -> X) (a : list Z),
map (compose f g) a = map (f) (map g a).
Proof.
  intros X Y Z f g a.
  simples a. rewrite IHa. reflexivity. Qed.

(*if function application is commutative for two functions f and g, then
mapping f and g onto lists is also commutative*)
Theorem map_funcs_backwards : forall (X: Type) (f : X -> X) (g : X -> X) (l : list X),
(forall (x : X), f (g x) = g (f x)) -> map f (map g l) = map g (map f l).
Proof.
  intros X f g l H.
  simples l. rewrite IHl. f_equal. apply H. Qed.


(*If map of any function on a list yields empty list, then the original list should be empty list*)
Theorem map_output_nil: forall (X Y: Type) (f : X->Y) (l : list X),
(map f l = []) -> (l = []).
Proof.
  intros X Y f l.
  simples l. intros H. inversion H. Qed.

(*If f and g are inverses, then map f and map g undo each other; map g (map f x) = x and map f (map g y) = y*)
Theorem map_inverses_undo: forall (X Y: Type) (f : X -> Y) (g : Y -> X) (l1 : list X) (l2 : list Y),
((inverses f g) -> ((forall (l1 : list X), map g (map f l1) = l1) /\ (forall (l2 : list Y), map f (map g l2) = l2) )).
Proof.
  intros X Y f g. intros listy1 listy2 H.
  apply inverses_undo in H as H2.
  destruct H2.
  split.
  -intros l1. simples l1. rewrite IHl1. rewrite H0. reflexivity.
  -intros l2. simples l2. rewrite IHl2. rewrite H1. reflexivity. Qed. 


(*map and taking the inverse are commutative; inverse (map f) is
equal to map (inverse f). Here, this is represented as 
(assume f and g are inverses), map f is inverses with map g,
so if map f x = y, then map g y = x*)
Theorem map_inverse_comm: forall (X Y: Type) (f : X -> Y) (g : Y -> X) (l1 : list X) (l2 : list Y),
((inverses f g) -> ( (map f l1 = l2) <-> (map g l2 = l1))).
Proof.
  intros X Y f g l1 l2 H.
  apply map_inverses_undo in H as H2. destruct H2.
  split.
  -intros Left. rewrite <- Left. apply H0.
  -intros Left. rewrite <- Left. apply H1.
  -apply l1.
  -apply l2. Qed.


(*map is revolutive*)
Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  simples l.  rewrite <- IHl. rewrite map_f_app_dist. simpl. reflexivity. Qed.






(*Definition: filter*)
  Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.


(*filter and append are distrubutive*)
Theorem filter_f_app_dist: forall (X : Type) (f : X -> bool) (a b : list X),
filter f (a ++ b) = filter f(a) ++ filter f(b).
Proof.
  intros X f a b.
  induction a.
  -simpl. reflexivity.
  -simpl. destruct (f x).
    +simpl. rewrite IHa. reflexivity.
    +rewrite IHa. reflexivity. Qed.


(*filter is commutative*)
Theorem filter_comm: forall {X: Type} (f: X -> bool) (g: X -> bool) (a : list X),
filter f (filter g a) = filter g (filter f a).
Proof.
  intros X f g a.
  induction a.
  -simpl. reflexivity.
  -simpl. destruct (g x) eqn:Eg.
    +simpl. destruct (f x) eqn: Ef.
      *simpl. rewrite Eg. rewrite IHa. reflexivity.
      *rewrite IHa. reflexivity.
    +destruct (f x) eqn: Ef.
      *simpl. rewrite Eg. rewrite IHa. reflexivity.
      *rewrite IHa. reflexivity. Qed.


(*filter is idempotent*)
Theorem filter_idempotent: forall {X: Type} (f: X -> bool) (a: list X),
filter f (filter f a) = filter f a.
Proof.
  intros X f a.
  induction a.
  -simpl. reflexivity.
  -simpl. destruct (f x) eqn:Ef.
    +simpl. rewrite Ef. rewrite IHa. reflexivity.
    +rewrite IHa. reflexivity. Qed.


(*filter and map are commutative*)
Theorem filter_map_comm: forall {X Y: Type} (p: Y -> bool) (f: X -> Y) (x : list X),
filter p (map f x) = map f (filter (compose p f) x).
Proof.
  intros X Y p f x.
  induction x.
  -simpl. reflexivity.
  -simpl. destruct (p (f x)) eqn:Epf.
    +rewrite compose_notation. rewrite Epf. simpl. rewrite IHx. reflexivity.
    +rewrite compose_notation. rewrite Epf. rewrite IHx. reflexivity. Qed.


(*a filtered list must have equal or smaller size than the original
unfiltered list*)
Theorem filter_size_decrease : forall {X : Type} (p : X -> bool) (l : list X),
length (filter p l) <= length l.
Proof.
  intros X p l.
  induction l.
  -simpl. lia.
  -simpl. destruct (p x).
    +simpl. lia.
    +simpl. lia. Qed. 





(*Definition: fold right*)
Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y): Y :=
match l with
| nil => b
| h :: t => f h (fold f t b)
end.

(*fold and append are distributive*)
Theorem fold_app_dist: forall (X Y: Type) (f : X -> Y -> Y) (x y : list X) (b : Y),
fold f (x ++ y) b = fold f x (fold  f y b).
Proof.
  intros X Y f x y b.
  induction x.
    -simpl. reflexivity.
    -simpl. f_equal. apply IHx. Qed.


(*common list functions using fold*)
Definition listsum (l : list nat) :=
  fold plus l 0.

Definition listproduct (l : list nat) :=
  fold mult l 1.

Definition listflatten {X: Type} (l : list (list X)) :=
  fold app l [].

Definition listallp {X: Type} (p : X -> bool) (l: list X) :=
  fold andb (map p l) true.

Definition listsomep {X: Type} (p : X -> bool) (l: list X) :=
  fold orb (map p l) false.

(*fold left*)
Fixpoint foldL {X Y: Type} (f : Y->X->Y) (b : Y) (l : list X): Y :=
  match l with
  | nil => b
  | h :: t => (foldL f (f b h) t)
  end.



Theorem foldL_lemma: forall {X: Type} (f : X -> X -> X) (l : list X) (x y : X),
(associative f) -> foldL f (f y x) l = f y (foldL f x l).
Proof.
  intros X f l x y assoc.
  generalize dependent x.
  induction l.
    -simpl. reflexivity.
    -simpl. intros x0. rewrite <- IHl. f_equal. rewrite assoc. reflexivity. Qed.

Theorem foldL_lemma2: forall {X : Type} (f: X -> X -> X) (l: list X) (a a0 x : X),
(associative f) -> f a (foldL f x (l ++ [a0])) = f (f a (foldL f x l)) a0.
Proof.
  intros X f l a a0 x assoc.
  generalize dependent x.
  induction l.
    -simpl. intros x. apply assoc.
    -simpl. intros x0. rewrite <- IHl. reflexivity. Qed.

Theorem foldL_lemma3: forall {X : Type} (f: X -> X -> X) (l lnew: list X) (a a0 x xnew : X),
(associative f) -> f a (foldL f x (l ++ a0 :: xnew :: lnew)) = f (f a (foldL f x l)) (f a0 (foldL f xnew lnew)).
Proof.
  intros X f l lnew a a0 x xnew assoc.
  generalize dependent x.
  generalize dependent xnew.
  induction l.
    -simpl. intros x xnew. rewrite <- foldL_lemma.
      +rewrite <- foldL_lemma.
        *rewrite <- foldL_lemma.
          --f_equal. rewrite assoc. rewrite assoc. rewrite assoc. reflexivity.
          --apply assoc.
        *apply assoc.
      +apply assoc.
    -simpl. intros xnew x0. rewrite IHl. reflexivity. Qed.



(*if f is associative and commutative, then foldL and foldR are equivalent*)
Theorem foldL_foldR_assoc_comm :
forall {X : Type} (f : X -> X -> X) `{associative f} (l : list X) (b : X),
(forall x y : X, f x y = f y x) -> fold f l b = foldL f b l.
Proof.
  intros X f assoc l b H.
  induction l.
    -simpl. reflexivity.
    -simpl. assert (H2 : foldL f (f b x) l = foldL f (f x b) l).
      +rewrite H. reflexivity.
      +rewrite H2. rewrite foldL_lemma.
        *rewrite IHl. reflexivity.
        *apply assoc. Qed.



(*SECTION 3 -- OTHER LIST FUNCTIONS*)

(*a function which takes two lists and creates a new list that alternates
their elements*)
Fixpoint alternate {X : Type} (l1 l2 : list X) : list X :=
    match l1 with
      |[] => l2
      |h :: t => match l2 with
                  |[] => l1
                  |h2 :: t2 => h :: h2 :: (alternate t t2)
                  end
    end.


(*flat map definition-- a map that takes a function which outputs a list.
after applying this function to every element of the given list as in a regular map
function, this function then conjoins the elements so that a list is returned
rather than a list of lists.*)
Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
: list Y :=
match l with
| [] => []
| h :: t => (f h) ++ (flat_map f t)
end.

Definition nearest_multiples_of_two (n : nat) : list nat :=
  [n*2; n*4].

Example flat_map_ex : flat_map nearest_multiples_of_two [1;3;5] = [2;4;6;12;10;20].
Proof. simpl. reflexivity. Qed.


(*ap: taking a list of functions and a list of values and
applying one function to one value each piecewise*)
Fixpoint ap {X: Type} (lf : list (X -> X)) (l : list X) : list X :=
  match l with
  | [] => []
  | h :: t => match lf with
              |[] => l
              |hf :: tf => [hf h] ++ ap tf t
              end
  end.

Definition add1 (n : nat) := n + 1.
Definition add3 (n : nat) := n + 3.

Example testap: ap [add1; add3] [0; 2] = [1; 5].
    Proof. simpl. unfold add1. unfold add3. simpl. reflexivity.  Qed.

Example testap_uneven: ap [add1] [0;2] = [1;2].
Proof. simpl. unfold add1. simpl. reflexivity. Qed.


(*like ap, but now every function is applied on every element,
like a cross product*)
Fixpoint zap {X: Type} (lf : list (X -> X)) (l : list X) : list X :=
match lf with
|[] => []
|hf :: tf => map hf l ++ zap tf l
end.

Example testzap: zap [add1; add3] [0; 2] = [1;3;3;5].
Proof. simpl. unfold add1. unfold add3. simpl. reflexivity. Qed.

Example testzap2 : zap [add1] [0;2] = [1;3].
Proof. simpl. unfold add1. simpl. reflexivity. Qed.

(*if zap is performed with a singleton list of functions, then it is
equivalent to using map on that one function*)
Theorem singleton_zap_is_map : forall {X : Type} (f : X -> X) (l : list X),
zap [f] l = map f l.
Proof.
  intros X f l.
  simples l.
  rewrite app_nil_r. reflexivity. Qed.





(*SECTION 4 -- NELIST DEFINITION AND COMMON FUNCTIONS: APPEND, REVERSE, LENGTH*)

(*definition of NElists, nonempty lists*)
Inductive NElist (A: Type) : Type :=
  |NEcons (a : A) (l: list A).

  Arguments NEcons {A}.

(*converting from NElists to lists*)
Definition NElist_to_list {X : Type} (ne : NElist X):=
    match ne with
    | NEcons h t => h :: t
    end.

(*returns the head of an NElist*)
Definition headNE {X : Type} (l : NElist X) :=
  match l with
  NEcons h t => h
  end.

(*returns the tail of an NElist*)
Definition tailNE {X : Type} (l : NElist X) :=
  match l with
  NEcons h t => t
  end.

(*append for NElists*)
  Definition appNE {X : Type} (l1 l2 : NElist X) : NElist X :=
  match l1 with
  | NEcons h t => NEcons h (t ++ (NElist_to_list l2))
  end.

  Example appNE_test1: appNE (NEcons 1 [2; 3]) (NEcons 4 [5;6]) = NEcons 1 [2; 3; 4; 5; 6].
  Proof. simpl. reflexivity. Qed.

  Example appNE_test2: appNE (NEcons 1 []) (NEcons 4 [5;6]) = NEcons 1 [4; 5; 6].
  Proof. simpl. reflexivity. Qed.

  Example appNE_test3: appNE (NEcons 1 [2; 3]) (NEcons 4 []) = NEcons 1 [2;3;4].
  Proof. simpl. reflexivity. Qed.

  Example appNE_test4: appNE (NEcons 1 []) (NEcons 4 []) = NEcons 1 [4].
  Proof. simpl. reflexivity. Qed.


(*Proving the conversion between lists and NElists 
by showing that NEcons is equivalent to normal list cons*)
Lemma represent_NEcons : forall {X : Type} (a x : X) (l : list X),
NEcons a (x :: l) = appNE (NEcons a []) (NEcons x l).
Proof.
  intros X a x l.
  simpl.
  induction l.
    -reflexivity.
    - reflexivity. Qed.


(*'Mixapps' -- append functions that take a list and an NElist, or vice versa, and
appends them, returning in NElist form.*)

  Definition Mixapp1 {X : Type} (l1 : list X) (l2 : NElist X) : NElist X :=
  match l1 with
  | []     => l2
  | h :: t => match l2 with
                          |NEcons hi ti => NEcons h (app (t) (hi :: ti))
                          end
  end.  


  Definition Mixapp2 {X : Type} (l1 : NElist X) (l2 : list X) : NElist X :=
  match l1 with
  | NEcons h t=> match l2 with
                          |[] => l1
                          |hi :: ti => NEcons h (app t (hi :: ti))
                          end
  end.  

  Definition Mixapp2' {X : Type} (l1 : NElist X) (l2 : list X) : NElist X :=
  match l1 with
  | NEcons h nil      => NEcons h l2
  | NEcons h (h2 :: t) => match l2 with
                          |[] => l1
                          |hi :: ti => NEcons h (app (h2 :: t) (hi :: ti))
                          end
  end.  

  Example Mixapp1_test1: Mixapp1 ([1; 2; 3]) (NEcons 4 [5;6]) = NEcons 1 [2; 3; 4; 5; 6].
  Proof. simpl. reflexivity. Qed.

  Example Mixapp1_test2: Mixapp1 ([1]) (NEcons 4 [5;6]) = NEcons 1 [4; 5; 6].
  Proof. simpl. reflexivity. Qed.

  Example Mixapp1_test3: Mixapp1 ([1; 2; 3]) (NEcons 4 []) = NEcons 1 [2;3;4].
  Proof. simpl. reflexivity. Qed.

  Example Mixapp1_test4: Mixapp1 ([1]) (NEcons 4 []) = NEcons 1 [4].
  Proof. simpl. reflexivity. Qed.

  Example Mixapp1_test5: Mixapp1 ([]) (NEcons 4 []) = NEcons 4 [].
  Proof. simpl. reflexivity. Qed.

  Example Mixapp2_test4: Mixapp2 (NEcons 1 []) ([4]) = NEcons 1 [4].
  Proof. simpl. reflexivity. Qed.

  Example Mixapp2_test5: Mixapp2 (NEcons 4 []) ([]) = NEcons 4 [].
  Proof. simpl. reflexivity. Qed.

(*reverse for NElists*)
Definition revNE {X:Type} (l:NElist X) : NElist X :=
  match l with
  | NEcons h (t) => Mixapp1 (rev (t)) (NEcons h nil)
  end.

  Example revNE_test1: revNE (NEcons 1 [2;3]) = NEcons 3 [2; 1].
  Proof. simpl. reflexivity. Qed.

  Example revNE_test2: revNE (NEcons 1 []) = NEcons 1 [].
  Proof. simpl. reflexivity. Qed.

(*length for NElists*)
Definition lengthNE {X : Type} (l : NElist X) : nat :=
  match l with
  | NEcons _ nil => 1
  | NEcons _ l' => S (length l')
  end.



(*SECTION 4.5 -- NELIST COMMON FUNCTION THEOREMS*)

(*NElist append is associative*)
  Theorem appNE_assoc : forall {A : Type} (l m n:NElist A),
  appNE l (appNE m n) = appNE (appNE l m) n.
  Proof.
    intros A l m n. destruct l. destruct m. destruct n. simpl.
    rewrite <- app_assoc. reflexivity. Qed.
    
 (*NElist append and length are distributive*)   
 Lemma appNE_length : forall (X:Type) (l1 l2 : NElist X),
 lengthNE (appNE l1 l2) = lengthNE l1 + lengthNE l2.
 Proof.
  intros X l1 l2. destruct l1. destruct l2.
  destruct l.
  -simpl. destruct l0.
    +simpl. reflexivity.
    +reflexivity.
  -simpl. destruct l0.
    +simpl. f_equal. f_equal. rewrite app_length. simpl. reflexivity.
    +simpl. f_equal. f_equal. rewrite app_length. simpl. reflexivity. Qed.
    
    
(*proving an equivalence of appNE and Mixapp1*)
Lemma appNE_Mixapp1_eq: forall (X : Type) (l1 l2 : NElist X) (l : list X),
(NElist_to_list l1 = l) -> (Mixapp1 l l2 = appNE l1 l2).
Proof.
  intros X l1 l2 l. intros H. destruct l1. destruct l2.
  simpl in H.
  destruct l0.
  -rewrite <- H. simpl. reflexivity.
  -rewrite <- H. simpl. reflexivity. Qed.

Lemma appNE_Mixapp1_eq': forall (X : Type) (l1 l2 : NElist X),
(Mixapp1 (NElist_to_list l1) l2 = appNE l1 l2).
Proof.
  intros X l1 l2. destruct l1. destruct l2.
  destruct l0.
  -simpl. reflexivity.
  - simpl. reflexivity. Qed.

(*proving an equivalence of regular list append and Mixapp1*)
Lemma app_Mixapp1_eq: forall (X : Type) (l1 : list X) (l : NElist X),
(NElist_to_list (Mixapp1 l1 l) = l1 ++ NElist_to_list l).
Proof.
  intros X l1 l. destruct l.
  simpl. destruct l.
  -induction l1.
    +simpl. reflexivity.
    +simpl. rewrite <- IHl1. reflexivity. 
  -induction l1.
    +simpl. reflexivity.
    +simpl. reflexivity. Qed.
    
    
(*proving an equivalence of regular list reverse and appand with NElist reverse and append*)
Lemma rev_appNE_app: forall {X : Type} (l : list X) (a : X),
(rev(l ++ [a]) = NElist_to_list (NEcons a (rev l))).
Proof.
  intros X l a.
  induction l.
    -simpl. reflexivity.
    -simpl. rewrite IHl. simpl. reflexivity. Qed.


(*helper for revNE_appNE_distr*)
Lemma revNE_appNE_pullFirstOut_nil: forall {X : Type} (a : X) (l2 : NElist X), 
revNE (appNE (NEcons a []) l2) = appNE (revNE l2) (NEcons a []).
Proof.
  intros X a l2.
  destruct l2.
  induction l.
    -simpl. reflexivity.
    -simpl. rewrite <- app_assoc. apply appNE_Mixapp1_eq.
    rewrite app_assoc.
    apply app_Mixapp1_eq. Qed.
  
(*helper for revNE_appNE_distr*)
Lemma revNE_appNE_pullFirstOut: forall {X : Type} (a x : X) (l: list X) (l2 : NElist X), 
revNE (appNE (NEcons a (x :: l)) l2) = appNE (revNE (appNE (NEcons x l) l2)) (NEcons a []).
Proof.
  intros X a x l l2.
  rewrite represent_NEcons. rewrite <- appNE_assoc.
  rewrite revNE_appNE_pullFirstOut_nil. reflexivity. Qed.

(*NElist reverse and NElist append are distributive*)
 Theorem revNE_appNE_distr: forall X (l1 l2 : NElist X),
  revNE (appNE l1 l2) = appNE (revNE l2) (revNE l1).
   Proof.
    intros X l1 l2.
    destruct l1.
    generalize dependent a.
    induction l.
      - intros a. rewrite revNE_appNE_pullFirstOut_nil. reflexivity.
      - intros a. rewrite revNE_appNE_pullFirstOut.
      rewrite IHl.
      rewrite represent_NEcons. rewrite revNE_appNE_pullFirstOut_nil.
      rewrite appNE_assoc. reflexivity. Qed.

(*revNEerse of a singleton list is itself*)
Lemma revNE_singleton : forall {X : Type} (a : X),
revNE (NEcons a []) = NEcons a [].
Proof.
  intros X a.
  simpl. reflexivity. Qed.

(*revNEerse is involutive*)
 Theorem revNE_involutive : forall X : Type, forall l : NElist X,
   revNE (revNE l) = l.
   Proof.
   intros X l. destruct l.
   generalize dependent a.
   induction l.
   -reflexivity.
   -intros a. rewrite represent_NEcons.
   rewrite revNE_appNE_distr. rewrite revNE_appNE_distr.
   rewrite IHl. rewrite revNE_singleton. rewrite revNE_singleton.
   reflexivity. Qed.



(*SECTION 5 -- MORE COMMON NELIST FUNCTIONS : MAP, FILTER, REDUCE*)

(*map for NElists*)
Definition mapNE {X Y : Type} (f : X->Y) (l : NElist X) : NElist Y :=
  match l with
  | NEcons h []     => NEcons (f h) []
  | NEcons h (h2 :: t) => NEcons (f h) (map f (h2 :: t))
  end.

(*helper for mapNE_appNE_dist*)
Lemma mapNE_base : forall {X Y : Type} (f : X->Y) (a : X),
mapNE f (NEcons a [ ]) = NEcons (f a) [].
Proof.
  intros X Y f a.
  simpl. reflexivity. Qed.

(*helper for mapNE_appNE_dist*)
Lemma mapNE_appNE_help : forall {X Y : Type} (f : X->Y) (l2 : NElist X) (a : X),
mapNE f (appNE (NEcons a [ ]) l2) =
appNE (mapNE f (NEcons a [ ])) (mapNE f l2).
intros X Y f l2 a. rewrite mapNE_base. destruct l2 as [a0 l0]. rewrite <- represent_NEcons.
induction l0.
  +simpl. reflexivity.
  +simpl. reflexivity. Qed.

(*map and append for NElists distribute*)
Theorem mapNE_appNE_dist : forall {X Y : Type} (f : X->Y) (l1 l2 : NElist X),
mapNE f (appNE l1 l2) = appNE (mapNE f l1) (mapNE f l2).
Proof.
  intros X Y f l1 l2.
  destruct l1. generalize dependent a. induction l.
  -intros a. rewrite mapNE_appNE_help. reflexivity.
  -intros a. rewrite represent_NEcons.
  rewrite <- appNE_assoc. rewrite mapNE_appNE_help.
  rewrite mapNE_base.
  rewrite IHl. rewrite appNE_assoc.
  f_equal.
  rewrite mapNE_appNE_help. rewrite mapNE_base. reflexivity. Qed.


(*filter for NElists. note-- this function has to output a list. it can't necessarily
output an NElist-- even if the inputs are all NElists, it's possible that test 
fails on all of them, in which case the empty list should be returned.*)
Definition filterNE {X:Type} (test: X->bool) (l:NElist X) : list X :=
match l with
| NEcons h [] => if test h then [h] else []
| NEcons h (h2 :: t) =>
if test h then h :: (filter test (h2 :: t))
else filter test (h2 :: t)
end.

Definition is_over_2 (n : nat) := if (3 <=? n) then true else false.
Definition is_over_99 (n : nat) := if (100 <=? n) then true else false.

Example test_filterNE1 : filterNE is_over_2 (NEcons 1 [2;3;4]) = [3;4].
Proof. simpl. reflexivity. Qed.

Example test_filterNE2 : filterNE is_over_99 (NEcons 1 [2;3;4]) = [].
Proof. simpl. reflexivity. Qed.


(*helper for filterNE_append_dist*)
Theorem filterNE_append_dist_singleton: forall {X:Type} (p : X-> bool) (a : X) (l2 : NElist X),
filterNE p (appNE (NEcons a []) l2) =  app (filterNE p (NEcons a [])) (filterNE p l2).
Proof.
  intros X p a l2.
  destruct l2. generalize dependent a0. induction l.
  -intros a0. simpl. destruct (p a) eqn:Epa.
    +destruct (p a0).
      *reflexivity.
      *simpl. reflexivity.
    +destruct (p a0).
      *reflexivity.
      *simpl. reflexivity.
  -intros a0. destruct (p a) eqn:Epa.
    +simpl. rewrite Epa. reflexivity.
    +simpl. rewrite Epa. reflexivity. Qed.

(*filter for NElists and append for lists distribute*)
Theorem filterNE_append_dist: forall {X:Type} (p : X-> bool) (l1 l2 : NElist X),
filterNE p (appNE l1 l2) =  app (filterNE p l1) (filterNE p l2).
Proof.
  intros X p l1 l2.
  destruct l1. destruct l2.
  generalize dependent a.
  induction l.
    -intros a. rewrite filterNE_append_dist_singleton. reflexivity.
    -intros a. rewrite represent_NEcons. rewrite <- appNE_assoc.
    rewrite filterNE_append_dist_singleton. rewrite filterNE_append_dist_singleton.
    rewrite IHl. rewrite app_assoc. reflexivity. Qed.


(*fold for NElists-- fold right*)
Definition foldNE {X Y: Type} (f : X->Y->Y) (l : NElist X) (b : Y): Y :=
match l with
| NEcons h nil => f h b
| NEcons h (h2 :: t) => f h (fold f (h2 :: t) b)
end.

(*reduce for NElists.*)
Definition reduceNE {X: Type} (f : X->X->X) (l : NElist X): X:=
  match l with
  | NEcons h [] => h
  | NEcons h (h2 :: t) => f h (foldL f h2 t)
  end.

  Example testfoldNE1: foldNE (plus) (NEcons 1 [2;3]) 0 = 6.
  Proof. simpl. reflexivity. Qed.

  Example testfoldNE2: foldNE (plus) (NEcons 1 [2;3]) 5 = 11.
  Proof. simpl. reflexivity. Qed.

  Example testreduceNE1: reduceNE (plus) (NEcons 1 [2; 3]) = 6.
  Proof. simpl. reflexivity.  Qed.

  Example testreduceNEnil: reduceNE (plus) (NEcons 15 []) = 15.
  Proof. simpl. reflexivity. Qed.

(*reduce for NElists and append for NElists distribute*)
Theorem reduceNE_append_dist: forall {X:Type} (f : X->X->X) (l1 l2 : NElist X),
(associative f) -> reduceNE f (appNE l1 l2) =  f (reduceNE f l1) (reduceNE f l2).
Proof.
  intros X f l1 l2 assoc. destruct l1. destruct l2. generalize dependent l0.
  induction l.
    -intros l0. simpl. destruct l0 as [|xnew lnew].
      +simpl. reflexivity.
      +simpl. f_equal. simpl. apply foldL_lemma. apply assoc.
    -intros l0. destruct l0 as [|xnew lnew].
      +simpl. apply foldL_lemma2. apply assoc.
      +simpl. apply foldL_lemma3. apply assoc. Qed.


(*some useful functions that can be defined using reduceNE*)

Definition first {X: Type} (a b : X):=
  a.

Definition last {X: Type} (a b : X):=
  b.
  
Definition head {X: Type} (l : NElist X):=
  reduceNE first l.

Definition lastElt {X : Type} (l: NElist X):=
  reduceNE last l.

  Example testhead1:  head(NEcons 1 [2;3]) = 1.
  Proof. simpl. unfold first. reflexivity.  Qed.

  Example testLastElt1: lastElt (NEcons 1 [2;3]) = 3.
  Proof. simpl. unfold last. reflexivity. Qed.

Theorem head_headNE_equal : forall {X : Type} (l : NElist X),
head l = headNE l.
Proof.
  intros X l.
  destruct l as [a l2].
  unfold head. unfold headNE.
  induction l2.
    -simpl. reflexivity.
    -simpl. unfold first. reflexivity. Qed.

Definition minList (l : NElist nat) : nat :=
  reduceNE smaller l.

Example testminList1:  minList (NEcons 1 [2;3]) = 1.
Proof. simpl. unfold smaller. simpl. reflexivity.  Qed.

Definition maxList (l : NElist nat) : nat :=
  reduceNE bigger l.

Example testmaxList:  maxList (NEcons 1 [2;3]) = 3.
Proof. simpl. unfold bigger. simpl. reflexivity.  Qed.



(*SECTION 6 : OTHER NELIST FUNCTIONS*)

(*the NElist version of flatmap*)
Definition NEflat_map {X Y: Type} (f: X -> NElist Y) (l: NElist X)
    : NElist Y :=
  match l with
  | NEcons h [] => f h
  | NEcons h (h2 :: t) => Mixapp2 (f h) (flat_map (compose NElist_to_list f) (h2 :: t))
  end.



  (*SECTION 7-- NELIST HOMOMORPHISMS*)

  (*the definition of a homomorphism*)
  Definition homomorphism {X Y: Type} (h : NElist X -> Y) : Prop :=
    exists (g : Y -> Y -> Y), (associative g) /\
    (forall (x y : NElist X), h (appNE x y) = g (h x) (h y)).


  Definition h' {X Y : Type} (h : NElist X -> Y) (x : X) : Y :=
    h (NEcons x []).

  (*A lemma showing that a function is a homomorphism if and only if
  it can be represented as a composition of a map of some function and a
  reduction of some associative operation*)
  Lemma homomorphism_lemma {X Y: Type} (h : NElist X -> Y) :
  homomorphism h <-> exists (g : Y -> Y -> Y) (f : X -> Y), (associative g) /\
  forall (x : NElist X), h x = reduceNE g (mapNE f x).
  Proof.
    split; intros H; try unfold homomorphism in H; destruct H as [g0 H].
      -exists g0. destruct H. exists (h' h).
      split; try apply H. intros z.
      geninduction z; intros a; try unfold h'.
        +simpl. try reflexivity.
        +rewrite represent_NEcons. rewrite H0. rewrite IHl'.
      rewrite mapNE_appNE_dist. rewrite reduceNE_append_dist; try reflexivity. apply H.
      -destruct H as [f0 H]. destruct H as [assoc H]. unfold homomorphism. exists g0.
      split; try apply assoc. intros z0 z1. rewrite H.
      rewrite mapNE_appNE_dist.
      rewrite reduceNE_append_dist; try rewrite H; try rewrite H; try reflexivity.
      apply assoc. Qed.



Definition AbstractID {X : Type} (x : X):= x.

(*proofs that various functions are homomorphisms by proving that they follow the 
format described above in the homomorphism_lemma*)

Theorem reduceNE_homomorphim : forall {X : Type} (f : X -> X -> X) (l : NElist X),
(associative f) -> reduceNE f l = reduceNE f (mapNE AbstractID l).
Proof.
  intros X f l assoc.
  destruct l.
  generalize dependent a.
  induction l.
  -intros a. simpl. unfold AbstractID. reflexivity.
  -intros a. rewrite represent_NEcons.
  rewrite reduceNE_append_dist.
    +rewrite mapNE_appNE_dist. rewrite reduceNE_append_dist.
      *rewrite <- IHl. reflexivity.
      *apply assoc.
    +apply assoc. Qed.

Theorem mapNE_homomorphism : forall {X: Type} (f : X -> X) (g : X -> NElist X) (l : NElist X),
(forall (a : X), g a = NEcons (f a) []) -> (mapNE f l = reduceNE appNE (mapNE g l)).
Proof.
  intros X f g l.
  intros H.
  destruct l as [x l0].
  generalize dependent x.
  induction l0.
  -intros x. simpl. rewrite H. reflexivity.
  -intros x0. rewrite represent_NEcons.
  rewrite mapNE_appNE_dist. rewrite IHl0.
  rewrite mapNE_appNE_dist. rewrite reduceNE_append_dist.
    +f_equal. unfold mapNE. unfold reduceNE. rewrite H. reflexivity.
    +unfold associative. intros a b c. rewrite appNE_assoc. reflexivity. Qed.


(*filterNE_homomorphism helpers*)

Definition fp {X : Type} (p : X -> bool) (x : X) :=
  match (p x) with
    |true => [x]
    |false => []
  end.

Theorem rewrite_cons : forall {X : Type} (a x : X) (l : list X),
a :: x :: l = [a] ++ x :: l.
Proof.
  intros X a x l. reflexivity. Qed.

Theorem rewrite_cons2 : forall {X : Type} (x : X) (l : list X),
x :: l = [x] ++ l.
Proof.
  intros X x l. reflexivity. Qed.

Theorem map_singleton_pull : forall {X Y : Type} (f : X -> Y) (a : X) (l : list X),
map f ([a] ++ l) = [f(a)] ++ map f l.
Proof.
  intros X Y f a l.
  induction l.
  -simpl. reflexivity.
  -simpl. reflexivity. Qed.

  Theorem fold_singleton_pull : forall {X : Type} (a : list X) (l : list (list X)),
  fold app ([a] ++ l) [] = app (fold app [a] []) (fold app l []).
  Proof.
    intros X a l.
    generalize dependent a.
    induction l.
    -intros a. simpl. rewrite app_nil_r. rewrite app_nil_r. reflexivity.
    -intros a. simpl. rewrite <- app_assoc. simpl. reflexivity. Qed.


Theorem filterNE_homomorphism : forall {X : Type} (p : X -> bool) (l : NElist X),
filterNE p l =  fold (app) (map (fp p) (NElist_to_list l)) [].
Proof.
  intros X p l.
  destruct l as [a l']. generalize dependent a.
  unfold NElist_to_list.
  induction l'.
  -intros a. simpl. unfold fp. rewrite app_nil_r. reflexivity.
  -intros a. rewrite represent_NEcons.
  rewrite filterNE_append_dist. rewrite IHl'.
  rewrite rewrite_cons. rewrite map_singleton_pull.
  rewrite fold_singleton_pull. f_equal.
  simpl.
  destruct (p a) eqn:Epa.
    +unfold fp. rewrite Epa. rewrite app_nil_r. reflexivity.
    +rewrite app_nil_r. unfold fp. rewrite Epa. reflexivity. Qed.


Definition Kc {X Y: Type} (c : Y) (a : X) :=
  c.

Theorem lengthNE_homomorphism: forall {X : Type} (l : NElist X), 
lengthNE l = reduceNE (plus) (mapNE (Kc 1) l).
Proof.
  intros X l.
  destruct l. generalize dependent a. induction l.
  -simpl. unfold Kc. reflexivity.
  -intros a. rewrite represent_NEcons.
  rewrite appNE_length. rewrite IHl.
  rewrite mapNE_appNE_dist. rewrite reduceNE_append_dist.
    +simpl. reflexivity.
    +unfold associative. intros a0 b c.
    induction a0.
      *simpl. reflexivity.
      *simpl. rewrite IHa0. reflexivity. Qed.


Theorem head_homomorphism: forall {X : Type} (l : NElist X),
head l = reduceNE first l.
Proof.
  intros X l.
  destruct l. destruct l.
  -simpl. reflexivity.
  -simpl. reflexivity. Qed.


Theorem last_homomorphism : forall {X : Type} (l : NElist X),
lastElt l = reduceNE last l.
Proof.
  intros X l.
  destruct l. destruct l.
  -reflexivity.
  -reflexivity. Qed.



(*NEh_homomorphism helpers*)
Definition NEinv_function {X Y: Type} (h : NElist X -> NElist Y) (h' : NElist Y -> NElist X) (a b : NElist Y) :=
h (appNE (h' a)  (h' b) ).

Theorem NEinv_func_append : forall {X Y: Type} (h : NElist X -> NElist Y) (h' : NElist Y -> NElist X) (a b : NElist X),
inverses h h' -> h (appNE a b) = NEinv_function h h' (h a) (h b).
Proof.
  intros X Y h h' a b.
  intros H.
  unfold NEinv_function.
  apply inverses_undo in H.
  destruct H.
  rewrite H. rewrite H. reflexivity. Qed.

Definition NEfh {X Y : Type} (h : NElist X -> Y) (x : X) :=
  h (NEcons x []).




(*Proof that if a function h is invertible, then h is a homomorphism, as there can be
constructed a function and operation so that a map of that function and a reduction
of that operation can be composed to form h*)
Theorem NEh_homomorphism: forall {X Y: Type} (h : NElist X -> NElist Y) (h' : NElist Y -> NElist X) (l : NElist X),
inverses h h' -> h l = reduceNE (NEinv_function h h') (mapNE (NEfh h) l).
Proof.
  intros X Y h h' l. intros H.
  destruct l. generalize dependent a.
  induction l.
  -intros a. simpl. unfold NEfh. reflexivity.
  -intros a. rewrite represent_NEcons.
  rewrite mapNE_appNE_dist. rewrite reduceNE_append_dist.
    +rewrite <- IHl. simpl.
    unfold NEinv_function. f_equal.
    apply inverses_undo in H. destruct H.
    rewrite H. unfold NEfh. rewrite H. simpl. reflexivity. 
    +unfold associative.
    unfold NEinv_function.
    intros a0 b c.
    apply inverses_undo in H. destruct H.
    rewrite H. rewrite H. f_equal.
    rewrite appNE_assoc. reflexivity. Qed.







(*reverse_homomorphism heplers*)
Definition rev_operator {X : Type} (x y : list X) :=
rev (rev x ++ rev y).

Theorem rev_operator_altform : forall {X : Type} (x y : list X),
rev_operator x y = y ++ x.
Proof.
  intros X x y.
  unfold rev_operator.
  destruct x.
  -simpl. rewrite app_nil_r. rewrite rev_involutive. reflexivity.
  -simpl.
  rewrite rev_app_distr. rewrite rev_involutive. f_equal.
  rewrite rev_app_distr. rewrite rev_involutive. simpl. reflexivity. Qed.

Definition operator_opposite {X Y: Type} (op : X -> X -> Y) (x y : X) :=
  op y x.

Definition elt_to_singleton {X : Type} (x : X) :=
  [x].



(*proof that reverse is a homomorphism*)
Theorem reverse_homomorphism : forall {X : Type} (l : list X),
rev l = fold (operator_opposite app) (map elt_to_singleton l) [].
intros X l.
induction l.
-simpl. reflexivity.
-simpl. rewrite <- IHl. unfold operator_opposite.
unfold elt_to_singleton. reflexivity. Qed.










(*SECTION 9-- PROMOTIONS*)

(*This section is a collection of theorems that generalize the distributive properties
of common functions.*)


Theorem map_promotion : forall {X Y: Type} (f : X -> Y) (l : list (list X)),
map f (fold app l []) = fold app (map (map f) l) [].
Proof.
  intros X Y f l.
  induction l.
    -simpl. reflexivity.
    -simpl. rewrite map_f_app_dist. f_equal.
    rewrite IHl. reflexivity. Qed.


Theorem mapNE_promotion : forall {X Y: Type} (f : X -> Y) (l : NElist (NElist X)),
mapNE f (reduceNE appNE l) = reduceNE appNE (mapNE (mapNE f) l).
Proof.
  intros X Y f l.
  geninduction l.
    -simpl. reflexivity.
    -intros a. rewrite represent_NEcons.
    rewrite reduceNE_append_dist.
      +rewrite mapNE_appNE_dist. rewrite IHl'.
      rewrite mapNE_appNE_dist.
      rewrite reduceNE_append_dist.
        *reflexivity.
        *unfold associative. intros a0 b c. apply appNE_assoc.
      +unfold associative. intros a0 b c. apply appNE_assoc. Qed.


Theorem filter_promotion : forall {X: Type} (p : X -> bool) (l : list (list X)),
filter p (fold app l []) = fold app (map (filter p) l) [].
Proof.
  intros X p l.
  induction l.
    -simpl. reflexivity.
    -simpl. rewrite filter_f_app_dist. f_equal.
    rewrite IHl. reflexivity. Qed.

Theorem filterNE_promotion : forall {X: Type} (p : X -> bool) (l : NElist (NElist X)),
filterNE p (reduceNE appNE l) = reduceNE app (mapNE (filterNE p) l).
Proof.
  intros X p l.
  destruct l. generalize dependent a.
  induction l.
    -simpl. reflexivity.
    -intros a. rewrite represent_NEcons.
    rewrite reduceNE_append_dist.
      +rewrite filterNE_append_dist.
      rewrite mapNE_appNE_dist. rewrite reduceNE_append_dist.
        *rewrite <- IHl. reflexivity.
        *unfold associative. intros a0 b c. apply app_assoc.
      +unfold associative. intros a0 b c. apply appNE_assoc. Qed.


Theorem reduceNE_promotion : forall {X: Type} (op : X -> X -> X) (l : NElist (NElist X)),
(associative op) -> reduceNE op (reduceNE appNE l) = reduceNE op (mapNE (reduceNE op) l).
Proof.
  intros X op l H.
  destruct l.
  generalize dependent a.
  induction l.
    -simpl. reflexivity.
    -intros a. rewrite represent_NEcons.
    rewrite reduceNE_append_dist.
      +rewrite reduceNE_append_dist.
        *rewrite mapNE_appNE_dist. rewrite reduceNE_append_dist.
          --rewrite <- IHl. reflexivity.
          --apply H.
        *apply H.
      +unfold associative. intros a0 b c.
      apply appNE_assoc. Qed.
      

Definition smallerf {X : Type} (f : X -> nat) (n m : X) : X :=
  match leb (f n) (f m) with
  |true => n
  |false => m
  end.

Definition biggerf {X : Type} (f : X -> nat) (n m : X) : X :=
  match leb (f n) (f m) with
  |true => m
  |false => n
  end.




(*SECTION 10 -- SUDOKU APPLICATION*)

Definition matrix (X : Type) : Type := list (list X).

Definition num_lists_in_matrix {X : Type} (m : matrix X) : nat :=
  length (m).

Fixpoint size_lists_in_matrix {X : Type} (m : matrix X) : list nat :=
  match m with
  |[] => []
  |h :: t => length h :: (size_lists_in_matrix t)
  end.

Definition board := matrix ascii.

Fixpoint n_is_only_elt (n : nat) (l : list nat) : bool :=
  match l with
  |[] => true
  |h :: t => if (h =? n) then (n_is_only_elt n t) else false
  end.


Class filled_board (b : board) :=
  { colsize : nat;
    num_lists : num_lists_in_matrix b = colsize;
    num_size : n_is_only_elt colsize (size_lists_in_matrix b) = true
  }.

  
Definition ascii_equal := Strings.Ascii.eqb.

Definition ascii_notequal (a : ascii) (b : ascii) := if ascii_equal a b then false else true.


Fixpoint notElem (x : ascii) (l : list ascii) : bool :=
  match l with
  |[] => true
  |h :: t => andb (ascii_notequal h x) (notElem x t)
  end.

Fixpoint nodups (l : list ascii) : bool :=
  match l with
  |[] => true
  |h :: t => andb (notElem h t) (nodups t)
  end.


Fixpoint all_nodups (li : list (list ascii)) : bool :=
  match li with
  |[] => true
  |h :: t => andb (nodups h) (all_nodups t)
  end.


Definition rows (b : board) := b.


Definition head_singleton {X : Type} (l : list X) :=
  match l with
  |[] => []
  |h :: t => [h]
  end.

Definition taill {X : Type} (l : list X) :=
  match l with
  |[] => []
  |h :: t => t
  end.

Fixpoint list_of_heads {X : Type} (l : list (list X)) :=
  match l with
  |[] => []
  |h :: t => head_singleton h ++ list_of_heads t
  end.

Example test_listofheads: list_of_heads [[1;2];[3;4]] = [1;3].
Proof. simpl. reflexivity. Qed.

Fixpoint list_of_tails {X : Type} (l : list (list X)) : list (list X) :=
  match l with
  |[] => []
  |h :: t => taill h :: list_of_tails t
  end.

Example test_listoftails: list_of_tails [[1;2;3];[4;5;6]] = [[2;3];[5;6]].
Proof. simpl. reflexivity. Qed.


Fixpoint list_of_singletons {X : Type} (l : list X) :=
  match l with
  |[] => []
  |h :: t => [h] :: list_of_singletons t
  end.

Example test_list_of_singletons: list_of_singletons [1;2;3] = [[1];[2];[3]].
Proof. simpl. reflexivity. Qed.


Fixpoint append_piecewise {X : Type} (l1: list X) (l2: list X) :=
  match l1 with
  |[] => []
  |h :: t => match l2 with
              |[] => []
              |h2 :: t2 => ([h] ++ [h2]) :: append_piecewise t t2
              end
  end.
(*Note: may encounter error if l1 and l2 are not the same length*)

Example test_append_piecewise: append_piecewise [1;2;3] [4;5;6] = [[1;4];[2;5];[3;6]].
Proof. simpl. reflexivity. Qed.


Fixpoint append_piecewise_listlist {X : Type} (l1: list (list X)) (l2: list (list X)) : list (list X) :=
  match l1 with
  |[] => match l2 with
          |[] => []
          |h3 :: t3 => h3 :: t3
          end
  |h :: t => match l2 with
              |[] => l1
              |h2 :: t2 => (h ++ h2) :: append_piecewise_listlist t t2
              end
  end.
(*Note: may get weird with null lists [] / lists of different sizes*)

Example test_append_piecewise_listlist: append_piecewise_listlist [[1];[2];[3]] [[4];[5];[6]] = [[1;4];[2;5];[3;6]].
Proof. simpl. reflexivity. Qed.

Example nnn : append_piecewise_listlist [[1];[2]] [[3;5];[4;6]] = [[1;3;5];[2;4;6]].
Proof. simpl. reflexivity. Qed.


Fixpoint list_of_singletons_listlist {X : Type} (l : list (list X)) :=
  match l with
  |[] => []
  |h :: t => list_of_singletons h :: list_of_singletons_listlist t
  end.

Example test_los_listlist: list_of_singletons_listlist [[1;2;3];[4;5;6]] = [[[1];[2];[3]];[[4];[5];[6]]].
Proof. simpl. reflexivity. Qed.


Definition transpose {X :Type} (l : list (list X)) :=
  match l with
  |[] => []
  |h :: t => foldL (append_piecewise_listlist) (list_of_singletons h) (list_of_singletons_listlist t)
  end.


Example test_transpose: transpose [[1;2;3];[4;5;6]] = [[1;4];[2;5];[3;6]].
Proof. simpl. reflexivity. Qed.

Example test_transpose2 : transpose [[]; [1;2]] = [[1];[2]].
Proof. simpl. reflexivity. Qed.

Example test_transpose_inv_emplist : transpose (transpose [[]; [1;2]]) = [[1;2]].
Proof. simpl. reflexivity. Qed.

Example test_transpose_unequeal : transpose [[1;2;3];[4;5]] = [[1;4];[2;5];[3]].
Proof. simpl. reflexivity. Qed.


Definition cols (b : board) :=
  transpose b.




  
Fixpoint isolate_first_n {X : Type} (n : nat) (l: list X) : list (list X) :=
  match l with
  |[] => []
  | h :: t => if (n =? 0) then [h :: t] else ([h] :: (isolate_first_n (n-1) t))
  end.

Example test_isolate1stn : isolate_first_n 2 [1;2;3;4] = [[1];[2];[3;4]].
Proof. simpl. reflexivity. Qed.


Fixpoint combine_first_n {X: Type} (n : nat) (l : list (list X)) (b : list X): list (list X) :=
  match l with
  | nil => [b]
  | h :: t => if n =? 0 then ([b] ++ (h::t)) else (combine_first_n (n-1) t (b ++ h))
  end.


Example test_combine1stn : combine_first_n 2 [[1];[2];[3; 4]] [] = [[1;2];[3;4]].
Proof. simpl. reflexivity. Qed.


Example test_combine1stn2 : combine_first_n 2 [[1];[2];[3];[4]] [] = [[1;2];[3]; [4]].
Proof. simpl. reflexivity. Qed.


Definition group_first_n {X: Type} (n : nat) (l : list X) : list(list X) :=
  combine_first_n n (isolate_first_n n l) [].



Example test_group1stn : group_first_n 2 [1;2;3;4] = [[1;2];[3;4]].
Proof. unfold group_first_n. simpl. reflexivity. Qed.


Example test_group1stn2 : group_first_n 2 [1;2;3;4;5;6] = [[1;2];[3;4;5;6]].
Proof. unfold group_first_n. simpl. reflexivity. Qed.



Fixpoint combine_by_n {X: Type} (boxsize : nat) (n : nat) (l : list (list X)) (b : list X): list (list X) :=
  match l with
  | nil => [b]
  | h :: t => if (neq n 0) then (combine_by_n boxsize (n-1) t (b ++ h)) else (([b] ++ (combine_by_n boxsize (boxsize - 1) (t) h)))
  end.

Example test_combinebyn : combine_by_n 3 3 [[1];[2];[3];[4];[5];[6];[7];[8];[9]] [] = [[1;2;3];[4;5;6];[7;8;9]].
Proof. simpl. reflexivity. Qed.


Definition groupby {X : Type} (n : nat) (l: list X) : list (list X) :=
  combine_by_n n n (list_of_singletons l) [].

  
Example test_groupby : groupby 3 [1;2;3;4;5;6;7;8;9] = [[1;2;3];[4;5;6];[7;8;9]].
Proof. unfold groupby. simpl. reflexivity. Qed.



Definition ungroup {X: Type} (l : list (list X)) : list X :=
  foldL app [] l.

Example test_ungroup : ungroup [[1;2;3];[4;5;6];[7;8;9]] = [1;2;3;4;5;6;7;8;9].
Proof. unfold ungroup. simpl. reflexivity. Qed.



Definition boxs_gen {X : Type} (boxsize : nat) (l : list (list X)) : list (list X) :=
  map ungroup (ungroup (map transpose (groupby boxsize (map (groupby boxsize) (l))))).


Example test_boxs_gen : boxs_gen 2 [[1;2;3;4];[5;6;7;8];[9;10;11;12];[13;14;15;16]] = [[1;2;5;6];[3;4;7;8];[9;10;13;14];[11;12;15;16]].
Proof. unfold boxs_gen. simpl. unfold ungroup. simpl. reflexivity. Qed.



Definition boxs (boxsize : nat) (b : board) := boxs_gen boxsize b.






Definition correct (b : board) (boxsize : nat) : bool :=
  andb (andb (all_nodups (rows b)) (all_nodups (cols b))) (all_nodups (boxs boxsize b)).


  
Definition choices_type : Type := matrix (list ascii).


Definition choose (blank : ascii -> bool) (cellvals : list ascii) (e : ascii):=
  if blank e then cellvals else [e].


Definition choices (b : board) (blank : ascii -> bool) (cellvals : list ascii) : choices_type :=
  map (map (choose blank cellvals)) b.




(*take ELEMENT and append to beginning of each list in list lists*)
Fixpoint cp_helper0 {X : Type} (x : X) (l : list (list X)) : list (list X) :=
  match l with
  |[] => []
  |h :: t => ([x] ++ h) :: cp_helper0 x t
  end.


Example test_cphelp0 : cp_helper0 0 [[1;2];[3;4]] = [[0;1;2];[0;3;4]].
Proof. simpl. reflexivity. Qed.


(*cartesian product with single list at start*)
Fixpoint cp_helper {X : Type} (l : list X) (ll : list (list X)) : list (list X) :=
  match l with
  |[] => []
  |h :: t => cp_helper0 h ll ++ cp_helper t ll
  end.
  
Example test_cphelp : cp_helper [1;2] [[3;4;5];[6;7;8]] = [[1;3;4;5];[1;6;7;8];[2;3;4;5];[2;6;7;8]].
Proof. simpl. reflexivity. Qed.


Fixpoint cp {X : Type} (l : list (list X)) : list (list X) :=
  match l with
  |[] => []
  |h :: [] => list_of_singletons h
  |h :: t => cp_helper h (cp t)
  end.


Example test_cp : cp [[1;2];[3;4];[5;6]] = [[1;3;5];[1;3;6];[1;4;5];[1;4;6];[2;3;5];[2;3;6];[2;4;5];[2;4;6]].
Proof. simpl. reflexivity. Qed.


Definition mcp {X: Type} (m : matrix (list X)) : list (matrix X) :=
  cp (map cp m).


Example test_mcp : mcp [[[1;2];[1;2]];[[1;2];[1;2]]] = [[[1; 1]; [1; 1]]; [[1; 1]; [1; 2]];
[[1; 1]; [2; 1]]; [[1; 1]; [2; 2]];
[[1; 2]; [1; 1]]; [[1; 2]; [1; 2]];
[[1; 2]; [2; 1]]; [[1; 2]; [2; 2]];
[[2; 1]; [1; 1]]; [[2; 1]; [1; 2]];
[[2; 1]; [2; 1]]; [[2; 1]; [2; 2]];
[[2; 2]; [1; 1]]; [[2; 2]; [1; 2]];
[[2; 2]; [2; 1]]; [[2; 2]; [2; 2]]].
Proof. unfold mcp. simpl. reflexivity. Qed.


Fixpoint filter_specific {X Y:Type} (test: X-> Y -> bool) (l:list X) (n : Y) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h n then h :: (filter_specific test t n)
    else filter_specific test t n
  end.

Definition sudoku (b : board) (blank : ascii -> bool) (cellvals : list ascii) (boxsize : nat) : list board :=
  filter_specific correct (mcp (choices b blank cellvals)) (boxsize).
  


Definition a_char := Ascii false true true false false false false true.
Definition b_char := Ascii false true true false false false true false.
Definition blank_char := Ascii false false true false false false false false.





Definition blank (a : ascii) := if ascii_equal a blank_char then true else false.


Example test_choices : (choices
[[a_char; blank_char];
[blank_char; blank_char]] blank
[a_char; b_char]) = [[[a_char]; [a_char; b_char]];
[[a_char; b_char]; [a_char; b_char]]].
Proof. unfold choices. simpl. unfold choose. simpl. reflexivity. Qed. 


Example test_mcp2 : mcp [[[a_char]; [a_char; b_char]];
[[a_char; b_char]; [a_char; b_char]]] = [[[a_char; a_char]; [a_char; a_char]];
[[a_char; a_char]; [a_char; b_char]];
[[a_char; a_char]; [b_char; a_char]];
[[a_char; a_char]; [b_char; b_char]];
[[a_char; b_char]; [a_char; a_char]];
[[a_char; b_char]; [a_char; b_char]];
[[a_char; b_char]; [b_char; a_char]];
[[a_char; b_char]; [b_char; b_char]]].
Proof. unfold mcp. simpl. reflexivity. Qed.


Example test_correct : correct [[a_char; b_char]; [b_char; a_char]] 1 = true.
Proof. unfold correct. simpl. reflexivity. Qed.


Example test_sudoku: sudoku  [[a_char; blank_char];
[blank_char; blank_char]] blank [a_char ; b_char] 1= [[[a_char; b_char];
[b_char; a_char]]].
Proof. unfold sudoku. simpl. reflexivity. Qed.


Example test_sudoku': sudoku  [[blank_char; blank_char];
[blank_char; blank_char]] blank [a_char ; b_char] 1= [[[a_char; b_char];
[b_char; a_char]]; [[b_char; a_char];
[a_char; b_char]]].
Proof. unfold sudoku. simpl. reflexivity. Qed.



Definition single {X : Type} (l : list X) :=
  match l with
  |[] => false
  |h :: [] => true
  |h2 :: t2 => false
  end.

Goal forall {X : Type} (x : X), single [x] = true.
Proof. intros X x. simpl. reflexivity. Qed.

Goal forall {X : Type} (x y : X), single [x;y] = false.
Proof. intros X x. simpl. reflexivity. Qed.


Definition fixed (l : list (list ascii)) : list ascii :=
foldL app [] (filter single l).

Definition example_choice : choices_type := [[[a_char]; [a_char; b_char]];
[[a_char; b_char]; [a_char; b_char]]].

Definition example_row : matrix ascii := [[a_char]; [a_char; b_char]].

Example test_fixed : fixed example_row = [a_char].
Proof. unfold fixed. simpl. reflexivity. Qed.



Fixpoint delete_single {X : Type} (x : X) (l : list X) (equality : X -> X -> bool) :=
  match l with
  | [] => []
  | h :: t => if equality h x then (delete_single x t equality) else (h :: (delete_single x t equality))
  end.

(*delete every element of l1 from l2*)
Fixpoint delete_all {X : Type} (l1 l2 : list X) (equality : X -> X -> bool) :=
  match l1 with
  | [] => l2
  | h :: t => delete_all t (delete_single h l2 equality) equality
  end.


Fixpoint list_equal {X : Type} (l1 l2 : list X) (x_Equal : X -> X -> bool) : bool :=
  match l1 with
    | [] => match l2 with
            | [] => true
            | h0 :: t0 => false
            end
    | h :: t => match l2 with
            | [] => false
            | h1 :: t1 => if (x_Equal h h1) then list_equal t t1 x_Equal else false
                end
  end.

Example test_listequal : list_equal [1;2;3] [1;2;3;4] eqb = false.
Proof. simpl. reflexivity. Qed.

Example test_listequal2 : list_equal [1;2;3] [1;2;3] eqb = true.
Proof. simpl. reflexivity. Qed.

Example test_listequal3 : list_equal [1;2;3] [1;2;2] eqb = false.
Proof. simpl. reflexivity. Qed. 

Definition equality_list_ascii (a b : list ascii) := list_equal a b ascii_equal.

Definition equality_listlist_ascii (a b : list (list ascii)) := list_equal a b equality_list_ascii.

Definition equality_choices_type (a b : choices_type) : bool :=
  list_equal a b equality_listlist_ascii.

Definition remove (x : list ascii) (l : list ascii) :=
  if single l then l else delete_all x l ascii_equal.

Definition sudoku_reduce (l : list (list ascii)) : list (list ascii) :=
  map (remove (fixed l)) l. 

Example test_sudoku_reduce : sudoku_reduce [[a_char];
[a_char; b_char]] = [[a_char];[b_char]].
Proof. unfold sudoku_reduce. simpl. unfold remove. simpl. reflexivity. Qed.

Definition pruneBy (f : matrix (list ascii) -> matrix (list ascii)) (m : matrix (list ascii)) :=
  f (map sudoku_reduce (f m)).

Definition rows_matrix (m : matrix (list ascii)) := m.

Definition cols_matrix (m : matrix (list ascii)) := transpose m.

Definition boxs_matrix (boxsize : nat) (m : matrix (list (ascii))) := boxs_gen boxsize m.


Example test_pruneBy_rows : pruneBy rows_matrix [[[a_char];
[a_char; b_char]]; [[a_char;b_char];[a_char;b_char]]] = [[[a_char];[b_char]];[[a_char;b_char];[a_char;b_char]]].
Proof. unfold pruneBy. simpl. unfold sudoku_reduce. simpl. unfold remove. simpl. unfold rows_matrix. reflexivity. Qed.

Example test_pruneBy_cols : pruneBy cols_matrix [[[a_char];
[a_char; b_char]]; [[a_char;b_char];[a_char;b_char]]] = [[[a_char];
[a_char; b_char]]; [[b_char];[a_char;b_char]]].
Proof. unfold pruneBy. unfold sudoku_reduce. unfold remove. simpl. reflexivity. Qed.


Definition pruneBy_boxs (boxsize : nat) (m : matrix (list ascii)) :=
  match boxsize with
  | 1 => m
  | _ => boxs_matrix boxsize (map sudoku_reduce (boxs_matrix boxsize m))
  end.
  
Definition c_char := Ascii false true true false false false true true.
Definition d_char := Ascii false true true false false true false false.
Definition e_char := Ascii false true true false false true false true.
Definition f_char := Ascii false true true false false true true false.
Definition g_char := Ascii false true true false false true true true.
Definition h_char := Ascii false true true false true false false false.
Definition i_char := Ascii false true true false true false false true.

Definition fourbyfour_choices := [[[a_char];
[a_char; b_char; c_char; d_char]; [b_char]; [d_char]]; 
[[a_char; b_char; c_char; d_char];[a_char; b_char; c_char; d_char]; [a_char];[c_char]];
[[b_char];[d_char];[c_char];[a_char]]; [[c_char];[a_char];[d_char];[b_char]]].

Example test_pruneBy_boxs : pruneBy_boxs 2 fourbyfour_choices =
[[[a_char];
[b_char; c_char; d_char]; [b_char]; [d_char]]; 
[[b_char; c_char; d_char];[b_char; c_char; d_char]; [a_char];[c_char]];
[[b_char];[d_char];[c_char];[a_char]]; [[c_char];[a_char];[d_char];[b_char]]].
Proof. unfold pruneBy_boxs. unfold sudoku_reduce. simpl. unfold remove. simpl.
unfold boxs_matrix. unfold boxs_gen. simpl. unfold ungroup. simpl. reflexivity. Qed.


Example test_pruneby_boxs_boxsize1 : pruneBy_boxs 1 [[[a_char]; [a_char; b_char]];
[[a_char; b_char]; [a_char; b_char]]] = [[[a_char]; [a_char; b_char]];
[[a_char; b_char]; [a_char; b_char]]].
Proof. unfold pruneBy_boxs. reflexivity. Qed. 



Definition prune (boxsize : nat) (m : matrix (list ascii)) : matrix (list ascii) :=
  pruneBy_boxs boxsize (pruneBy cols_matrix (pruneBy rows_matrix m)).


Example test_prune0 : prune 2 fourbyfour_choices = 
[[[a_char];
[c_char]; [b_char]; [d_char]]; 
[[d_char];[b_char]; [a_char];[c_char]];
[[b_char];[d_char];[c_char];[a_char]]; [[c_char];[a_char];[d_char];[b_char]]].
Proof. unfold prune. unfold pruneBy. unfold pruneBy_boxs. unfold sudoku_reduce.
 unfold remove. simpl. unfold boxs_matrix. unfold boxs_gen. simpl. unfold ungroup. simpl.
 reflexivity. Qed.





Example test_prune : prune 1 [[[a_char]; [a_char; b_char]];
[[a_char; b_char]; [a_char; b_char]]] = [[[a_char]; [b_char]];
[[b_char]; [a_char]]].
simpl.
 unfold prune. unfold pruneBy. simpl. unfold remove. simpl. reflexivity. Qed.



Definition sudoku2 (b : board) (blank : ascii -> bool) (cellvals : list ascii) (boxsize : nat) : list board
 := filter_specific correct (mcp (prune boxsize (choices b blank cellvals))) (boxsize).


Definition fourbyfour_board := [[a_char;
blank_char; b_char; d_char]; 
[blank_char; blank_char; a_char; c_char];
[b_char;d_char;c_char;a_char]; [c_char;a_char;d_char;b_char]].

Example test_sudoku2_fourbyfour : sudoku2 fourbyfour_board blank [a_char; b_char;c_char;d_char] 2 = 
[[[a_char;
c_char; b_char; d_char]; 
[d_char; b_char; a_char; c_char];
[b_char;d_char;c_char;a_char]; [c_char;a_char;d_char;b_char]]].
Proof. unfold sudoku2. simpl. reflexivity. Qed.

Example test_sudoku2: sudoku2 [[a_char; blank_char];
[blank_char; blank_char]] blank [a_char ; b_char] 1= [[[a_char; b_char];
[b_char; a_char]]].
Proof. unfold sudoku2. simpl. reflexivity. Qed.



Definition search (m : matrix (list ascii)) (boxsize : nat) :=
  filter_specific correct (mcp m) boxsize.


Definition head_list {X : Type} (elt : X)  (l : list X) :=
  match l with
  |[] => elt
  |h :: t => h
  end.



Definition sudoku_final (b : board) (blank : ascii -> bool)
  (cellvals : list ascii) (boxsize : nat)  := 
 head_list [] (search (prune boxsize (choices b blank cellvals)) boxsize).

 Example test_sudoku_final_fourbyfour : sudoku_final
      fourbyfour_board blank [a_char; b_char;c_char;d_char] 2 = 
 [[a_char;
 c_char; b_char; d_char]; 
 [d_char; b_char; a_char; c_char];
 [b_char;d_char;c_char;a_char]; [c_char;a_char;d_char;b_char]].
 Proof. unfold sudoku_final.  simpl. reflexivity. Qed.
 
 Example test_sudoku_final: sudoku_final [[a_char; blank_char];
 [blank_char; blank_char]] blank [a_char ; b_char] 1= [[a_char; b_char];
 [b_char; a_char]].
 Proof. unfold sudoku_final. simpl. reflexivity. Qed.


