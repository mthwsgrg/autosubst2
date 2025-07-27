(** * General Header Autosubst - Assumptions and Definitions *)

(** ** Axiomatic Assumptions
    For our development, during rewriting of the reduction rules,  we have to extend Coq with two well known axiomatic assumptions, namely _functional extensionality_ and _propositional extensionality_. The latter entails _proof irrelevance_.
*)

(** *** Functional Extensionality
    We import the axiom from the Coq Standard Library and derive a utility tactic to make the assumption practically usable.
 *)

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.Tactics.

Tactic Notation "nointr" tactic(t) :=
  let m := fresh "marker" in
  pose (m := tt);
  t; revert_until m; clear m.

Ltac fext := nointr repeat (
  match goal with
    [ |- ?x = ?y ] =>
    (refine (@functional_extensionality_dep _ _ _ _ _) ||
     refine (@forall_extensionality _ _ _ _) ||
     refine (@forall_extensionalityP _ _ _ _) ||
     refine (@forall_extensionalityS _ _ _ _)); intro
  end).


(** ** Functor Instances

Exemplary functor instances needed to make Autosubst's generation possible for functors.
Two things are important:
1. The names are fixed.
2. For Coq to check termination, also the proofs have to be closed with Defined.
 *)

(** *** List Instance *)
Require Export List.

Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y)  :=
  fun x => g (f x).

Notation "'list_map'" := map.

Definition list_ext {A B} {f g : A -> B} :
  (forall x, f x = g x) -> forall xs,  list_map f xs = map g xs.
  intros H. induction xs. reflexivity.
  cbn. f_equal. apply H. apply IHxs.
Defined.

Definition list_id {A}  { f : A -> A} :
  (forall x, f x = x) -> forall xs, List.map f xs = xs.
Proof.
  intros H. induction xs. reflexivity.
  cbn. rewrite H. rewrite IHxs; eauto.
Defined.

Definition list_comp {A B C} {f: A -> B} {g: B -> C} {h} :
  (forall x, (funcomp  g f) x = h x) -> forall xs, map g (map f xs) = map h xs.
Proof.
  induction xs. reflexivity.
  cbn. rewrite <- H. f_equal. apply IHxs.
Defined.

(** *** Prod Instance *)

Definition prod_map {A B C D} (f : A -> C) (g : B -> D) (p : A * B) :
  C * D.
Proof.
  destruct p. split. auto. auto.
Defined.

Definition prod_id {A B} {f : A -> A} {g : B -> B} :
  (forall x, f x = x) -> (forall x, g x = x) -> forall p, prod_map f g p = p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_ext {A B C D} {f f' : A -> C} {g g': B -> D} :
  (forall x, f x = f' x) -> (forall x, g x = g' x) -> forall p, prod_map f g p = prod_map f' g' p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
Defined.

Definition prod_comp {A B C D E F} {f1 : A -> C} {g1 : C -> E} { h1} {f2: B -> D} {g2: D -> F} {h2}:
  (forall x, (funcomp  g1 f1) x = h1 x) -> (forall x, (funcomp g2 f2) x = h2 x) -> forall p, prod_map g1 g2 (prod_map f1 f2 p) = prod_map h1 h2 p.
Proof.
  intros. destruct p. cbn. f_equal; auto.
  now rewrite <- H. now rewrite <- H0.
Defined.


(** *** Function Instance *)

Definition cod X A:  Type :=  X -> A.

Definition cod_map {X} {A B} (f : A -> B) (p : X -> A) :
  X -> B.
Proof. eauto. Defined.

(** Note that this requires functional extensionality. *)
Definition cod_id {X} {A} {f : A -> A} :
  (forall x, f x = x) -> forall (p: X -> A), cod_map f p = p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_ext {X} {A B} {f f' : A -> B} :
  (forall x, f x = f' x) -> forall (p: X -> A), cod_map f p = cod_map f' p.
Proof. intros H p. unfold cod_map. fext. congruence. Defined.

Definition cod_comp {X} {A B C} {f : A -> B} {g : B -> C} {h} :
  (forall x, (funcomp g f) x =  h x) -> forall (p: X -> _), cod_map g (cod_map f p) = cod_map h p.
Proof. intros H p. unfold cod_map. fext. intros x. now rewrite <- H. Defined.

#[export] Hint Rewrite in_map_iff : FunctorInstances.





(** Vectors *)



(** A ℕ-indexed finite type for vectors *)
Fixpoint finat (n : nat) : Type :=
  match n with
  | 0 => False
  | S m => option (finat m)
  end.



(** Vector definition *)
Notation vec n A := (cod (finat n)  A).

(** Vector satisfies the functor laws *)
Definition vec_map {A B: Type} {n: nat} (f: A -> B) (v: vec n A) := fun n => f (v n).
Definition vec_id {n: nat} {A} {f : A -> A} :
  (forall x, f x = x) -> forall (p: finat n -> A), vec_map f p = p.
Proof. intros H p. unfold vec_map. fext. congruence. Defined.
Definition vec_ext {n: nat} {A B} {f f' : A -> B} :
  (forall x, f x = f' x) -> forall (p: finat n -> A), vec_map f p = vec_map f' p.
Proof. intros H p. unfold vec_map. fext. congruence. Defined.
Definition vec_comp {n: nat} {A B C} {f : A -> B} {g : B -> C} {h} :
  (forall x, (funcomp g f) x =  h x) -> forall (p: finat n -> _), vec_map g (vec_map f p) = vec_map h p.
Proof. intros H p. unfold vec_map. fext. intros x. now rewrite <- H. Defined.



(** finat functions *)
Fixpoint finat_add (m : nat) {n} : finat ( n) -> finat ( (m + n)) :=
  fun n => match m with
        | 0 => n
        | S m => Some (finat_add m n)
        end.


Definition finat_expand {m : nat} {n} : finat (m) -> finat ((m + n)).
Proof.
  induction m.
  - intros [].
  - intros [x|].
    + exact (finat_add 1 (IHm x)).
    + exact None.
Defined.


Lemma destruct_finat {m n} (x : finat ((m + n))):
  (exists x', x = finat_expand  x') \/ exists x', x = finat_add m x'.
Proof.
  induction m; simpl in *.
  - right. eauto.
  - destruct x as [x|].
    + destruct (IHm x) as [[x' ->] |[x' ->]].
      * left. now exists (Some x').
      * right. eauto.
    + left. exists None. eauto.
Qed.





(** Vector operations *)
Definition vcons {X : Type} {n : nat} (x : X) (f : finat (n) -> X) (m : finat ( (S n))) : X :=
  match m with
  | None => x
  | Some i => f i
  end.

Fixpoint vcat {X: Type} {m : nat} : forall {n} (f : finat ( m) -> X) (g : finat ( n) -> X),
             finat ((m + n))  -> X.
Proof.
  destruct m.
  - intros n f g. exact g.
  - intros n f g. cbn. apply vcons.
    + exact (f None).
    + apply vcat.
      * intros z. exact (f (Some z)).
      * exact g.
Defined.


Notation vcomp f g := (funcomp g f). 





(** Vector properties *)
Lemma vcons_comp (T: Type) U {m} (s: T) (sigma: finat (m) -> T) (tau: T -> U ) :
  vcomp (vcons s sigma) tau =  vcons (tau s) (vcomp sigma  tau).
Proof.
  fext. intros [x|]. reflexivity. simpl. reflexivity.
Qed.



Lemma vcat_first' {X} {m n} (f : finat (m) -> X) (g : finat (n) -> X) z:
  (vcat f g) (finat_expand  z) = f z.
Proof.
 induction m.
  - inversion z.
  - destruct z.
    + simpl. simpl. now rewrite IHm.
    + reflexivity.
Qed.

Lemma vcat_first X m n (f : finat (m) -> X) (g : finat (n) -> X) :
  (vcomp finat_expand  (vcat f g)) = f.
Proof. fext. intros z. unfold funcomp. apply vcat_first'. Qed.

Lemma vcat_second' X  m n (f : finat (m) -> X) (g : finat (n) -> X) z :
  vcat  f g (finat_add m z) = g z.
Proof. induction m; cbn; eauto. Qed.

Lemma vcat_tail X  m n (f : finat (m) -> X) (g : finat (n) -> X) :
  vcomp (finat_add m) ( vcat f g) = g.
Proof. fext. intros z. unfold funcomp. apply vcat_second'. Qed.


Lemma vcat_comp' X Y (m d:nat)  (f : finat (m) -> X) (g : finat (d) -> X) (h : X -> Y) x:
 h (vcat  f g x)  = vcat  (vcomp f  h) (vcomp g  h) x.
Proof.
  simpl in *.
  destruct (destruct_finat x) as [[x' ->]|[x' ->]].
  - now rewrite !vcat_first'.
  - now rewrite !vcat_second'.
Qed.

Lemma vcat_comp {X Y} {m:nat} {d} {f : finat ( m) -> X} {g : finat (d) -> X} {h : X -> Y} :
 vcomp (vcat f g)  h = vcat   (vcomp f  h) (vcomp g  h).
Proof. fext. intros z. unfold funcomp. apply vcat_comp'. Qed.


Definition empty_vec {X} : finat 0 -> X :=  fun x => match x with end.

Lemma empty_comp_vec: forall {Y Z} {f: Y -> Z} , ( vcomp empty_vec f) = empty_vec.
  intros.
  fext.
  intros.
  destruct x.
Qed.

