(* binary search trees on Z *)
(* (C) Pierre Cast�ran *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Export ZArith.
Require Import Extraction.

Open Scope Z_scope.

(* binary trees *)

Inductive Z_btree : Set :=
| Z_leaf : Z_btree
| Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.


Definition is_bnode (t: Z_btree) : Prop :=
  match t with 
  | Z_leaf => False 
  | _ => True
  end.


(* n : Z occurs in some tree *)

Inductive occ (n:Z) : Z_btree -> Prop :=
| occ_root : forall t1 t2:Z_btree, occ n (Z_bnode n t1 t2)
| occ_l : forall (p:Z) (t1 t2:Z_btree), occ n t1 -> occ n (Z_bnode p t1 t2)
| occ_r : forall (p:Z) (t1 t2:Z_btree), occ n t2 -> occ n (Z_bnode p t1 t2)
.

#[ export ] Hint  Constructors   occ  : searchtrees.

Derive Inversion_clear OCC_INV with
    (forall (z z':Z) (t1 t2:Z_btree), occ z' (Z_bnode z t1 t2)).

Lemma occ_inv :
  forall (z z':Z) (t1 t2:Z_btree),
    occ z' (Z_bnode z t1 t2) -> z = z' \/ occ z' t1 \/ occ z' t2.
Proof.
  inversion 1 using OCC_INV; auto with searchtrees.
Qed.

#[ export ] Hint Resolve occ_inv: searchtrees.

Lemma not_occ_Leaf : forall z:Z, ~ occ z Z_leaf.
Proof.
  unfold not;  inversion_clear 1.
Qed.
#[ export ] Hint Resolve not_occ_Leaf: searchtrees.

(* naive search *)

Definition naive_occ_dec : forall (n:Z) (t:Z_btree), {occ n t} + {~ occ n t}.
Proof.
  intros n t; induction t as [| z t1 IH1 t2 IH2].
  -  right; auto with searchtrees.
  -  case (Z.eq_dec n z).
     + intro e; subst n;  left; auto with searchtrees.
     +  case IH1; case IH2; intros; auto with searchtrees.
        right; intro H; elim (occ_inv H); auto with searchtrees.
        tauto.
Defined.

(** Tests :
Extraction naive_occ_dec.
 *)
(* auxiliary definition for search, insertion and deletion *)

(* z is less than every label in t *)
Inductive min (z:Z) (t:Z_btree) : Prop :=
| min_intro : (forall z':Z, occ z' t -> z < z') -> min z t.

#[ export ] Hint Constructors min: searchtrees.

(* z is greater than every label in t *)
Inductive maj (z:Z) (t:Z_btree) : Prop :=
  maj_intro : (forall z':Z, occ z' t -> z' < z) -> maj z t
.

#[ export ] Hint Constructors maj: searchtrees.

(* search-ness predicate on binary trees *)
Inductive search_tree : Z_btree -> Prop :=
| leaf_search_tree : search_tree Z_leaf
| bnode_search_tree :
    forall (z:Z) (t1 t2:Z_btree),
      search_tree t1 ->
      search_tree t2 ->
      maj z t1 -> min z t2 -> search_tree (Z_bnode z t1 t2)
.

#[ export ] Hint Constructors search_tree : searchtrees.

Lemma min_leaf : forall z:Z, min z Z_leaf.
Proof.
  intro z; apply min_intro; intros z' H; inversion_clear H.
Qed.

#[ export ] Hint Resolve min_leaf: searchtrees.

Lemma maj_leaf : forall z:Z, maj z Z_leaf.
Proof.
  intro z; apply maj_intro; intros z' H; inversion_clear H.
Qed.

#[ export ] Hint Resolve maj_leaf: searchtrees.

Lemma maj_not_occ : forall (z:Z) (t:Z_btree), maj z t -> ~ occ z t.
Proof.
  intros z t H H'; elim H; intros; absurd (z < z); auto.
  apply Z.lt_irrefl.
Qed.

#[ export ] Hint Resolve maj_not_occ: searchtrees.

Lemma min_not_occ : forall (z:Z) (t:Z_btree), min z t -> ~ occ z t.
Proof.
  intros z t H H'; elim H; intros; absurd (z < z); auto.
  apply Z.lt_irrefl.
Qed.

#[ export ] Hint Resolve min_not_occ: searchtrees.

Section search_tree_basic_properties.

  Variable n : Z.
  Variables t1 t2 : Z_btree.
  Hypothesis se : search_tree (Z_bnode n t1 t2).

  Lemma search_tree_l : search_tree t1.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[ local ] Hint Resolve search_tree_l: searchtrees.

  Lemma search_tree_r : search_tree t2.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[local] Hint Resolve search_tree_r: searchtrees.

  Lemma maj_l : maj n t1.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[local] Hint Resolve maj_l: searchtrees.

  Lemma min_r : min n t2.
  Proof.
    inversion_clear se; auto with searchtrees.
  Qed.
  #[local] Hint Resolve min_r: searchtrees.

  Lemma not_right : forall p:Z, p <= n -> ~ occ p t2.
  Proof.
    intros p H; elim min_r.
    unfold not; intros; absurd (n < p); auto with searchtrees.
    apply Zle_not_lt; assumption.
  Qed.

