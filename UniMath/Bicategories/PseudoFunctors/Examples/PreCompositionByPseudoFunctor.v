(* ******************************************************************************* *)
(** * Pre-composition by a pseudofunctor is a pseudofunctor
    Gabriel Merlin
    January 2025
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.

Local Open Scope cat.

Section PreCompositionByPseudoFunctor.
  Context {B₁ B₂ B₃ : bicat}
          (F : psfunctor B₁ B₂).

  Definition right_whisker_comp_pstrans
             {G₁ G₂ G₃ : psfunctor B₂ B₃}
             (η : pstrans G₁ G₂)
             (θ : pstrans G₂ G₃)
    : invertible_modification (comp_pstrans (η ▻ F) (θ ▻ F))
        ((comp_pstrans η θ) ▻ F).
  Proof.
    use make_invertible_modification.
    - intro X.
      exact (id2_invertible_2cell (comp_pstrans (η ▻ F) (θ ▻ F) X)).
    - abstract
        (intros X Y f; cbn ;
         rewrite id2_rwhisker, lwhisker_id2, id2_left, id2_right ;
         reflexivity).
  Defined.

  (** Right whiskering of a modification by a pseudo-functor *)
  Definition modification_psfunctor
             {G₁ G₂ : psfunctor B₂ B₃}
             {η₁ η₂ : pstrans G₁ G₂}
             (m : modification η₁ η₂)
    : modification (η₁ ▻ F) (η₂ ▻ F).
  Proof.
    use make_modification.
    - intro X.
      exact (m (F X)).
    - intros X Y f; cbn.
      apply modnaturality_of.
  Defined.

  Lemma vcomp_modification_psfunctor
        {G₁ G₂ : psfunctor B₂ B₃}
        {η₁ η₂ η₃ : pstrans G₁ G₂}
        (m₁ : modification η₁ η₂)
        (m₂ : modification η₂ η₃)
    : modification_psfunctor (vcomp2 m₁ m₂) =
      vcomp2 (modification_psfunctor m₁) (modification_psfunctor m₂).
  Proof.
    use modification_eq.
    intro.
    reflexivity.
  Qed.

  Lemma id_pstrans_psfunctor
        {G₁ G₂ : psfunctor B₂ B₃}
        (η : pstrans G₁ G₂)
    : modification_psfunctor (id2 η) = id2 (η ▻ F).
  Proof.
    use modification_eq.
    intro.
    reflexivity.
  Qed.

  Definition pre_comp_psfunctor_data
    : psfunctor_data (psfunctor_bicat B₂ B₃) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor_data.
    - intro G; exact (comp_psfunctor G F).
    - intros G₁ G₂ η; exact (right_whisker F η).
    - intros G₁ G₂ η₁ η₂ m; exact (modification_psfunctor m).
    - intro G; exact (id2 (id_pstrans (comp_psfunctor G F))).
    - intros G₁ G₂ G₃ η₁ η₂.
      exact (cell_from_invertible_2cell (right_whisker_comp_pstrans η₁ η₂)).
  Defined.

  Lemma pre_comp_psfunctor_is_ps
    : psfunctor_laws pre_comp_psfunctor_data.
  Proof.
    repeat split.
    - intros G₁ G₂ η.
      apply id_pstrans_psfunctor.
    - intros G₁ G₂ η₁ η₂ η₃ m n.
      apply vcomp_modification_psfunctor.
    - intros G₁ G₂ η.
      use modification_eq.
      intro; cbn.
      rewrite id2_rwhisker, 2 ! id2_left.
      reflexivity.
    - intros G₁ G₂ η.
      use modification_eq.
      intro; cbn.
      rewrite lwhisker_id2, 2 ! id2_left.
      reflexivity.
    - intros G₁ G₂ G₃ G₄ η₁ η₂ η₃.
      use modification_eq.
      intro; cbn.
      rewrite lwhisker_id2, id2_rwhisker, ! id2_right.
      apply id2_left.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      rewrite id2_left, id2_right.
      reflexivity.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      rewrite id2_left, id2_right.
      reflexivity.
  Qed.

  Definition pre_comp_psfunctor
    : psfunctor (psfunctor_bicat B₂ B₃) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor.
    - exact pre_comp_psfunctor_data.
    - exact pre_comp_psfunctor_is_ps.
    - split.
      + intro G.
        use make_is_invertible_modification.
        intro.
        apply is_invertible_2cell_id₂.
      + intros G₁ G₂ G₃ η₁ η₂.
        use make_is_invertible_modification.
        intro.
        apply is_invertible_2cell_id₂.
  Defined.

  (* Derived constructions. *)
  Definition is_invertible_modification_psfunctor
             {G₁ G₂ : psfunctor B₂ B₃}
             {η₁ η₂ : pstrans G₁ G₂}
             (m : invertible_modification η₁ η₂)
    : is_invertible_modification
        (modification_psfunctor (cell_from_invertible_2cell m))
    := psfunctor_is_iso pre_comp_psfunctor m.

  Definition invertible_modification_psfunctor
             {G₁ G₂ : psfunctor B₂ B₃}
             {η₁ η₂ : pstrans G₁ G₂}
             (m : invertible_modification η₁ η₂)
    : invertible_modification (η₁ ▻ F) (η₂ ▻ F)
    := psfunctor_inv2cell pre_comp_psfunctor m.
End PreCompositionByPseudoFunctor.
