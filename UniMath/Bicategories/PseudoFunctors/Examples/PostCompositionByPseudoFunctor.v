(* ******************************************************************************* *)
(** * Post-composition by a pseudofunctor is a pseudofunctor
    Gabriel Merlin
    January 2025
 ********************************************************************************* *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.PseudoFunctors.Display.PseudoFunctorBicat.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Import PseudoFunctor.Notations.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.

Local Open Scope cat.

Section PostCompositionByPseudoFunctor.
  Context {B₁ B₂ B₃ : bicat}
          (G : psfunctor B₂ B₃).

  Definition inv_left_whisker_id_pstrans
             (F : psfunctor B₁ B₂)
    : invertible_modification (id_pstrans (comp_psfunctor G F)) (G ◅ id_pstrans F).
  Proof.
    use make_invertible_modification.
    - exact (λ X, psfunctor_id G (F X)).
    - abstract
        (intros X Y f; cbn ;
         refine (!_) ;
         rewrite psfunctor_vcomp ;
         rewrite vassocr, vassoc4 ;
         rewrite psfunctor_F_lunitor ;
         rewrite 2 ! vassoc4 ;
         rewrite vcomp_rinv, id2_right ;
         rewrite rwhisker_vcomp ;
         rewrite vcomp_rinv, id2_rwhisker, id2_left ;
         rewrite psfunctor_rinvunitor ;
         rewrite <- vassoc4 ;
         rewrite vcomp_rinv, id2_right ;
         apply vassocr).
  Defined.

  Definition left_whisker_id_pstrans
             (F : psfunctor B₁ B₂)
    : invertible_modification (G ◅ id_pstrans F) (id_pstrans (comp_psfunctor G F))
    := inv_of_invertible_2cell (inv_left_whisker_id_pstrans F).


  Definition left_whisker_comp_pstrans_data
             {F₁ F₂ F₃ : psfunctor B₁ B₂}
             (η : pstrans F₁ F₂)
             (θ : pstrans F₂ F₃)
    : invertible_modification_data (comp_pstrans (G ◅ η) (G ◅ θ))
        (G ◅ (comp_pstrans η θ))
    := (λ X, psfunctor_comp G (η X) (θ X)).

  Definition left_whisker_comp_pstrans_is_modification
             {F₁ F₂ F₃ : psfunctor B₁ B₂}
             (η : pstrans F₁ F₂)
             (θ : pstrans F₂ F₃)
    : is_modification (left_whisker_comp_pstrans_data η θ).
  Proof.
    intros X Y f; cbn.
    refine (vassocl _ _ _ @ _ @ vassocl _ _ _).
    apply rhs_right_inv_cell.
    rewrite vassocl.
    refine (maponpaths _ (! psfunctor_rassociator G _ _ _) @ _).
    rewrite psfunctor_vcomp, vassoc4, vassocr.
    apply (maponpaths (λ x, vcomp2 x _)).
    rewrite vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite vassocr, rwhisker_vcomp.
      rewrite vassocl, vcomp_linv, id2_right.
      rewrite <- rwhisker_vcomp.
      rewrite vassocl, <- psfunctor_rwhisker.
      apply vassocr.
    }
    rewrite psfunctor_vcomp, vassoc4, vassocr.
    apply (maponpaths (λ x, vcomp2 x _)).
    rewrite vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite vassocr.
      refine (!_).
      apply psfunctor_lassociator.
    }
    rewrite psfunctor_vcomp, vassoc4, vassocr.
    apply (maponpaths (λ x, vcomp2 x _)).
    rewrite vassocl.
    etrans.
    {
      apply maponpaths.
      rewrite vassocr, lwhisker_vcomp.
      rewrite vassocl, vcomp_linv, id2_right.
      rewrite <- lwhisker_vcomp, vassocl.
      rewrite <- psfunctor_lwhisker.
      apply vassocr.
    }
    rewrite psfunctor_vcomp, vassoc4, vassocr.
    apply (maponpaths (λ x, vcomp2 x _)).
    rewrite 2 ! vassocr.
    refine (!_).
    apply psfunctor_rassociator.
  Qed.

  Definition left_whisker_comp_pstrans
             {F₁ F₂ F₃ : psfunctor B₁ B₂}
             (η : pstrans F₁ F₂)
             (θ : pstrans F₂ F₃)
    : invertible_modification (comp_pstrans (G ◅ η) (G ◅ θ)) (G ◅ (comp_pstrans η θ))
    := make_invertible_modification (left_whisker_comp_pstrans_data η θ)
         (left_whisker_comp_pstrans_is_modification η θ).

  (** Left whiskering of a modification by a pseudofunctor. *)
  Definition psfunctor_modification
             {F₁ F₂ : psfunctor B₁ B₂}
             {η₁ η₂ : pstrans F₁ F₂}
             (m : modification η₁ η₂)
    : modification (G ◅ η₁) (G ◅ η₂).
  Proof.
    use make_modification.
    - intro X.
      exact (psfunctor_on_cells G (m X)).
    - intros X Y f; cbn.
      rewrite 2 ! vassocr.
      rewrite <- psfunctor_rwhisker.
      apply rhs_right_inv_cell.
      rewrite vassocl.
      rewrite <- psfunctor_lwhisker.
      rewrite vassocr.
      rewrite vassocl with (z := cell_from_invertible_2cell (psfunctor_comp G (# F₁ f) (η₁ Y))).
      rewrite vcomp_linv, id2_right.
      rewrite vassocl.
      rewrite <- psfunctor_vcomp.
      rewrite modnaturality_of.
      rewrite psfunctor_vcomp.
      rewrite vassocr.
      reflexivity.
  Defined.

  Lemma vcomp_psfunctor_modification
        {F₁ F₂ : psfunctor B₁ B₂}
        {η₁ η₂ η₃ : pstrans F₁ F₂}
        (m₁ : modification η₁ η₂)
        (m₂ : modification η₂ η₃)
    : psfunctor_modification (vcomp2 m₁ m₂) =
      vcomp2 (psfunctor_modification m₁) (psfunctor_modification m₂).
  Proof.
    use modification_eq.
    intro; cbn.
    apply psfunctor_vcomp.
  Qed.

  Lemma psfunctor_id_pstrans
        {F₁ F₂ : psfunctor B₁ B₂}
        (η : pstrans F₁ F₂)
    : psfunctor_modification (id2 η) = id2 (G ◅ η).
  Proof.
    use modification_eq.
    intro; cbn.
    apply psfunctor_id2.
  Qed.


  Definition post_comp_psfunctor_data
    : psfunctor_data (psfunctor_bicat B₁ B₂) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor_data.
    - intro F; exact (comp_psfunctor G F).
    - intros F₁ F₂ η; exact (left_whisker G η).
    - intros F₁ F₂ η₁ η₂ m; exact (psfunctor_modification m).
    - intro F; exact (cell_from_invertible_2cell (inv_left_whisker_id_pstrans F)).
    - intros F₁ F₂ F₃ η₁ η₂.
      exact (cell_from_invertible_2cell (left_whisker_comp_pstrans η₁ η₂)).
  Defined.

  Lemma post_comp_psfunctor_is_ps
    : psfunctor_laws post_comp_psfunctor_data.
  Proof.
    repeat split.
    - intros F₁ F₂ η.
      apply psfunctor_id_pstrans.
    - intros F₁ F₂ η₁ η₂ η₃ m n.
      apply vcomp_psfunctor_modification.
    - intros F₁ F₂ η.
      use modification_eq.
      intro; cbn.
      apply psfunctor_lunitor.
    - intros F₁ F₂ η.
      use modification_eq.
      intro; cbn.
      apply psfunctor_runitor.
    - intros F₁ F₂ F₃ F₄ η₁ η₂ η₃.
      use modification_eq.
      intro; cbn.
      apply psfunctor_lassociator.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      apply psfunctor_lwhisker.
    - intros G₁ G₂ G₃ η₁ η₂₁ η₂₂ m.
      use modification_eq.
      intro; cbn.
      apply psfunctor_rwhisker.
  Qed.

  Definition post_comp_psfunctor
    : psfunctor (psfunctor_bicat B₁ B₂) (psfunctor_bicat B₁ B₃).
  Proof.
    use make_psfunctor.
    - exact post_comp_psfunctor_data.
    - exact post_comp_psfunctor_is_ps.
    - split.
      + intro F.
        exact (property_from_invertible_2cell (inv_left_whisker_id_pstrans F)).
      + intros F₁ F₂ F₃ η₁ η₂.
        exact (property_from_invertible_2cell (left_whisker_comp_pstrans η₁ η₂)).
  Defined.

  (* Derived constructions. *)
  Definition is_invertible_psfunctor_modification
             {F₁ F₂ : psfunctor B₁ B₂}
             {η₁ η₂ : pstrans F₁ F₂}
             (m : invertible_modification η₁ η₂)
    : is_invertible_modification
        (psfunctor_modification (cell_from_invertible_2cell m))
    := psfunctor_is_iso post_comp_psfunctor m.

  Definition psfunctor_invertible_modification
             {F₁ F₂ : psfunctor B₁ B₂}
             {η₁ η₂ : pstrans F₁ F₂}
             (m : invertible_modification η₁ η₂)
    : invertible_modification (G ◅ η₁) (G ◅ η₂)
    := psfunctor_inv2cell post_comp_psfunctor m.
End PostCompositionByPseudoFunctor.
