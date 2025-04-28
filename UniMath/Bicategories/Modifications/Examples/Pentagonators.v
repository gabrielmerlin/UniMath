(* ************************************************************************* *)
(** * Pentagonators between pseudo transformations.
    Gabriel Merlin
    January 2025
 *************************************************************************** *)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Bicategories.Core.Bicat.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Core.BicategoryLaws.
Require Import UniMath.Bicategories.Core.Unitors.
Require Import UniMath.Bicategories.PseudoFunctors.PseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.Composition.
Require Import UniMath.Bicategories.Transformations.PseudoTransformation.
Require Import UniMath.Bicategories.Transformations.Examples.Associativity.
Require Import UniMath.Bicategories.Transformations.Examples.Whiskering.
Require Import UniMath.Bicategories.Modifications.Modification.
Require Import UniMath.Bicategories.Modifications.Examples.Associativity.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PreCompositionByPseudoFunctor.
Require Import UniMath.Bicategories.PseudoFunctors.Examples.PostCompositionByPseudoFunctor.

Local Open Scope cat.
Local Open Scope bicategory.

Section Associativity.
  Context {B₁ B₂ B₃ B₄: bicat}
          {F₁ : psfunctor B₁ B₂}
          {F₂ : psfunctor B₂ B₃}
          {F₃ : psfunctor B₃ B₄}
          {G : psfunctor B₁ B₄}.

  Definition rassociator_to_lassociator_post_pstrans
             {σ : pstrans G (comp_psfunctor (comp_psfunctor F₃ F₂) F₁)}
             {τ : pstrans G (comp_psfunctor F₃ (comp_psfunctor F₂ F₁))}
             (m : modification (σ · rassociator_pstrans F₁ F₂ F₃) τ)
    : modification σ (τ · lassociator_pstrans F₁ F₂ F₃)
    := (vcomp2
          (vcomp2
             (vcomp2 (rinvunitor _)
                (lwhisker σ
                   (property_from_invertible_2cell
                      (rassociator_lassociator_pstrans F₁ F₂ F₃))^-1))
             (lassociator _ _ _))
          (rwhisker _ m)).

  Definition invertible_rassociator_to_lassociator_post_pstrans
             {σ : pstrans G (comp_psfunctor (comp_psfunctor F₃ F₂) F₁)}
             {τ : pstrans G (comp_psfunctor F₃ (comp_psfunctor F₂ F₁))}
             (m : invertible_modification (σ · rassociator_pstrans F₁ F₂ F₃) τ)
    : invertible_modification σ (τ · lassociator_pstrans F₁ F₂ F₃).
  Proof.
    use make_invertible_2cell.
    - exact (rassociator_to_lassociator_post_pstrans (cell_from_invertible_2cell m)).
    - unfold rassociator_to_lassociator_post_pstrans.
      is_iso; apply property_from_invertible_2cell.
  Defined.

  Definition lassociator_to_rassociator_post_pstrans
             {σ : pstrans G (comp_psfunctor F₃ (comp_psfunctor F₂ F₁))}
             {τ : pstrans G (comp_psfunctor (comp_psfunctor F₃ F₂) F₁)}
             (m : modification (σ · lassociator_pstrans F₁ F₂ F₃) τ)
    : modification σ (τ · rassociator_pstrans F₁ F₂ F₃)
    := (vcomp2
          (vcomp2
             (vcomp2 (rinvunitor _)
                (lwhisker σ
                   (property_from_invertible_2cell
                      (lassociator_rassociator_pstrans F₁ F₂ F₃))^-1))
             (lassociator _ _ _))
          (rwhisker _ m)).

  Definition invertible_lassociator_to_rassociator_post_pstrans
             {σ : pstrans G (comp_psfunctor F₃ (comp_psfunctor F₂ F₁))}
             {τ : pstrans G (comp_psfunctor (comp_psfunctor F₃ F₂) F₁)}
             (m : invertible_modification (σ · lassociator_pstrans F₁ F₂ F₃) τ)
    : invertible_modification σ (τ · rassociator_pstrans F₁ F₂ F₃).
  Proof.
    use make_invertible_2cell.
    - exact (lassociator_to_rassociator_post_pstrans (cell_from_invertible_2cell m)).
    - unfold lassociator_to_rassociator_post_pstrans.
      is_iso; apply property_from_invertible_2cell.
  Defined.

  Definition lassociator_to_rassociator_pre_pstrans
             {σ : pstrans (comp_psfunctor F₃ (comp_psfunctor F₂ F₁)) G}
             {τ : pstrans (comp_psfunctor (comp_psfunctor F₃ F₂) F₁) G}
             (m : modification σ (lassociator_pstrans F₁ F₂ F₃ · τ))
    : modification (rassociator_pstrans F₁ F₂ F₃ · σ) τ
    := (vcomp2
          (vcomp2
             (vcomp2 (lwhisker _ m) (lassociator _ _ _))
             (rwhisker τ
                (cell_from_invertible_2cell
                   (rassociator_lassociator_pstrans F₁ F₂ F₃))))
          (lunitor _)).

  Definition invertible_lassociator_to_rassociator_pre_pstrans
             {σ : pstrans (comp_psfunctor F₃ (comp_psfunctor F₂ F₁)) G}
             {τ : pstrans (comp_psfunctor (comp_psfunctor F₃ F₂) F₁) G}
             (m : invertible_modification σ (lassociator_pstrans F₁ F₂ F₃ · τ))
    : invertible_modification (rassociator_pstrans F₁ F₂ F₃ · σ) τ.
  Proof.
    use make_invertible_2cell.
    - exact (lassociator_to_rassociator_pre_pstrans (cell_from_invertible_2cell m)).
    - unfold lassociator_to_rassociator_pre_pstrans.
      is_iso; apply property_from_invertible_2cell.
  Defined.

  Definition rassociator_to_lassociator_pre_pstrans
             {σ : pstrans (comp_psfunctor (comp_psfunctor F₃ F₂) F₁) G}
             {τ : pstrans (comp_psfunctor F₃ (comp_psfunctor F₂ F₁)) G}
             (m : modification σ (rassociator_pstrans F₁ F₂ F₃ · τ))
    : modification (lassociator_pstrans F₁ F₂ F₃ · σ) τ
    := (vcomp2
          (vcomp2
             (vcomp2 (lwhisker _ m) (lassociator _ _ _))
             (rwhisker τ
                (cell_from_invertible_2cell
                   (lassociator_rassociator_pstrans F₁ F₂ F₃))))
          (lunitor _)).

  Definition invertible_rassociator_to_lassociator_pre_pstrans
             {σ : pstrans (comp_psfunctor (comp_psfunctor F₃ F₂) F₁) G}
             {τ : pstrans (comp_psfunctor F₃ (comp_psfunctor F₂ F₁)) G}
             (m : invertible_modification σ (rassociator_pstrans F₁ F₂ F₃ · τ))
    : invertible_modification (lassociator_pstrans F₁ F₂ F₃ · σ) τ.
  Proof.
    use make_invertible_2cell.
    - exact (rassociator_to_lassociator_pre_pstrans (cell_from_invertible_2cell m)).
    - unfold rassociator_to_lassociator_pre_pstrans.
      is_iso; apply property_from_invertible_2cell.
  Defined.
End Associativity.


Section Pentagonators.
  Context {B₁ B₂ B₃ B₄ B₅ : bicat}.
  Variables (F : psfunctor B₁ B₂)
            (G : psfunctor B₂ B₃)
            (H : psfunctor B₃ B₄)
            (I : psfunctor B₄ B₅).

  Definition rassociator_rassociator_pstrans_data
    : invertible_modification_data
        ((rassociator_pstrans G H I ▻ F)
         · rassociator_pstrans F (comp_psfunctor H G) I
         · (I ◅ rassociator_pstrans F G H))
        (rassociator_pstrans F G (comp_psfunctor I H)
         · rassociator_pstrans (comp_psfunctor G F) H I).
  Proof.
    intro.
    refine (comp_of_invertible_2cell
              (lwhisker_of_invertible_2cell _
                 (inv_of_invertible_2cell (psfunctor_id I _)))
              (runitor_invertible_2cell _)).
  Defined.

  Definition rassociator_rassociator_pstrans_is_modification
    : is_modification rassociator_rassociator_pstrans_data.
  Proof.
    intros X Y f.
    cbn [comp_of_invertible_2cell lwhisker_of_invertible_2cell
         rwhisker_of_invertible_2cell].
    etrans.
    { apply maponpaths. refine (!_). apply lwhisker_vcomp. }
    rewrite vassocr.
    refine (maponpaths (λ x, vcomp2 x _) _ @ _).
    {
      refine (vassocl _ _ _ @ _).
      etrans.
      { apply maponpaths, lwhisker_lwhisker_rassociator. }
      rewrite vassocl, vassoc4.
      rewrite vcomp_whisker.
      rewrite <- vassoc4, vassocl, vassoc4.
      rewrite <- lwhisker_lwhisker.
      rewrite <- vassoc4, vassocl, vassoc4.
      rewrite lwhisker_vcomp.
      rewrite (modnaturality_of
                 (cell_from_invertible_2cell
                    (left_whisker_id_pstrans I
                       (comp_psfunctor H (comp_psfunctor G F))))).
      rewrite <- lwhisker_vcomp.
      rewrite <- vassoc4, vassocr.
      refine (maponpaths (λ x, vcomp2 x _) _ @ vassocl _ _ _).
      apply rwhisker_lwhisker_rassociator.
    }
    rewrite <- vassoc4.
    refine (_ @ vassocr _ _ _ @ maponpaths (λ x, vcomp2 x _) (rwhisker_vcomp _ _ _)).
    apply maponpaths.
    rewrite <- vassoc4, vassocl.
    etrans.
    {
      do 4 apply maponpaths.
      apply runitor_triangle.
    }
    rewrite vcomp_runitor.
    rewrite vassocr, vassoc4.
    apply (maponpaths (λ x, vcomp2 x _)).
    rewrite <- left_unit_assoc.
    rewrite vassocl, lwhisker_vcomp.
    etrans.
    {
      do 2 apply maponpaths.
      refine (vassocl _ _ _ @ _).
      rewrite rinvunitor_runitor.
      apply id2_right.
    }
    apply lunitor_lwhisker.
  Qed.

  Definition rassociator_rassociator_pstrans
    : invertible_modification
        ((rassociator_pstrans G H I ▻ F)
         · rassociator_pstrans F (comp_psfunctor H G) I
         · (I ◅ rassociator_pstrans F G H))
        (rassociator_pstrans F G (comp_psfunctor I H)
         · rassociator_pstrans (comp_psfunctor G F) H I)
    := make_invertible_modification rassociator_rassociator_pstrans_data
         rassociator_rassociator_pstrans_is_modification.

  Definition inverse_pentagonator
    : invertible_modification
        (rassociator_pstrans F G (comp_psfunctor I H)
         · rassociator_pstrans (comp_psfunctor G F) H I)
        ((rassociator_pstrans G H I ▻ F)
         · rassociator_pstrans F (comp_psfunctor H G) I
         · (I ◅ rassociator_pstrans F G H))
    := inv_of_invertible_2cell rassociator_rassociator_pstrans.


  Let rwhisker_rassociator_to_rwhisker_lassociator_pre_pstrans
      {E : psfunctor B₁ B₅}
      {σ : pstrans (comp_psfunctor (comp_psfunctor I (comp_psfunctor H G)) F) E}
      {τ : pstrans (comp_psfunctor (comp_psfunctor (comp_psfunctor I H) G) F) E}
      (m : invertible_modification ((rassociator_pstrans G H I ▻ F) · σ) τ)
    : invertible_modification σ ((lassociator_pstrans G H I ▻ F) · τ).
  Proof.
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (comp_of_invertible_2cell
                    (linvunitor_invertible_2cell _)
                    (rwhisker_of_invertible_2cell σ _))
                 (rassociator_invertible_2cell _ _ _))
              (lwhisker_of_invertible_2cell _ m)).
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (psfunctor_id (pre_comp_psfunctor F) _)
                 (invertible_modification_psfunctor F _))
              (inv_of_invertible_2cell (right_whisker_comp_pstrans F _ _))).
    apply inv_of_invertible_2cell, lassociator_rassociator_pstrans.
  Defined.

  Let rwhisker_rassociator_to_rwhisker_lassociator_post_pstrans
      {E : psfunctor B₁ B₅}
      {σ : pstrans E (comp_psfunctor (comp_psfunctor (comp_psfunctor I H) G) F)}
      {τ : pstrans E (comp_psfunctor (comp_psfunctor I (comp_psfunctor H G)) F)}
      (m : invertible_modification (σ · (rassociator_pstrans G H I ▻ F)) τ)
    : invertible_modification σ (τ · (lassociator_pstrans G H I ▻ F)).
  Proof.
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (comp_of_invertible_2cell
                    (rinvunitor_invertible_2cell _)
                    (lwhisker_of_invertible_2cell σ _))
                 (lassociator_invertible_2cell _ _ _))
              (rwhisker_of_invertible_2cell _ m)).
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (psfunctor_id (pre_comp_psfunctor F) _)
                 (invertible_modification_psfunctor F _))
              (inv_of_invertible_2cell (right_whisker_comp_pstrans F _ _))).
    apply inv_of_invertible_2cell, rassociator_lassociator_pstrans.
  Defined.

  Let rwhisker_lassociator_to_rwhisker_rassociator_post_pstrans
      {E : psfunctor B₁ B₅}
      {σ : pstrans E (comp_psfunctor (comp_psfunctor (comp_psfunctor I H) G) F)}
      {τ : pstrans E (comp_psfunctor (comp_psfunctor I (comp_psfunctor H G)) F)}
      (m : invertible_modification σ (τ · (lassociator_pstrans G H I ▻ F)))
    : invertible_modification (σ · (rassociator_pstrans G H I ▻ F)) τ.
  Proof.
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (comp_of_invertible_2cell
                    (rwhisker_of_invertible_2cell _ m)
                    (rassociator_invertible_2cell _ _ _))
                 (lwhisker_of_invertible_2cell τ _))
              (runitor_invertible_2cell τ)).
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (right_whisker_comp_pstrans F _ _)
                 (invertible_modification_psfunctor F _))
              (inv_of_invertible_2cell (psfunctor_id (pre_comp_psfunctor F) _))).
    apply lassociator_rassociator_pstrans.
  Defined.

  Let lwhisker_rassociator_to_lwhisker_lassociator_post_pstrans
      {E : psfunctor B₁ B₅}
      {σ : pstrans E (comp_psfunctor I (comp_psfunctor (comp_psfunctor H G) F))}
      {τ : pstrans E (comp_psfunctor I (comp_psfunctor H (comp_psfunctor G F)))}
      (m : invertible_modification (σ · (I ◅ rassociator_pstrans F G H)) τ)
    : invertible_modification σ (τ · (I ◅ lassociator_pstrans F G H)).
  Proof.
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (comp_of_invertible_2cell
                    (rinvunitor_invertible_2cell _)
                    (lwhisker_of_invertible_2cell σ _))
                 (lassociator_invertible_2cell _ _ _))
              (rwhisker_of_invertible_2cell _ m)).
    refine (comp_of_invertible_2cell
              (comp_of_invertible_2cell
                 (inv_left_whisker_id_pstrans I _)
                 (psfunctor_invertible_modification I _))
              (inv_of_invertible_2cell (left_whisker_comp_pstrans I _ _))).
    apply inv_of_invertible_2cell, rassociator_lassociator_pstrans.
  Defined.


  Definition inverse_pentagonator_2
    : invertible_modification
        (((lassociator_pstrans G H I) ▻ F)
         · rassociator_pstrans F G (comp_psfunctor I H))
        (rassociator_pstrans F (comp_psfunctor H G) I
         · (I ◅ rassociator_pstrans F G H)
         · lassociator_pstrans (comp_psfunctor G F) H I).
  Proof.
    apply invertible_rassociator_to_lassociator_post_pstrans.
    apply (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).
    apply inv_of_invertible_2cell,
          rwhisker_rassociator_to_rwhisker_lassociator_pre_pstrans.
    apply (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).
    exact rassociator_rassociator_pstrans.
  Defined.

  Definition inverse_pentagonator_4
    : invertible_modification
        (rassociator_pstrans (comp_psfunctor G F) H I
         · (I ◅ lassociator_pstrans F G H))
        (lassociator_pstrans F G (comp_psfunctor I H)
         · ((rassociator_pstrans G H I) ▻ F)
         · rassociator_pstrans F (comp_psfunctor H G) I).
  Proof.
    refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    apply inv_of_invertible_2cell,
          invertible_rassociator_to_lassociator_pre_pstrans.
    refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    apply lwhisker_rassociator_to_lwhisker_lassociator_post_pstrans.
    exact rassociator_rassociator_pstrans.
  Defined.

  Definition inverse_pentagon_5_pstrans
    : invertible_modification
        ((I ◅ (rassociator_pstrans F G H))
         · lassociator_pstrans (comp_psfunctor G F) H I)
        (lassociator_pstrans F (comp_psfunctor H G) I
         · (lassociator_pstrans G H I ▻ F)
         · rassociator_pstrans F G (comp_psfunctor I H)).
  Proof.
    refine (comp_of_invertible_2cell _ (lassociator_invertible_2cell _ _ _)).
    apply inv_of_invertible_2cell,
          invertible_rassociator_to_lassociator_pre_pstrans.
    refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    apply invertible_rassociator_to_lassociator_post_pstrans.
    apply (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).
    apply inv_of_invertible_2cell,
          rwhisker_rassociator_to_rwhisker_lassociator_pre_pstrans.
    apply (comp_of_invertible_2cell (lassociator_invertible_2cell _ _ _)).
    exact rassociator_rassociator_pstrans.
  Defined.

  Definition inverse_pentagonator_7
    : invertible_modification
        (lassociator_pstrans F G (comp_psfunctor I H)
         · (rassociator_pstrans G H I ▻ F))
        (rassociator_pstrans (comp_psfunctor G F) H I
         · (I ◅ lassociator_pstrans F G H)
         · lassociator_pstrans F (comp_psfunctor H G) I).
  Proof.
    apply invertible_rassociator_to_lassociator_pre_pstrans.
    refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    apply invertible_rassociator_to_lassociator_post_pstrans.
    refine (comp_of_invertible_2cell _ (rassociator_invertible_2cell _ _ _)).
    apply lwhisker_rassociator_to_lwhisker_lassociator_post_pstrans.
    exact rassociator_rassociator_pstrans.
  Defined.

  Definition pentagonator
    : invertible_modification
        (lassociator_pstrans (comp_psfunctor G F) H I
         · lassociator_pstrans F G (comp_psfunctor I H))
        ((I ◅ lassociator_pstrans F G H)
         · lassociator_pstrans F (comp_psfunctor H G) I
         · (lassociator_pstrans G H I ▻ F)).
  Proof.
    apply rwhisker_rassociator_to_rwhisker_lassociator_post_pstrans.
    apply (comp_of_invertible_2cell (rassociator_invertible_2cell _ _ _)).
    apply invertible_rassociator_to_lassociator_pre_pstrans.
    exact (comp_of_invertible_2cell inverse_pentagonator_7
             (rassociator_invertible_2cell _ _ _)).
  Defined.

  Definition lassociator_lassociator_pstrans
    : invertible_modification
        ((I ◅ lassociator_pstrans F G H)
         · lassociator_pstrans F (comp_psfunctor H G) I
         · (lassociator_pstrans G H I ▻ F))
        (lassociator_pstrans (comp_psfunctor G F) H I
         · lassociator_pstrans F G (comp_psfunctor I H))
    := inv_of_invertible_2cell pentagonator.

  Definition pentagon_2_pstrans
    : invertible_modification
        ((I ◅ lassociator_pstrans F G H)
         · lassociator_pstrans F (comp_psfunctor H G) I)
        (lassociator_pstrans (comp_psfunctor G F) H I
         · lassociator_pstrans F G (comp_psfunctor I H)
         · (rassociator_pstrans G H I ▻ F)).
  Proof.
    apply inv_of_invertible_2cell, rwhisker_lassociator_to_rwhisker_rassociator_post_pstrans.
    exact pentagonator.
  Defined.
End Pentagonators.
