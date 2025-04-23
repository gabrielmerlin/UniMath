(************************************************************************

Morphisms for inverters

************************************************************************)
Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Subcategory.Full.
Require Import UniMath.Bicategories.Core.Bicat. Import Bicat.Notations.
Require Import UniMath.Bicategories.Core.Invertible_2cells.
Require Import UniMath.Bicategories.Limits.Inverters.

Local Open Scope cat.

(**

  Suppose, we have a diagram as follows


                        ---- f₁ ---->
     p₁ ---- i₁ ----> x₁     V        y₁
                        ---- g₁ ---->
                      |               |
                      |               |
                      l₁     ≃        l₂
                      |               |
                      |               |
                      V               V
                        ---- f₂ ---->
     p₂ ---- i₂ ----> x₂     V        y₂
                        ---- g₂ ---->


  where both rows are inverters cones.
  If the bottom row is an inverter, then there exists a morphism from p₁ to p₂
  and an invertible cell filling the so-formed square.

*)
Section InverterMorphism.
  Context {B : bicat}
          {x₁ y₁ x₂ y₂ : B}
          {f₁ g₁ : x₁ --> y₁}
          {α₁ : f₁ ==> g₁}
          {f₂ g₂ : x₂ --> y₂}
          {α₂ : f₂ ==> g₂}
          (lx : x₁ --> x₂)
          (ly : y₁ --> y₂)
          (γ₂ : invertible_2cell (lx · f₂) (f₁ · ly))
          (γ₃ : invertible_2cell (lx · g₂) (g₁ · ly))
          (pα : (lx ◃ α₂) • γ₃ = γ₂ • (α₁ ▹ ly)).

  Let eq_hlxα₂ {q : B} (h : hom q x₁)
    : rassociator _ _ _ • (((h ◃ γ₂) • (lassociator _ _ _ • (h ◃ α₁ ▹ ly)) • rassociator _ _ _ • (h ◃ γ₃^-1)) • lassociator _ _ _)
      = h · lx ◃ α₂.
  Proof.
    rewrite <- rwhisker_lwhisker.
    rewrite <- vassoc4.
    rewrite lassociator_rassociator, id2_right.
    rewrite 2 ! lwhisker_vcomp.
    rewrite <- pα.
    rewrite vassocl.
    rewrite vcomp_rinv, id2_right.
    rewrite lwhisker_lwhisker.
    rewrite vassocr.
    rewrite rassociator_lassociator.
    apply id2_left.
  Qed.

  Definition inverter_cone_is_invertible_cell_morphism
             (cone : inverter_cone α₁)
    : is_invertible_2cell (inverter_cone_pr1 cone · lx ◃ α₂).
  Proof.
    use eq_is_invertible_2cell.
    - exact (rassociator _ _ _
             • (((inverter_cone_pr1 cone ◃ γ₂)
                • (lassociator _ _ _ • (inverter_cone_pr1 cone ◃ α₁ ▹ ly))
                • rassociator _ _ _ • (inverter_cone_pr1 cone ◃ γ₃^-1))
             • lassociator _ _ _)).
    - abstract
        (rewrite <- rwhisker_lwhisker ;
         rewrite <- vassoc4 ;
         rewrite lassociator_rassociator, id2_right ;
         rewrite 2 ! lwhisker_vcomp ;
         rewrite <- pα ;
         rewrite vassocl ;
         rewrite vcomp_rinv, id2_right ;
         rewrite lwhisker_lwhisker ;
         rewrite vassocr ;
         rewrite rassociator_lassociator ;
         apply id2_left).
    - set (cell := _ ◃ α₁).
      is_iso.
      { apply property_from_invertible_2cell. }
      apply inverter_cone_is_invertible_cell.
  Defined.

  Definition inverter_cone_morphism
             (cone : inverter_cone α₁)
    : inverter_cone α₂.
  Proof.
    use make_inverter_cone.
    - exact cone.
    - exact (inverter_cone_pr1 cone · lx).
    - apply inverter_cone_is_invertible_cell_morphism.
  Defined.

  Definition universal_inverter_cat_morphism (q : B)
    : functor
        (@universal_inverter_cat B _ _ _ _ α₁ q)
        (@universal_inverter_cat B _ _ _ _ α₂ q).
  Proof.
    use full_sub_category_functor.
    - exact (post_comp _ lx).
    - intro h; cbn; intro inv_hα₁.
      exact (inverter_cone_is_invertible_cell
              (inverter_cone_morphism (make_inverter_cone q h inv_hα₁))).
  Defined.

  Section MorphismToInverter.
    Context {cone : inverter_cone α₂}
            (H : has_inverter_ump cone).

    Definition inverter_ump_mor_morphism
               {i : B}
               (m : i --> x₁)
               (inv_mα : is_invertible_2cell (m ◃ α₁))
      : i --> cone
      := pr1 H (inverter_cone_morphism (make_inverter_cone i m inv_mα)).

    Definition inverter_ump_mor_pr1_morphism
               {i : B}
               (m : i --> x₁)
               (inv_mα : is_invertible_2cell (m ◃ α₁))
      : invertible_2cell
          (inverter_ump_mor_morphism m inv_mα · inverter_cone_pr1 cone)
          (m · lx)
      := inverter_1cell_pr1
           (pr1 H (inverter_cone_morphism (make_inverter_cone i m inv_mα))).
  End MorphismToInverter.
End InverterMorphism.
