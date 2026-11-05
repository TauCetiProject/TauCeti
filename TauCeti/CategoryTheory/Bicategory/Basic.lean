/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Coherence of the unitor isomorphisms `X ≫ 𝟙 b ≅ 𝟙 a ≫ X`

For a `1`-morphism `X : a ⟶ b` in a bicategory, `ρ_ X ≪≫ (λ_ X).symm : X ≫ 𝟙 b ≅ 𝟙 a ≫ X` is
the naturality isomorphism of an identity component. This file records the coherence
conditions it satisfies when it serves as the naturality isomorphisms of a strong
transformation with identity components, or as the components of a modification between
whiskerings of such transformations.

These conditions are equations between composites of unitors and associators, which `simp`
or `bicategory` prove for `1`-morphisms of `B`. They are stated separately for goals whose
sources and targets agree with those of `B` only after unfolding definitions, such as
`((𝟭 Γ).toPseudofunctor.comp F).obj x` and `F.obj x`; there `simp` cannot rewrite, while these
lemmas apply by unification. For the same reason the unit and composition conditions take the
comparison `2`-cells `e` and `e'` as arguments, with hypotheses that they are identities.

## Main statements

* `CategoryTheory.Bicategory.rightUnitor_trans_leftUnitor_symm_naturality`: naturality in `X`;
* `CategoryTheory.Bicategory.rightUnitor_trans_leftUnitor_symm_naturality_id`,
  `CategoryTheory.Bicategory.rightUnitor_trans_leftUnitor_symm_naturality_comp`: the unit and
  composition conditions of a strong transformation with identity components.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): strong transformations and
  modifications.
-/

public section

namespace CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

/-- The isomorphisms `ρ_ X ≪≫ (λ_ X).symm : X ≫ 𝟙 b ≅ 𝟙 a ≫ X` are natural in `X`. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality {a b : B} {X Y : a ⟶ b} (Θ : X ⟶ Y) :
    Θ ▷ 𝟙 b ≫ (ρ_ Y ≪≫ (λ_ Y).symm).hom = (ρ_ X ≪≫ (λ_ X).symm).hom ≫ 𝟙 a ◁ Θ := by
  simp

/-- The unit condition of a strong transformation with identity components and naturality
isomorphisms `ρ_ ≪≫ (λ_).symm`, for unit comparisons `e` and `e'` that are identities. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_id {a : B} (e e' : 𝟙 a ⟶ 𝟙 a)
    (he : e = 𝟙 _) (he' : e' = 𝟙 _) :
    (ρ_ (𝟙 a) ≪≫ (λ_ (𝟙 a)).symm).hom ≫ 𝟙 a ◁ e =
      e' ▷ 𝟙 a ≫ (λ_ (𝟙 a)).hom ≫ (ρ_ (𝟙 a)).inv := by
  subst he he'
  simp [unitors_equal]

/-- The composition condition of a strong transformation with identity components and
naturality isomorphisms `ρ_ ≪≫ (λ_).symm`, for composition comparisons `e` and `e'` that are
identities. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_comp {a b c : B} (u : a ⟶ b) (v : b ⟶ c)
    (e e' : u ≫ v ⟶ u ≫ v) (he : e = 𝟙 _) (he' : e' = 𝟙 _) :
    (ρ_ (u ≫ v) ≪≫ (λ_ (u ≫ v)).symm).hom ≫ 𝟙 a ◁ e =
      e' ▷ 𝟙 c ≫ (α_ u v (𝟙 c)).hom ≫ u ◁ (ρ_ v ≪≫ (λ_ v).symm).hom ≫ (α_ u (𝟙 b) v).inv ≫
        (ρ_ u ≪≫ (λ_ u).symm).hom ▷ v ≫ (α_ (𝟙 a) u v).hom := by
  subst he he'
  simp

/-- The isomorphisms `ρ_ ≪≫ (λ_).symm` are compatible with a `2`-morphism
`N : X ≫ v ⟶ u ≫ Y` whiskered by identities: this is the naturality condition of the
modification with these components between whiskerings by strong transformations with
identity components. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_whisker {a b a' b' : B} (X : a ⟶ b)
    (Y : a' ⟶ b') (u : a ⟶ a') (v : b ⟶ b') (N : X ≫ v ⟶ u ≫ Y) :
    X ◁ (ρ_ v ≪≫ (λ_ v).symm).hom ≫ ((α_ _ _ _).inv ≫ (ρ_ X ≪≫ (λ_ X).symm).hom ▷ v ≫
        (α_ _ _ _).hom ≫ 𝟙 a ◁ N ≫ (α_ _ _ _).inv) =
      ((α_ _ _ _).inv ≫ N ▷ 𝟙 b' ≫ (α_ _ _ _).hom ≫ u ◁ (ρ_ Y ≪≫ (λ_ Y).symm).hom ≫
        (α_ _ _ _).inv) ≫ (ρ_ u ≪≫ (λ_ u).symm).hom ▷ Y := by
  simp

/-- The isomorphisms `ρ_ ≪≫ (λ_).symm` are compatible with `(λ_ (𝟙 _)).inv`: this is the
naturality condition of the modification `𝟙 _ ≅ τ ≫ σ` with components `(λ_ (𝟙 _)).symm`, for
strong transformations `τ` and `σ` with identity components. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor_inv {a b : B} (X : a ⟶ b) :
    X ◁ (λ_ (𝟙 b)).inv ≫ ((α_ _ _ _).inv ≫ (ρ_ X ≪≫ (λ_ X).symm).hom ▷ 𝟙 b ≫
        (α_ _ _ _).hom ≫ 𝟙 a ◁ (ρ_ X ≪≫ (λ_ X).symm).hom ≫ (α_ _ _ _).inv) =
      (ρ_ X ≪≫ (λ_ X).symm).hom ≫ (λ_ (𝟙 a)).inv ▷ X := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  bicategory

/-- The isomorphisms `ρ_ ≪≫ (λ_).symm` are compatible with `(λ_ (𝟙 _)).hom`: this is the
naturality condition of the modification `σ ≫ τ ≅ 𝟙 _` with components `λ_ (𝟙 _)`, for
strong transformations `τ` and `σ` with identity components. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor {a b : B} (X : a ⟶ b) :
    X ◁ (λ_ (𝟙 b)).hom ≫ (ρ_ X ≪≫ (λ_ X).symm).hom =
      ((α_ _ _ _).inv ≫ (ρ_ X ≪≫ (λ_ X).symm).hom ▷ 𝟙 b ≫
        (α_ _ _ _).hom ≫ 𝟙 a ◁ (ρ_ X ≪≫ (λ_ X).symm).hom ≫ (α_ _ _ _).inv) ≫
        (λ_ (𝟙 a)).hom ▷ X := by
  simp

end CategoryTheory.Bicategory
