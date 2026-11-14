/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Monoid

/-!
# Product constructions for smooth monoid morphisms

Factor inclusions and universal product pairings for bundled smooth multiplicative and additive
monoid morphisms, complementing `ContMDiffMonoidMorphism.fst` and `ContMDiffMonoidMorphism.snd`.
-/

public section

open Manifold
open scoped ContDiff Manifold

namespace ContMDiffMonoidMorphism

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Monoid G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Monoid G']

/-- The inclusion of the first factor into a product as a smooth monoid morphism. -/
@[to_additive
  /-- The inclusion of the first summand into a product as a smooth additive monoid morphism. -/]
def inl : ContMDiffMonoidMorphism I (I.prod I') n G (G × G') where
  toMonoidHom := MonoidHom.inl G G'
  contMDiff_toFun := contMDiff_id.prodMk contMDiff_const

@[to_additive (attr := simp)]
theorem inl_apply (x : G) :
    inl (I := I) (I' := I') (n := n) (G' := G') x = (x, 1) :=
  (rfl)

@[to_additive (attr := simp)]
theorem fst_comp_inl :
    (fst (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inl = id := by
  apply DFunLike.coe_injective
  funext x
  simp

@[to_additive (attr := simp)]
theorem snd_comp_inl :
    (snd (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inl = 1 := by
  apply DFunLike.coe_injective
  funext x
  simp
  rfl

/-- The inclusion of the second factor into a product as a smooth monoid morphism. -/
@[to_additive
  /-- The inclusion of the second summand into a product as a smooth additive monoid morphism. -/]
def inr : ContMDiffMonoidMorphism I' (I.prod I') n G' (G × G') where
  toMonoidHom := MonoidHom.inr G G'
  contMDiff_toFun := contMDiff_const.prodMk contMDiff_id

@[to_additive (attr := simp)]
theorem inr_apply (y : G') :
    inr (I := I) (I' := I') (n := n) (G := G) y = (1, y) :=
  (rfl)

@[to_additive (attr := simp)]
theorem fst_comp_inr :
    (fst (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inr = 1 := by
  apply DFunLike.coe_injective
  funext x
  simp
  rfl

@[to_additive (attr := simp)]
theorem snd_comp_inr :
    (snd (I := I) (I' := I') (n := n) (G := G) (G' := G')).comp inr = id := by
  apply DFunLike.coe_injective
  funext x
  simp

section Prod

variable {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {G'' : Type*} [TopologicalSpace G''] [ChartedSpace H'' G''] [Monoid G'']

/-- Pairing two smooth monoid morphisms into a product. -/
@[to_additive /-- Pairing two smooth additive monoid morphisms into a product. -/]
def prod (φ : ContMDiffMonoidMorphism I'' I n G'' G)
    (ψ : ContMDiffMonoidMorphism I'' I' n G'' G') :
    ContMDiffMonoidMorphism I'' (I.prod I') n G'' (G × G') where
  toMonoidHom := φ.toMonoidHom.prod ψ.toMonoidHom
  contMDiff_toFun := φ.contMDiff_toFun.prodMk ψ.contMDiff_toFun

@[to_additive (attr := simp)]
theorem prod_apply (φ : ContMDiffMonoidMorphism I'' I n G'' G)
    (ψ : ContMDiffMonoidMorphism I'' I' n G'' G') (x : G'') :
    φ.prod ψ x = (φ x, ψ x) :=
  (rfl)

@[to_additive (attr := simp)]
theorem fst_comp_prod (φ : ContMDiffMonoidMorphism I'' I n G'' G)
    (ψ : ContMDiffMonoidMorphism I'' I' n G'' G') :
    fst.comp (φ.prod ψ) = φ := by
  apply DFunLike.coe_injective
  funext x
  simp

@[to_additive (attr := simp)]
theorem snd_comp_prod (φ : ContMDiffMonoidMorphism I'' I n G'' G)
    (ψ : ContMDiffMonoidMorphism I'' I' n G'' G') :
    snd.comp (φ.prod ψ) = ψ := by
  apply DFunLike.coe_injective
  funext x
  simp

end Prod

end ContMDiffMonoidMorphism
