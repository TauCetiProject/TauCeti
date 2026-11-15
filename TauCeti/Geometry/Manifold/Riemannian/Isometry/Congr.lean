/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group

/-!
# Transporting the Riemannian isometry group along a Riemannian isometry

A smooth Riemannian isometry `Φ : RiemannianIsometry I J M N` conjugates Riemannian
self-isometries of `M` into Riemannian self-isometries of `N` by `Ψ ↦ Φ ∘ Ψ ∘ Φ⁻¹`. Because
this preserves composition, it is a group isomorphism `Isom I M ≃* Isom J N` between the
isometry groups built in `TauCeti.Geometry.Manifold.Riemannian.Isometry.Group`.

This file records `TauCeti.RiemannianIsometry.isomCongr`, its pointwise action, its
functoriality (`isomCongr_refl`, `isomCongr_trans`, `isomCongr_symm`), and its naturality
against the forgetful homomorphism `toDiff` to the diffeomorphism group through
`Diffeomorph.diffCongr`.

## Main definitions

* `TauCeti.RiemannianIsometry.isomCongr Φ`: the group isomorphism `Isom I M ≃* Isom J N`
  conjugating by `Φ : RiemannianIsometry I J M N`.

## Main results

* `TauCeti.RiemannianIsometry.isomCongr_apply_apply`: the pointwise action
  `isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y))`.
* `TauCeti.RiemannianIsometry.isomCongr_refl`,
  `TauCeti.RiemannianIsometry.isomCongr_trans`, and
  `TauCeti.RiemannianIsometry.isomCongr_symm`: functoriality on the groupoid of Riemannian
  isometries.
* `TauCeti.RiemannianIsometry.toDiff_comp_isomCongr` and
  `TauCeti.RiemannianIsometry.toDiffeomorph_isomCongr`: naturality of `isomCongr` against the
  forgetful homomorphism `toDiff` to `Diff _ _ ∞`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- Conjugation by a smooth Riemannian isometry `Φ : RiemannianIsometry I J M N` as a group
isomorphism between the Riemannian isometry groups: `isomCongr Φ Ψ = Φ ∘ Ψ ∘ Φ⁻¹`. -/
def isomCongr (Φ : RiemannianIsometry I J M N) : Isom I M ≃* Isom J N where
  toFun Ψ := (Φ.symm.trans Ψ).trans Φ
  invFun Ξ := (Φ.trans Ξ).trans Φ.symm
  left_inv Ψ := by
    ext x
    simp
  right_inv Ξ := by
    ext y
    simp
  map_mul' Ψ₁ Ψ₂ := by
    ext y
    simp

/-- The underlying Riemannian isometry of `isomCongr Φ Ψ` is `(Φ.symm.trans Ψ).trans Φ`. -/
theorem isomCongr_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    isomCongr Φ Ψ = (Φ.symm.trans Ψ).trans Φ := (rfl)

/-- The conjugating isomorphism acts pointwise by `isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y))`. -/
@[simp, grind =]
theorem isomCongr_apply_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) (y : N) :
    isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y)) := by
  simp [isomCongr_apply]

/-- Conjugating by the identity Riemannian isometry is the identity isomorphism. -/
@[simp]
theorem isomCongr_refl :
    isomCongr (RiemannianIsometry.refl I M) = MulEquiv.refl (Isom I M) := by
  ext Ψ x
  simp

/-- Conjugation is functorial: conjugating by a composite Riemannian isometry is the composite
of the conjugating isomorphisms. -/
@[simp]
theorem isomCongr_trans (Φ : RiemannianIsometry I J M N) (Φ' : RiemannianIsometry J K N P) :
    isomCongr (Φ.trans Φ') = (isomCongr Φ).trans (isomCongr Φ') := by
  ext Ψ z
  simp

/-- The isomorphism conjugating by `Φ.symm` is the inverse of the one conjugating by `Φ`. -/
@[simp, grind =]
theorem isomCongr_symm (Φ : RiemannianIsometry I J M N) :
    (isomCongr Φ).symm = isomCongr Φ.symm := by
  ext Ξ x
  simp [isomCongr]

/-- Naturality of `isomCongr` against the forgetful homomorphism `toDiff` to the diffeomorphism
group: conjugating Riemannian isometries by `Φ` and forgetting the metric condition equals
forgetting the metric condition and conjugating diffeomorphisms through
`Diffeomorph.diffCongr`. -/
theorem toDiff_comp_isomCongr (Φ : RiemannianIsometry I J M N) :
    toDiff.comp (isomCongr Φ).toMonoidHom =
      (Diffeomorph.diffCongr Φ.toDiffeomorph).toMonoidHom.comp toDiff := by
  ext Ψ y
  simp [coe_symm]

/-- Forgetting the metric condition sends `isomCongr Φ Ψ` to the conjugate `diffCongr` of the
underlying diffeomorphisms; the elementwise shadow of `toDiff_comp_isomCongr`. -/
@[simp]
theorem toDiffeomorph_isomCongr (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    (isomCongr Φ Ψ).toDiffeomorph = Φ.toDiffeomorph.diffCongr Ψ.toDiffeomorph := by
  simpa using DFunLike.congr_fun (toDiff_comp_isomCongr Φ) Ψ

end TauCeti.RiemannianIsometry

end
