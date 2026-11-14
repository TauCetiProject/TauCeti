/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Congr
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Group

/-!
# Transporting the isometry group along a Riemannian isometry

A smooth Riemannian isometry `Φ : RiemannianIsometry I J M N` conjugates self-isometries of `M`
into self-isometries of `N` by `Ψ ↦ Φ ∘ Ψ ∘ Φ⁻¹`. Because conjugation preserves composition, it
defines a group isomorphism `Isom I M ≃* Isom J N` between the Riemannian isometry groups built in
`TauCeti.Geometry.Manifold.Riemannian.Isometry.Group`. This file records that isomorphism,
`TauCeti.RiemannianIsometry.isomCongr`, its pointwise action, its functoriality under
`RiemannianIsometry.refl`, `RiemannianIsometry.trans` and `RiemannianIsometry.symm`, and its
compatibility with the forgetful homomorphism `TauCeti.RiemannianIsometry.toDiff` through
`Diffeomorph.diffCongr`.

The construction is the Riemannian-isometry analogue of `Diffeomorph.diffCongr`
(`TauCeti/Geometry/Diffeomorphism/Congr.lean`) and `Equiv.permCongr`
(`Mathlib/Logic/Equiv/Defs.lean`).

## Main definitions

* `TauCeti.RiemannianIsometry.isomCongr Φ`: the group isomorphism `Isom I M ≃* Isom J N`
  conjugating by a Riemannian isometry `Φ : RiemannianIsometry I J M N`.

## Main results

* `TauCeti.RiemannianIsometry.isomCongr_apply_apply`: the pointwise action
  `Φ.isomCongr Ψ y = Φ (Ψ (Φ.symm y))`.
* `TauCeti.RiemannianIsometry.isomCongr_refl`, `isomCongr_trans`, `isomCongr_symm`: functoriality
  on the groupoid of Riemannian isometries.
* `TauCeti.RiemannianIsometry.toDiff_comp_isomCongr` and `toDiffeomorph_isomCongr`: naturality
  against forgetting the metric condition to `Diff`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapter 2.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- Conjugation by a smooth Riemannian isometry `Φ : RiemannianIsometry I J M N` as a group
isomorphism between the Riemannian isometry groups: `Φ.isomCongr Ψ = Φ ∘ Ψ ∘ Φ⁻¹`. -/
def isomCongr (Φ : RiemannianIsometry I J M N) : Isom I M ≃* Isom J N where
  toFun Ψ := (Φ.symm.trans Ψ).trans Φ
  invFun Θ := (Φ.trans Θ).trans Φ.symm
  left_inv Ψ := by
    ext x
    simp
  right_inv Θ := by
    ext y
    simp
  map_mul' Ψ₁ Ψ₂ := by
    ext y
    simp

/-- The underlying Riemannian isometry of `Φ.isomCongr Ψ` is `(Φ.symm.trans Ψ).trans Φ`. -/
theorem isomCongr_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    Φ.isomCongr Ψ = (Φ.symm.trans Ψ).trans Φ :=
  (rfl)

/-- The conjugating isomorphism acts pointwise by `Φ.isomCongr Ψ y = Φ (Ψ (Φ.symm y))`. -/
@[simp, grind =]
theorem isomCongr_apply_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) (y : N) :
    Φ.isomCongr Ψ y = Φ (Ψ (Φ.symm y)) := by
  simp [isomCongr_apply]

/-- Conjugation by `Φ` commutes with inversion: `(Φ.isomCongr Ψ)⁻¹ = Φ.isomCongr Ψ⁻¹`. -/
theorem isomCongr_inv (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    (Φ.isomCongr Ψ)⁻¹ = Φ.isomCongr Ψ⁻¹ :=
  (map_inv Φ.isomCongr Ψ).symm

/-- Conjugating by the identity Riemannian isometry is the identity group isomorphism. -/
@[simp]
theorem isomCongr_refl :
    (RiemannianIsometry.refl I M).isomCongr = MulEquiv.refl (Isom I M) := by
  ext Ψ x
  simp

/-- Conjugation is functorial: conjugating by a composite Riemannian isometry is the composite of
the conjugating group isomorphisms. -/
@[simp]
theorem isomCongr_trans (Φ : RiemannianIsometry I J M N) (Ψ : RiemannianIsometry J K N P) :
    (Φ.trans Ψ).isomCongr = Φ.isomCongr.trans Ψ.isomCongr := by
  ext Θ z
  simp

/-- The group isomorphism conjugating by `Φ.symm` is the inverse of the one conjugating by `Φ`. -/
@[simp, grind =]
theorem isomCongr_symm (Φ : RiemannianIsometry I J M N) :
    Φ.isomCongr.symm = Φ.symm.isomCongr := by
  ext Θ x
  simp [isomCongr]

/-- Naturality of `isomCongr` against the forgetful homomorphism `toDiff` to self-diffeomorphisms,
as a commutative square of group homomorphisms intertwining `isomCongr` with
`Diffeomorph.diffCongr`. -/
theorem toDiff_comp_isomCongr (Φ : RiemannianIsometry I J M N) :
    toDiff.comp Φ.isomCongr.toMonoidHom =
      (Diffeomorph.diffCongr Φ.toDiffeomorph).toMonoidHom.comp toDiff := by
  ext Ψ y
  simp [coe_symm]

/-- Forgetting the metric condition sends `Φ.isomCongr Ψ` to `diffCongr` of the underlying
self-diffeomorphisms; the elementwise shadow of `toDiff_comp_isomCongr`. -/
@[simp]
theorem toDiffeomorph_isomCongr (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    (Φ.isomCongr Ψ).toDiffeomorph = Φ.toDiffeomorph.diffCongr Ψ.toDiffeomorph := by
  ext y
  simp [coe_symm]

end TauCeti.RiemannianIsometry

end
