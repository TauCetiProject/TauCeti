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
into self-isometries of `N` by `Ψ ↦ Φ ∘ Ψ ∘ Φ⁻¹`. Because this preserves composition, it is a
group isomorphism `Isom I M ≃* Isom J N` between the isometry groups built in
`TauCeti.Geometry.Manifold.Riemannian.Isometry.Group`. This file records that isomorphism,
`TauCeti.RiemannianIsometry.isomCongr`, its pointwise action, its functoriality with respect to
`refl`, `trans`, and `symm`, and its naturality with respect to the forgetful homomorphism
`toDiff` to the diffeomorphism group via `Diffeomorph.diffCongr`.

## Main definitions

* `TauCeti.RiemannianIsometry.isomCongr Φ`: the group isomorphism `Isom I M ≃* Isom J N`
  conjugating by a Riemannian isometry `Φ : RiemannianIsometry I J M N`.

## Main results

* `TauCeti.RiemannianIsometry.isomCongr_apply_apply`: the pointwise action
  `isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y))`.
* `TauCeti.RiemannianIsometry.isomCongr_refl`, `isomCongr_trans`, `isomCongr_symm`: functoriality
  of conjugation on the groupoid of Riemannian isometries.
* `TauCeti.RiemannianIsometry.toDiff_comp_isomCongr` and `toDiff_isomCongr`: naturality against
  `toDiff` and `Diffeomorph.diffCongr`.

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
isomorphism between the isometry groups: `isomCongr Φ Ψ = Φ ∘ Ψ ∘ Φ⁻¹`. -/
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
    simp [mul_def]

/-- The underlying isometry of `isomCongr Φ Ψ` is `(Φ.symm.trans Ψ).trans Φ`. -/
theorem isomCongr_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    isomCongr Φ Ψ = (Φ.symm.trans Ψ).trans Φ := (rfl)

/-- The conjugating isomorphism acts pointwise by `isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y))`. -/
@[simp]
theorem isomCongr_apply_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) (y : N) :
    isomCongr Φ Ψ y = Φ (Ψ (Φ.symm y)) := by
  rw [isomCongr_apply, trans_apply, trans_apply]

/-- Conjugating by the identity isometry is the identity isomorphism. -/
@[simp]
theorem isomCongr_refl :
    isomCongr (RiemannianIsometry.refl I M) = MulEquiv.refl (Isom I M) := by
  ext Ψ x
  simp

/-- Conjugation is functorial: conjugating by a composite isometry is the composite of the
conjugating isomorphisms. -/
@[simp]
theorem isomCongr_trans (Φ : RiemannianIsometry I J M N) (Ψ : RiemannianIsometry J K N P) :
    isomCongr (Φ.trans Ψ) = (isomCongr Φ).trans (isomCongr Ψ) := by
  ext Θ z
  simp

/-- The isomorphism conjugating by `Φ.symm` is the inverse of the one conjugating by `Φ`. -/
@[simp]
theorem isomCongr_symm (Φ : RiemannianIsometry I J M N) :
    (isomCongr Φ).symm = isomCongr Φ.symm :=
  MulEquiv.ext fun _ ↦ (isomCongr Φ).injective (by ext y; simp)

/-- Naturality of `isomCongr` against the forgetful homomorphism `toDiff`: conjugating Riemannian
isometries by `Φ` and forgetting the metric equals forgetting the metric and conjugating
diffeomorphisms by `Φ.toDiffeomorph`. -/
theorem toDiff_comp_isomCongr (Φ : RiemannianIsometry I J M N) :
    toDiff.comp (isomCongr Φ).toMonoidHom =
      (Diffeomorph.diffCongr Φ.toDiffeomorph).toMonoidHom.comp toDiff := by
  ext Ψ y
  simp [Diffeomorph.diffCongr_apply_apply, coe_symm]

/-- Elementwise naturality of `isomCongr` against `toDiff`. -/
theorem toDiff_isomCongr (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    toDiff (isomCongr Φ Ψ) = Φ.toDiffeomorph.diffCongr (toDiff Ψ) :=
  DFunLike.congr_fun (toDiff_comp_isomCongr Φ) Ψ

end TauCeti.RiemannianIsometry

end
