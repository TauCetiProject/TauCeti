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

A Riemannian isometry `Φ : RiemannianIsometry I J M N` conjugates self-isometries of `M` into
self-isometries of `N` by `Ψ ↦ Φ ∘ Ψ ∘ Φ⁻¹`. Because composition of Riemannian isometries is a
Riemannian isometry, this gives a group isomorphism `Isom I M ≃* Isom J N` compatible with the
diffeomorphism conjugation `Diffeomorph.diffCongr` under the forgetful homomorphism `toDiff`.

## Main definitions

* `TauCeti.RiemannianIsometry.isomCongr Φ`: the group isomorphism `Isom I M ≃* Isom J N`
  conjugating by `Φ : RiemannianIsometry I J M N`.

## Main results

* `TauCeti.RiemannianIsometry.isomCongr_apply_apply`: `Φ.isomCongr Ψ y = Φ (Ψ (Φ.symm y))`.
* `TauCeti.RiemannianIsometry.isomCongr_refl`, `isomCongr_symm`, `isomCongr_trans`: functoriality
  on the groupoid of Riemannian isometries.
* `TauCeti.RiemannianIsometry.toDiff_comp_isomCongr`: compatibility with `Diffeomorph.diffCongr`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
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

/-- Conjugation by a Riemannian isometry `Φ : RiemannianIsometry I J M N` as a group isomorphism
`Isom I M ≃* Isom J N`: `Φ.isomCongr Ψ = Φ ∘ Ψ ∘ Φ⁻¹`. -/
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
    simp [mul_def]

/-- The conjugating isomorphism acts pointwise by `Φ.isomCongr Ψ y = Φ (Ψ (Φ.symm y))`. -/
@[simp]
theorem isomCongr_apply_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) (y : N) :
    Φ.isomCongr Ψ y = Φ (Ψ (Φ.symm y)) := by
  simp [isomCongr]

/-- The underlying Riemannian isometry of `Φ.isomCongr Ψ` is `(Φ.symm.trans Ψ).trans Φ`. -/
theorem isomCongr_apply (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    Φ.isomCongr Ψ = (Φ.symm.trans Ψ).trans Φ := (rfl)

/-- Conjugating by the identity Riemannian isometry is the identity isomorphism. -/
@[simp]
theorem isomCongr_refl :
    (RiemannianIsometry.refl I M).isomCongr = MulEquiv.refl (Isom I M) := by
  ext Ψ x
  simp

/-- The inverse of `Φ.isomCongr` conjugates by `Φ.symm`. -/
@[simp]
theorem isomCongr_symm (Φ : RiemannianIsometry I J M N) :
    Φ.isomCongr.symm = Φ.symm.isomCongr := by
  ext Ξ x
  simp [isomCongr]

/-- Conjugation is functorial: conjugating by `Φ.trans Φ'` is `Φ.isomCongr.trans Φ'.isomCongr`. -/
theorem isomCongr_trans (Φ : RiemannianIsometry I J M N) (Φ' : RiemannianIsometry J K N P) :
    (Φ.trans Φ').isomCongr = Φ.isomCongr.trans Φ'.isomCongr := by
  ext Ψ z
  simp

/-- Forgetting the metric condition turns `isomCongr` into `Diffeomorph.diffCongr`. -/
@[simp]
theorem toDiffeomorph_isomCongr (Φ : RiemannianIsometry I J M N) (Ψ : Isom I M) :
    (Φ.isomCongr Ψ).toDiffeomorph =
      Diffeomorph.diffCongr Φ.toDiffeomorph Ψ.toDiffeomorph := by
  ext y
  simp [isomCongr, coe_symm]

/-- Naturality of `isomCongr` with respect to the forgetful homomorphism `toDiff`. -/
theorem toDiff_comp_isomCongr (Φ : RiemannianIsometry I J M N) :
    (toDiff (I := J) (M := N)).comp Φ.isomCongr.toMonoidHom =
      (Diffeomorph.diffCongr Φ.toDiffeomorph).toMonoidHom.comp (toDiff (I := I) (M := M)) := by
  ext Ψ y
  simp [isomCongr, coe_symm]

end TauCeti.RiemannianIsometry

end
