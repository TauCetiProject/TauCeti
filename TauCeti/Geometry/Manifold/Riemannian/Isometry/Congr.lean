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

A smooth Riemannian isometry `e : RiemannianIsometry I J M N` conjugates smooth Riemannian
self-isometries of `M` into smooth Riemannian self-isometries of `N` by `Φ ↦ e ∘ Φ ∘ e⁻¹`. Because
conjugation preserves composition, it is a group isomorphism `Isom I M ≃* Isom J N` between the
isometry groups built in `TauCeti.Geometry.Manifold.Riemannian.Isometry.Group`. When two models of
the same geometry are identified by a Riemannian isometry, such as the upper half-plane and the
two-dimensional upper half-space, `isomCongr` transports any action by Riemannian isometries of one
model to the other.

This file records `TauCeti.RiemannianIsometry.isomCongr`, its pointwise and intertwining formulas,
its functoriality on the groupoid of Riemannian isometries (`isomCongr_refl`, `isomCongr_trans`,
`isomCongr_symm`), and its naturality against the forgetful homomorphism `toDiff` into the
self-diffeomorphism group through `Diffeomorph.diffCongr`.

## Main definitions

* `TauCeti.RiemannianIsometry.isomCongr e`: the group isomorphism `Isom I M ≃* Isom J N`
  conjugating by `e : RiemannianIsometry I J M N`.

## Main results

* `TauCeti.RiemannianIsometry.isomCongr_apply_apply` and
  `TauCeti.RiemannianIsometry.isomCongr_apply_apply_self`: the pointwise action
  `e.isomCongr Φ y = e (Φ (e.symm y))` and intertwining identity `e.isomCongr Φ (e x) = e (Φ x)`.
* `TauCeti.RiemannianIsometry.isomCongr_refl`, `TauCeti.RiemannianIsometry.isomCongr_trans`, and
  `TauCeti.RiemannianIsometry.isomCongr_symm`: functoriality of `isomCongr`.
* `TauCeti.RiemannianIsometry.toDiff_comp_isomCongr` and
  `TauCeti.RiemannianIsometry.toDiffeomorph_isomCongr`: naturality against `toDiff` and
  `Diffeomorph.diffCongr`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
* `TauCeti/Geometry/Diffeomorphism/Congr.lean` (`Diffeomorph.diffCongr`) and
  `Mathlib/Logic/Equiv/Defs.lean` (`Equiv.permCongr`), whose conjugation pattern this file follows.
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

/-- Conjugation by a smooth Riemannian isometry `e : RiemannianIsometry I J M N` as a group
isomorphism between the isometry groups: `e.isomCongr Φ = e ∘ Φ ∘ e⁻¹`. -/
def isomCongr (e : RiemannianIsometry I J M N) : Isom I M ≃* Isom J N where
  toFun Φ := (e.symm.trans Φ).trans e
  invFun Ψ := (e.trans Ψ).trans e.symm
  left_inv Φ := by
    ext x
    simp
  right_inv Ψ := by
    ext y
    simp
  map_mul' Φ Ψ := by
    ext y
    simp

/-- The underlying Riemannian isometry of `e.isomCongr Φ` is `(e.symm.trans Φ).trans e`. -/
theorem isomCongr_apply (e : RiemannianIsometry I J M N) (Φ : Isom I M) :
    e.isomCongr Φ = (e.symm.trans Φ).trans e := (rfl)

/-- The conjugating isomorphism acts pointwise by `e.isomCongr Φ y = e (Φ (e.symm y))`. -/
@[simp, grind =]
theorem isomCongr_apply_apply (e : RiemannianIsometry I J M N) (Φ : Isom I M) (y : N) :
    e.isomCongr Φ y = e (Φ (e.symm y)) := by
  simp [isomCongr_apply]

/-- Conjugation intertwines `Φ` and `e.isomCongr Φ` along `e`: `e.isomCongr Φ (e x) = e (Φ x)`. -/
theorem isomCongr_apply_apply_self (e : RiemannianIsometry I J M N) (Φ : Isom I M) (x : M) :
    e.isomCongr Φ (e x) = e (Φ x) := by
  simp

/-- The inverse of `e.isomCongr Φ` is `e.isomCongr Φ⁻¹`. -/
theorem isomCongr_inv (e : RiemannianIsometry I J M N) (Φ : Isom I M) :
    (e.isomCongr Φ)⁻¹ = e.isomCongr Φ⁻¹ :=
  (map_inv e.isomCongr Φ).symm

/-- Conjugating by the identity Riemannian isometry is the identity group isomorphism. -/
@[simp]
theorem isomCongr_refl :
    (RiemannianIsometry.refl I M).isomCongr = MulEquiv.refl (Isom I M) := by
  ext Φ x
  simp

/-- Conjugation is functorial: conjugating by a composite Riemannian isometry is the composite of
the conjugating isomorphisms. -/
@[simp]
theorem isomCongr_trans (e : RiemannianIsometry I J M N) (e' : RiemannianIsometry J K N P) :
    (e.trans e').isomCongr = e.isomCongr.trans e'.isomCongr := by
  ext Φ z
  simp

/-- The isomorphism conjugating by `e.symm` is the inverse of the one conjugating by `e`. -/
@[simp, grind =]
theorem isomCongr_symm (e : RiemannianIsometry I J M N) :
    e.isomCongr.symm = e.symm.isomCongr := by
  ext Ψ x
  simp [isomCongr]

/-- Naturality of `isomCongr` against the forgetful homomorphism `toDiff` to self-diffeomorphisms,
intertwining `isomCongr` with `Diffeomorph.diffCongr`. -/
theorem toDiff_comp_isomCongr (e : RiemannianIsometry I J M N) :
    toDiff.comp e.isomCongr.toMonoidHom =
      (Diffeomorph.diffCongr e.toDiffeomorph).toMonoidHom.comp toDiff := by
  ext Φ y
  simp [coe_symm]

/-- Forgetting the metric condition sends `e.isomCongr Φ` to `diffCongr` of the underlying
self-diffeomorphism. -/
@[simp]
theorem toDiffeomorph_isomCongr (e : RiemannianIsometry I J M N) (Φ : Isom I M) :
    (e.isomCongr Φ).toDiffeomorph = e.toDiffeomorph.diffCongr Φ.toDiffeomorph := by
  simpa using DFunLike.congr_fun (toDiff_comp_isomCongr e) Φ

end TauCeti.RiemannianIsometry

end
