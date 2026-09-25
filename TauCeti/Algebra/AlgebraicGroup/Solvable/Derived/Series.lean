/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Series.PointClosure
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Basic

/-!
# Solvability and termination of the derived series

For an affine group with schematically dense rational points, the scheme-theoretic and abstract
derived series reach the identity at the same index. Thus the scheme-theoretic series terminates
exactly when the rational-point group is solvable. This applies in particular to reduced finite-type
affine groups over algebraically closed fields.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

open TauCeti WithConv

variable {k : Type*} [Field k] (H : _root_.CommHopfAlgCat k)

namespace CommHopfAlgCat

/-- With schematically dense rational points, scheme-theoretic and abstract derived series
reach the identity at the same index. -/
@[simp] theorem derivedSeriesDefiningIdeal_eq_augmentation_iff_of_dense_points
    (h : HopfIdeal.vanishingIdeal (⊤ : Subgroup (WithConv (H →ₐ[k] k))) = ⊥) (n : ℕ) :
    derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation k H ↔
      derivedSeries (WithConv (H →ₐ[k] k)) n = ⊥ := by
  rw [derivedSeriesDefiningIdeal_eq_vanishingIdeal_derivedSeries_of_dense_points H h,
    HopfIdeal.vanishingIdeal_eq_augmentation_iff]

/-- With schematically dense rational points, rational-point solvability is equivalent to
termination of the scheme-theoretic derived series. -/
theorem isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation_of_dense_points
    (h : HopfIdeal.vanishingIdeal (⊤ : Subgroup (WithConv (H →ₐ[k] k))) = ⊥) :
    Group.IsSolvable (WithConv (H →ₐ[k] k)) ↔
      ∃ n, derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation k H := by
  simp only [derivedSeriesDefiningIdeal_eq_augmentation_iff_of_dense_points H h]
  exact ⟨fun h ↦ h.solvable, fun h ↦ ⟨h⟩⟩

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]

/-- Scheme-theoretic and abstract derived series reach the identity at the same index. -/
theorem derivedSeriesDefiningIdeal_eq_augmentation_iff (n : ℕ) :
    derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation k H ↔
      derivedSeries (WithConv (H →ₐ[k] k)) n = ⊥ :=
  H.derivedSeriesDefiningIdeal_eq_augmentation_iff_of_dense_points
    HopfIdeal.vanishingIdeal_top n

/-- A reduced finite-type affine group over an algebraically closed field has solvable
rational points exactly when its scheme-theoretic derived series reaches the identity. -/
theorem isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation :
    Group.IsSolvable (WithConv (H →ₐ[k] k)) ↔
      ∃ n, derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation k H :=
  H.isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation_of_dense_points
    HopfIdeal.vanishingIdeal_top

end CommHopfAlgCat

open CommHopfAlgCat

namespace TauCeti.geometricallySolvablePointsCommHopfAlgProperty

variable [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]

/-- Over an algebraically closed field, the geometric-points solvability property of a
reduced finite-type affine group is equivalent to termination of its derived series. -/
theorem iff_exists_derivedSeriesDefiningIdeal_eq_augmentation :
    geometricallySolvablePointsCommHopfAlgProperty k H ↔
      ∃ n, derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation k H := by
  rw [← isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation,
    geometricallySolvablePointsCommHopfAlgProperty_iff]
  let e : k ≃ₐ[k] AlgebraicClosure k := AlgEquiv.ofBijective
    (Algebra.ofId k (AlgebraicClosure k)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  constructor
  · intro h
    let := h
    exact Group.isSolvable_of_isSolvable_injective
      (f := AlgHom.mapValue e.toAlgHom) (AlgHom.mapValue_injective e.injective)
  · intro h
    let := h
    exact Group.isSolvable_of_isSolvable_injective
      (f := AlgHom.mapValue e.symm.toAlgHom) (AlgHom.mapValue_injective e.symm.injective)

end TauCeti.geometricallySolvablePointsCommHopfAlgProperty
