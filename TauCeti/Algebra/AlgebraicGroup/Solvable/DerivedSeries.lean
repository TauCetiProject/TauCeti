/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Derived.Series

/-!
# Solvability and termination of the derived series

For a reduced finite-type affine group over an algebraically closed field, the scheme-theoretic
and abstract derived series reach the identity at the same index. Thus the scheme-theoretic
series terminates exactly when the rational-point group is solvable.

## References

* A. Borel, *Linear Algebraic Groups*, §10.5.
* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

namespace TauCeti

open WithConv

variable {k : Type*} [Field k] [IsAlgClosed k] (H : _root_.CommHopfAlgCat k)
  [Algebra.FiniteType k H] [IsReduced H]

/-- Scheme-theoretic and abstract derived series reach the identity at the same index. -/
theorem derivedSeriesDefiningIdeal_eq_augmentation_iff (n : ℕ) :
    derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation k H ↔
      derivedSeries (WithConv (H →ₐ[k] k)) n = ⊥ := by
  rw [derivedSeriesDefiningIdeal_eq_vanishingIdeal_derivedSeries,
    HopfIdeal.vanishingIdeal_eq_augmentation_iff]

/-- A reduced finite-type affine group over an algebraically closed field has solvable
rational points exactly when its scheme-theoretic derived series reaches the identity. -/
theorem isSolvable_points_iff_exists_derivedSeriesDefiningIdeal_eq_augmentation :
    Group.IsSolvable (WithConv (H →ₐ[k] k)) ↔
      ∃ n, derivedSeriesDefiningIdeal H n = HopfIdeal.augmentation k H := by
  simp only [derivedSeriesDefiningIdeal_eq_augmentation_iff]
  exact ⟨fun h ↦ h.solvable, fun h ↦ ⟨h⟩⟩

end TauCeti
