/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.PositiveDegrees.Grading
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Scalar restriction of positive gradings

Restricting scalars preserves positive support and the submodules above each degree
cutoff. These statements do not require a direct-sum decomposition: positive support
is a condition on the pieces, and scalar restriction preserves their sums.

Adapted from `Mei/Algebra/PositiveDegrees/RestrictScalars.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7` (Apache 2.0).
-/

public section

namespace TauCeti

variable {N R S M : Type*} [AddCommMonoid N] [Semiring R] [Semiring S]
  [AddCommMonoid M] [Module S M] [Module R M] [SMul R S] [IsScalarTower R S M]

/-- Restricting scalars preserves the vanishing pieces of a positive grading. -/
instance IsPositiveGrading.restrictScalars (d : PositiveDegrees N)
    (ℒ : N → Submodule S M) [IsPositiveGrading d ℒ] :
    IsPositiveGrading d (fun n => (ℒ n).restrictScalars R) where
  eq_bot n hn := by
    rw [Submodule.restrictScalars_eq_bot_iff]
    exact IsPositiveGrading.eq_bot (d := d) (ℒ := ℒ) n hn

/-- The degree filtration commutes with restriction of scalars on every piece. -/
@[simp]
theorem PositiveDegrees.degreeSubmodule_restrictScalars (d : PositiveDegrees N)
    (ℒ : N → Submodule S M) (k : ℕ) :
    d.degreeSubmodule (fun n => (ℒ n).restrictScalars R) k =
      (d.degreeSubmodule ℒ k).restrictScalars R := by
  simp only [d.degreeSubmodule_def, Submodule.restrictScalars_iSup]

end TauCeti
