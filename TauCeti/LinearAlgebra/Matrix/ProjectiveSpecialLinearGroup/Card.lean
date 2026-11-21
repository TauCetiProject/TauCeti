/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.Coset.Card
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Cardinality of projective special linear groups

This file relates the cardinality of `PSL(n, R) = SL(n, R) ⧸ Z(SL(n, R))` to that of `SL(n, R)`
and the `n`-th roots of unity in `R`.

## Main results

* `Matrix.ProjectiveSpecialLinearGroup.card_mul_card_rootsOfUnity`: for `0 < n`,
  `|PSL(n, R)| · |rootsOfUnity n R| = |SL(n, R)|`.
-/

public section

namespace Matrix.ProjectiveSpecialLinearGroup

/-- For `0 < n` and any commutative ring `R`, the order of `PSL(n, R)` times the number of
`n`-th roots of unity in `R` equals the order of `SL(n, R)` (both sides are `0` when `SL(n, R)` is
infinite). -/
theorem card_mul_card_rootsOfUnity (n : ℕ) (hn : 0 < n) (R : Type*) [CommRing R] :
    Nat.card (ProjectiveSpecialLinearGroup (Fin n) R) * Nat.card (rootsOfUnity n R) =
      Nat.card (SpecialLinearGroup (Fin n) R) := by
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin n) R))
  rw [Nat.card_congr (SpecialLinearGroup.centerMulEquivRootsOfUnityFin n hn R).toEquiv] at hlag
  exact hlag.symm

end Matrix.ProjectiveSpecialLinearGroup
