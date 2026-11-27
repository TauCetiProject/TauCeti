/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Filtration.Demazure

/-!
# Checks for Demazure filtrations below the exact type

Over a discrete valuation ring `A` with maximal ideal `𝔪` and residue field `k`, take the type
`μ = (2, 1, 0)`. The module `k³`, of the lower type `(1, 1, 1)`, carries Demazure filtrations of
type `μ`: the tower first chooses a rank-two quotient of `k³`, which `k³` itself is not. The
module `A ⧸ 𝔪 ³`, of type `(3)`, has the same length but does not: its type is not dominated by
`μ`, and already its first quotient `A ⧸ 𝔪` is too small for the two-dimensional first graded
piece.
-/

open IsLocalRing

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

-- `k³ = ∏ (A ⧸ 𝔪)` has type `(1, 1, 1) ≤ (2, 1, 0)`, so it carries filtrations of that type.
example : Nonempty ((maximalIdeal A).DemazureFiltration ![2, 1, 0]
    (∀ _ : Fin 3, A ⧸ maximalIdeal A ^ 1)) := by
  rw [Ideal.DemazureFiltration.nonempty_iff_sum_min_le (LinearEquiv.refl _ _)]
  refine ⟨by decide, fun k ↦ ?_⟩
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  omega

-- `A ⧸ 𝔪 ³` has type `(3)`, which is not below `(2, 1, 0)`.
example : IsEmpty ((maximalIdeal A).DemazureFiltration ![2, 1, 0]
    (∀ _ : Fin 1, A ⧸ maximalIdeal A ^ 3)) := by
  rw [← not_nonempty_iff, Ideal.DemazureFiltration.nonempty_iff_sum_min_le (LinearEquiv.refl _ _)]
  rintro ⟨-, h⟩
  have := h 1
  simp [Fin.sum_univ_three] at this
