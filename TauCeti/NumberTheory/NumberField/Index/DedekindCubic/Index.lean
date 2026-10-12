/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.DedekindCubic.Order
import TauCeti.NumberTheory.NumberField.Index.Basic

/-!
# The index of Dedekind's cubic order

The order with basis `(1, θ, (θ² - θ)/2)` is a full-rank lattice in the ring of
integers when `θ` generates the cubic field. Thus its additive quotient is finite,
and its index is a positive natural number. The index is one exactly when the
order is the full ring of integers.

The argument follows Neukirch, *Algebraic Number Theory*, Chapter III, §2, Exercise 1.
-/

public section
noncomputable section

open Polynomial NumberField Module
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [CharZero K] {θ : 𝓞 K}

/-- The index of Dedekind's order in the full ring of integers. -/
def dedekindOrderIndex (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) : ℕ :=
  (dedekindOrder hθ).toSubmodule.cardQuot

/-- The index is the cardinality of the additive quotient by Dedekind's order. -/
theorem dedekindOrderIndex_def
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    dedekindOrderIndex hθ =
      Nat.card (𝓞 K ⧸ (dedekindOrder hθ).toSubmodule) :=
  Submodule.cardQuot_apply _

section NumberField

variable [NumberField K]

/-- Dedekind's cubic order has finite index in the full ring of integers when `θ` generates `K`. -/
theorem finite_quotient_dedekindOrder
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Finite (𝓞 K ⧸ (dedekindOrder hθ).toSubmodule) := by
  let t : IntegralPrimitiveElement K := ⟨θ, hgen⟩
  have hle : t.adjoin.toSubmodule ≤ (dedekindOrder hθ).toSubmodule := by
    -- `toSubmodule` retains the subalgebra's carrier, so the two inclusions
    -- are definitionally equal.
    change t.adjoin ≤ dedekindOrder hθ
    rw [IntegralPrimitiveElement.adjoin_def]
    apply Algebra.adjoin_le
    intro x hx
    have hx' : x = θ := by simpa [t] using hx
    rw [hx']
    exact (mem_dedekindOrder_iff hθ θ).2 ⟨0, 1, 0, by simp⟩
  exact Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)

/-- The index of Dedekind's cubic order is positive when `θ` generates `K`. -/
theorem dedekindOrderIndex_pos
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    0 < dedekindOrderIndex hθ := by
  let _ := finite_quotient_dedekindOrder hθ hgen
  rw [dedekindOrderIndex_def]
  exact Nat.card_pos

end NumberField

/-- Dedekind's cubic order has index one exactly when it is the full ring of integers. -/
@[simp] theorem dedekindOrderIndex_eq_one_iff
    (hθ : θ ^ 3 - θ ^ 2 - 2 * θ - 8 = 0) :
    dedekindOrderIndex hθ = 1 ↔ dedekindOrder hθ = ⊤ := by
  rw [dedekindOrderIndex, Submodule.cardQuot_eq_one_iff, Algebra.toSubmodule_eq_top]

end TauCeti.NumberField

end
end
