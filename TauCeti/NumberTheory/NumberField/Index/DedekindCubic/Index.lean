/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.DedekindCubic.Order
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import TauCeti.NumberTheory.NumberField.Index.Basic
import Mathlib.Tactic.ComputeDegree

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

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K}

/-- The cardinality of the quotient by Dedekind's order. The generator hypothesis makes this a
finite, positive index in the full ring of integers. -/
def dedekindOrderIndex (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (_hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : ℕ :=
  (dedekindOrder (dedekindCubic_relation hmin)).toSubmodule.cardQuot

/-- The index is the cardinality of the additive quotient by Dedekind's order. -/
theorem dedekindOrderIndex_def
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    dedekindOrderIndex hmin hgen =
      Nat.card (𝓞 K ⧸ (dedekindOrder (dedekindCubic_relation hmin)).toSubmodule) :=
  Submodule.cardQuot_apply _

/-- Dedekind's cubic order has finite index in the full ring of integers. -/
theorem finite_quotient_dedekindOrder
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Finite (𝓞 K ⧸ (dedekindOrder (dedekindCubic_relation hmin)).toSubmodule) := by
  apply Submodule.finiteQuotientOfFreeOfRankEq
  -- `toSubmodule` and the subalgebra have the same carrier, hence the same subtype module.
  change Module.finrank ℤ (dedekindOrder (dedekindCubic_relation hmin)) =
    Module.finrank ℤ (𝓞 K)
  let t : IntegralPrimitiveElement K := ⟨θ, hgen⟩
  rw [Module.finrank_eq_card_basis (dedekindOrderBasis hmin),
    ← t.finrank_adjoin, IntegralPrimitiveElement.adjoin_def,
    (Algebra.adjoin.powerBasis' θ.isIntegral).finrank,
    Algebra.adjoin.powerBasis'_dim, hmin]
  symm
  compute_degree <;> norm_num

/-- The index of Dedekind's cubic order is positive. -/
theorem dedekindOrderIndex_pos
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : 0 < dedekindOrderIndex hmin hgen := by
  let _ := finite_quotient_dedekindOrder hmin hgen
  rw [dedekindOrderIndex_def]
  exact Nat.card_pos

/-- Dedekind's cubic order has index one exactly when it is the full ring of integers. -/
@[simp] theorem dedekindOrderIndex_eq_one_iff
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    dedekindOrderIndex hmin hgen = 1 ↔
      dedekindOrder (dedekindCubic_relation hmin) = ⊤ := by
  rw [dedekindOrderIndex, Submodule.cardQuot_eq_one_iff, Algebra.toSubmodule_eq_top]

end TauCeti.NumberField

end
end
