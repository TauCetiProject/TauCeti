/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Index.DedekindCubic.Order
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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

/-- The index of Dedekind's order in the full ring of integers. -/
def dedekindOrderIndex (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8) : ℕ :=
  (dedekindOrder (dedekindCubic_relation hmin)).toSubmodule.cardQuot

/-- The index is the cardinality of the additive quotient by Dedekind's order. -/
theorem dedekindOrderIndex_def
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8) :
    dedekindOrderIndex hmin =
      Nat.card (𝓞 K ⧸ (dedekindOrder (dedekindCubic_relation hmin)).toSubmodule) :=
  Submodule.cardQuot_apply _

private theorem finrank_dedekindCubic
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : Module.finrank ℚ K = 3 := by
  have hdegree : (minpoly ℚ (θ : K)).natDegree = 3 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ θ.isIntegral_coe,
      RingOfIntegers.minpoly_coe, Polynomial.Monic.natDegree_map
        (minpoly.monic θ.isIntegral), hmin]
    compute_degree <;> norm_num
  exact (Field.primitive_element_iff_minpoly_natDegree_eq ℚ (θ : K)).mp
    ((IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
      (fun x _ => IsAlgebraic.of_finite ℚ x)).mpr hgen) |>.symm.trans hdegree

/-- Dedekind's cubic order has finite index in the full ring of integers. -/
theorem finite_dedekindOrderQuotient
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    Finite (𝓞 K ⧸ (dedekindOrder (dedekindCubic_relation hmin)).toSubmodule) := by
  apply Submodule.finiteQuotientOfFreeOfRankEq
  -- `toSubmodule` and the subalgebra have the same carrier, hence the same subtype module.
  change Module.finrank ℤ (dedekindOrder (dedekindCubic_relation hmin)) =
    Module.finrank ℤ (𝓞 K)
  rw [Module.finrank_eq_card_basis (dedekindOrderBasis hmin),
    RingOfIntegers.rank K, finrank_dedekindCubic hmin hgen]
  simp

/-- The index of Dedekind's cubic order is positive. -/
theorem dedekindOrderIndex_pos
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) : 0 < dedekindOrderIndex hmin := by
  let _ := finite_dedekindOrderQuotient hmin hgen
  rw [dedekindOrderIndex_def]
  exact Nat.card_pos

/-- Dedekind's cubic order has index one exactly when it is the full ring of integers. -/
@[simp] theorem dedekindOrderIndex_eq_one_iff
    (hmin : minpoly ℤ θ = X ^ 3 - X ^ 2 - C 2 * X - C 8) :
    dedekindOrderIndex hmin = 1 ↔
      dedekindOrder (dedekindCubic_relation hmin) = ⊤ := by
  rw [dedekindOrderIndex, Submodule.cardQuot_eq_one_iff, Algebra.toSubmodule_eq_top]

end TauCeti.NumberField

end
end
