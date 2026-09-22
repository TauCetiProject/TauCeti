/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

/-!
# Units bounded at every infinite place

Only finitely many units of the ring of integers of a number field have absolute value at most
`B` at every infinite place: such a unit is an algebraic integer all of whose conjugates are
bounded by `B`, and there are finitely many of those
(`NumberField.Embeddings.finite_of_norm_le`). This finiteness is what makes the certification
of a fundamental unit a finite search.

## Main results

* `TauCeti.NumberField.Units.finite_setOf_forall_apply_le`: the set of units with absolute value at
  most `B` at every infinite place is finite.
* `TauCeti.NumberField.Units.finite_setOf_norm_logEmbedding_le`: the set of units in a bounded
  region of logarithmic space is finite.
-/

public section

open NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- **Finiteness of bounded units.** Only finitely many units have absolute value at most `B` at
every infinite place. -/
theorem finite_setOf_forall_apply_le (B : ℝ) :
    {u : (𝓞 K)ˣ | ∀ w : InfinitePlace K, w u ≤ B}.Finite := by
  refine ((Embeddings.finite_of_norm_le K ℂ B).preimage (Units.coe_injective K).injOn).subset
    fun u hu => ⟨RingOfIntegers.isIntegral_coe (u : 𝓞 K), (InfinitePlace.le_iff_le (u : K) B).mp hu⟩

open scoped Classical NumberField in
/-- **Finiteness of logarithmically bounded units.** Only finitely many units have logarithmic
embedding of norm at most `r`.

The estimate is uniform over all infinite places, including the distinguished place omitted from
`logSpace`: the product formula bounds its logarithm in terms of the other components. -/
theorem finite_setOf_norm_logEmbedding_le (r : ℝ) :
    {u : (𝓞 K)ˣ |
      ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ ≤ r}.Finite := by
  -- The argument follows Mathlib's
  -- `NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite`.
  by_cases hr : 0 ≤ r
  · refine (finite_setOf_forall_apply_le (K := K)
      (Real.exp (Fintype.card (InfinitePlace K) * r))).subset ?_
    intro u hu w
    rw [← Real.exp_log (Units.pos_at_place u w)]
    have hlog : |Real.log (w u)| ≤ Fintype.card (InfinitePlace K) * r :=
      NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le
        (K := K) (x := u) hr hu w
    exact Real.exp_le_exp.mpr ((le_abs_self (Real.log (w u))).trans hlog)
  · have hr' : r < 0 := lt_of_not_ge hr
    have hempty : {u : (𝓞 K)ˣ |
        ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ ≤ r} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro u
      exact fun hu ↦ (not_le_of_gt hr') ((norm_nonneg _).trans hu)
    rw [hempty]
    exact Set.finite_empty

end TauCeti.NumberField.Units
