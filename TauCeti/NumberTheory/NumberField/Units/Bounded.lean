/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.NumberTheory.Height.NumberField

/-!
# Bounded families of units

Only finitely many units of the ring of integers of a number field have absolute value at most
`B` at every infinite place: such a unit is an algebraic integer all of whose conjugates are
bounded by `B`, and there are finitely many of those
(`NumberField.Embeddings.finite_of_norm_le`). This finiteness is what makes the certification
of a fundamental unit a finite search.

The relative multiplicative and logarithmic heights also have the Northcott property on units.
This is inherited from the corresponding Northcott property on the ambient number field, since
the coercion of units into the field is injective. In particular, a bound on height cuts out only
finitely many units.

## Main results

* `TauCeti.NumberField.Units.finite_setOf_forall_apply_le`: the set of units with absolute value at
  most `B` at every infinite place is finite.
* `TauCeti.NumberField.Units.finite_setOf_norm_logEmbedding_le`: the set of units in a bounded
  region of logarithmic space is finite.
* `TauCeti.NumberField.Units.finite_setOfPred_mulHeight₁_le` and
  `TauCeti.NumberField.Units.finite_setOfPred_logHeight₁_le`: the sets of units of bounded
  relative multiplicative or logarithmic height are finite.
-/

public section

open NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-! ### Finiteness at bounded height -/

private instance : Filter.TendstoCofinite (fun u : (𝓞 K)ˣ ↦ (u : K)) :=
  Filter.tendstoCofinite_of_injective (Units.coe_injective K)

/-- The relative multiplicative height has the Northcott property when restricted to the units
of a number field. -/
instance : Northcott (fun u : (𝓞 K)ˣ ↦ Height.mulHeight₁ (u : K)) := by
  rw [← Function.comp_def]
  exact Northcott.comp_of_finite_fibers ..

/-- The relative logarithmic height has the Northcott property when restricted to the units of a
number field. -/
instance : Northcott (fun u : (𝓞 K)ˣ ↦ Height.logHeight₁ (u : K)) := by
  rw [← Function.comp_def]
  exact Northcott.comp_of_finite_fibers ..

/-- Only finitely many units of a number field have relative multiplicative height at most a
fixed bound. -/
theorem finite_setOfPred_mulHeight₁_le (B : ℝ) :
    {u : (𝓞 K)ˣ | Height.mulHeight₁ (u : K) ≤ B}.Finite :=
  Northcott.finite_le B

/-- Only finitely many units of a number field have relative logarithmic height at most a fixed
bound. -/
theorem finite_setOfPred_logHeight₁_le (B : ℝ) :
    {u : (𝓞 K)ˣ | Height.logHeight₁ (u : K) ≤ B}.Finite :=
  Northcott.finite_le B

/-! ### Finiteness from bounds at the infinite places -/

/-- **Finiteness of bounded units.** Only finitely many units have absolute value at most `B` at
every infinite place. -/
theorem finite_setOf_forall_apply_le (B : ℝ) :
    {u : (𝓞 K)ˣ | ∀ w : InfinitePlace K, w u ≤ B}.Finite := by
  refine ((Embeddings.finite_of_norm_le K ℂ B).preimage (Units.coe_injective K).injOn).subset
    fun u hu => ⟨RingOfIntegers.isIntegral_coe (u : 𝓞 K), (InfinitePlace.le_iff_le (u : K) B).mp hu⟩

open scoped Classical NumberField in
/-- **Finiteness of logarithmically bounded units.** Only finitely many units have logarithmic
embedding of norm at most `r`.

This reduces searches among units with bounded logarithmic embedding to finite searches. -/
theorem finite_setOf_norm_logEmbedding_le (r : ℝ) :
    {u : (𝓞 K)ˣ |
      ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ ≤ r}.Finite := by
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
    refine Set.finite_empty.subset ?_
    intro u hu
    exact (not_le_of_gt hr') ((norm_nonneg _).trans hu)

end TauCeti.NumberField.Units
