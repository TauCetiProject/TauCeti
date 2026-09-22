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

This reduces searches among units with bounded logarithmic embedding to finite searches. -/
theorem finite_setOf_norm_logEmbedding_le (r : ℝ) :
    {u : (𝓞 K)ˣ |
      ‖NumberField.Units.logEmbedding K (Additive.ofMul u)‖ ≤ r}.Finite := by
  change {u : Additive ((𝓞 K)ˣ) |
    ‖NumberField.Units.logEmbedding K u‖ ≤ r}.Finite
  let f := NumberField.Units.logEmbedding K
  let _ : Finite f.ker := by
    rw [NumberField.Units.dirichletUnitTheorem.logEmbedding_ker]
    refine Finite.of_injective
      (fun x : (NumberField.Units.torsion K).toAddSubgroup =>
        Additive.ofMul (⟨x.1.toMul, x.property⟩ : NumberField.Units.torsion K)) ?_
    intro x y h
    exact Subtype.ext (congrArg Subtype.val h)
  refine Set.Finite.of_finite_fibers f ?_ ?_
  · -- Reuse Mathlib's finiteness of the unit lattice inside a closed ball.
    refine (NumberField.Units.dirichletUnitTheorem.unitLattice_inter_ball_finite K r).subset ?_
    rintro y ⟨u, hu, rfl⟩
    exact ⟨⟨u, Submodule.mem_top, rfl⟩, mem_closedBall_zero_iff.mpr hu⟩
  · rintro y ⟨u, hu, rfl⟩
    let _ : Finite (f ⁻¹' {f u}) :=
      Finite.of_equiv f.ker (f.fiberEquivKer u).symm
    exact Set.toFinite _

end TauCeti.NumberField.Units
