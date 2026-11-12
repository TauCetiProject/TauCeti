/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Count
public import TauCeti.SetTheory.Cardinal.Finite
import Mathlib.Logic.Equiv.Basic

/-!
# Matching countable enumerations of a counting measure

Two countable families of occurrences represent the same measure exactly when there is a
bijection between their indices preserving locations. Measurable singletons distinguish
locations, and countability ensures that equal extended multiplicities give equivalent
fibers, even when those fibers are infinite. Repeated locations and empty index types are
allowed. This permits constructions on enumerated occurrences to descend to measures.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The mass of a sum of Dirac measures at a singleton is the extended cardinality of
its fiber. The index type need not be countable. -/
theorem sum_dirac_apply_singleton {ι X : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] (x : ι → X) (a : X) :
    (Measure.sum fun i => Measure.dirac (x i)) {a} = ENat.card {i // x i = a} := by
  classical
  rw [← Set.coe_ofPred (fun i => x i = a), ← ENNReal.tsum_one,
    tsum_subtype {i | x i = a} (fun _ => (1 : ℝ≥0∞))]
  simp only [Measure.sum_apply _ (measurableSet_singleton a),
    Measure.dirac_apply' _ (measurableSet_singleton a), Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mem_ofPred_eq]

/-- Two countable occurrence enumerations give the same counting measure exactly when their
indices can be matched bijectively without changing locations. Infinite multiplicities are
allowed; no sigma-finiteness assumption is needed. -/
theorem sum_dirac_eq_sum_dirac_iff_exists_equiv
    {ι ι' X : Type*} [Countable ι] [Countable ι']
    [MeasurableSpace X] [MeasurableSingletonClass X] {x : ι → X} {y : ι' → X} :
    (Measure.sum fun i => Measure.dirac (x i)) =
      (Measure.sum fun j => Measure.dirac (y j)) ↔
      ∃ e : ι ≃ ι', ∀ i, y (e i) = x i := by
  classical
  constructor
  · intro h
    have hfiber (a : X) : Nonempty ({i // x i = a} ≃ {j // y j = a}) := by
      have hmass := congrArg (fun μ : Measure X => μ {a}) h
      rw [sum_dirac_apply_singleton, sum_dirac_apply_singleton] at hmass
      exact nonempty_equiv_of_enatCard_eq (ENat.toENNReal_inj.mp hmass)
    exact ⟨Equiv.ofFiberEquiv (fun a => (hfiber a).some), Equiv.ofFiberEquiv_map _⟩
  · rintro ⟨e, he⟩
    simpa only [Function.comp_def, he] using
      (Measure.sum_comp_equiv e (fun j => Measure.dirac (y j)))

end TauCeti
