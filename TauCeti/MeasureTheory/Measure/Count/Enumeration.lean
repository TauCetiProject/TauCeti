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

This file also records `Measure.sum_elim_zero_eq_sum_isSome` for restricting optional
enumerations `ι → Option X` to their present (`isSome`) indices.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Summing `Option.elim 0 f` over an optional family agrees with summing `f` over the
present (`isSome`) indices. -/
theorem sum_elim_zero_eq_sum_isSome {ι X Y : Type*} [MeasurableSpace Y]
    (x : ι → Option X) (f : X → Measure Y) :
    (Measure.sum fun i => (x i).elim 0 f) =
      Measure.sum fun i : {i : ι // (x i).isSome} => f ((x i.val).get i.property) := by
  classical
  have hfun : (fun i => (x i).elim (0 : Measure Y) f) =
      Function.extend Subtype.val
        (fun i : {i : ι // (x i).isSome} => f ((x i.val).get i.property)) 0 := by
    funext i
    by_cases hi : (x i).isSome
    · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hi
      simpa [ha] using (Subtype.val_injective.extend_apply
        (fun j : {j : ι // (x j).isSome} => f ((x j.val).get j.property))
        0 ⟨i, hi⟩).symm
    · have hnot : i ∉ Set.range (Subtype.val : {j : ι // (x j).isSome} → ι) := by
        rintro ⟨⟨j, hj⟩, rfl⟩
        exact hi hj
      rw [Option.not_isSome_iff_eq_none.mp hi, Option.elim_none,
        Function.extend_apply' _ _ _ hnot, Pi.zero_apply]
  rw [hfun, Measure.sum_extend_zero Subtype.val_injective]

end MeasureTheory.Measure

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
