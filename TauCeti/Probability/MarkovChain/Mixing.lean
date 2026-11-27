/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.Composition.TotalVariation
public import Mathlib.Probability.Kernel.Invariance
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Probability.Kernel.Composition.Power
import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.TotalVariation.Basic

/-!
# Worst-case total variation distances for Markov chains

`Kernel.tvToStationary` measures the worst-case distance from a time-`t` law to a reference
measure, and `Kernel.tvBetweenStarts` measures the worst-case distance between two time-`t`
laws. Both are real-valued suprema of half of Mathlib's total variation distance, with value
zero for an empty or unbounded family. For a Markov kernel, the distance between starts lies
in `[0, 1]`, as does the distance to a reference probability measure.

For a Markov kernel on a finite state space with measurable singletons, both distances are
nonincreasing. If the space is also nonempty, point starts attain the worst-case distances over
all initial probability laws. The distance between starts is submultiplicative and bounds the
factor by which additional steps contract the distance to an invariant probability measure.

## References

* D. A. Levin and Y. Peres, with contributions by E. L. Wilmer, *Markov Chains and Mixing Times*,
  second edition, American Mathematical Society, 2017, Lemmas 4.10 and 4.11 and Exercises 4.1–4.3.
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α]

/-- The worst-case normalized total variation distance after `t` steps from a reference
measure `π`. On a nonempty finite space the supremum is a maximum. The value is zero if the
space is empty, the row distances are unbounded, or the reference measure is infinite. -/
noncomputable def tvToStationary (κ : Kernel α α) (π : Measure α) (t : ℕ) : ℝ :=
  ⨆ x, tvDist ((κ ^ t) x) π / 2

/-- The worst-case normalized total variation distance between two `t`-step laws. On a
nonempty finite space the supremum is a maximum. The value is zero if the space is empty
or the row distances are unbounded. -/
noncomputable def tvBetweenStarts (κ : Kernel α α) (t : ℕ) : ℝ :=
  ⨆ z : α × α, tvDist ((κ ^ t) z.1) ((κ ^ t) z.2) / 2

/-- The supremum formula for the worst-case distance to a fixed measure. -/
theorem tvToStationary_def (κ : Kernel α α) (π : Measure α) (t : ℕ) :
    κ.tvToStationary π t = ⨆ x, tvDist ((κ ^ t) x) π / 2 := (rfl)

/-- The supremum formula for the worst-case distance between starts. -/
theorem tvBetweenStarts_def (κ : Kernel α α) (t : ℕ) :
    κ.tvBetweenStarts t = ⨆ z : α × α, tvDist ((κ ^ t) z.1) ((κ ^ t) z.2) / 2 := (rfl)

/-- The worst-case distance to the reference measure is nonnegative. -/
theorem tvToStationary_nonneg {κ : Kernel α α} {π : Measure α} {t : ℕ} :
    0 ≤ κ.tvToStationary π t :=
  Real.iSup_nonneg fun _ ↦ div_nonneg tvDist_nonneg (by norm_num)

/-- The worst-case distance between starts is nonnegative. -/
theorem tvBetweenStarts_nonneg {κ : Kernel α α} {t : ℕ} : 0 ≤ κ.tvBetweenStarts t :=
  Real.iSup_nonneg fun _ ↦ div_nonneg tvDist_nonneg (by norm_num)

/-- On a subsingleton state space, the worst-case distance to a reference probability measure
is zero. -/
@[simp] theorem tvToStationary_of_subsingleton [Subsingleton α] (κ : Kernel α α)
    [IsMarkovKernel κ] (π : Measure α) [IsProbabilityMeasure π] (t : ℕ) :
    κ.tvToStationary π t = 0 := by
  have h (x : α) : tvDist ((κ ^ t) x) π = 0 := by
    rw [((κ ^ t) x).eq_dirac_of_subsingleton x, π.eq_dirac_of_subsingleton x, tvDist_self]
  simp [tvToStationary_def, h]

/-- On a subsingleton state space, the worst-case distance between starts is zero. -/
@[simp] theorem tvBetweenStarts_of_subsingleton [Subsingleton α] (κ : Kernel α α) (t : ℕ) :
    κ.tvBetweenStarts t = 0 := by
  have h (z : α × α) : tvDist ((κ ^ t) z.1) ((κ ^ t) z.2) = 0 := by
    rw [Subsingleton.elim z.2 z.1, tvDist_self]
  simp [tvBetweenStarts_def, h]

variable {κ : Kernel α α} {π : Measure α} {s t : ℕ}

section RowBounds

variable [Finite α] (κ)

/-- Each point start is bounded by the worst-case distance to the reference measure. -/
theorem tvDist_pow_apply_le_tvToStationary (x : α) :
    tvDist ((κ ^ t) x) π / 2 ≤ κ.tvToStationary π t :=
  le_ciSup (f := fun z ↦ tvDist ((κ ^ t) z) π / 2) (Set.finite_range _).bddAbove x

/-- Each pair of point starts is bounded by the worst-case distance between starts. -/
theorem tvDist_pow_apply_le_tvBetweenStarts (x y : α) :
    tvDist ((κ ^ t) x) ((κ ^ t) y) / 2 ≤ κ.tvBetweenStarts t :=
  le_ciSup (f := fun z : α × α ↦ tvDist ((κ ^ t) z.1) ((κ ^ t) z.2) / 2)
    (Set.finite_range _).bddAbove (x, y)

variable {κ} [Nonempty α]

/-- A uniform upper bound for the distances of the rows bounds the worst-case distance. -/
theorem tvToStationary_le_iff {r : ℝ} :
    κ.tvToStationary π t ≤ r ↔ ∀ x, tvDist ((κ ^ t) x) π / 2 ≤ r :=
  ciSup_le_iff (Set.finite_range _).bddAbove

/-- A uniform upper bound for the distances between pairs of rows bounds the worst-case
distance between starts. -/
theorem tvBetweenStarts_le_iff {r : ℝ} :
    κ.tvBetweenStarts t ≤ r ↔ ∀ x y, tvDist ((κ ^ t) x) ((κ ^ t) y) / 2 ≤ r := by
  rw [tvBetweenStarts_def, ciSup_le_iff (Set.finite_range _).bddAbove]
  exact Prod.forall

end RowBounds

/-- The worst-case distance between starts is at most twice the distance to any fixed finite
measure. -/
theorem tvBetweenStarts_le_two_mul_tvToStationary [Finite α] [IsFiniteMeasure π] :
    κ.tvBetweenStarts t ≤ 2 * κ.tvToStationary π t := by
  rw [tvBetweenStarts_def]
  refine Real.iSup_le (fun ⟨x, y⟩ ↦ ?_) (mul_nonneg (by norm_num) tvToStationary_nonneg)
  have h := tvDist_triangle ((κ ^ t) x) π ((κ ^ t) y)
  rw [tvDist_comm π] at h
  linarith [κ.tvDist_pow_apply_le_tvToStationary (π := π) (t := t) x,
    κ.tvDist_pow_apply_le_tvToStationary (π := π) (t := t) y]

section ProbabilityBounds

variable [IsMarkovKernel κ]

/-- The worst-case distance to a reference probability measure is at most one. -/
theorem tvToStationary_le_one [IsProbabilityMeasure π] : κ.tvToStationary π t ≤ 1 := by
  rw [tvToStationary_def]
  exact Real.iSup_le (fun _ ↦ tvDist_div_two_le_one) zero_le_one

/-- The worst-case distance between starts is at most one. -/
theorem tvBetweenStarts_le_one : κ.tvBetweenStarts t ≤ 1 := by
  rw [tvBetweenStarts_def]
  exact Real.iSup_le (fun _ ↦ tvDist_div_two_le_one) zero_le_one

end ProbabilityBounds

section TimeZero

variable (κ)

/-- At time zero, the distance to a reference probability measure is one minus its smallest
singleton mass on a finite state space. -/
theorem tvToStationary_zero [Finite α] [IsProbabilityMeasure π] :
    κ.tvToStationary π 0 = 1 - ⨅ x, π.real {x} := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure π
  simp only [tvToStationary_def, pow_zero, one_apply, tvDist_dirac_left,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hb := (Set.finite_range (fun x : α ↦ π.real {x})).bddBelow
  have hd := (Set.finite_range (fun x : α ↦ 1 - π.real {x})).bddAbove
  refine le_antisymm (ciSup_le fun x ↦ sub_le_sub_left (ciInf_le hb x) 1) ?_
  apply sub_le_comm.mp
  refine le_ciInf fun x ↦ ?_
  linarith [le_ciSup hd x]

variable [MeasurableSingletonClass α]

/-- Distinct states have disjoint time-zero laws, so the worst-case distance is one. -/
@[simp] theorem tvBetweenStarts_zero [Finite α] [Nontrivial α] :
    κ.tvBetweenStarts 0 = 1 := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne α
  have h : 1 ≤ κ.tvBetweenStarts 0 := by
    simpa [Measure.dirac_real_apply, hxy.symm] using
      κ.tvDist_pow_apply_le_tvBetweenStarts (t := 0) x y
  refine le_antisymm ?_ h
  rw [tvBetweenStarts_def]
  refine Real.iSup_le (fun ⟨a, b⟩ ↦ ?_) zero_le_one
  simp only [pow_zero, one_apply, tvDist_dirac_left]
  linarith [measureReal_nonneg (μ := Measure.dirac b) (s := {a})]

end TimeZero

variable [Finite α] [MeasurableSingletonClass α] (κ)

/-- The distance after `t` steps from any initial distribution to a fixed measure is bounded
by the worst-case distance from point starts. -/
theorem tvDist_pow_comp_le_tvToStationary [IsFiniteKernel κ] (μ : Measure α)
    [IsProbabilityMeasure μ] :
    tvDist ((κ ^ t : Kernel α α) ∘ₘ μ) π / 2 ≤ κ.tvToStationary π t := by
  by_cases hπ : IsFiniteMeasure π
  · let := Fintype.ofFinite α
    have h := μ.tvDist_comp_le_sum (κ ^ t) (Kernel.const α π)
    simp only [Measure.const_comp, measure_univ, one_smul, Kernel.const_apply] at h
    apply (div_le_iff₀ (by norm_num)).mpr
    calc
      _ ≤ ∑ x, μ.real {x} * tvDist ((κ ^ t) x) π := h
      _ ≤ ∑ x, μ.real {x} * (κ.tvToStationary π t * 2) :=
        Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left
          ((div_le_iff₀ (by norm_num)).mp (κ.tvDist_pow_apply_le_tvToStationary x))
          measureReal_nonneg
      _ = κ.tvToStationary π t * 2 := by
        rw [← Finset.sum_mul, sum_measureReal_singleton, Finset.coe_univ]
        simp
  · simpa only [tvDist_of_not_isFiniteMeasure_right hπ, zero_div] using
      (tvToStationary_nonneg (κ := κ) (π := π) (t := t))

/-- After `t` steps, the distance between the evolved laws is bounded by the initial
distance multiplied by the worst-case distance between point starts. -/
theorem tvDist_pow_comp_le_mul_tvBetweenStarts [IsFiniteKernel κ] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist ((κ ^ t : Kernel α α) ∘ₘ μ) ((κ ^ t : Kernel α α) ∘ₘ ν) / 2 ≤
      tvDist μ ν / 2 * κ.tvBetweenStarts t := by
  have h := μ.tvDist_comp_le_mul (κ ^ t) (ν := ν) (by simp)
    (c := κ.tvBetweenStarts t) fun x y ↦ by
      linarith [κ.tvDist_pow_apply_le_tvBetweenStarts (t := t) x y]
  linarith

/-- After `t` steps, any two initial distributions have distance at most the worst-case
distance between point starts. -/
theorem tvDist_pow_comp_le_tvBetweenStarts [IsFiniteKernel κ] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist ((κ ^ t : Kernel α α) ∘ₘ μ) ((κ ^ t : Kernel α α) ∘ₘ ν) / 2 ≤ κ.tvBetweenStarts t := by
  refine (κ.tvDist_pow_comp_le_mul_tvBetweenStarts μ ν).trans ?_
  exact mul_le_of_le_one_left tvBetweenStarts_nonneg tvDist_div_two_le_one

/-- The worst-case distance to the reference measure is attained over all initial
probability laws, including point masses. -/
theorem isGreatest_tvToStationary [Nonempty α] [IsFiniteKernel κ] :
    IsGreatest (range fun μ : ProbabilityMeasure α ↦
      tvDist ((κ ^ t : Kernel α α) ∘ₘ (μ : Measure α)) π / 2)
      (κ.tvToStationary π t) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := Finite.ciSup_mem (fun x ↦ tvDist ((κ ^ t) x) π / 2)
    refine ⟨⟨Measure.dirac x, inferInstance⟩, ?_⟩
    simpa only [ProbabilityMeasure.coe_mk, Measure.dirac_bind (κ ^ t).measurable,
      tvToStationary_def] using hx
  · rintro _ ⟨μ, rfl⟩
    exact κ.tvDist_pow_comp_le_tvToStationary (μ : Measure α)

/-- The worst-case distance between starts is attained over all pairs of initial
probability laws, including pairs of point masses. -/
theorem isGreatest_tvBetweenStarts [Nonempty α] [IsFiniteKernel κ] :
    IsGreatest (range fun z : ProbabilityMeasure α × ProbabilityMeasure α ↦
      tvDist ((κ ^ t : Kernel α α) ∘ₘ (z.1 : Measure α))
        ((κ ^ t : Kernel α α) ∘ₘ (z.2 : Measure α)) / 2)
      (κ.tvBetweenStarts t) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨x, y⟩, hxy⟩ :=
      Finite.ciSup_mem (fun z : α × α ↦ tvDist ((κ ^ t) z.1) ((κ ^ t) z.2) / 2)
    refine ⟨(⟨Measure.dirac x, inferInstance⟩, ⟨Measure.dirac y, inferInstance⟩), ?_⟩
    simpa only [ProbabilityMeasure.coe_mk, Measure.dirac_bind (κ ^ t).measurable,
      tvBetweenStarts_def] using hxy
  · rintro _ ⟨⟨μ, ν⟩, rfl⟩
    exact κ.tvDist_pow_comp_le_tvBetweenStarts (μ : Measure α) (ν : Measure α)

/-- For an invariant probability measure, the distance to stationarity is at most the
worst-case distance between starts. -/
theorem tvToStationary_le_tvBetweenStarts [IsFiniteKernel κ] [IsProbabilityMeasure π]
    (hπ : κ.Invariant π) :
    κ.tvToStationary π t ≤ κ.tvBetweenStarts t := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure π
  refine tvToStationary_le_iff.mpr fun x ↦ ?_
  simpa only [Measure.dirac_bind (κ ^ t).measurable, hπ.pow_comp] using
    κ.tvDist_pow_comp_le_tvBetweenStarts (t := t) (Measure.dirac x) π

variable {κ} [IsMarkovKernel κ]

/-- The worst-case distance between starts is submultiplicative in time. -/
theorem tvBetweenStarts_add_le :
    κ.tvBetweenStarts (s + t) ≤ κ.tvBetweenStarts s * κ.tvBetweenStarts t := by
  rw [tvBetweenStarts_def]
  refine Real.iSup_le (fun ⟨x, y⟩ ↦ ?_) (mul_nonneg tvBetweenStarts_nonneg tvBetweenStarts_nonneg)
  rw [Nat.add_comm, Kernel.pow_add, Kernel.comp_apply, Kernel.comp_apply]
  exact (κ.tvDist_pow_comp_le_mul_tvBetweenStarts (t := t)
    ((κ ^ s) x) ((κ ^ s) y)).trans
    (mul_le_mul_of_nonneg_right (κ.tvDist_pow_apply_le_tvBetweenStarts x y)
      tvBetweenStarts_nonneg)

/-- For an invariant probability measure, the worst-case distance after `s + t` steps is at
most the distance to stationarity at time `s` times the distance between starts at time `t`. -/
theorem tvToStationary_add_le [IsProbabilityMeasure π] (hπ : κ.Invariant π) :
    κ.tvToStationary π (s + t) ≤ κ.tvToStationary π s * κ.tvBetweenStarts t := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure π
  refine tvToStationary_le_iff.mpr fun x ↦ ?_
  rw [Nat.add_comm, Kernel.pow_add, Kernel.comp_apply]
  have h := κ.tvDist_pow_comp_le_mul_tvBetweenStarts (t := t) ((κ ^ s) x) π
  rw [hπ.pow_comp] at h
  exact h.trans (mul_le_mul_of_nonneg_right (κ.tvDist_pow_apply_le_tvToStationary x)
    tvBetweenStarts_nonneg)

/-- The worst-case distance to any fixed measure is nonincreasing in time. -/
theorem tvToStationary_antitone : Antitone (κ.tvToStationary π) := by
  intro s t hst
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [tvToStationary_def]
  refine Real.iSup_le (fun x ↦ ?_) tvToStationary_nonneg
  rw [Kernel.pow_add, Kernel.comp_apply]
  exact κ.tvDist_pow_comp_le_tvToStationary ((κ ^ u) x)

/-- The worst-case distance between starts is nonincreasing in time. -/
theorem tvBetweenStarts_antitone : Antitone κ.tvBetweenStarts := by
  intro s t hst
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact tvBetweenStarts_add_le.trans (mul_le_of_le_one_right tvBetweenStarts_nonneg
    tvBetweenStarts_le_one)

end ProbabilityTheory.Kernel
