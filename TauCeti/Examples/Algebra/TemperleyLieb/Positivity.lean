/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Positivity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Examples of Markov-trace positivity and the first bad level

Concrete evaluations illustrating Jones's positivity theorem and the first bad level
`⌊π / arccos (δ / 2)⌋₊` for the Hermitian forms `(x, y) ↦ tr n (x⋆ * y)` of a Temperley–Lieb Markov
trace:

* **At `δ = 1 / 2`:** `1 / 2` lies in `(2 cos (π / 2), 2 cos (π / 3)) = (0, 1)`, so it is
  inadmissible with first bad level `⌊π / arccos (1 / 4)⌋₊ = 2`. The Hermitian forms are positive
  semidefinite on zero and one strand, whereas `f_2 = 1 - 2 • e_0` is a self-adjoint idempotent of
  trace `(1 / 2)² - 1 = -3 / 4 < 0`.
* **At `δ = 0`:** every Markov trace vanishes on one or more strands and is the identity on zero
  strands, so the Hermitian forms are positive semidefinite at every level even though
  `0 ∉ jonesLoopParameters`; the spin-model trace at `q = i` realizes such a Markov trace. This
  shows that `0 < δ` cannot be omitted in `IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`.
* **At `δ < 0`:** positivity fails already on one strand, since `tr 1 (1⋆ * 1) = δ < 0`.
* **For `1 < δ < √2`:** `δ` lies in `(2 cos (π / 3), 2 cos (π / 4))`, so it is inadmissible with
  first bad level `3`; `tr 2 f_2 = δ² - 1 > 0` while `tr 3 f_3 = δ³ - 2 δ < 0`.
* **At `δ = √2 = 2 cos (π / 4)`:** `√2` is admissible, `[4] = 0`, all Hermitian forms are positive
  semidefinite, and `f_3` lies in the trace radical (`tr 3 f_3 = 0`) without becoming negative.
* **Wrong recursion coefficient:** Wenzl's recursion gives `f_2 = 1 - δ⁻¹ • e_0` of trace
  `δ² - 1 = [3]`, whereas replacing `[1] / [2] = δ⁻¹` by `[2] / [1] = δ` gives `1 - δ • e_0`,
  which for `δ ≠ 0` over a domain is idempotent only when `δ² = 1`.
-/

public section

open Real TauCeti TauCeti.TemperleyLieb
open scoped ComplexOrder

namespace TauCeti.Examples.TemperleyLieb

/-- Every real loop parameter is self-adjoint when coerced to `ℂ`. -/
local instance (δ : ℝ) : Fact (IsSelfAdjoint (δ : ℂ)) :=
  ⟨Complex.conj_ofReal δ⟩

/-- For a nonzero real loop parameter `δ` with `δ² ≠ 1`, the quantum integers `[1], [2], [3]` are
units in `ℂ`. -/
private theorem isUnit_qInt_of_mem_Icc_three {δ : ℝ} (hδ : δ ≠ 0) (hδ2 : δ ^ 2 ≠ 1)
    {k : ℕ} (hk : k ∈ Finset.Icc 1 3) : IsUnit (qInt ℂ (δ : ℂ) k) := by
  have hq : qInt ℂ (δ : ℂ) k = (qInt ℝ δ k : ℂ) := (Complex.ofRealHom.map_qInt δ k).symm
  rw [hq]
  fin_cases hk
  · simp
  · exact (Complex.ofReal_ne_zero.2 (by rwa [qInt_two])).isUnit
  · exact (Complex.ofReal_ne_zero.2 (by rw [qInt_three]; exact sub_ne_zero.2 hδ2)).isUnit

/-- The loop parameter `1 / 2` is inadmissible, with first bad level `⌊π / arccos (1 / 4)⌋₊ = 2`. -/
theorem notMem_jonesLoopParameters_one_half_and_floor :
    (1 / 2 : ℝ) ∉ jonesLoopParameters ∧ ⌊π / arccos ((1 / 2 : ℝ) / 2)⌋₊ = 2 := by
  have hlo : 2 * cos (π / (2 : ℕ)) < (1 / 2 : ℝ) := by simp
  have hhi : (1 / 2 : ℝ) < 2 * cos (π / (2 + 1 : ℕ)) := by
    norm_num [show ((2 + 1 : ℕ) : ℝ) = 3 by norm_num, Real.cos_pi_div_three]
  exact ⟨notMem_jonesLoopParameters_of_Ioo (by omega) hlo hhi,
    floor_pi_div_arccos_eq_of_Ioo (by omega) hlo hhi⟩

/-- At `δ = 1 / 2`, a Markov trace is positive semidefinite on fewer than two strands, while the
two-strand Jones–Wenzl projection `f_2` is a self-adjoint idempotent of trace `-3 / 4`. -/
theorem one_half_first_bad_level
    {tr : ∀ n : ℕ, TauCeti.TemperleyLieb ℂ ((1 / 2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((1 / 2 : ℝ) : ℂ) tr) :
    (∀ n < 2, ∀ x, 0 ≤ tr n (star x * x)) ∧
      IsSelfAdjoint (jonesWenzl ((1 / 2 : ℝ) : ℂ) 2) ∧
      IsIdempotentElem (jonesWenzl ((1 / 2 : ℝ) : ℂ) 2) ∧
      tr 2 (jonesWenzl ((1 / 2 : ℝ) : ℂ) 2) = -3 / 4 := by
  obtain ⟨hnotMem, hfloor⟩ := notMem_jonesLoopParameters_one_half_and_floor
  have hunit : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ ((1 / 2 : ℝ) : ℂ) k) := fun _ hk ↦
    isUnit_qInt_of_mem_Icc_three (by norm_num) (by norm_num)
      (Finset.Icc_subset_Icc le_rfl (by omega) hk)
  refine ⟨fun n hn x ↦ htr.map_star_mul_self_nonneg_of_lt_floor (by norm_num) hnotMem
      (hfloor.symm ▸ hn) x,
    isSelfAdjoint_jonesWenzl 2, isIdempotentElem_jonesWenzl hunit, ?_⟩
  rw [htr.map_jonesWenzl 2 hunit, qInt_three]
  norm_num

/-- At `δ = 0`, `0 ∉ jonesLoopParameters`, yet a Markov trace exists (realized by the spin model at
`q = i`), vanishes in every positive degree, and has positive semidefinite Hermitian forms in all
degrees. Thus `0 < δ` is essential in `IsMarkovTrace.forall_map_star_mul_self_nonneg_iff`. -/
theorem zero_loopParameter_counterexample :
    (0 : ℝ) ∉ jonesLoopParameters ∧
      (∃ tr : ∀ n : ℕ, TauCeti.TemperleyLieb ℂ ((0 : ℝ) : ℂ) n →ₗ[ℂ] ℂ,
        IsMarkovTrace ℂ ((0 : ℝ) : ℂ) tr) ∧
      ∀ {tr : ∀ n : ℕ, TauCeti.TemperleyLieb ℂ ((0 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
        (_ : IsMarkovTrace ℂ ((0 : ℝ) : ℂ) tr),
        (∀ n, tr (n + 1) = 0) ∧ ∀ n x, 0 ≤ tr n (star x * x) := by
  refine ⟨notMem_jonesLoopParameters_of_nonpos le_rfl, ?_, fun htr ↦ ?_⟩
  · let q : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
    have hq : ((0 : ℝ) : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ)) := by
      simp [q, Complex.inv_I]
    exact ⟨fun _ ↦ markovTrace q hq, isMarkovTrace_markovTrace q hq⟩
  · refine ⟨htr.apply_succ_eq_zero_of_eq_zero (by simp), fun n x ↦ ?_⟩
    exact htr.map_star_mul_self_nonneg_of_eq_two_mul_cos (m := 2) le_rfl (by simp) x

/-- At any negative loop parameter `δ < 0`, positivity fails already on one strand because
`tr 1 (1⋆ * 1) = δ < 0`. -/
theorem map_star_one_mul_one_neg_of_neg {δ : ℝ} (hδ : δ < 0)
    {tr : ∀ n : ℕ, TauCeti.TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    tr 1 (star 1 * 1) < 0 := by
  rw [star_one, mul_one, htr.map_one 1, pow_one]
  exact_mod_cast hδ

/-- Every loop parameter `δ` strictly between `1` and `√2` is inadmissible with first bad level `3`:
the Hermitian forms are positive semidefinite on fewer than three strands and
`tr 2 f_2 = δ² - 1 > 0`, whereas `tr 3 f_3 = δ³ - 2 δ < 0`. -/
theorem between_one_and_sqrt_two_first_bad_level {δ : ℝ} (h1 : 1 < δ) (h2 : δ < √2)
    {tr : ∀ n : ℕ, TauCeti.TemperleyLieb ℂ (δ : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (δ : ℂ) tr) :
    δ ∉ jonesLoopParameters ∧
      ⌊π / arccos (δ / 2)⌋₊ = 3 ∧
      (∀ n < 3, ∀ x, 0 ≤ tr n (star x * x)) ∧
      tr 2 (jonesWenzl (δ : ℂ) 2) = ((δ ^ 2 - 1 : ℝ) : ℂ) ∧
      0 < tr 2 (jonesWenzl (δ : ℂ) 2) ∧
      tr 3 (jonesWenzl (δ : ℂ) 3) = ((δ ^ 3 - 2 * δ : ℝ) : ℂ) ∧
      tr 3 (jonesWenzl (δ : ℂ) 3) < 0 := by
  have hlo : 2 * cos (π / (3 : ℕ)) < δ := by
    norm_num [Real.cos_pi_div_three]
    exact h1
  have hhi : δ < 2 * cos (π / (3 + 1 : ℕ)) := by
    rw [show ((3 + 1 : ℕ) : ℝ) = 4 by norm_num, Real.cos_pi_div_four]
    linarith
  have hnotMem : δ ∉ jonesLoopParameters := notMem_jonesLoopParameters_of_Ioo (by omega) hlo hhi
  have hfloor : ⌊π / arccos (δ / 2)⌋₊ = 3 := floor_pi_div_arccos_eq_of_Ioo (by omega) hlo hhi
  have hδpos : 0 < δ := by linarith
  have hsq_lt : δ ^ 2 < 2 := by
    nlinarith [Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsq_gt : 1 < δ ^ 2 := by nlinarith
  have hq (j : ℕ) : qInt ℂ (δ : ℂ) j = (qInt ℝ δ j : ℂ) :=
    (Complex.ofRealHom.map_qInt δ j).symm
  have hunit3 : ∀ k ∈ Finset.Icc 1 3, IsUnit (qInt ℂ (δ : ℂ) k) :=
    fun _ ↦ isUnit_qInt_of_mem_Icc_three hδpos.ne' hsq_gt.ne'
  have hunit2 : ∀ k ∈ Finset.Icc 1 2, IsUnit (qInt ℂ (δ : ℂ) k) :=
    fun k hk ↦ hunit3 k (Finset.Icc_subset_Icc le_rfl (by omega) hk)
  have hf2 : tr 2 (jonesWenzl (δ : ℂ) 2) = ((δ ^ 2 - 1 : ℝ) : ℂ) := by
    rw [htr.map_jonesWenzl 2 hunit2, hq, qInt_three]
  have hf3 : tr 3 (jonesWenzl (δ : ℂ) 3) = ((δ ^ 3 - 2 * δ : ℝ) : ℂ) := by
    rw [htr.map_jonesWenzl 3 hunit3, hq, qInt_four]
  refine ⟨hnotMem, hfloor,
    fun n hn x ↦ htr.map_star_mul_self_nonneg_of_lt_floor hδpos hnotMem (hfloor.symm ▸ hn) x,
    hf2, ?_, hf3, ?_⟩
  · rw [hf2]
    exact_mod_cast sub_pos.2 hsq_gt
  · rw [hf3]
    have hneg : δ ^ 3 - 2 * δ < 0 := by
      have : δ ^ 3 - 2 * δ = δ * (δ ^ 2 - 2) := by ring
      rw [this]
      exact mul_neg_of_pos_of_neg hδpos (sub_neg.2 hsq_lt)
    exact_mod_cast hneg

/-- At the admissible loop parameter `δ = √2 = 2 cos (π / 4)`, `[4] = 0`, all Hermitian forms of a
Markov trace are positive semidefinite, and `f_3` has trace zero and therefore lies in the trace
radical. -/
theorem sqrt_two_jonesWenzl_three_mem_traceRadical
    {tr : ∀ n : ℕ, TauCeti.TemperleyLieb ℂ ((√2 : ℝ) : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ ((√2 : ℝ) : ℂ) tr) :
    √2 ∈ jonesLoopParameters ∧
      qInt ℝ (√2) 4 = 0 ∧
      (∀ n x, 0 ≤ tr n (star x * x)) ∧
      tr 3 (jonesWenzl ((√2 : ℝ) : ℂ) 3) = 0 ∧
      jonesWenzl ((√2 : ℝ) : ℂ) 3 ∈ (tr 3).traceRadical (htr.map_mul_comm 3) := by
  have hmem : √2 ∈ jonesLoopParameters :=
    mem_jonesLoopParameters.2
      (Or.inl ⟨4, by omega, by rw [show ((4 : ℕ) : ℝ) = 4 by norm_num, Real.cos_pi_div_four]; ring⟩)
  have hq4 : qInt ℝ (√2) 4 = 0 := by
    rw [qInt_four, show (√2 : ℝ) ^ 3 = √2 ^ 2 * √2 by ring, Real.sq_sqrt zero_le_two]
    ring
  have hunit3 : ∀ k ∈ Finset.Icc 1 3, IsUnit (qInt ℂ ((√2 : ℝ) : ℂ) k) := fun _ ↦
    isUnit_qInt_of_mem_Icc_three (by positivity) (by rw [Real.sq_sqrt zero_le_two]; norm_num)
  have htr3 : tr 3 (jonesWenzl ((√2 : ℝ) : ℂ) 3) = 0 := by
    rw [htr.map_jonesWenzl 3 hunit3]
    exact (Complex.ofRealHom.map_qInt (√2) 4).symm.trans (by simp [hq4])
  refine ⟨hmem, hq4,
    fun n x ↦ htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hmem x, htr3, ?_⟩
  rw [htr.mem_traceRadical_iff_map_star_mul_self_eq_zero
      (htr.map_star_mul_self_nonneg_of_mem_jonesLoopParameters hmem),
    star_jonesWenzl, (isIdempotentElem_jonesWenzl hunit3).eq, htr3]

/-- Over an integral domain with `δ ≠ 0`, replacing the Wenzl recursion coefficient
`[1] / [2] = δ⁻¹` on two strands by `[2] / [1] = δ` produces `1 - δ • e_0`, which is idempotent if
and only if `δ² = 1`. -/
theorem isIdempotentElem_one_sub_smul_e_iff {R : Type*} [CommRing R] [IsDomain R] {δ : R}
    (hδ : δ ≠ 0) :
    IsIdempotentElem (1 - δ • e δ (0 : Fin 1) : TauCeti.TemperleyLieb R δ 2) ↔ δ ^ 2 = 1 := by
  set u : TauCeti.TemperleyLieb R δ 2 := e δ (0 : Fin 1) with hu
  have hexpand : (1 - δ • u) * (1 - δ • u) = 1 + (δ ^ 3 - 2 * δ) • u := by
    have hsq : (δ • u) * (δ • u) = (δ ^ 3) • u := by
      rw [smul_mul_assoc, mul_smul_comm, hu, e_mul_self, smul_smul, smul_smul]
      congr 1
      ring
    rw [mul_sub, mul_one, sub_mul, one_mul, hsq]
    simp only [sub_eq_add_neg, neg_add_rev, neg_neg, ← neg_smul, add_assoc, ← add_smul]
    congr 2
    ring
  rw [IsIdempotentElem, hexpand]
  constructor
  · intro hid
    have hsmul : (δ ^ 3 - 2 * δ) • u = (-δ) • u := by
      have hsub : 1 + (δ ^ 3 - 2 * δ) • u = 1 + (-δ) • u := by
        simpa [sub_eq_add_neg, neg_smul] using hid
      exact add_left_cancel hsub
    rw [hu] at hsmul
    have hcoeff : δ ^ 3 - 2 * δ = -δ := smul_left_injective_e_two 0 hsmul
    have hmul : δ * (δ ^ 2 - 1) = 0 := by linear_combination hcoeff
    exact sub_eq_zero.1 ((mul_eq_zero.1 hmul).resolve_left hδ)
  · intro hsq
    have hcoeff : δ ^ 3 - 2 * δ = -δ := by linear_combination δ * hsq
    rw [hcoeff, neg_smul, ← sub_eq_add_neg]

end TauCeti.Examples.TemperleyLieb
