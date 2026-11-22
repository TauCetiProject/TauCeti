/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Cesàro averages under shifts, finite modifications, and residue decompositions

* `TauCeti.tendsto_natCast_add_div_add_one`: limit `((n : ℝ) + c) / ((n : ℝ) + 1) → 1`.
* `TauCeti.tendsto_add_sub_div_div_succ`: residue-count density `((n + q - r) / q) / (n + 1) → q⁻¹`.
* `TauCeti.tendsto_cesaro_congr_of_eventuallyEq`, `TauCeti.tendsto_cesaro_comp_add_iff`:
  finite-modification and index-shift invariance.
* `TauCeti.tendsto_cesaro_of_forall_mod`, `TauCeti.tendsto_cesaro_mul_add_of_ite_mod`:
  residue-class decompositions modulo `q > 0`.
-/

public section

open Filter Finset Topology

namespace TauCeti

/-- For any real constant `c`, `((n : ℝ) + c) / ((n : ℝ) + 1)` converges to `1`. -/
theorem tendsto_natCast_add_div_add_one (c : ℝ) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + c) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  simpa [add_comm c, add_comm (1 : ℝ), one_mul] using
    tendsto_add_mul_div_add_mul_atTop_nhds c 1 1 (one_ne_zero : (1 : ℝ) ≠ 0)

/-- For `q > 0` and `r < q`, `((n + q - r) / q) / (n + 1)` converges to `q⁻¹`. -/
theorem tendsto_add_sub_div_div_succ {q r : ℕ} (hq : 0 < q) (hr : r < q) :
    Tendsto (fun n : ℕ ↦ (((n + q - r) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (q : ℝ)⁻¹) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlo : Tendsto (fun n : ℕ ↦ (q : ℝ)⁻¹ * (1 - (r + 1 : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 (q : ℝ)⁻¹) := by
    simpa using (tendsto_const_nhds (x := (q : ℝ)⁻¹)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (hinv.const_mul (r + 1 : ℝ)))
  have hhi : Tendsto (fun n : ℕ ↦ (q : ℝ)⁻¹ * (1 + ((q : ℝ) - 1) * ((n + 1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 (q : ℝ)⁻¹) := by
    simpa using (tendsto_const_nhds (x := (q : ℝ)⁻¹)).mul
      ((tendsto_const_nhds (x := (1 : ℝ))).add (hinv.const_mul ((q : ℝ) - 1)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n ↦ ?_) (fun n ↦ ?_)
  all_goals
    have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    have hnat : ((q * ((n + q - r) / q) + (n + q - r) % q : ℕ) : ℝ) = ((n + q - r : ℕ) : ℝ) := by
      exact_mod_cast Nat.div_add_mod (n + q - r) q
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add] at hnat
  · have hmod_le : (((n + q - r) % q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt _ hq).le
    rw [(by field_simp; push_cast; ring : 1 - (r + 1 : ℝ) * ((n + 1 : ℕ) : ℝ)⁻¹ =
        ((n : ℝ) - r) / ((n + 1 : ℕ) : ℝ)), inv_mul_eq_div, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · rw [(by field_simp; push_cast; ring : 1 + ((q : ℝ) - 1) * ((n + 1 : ℕ) : ℝ)⁻¹ =
        ((n : ℝ) + q) / ((n + 1 : ℕ) : ℝ)), inv_mul_eq_div, div_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) ((n + q - r) % q), Nat.cast_nonneg (α := ℝ) r]

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Changing finitely many terms does not alter convergence or limit of Cesàro averages. -/
theorem tendsto_cesaro_congr_of_eventuallyEq {f g : ℕ → E} {L : E} (hfg : f =ᶠ[atTop] g) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i) atTop (𝓝 L) ↔
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), g i) atTop (𝓝 L) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfg
  have hlim : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range N, (f i - g i))
      atTop (𝓝 0) := by simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (∑ i ∈ range N, (f i - g i))
  have hdiff : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i -
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), g i) atTop (𝓝 0) := by
    refine hlim.congr' (eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩); dsimp only
    rw [← smul_sub, ← sum_sub_distrib, ← sum_range_add_sum_Ico _ (by omega : N ≤ n + 1),
      sum_eq_zero (s := Ico N (n + 1)) fun i hi ↦ by rw [hN i (mem_Ico.mp hi).1, sub_self],
      add_zero]
  exact ⟨fun hf ↦ by simpa using hf.sub hdiff, fun hg ↦ by simpa using hdiff.add hg⟩

/-- Shifting the index of a sequence by `m` preserves Cesàro limits. -/
theorem tendsto_cesaro_comp_add_iff {f : ℕ → E} {L : E} (m : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f (i + m)) atTop (𝓝 L) ↔
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i) atTop (𝓝 L) := by
  have hsum (n : ℕ) : ∑ i ∈ range (n + 1), f (i + m) + ∑ i ∈ range m, f i =
      ∑ i ∈ range (n + m + 1), f i := by
    conv_rhs => rw [(by omega : n + m + 1 = m + (n + 1)), sum_range_add, add_comm]
    exact congrArg (· + ∑ i ∈ range m, f i) (sum_congr rfl fun i _ ↦ by rw [Nat.add_comm])
  have hprefix : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range m, f i) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (∑ i ∈ range m, f i)
  constructor
  · intro hB
    have hratio : Tendsto (fun n : ℕ ↦ ((n - m + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) :=
      (tendsto_natCast_add_div_add_one (1 - (m : ℝ))).congr' <| by
        filter_upwards [eventually_ge_atTop m] with n hn
        rw [Nat.cast_add, Nat.cast_sub hn]; push_cast; ring_nf
    refine Tendsto.congr' ?_
      (by simpa using (hratio.smul (hB.comp (tendsto_sub_atTop_nat m))).add hprefix)
    filter_upwards [eventually_ge_atTop m] with n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [Nat.add_sub_cancel, smul_smul, div_eq_mul_inv, mul_right_comm,
      mul_inv_cancel₀ (by positivity), one_mul, ← smul_add, hsum k]; push_cast; rfl
  · intro hA
    have hratio : Tendsto (fun n : ℕ ↦ ((n + m + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 1) :=
      (tendsto_natCast_add_div_add_one ((m : ℝ) + 1)).congr fun n ↦ by push_cast; ring_nf
    refine Tendsto.congr (fun n ↦ ?_)
      (by simpa using (hratio.smul (hA.comp (tendsto_add_atTop_nat m))).sub hprefix)
    rw [smul_smul, div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ (by positivity), one_mul,
      ← hsum n, smul_add, add_sub_cancel_right]; push_cast; rfl

/-- If a sequence has Cesàro limits along every residue class modulo `q > 0`, its Cesàro averages
converge to the average of those limits. -/
theorem tendsto_cesaro_of_forall_mod {f : ℕ → E} {q : ℕ} (hq : 0 < q) {L : ℕ → E}
    (hL : ∀ r < q, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ i ∈ range (n + 1), f (q * i + r)) atTop (𝓝 (L r))) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i) atTop
      (𝓝 ((q : ℝ)⁻¹ • ∑ r ∈ range q, L r)) := by
  have hsum : Tendsto (fun n : ℕ ↦ ∑ r ∈ range q,
      ((((n + q - r) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) •
        (((((n + q - r) / q - 1) + 1 : ℕ) : ℝ)⁻¹ •
          ∑ m ∈ range (((n + q - r) / q - 1) + 1), f (q * m + r))) atTop
      (𝓝 (∑ r ∈ range q, (q : ℝ)⁻¹ • L r)) :=
    tendsto_finsetSum (range q) fun r hr ↦ by
      have hrq : r < q := mem_range.mp hr
      exact (tendsto_add_sub_div_div_succ hq hrq).smul ((hL r hrq).comp
        (tendsto_atTop_atTop.mpr fun b ↦ ⟨q * (b + 1), fun n hn ↦ by
          have : b + 1 ≤ (n + q - r) / q := by rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm]; omega
          omega⟩))
  rw [← smul_sum] at hsum; refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop q] with n hn
  rw [← Finset.sum_range_add_one_eq_sum_mod f hq n, smul_sum]
  refine sum_congr rfl fun r hr ↦ ?_; have hrq : r < q := mem_range.mp hr
  have hk : 1 ≤ (n + q - r) / q := by rw [Nat.le_div_iff_mul_le hq]; omega
  rw [Nat.sub_add_cancel hk, smul_smul]; congr 1
  field_simp [(by exact_mod_cast (by omega : (n + q - r) / q ≠ 0) :
    (((n + q - r) / q : ℕ) : ℝ) ≠ 0)]

/-- If the masked Cesàro average on `i % q = r` (`r < q`) converges to `L`, then the progression
`i ↦ q * i + r` has Cesàro limit `q • L`. -/
theorem tendsto_cesaro_mul_add_of_ite_mod {f : ℕ → E} {q r : ℕ} (hq : 0 < q) (hr : r < q) {L : E}
    (h : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ i ∈ range (n + 1), if i % q = r then f i else 0) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f (q * i + r))
      atTop (𝓝 ((q : ℝ) • L)) := by
  have hsub : Tendsto (fun m : ℕ ↦ q * (m + 1) - 1) atTop atTop := tendsto_atTop_atTop.mpr
    fun b ↦ ⟨b, fun m hm ↦ by have : m + 1 ≤ q * (m + 1) := Nat.le_mul_of_pos_left _ hq; omega⟩
  refine ((h.comp hsub).const_smul (q : ℝ)).congr fun m ↦ ?_
  have hsum : ∑ i ∈ range (q * (m + 1)), (if i % q = r then f i else 0) =
      ∑ j ∈ range (m + 1), f (q * j + r) := by
    rw [sum_range_mul_eq_sum_sum, sum_comm, sum_congr rfl fun s hs ↦ (by
        by_cases hsr : s = r <;>
          simp [hsr, Nat.mod_eq_of_lt (mem_range.mp hs), Nat.mod_eq_of_lt hr] :
        ∑ j ∈ range (m + 1), (if (q * j + s) % q = r then f (q * j + s) else 0) =
          if s = r then ∑ j ∈ range (m + 1), f (q * j + r) else 0),
      sum_ite_eq' (range q) r]; simp [mem_range.mpr hr]
  simp only [Function.comp_apply, Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos m)), hsum,
    smul_smul, Nat.cast_mul, mul_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hq.ne'), one_mul]

end TauCeti
