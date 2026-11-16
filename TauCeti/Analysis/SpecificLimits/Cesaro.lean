/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.Positivity

/-!
# Cesàro averages under shifts, finite modifications, and residue decompositions

This file records elementary invariance and decomposition properties of the successor-indexed
Cesàro averages `n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Finset.range (n + 1), f i` in a real
seminormed vector space:

* `TauCeti.tendsto_cesaro_congr_of_eventuallyEq`: modifying finitely many terms does not change
  the Cesàro limit.
* `TauCeti.tendsto_cesaro_comp_add_iff`: for a bounded sequence, shifting the index by `m` does
  not change the Cesàro limit.
* `TauCeti.tendsto_cesaro_of_forall_mod`: if a bounded sequence has Cesàro limits along every
  residue class modulo `q > 0`, its overall Cesàro average converges to the mean of those limits.
* `TauCeti.tendsto_cesaro_mul_add_of_ite_mod`: convergence of the Cesàro average of a sequence
  masked to a single residue class `r mod q` implies convergence along the progression `q * i + r`.
-/

public section

open Filter Finset Topology

namespace TauCeti

/-- Reindex a sum over `range (q * k)` by quotient and remainder modulo `q`. -/
private theorem sum_range_mul_eq_sum_mod {M : Type*} [AddCommMonoid M] (f : ℕ → M) (q k : ℕ) :
    ∑ i ∈ range (q * k), f i = ∑ r ∈ range q, ∑ m ∈ range k, f (q * m + r) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp_rw [sum_range_succ, sum_add_distrib]

/-- For `q > 0`, the quotient ratio `((n + 1) / q) / (n + 1)` converges to `q⁻¹`. -/
private theorem tendsto_div_nat_div_succ {q : ℕ} (hq : 0 < q) :
    Tendsto (fun n : ℕ ↦ (((n + 1) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 (q : ℝ)⁻¹) := by
  have hrem : Tendsto (fun n : ℕ ↦
      (((n + 1) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) - (q : ℝ)⁻¹) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
    refine squeeze_zero_norm (fun n ↦ ?_) hbound
    have hdiv : ((n + 1 : ℕ) : ℝ) = (q : ℝ) * (((n + 1) / q : ℕ) : ℝ) +
        (((n + 1) % q : ℕ) : ℝ) := by exact_mod_cast (Nat.div_add_mod (n + 1) q).symm
    have heq : (((n + 1) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) - (q : ℝ)⁻¹ =
        -((((n + 1) % q : ℕ) : ℝ) / ((q : ℝ) * ((n + 1 : ℕ) : ℝ))) := by
      field_simp
      linarith
    rw [heq, norm_neg, Real.norm_of_nonneg (by positivity)]
    have hmod_lt : (((n + 1) % q : ℕ) : ℝ) ≤ q := by
      exact_mod_cast (Nat.mod_lt (n + 1) hq).le
    calc (((n + 1) % q : ℕ) : ℝ) / ((q : ℝ) * ((n + 1 : ℕ) : ℝ))
        ≤ (q : ℝ) / ((q : ℝ) * ((n + 1 : ℕ) : ℝ)) := by gcongr
      _ = ((n + 1 : ℕ) : ℝ)⁻¹ := by field_simp
  simpa using hrem.add (tendsto_const_nhds (x := (q : ℝ)⁻¹))

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Changing finitely many terms of a sequence does not change the convergence or value of its
Cesàro averages. -/
theorem tendsto_cesaro_congr_of_eventuallyEq {f g : ℕ → E} {L : E} (hfg : f =ᶠ[atTop] g) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i) atTop (𝓝 L) ↔
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), g i) atTop (𝓝 L) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfg
  have hdiff : Tendsto (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i -
        ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), g i) atTop (𝓝 0) := by
    have hconst : ∀ n ≥ N, ∑ i ∈ range (n + 1), (f i - g i) =
        ∑ i ∈ range N, (f i - g i) := by
      intro n hn
      rw [← sum_range_add_sum_Ico _ (by omega : N ≤ n + 1)]
      have hzero : ∑ i ∈ Ico N (n + 1), (f i - g i) = 0 :=
        sum_eq_zero fun i hi ↦ by rw [hN i (mem_Ico.mp hi).1, sub_self]
      rw [hzero, add_zero]
    have hlim : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range N, (f i - g i))
        atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).smul_const
        (∑ i ∈ range N, (f i - g i))
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [← smul_sub, ← sum_sub_distrib, hconst n hn]
  refine ⟨fun hf ↦ ?_, fun hg ↦ ?_⟩
  · simpa using hf.sub hdiff
  · simpa using hdiff.add hg

/-- For a bounded sequence, shifting the index by a fixed offset `m` does not change the
convergence or value of its Cesàro averages. -/
theorem tendsto_cesaro_comp_add_iff {f : ℕ → E} {L : E} (hbdd : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C) (m : ℕ) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f (i + m)) atTop (𝓝 L) ↔
      Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i) atTop (𝓝 L) := by
  obtain ⟨C, hC⟩ := hbdd
  have hdiff : Tendsto (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f (i + m) -
        ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * (2 * (m : ℝ) * C)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).mul_const
        (2 * (m : ℝ) * C)
    refine squeeze_zero_norm (fun n ↦ ?_) hbound
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
    have hshift : ∑ i ∈ range (n + 1), f (i + m) - ∑ i ∈ range (n + 1), f i =
        ∑ i ∈ range m, f (n + 1 + i) - ∑ i ∈ range m, f i := by
      have h1 : ∑ i ∈ range (m + (n + 1)), f i =
          ∑ i ∈ range m, f i + ∑ i ∈ range (n + 1), f (m + i) := sum_range_add f m (n + 1)
      have h2 : ∑ i ∈ range (n + 1 + m), f i =
          ∑ i ∈ range (n + 1), f i + ∑ i ∈ range m, f (n + 1 + i) := sum_range_add f (n + 1) m
      rw [Nat.add_comm m (n + 1)] at h1
      simp_rw [Nat.add_comm m _] at h1
      exact sub_eq_sub_iff_add_eq_add.mpr (by rw [add_comm, ← h1, h2, add_comm])
    rw [hshift]
    calc ‖∑ i ∈ range m, f (n + 1 + i) - ∑ i ∈ range m, f i‖
        ≤ ‖∑ i ∈ range m, f (n + 1 + i)‖ + ‖∑ i ∈ range m, f i‖ := norm_sub_le _ _
      _ ≤ ∑ i ∈ range m, ‖f (n + 1 + i)‖ + ∑ i ∈ range m, ‖f i‖ :=
          add_le_add (norm_sum_le _ _) (norm_sum_le _ _)
      _ ≤ ∑ _i ∈ range m, C + ∑ _i ∈ range m, C :=
          add_le_add (sum_le_sum fun _ _ ↦ hC _) (sum_le_sum fun _ _ ↦ hC _)
      _ = 2 * (m : ℝ) * C := by simp; ring
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · simpa using hf.sub hdiff
  · simpa using hdiff.add hf

/-- The trailing remainder of length `(n + 1) % q` in a bounded Cesàro average tends to `0`. -/
private theorem tendsto_cesaro_tail_mod {f : ℕ → E} {q : ℕ} (hq : 0 < q)
    {C : ℝ} (hC : ∀ n, ‖f n‖ ≤ C) :
    Tendsto (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ Ico (q * ((n + 1) / q)) (n + 1), f i) atTop (𝓝 0) := by
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hbound : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * ((q : ℝ) * C)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))).mul_const
      ((q : ℝ) * C)
  refine squeeze_zero_norm (fun n ↦ ?_) hbound
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  gcongr
  calc ‖∑ i ∈ Ico (q * ((n + 1) / q)) (n + 1), f i‖
      ≤ ∑ i ∈ Ico (q * ((n + 1) / q)) (n + 1), ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Ico (q * ((n + 1) / q)) (n + 1), C := sum_le_sum fun _ _ ↦ hC _
    _ = ((n + 1 - q * ((n + 1) / q) : ℕ) : ℝ) * C := by simp
    _ ≤ (q : ℝ) * C := by
        gcongr
        have hrem_eq : n + 1 - q * ((n + 1) / q) = (n + 1) % q := by
          have := Nat.div_add_mod (n + 1) q
          omega
        rw [hrem_eq]
        exact_mod_cast (Nat.mod_lt (n + 1) hq).le

/-- If a bounded sequence has Cesàro limits along every residue class modulo `q > 0`, then its
Cesàro averages converge to the average of those limits. -/
theorem tendsto_cesaro_of_forall_mod {f : ℕ → E} {q : ℕ} (hq : 0 < q)
    (hbdd : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C) {L : ℕ → E}
    (hL : ∀ r < q, Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ i ∈ range (n + 1), f (q * i + r)) atTop (𝓝 (L r))) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f i) atTop
      (𝓝 ((q : ℝ)⁻¹ • ∑ r ∈ range q, L r)) := by
  obtain ⟨C, hC⟩ := hbdd
  have hk_top : Tendsto (fun n : ℕ ↦ (n + 1) / q - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨q * (b + 1), fun n hn ↦ ?_⟩
    have : b + 1 ≤ (n + 1) / q := by
      rw [Nat.le_div_iff_mul_le hq, Nat.mul_comm]
      omega
    omega
  have hmain : Tendsto (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (q * ((n + 1) / q)), f i) atTop
      (𝓝 ((q : ℝ)⁻¹ • ∑ r ∈ range q, L r)) := by
    have hsum : Tendsto (fun n : ℕ ↦ ∑ r ∈ range q,
        ((((n + 1) / q : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) •
          (((((n + 1) / q - 1) + 1 : ℕ) : ℝ)⁻¹ •
            ∑ m ∈ range (((n + 1) / q - 1) + 1), f (q * m + r))) atTop
        (𝓝 (∑ r ∈ range q, (q : ℝ)⁻¹ • L r)) :=
      tendsto_finsetSum (range q) fun r hr ↦
        (tendsto_div_nat_div_succ hq).smul ((hL r (mem_range.mp hr)).comp hk_top)
    rw [← smul_sum] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop q] with n hn
    have hk : 1 ≤ (n + 1) / q := by
      rw [Nat.le_div_iff_mul_le hq]
      omega
    have hk1 : (n + 1) / q - 1 + 1 = (n + 1) / q := Nat.sub_add_cancel hk
    have hk0 : (((n + 1) / q : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
    rw [sum_range_mul_eq_sum_mod, smul_sum]
    refine sum_congr rfl fun r _ ↦ ?_
    rw [hk1, smul_smul]
    congr 1
    field_simp
  have htot := hmain.add (tendsto_cesaro_tail_mod hq hC)
  rw [add_zero] at htot
  refine htot.congr fun n ↦ ?_
  rw [← smul_add, sum_range_add_sum_Ico _ (Nat.mul_div_le (n + 1) q)]

/-- If the Cesàro average of a sequence masked to a single residue class `r mod q` (`0 ≤ r < q`)
converges to `L`, then the Cesàro average along the progression `i ↦ q * i + r` converges to
`q • L`. -/
theorem tendsto_cesaro_mul_add_of_ite_mod {f : ℕ → E} {q r : ℕ} (hq : 0 < q) (hr : r < q) {L : E}
    (h : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ i ∈ range (n + 1), if i % q = r then f i else 0) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹ • ∑ i ∈ range (n + 1), f (q * i + r))
      atTop (𝓝 ((q : ℝ) • L)) := by
  have hsub : Tendsto (fun m : ℕ ↦ q * (m + 1) - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨b, fun m hm ↦ ?_⟩
    have : m + 1 ≤ q * (m + 1) := Nat.le_mul_of_pos_left _ hq
    omega
  have hcomp := (h.comp hsub).const_smul (q : ℝ)
  refine hcomp.congr fun m ↦ ?_
  have hidx : q * (m + 1) - 1 + 1 = q * (m + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hq (Nat.succ_pos m))
  have hsum : ∑ i ∈ range (q * (m + 1)), (if i % q = r then f i else 0) =
      ∑ j ∈ range (m + 1), f (q * j + r) := by
    rw [sum_range_mul_eq_sum_mod]
    have hinner : ∀ s ∈ range q,
        ∑ j ∈ range (m + 1), (if (q * j + s) % q = r then f (q * j + s) else 0) =
          if s = r then ∑ j ∈ range (m + 1), f (q * j + r) else 0 := by
      intro s hs
      have hs' : s < q := mem_range.mp hs
      have hmod (j : ℕ) : (q * j + s) % q = s := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hs']
      simp_rw [hmod]
      split_ifs with hsr
      · subst hsr; rfl
      · simp
    rw [sum_congr rfl hinner, sum_ite_eq' (range q) r]
    simp [mem_range.mpr hr]
  simp only [Function.comp_apply, hidx, hsum, smul_smul, Nat.cast_mul, mul_inv]
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]

end TauCeti
