/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.ContinuousOn
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Summable real and complex powers

A nonnegative family `f` with a summable positive power `f ^ p` tends to `0` along the cofinite
filter, since its terms are the `p`-th roots of a summable family.

For `1 < s.re` and any complex shift `c : ℂ`, the shifted principal-power series
`∑' n : ℕ, ((n : ℂ) + c) ^ (-s)` converges absolutely. At a nonpositive integer shift `c = -n`
(`n : ℕ`), the base `(n : ℂ) + c` vanishes and the principal-power summand `0 ^ (-s)` is `0` for
`1 < s.re` by Lean's totalized `Complex.cpow`; genuine non-totalized shifts require `c ∉ -ℕ`.

## Main results

* `TauCeti.tendsto_cofinite_zero_of_summable_rpow` — a nonnegative family with a summable positive
  power tends to `0`.
* `TauCeti.eventually_re_natCast_add_pos` — `(n : ℂ) + c` has positive real part for all
  sufficiently large `n`.
* `TauCeti.summable_norm_natCast_add_cpow_neg` and `TauCeti.summable_natCast_add_cpow_neg` —
  absolute convergence of `∑' n : ℕ, ((n : ℂ) + c) ^ (-s)` for `1 < s.re` and any `c : ℂ`.
* `TauCeti.exists_norm_natCast_add_cpow_neg_le` — compact-uniform summable majorant
  `C * (n + 1) ^ (-σ)` (`1 < σ`) on compact subsets of
  `{p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}`.
-/

public section

open Complex

namespace TauCeti

/-- A nonnegative family `f` with `f ^ p` summable for some `0 < p` tends to `0` along the
cofinite filter. -/
theorem tendsto_cofinite_zero_of_summable_rpow {ι : Type*} {f : ι → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : ∀ i, 0 ≤ f i) (h : Summable fun i ↦ f i ^ p) :
    Filter.Tendsto f Filter.cofinite (nhds 0) := by
  have h' := h.tendsto_cofinite_zero.rpow_const (p := p⁻¹) (Or.inr (inv_nonneg.2 hp.le))
  rw [Real.zero_rpow (inv_ne_zero hp.ne')] at h'
  exact h'.congr fun i ↦ Real.rpow_rpow_inv (hf i) hp.ne'

/-- For any `c : ℂ`, `(n : ℂ) + c` has positive real part for all sufficiently large `n : ℕ`. -/
theorem eventually_re_natCast_add_pos (c : ℂ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < ((n : ℂ) + c).re := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-c.re)
  refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
  simp only [add_re, natCast_re]
  linarith [show (N : ℝ) ≤ n from Nat.cast_le.mpr hn]

/-- For `1 < s.re` and any `c : ℂ`, the principal-power series `∑' n : ℕ, ‖(n + c) ^ (-s)‖` is
summable (for `c = -n` with `n : ℕ`, the `n`-th summand uses the totalized principal power
`0 ^ (-s) = 0`). -/
theorem summable_norm_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖((n : ℂ) + c) ^ (-s)‖) := by
  obtain ⟨N, hN_pos⟩ := Filter.eventually_atTop.mp (eventually_re_natCast_add_pos c)
  have hN : (N : ℂ) + c ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (hN_pos N le_rfl))
  obtain ⟨U, hU, -, C, -, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hN (-s)
  have hp : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-s.re)) :=
    ((summable_nat_add_iff 1).mpr
      ((Real.summable_nat_rpow (p := -s.re)).mpr (by linarith))).congr
      fun n => by push_cast; rw [add_comm]
  refine (summable_nat_add_iff N).mp ?_
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hp.mul_left C)
  have h := hbound ((N : ℂ) + c) (mem_of_mem_nhds hU) (n : ℝ) (Nat.cast_nonneg n)
  simpa only [ofReal_natCast, neg_re, Nat.cast_add, add_assoc] using h

/-- For `1 < s.re` and any `c : ℂ`, `n ↦ (n + c) ^ (-s)` is summable (with totalized `0 ^ (-s) = 0`
at index `n` when `c = -n`). -/
theorem summable_natCast_add_cpow_neg {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) :=
  (summable_norm_natCast_add_cpow_neg hs c).of_norm

private theorem exists_norm_natCast_add_cpow_neg_le_prefix {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hK_ne : ∀ p ∈ K, ∀ n : ℕ, p.2 ≠ -(n : ℂ)) (σ B_im : ℝ) (N : ℕ) :
    ∃ C₀ ≥ 0, ∀ n < N, ∀ p ∈ K,
      ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im) ≤ C₀ * ((n : ℝ) + 1) ^ (-σ) := by
  let g : ℕ × (ℂ × ℂ) → ℝ := fun np =>
    ‖(np.1 : ℂ) + np.2.2‖ ^ (-np.2.1.re) * ((np.1 : ℝ) + 1) ^ σ * Real.exp (Real.pi * B_im)
  have hS : IsCompact ((↑(Finset.range N) : Set ℕ) ×ˢ K) :=
    (Finset.finite_toSet (Finset.range N)).isCompact.prod hK
  have hg_cont : ContinuousOn g ((↑(Finset.range N) : Set ℕ) ×ˢ K) := by
    refine continuousOn_prod_of_discrete_left.mpr fun n => ?_
    refine ContinuousOn.mono ?_ (fun p hp => hp.2)
    intro p hp
    have hne : (n : ℂ) + p.2 ≠ 0 := fun h => hK_ne p hp n (eq_neg_of_add_eq_zero_right h)
    have hnorm_pos : ‖(n : ℂ) + p.2‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    exact ((((continuous_const.add continuous_snd).norm.continuousAt.rpow
      (continuous_re.comp continuous_fst).neg.continuousAt (Or.inl hnorm_pos)).mul
      continuousAt_const).mul continuousAt_const).continuousWithinAt
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hg_cont
  refine ⟨max M 0, le_max_right _ _, fun n hn p hp => ?_⟩
  have hg_nonneg : 0 ≤ g (n, p) := by
    dsimp [g]
    positivity
  have hle : g (n, p) ≤ max M 0 := by
    have h := hM (n, p) ⟨Finset.mem_range.mpr hn, hp⟩
    rw [Real.norm_of_nonneg hg_nonneg] at h
    exact h.trans (le_max_left _ _)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hpow_mul : ((n : ℝ) + 1) ^ σ * ((n : ℝ) + 1) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero]
  calc
    ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im)
        = g (n, p) * ((n : ℝ) + 1) ^ (-σ) := by
          dsimp [g]
          rw [mul_assoc, mul_comm (Real.exp (Real.pi * B_im)), ← mul_assoc,
            mul_assoc _ _ ((_ : ℝ) ^ (-σ)), hpow_mul, mul_one]
    _ ≤ max M 0 * ((n : ℝ) + 1) ^ (-σ) :=
        mul_le_mul_of_nonneg_right hle (Real.rpow_nonneg hpos.le _)

private theorem norm_natCast_add_cpow_neg_le_tail {K : Set (ℂ × ℂ)} {σ R_c B_im : ℝ}
    (hσ_gt : 1 < σ) (hσ_le : ∀ p ∈ K, σ ≤ p.1.re) (hR_c : ∀ p ∈ K, ‖p.2‖ ≤ R_c)
    {N n : ℕ} (hN_gt : 2 * R_c + 1 < (N : ℝ)) (hN_ge2 : (2 : ℝ) ≤ (N : ℝ))
    (hn : N ≤ n) {p : ℂ × ℂ} (hp : p ∈ K) :
    ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im) ≤
      ((2 : ℝ) ^ σ * Real.exp (Real.pi * B_im)) * ((n : ℝ) + 1) ^ (-σ) := by
  have hn_cast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
  have hlow : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + p.2‖ := by
    have htri : (n : ℝ) - ‖p.2‖ ≤ ‖(n : ℂ) + p.2‖ := by
      have h := norm_add_le ((n : ℂ) + p.2) (-p.2)
      rw [add_neg_cancel_right, norm_neg, Complex.norm_natCast] at h
      linarith
    linarith [hR_c p hp]
  have hbase_ge1 : 1 ≤ ((n : ℝ) + 1) / 2 := by linarith [hN_ge2.trans hn_cast]
  have hbase_pos : 0 < ((n : ℝ) + 1) / 2 := by positivity
  have hrpow1 : ‖(n : ℂ) + p.2‖ ^ (-p.1.re) ≤ (((n : ℝ) + 1) / 2) ^ (-p.1.re) :=
    Real.rpow_le_rpow_of_nonpos hbase_pos hlow (by linarith [hσ_le p hp, hσ_gt])
  have hrpow2 : (((n : ℝ) + 1) / 2) ^ (-p.1.re) ≤ (((n : ℝ) + 1) / 2) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hbase_ge1 (neg_le_neg (hσ_le p hp))
  have hrpow_eq : (((n : ℝ) + 1) / 2) ^ (-σ) = (2 : ℝ) ^ σ * ((n : ℝ) + 1) ^ (-σ) := by
    rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
      Real.rpow_neg (by positivity), div_eq_mul_inv, inv_inv, mul_comm]
  calc
    ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im)
        ≤ (((n : ℝ) + 1) / 2) ^ (-σ) * Real.exp (Real.pi * B_im) :=
          mul_le_mul_of_nonneg_right (hrpow1.trans hrpow2) (Real.exp_pos _).le
    _ = ((2 : ℝ) ^ σ * Real.exp (Real.pi * B_im)) * ((n : ℝ) + 1) ^ (-σ) := by
          rw [hrpow_eq]; ring

/-- On any compact subset `K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}`, the
principal powers `((n : ℂ) + p.2) ^ (-p.1)` admit a uniform summable bound
`C * ((n : ℝ) + 1) ^ (-σ)` with `1 < σ` and `0 ≤ C`. -/
theorem exists_norm_natCast_add_cpow_neg_le {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hK_sub : K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}) :
    ∃ σ : ℝ, 1 < σ ∧ ∃ C ≥ 0, ∀ p ∈ K, ∀ n : ℕ,
      ‖((n : ℂ) + p.2) ^ (-p.1)‖ ≤ C * ((n : ℝ) + 1) ^ (-σ) := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨2, by norm_num, 0, le_rfl, fun _ hp => False.elim hp⟩
  obtain ⟨p₀, hp₀, hp₀_min⟩ :=
    hK.exists_isMinOn hKne (continuous_re.comp continuous_fst).continuousOn
  set σ : ℝ := p₀.1.re
  have hσ_gt : 1 < σ := (hK_sub hp₀).1
  have hσ_le : ∀ p ∈ K, σ ≤ p.1.re := fun p hp => hp₀_min hp
  obtain ⟨B_im, hB_im⟩ := hK.exists_bound_of_continuousOn
    (continuous_abs.comp (continuous_im.comp continuous_fst)).continuousOn
  obtain ⟨R_c, hR_c⟩ := hK.exists_bound_of_continuousOn
    (continuous_norm.comp continuous_snd).continuousOn
  set B_im' : ℝ := max B_im 0
  set R_c' : ℝ := max R_c 0
  have hB_im' : ∀ p ∈ K, |p.1.im| ≤ B_im' := fun p hp =>
    (by simpa [Real.norm_eq_abs] using hB_im p hp : |p.1.im| ≤ B_im).trans (le_max_left _ _)
  have hR_c' : ∀ p ∈ K, ‖p.2‖ ≤ R_c' := fun p hp =>
    (by simpa using hR_c p hp : ‖p.2‖ ≤ R_c).trans (le_max_left _ _)
  set N : ℕ := ⌊2 * R_c'⌋₊ + 2
  have hN_gt : 2 * R_c' + 1 < (N : ℝ) := by
    have hlt := Nat.lt_floor_add_one (2 * R_c')
    dsimp [N]; push_cast; linarith
  have hN_ge2 : (2 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.le_add_left 2 ⌊2 * R_c'⌋₊
  obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := exists_norm_natCast_add_cpow_neg_le_prefix hK
    (fun p hp => (hK_sub hp).2) σ B_im' N
  set C_tail : ℝ := (2 : ℝ) ^ σ * Real.exp (Real.pi * B_im')
  refine ⟨σ, hσ_gt, max C₀ C_tail, le_trans hC₀_nonneg (le_max_left _ _), fun p hp n => ?_⟩
  have hterm_le : ‖((n : ℂ) + p.2) ^ (-p.1)‖ ≤
      ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im') := by
    refine (Complex.norm_cpow_le_mul_exp ((n : ℂ) + p.2) (-p.1)).trans ?_
    simp only [neg_re, neg_im, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB_im' p hp) Real.pi_pos.le))
      (Real.rpow_nonneg (norm_nonneg _) _)
  refine hterm_le.trans ?_
  by_cases hn : n < N
  · exact (hC₀ n hn p hp).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  · exact (norm_natCast_add_cpow_neg_le_tail hσ_gt hσ_le hR_c' hN_gt hN_ge2
      (le_of_not_gt hn) hp).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))

end TauCeti
