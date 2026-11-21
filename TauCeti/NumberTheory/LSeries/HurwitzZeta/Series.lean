/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# The complex-parameter Hurwitz zeta series

For a complex shift parameter `c : ℂ` and exponent `s : ℂ` with `1 < s.re`, the complex Hurwitz
series
`complexHurwitzSeries s c = ∑' n : ℕ, exp (-s * log (n + c))`
converges absolutely for every `c : ℂ`. The pointwise agreement domain consists of non-singular
shifts `c ∉ -ℕ` (as distinct from `slitPlane` or `0 < c.re`, since negative noninteger shifts lie on
or across the branch cut `(-∞, 0]` of the principal logarithm), where every base `n + c` is nonzero
and each summand coincides with the principal complex power `(n + c) ^ (-s)`. Note that
holomorphy and meromorphic continuation in `Continuation.lean` are developed on `{0 < c.re}`, where
no base `n + c` meets the branch cut `(-∞, 0]`. At a nonpositive integer shift `c = -n` (`n : ℕ`),
the defining summand at index `n` is `exp (-s * log 0) = exp 0 = 1` (by Lean's
`Complex.log 0 = 0`), whereas the corresponding principal-power summand `0 ^ (-s)` is `0` for
`1 < s.re`; thus convergence at `c ∈ -ℕ` is purely formal under totalization.

For `1 < s.re`, shifting `c ≠ 0` by `1` subtracts the initial `n = 0` term `c ^ (-s)`. Along the
real interval `(0, 1]`, `complexHurwitzSeries s x` agrees with Mathlib's circle-parametrized
Hurwitz zeta function `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`; at `c = 1` it reduces to
`riemannZeta s`, and at `c = 1 / 2` the odd-integer sum yields
`((2 : ℂ) ^ s - 1) * riemannZeta s`.

## Main definitions and results

* `TauCeti.complexHurwitzSeries`: the Dirichlet-type series `∑' n : ℕ, exp (-s * log (n + c))`.
* `TauCeti.exists_norm_complexHurwitzSeries_term_le`: compact-uniform summable majorant
  `C * (n + 1) ^ (-σ)` (`1 < σ`) on compact subsets of the pointwise agreement domain
  `{p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}`.
* `TauCeti.summable_norm_complexHurwitzSeries_term`, `TauCeti.summable_complexHurwitzSeries_term`,
  `TauCeti.hasSum_complexHurwitzSeries_term`, `TauCeti.hasSum_complexHurwitzSeries`, and
  `TauCeti.hasSum_complexHurwitzSeries_of_re_pos`: formal absolute convergence and `HasSum` on
  `1 < s.re` for arbitrary `c : ℂ`, and principal-power convergence on the pointwise agreement
  domain `c ∉ -ℕ` (in particular `0 < c.re`).
* `TauCeti.complexHurwitzSeries_add_one_right`: shift identity
  `complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s)` for `1 < s.re` and
  `c ≠ 0`.
* `TauCeti.complexHurwitzSeries_ofReal_eq_hurwitzZeta`: agreement with `HurwitzZeta.hurwitzZeta`
  for real `x ∈ (0, 1]` and `1 < s.re`.
* `TauCeti.complexHurwitzSeries_one_right` and `TauCeti.complexHurwitzSeries_one_half_right`:
  specializations at `c = 1` and `c = 1 / 2`.

## References

* J. C. Lagarias and W. C. W. Li, *The Lerch zeta function II. Analytic continuation*, Forum Math.
  **24** (2012), 49–84.
* F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, §25.11.
-/

public section

open Complex Set Filter
open scoped Topology

namespace TauCeti

/-- The complex-parameter Hurwitz zeta series `∑' n : ℕ, exp (-s * log (n + c))`, using the
principal complex logarithm. The pointwise agreement domain is `1 < s.re` and `c ∉ -ℕ`, where
every base `n + c` is nonzero and each summand equals `(n + c) ^ (-s)` (including negative
noninteger shifts on the branch cut `(-∞, 0]`, whereas the analytic continuation in
`Continuation.lean` stays on `0 < c.re` inside `slitPlane`). On `1 < s.re`, the series also
converges formally for `c = -n` (`n : ℕ`) under totalization: at index `n` the defining summand is
`exp (-s * log 0) = 1` (whereas the totalized principal power `0 ^ (-s)` is `0`), so values at
`c ∈ -ℕ` are totalized artifacts outside the pointwise agreement domain. -/
noncomputable def complexHurwitzSeries (s c : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c))

/-- Defining equation for `complexHurwitzSeries`. -/
theorem complexHurwitzSeries_def (s c : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, Complex.exp (-s * Complex.log (n + c)) := (rfl)

/-- Away from the nonpositive integers `c = -n`, every shifted base `n + c` is nonzero, so
`complexHurwitzSeries s c` coincides termwise with `∑' n : ℕ, (n + c) ^ (-s)`. -/
theorem complexHurwitzSeries_eq_tsum_cpow {c : ℂ} (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) (s : ℂ) :
    complexHurwitzSeries s c = ∑' n : ℕ, ((n : ℂ) + c) ^ (-s) := by
  refine tsum_congr fun n => ?_
  have hne : (n : ℂ) + c ≠ 0 := fun h => hc n (eq_neg_of_add_eq_zero_right h)
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- On any compact subset `K` of the pointwise agreement domain
`{p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}`, the defining terms
`Complex.exp (-p.1 * Complex.log (n + p.2))` admit a uniform summable bound
`C * ((n : ℝ) + 1) ^ (-σ)` with `1 < σ` and `0 ≤ C`. -/
theorem exists_norm_complexHurwitzSeries_term_le {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (hK_sub : K ⊆ {p : ℂ × ℂ | 1 < p.1.re ∧ ∀ n : ℕ, p.2 ≠ -(n : ℂ)}) :
    ∃ σ : ℝ, 1 < σ ∧ ∃ C ≥ 0, ∀ p ∈ K, ∀ n : ℕ,
      ‖Complex.exp (-p.1 * Complex.log (n + p.2))‖ ≤ C * ((n : ℝ) + 1) ^ (-σ) := by
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
  have hterm_le : ∀ (n : ℕ) {p : ℂ × ℂ}, p ∈ K →
      ‖Complex.exp (-p.1 * Complex.log ((n : ℂ) + p.2))‖ ≤
        ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im') := fun n p hp => by
    have hne : (n : ℂ) + p.2 ≠ 0 := fun h => (hK_sub hp).2 n (eq_neg_of_add_eq_zero_right h)
    rw [mul_comm (-p.1), ← cpow_def_of_ne_zero hne]
    refine (Complex.norm_cpow_le_mul_exp ((n : ℂ) + p.2) (-p.1)).trans ?_
    simp only [neg_re, neg_im, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hB_im' p hp) Real.pi_pos.le))
      (Real.rpow_nonneg (norm_nonneg _) _)
  set N : ℕ := ⌊2 * R_c'⌋₊ + 2
  have hhead_gen : ∀ m : ℕ, ∃ C₀ ≥ 0, ∀ n < m, ∀ p ∈ K,
      ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im') ≤
        C₀ * ((n : ℝ) + 1) ^ (-σ) := by
    intro m
    induction m with
    | zero => exact ⟨0, le_rfl, fun _ hn => absurd hn (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := ih
      have hcont : ContinuousOn
          (fun p : ℂ × ℂ => ‖(k : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im')) K := by
        intro p hp
        have hne : (k : ℂ) + p.2 ≠ 0 := fun h => (hK_sub hp).2 k (eq_neg_of_add_eq_zero_right h)
        have hnorm_pos : ‖(k : ℂ) + p.2‖ ≠ 0 := norm_ne_zero_iff.mpr hne
        exact (((((continuous_const.add continuous_snd).norm).continuousAt).rpow
          ((continuous_re.comp continuous_fst).neg.continuousAt) (Or.inl hnorm_pos)).mul
          continuousAt_const).continuousWithinAt
      obtain ⟨M_k, hM_k⟩ := hK.exists_bound_of_continuousOn hcont
      have hk_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ (-σ) := Real.rpow_pos_of_pos (by positivity) _
      refine ⟨max C₀ (max M_k 0 / ((k : ℝ) + 1) ^ (-σ)),
        le_trans hC₀_nonneg (le_max_left _ _), fun n hn p hp => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn_lt | rfl
      · exact (hC₀ n hn_lt p hp).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
      · have hval_nonneg : 0 ≤ ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im') :=
          mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
        have hMk : ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im') ≤ max M_k 0 := by
          have := hM_k p hp
          rw [Real.norm_of_nonneg hval_nonneg] at this
          exact this.trans (le_max_left _ _)
        calc ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im')
            ≤ (max M_k 0 / ((n : ℝ) + 1) ^ (-σ)) * ((n : ℝ) + 1) ^ (-σ) := by
              rw [div_mul_cancel₀ _ hk_pos.ne']; exact hMk
          _ ≤ max C₀ (max M_k 0 / ((n : ℝ) + 1) ^ (-σ)) * ((n : ℝ) + 1) ^ (-σ) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hk_pos.le
  obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := hhead_gen N
  set C_tail : ℝ := (2 : ℝ) ^ σ * Real.exp (Real.pi * B_im')
  refine ⟨σ, hσ_gt, max C₀ C_tail, le_trans hC₀_nonneg (le_max_left _ _), fun p hp n => ?_⟩
  refine (hterm_le n hp).trans ?_
  by_cases hn : n < N
  · exact (hC₀ n hn p hp).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _))
  · have hn_ge : N ≤ n := le_of_not_gt hn
    have hN_gt : 2 * R_c' + 1 < (N : ℝ) := by
      have hlt := Nat.lt_floor_add_one (2 * R_c')
      dsimp [N]
      push_cast
      linarith
    have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by
      have h2N : (2 : ℝ) ≤ (N : ℝ) := by dsimp [N]; push_cast; linarith
      exact h2N.trans (Nat.cast_le.mpr hn_ge)
    have hlow : ((n : ℝ) + 1) / 2 ≤ ‖(n : ℂ) + p.2‖ := by
      have htri : (n : ℝ) - ‖p.2‖ ≤ ‖(n : ℂ) + p.2‖ := by
        have h := norm_add_le ((n : ℂ) + p.2) (-p.2)
        rw [add_neg_cancel_right, norm_neg, Complex.norm_natCast] at h
        linarith
      have hn_cast : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn_ge
      linarith [hR_c' p hp]
    have hbase_ge1 : 1 ≤ ((n : ℝ) + 1) / 2 := by linarith
    have hbase_pos : 0 < ((n : ℝ) + 1) / 2 := by linarith
    have hrpow1 : ‖(n : ℂ) + p.2‖ ^ (-p.1.re) ≤ (((n : ℝ) + 1) / 2) ^ (-p.1.re) :=
      Real.rpow_le_rpow_of_nonpos hbase_pos hlow (by linarith [hσ_le p hp])
    have hrpow2 : (((n : ℝ) + 1) / 2) ^ (-p.1.re) ≤ (((n : ℝ) + 1) / 2) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le hbase_ge1 (neg_le_neg (hσ_le p hp))
    have hrpow_eq : (((n : ℝ) + 1) / 2) ^ (-σ) = (2 : ℝ) ^ σ * ((n : ℝ) + 1) ^ (-σ) := by
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity),
        Real.rpow_neg (by positivity), div_eq_mul_inv, inv_inv, mul_comm]
    have htail : ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im') ≤
        C_tail * ((n : ℝ) + 1) ^ (-σ) := by
      calc ‖(n : ℂ) + p.2‖ ^ (-p.1.re) * Real.exp (Real.pi * B_im')
          ≤ (((n : ℝ) + 1) / 2) ^ (-σ) * Real.exp (Real.pi * B_im') :=
            mul_le_mul_of_nonneg_right (hrpow1.trans hrpow2) (Real.exp_pos _).le
        _ = C_tail * ((n : ℝ) + 1) ^ (-σ) := by
            rw [hrpow_eq]; dsimp [C_tail]; ring
    exact htail.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))

/-- For `1 < s.re` and any `c : ℂ`, the defining terms `exp (-s * log (n + c))` are absolutely
summable. On the pointwise agreement domain `c ∉ -ℕ` this is absolute convergence of
`∑' n, (n + c) ^ (-s)`; at `c = -n` (`n : ℕ`), the `n`-th summand is totalized to `exp 0 = 1`
(unlike `0 ^ (-s) = 0`), so summability holds formally there as well. -/
theorem summable_norm_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => ‖Complex.exp (-s * Complex.log (n + c))‖) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-c.re)
  refine (summable_nat_add_iff N).mp
    (((summable_nat_add_iff N).mpr (summable_norm_natCast_add_cpow_neg hs c)).congr fun n => ?_)
  have hne : (((n + N : ℕ) : ℂ) + c) ≠ 0 := fun h0 => by
    have hre := congrArg Complex.re h0
    simp only [add_re, natCast_re, Nat.cast_add, zero_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [cpow_def_of_ne_zero hne, mul_comm]

/-- For `1 < s.re` and any `c : ℂ`, the defining terms of `complexHurwitzSeries s c` are
summable (formal totalized convergence at `c = -n` with `n`-th term `exp 0 = 1`; principal-power
convergence on the pointwise agreement domain `c ∉ -ℕ`). -/
theorem summable_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    Summable (fun n : ℕ => Complex.exp (-s * Complex.log (n + c))) :=
  (summable_norm_complexHurwitzSeries_term hs c).of_norm

/-- For `1 < s.re` and any `c : ℂ`, the defining exponential-log terms sum to
`complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries_term {s : ℂ} (hs : 1 < s.re) (c : ℂ) :
    HasSum (fun n : ℕ => Complex.exp (-s * Complex.log (n + c))) (complexHurwitzSeries s c) := by
  rw [complexHurwitzSeries_def]
  exact (summable_complexHurwitzSeries_term hs c).hasSum

/-- On `1 < s.re` and away from `c = -n` (`n : ℕ`), `n ↦ (n + c) ^ (-s)` has sum
`complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries {s c : ℂ} (hs : 1 < s.re) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    HasSum (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) (complexHurwitzSeries s c) := by
  rw [complexHurwitzSeries_eq_tsum_cpow hc]
  exact (summable_natCast_add_cpow_neg hs c).hasSum

/-- On `1 < s.re` and `0 < c.re`, `n ↦ (n + c) ^ (-s)` has sum `complexHurwitzSeries s c`. -/
theorem hasSum_complexHurwitzSeries_of_re_pos {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re) :
    HasSum (fun n : ℕ => ((n : ℂ) + c) ^ (-s)) (complexHurwitzSeries s c) :=
  hasSum_complexHurwitzSeries hs fun n h => by
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]

/-- On `1 < s.re`, shifting the complex Hurwitz parameter `c ≠ 0` by `1` removes the `n = 0` term
`c ^ (-s)`. -/
theorem complexHurwitzSeries_add_one_right {s c : ℂ} (hs : 1 < s.re) (hc : c ≠ 0) :
    complexHurwitzSeries s (c + 1) = complexHurwitzSeries s c - c ^ (-s) := by
  rw [complexHurwitzSeries_def s c, (summable_complexHurwitzSeries_term hs c).tsum_eq_zero_add]
  have hshift : (∑' n : ℕ, Complex.exp (-s * Complex.log (((n + 1 : ℕ) : ℂ) + c))) =
      complexHurwitzSeries s (c + 1) :=
    tsum_congr fun n => by congr 3; push_cast; ring
  rw [Nat.cast_zero, zero_add, mul_comm (-s), ← cpow_def_of_ne_zero hc, hshift,
    add_sub_cancel_left]

/-- For real `x ∈ (0, 1]` and `1 < s.re`, `complexHurwitzSeries s x` agrees with Mathlib's
circle-parametrized `HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s`. -/
theorem complexHurwitzSeries_ofReal_eq_hurwitzZeta {s : ℂ} {x : ℝ} (hs : 1 < s.re)
    (hx : x ∈ Ioc 0 1) :
    complexHurwitzSeries s x = HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  have h1 := hasSum_complexHurwitzSeries_of_re_pos (c := (x : ℂ)) hs (by simpa using hx.1)
  have h2 := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (Ioc_subset_Icc_self hx) hs
  exact h1.unique (h2.congr_fun fun _ => by rw [cpow_neg, one_div])

/-- At `c = 1`, the complex Hurwitz series on `1 < s.re` equals `riemannZeta s`. -/
theorem complexHurwitzSeries_one_right {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s 1 = riemannZeta s := by
  have h := complexHurwitzSeries_ofReal_eq_hurwitzZeta (x := 1) hs (right_mem_Ioc.mpr zero_lt_one)
  rwa [ofReal_one, AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero] at h

example : complexHurwitzSeries 2 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [complexHurwitzSeries_one_right (by norm_num), riemannZeta_two]

/-- At `c = 1 / 2` and `1 < s.re`, partitioning positive integers by parity yields
`complexHurwitzSeries s (1 / 2) = (2 ^ s - 1) * riemannZeta s`. -/
theorem complexHurwitzSeries_one_half_right {s : ℂ} (hs : 1 < s.re) :
    complexHurwitzSeries s (1 / 2) = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hzeta : HasSum (fun k : ℕ => ((k : ℂ) + 1) ^ (-s)) (riemannZeta s) := by
    rw [← complexHurwitzSeries_one_right hs]
    exact hasSum_complexHurwitzSeries_of_re_pos hs (by simp)
  have heven : HasSum (fun k : ℕ => (((2 * k : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2)) :=
    ((hasSum_complexHurwitzSeries_of_re_pos hs (by norm_num)).mul_left ((2 : ℂ) ^ (-s))).congr_fun
      fun k => by
        have hmul := ofReal_mul_cpow (r := 2) zero_le_two ((k : ℂ) + 1 / 2) (-s)
        simp only [ofReal_ofNat] at hmul
        rw [← hmul]; congr 1; push_cast; ring
  have hodd : HasSum (fun k : ℕ => (((2 * k + 1 : ℕ) : ℂ) + 1) ^ (-s))
      ((2 : ℂ) ^ (-s) * riemannZeta s) :=
    (hzeta.mul_left ((2 : ℂ) ^ (-s))).congr_fun fun k => by
      have hmul := ofReal_mul_cpow (r := 2) zero_le_two ((k : ℂ) + 1) (-s)
      simp only [ofReal_ofNat] at hmul
      rw [← hmul]; congr 1; push_cast; ring
  have hsum : (2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2) + (2 : ℂ) ^ (-s) * riemannZeta s =
      riemannZeta s := (HasSum.even_add_odd heven hodd).unique hzeta
  have htwo : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, add_neg_cancel, cpow_zero]
  calc complexHurwitzSeries s (1 / 2)
      = (2 : ℂ) ^ s * ((2 : ℂ) ^ (-s) * complexHurwitzSeries s (1 / 2)) := by
        rw [← mul_assoc, htwo, one_mul]
    _ = (2 : ℂ) ^ s * (riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s) := by
        rw [eq_sub_of_add_eq hsum]
    _ = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
        rw [mul_sub, ← mul_assoc, htwo]; ring

example : complexHurwitzSeries 2 (1 + I) - complexHurwitzSeries 2 (2 + I) = -I / 2 := by
  have hne : (1 + I : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hshift := complexHurwitzSeries_add_one_right (s := 2) (by norm_num) hne
  have h2I : (1 + I : ℂ) + 1 = 2 + I := by ring
  have hsq : (1 + I : ℂ) ^ (2 : ℕ) = 2 * I := by rw [sq]; ring_nf; simp
  rw [h2I] at hshift
  rw [hshift, sub_sub_cancel]
  simp only [cpow_neg, cpow_ofNat, hsq, mul_inv, inv_I]
  ring

end TauCeti

end
