/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Unconditional
public import TauCeti.Analysis.SpecialFunctions.Pow.Burkholder
public import TauCeti.MeasureTheory.Function.Lp.HaarBasis.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Unconditionality of the Haar basis of `Lᵖ([0, 1])`

For `1 < p < ∞` and `𝕜` equal to `ℝ` or `ℂ` (`[RCLike 𝕜]`), the Haar basis `haarBasis 𝕜 p hp` of
`Lᵖ(I; 𝕜)` is unconditional.

For `2 ≤ p < ∞` over `ℝ`, unconditionality with the sharp sign-transform constant `p - 1` follows
from Burkholder's scalar Bellman estimates (`TauCeti.mul_burkholderPhi_le` and
`TauCeti.two_mul_burkholderPhi_abs_le`). Writing `F_N = ∑_{k < N} c_k h_k` and
`G_N = ∑_{k < N} ε_k c_k h_k` with `|ε_k| = 1`, the functions `F_N` and `G_N` are constant on the
dyadic cell numbered `N`, while `h_N` equals `1` on its left half `2 * N` and `-1` on its right
half `2 * N + 1`, each of half the measure. Integrating the midpoint inequality over `dyadicCell N`
shows that `∫ x, Φ_p(|F_N x|, |G_N x|)` is nondecreasing for `N ≥ 1`, and at `N = 1` the integrand
is a nonnegative constant. Integrating the majorization inequality then gives
`‖G_N‖_p ≤ (p - 1) ‖F_N‖_p`.

At `p = 2`, `L²`-orthogonality of distinct Haar functions yields Parseval's identity for finite
Haar sums and shows that any unimodular Haar multiplier (`‖u_k‖ = 1`) preserves the `L²` norm.

For `1 < p ≤ 2` over `ℝ`, pairing against `L^q(I)` (`1 / p + 1 / q = 1`, so `2 ≤ q < ∞`) via
`MeasureTheory.Lp.toDual`, pulling finite Haar sums through `dyadicProj ℝ q N`, and using
orthogonality to transpose the sign multiplier from `Lᵖ` to `L^q` transfers the `L^q` bound
`q - 1 = p / (p - 1) - 1` to `Lᵖ`. Together the two regimes give the sharp real unconditional
constant `max p (p / (p - 1)) - 1` for `1 < p < ∞`. Splitting `Lᵖ(I; 𝕜)` into real and imaginary
parts extends the bound to `[RCLike 𝕜]` with factor `2`.

Because the initial projections `dyadicProj 𝕜 p N` are contractions, the initial-segment sign bound
extends with the same constant to all finite coordinate projections
(`SchauderBasis.norm_proj_finset_le_of_range_signed`), giving unconditional convergence of the Haar
expansion and the bundled `UnconditionalSchauderBasis` `haarUnconditionalBasis`.

## Main definitions

* `TauCeti.unitInterval.haarUnconditionalBasis 𝕜 p hp1 hp`: the Haar system as an
  `UnconditionalSchauderBasis` of `Lᵖ(I; 𝕜)` for `1 < p < ∞`.

## Main results

* `TauCeti.unitInterval.integral_burkholderPhi_haarFun_nonneg`: nonnegativity of the integrated
  Burkholder function on signed Haar partial sums for `2 ≤ p`.
* `TauCeti.unitInterval.norm_sq_sum_haarBasis_two`,
  `TauCeti.unitInterval.norm_sum_unimodular_haarBasis_two`: Parseval's identity and `L²` isometry
  of unimodular Haar multipliers.
* `TauCeti.unitInterval.norm_sum_signed_haarBasis_real_le`: sharp real `Lᵖ` bound
  `max p.toReal (p.toReal / (p.toReal - 1)) - 1` on signed Haar sums for `1 < p < ∞`.
* `TauCeti.unitInterval.norm_sum_signed_haarBasis_le`: `Lᵖ(I; 𝕜)` bound on signed Haar sums.
* `TauCeti.unitInterval.hasSum_haarBasis`: unconditional convergence of the Haar expansion in
  `Lᵖ(I; 𝕜)` for `1 < p < ∞`.
* `TauCeti.unitInterval.nnNormProjBound_haarUnconditionalBasis_real_le`,
  `TauCeti.unitInterval.nnNormProjBound_haarUnconditionalBasis_le`: unconditional basis constant
  estimates over `ℝ` and `𝕜`.

## References

* D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
  Ann. Probab. **12** (1984), 647–702.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Graduate Texts in
  Mathematics 233, Springer (2016), §6.1.
-/

public section

noncomputable section

open MeasureTheory Filter ComplexConjugate TauCeti
open scoped ENNReal Topology unitInterval

namespace TauCeti.unitInterval

/-! ### Finite Haar sums and integrability -/

/-- Pointwise partial sum `∑_{k < N} c_k h_k(x)` of the Haar functions with real coefficients. -/
private def haarSum (c : ℕ → ℝ) (N : ℕ) (x : I) : ℝ :=
  ∑ k ∈ Finset.range N, c k * haarFun k x

private theorem haarSum_def (c : ℕ → ℝ) (N : ℕ) (x : I) :
    haarSum c N x = ∑ k ∈ Finset.range N, c k * haarFun k x :=
  rfl

@[simp]
private theorem haarSum_zero (c : ℕ → ℝ) (x : I) : haarSum c 0 x = 0 := by
  simp [haarSum]

private theorem haarSum_succ (c : ℕ → ℝ) (N : ℕ) (x : I) :
    haarSum c (N + 1) x = haarSum c N x + c N * haarFun N x := by
  simp [haarSum, Finset.sum_range_succ]

@[fun_prop]
private theorem measurable_haarSum (c : ℕ → ℝ) (N : ℕ) : Measurable (haarSum c N) := by
  unfold haarSum
  fun_prop

private theorem norm_haarSum_le (c : ℕ → ℝ) (N : ℕ) (x : I) :
    ‖haarSum c N x‖ ≤ ∑ k ∈ Finset.range N, |c k| := by
  calc
    ‖∑ k ∈ Finset.range N, c k * haarFun k x‖
        ≤ ∑ k ∈ Finset.range N, ‖c k * haarFun k x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, |c k| := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_haarFun_le k x)

private theorem haarSum_eq_of_mem_dyadicCell (c : ℕ → ℝ) {N : ℕ} {x y : I}
    (hx : x ∈ dyadicCell N) (hy : y ∈ dyadicCell N) :
    haarSum c N x = haarSum c N y := by
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [haarFun_eq_of_mem_dyadicCell (Finset.mem_range.1 hk) hx hy]

private theorem integrable_burkholderPhi_haarSum {p : ℝ} (hp : 2 ≤ p) (c d : ℕ → ℝ) (N : ℕ) :
    Integrable (fun x => burkholderPhi p |haarSum c N x| |haarSum d N x|)
      (volume : Measure I) := by
  let B : ℝ := (∑ k ∈ Finset.range N, |c k|) + ∑ k ∈ Finset.range N, |d k|
  have hB : 0 ≤ B := add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hmeas : Measurable fun x => burkholderPhi p |haarSum c N x| |haarSum d N x| := by
    have hcont : Continuous fun z : ℝ × ℝ => burkholderPhi p |z.1| |z.2| := by
      simp only [burkholderPhi_def]
      fun_prop (disch := linarith)
    exact hcont.measurable.comp ((measurable_haarSum c N).prodMk (measurable_haarSum d N))
  refine (MemLp.of_bound hmeas.aestronglyMeasurable (B ^ (p - 1) * (p * B))
    (ae_of_all _ fun x => ?_)).integrable le_rfl
  have hc : |haarSum c N x| ≤ ∑ k ∈ Finset.range N, |c k| := by
    simpa [Real.norm_eq_abs] using norm_haarSum_le c N x
  have hd : |haarSum d N x| ≤ ∑ k ∈ Finset.range N, |d k| := by
    simpa [Real.norm_eq_abs] using norm_haarSum_le d N x
  have hsum : |haarSum c N x| + |haarSum d N x| ≤ B := add_le_add hc hd
  have hlin : |((p - 1) * |haarSum c N x| - |haarSum d N x|)| ≤ p * B := by
    rw [abs_le]
    have h1 : 0 ≤ |haarSum c N x| := abs_nonneg _
    have h2 : 0 ≤ |haarSum d N x| := abs_nonneg _
    constructor <;> nlinarith
  rw [burkholderPhi_def, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact mul_le_mul (Real.rpow_le_rpow (by positivity) hsum (by linarith)) hlin
    (abs_nonneg _) (Real.rpow_nonneg hB _)

private theorem integrable_rpow_abs_haarSum {p : ℝ} (hp : 0 ≤ p) (c : ℕ → ℝ) (N : ℕ) :
    Integrable (fun x => |haarSum c N x| ^ p) (volume : Measure I) := by
  let B : ℝ := ∑ k ∈ Finset.range N, |c k|
  have hmeas : Measurable fun x => |haarSum c N x| ^ p :=
    (Real.continuous_rpow_const hp).measurable.comp
      (continuous_abs.measurable.comp (measurable_haarSum c N))
  refine (MemLp.of_bound hmeas.aestronglyMeasurable (B ^ p)
    (ae_of_all _ fun x => ?_)).integrable le_rfl
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _)
    (by simpa [Real.norm_eq_abs] using norm_haarSum_le c N x) hp

/-! ### The Bellman step for `2 ≤ p < ∞` -/

private theorem setIntegral_dyadicCell_two_mul_burkholderPhi (p : ℝ) (c d : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) {x₀ : I} (hx₀ : x₀ ∈ dyadicCell N) :
    (∫ x in dyadicCell (2 * N), burkholderPhi p |haarSum c (N + 1) x| |haarSum d (N + 1) x|) =
      (volume.real (dyadicCell N) / 2) *
        burkholderPhi p |haarSum c N x₀ + c N| |haarSum d N x₀ + d N| := by
  have hsub : dyadicCell (2 * N) ⊆ dyadicCell N :=
    fun _ => mem_dyadicCell_of_mem_two_mul_add (e := 0) hN two_pos
  have hvol : volume (dyadicCell (2 * N)) = volume (dyadicCell N) / 2 := by
    simpa using volume_dyadicCell_two_mul_add (e := 0) hN two_pos
  calc
    ∫ x in dyadicCell (2 * N), burkholderPhi p |haarSum c (N + 1) x| |haarSum d (N + 1) x|
        = ∫ _ in dyadicCell (2 * N),
            burkholderPhi p |haarSum c N x₀ + c N| |haarSum d N x₀ + d N| :=
          setIntegral_congr_fun (measurableSet_dyadicCell _) fun x hx => by
            rw [haarSum_succ, haarSum_succ, haarSum_eq_of_mem_dyadicCell c (hsub hx) hx₀,
              haarSum_eq_of_mem_dyadicCell d (hsub hx) hx₀, haarFun_eq_one hN hx, mul_one, mul_one]
    _ = (volume.real (dyadicCell N) / 2) *
          burkholderPhi p |haarSum c N x₀ + c N| |haarSum d N x₀ + d N| := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, hvol, ENNReal.toReal_div,
            ENNReal.toReal_ofNat, ← measureReal_def]

private theorem setIntegral_dyadicCell_two_mul_add_one_burkholderPhi (p : ℝ) (c d : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) {x₀ : I} (hx₀ : x₀ ∈ dyadicCell N) :
    (∫ x in dyadicCell (2 * N + 1), burkholderPhi p |haarSum c (N + 1) x| |haarSum d (N + 1) x|) =
      (volume.real (dyadicCell N) / 2) *
        burkholderPhi p |haarSum c N x₀ - c N| |haarSum d N x₀ - d N| := by
  have hsub : dyadicCell (2 * N + 1) ⊆ dyadicCell N :=
    fun _ => mem_dyadicCell_of_mem_two_mul_add hN one_lt_two
  calc
    ∫ x in dyadicCell (2 * N + 1), burkholderPhi p |haarSum c (N + 1) x| |haarSum d (N + 1) x|
        = ∫ _ in dyadicCell (2 * N + 1),
            burkholderPhi p |haarSum c N x₀ - c N| |haarSum d N x₀ - d N| :=
          setIntegral_congr_fun (measurableSet_dyadicCell _) fun x hx => by
            rw [haarSum_succ, haarSum_succ, haarSum_eq_of_mem_dyadicCell c (hsub hx) hx₀,
              haarSum_eq_of_mem_dyadicCell d (hsub hx) hx₀, haarFun_eq_neg_one hN hx,
              mul_neg_one, mul_neg_one, ← sub_eq_add_neg, ← sub_eq_add_neg]
    _ = (volume.real (dyadicCell N) / 2) *
          burkholderPhi p |haarSum c N x₀ - c N| |haarSum d N x₀ - d N| := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def,
            volume_dyadicCell_two_mul_add hN one_lt_two, ENNReal.toReal_div, ENNReal.toReal_ofNat,
            ← measureReal_def]

/-- For `0 < N`, `2 ≤ p`, and `|ε N| = 1`, the integral of `Φ_p(|F_N|, |G_N|)` is nondecreasing
from step `N` to step `N + 1`. -/
private theorem integral_burkholderPhi_haarSum_le_succ {p : ℝ} (hp : 2 ≤ p)
    (c ε : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (hεN : |ε N| = 1) :
    ∫ x, burkholderPhi p |haarSum c N x| |haarSum (fun k => ε k * c k) N x| ≤
      ∫ x, burkholderPhi p |haarSum c (N + 1) x| |haarSum (fun k => ε k * c k) (N + 1) x| := by
  let d : ℕ → ℝ := fun k => ε k * c k
  let Φ (M : ℕ) (x : I) : ℝ := burkholderPhi p |haarSum c M x| |haarSum d M x|
  have hΦ (M : ℕ) : Integrable (Φ M) volume := integrable_burkholderPhi_haarSum hp c d M
  rw [← integral_add_compl (measurableSet_dyadicCell N) (hΦ N),
    ← integral_add_compl (measurableSet_dyadicCell N) (hΦ (N + 1))]
  have hcompl : ∫ x in (dyadicCell N)ᶜ, Φ N x = ∫ x in (dyadicCell N)ᶜ, Φ (N + 1) x :=
    setIntegral_congr_fun (measurableSet_dyadicCell N).compl fun x hx => by
      simp [Φ, haarSum_succ, haarFun_eq_zero hN hx]
  rw [hcompl]
  refine add_le_add_left ?_ _
  obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero (μ := (volume : Measure I)) (s := dyadicCell N)
    (by rw [volume_dyadicCell hN]; exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  have hLHS : ∫ x in dyadicCell N, Φ N x =
      volume.real (dyadicCell N) * burkholderPhi p |haarSum c N x₀| |haarSum d N x₀| := by
    calc ∫ x in dyadicCell N, Φ N x
        = ∫ _ in dyadicCell N, burkholderPhi p |haarSum c N x₀| |haarSum d N x₀| :=
          setIntegral_congr_fun (measurableSet_dyadicCell N) fun x hx => by
            dsimp only [Φ]
            rw [haarSum_eq_of_mem_dyadicCell c hx hx₀, haarSum_eq_of_mem_dyadicCell d hx hx₀]
      _ = volume.real (dyadicCell N) * burkholderPhi p |haarSum c N x₀| |haarSum d N x₀| := by simp
  have hRHS : ∫ x in dyadicCell N, Φ (N + 1) x =
      (∫ x in dyadicCell (2 * N), Φ (N + 1) x) + ∫ x in dyadicCell (2 * N + 1), Φ (N + 1) x := by
    conv_lhs => rw [dyadicCell_eq_union hN]
    exact setIntegral_union (disjoint_dyadicCell_two_mul hN) (measurableSet_dyadicCell _)
      (hΦ (N + 1)).integrableOn (hΦ (N + 1)).integrableOn
  rw [hLHS, hRHS, setIntegral_dyadicCell_two_mul_burkholderPhi p c d hN hx₀,
    setIntegral_dyadicCell_two_mul_add_one_burkholderPhi p c d hN hx₀]
  have hmid := mul_le_mul_of_nonneg_left
    (two_mul_burkholderPhi_abs_le hp (haarSum c N x₀) (haarSum d N x₀) (c N) hεN)
    (div_nonneg measureReal_nonneg zero_le_two : 0 ≤ volume.real (dyadicCell N) / 2)
  dsimp only [d] at hmid ⊢
  linarith

/-- For `2 ≤ p` and signs `|ε k| = 1`, Burkholder's function `Φ_p` has nonnegative integral along
every partial sum of the Haar system and its signed transform. -/
theorem integral_burkholderPhi_haarFun_nonneg {p : ℝ} (hp : 2 ≤ p)
    (c : ℕ → ℝ) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1) (N : ℕ) :
    0 ≤ ∫ x, burkholderPhi p
      |∑ k ∈ Finset.range N, c k * haarFun k x|
      |∑ k ∈ Finset.range N, (ε k * c k) * haarFun k x| := by
  simp_rw [← haarSum_def]
  induction N with
  | zero => simp
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine integral_nonneg fun x => ?_
      have h0 : |haarSum (fun k => ε k * c k) 1 x| = |c 0| := by
        simp [haarSum, abs_mul, hε 0]
      have hc0 : |haarSum c 1 x| = |c 0| := by simp [haarSum]
      have hlin : (p - 1) * |c 0| - |c 0| = (p - 2) * |c 0| := by ring
      rw [hc0, h0, burkholderPhi_def, hlin]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
        (mul_nonneg (by linarith) (abs_nonneg _))
    · exact ih.trans (integral_burkholderPhi_haarSum_le_succ hp c ε hN (hε N))

/-- For `2 ≤ p` and signs `|ε k| = 1`, the `p`-th moment of a signed Haar partial sum is at most
`(p - 1) ^ p` times the `p`-th moment of the unsigned partial sum. -/
theorem integral_rpow_abs_haarFun_signed_le {p : ℝ} (hp : 2 ≤ p)
    (c : ℕ → ℝ) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1) (N : ℕ) :
    ∫ x, |∑ k ∈ Finset.range N, (ε k * c k) * haarFun k x| ^ p ≤
      (p - 1) ^ p * ∫ x, |∑ k ∈ Finset.range N, c k * haarFun k x| ^ p := by
  let d : ℕ → ℝ := fun k => ε k * c k
  have hp0 : 0 ≤ p := by linarith
  have hint_c : Integrable (fun x => |haarSum c N x| ^ p) volume :=
    integrable_rpow_abs_haarSum hp0 c N
  have hint_d : Integrable (fun x => |haarSum d N x| ^ p) volume :=
    integrable_rpow_abs_haarSum hp0 d N
  have hint_Φ : Integrable (fun x => burkholderPhi p |haarSum c N x| |haarSum d N x|) volume :=
    integrable_burkholderPhi_haarSum hp c d N
  set κ : ℝ := (p - 1) ^ (p - 1) / p ^ (p - 2)
  have hκ : 0 ≤ κ := div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hp0 _)
  have hle : κ * ∫ x, burkholderPhi p |haarSum c N x| |haarSum d N x| ≤
      (p - 1) ^ p * (∫ x, |haarSum c N x| ^ p) - ∫ x, |haarSum d N x| ^ p := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hint_c.const_mul _) hint_d]
    exact integral_mono (hint_Φ.const_mul _) ((hint_c.const_mul _).sub hint_d) fun x =>
      mul_burkholderPhi_le hp (abs_nonneg _) (abs_nonneg _)
  have hΦ0 : 0 ≤ κ * ∫ x, burkholderPhi p |haarSum c N x| |haarSum d N x| :=
    mul_nonneg hκ (integral_burkholderPhi_haarFun_nonneg hp c hε N)
  dsimp only [haarSum, d] at hle hΦ0
  linarith

private theorem coeFn_sum_haarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (c : ℕ → 𝕜) (N : ℕ) :
    (∑ k ∈ Finset.range N, c k • haarBasis 𝕜 p hp k : Lp 𝕜 p (volume : Measure I)) =ᵐ[volume]
      fun x => ∑ k ∈ Finset.range N, c k * (haarFun k x : 𝕜) := by
  have hterm (k : ℕ) :
      (c k • haarBasis 𝕜 p hp k : Lp 𝕜 p (volume : Measure I)) =ᵐ[volume]
        fun x => c k * (haarFun k x : 𝕜) := by
    filter_upwards [Lp.coeFn_smul (c k) (haarBasis 𝕜 p hp k),
      coeFn_haarBasis (𝕜 := 𝕜) (p := p) hp k] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  filter_upwards [Lp.coeFn_finsetSum (Finset.range N) fun k => c k • haarBasis 𝕜 p hp k,
    ae_all_iff.2 fun k : Fin N => hterm k] with x hsum hk
  rw [hsum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun k hk_mem => hk ⟨k, Finset.mem_range.1 hk_mem⟩

/-- **Sharp `Lᵖ` sign-transform bound for the real Haar basis (`2 ≤ p < ∞`).** -/
theorem norm_sum_signed_haarBasis_real_le_of_two_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp2 : 2 ≤ p) (hp : p ≠ ∞) (c : ℕ → ℝ) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (ε k * c k) • haarBasis ℝ p hp k‖ ≤
      (p.toReal - 1) * ‖∑ k ∈ Finset.range N, c k • haarBasis ℝ p hp k‖ := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans_le hp2).ne'
  set r := p.toReal
  have hr2 : 2 ≤ r := by simpa [r] using ENNReal.toReal_mono hp hp2
  set f : Lp ℝ p (volume : Measure I) := ∑ k ∈ Finset.range N, c k • haarBasis ℝ p hp k
  set g : Lp ℝ p (volume : Measure I) := ∑ k ∈ Finset.range N, (ε k * c k) • haarBasis ℝ p hp k
  have hf_rpow : ‖f‖ ^ r = ∫ x, |∑ k ∈ Finset.range N, c k * haarFun k x| ^ r := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp f]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sum_haarBasis hp c N] with x hx
    simp only [f, r, Real.norm_eq_abs, hx, RCLike.ofReal_real_eq_id, id_eq]
  have hg_rpow : ‖g‖ ^ r = ∫ x, |∑ k ∈ Finset.range N, (ε k * c k) * haarFun k x| ^ r := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp g]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sum_haarBasis hp (fun k => ε k * c k) N] with x hx
    simp only [g, r, Real.norm_eq_abs, hx, RCLike.ofReal_real_eq_id, id_eq]
  refine (Real.rpow_le_rpow_iff (norm_nonneg g)
    (mul_nonneg (by linarith) (norm_nonneg f)) (by linarith : 0 < r)).1 ?_
  rw [Real.mul_rpow (by linarith) (norm_nonneg f), hg_rpow, hf_rpow]
  exact integral_rpow_abs_haarFun_signed_le hr2 c hε N

/-! ### `L²` orthogonality and unimodular multipliers -/

/-- **Parseval's identity for finite Haar sums in `L²([0, 1]; 𝕜)`.** -/
theorem norm_sq_sum_haarBasis_two (𝕜 : Type*) [RCLike 𝕜] (c : ℕ → 𝕜) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, c k • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k‖ ^ 2 =
      ∑ k ∈ Finset.range N, ‖c k‖ ^ 2 * ∫ x, haarFun k x ^ 2 := by
  have hint (j k : ℕ) : Integrable (fun x => haarFun j x * haarFun k x) volume := by
    refine (MemLp.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)).integrable le_rfl
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_haarFun_le k x)).trans (norm_haarFun_le j x)
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  have hcongr : (∫ x, ‖(∑ k ∈ Finset.range N, c k • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k) x‖ ^ 2) =
      ∫ x, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        RCLike.re (conj (c j) * c k) * (haarFun j x * haarFun k x) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sum_haarBasis (𝕜 := 𝕜) (p := 2) ENNReal.ofNat_ne_top c N] with x hx
    rw [hx]
    have hsq : ∀ z : 𝕜, ‖z‖ ^ 2 = RCLike.re (conj z * z) := fun z => by
      have := congrArg RCLike.re (RCLike.conj_mul z)
      simpa using this.symm
    rw [hsq]
    simp only [map_sum, map_mul, RCLike.conj_ofReal]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    have : conj (c j) * (haarFun j x : 𝕜) * (c k * (haarFun k x : 𝕜)) =
        ((haarFun j x * haarFun k x : ℝ) : 𝕜) * (conj (c j) * c k) := by
      push_cast
      ring
    rw [this, ← Algebra.smul_def, RCLike.smul_re, mul_comm]
  rw [hcongr, integral_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => (hint j k).const_mul _]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => (hint j k).const_mul _,
    Finset.sum_eq_single_of_mem j hj fun k _ hkj => by
      rw [integral_const_mul, integral_haarFun_mul_of_ne hkj.symm, mul_zero]]
  rw [integral_const_mul]
  have hcj : RCLike.re (conj (c j) * c j) = ‖c j‖ ^ 2 := by
    simpa using congrArg RCLike.re (RCLike.conj_mul (c j))
  simp [hcj, sq]

/-- Unimodular Haar multipliers (`‖u k‖ = 1`, in particular real signs `±1`) are `L²` isometries. -/
theorem norm_sum_unimodular_haarBasis_two (𝕜 : Type*) [RCLike 𝕜]
    (c : ℕ → 𝕜) {u : ℕ → 𝕜} (hu : ∀ k, ‖u k‖ = 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (u k * c k) • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k‖ =
      ‖∑ k ∈ Finset.range N, c k • haarBasis 𝕜 2 ENNReal.ofNat_ne_top k‖ := by
  refine sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.1 ?_
  rw [norm_sq_sum_haarBasis_two, norm_sq_sum_haarBasis_two]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, hu k, one_mul]

/-! ### Hölder duality for `1 < p ≤ 2` -/

private theorem integral_haarFun_mul_dyadicProj {q : ℝ≥0∞} [Fact (1 ≤ q)] {k N : ℕ}
    (hk : k < N) (g : Lp ℝ q (volume : Measure I)) :
    ∫ x, haarFun k x * g x = ∫ x, haarFun k x * dyadicProj ℝ q N g x := by
  have hN : N ≠ 0 := by omega
  have hm : StronglyMeasurable[dyadicFiltration N] (haarFun k) :=
    ((measurable_haarFun_dyadicFiltration k).mono
      (dyadicFiltration.mono (by omega)) le_rfl).stronglyMeasurable
  have hg_int : Integrable g (volume : Measure I) := (Lp.memLp g).integrable Fact.out
  have hpull := condExp_stronglyMeasurable_mul_of_bound (dyadicFiltration.le N) hm hg_int 1
    (ae_of_all _ (norm_haarFun_le k))
  calc
    ∫ x, haarFun k x * g x
        = ∫ x, volume[haarFun k * ⇑g | dyadicFiltration N] x :=
          (integral_condExp (dyadicFiltration.le N)).symm
    _ = ∫ x, haarFun k x * volume[⇑g | dyadicFiltration N] x := integral_congr_ae hpull
    _ = ∫ x, haarFun k x * dyadicProj ℝ q N g x := by
          refine integral_congr_ae ?_
          filter_upwards [dyadicProj_ae_eq hN g] with x hx
          rw [hx]

/-- Orthogonality of distinct Haar functions makes signed Haar partial sums self-transpose with
respect to the integral pairing on `I`. -/
private theorem integral_haarSum_signed_mul (c d ε : ℕ → ℝ) (N : ℕ) :
    ∫ x, haarSum (fun k => ε k * c k) N x * haarSum d N x =
      ∫ x, haarSum c N x * haarSum (fun k => ε k * d k) N x := by
  have hint (j k : ℕ) : Integrable (fun x => haarFun j x * haarFun k x) volume := by
    refine (MemLp.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)).integrable le_rfl
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_haarFun_le k x)).trans (norm_haarFun_le j x)
  have expand (a b : ℕ → ℝ) :
      (∫ x, haarSum a N x * haarSum b N x) =
        ∑ k ∈ Finset.range N, a k * b k * ∫ x, haarFun k x * haarFun k x := by
    have hfun : (fun x => haarSum a N x * haarSum b N x) =
        fun x => ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (a k * b j) * (haarFun k x * haarFun j x) := by
      ext x
      dsimp only [haarSum]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hfun, integral_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun j _ => (hint k j).const_mul _]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [integral_finsetSum _ fun j _ => (hint k j).const_mul _,
      Finset.sum_eq_single_of_mem k hk fun j _ hjk => by
        rw [integral_const_mul, integral_haarFun_mul_of_ne hjk.symm, mul_zero]]
    exact integral_const_mul _ _
  rw [expand, expand]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem toDual_sum_signed_haarBasis {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : p ≠ ∞) (hq : q ≠ ∞) (c ε : ℕ → ℝ) (N : ℕ)
    (g : Lp ℝ q (volume : Measure I)) :
    Lp.toDual ℝ (volume : Measure I) p q
        (∑ k ∈ Finset.range N, (ε k * c k) • haarBasis ℝ p hp k) g =
      Lp.toDual ℝ (volume : Measure I) p q
        (∑ k ∈ Finset.range N, c k • haarBasis ℝ p hp k)
        (∑ k ∈ Finset.range N, (ε k * (haarBasis ℝ q hq).coord k g) • haarBasis ℝ q hq k) := by
  let d (k : ℕ) : ℝ := (haarBasis ℝ q hq).coord k g
  let gN : Lp ℝ q (volume : Measure I) := ∑ k ∈ Finset.range N, d k • haarBasis ℝ q hq k
  have hgN_eq : dyadicProj ℝ q N g = gN := by
    rw [← haarBasis_proj (𝕜 := ℝ) hq, SchauderBasis.proj_apply]
  have hg_int : Integrable g (volume : Measure I) := (Lp.memLp g).integrable Fact.out
  have hgN_int : Integrable gN (volume : Measure I) := (Lp.memLp gN).integrable Fact.out
  have hint_mul {u : I → ℝ} (hu : Integrable u volume) (k : ℕ) :
      Integrable (fun x => haarFun k x * u x) volume :=
    hu.bdd_mul (measurable_haarFun k).aestronglyMeasurable (ae_of_all _ (norm_haarFun_le k))
  have hmul (u : I → ℝ) (k : ℕ) (x : I) :
      ε k * c k * haarFun k x * u x = (ε k * c k) * (haarFun k x * u x) :=
    mul_assoc (ε k * c k) (haarFun k x) (u x)
  rw [Lp.toDual_apply, Lp.toDual_apply]
  calc
    ∫ x, (∑ k ∈ Finset.range N, (ε k * c k) • haarBasis ℝ p hp k) x * g x
        = ∫ x, haarSum (fun k => ε k * c k) N x * g x := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_sum_haarBasis hp (fun k => ε k * c k) N] with x hx
          simp only [haarSum, hx, RCLike.ofReal_real_eq_id, id_eq]
    _ = ∑ k ∈ Finset.range N, (ε k * c k) * ∫ x, haarFun k x * g x := by
          simp_rw [haarSum, Finset.sum_mul, hmul]
          rw [integral_finsetSum _ fun k _ => (hint_mul hg_int k).const_mul _]
          exact Finset.sum_congr rfl fun k _ => integral_const_mul _ _
    _ = ∑ k ∈ Finset.range N, (ε k * c k) * ∫ x, haarFun k x * gN x := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [integral_haarFun_mul_dyadicProj (Finset.mem_range.1 hk), hgN_eq]
    _ = ∫ x, haarSum (fun k => ε k * c k) N x * gN x := by
          simp_rw [haarSum, Finset.sum_mul, hmul]
          rw [integral_finsetSum _ fun k _ => (hint_mul hgN_int k).const_mul _]
          exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm
    _ = ∫ x, haarSum (fun k => ε k * c k) N x * haarSum d N x := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_sum_haarBasis hq d N] with x hx
          simp only [gN, haarSum, hx, RCLike.ofReal_real_eq_id, id_eq]
    _ = ∫ x, haarSum c N x * haarSum (fun k => ε k * d k) N x :=
          integral_haarSum_signed_mul c d ε N
    _ = ∫ x, (∑ k ∈ Finset.range N, c k • haarBasis ℝ p hp k) x *
          (∑ k ∈ Finset.range N, (ε k * d k) • haarBasis ℝ q hq k) x := by
          refine integral_congr_ae ?_
          filter_upwards [coeFn_sum_haarBasis hp c N,
            coeFn_sum_haarBasis hq (fun k => ε k * d k) N] with x hfx hgx
          simp only [haarSum, hfx, hgx, RCLike.ofReal_real_eq_id, id_eq]

/-- **Sharp `Lᵖ` sign-transform bound for the real Haar basis (`1 < p ≤ 2`).** -/
theorem norm_sum_signed_haarBasis_real_le_of_le_two {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp2 : p ≤ 2) (hp : p ≠ ∞) (c : ℕ → ℝ) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1)
    (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (ε k * c k) • haarBasis ℝ p hp k‖ ≤
      (p.toReal / (p.toReal - 1) - 1) *
        ‖∑ k ∈ Finset.range N, c k • haarBasis ℝ p hp k‖ := by
  set r := p.toReal
  have hr1 : 1 < r := by simpa [r] using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  have hr2 : r ≤ 2 := by simpa [r] using ENNReal.toReal_mono ENNReal.ofNat_ne_top hp2
  set s := r / (r - 1)
  have hs2 : 2 ≤ s := (le_div_iff₀ (by linarith)).2 (by linarith)
  have hrs : r⁻¹ + s⁻¹ = 1 := by
    have hr0 : r ≠ 0 := by linarith
    simp only [s, inv_div]
    field_simp [hr0]
    ring
  set q : ℝ≥0∞ := ENNReal.ofReal s
  have hq : q ≠ ∞ := ENNReal.ofReal_ne_top
  have hq_toReal : q.toReal = s := ENNReal.toReal_ofReal (by linarith)
  have hq2 : 2 ≤ q := by
    have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    rw [h2]
    exact ENNReal.ofReal_le_ofReal hs2
  have : Fact (1 ≤ q) := ⟨one_le_two.trans hq2⟩
  have : p.HolderConjugate q := by
    rw [ENNReal.holderConjugate_iff, ← ENNReal.ofReal_toReal hp,
      ← ENNReal.ofReal_inv_of_pos (by linarith), ← ENNReal.ofReal_inv_of_pos (by linarith),
      ← ENNReal.ofReal_add (by positivity) (by positivity), hrs, ENNReal.ofReal_one]
  set f : Lp ℝ p (volume : Measure I) := ∑ k ∈ Finset.range N, c k • haarBasis ℝ p hp k
  set h : Lp ℝ p (volume : Measure I) := ∑ k ∈ Finset.range N, (ε k * c k) • haarBasis ℝ p hp k
  rw [← (Lp.toDual ℝ (volume : Measure I) p q).norm_map h]
  refine (Lp.toDual ℝ (volume : Measure I) p q h).opNorm_le_bound
    (mul_nonneg (by linarith) (norm_nonneg f)) fun g => ?_
  let d (k : ℕ) : ℝ := (haarBasis ℝ q hq).coord k g
  let gNε : Lp ℝ q (volume : Measure I) := ∑ k ∈ Finset.range N, (ε k * d k) • haarBasis ℝ q hq k
  have hgNε_norm : ‖gNε‖ ≤ (s - 1) * ‖g‖ := by
    calc
      ‖gNε‖ ≤ (q.toReal - 1) * ‖∑ k ∈ Finset.range N, d k • haarBasis ℝ q hq k‖ :=
        norm_sum_signed_haarBasis_real_le_of_two_le hq2 hq d hε N
      _ = (s - 1) * ‖dyadicProj ℝ q N g‖ := by
        rw [hq_toReal, ← SchauderBasis.proj_apply, haarBasis_proj]
      _ ≤ (s - 1) * ‖g‖ := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        simpa using (dyadicProj ℝ q N).le_of_opNorm_le (norm_dyadicProj_le ℝ q N) g
  calc
    ‖Lp.toDual ℝ (volume : Measure I) p q h g‖
        = ‖Lp.toDual ℝ (volume : Measure I) p q f gNε‖ :=
          congrArg norm (toDual_sum_signed_haarBasis hp hq c ε N g)
    _ ≤ ‖Lp.toDual ℝ (volume : Measure I) p q f‖ * ‖gNε‖ :=
        (Lp.toDual ℝ (volume : Measure I) p q f).le_opNorm gNε
    _ = ‖f‖ * ‖gNε‖ := by rw [(Lp.toDual ℝ (volume : Measure I) p q).norm_map]
    _ ≤ ‖f‖ * ((s - 1) * ‖g‖) := mul_le_mul_of_nonneg_left hgNε_norm (norm_nonneg f)
    _ = (s - 1) * ‖f‖ * ‖g‖ := by ring

/-- **Sharp `Lᵖ` sign-transform bound for the real Haar basis (`1 < p < ∞`).** For `1 < p < ∞` and
signs `|ε k| = 1`, `‖∑_{k < N} ε_k c_k h_k‖_p ≤ (max p (p / (p - 1)) - 1) ‖∑_{k < N} c_k h_k‖_p`. -/
theorem norm_sum_signed_haarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (c : ℕ → ℝ) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, (ε k * c k) • haarBasis ℝ p hp k‖ ≤
      (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
        ‖∑ k ∈ Finset.range N, c k • haarBasis ℝ p hp k‖ := by
  rcases le_total 2 p with hp2 | hp2
  · exact (norm_sum_signed_haarBasis_real_le_of_two_le hp2 hp c hε N).trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_right (le_max_left _ _) 1) (norm_nonneg _))
  · exact (norm_sum_signed_haarBasis_real_le_of_le_two hp1 hp2 hp c hε N).trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_right (le_max_right _ _) 1) (norm_nonneg _))

private theorem one_le_haarRealBound {p : ℝ≥0∞} (hp1 : 1 < p) (hp : p ≠ ∞) :
    1 ≤ max p.toReal (p.toReal / (p.toReal - 1)) - 1 := by
  have hr1 : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  rcases le_total 2 p.toReal with hr2 | hr2
  · have : 2 ≤ max p.toReal (p.toReal / (p.toReal - 1)) := hr2.trans (le_max_left _ _)
    linarith
  · have hq2 : 2 ≤ p.toReal / (p.toReal - 1) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have : 2 ≤ max p.toReal (p.toReal / (p.toReal - 1)) := hq2.trans (le_max_right _ _)
    linarith

/-! ### Extension to `RCLike` scalars and unconditional basis of `Lᵖ([0, 1]; 𝕜)` -/

private theorem compLpL_sum_haarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (L : 𝕜 →L[ℝ] ℝ) (a : ℕ → 𝕜) (N : ℕ) :
    L.compLpL p (volume : Measure I) (∑ k ∈ Finset.range N, a k • haarBasis 𝕜 p hp k) =
      ∑ k ∈ Finset.range N, L (a k) • haarBasis ℝ p hp k := by
  refine Lp.ext ?_
  filter_upwards [L.coeFn_compLpL (∑ k ∈ Finset.range N, a k • haarBasis 𝕜 p hp k),
    coeFn_sum_haarBasis hp a N, coeFn_sum_haarBasis hp (fun k => L (a k)) N] with x h1 h2 h3
  rw [h1, h2, h3, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← Algebra.smul_def, L.map_smul, RCLike.ofReal_real_eq_id, id_eq, smul_eq_mul,
    mul_comm]

/-- **Sign-transform bound for the Haar basis of `Lᵖ([0, 1]; 𝕜)` (`1 < p < ∞`).** For `1 < p < ∞`
and signs `|ε k| = 1`, signed Haar partial sums in `Lᵖ(I; 𝕜)` satisfy
`‖∑_{k < N} ε_k c_k h_k‖_p ≤ 2 * (max p (p / (p - 1)) - 1) * ‖∑_{k < N} c_k h_k‖_p`. -/
theorem norm_sum_signed_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (c : ℕ → 𝕜) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, ((ε k : 𝕜) * c k) • haarBasis 𝕜 p hp k‖ ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
        ‖∑ k ∈ Finset.range N, c k • haarBasis 𝕜 p hp k‖ := by
  set C := max p.toReal (p.toReal / (p.toReal - 1)) - 1
  have hC0 : 0 ≤ C := zero_le_one.trans (one_le_haarRealBound hp1 hp)
  let reLp := (RCLike.reCLM (K := 𝕜)).compLpL p (volume : Measure I)
  let imLp := (RCLike.imCLM (K := 𝕜)).compLpL p (volume : Measure I)
  set f : Lp 𝕜 p (volume : Measure I) := ∑ k ∈ Finset.range N, c k • haarBasis 𝕜 p hp k
  set g : Lp 𝕜 p (volume : Measure I) :=
    ∑ k ∈ Finset.range N, ((ε k : 𝕜) * c k) • haarBasis 𝕜 p hp k
  have hre_le : ‖reLp f‖ ≤ ‖f‖ := Lp.norm_le_norm_of_ae_le <|
    ((RCLike.reCLM (K := 𝕜)).coeFn_compLpL f).mono fun x hx => by
      rw [hx, RCLike.reCLM_apply]
      exact RCLike.norm_re_le_norm (f x)
  have him_le : ‖imLp f‖ ≤ ‖f‖ := Lp.norm_le_norm_of_ae_le <|
    ((RCLike.imCLM (K := 𝕜)).coeFn_compLpL f).mono fun x hx => by
      rw [hx, RCLike.imCLM_apply]
      exact RCLike.norm_im_le_norm (f x)
  have hg_le : ‖g‖ ≤ 1 * ‖reLp g‖ + 1 * ‖imLp g‖ := by
    refine Lp.norm_le_add_of_ae_norm_le zero_le_one zero_le_one ?_
    filter_upwards [(RCLike.reCLM (K := 𝕜)).coeFn_compLpL g,
      (RCLike.imCLM (K := 𝕜)).coeFn_compLpL g] with x hre him
    rw [hre, him, RCLike.reCLM_apply, RCLike.imCLM_apply, one_mul, one_mul,
      Real.norm_eq_abs, Real.norm_eq_abs]
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [RCLike.norm_sq_eq_def]
    nlinarith [abs_nonneg (RCLike.re (g x)), abs_nonneg (RCLike.im (g x)),
      sq_abs (RCLike.re (g x)), sq_abs (RCLike.im (g x))]
  have hre_g : ‖reLp g‖ ≤ C * ‖f‖ := by
    rw [compLpL_sum_haarBasis hp (RCLike.reCLM (K := 𝕜))]
    simp_rw [RCLike.reCLM_apply, ← Algebra.smul_def, RCLike.smul_re]
    exact (norm_sum_signed_haarBasis_real_le hp1 hp _ hε N).trans
      (mul_le_mul_of_nonneg_left
        (compLpL_sum_haarBasis hp (RCLike.reCLM (K := 𝕜)) c N ▸ hre_le) hC0)
  have him_g : ‖imLp g‖ ≤ C * ‖f‖ := by
    rw [compLpL_sum_haarBasis hp (RCLike.imCLM (K := 𝕜))]
    simp_rw [RCLike.imCLM_apply, ← Algebra.smul_def, RCLike.smul_im]
    exact (norm_sum_signed_haarBasis_real_le hp1 hp _ hε N).trans
      (mul_le_mul_of_nonneg_left
        (compLpL_sum_haarBasis hp (RCLike.imCLM (K := 𝕜)) c N ▸ him_le) hC0)
  linarith

/-- Every finite signed coordinate multiplier of the real Haar basis on `Lᵖ(I)` (`1 < p < ∞`) has
norm at most `max p.toReal (p.toReal / (p.toReal - 1)) - 1`. -/
theorem norm_sum_signed_coord_haarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (A : Finset ℕ) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1)
    (f : Lp ℝ p (volume : Measure I)) :
    ‖∑ k ∈ A, ε k • (haarBasis ℝ p hp).coord k f • haarBasis ℝ p hp k‖ ≤
      (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖f‖ := by
  refine (haarBasis ℝ p hp).norm_sum_signed_coord_smul_le_of_range (fun N δ hδ g => ?_) A hε f
  simp only [RCLike.ofReal_real_eq_id, id_eq, smul_smul]
  calc
    ‖∑ k ∈ Finset.range N, (δ k * (haarBasis ℝ p hp).coord k g) • haarBasis ℝ p hp k‖
        ≤ (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
            ‖∑ k ∈ Finset.range N, (haarBasis ℝ p hp).coord k g • haarBasis ℝ p hp k‖ :=
          norm_sum_signed_haarBasis_real_le hp1 hp _ hδ N
    _ = (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖dyadicProj ℝ p N g‖ := by
          rw [← SchauderBasis.proj_apply, haarBasis_proj]
    _ ≤ (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖g‖ := by
          have : 0 ≤ max p.toReal (p.toReal / (p.toReal - 1)) - 1 :=
            zero_le_one.trans (one_le_haarRealBound hp1 hp)
          gcongr
          simpa using (dyadicProj ℝ p N).le_of_opNorm_le (norm_dyadicProj_le ℝ p N) g

/-- Every finite coordinate projection of the real Haar basis on `Lᵖ(I)` (`1 < p < ∞`) has operator
norm at most `max p.toReal (p.toReal / (p.toReal - 1)) - 1`. -/
theorem norm_proj_haarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis ℝ p hp) A‖ ≤
      max p.toReal (p.toReal / (p.toReal - 1)) - 1 :=
  (haarBasis ℝ p hp).norm_proj_finset_le_of_range_signed
    (zero_le_one.trans (one_le_haarRealBound hp1 hp))
    (fun N _ hδ g => by
      simpa using norm_sum_signed_coord_haarBasis_real_le hp1 hp (Finset.range N) hδ g) A

/-- Every finite signed coordinate multiplier of the Haar basis on `Lᵖ(I; 𝕜)` (`1 < p < ∞`) has
norm at most `2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1)`. -/
theorem norm_sum_signed_coord_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (A : Finset ℕ) {ε : ℕ → ℝ} (hε : ∀ k, |ε k| = 1)
    (f : Lp 𝕜 p (volume : Measure I)) :
    ‖∑ k ∈ A, (ε k : 𝕜) • (haarBasis 𝕜 p hp).coord k f • haarBasis 𝕜 p hp k‖ ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖f‖ := by
  refine (haarBasis 𝕜 p hp).norm_sum_signed_coord_smul_le_of_range (fun N δ hδ g => ?_) A hε f
  simp only [smul_smul]
  calc
    ‖∑ k ∈ Finset.range N, ((δ k : 𝕜) * (haarBasis 𝕜 p hp).coord k g) • haarBasis 𝕜 p hp k‖
        ≤ 2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
            ‖∑ k ∈ Finset.range N, (haarBasis 𝕜 p hp).coord k g • haarBasis 𝕜 p hp k‖ :=
          norm_sum_signed_haarBasis_le hp1 hp _ hδ N
    _ = 2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖dyadicProj 𝕜 p N g‖ := by
          rw [← SchauderBasis.proj_apply, haarBasis_proj]
    _ ≤ 2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) * ‖g‖ := by
          have : 0 ≤ 2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) :=
            mul_nonneg zero_le_two (zero_le_one.trans (one_le_haarRealBound hp1 hp))
          gcongr
          simpa using (dyadicProj 𝕜 p N).le_of_opNorm_le (norm_dyadicProj_le 𝕜 p N) g

/-- Every finite coordinate projection of the Haar basis on `Lᵖ(I; 𝕜)` (`1 < p < ∞`) has operator
norm at most `2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1)`. -/
theorem norm_proj_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis 𝕜 p hp) A‖ ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) :=
  (haarBasis 𝕜 p hp).norm_proj_finset_le_of_range_signed
    (mul_nonneg zero_le_two (zero_le_one.trans (one_le_haarRealBound hp1 hp)))
    (fun N _ hδ g => norm_sum_signed_coord_haarBasis_le hp1 hp (Finset.range N) hδ g) A

/-- **Unconditional convergence of the Haar expansion in `Lᵖ([0, 1]; 𝕜)`**, `1 < p < ∞`. -/
theorem hasSum_haarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) (f : Lp 𝕜 p (volume : Measure I)) :
    HasSum (fun n => (haarBasis 𝕜 p hp).coord n f • haarBasis 𝕜 p hp n) f :=
  (haarBasis 𝕜 p hp).hasSum_of_forall_norm_proj_le (norm_proj_haarBasis_le hp1 hp) f

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **The unconditional Haar basis of `Lᵖ([0, 1]; 𝕜)`**, `1 < p < ∞`: the Haar system
`haarBasis 𝕜 p hp` bundled as an `UnconditionalSchauderBasis`. -/
def haarUnconditionalBasis (hp1 : 1 < p) (hp : p ≠ ∞) :
    UnconditionalSchauderBasis ℕ 𝕜 (Lp 𝕜 p (volume : Measure I)) :=
  (haarBasis 𝕜 p hp).toUnconditionalSchauderBasis (hasSum_haarBasis hp1 hp)

variable {𝕜 p}

/-- Forgetting unconditionality of `haarUnconditionalBasis` recovers `haarBasis`. -/
@[simp]
theorem toSchauderBasis_haarUnconditionalBasis (hp1 : 1 < p) (hp : p ≠ ∞) :
    (haarUnconditionalBasis 𝕜 p hp1 hp).toSchauderBasis = haarBasis 𝕜 p hp := by
  simp [haarUnconditionalBasis]

/-- The `n`-th vector of `haarUnconditionalBasis` is the `Lᵖ` class of `haarFun n`. -/
@[simp]
theorem haarUnconditionalBasis_apply (hp1 : 1 < p) (hp : p ≠ ∞) (n : ℕ) :
    haarUnconditionalBasis 𝕜 p hp1 hp n =
      (memLp_ofReal_haarFun 𝕜 p n).toLp (fun x => (haarFun n x : 𝕜)) := by
  simp [haarUnconditionalBasis]

/-- The `n`-th vector of `haarUnconditionalBasis` is a.e. the Haar function `hₙ`. -/
theorem coeFn_haarUnconditionalBasis (hp1 : 1 < p) (hp : p ≠ ∞) (n : ℕ) :
    haarUnconditionalBasis 𝕜 p hp1 hp n =ᵐ[volume] fun x => (haarFun n x : 𝕜) := by
  simpa [haarUnconditionalBasis] using coeFn_haarBasis (𝕜 := 𝕜) (p := p) hp n

/-- The coordinate functionals of `haarUnconditionalBasis` agree with those of `haarBasis`. -/
@[simp]
theorem haarUnconditionalBasis_coord (hp1 : 1 < p) (hp : p ≠ ∞) :
    (haarUnconditionalBasis 𝕜 p hp1 hp).coord = (haarBasis 𝕜 p hp).coord := by
  simp [haarUnconditionalBasis]

/-- The finite coordinate projections of `haarUnconditionalBasis` agree with those of
`haarBasis`. -/
theorem haarUnconditionalBasis_proj (hp1 : 1 < p) (hp : p ≠ ∞) (A : Finset ℕ) :
    (haarUnconditionalBasis 𝕜 p hp1 hp).proj A =
      GeneralSchauderBasis.proj (haarBasis 𝕜 p hp) A := by
  simp [haarUnconditionalBasis]

/-- The projection of `haarUnconditionalBasis` onto `Finset.range N` is `dyadicProj 𝕜 p N`. -/
@[simp]
theorem haarUnconditionalBasis_proj_range (hp1 : 1 < p) (hp : p ≠ ∞) (N : ℕ) :
    (haarUnconditionalBasis 𝕜 p hp1 hp).proj (Finset.range N) = dyadicProj 𝕜 p N := by
  rw [haarUnconditionalBasis_proj, ← SchauderBasis.proj, haarBasis_proj]

/-- The unconditional basis constant of the real Haar basis of `Lᵖ([0, 1])` (`1 < p < ∞`) is at
most `max p.toReal (p.toReal / (p.toReal - 1)) - 1`. -/
theorem nnNormProjBound_haarUnconditionalBasis_real_le (hp1 : 1 < p) (hp : p ≠ ∞) :
    ((haarUnconditionalBasis ℝ p hp1 hp).nnNormProjBound : ℝ) ≤
      max p.toReal (p.toReal / (p.toReal - 1)) - 1 := by
  refine (haarUnconditionalBasis ℝ p hp1 hp).nnNormProjBound_le fun A => ?_
  rw [haarUnconditionalBasis_proj]
  exact norm_proj_haarBasis_real_le hp1 hp A

/-- The unconditional basis constant of the Haar basis of `Lᵖ([0, 1]; 𝕜)` (`1 < p < ∞`) is at most
`2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1)`. -/
theorem nnNormProjBound_haarUnconditionalBasis_le (hp1 : 1 < p) (hp : p ≠ ∞) :
    ((haarUnconditionalBasis 𝕜 p hp1 hp).nnNormProjBound : ℝ) ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) := by
  refine (haarUnconditionalBasis 𝕜 p hp1 hp).nnNormProjBound_le fun A => ?_
  rw [haarUnconditionalBasis_proj]
  exact norm_proj_haarBasis_le hp1 hp A

/-- On `L²([0, 1]; 𝕜)`, the unconditional Haar basis is suppression-`1` unconditional: its
unconditional basis constant is `1`. -/
@[simp]
theorem nnNormProjBound_haarUnconditionalBasis_two :
    (haarUnconditionalBasis 𝕜 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).nnNormProjBound = 1 := by
  let b := haarUnconditionalBasis 𝕜 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top
  refine le_antisymm ?_ ?_
  · rw [← NNReal.coe_le_coe, NNReal.coe_one]
    refine b.nnNormProjBound_le fun A => ?_
    dsimp only [b]
    rw [haarUnconditionalBasis_proj]
    refine (haarBasis 𝕜 2 ENNReal.ofNat_ne_top).norm_proj_finset_le_of_range_signed zero_le_one
      (fun N δ hδ g => ?_) A
    simp only [smul_smul, one_mul]
    rw [norm_sum_unimodular_haarBasis_two 𝕜 _
      (fun k => by rw [RCLike.norm_ofReal, hδ k]) N, ← SchauderBasis.proj_apply, haarBasis_proj]
    simpa using (dyadicProj 𝕜 2 N).le_of_opNorm_le (norm_dyadicProj_le 𝕜 2 N) g
  · have hproj : 1 ≤ ‖b.proj (Finset.range 1)‖ := by
      have hb0 : 0 < ‖b 0‖ := norm_pos_iff.2 fun h0 => by
        have := b.ortho 0 0
        simp [h0] at this
      have hfix : b.proj (Finset.range 1) (b 0) = b 0 := by
        rw [GeneralSchauderBasis.proj_apply_basis_mem, ite_eq_left (by simp)]
      have hle := (b.proj (Finset.range 1)).le_opNorm (b 0)
      rw [hfix] at hle
      exact (le_mul_iff_one_le_left hb0).1 hle
    exact NNReal.coe_le_coe.1
      (by simpa using hproj.trans (b.norm_proj_le_nnNormProjBound (Finset.range 1)))

end TauCeti.unitInterval
