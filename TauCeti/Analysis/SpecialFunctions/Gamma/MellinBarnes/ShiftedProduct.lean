/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.Contour.Residue.VerticalLineShift
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The Mellin–Barnes integral of `Γ(s) Γ(s + p)`

For `c ∈ Complex.slitPlane`, `p ∉ ℤ`, and any abscissa `σ > max 0 (-Re p)`, the vertical
Mellin–Barnes integral of the shifted Gamma product `Γ(s) Γ(s + p)` evaluates to the linear
combination of regularized hypergeometric functions `₀F₁`:

`(1 / 2π) ∫ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p) dy`
`  = (π / sin (π p)) (₀F₁(; 1 - p; c) - c ^ p · ₀F₁(; 1 + p; c))`.

This is the classical Mellin–Barnes representation of the modified Bessel function `2 c^{p/2}
K_p(2 √c)` (DLMF 10.32.13, written via DLMF 10.27.4 in terms of `I_{±p}` and hence `₀F₁`),
and on positive real arguments `c > 0` it evaluates the inverse Mellin transform
`mellinInv σ (fun s ↦ Γ(s) Γ(s + p)) c`. Together with the Mellin transform of Macdonald's
integral, this yields the integral representation of generalized Airy functions.

## Proof outline

1. **Exponential decay on vertical strips.** Stirling's vertical-strip formula
   (`TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le`) gives `‖Γ(s) Γ(s + p)‖` decaying like
   `e^{-π |Im s|}` uniformly on `Re s ∈ [a, b]`, while `‖c^{-s}‖` grows at most like
   `e^{|arg c| |Im s|}` (`Complex.norm_cpow_le_mul_exp_arg`) with `|arg c| < π` on
   `Complex.slitPlane`. Hence the integrand decays exponentially in `|Im s|` on every vertical
   strip, giving both vertical-line integrability and vanishing horizontal rectangle caps.
2. **Simple-pole residues.** For `p ∉ ℤ`, the poles of `c^{-s} Γ(s) Γ(s + p)` form two disjoint
   simple-pole lattices `-k` and `-p - k` (`k ∈ ℕ`). Euler's reflection formula converts their
   residues into `(π / sin (π p))` times the terms of `₀F₁(; 1 - p; c)` and
   `-c ^ p · ₀F₁(; 1 + p; c)`.
3. **Contour shifting.** `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue` shifts
   the vertical line from `σ₂` to any pole-avoiding abscissa `σ₁ ≤ σ₂`, picking up the finite sum
   of residues over the union of the pole sets in `(σ₁, σ₂)` (valid for all `p : ℂ`, including
   coincident double poles when `p ∈ ℤ`).
4. **Left-tail decay.** Choosing a pole-avoiding offset `δ ∈ (0, 1)` via
   `TauCeti.exists_mem_Ioo_zero_one_sub_ne_intCast` and applying the left-shift Gamma estimate
   `TauCeti.exists_norm_Gamma_sub_natCast_le` at `σ_N = -N - δ` bounds the shifted vertical
   integral by `O(‖c‖ ^ N / N!) → 0` as `N → ∞`, so the partial residue sums converge to the full
   `₀F₁` series.

## Main results

* `Complex.integrable_cpow_neg_mul_Gamma_mul_Gamma_add`: vertical-line integrability of
  `y ↦ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p)` for `c ∈ slitPlane` and pole-avoiding `σ`.
* `Complex.residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat` and
  `Complex.residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat`: the residues at `-k` and
  `-p - k`, together with their Euler-reflection forms matching `regularizedHGFunCoeff`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral_eq_sum_residue`: the raw
  finite contour-shift residue-sum identity between any two pole-avoiding vertical lines `σ₁ ≤ σ₂`,
  valid for arbitrary `p : ℂ` (including integer `p` with double poles).
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral`: the `regularizedHGFunCoeff`
  form of the contour-shift identity for `p ∉ ℤ`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_add`: evaluation of the vertical integral on
  `Complex.slitPlane` for `σ > max 0 (-Re p)` and `p ∉ ℤ`.
* `Complex.mellinInv_Gamma_mul_Gamma_add_eq_regularizedHGFun`: the `mellinInv` form for real
  `c > 0`.

## References

* NIST Digital Library of Mathematical Functions, §§5.5, 5.11, 10.27, 10.32 (equations 10.27.4
  and 10.32.13).
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, §6.5.
-/

public section

noncomputable section

open Real Set MeasureTheory Filter
open scoped Topology Nat
open Complex hiding exp continuous_exp log

namespace Complex

/-! ### Regularity and vertical-strip decay -/

/-- For `c ≠ 0`, the Mellin–Barnes integrand `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` is meromorphic
at every point of `ℂ`. -/
private lemma meromorphicAt_cpow_neg_mul_Gamma_mul_Gamma_add {c p : ℂ} (hc : c ≠ 0) (s : ℂ) :
    MeromorphicAt (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s := by
  have hcpow : (fun z : ℂ ↦ c ^ (-z)) = fun z ↦ Complex.exp (Complex.log c * (-z)) :=
    funext fun z ↦ cpow_def_of_ne_zero hc (-z)
  have h1 : AnalyticAt ℂ (fun z : ℂ ↦ c ^ (-z)) s := by
    rw [hcpow]
    exact (Complex.differentiable_exp.comp
      (differentiable_const _ |>.mul differentiable_id.neg)).analyticAt s
  have h2 : MeromorphicAt Gamma s := by
    have h := (differentiable_one_div_Gamma.analyticAt s).meromorphicAt.inv
    simpa only [Pi.inv_def, inv_inv] using h
  have h3 : MeromorphicAt (fun z ↦ Gamma (z + p)) s := by
    have h := ((differentiable_one_div_Gamma.comp (f := fun z : ℂ ↦ z + p)
      (by fun_prop)).analyticAt s).meromorphicAt.inv
    simpa only [Pi.inv_def, Function.comp_def, inv_inv] using h
  exact h1.meromorphicAt.mul (h2.mul h3)

/-- For `c ≠ 0`, the Mellin–Barnes integrand `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` is complex
differentiable at every `s` avoiding `-ℕ` and `-p - ℕ`. -/
private lemma differentiableAt_cpow_neg_mul_Gamma_mul_Gamma_add {c p s : ℂ} (hc : c ≠ 0)
    (hs : ∀ n : ℕ, s ≠ -n) (hsp : ∀ n : ℕ, s + p ≠ -n) :
    DifferentiableAt ℂ (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s := by
  have hcpow : (fun z : ℂ ↦ c ^ (-z)) = fun z ↦ Complex.exp (Complex.log c * (-z)) :=
    funext fun z ↦ cpow_def_of_ne_zero hc (-z)
  have h1 : DifferentiableAt ℂ (fun z : ℂ ↦ c ^ (-z)) s := by
    rw [hcpow]
    exact (Complex.differentiable_exp.comp
      (differentiable_const _ |>.mul differentiable_id.neg)).differentiableAt
  have h2 : DifferentiableAt ℂ Gamma s := differentiableAt_Gamma s hs
  have h3 : DifferentiableAt ℂ (fun z ↦ Gamma (z + p)) s :=
    (differentiableAt_Gamma (s + p) hsp).comp s (differentiableAt_id.add_const p)
  exact h1.mul (h2.mul h3)

/-- On any vertical strip `Re s ∈ [a, b]` and for any `0 < ε ≤ π`, the shifted Gamma product
`Γ(s) Γ(s + p)` satisfies `‖Γ(s) Γ(s + p)‖ ≤ K * exp (-((π - ε) * |Im s|))` for `|Im s| ≥ Y`. -/
private lemma exists_norm_Gamma_mul_Gamma_add_le_exp (p : ℂ) (a b : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ π) :
    ∃ K Y : ℝ, 0 ≤ K ∧ 0 ≤ Y ∧ ∀ s : ℂ, s.re ∈ Icc a b → Y ≤ |s.im| →
      ‖Gamma s * Gamma (s + p)‖ ≤ K * Real.exp (-((π - ε) * |s.im|)) := by
  set a' : ℝ := min a (a + p.re)
  set b' : ℝ := max b (b + p.re)
  obtain ⟨C, T, hS⟩ := TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le a' b'
  set B : ℝ := max (b' - 1 / 2) 0 + 1
  set δ : ℝ := ε / (2 * B)
  have hB : 0 < B := by positivity
  have hδ : 0 < δ := by positivity
  set K₀ : ℝ := Real.exp (Real.log (2 * π) / 2 + max C 0 - B * Real.log δ)
  have hΓ : ∀ z : ℂ, z.re ∈ Icc a' b' → max T 1 ≤ |z.im| →
      ‖Gamma z‖ ≤ K₀ * Real.exp (-((π / 2 - ε / 2) * |z.im|)) := by
    intro z hz hzim
    have hz1 : 1 ≤ |z.im| := (le_max_right T 1).trans hzim
    have hzpos : 0 < |z.im| := zero_lt_one.trans_le hz1
    have hGz : Gamma z ≠ 0 := Gamma_ne_zero fun n h ↦ hzpos.ne' (by simp [h])
    have hst := (abs_le.mp (hS z hz ((le_max_left T 1).trans hzim))).2
    have hlog_le : Real.log |z.im| ≤ δ * |z.im| - Real.log δ := by
      linarith [Real.log_le_sub_one_of_pos (mul_pos hδ hzpos), Real.log_mul hδ.ne' hzpos.ne']
    have hpow : (z.re - 1 / 2) * Real.log |z.im| ≤ B * (δ * |z.im| - Real.log δ) :=
      (mul_le_mul_of_nonneg_right (by linarith [hz.2, le_max_left (b' - 1 / 2) 0])
        (Real.log_nonneg hz1)).trans (mul_le_mul_of_nonneg_left hlog_le hB.le)
    have hC_le : C / |z.im| ≤ max C 0 :=
      (div_le_div_of_nonneg_right (le_max_left C 0) hzpos.le).trans
        (div_le_self (le_max_right C 0) hz1)
    have hBδ : B * δ = ε / 2 := by simp only [δ]; field_simp
    rw [← Real.exp_log (norm_pos_iff.mpr hGz)]
    simp only [K₀, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hst, hpow, hC_le, hBδ])
  set Y : ℝ := max (max T 1) (max T 1 + |p.im|)
  refine ⟨K₀ * K₀ * Real.exp ((π / 2 - ε / 2) * |p.im|), Y, by positivity,
    le_trans zero_le_one ((le_max_right T 1).trans (le_max_left _ _)), fun s hs hsim ↦ ?_⟩
  have htri : |s.im| - |p.im| ≤ |(s + p).im| := by
    simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub s.im (-p.im)
  have hG1 := hΓ s ⟨(min_le_left _ _).trans hs.1, hs.2.trans (le_max_left _ _)⟩
    ((le_max_left _ _).trans hsim)
  have hG2 := hΓ (s + p)
    ⟨(min_le_right _ _).trans (by simpa using add_le_add_right hs.1 p.re),
      le_trans (by simpa using add_le_add_right hs.2 p.re) (le_max_right _ _)⟩
    (by linarith [(le_max_right (max T 1) _).trans hsim])
  rw [norm_mul]
  calc ‖Gamma s‖ * ‖Gamma (s + p)‖
      ≤ (K₀ * Real.exp (-((π / 2 - ε / 2) * |s.im|))) *
          (K₀ * Real.exp (-((π / 2 - ε / 2) * |(s + p).im|))) := by gcongr
    _ = K₀ * K₀ * Real.exp (-((π / 2 - ε / 2) * (|s.im| + |(s + p).im|))) := by
        rw [mul_mul_mul_comm]; congr 1; rw [← Real.exp_add]; congr 1; ring
    _ ≤ K₀ * K₀ * Real.exp ((π / 2 - ε / 2) * |p.im| + -((π - ε) * |s.im|)) := by
        gcongr; nlinarith [htri, hε']
    _ = K₀ * K₀ * Real.exp ((π / 2 - ε / 2) * |p.im|) * Real.exp (-((π - ε) * |s.im|)) := by
        rw [Real.exp_add]; ring

/-- On any vertical strip `Re s ∈ [a, b]` and for `c ∈ slitPlane`, the integrand
`c ^ (-s) * (Γ(s) * Γ(s + p))` decays exponentially in `|Im s|` at rate `(π - |arg c|) / 2`. -/
private lemma exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_le_exp {c p : ℂ} (hc : c ∈ slitPlane)
    (a b : ℝ) :
    ∃ K Y : ℝ, 0 ≤ K ∧ 0 ≤ Y ∧ ∀ s : ℂ, s.re ∈ Icc a b → Y ≤ |s.im| →
      ‖c ^ (-s) * (Gamma s * Gamma (s + p))‖ ≤
        K * Real.exp (-((π - |c.arg|) / 2 * |s.im|)) := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  have harg : |c.arg| < π :=
    abs_lt.mpr ⟨neg_pi_lt_arg c, lt_of_le_of_ne (arg_le_pi c) (mem_slitPlane_iff_arg.mp hc).1⟩
  set α : ℝ := (π - |c.arg|) / 2
  have hα : 0 < α := half_pos (sub_pos.mpr harg)
  obtain ⟨KΓ, Y, hKΓ, hY, hΓ⟩ :=
    exists_norm_Gamma_mul_Gamma_add_le_exp p a b hα (by simp only [α]; linarith [abs_nonneg c.arg])
  set M_c : ℝ := max (‖c‖ ^ (-a)) (‖c‖ ^ (-b))
  have hM_c : 0 ≤ M_c := le_trans (Real.rpow_nonneg (norm_nonneg c) _) (le_max_left _ _)
  refine ⟨M_c * KΓ, Y, mul_nonneg hM_c hKΓ, hY, fun s hs hsim ↦ ?_⟩
  have hcpow : ‖c ^ (-s)‖ ≤ M_c * Real.exp (|c.arg| * |s.im|) := by
    refine (norm_cpow_le_mul_exp_arg c (-s)).trans ?_
    rw [neg_re, neg_im, abs_neg]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rcases le_total 1 ‖c‖ with h1 | h1
    · exact (Real.rpow_le_rpow_of_exponent_le h1 (neg_le_neg hs.1)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge (norm_pos_iff.mpr hc0) h1
        (neg_le_neg hs.2)).trans (le_max_right _ _)
  rw [norm_mul]
  calc ‖c ^ (-s)‖ * ‖Gamma s * Gamma (s + p)‖
      ≤ (M_c * Real.exp (|c.arg| * |s.im|)) * (KΓ * Real.exp (-((π - α) * |s.im|))) := by
        gcongr; exact hΓ s hs hsim
    _ = M_c * KΓ * Real.exp (|c.arg| * |s.im| + -((π - α) * |s.im|)) := by rw [Real.exp_add]; ring
    _ = M_c * KΓ * Real.exp (-(α * |s.im|)) := by congr 2; simp only [α]; ring

/-- For `c ∈ Complex.slitPlane` and any abscissa `σ` avoiding the poles of `Γ(s)` and `Γ(s + p)`,
the vertical Mellin–Barnes integrand `y ↦ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p)` is
integrable on `ℝ`. -/
theorem integrable_cpow_neg_mul_Gamma_mul_Gamma_add {c p : ℂ} (hc : c ∈ slitPlane)
    {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n) (hσp : ∀ n : ℕ, σ + p.re ≠ -n) :
    Integrable fun y : ℝ ↦
      c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p)) := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  have harg : |c.arg| < π :=
    abs_lt.mpr ⟨neg_pi_lt_arg c, lt_of_le_of_ne (arg_le_pi c) (mem_slitPlane_iff_arg.mp hc).1⟩
  set α : ℝ := (π - |c.arg|) / 2
  have hα : 0 < α := half_pos (sub_pos.mpr harg)
  have hcont : Continuous fun y : ℝ ↦
      c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p)) := by
    refine continuous_iff_continuousAt.mpr fun y ↦ ?_
    exact (differentiableAt_cpow_neg_mul_Gamma_mul_Gamma_add hc0
      (fun n h ↦ hσ n (by simpa using congrArg re h))
      (fun n h ↦ hσp n (by simpa using congrArg re h))).continuousAt.comp (by fun_prop)
  obtain ⟨K, Y, _, _, hK⟩ := exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_le_exp hc σ σ
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcont.continuousOn (s := Icc (-Y) Y))
  set C : ℝ := max K (max M 0 * Real.exp (α * Y))
  refine ((TauCeti.integrable_exp_neg_mul_abs hα).const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  rcases le_total Y |y| with hy | hy
  · refine (hK (σ + y * I) (by simp) (by simpa using hy)).trans ?_
    simpa [α] using mul_le_mul_of_nonneg_right (le_max_left K _) (Real.exp_pos _).le
  · have hMy : ‖c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p))‖ ≤ max M 0 :=
      (hM y (abs_le.mp hy)).trans (le_max_left M 0)
    have hexp : 1 ≤ Real.exp (α * Y) * Real.exp (-(α * |y|)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    calc ‖c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p))‖
        ≤ max M 0 * 1 := by simpa using hMy
      _ ≤ max M 0 * (Real.exp (α * Y) * Real.exp (-(α * |y|))) :=
        mul_le_mul_of_nonneg_left hexp (le_max_right M 0)
      _ = (max M 0 * Real.exp (α * Y)) * Real.exp (-(α * |y|)) := by ring
      _ ≤ C * Real.exp (-(α * |y|)) :=
        mul_le_mul_of_nonneg_right (le_max_right K _) (Real.exp_pos _).le

/-! ### Residues at the two simple-pole lattices -/

/-- The residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at the pole `s = -k` (`k : ℕ`) is
`(-1) ^ k / k! * c ^ k * Γ(p - k)`, whenever `c ≠ 0` and `p - k` is not a nonpositive integer. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat {c p : ℂ} (hc : c ≠ 0) (k : ℕ)
    (hp : ∀ m : ℕ, p - k ≠ -m) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-(k : ℂ)) =
      (-1) ^ k / (k ! : ℂ) * c ^ k * Gamma (p - k) := by
  refine TauCeti.Contour.residue_eq_of_tendsto_sub_mul
    (meromorphicAt_cpow_neg_mul_Gamma_mul_Gamma_add hc _) ?_
  have hcpow : Tendsto (fun s : ℂ ↦ c ^ (-s)) (𝓝[≠] (-(k : ℂ))) (𝓝 (c ^ k)) := by
    have h1 : (fun s : ℂ ↦ c ^ (-s)) = fun s ↦ Complex.exp (Complex.log c * (-s)) :=
      funext fun s ↦ cpow_def_of_ne_zero hc (-s)
    have hcont : Continuous fun s : ℂ ↦ c ^ (-s) := by rw [h1]; fun_prop
    have hval : c ^ (-(-(k : ℂ))) = c ^ k := by rw [neg_neg, cpow_natCast]
    exact hval ▸ hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hΓp : Tendsto (fun s : ℂ ↦ Gamma (s + p)) (𝓝[≠] (-(k : ℂ))) (𝓝 (Gamma (p - k))) := by
    have heq : -(k : ℂ) + p = p - k := by ring
    have hcont : ContinuousAt (fun s : ℂ ↦ Gamma (s + p)) (-(k : ℂ)) :=
      ((differentiableAt_Gamma (-(k : ℂ) + p) (by rwa [heq])).comp (-(k : ℂ))
        (differentiableAt_id.add_const p)).continuousAt
    exact heq ▸ hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine (((tendsto_add_natCast_mul_Gamma k).mul hcpow).mul hΓp).congr fun s ↦ ?_
  rw [sub_neg_eq_add]
  ring

/-- The residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at the pole `s = -p - k` (`k : ℕ`) is
`(-1) ^ k / k! * c ^ (p + k) * Γ(-p - k)`, whenever `-p - k` is not a nonpositive integer. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat {c p : ℂ} (k : ℕ)
    (hp : ∀ m : ℕ, -p - k ≠ -m) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-p - k) =
      (-1) ^ k / (k ! : ℂ) * c ^ (p + k) * Gamma (-p - k) := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hne : -p - k ≠ 0 := by simpa using hp 0
    have hpk : p + k ≠ 0 := fun h ↦ hne (by linear_combination -h)
    have hzero : (fun s : ℂ ↦ (0 : ℂ) ^ (-s) * (Gamma s * Gamma (s + p))) =ᶠ[𝓝[≠] (-p - k)]
        fun _ ↦ 0 := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hne)] with s hs
      simp [zero_cpow (neg_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs))]
    rw [TauCeti.Contour.residue_congr_nhdsNE hzero,
      TauCeti.Contour.residue_eq_zero_of_analyticAt analyticAt_const, zero_cpow hpk]
    simp
  refine TauCeti.Contour.residue_eq_of_tendsto_sub_mul
    (meromorphicAt_cpow_neg_mul_Gamma_mul_Gamma_add hc _) ?_
  have hmap : Tendsto (fun s : ℂ ↦ s + p) (𝓝[≠] (-p - k)) (𝓝[≠] (-(k : ℂ))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hval : (-p - k) + p = -(k : ℂ) := by ring
      exact hval ▸ (continuousAt_id.add continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs h
      exact Set.mem_compl_singleton_iff.mp hs
        (by linear_combination Set.mem_singleton_iff.mp h)
  have hΓp : Tendsto (fun s : ℂ ↦ (s + p + k) * Gamma (s + p))
      (𝓝[≠] (-p - k)) (𝓝 ((-1) ^ k / (k ! : ℂ))) :=
    (tendsto_add_natCast_mul_Gamma k).comp hmap
  have hcpow : Tendsto (fun s : ℂ ↦ c ^ (-s)) (𝓝[≠] (-p - k)) (𝓝 (c ^ (p + k))) := by
    have h1 : (fun s : ℂ ↦ c ^ (-s)) = fun s ↦ Complex.exp (Complex.log c * (-s)) :=
      funext fun s ↦ cpow_def_of_ne_zero hc (-s)
    have hcont : Continuous fun s : ℂ ↦ c ^ (-s) := by rw [h1]; fun_prop
    have hval : c ^ (-(-p - k)) = c ^ (p + k) := by congr 1; ring
    exact hval ▸ hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hΓ : Tendsto Gamma (𝓝[≠] (-p - k)) (𝓝 (Gamma (-p - k))) :=
    (differentiableAt_Gamma (-p - k) hp).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine ((hΓp.mul hcpow).mul hΓ).congr fun s ↦ ?_
  have hsub : s - (-p - k) = s + p + k := by ring
  rw [hsub]
  ring

/-- For `p ∉ ℤ` and `c ≠ 0`, the residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at `s = -k` is
`(π / sin (π * p))` times the `k`-th term of `₀F₁(; 1 - p; c)`. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat_eq_regularizedHGFunCoeff
    {c p : ℂ} (hc : c ≠ 0) (hp : ∀ m : ℤ, p ≠ m) (k : ℕ) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-(k : ℂ)) =
      π / sin (π * p) * (regularizedHGFunCoeff 0 {1 - p} k * c ^ k) := by
  have hp_sub : ∀ m : ℕ, p - k ≠ -m := fun m h ↦
    hp ((k : ℤ) - m) (by push_cast; linear_combination h)
  have h1p : ∀ m : ℕ, 1 - p + k ≠ -m := fun m h ↦
    hp (1 + (k : ℤ) + m) (by push_cast; linear_combination -h)
  have hsin_ne : sin (π * p) ≠ 0 := sin_ne_zero_iff.mpr fun m h ↦
    hp m (mul_left_cancel₀ (ofReal_ne_zero.mpr pi_ne_zero) (by linear_combination h))
  have hΓ1p : Gamma (1 - p + k) ≠ 0 := Gamma_ne_zero h1p
  have hsq : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; simp
  have hrefl : Gamma (p - k) = (-1) ^ k * π / (sin (π * p) * Gamma (1 - p + k)) := by
    have h := Gamma_mul_Gamma_one_sub (p - k)
    have harg : 1 - (p - (k : ℂ)) = 1 - p + k := by ring
    have hsin : sin (π * (p - k)) = (-1) ^ k * sin (π * p) := by
      rw [mul_sub, mul_comm (π : ℂ) (k : ℂ)]
      exact sin_antiperiodic.sub_nat_mul_eq k
    rw [harg, hsin] at h
    have hneg : (-1 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    rw [eq_div_iff (mul_ne_zero hsin_ne hΓ1p)]
    calc Gamma (p - k) * (sin (π * p) * Gamma (1 - p + k))
        = (Gamma (p - k) * Gamma (1 - p + k)) * sin (π * p) := by ring
      _ = (π / ((-1) ^ k * sin (π * p))) * sin (π * p) := by rw [h]
      _ = ((-1) ^ k * (-1) ^ k) * π / (-1) ^ k := by
          rw [hsq, one_mul, div_mul_eq_div_div, div_mul_cancel₀ _ hsin_ne]
      _ = (-1) ^ k * π := by rw [mul_assoc, mul_div_cancel_left₀ _ hneg]
  rw [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat hc k hp_sub, hrefl,
    regularizedHGFunCoeff_zero_singleton]
  have hfac : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  calc (-1) ^ k / ↑k ! * c ^ k * ((-1) ^ k * ↑π / (sin (↑π * p) * Gamma (1 - p + ↑k)))
      = ((-1) ^ k * (-1) ^ k) * (↑π / sin (↑π * p) * ((↑k ! * Gamma (1 - p + ↑k))⁻¹ * c ^ k)) := by
        field_simp [hsin_ne, hΓ1p, hfac]
    _ = ↑π / sin (↑π * p) * ((↑k ! * Gamma (1 - p + ↑k))⁻¹ * c ^ k) := by rw [hsq, one_mul]

/-- For `p ∉ ℤ`, the residue of `s ↦ c ^ (-s) * (Γ(s) * Γ(s + p))` at `s = -p - k` is
`-(π / sin (π * p)) * c ^ p` times the `k`-th term of `₀F₁(; 1 + p; c)`. -/
theorem residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat_eq_regularizedHGFunCoeff
    {c p : ℂ} (hp : ∀ m : ℤ, p ≠ m) (k : ℕ) :
    TauCeti.Contour.residue (fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))) (-p - k) =
      -(π / sin (π * p) * (c ^ p * (regularizedHGFunCoeff 0 {1 + p} k * c ^ k))) := by
  have hp_neg : ∀ m : ℕ, -p - k ≠ -m := fun m h ↦
    hp ((m : ℤ) - k) (by push_cast; linear_combination -h)
  rcases eq_or_ne c 0 with rfl | hc
  · have hp0 : p ≠ 0 := by simpa using hp 0
    have hpk : p + k ≠ 0 := fun h ↦ hp (-k) (by push_cast; linear_combination h)
    rw [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat k hp_neg, zero_cpow hpk, zero_cpow hp0]
    simp
  have h1p : ∀ m : ℕ, 1 + p + k ≠ -m := fun m h ↦
    hp (-(1 + (k : ℤ) + m)) (by push_cast; linear_combination h)
  have hsin_ne : sin (π * p) ≠ 0 := sin_ne_zero_iff.mpr fun m h ↦
    hp m (mul_left_cancel₀ (ofReal_ne_zero.mpr pi_ne_zero) (by linear_combination h))
  have hΓ1p : Gamma (1 + p + k) ≠ 0 := Gamma_ne_zero h1p
  have hsq : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by rw [← mul_pow]; simp
  have hrefl : Gamma (-p - k) = -((-1) ^ k * π / (sin (π * p) * Gamma (1 + p + k))) := by
    have h := Gamma_mul_Gamma_one_sub (-p - k)
    have harg : 1 - (-p - (k : ℂ)) = 1 + p + k := by ring
    have hsin : sin (π * (-p - k)) = -((-1) ^ k * sin (π * p)) := by
      have hneg : (π : ℂ) * (-p - k) = -(π * p + k * π) := by ring
      rw [hneg, sin_neg, sin_antiperiodic.add_nat_mul_eq k]
    rw [harg, hsin] at h
    have hneg : (-1 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
    rw [← neg_div, eq_div_iff (mul_ne_zero hsin_ne hΓ1p)]
    calc Gamma (-p - k) * (sin (π * p) * Gamma (1 + p + k))
        = (Gamma (-p - k) * Gamma (1 + p + k)) * sin (π * p) := by ring
      _ = (π / -((-1) ^ k * sin (π * p))) * sin (π * p) := by rw [h]
      _ = -(((-1) ^ k * (-1) ^ k) * π / (-1) ^ k) := by
          rw [hsq, one_mul, div_neg, neg_mul, div_mul_eq_div_div, div_mul_cancel₀ _ hsin_ne]
      _ = -((-1) ^ k * π) := by rw [mul_assoc, mul_div_cancel_left₀ _ hneg]
  rw [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat k hp_neg, hrefl,
    cpow_add _ _ hc, cpow_natCast, regularizedHGFunCoeff_zero_singleton]
  have hfac : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  calc (-1) ^ k / ↑k ! * (c ^ p * c ^ k) *
          -((-1) ^ k * ↑π / (sin (↑π * p) * Gamma (1 + p + ↑k)))
      = -(((-1) ^ k * (-1) ^ k) *
          (↑π / sin (↑π * p) * (c ^ p * ((↑k ! * Gamma (1 + p + ↑k))⁻¹ * c ^ k)))) := by
        field_simp [hsin_ne, hΓ1p, hfac]
    _ = -(↑π / sin (↑π * p) * (c ^ p * ((↑k ! * Gamma (1 + p + ↑k))⁻¹ * c ^ k))) := by
        rw [hsq, one_mul]

/-! ### Finite contour shift between two vertical lines -/

/-- Exact pole characterization inside an open vertical strip `(σ₁, σ₂)` when both boundary
abscissas avoid `-ℕ` and `-p.re - ℕ`. -/
private lemma exists_open_strip_avoiding_poles {p : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : ∀ n : ℕ, σ₁ ≠ -n) (hσ₁p : ∀ n : ℕ, σ₁ + p.re ≠ -n)
    (hσ₂ : ∀ n : ℕ, σ₂ ≠ -n) (hσ₂p : ∀ n : ℕ, σ₂ + p.re ≠ -n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℂ, σ₁ - ε < s.re → s.re < σ₂ + ε →
      ((∃ k : ℕ, s = -(k : ℂ)) ∨ (∃ k : ℕ, s = -p - k)) →
      s ∈ (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
          (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k) := by
  obtain ⟨ε₁, hε₁, h1⟩ := TauCeti.exists_pos_lt_abs_add_natCast hσ₁
  obtain ⟨ε₂, hε₂, h2⟩ := TauCeti.exists_pos_lt_abs_add_natCast hσ₂
  obtain ⟨ε₃, hε₃, h3⟩ := TauCeti.exists_pos_lt_abs_add_natCast hσ₁p
  obtain ⟨ε₄, hε₄, h4⟩ := TauCeti.exists_pos_lt_abs_add_natCast hσ₂p
  set ε : ℝ := min (min ε₁ ε₂) (min ε₃ ε₄)
  have hIco : ∀ {x₁ x₂ e₁ e₂ : ℝ} (k : ℕ), ε ≤ e₁ → ε ≤ e₂ →
      (∀ n : ℕ, e₁ < |x₁ + n|) → (∀ n : ℕ, e₂ < |x₂ + n|) →
      x₁ - ε < -(k : ℝ) → -(k : ℝ) < x₂ + ε → k ∈ Finset.Ico ⌈-x₂⌉₊ ⌈-x₁⌉₊ := by
    intro x₁ x₂ e₁ e₂ k he₁ he₂ hx₁ hx₂ hl hu
    refine TauCeti.mem_Ico_ceil_neg_iff.mpr ⟨?_, ?_⟩
    · rcases lt_or_ge (x₁ + k) 0 with h | h
      · linarith
      · have := hx₁ k; rw [abs_of_nonneg h] at this; linarith
    · rcases lt_or_ge (x₂ + k) 0 with h | h
      · have := hx₂ k; rw [abs_of_neg h] at this; linarith
      · linarith
  refine ⟨ε, lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), fun s hs1 hs2 hpole ↦ ?_⟩
  rcases hpole with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hIco k
      ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _))
      h1 h2 (by simpa using hs1) (by simpa using hs2), rfl⟩)
  · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hIco k
      ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
      h3 h4 (by simp only [sub_re, neg_re, natCast_re] at hs1; linarith)
      (by simp only [sub_re, neg_re, natCast_re] at hs2; linarith), rfl⟩)

/-- Horizontal rectangle caps `∫_{σ₁}^{σ₂} f(x ± i T) dx` tend to `0` as `T → ∞`. -/
private lemma tendsto_horizontal_cpow_neg_mul_Gamma_mul_Gamma_add
    {c p : ℂ} (hc : c ∈ slitPlane) (σ₁ σ₂ : ℝ) (sgn : ℝ) (hsgn : |sgn| = 1) :
    Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₁..σ₂,
        c ^ (-(x + (sgn * T : ℝ) * I)) *
          (Gamma (x + (sgn * T : ℝ) * I) * Gamma (x + (sgn * T : ℝ) * I + p)))
      atTop (𝓝 0) := by
  have harg : |c.arg| < π :=
    abs_lt.mpr ⟨neg_pi_lt_arg c, lt_of_le_of_ne (arg_le_pi c) (mem_slitPlane_iff_arg.mp hc).1⟩
  set α : ℝ := (π - |c.arg|) / 2
  have hα : 0 < α := half_pos (sub_pos.mpr harg)
  obtain ⟨K, Y, _, _, hK⟩ :=
    exists_norm_cpow_neg_mul_Gamma_mul_Gamma_add_le_exp hc (min σ₁ σ₂) (max σ₁ σ₂)
  have hlim : Tendsto (fun T : ℝ ↦ K * Real.exp (-(α * T)) * |σ₂ - σ₁|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ ↦ Real.exp (-(α * T))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hα))
    simpa using (h1.const_mul K).mul_const |σ₂ - σ₁|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (max Y 0)] with T hT
  have hT0 : 0 ≤ T := (le_max_right Y 0).trans hT
  have hTY : Y ≤ |sgn * T| := by
    rw [abs_mul, hsgn, one_mul, abs_of_nonneg hT0]
    exact (le_max_left Y 0).trans hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx ↦ ?_
  have hx' : (↑x + ↑(sgn * T) * I : ℂ).re ∈ Icc (min σ₁ σ₂) (max σ₁ σ₂) := by
    simpa [Set.uIcc] using Set.uIoc_subset_uIcc hx
  simpa [α, abs_mul, hsgn, abs_of_nonneg hT0] using
    hK (↑x + ↑(sgn * T) * I) hx' (by simpa using hTY)

/-- Evaluation of the finite residue sum over the two disjoint pole families in `(σ₁, σ₂)`. -/
private lemma sum_residue_strip_cpow_neg_mul_Gamma_mul_Gamma_add
    {c p : ℂ} (hc : c ≠ 0) (hp : ∀ m : ℤ, p ≠ m) (σ₁ σ₂ : ℝ) :
    ∑ s ∈ (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
        (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k),
        TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s =
      π / sin (π * p) *
        ((∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k) -
          c ^ p * ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
            regularizedHGFunCoeff 0 {1 + p} k * c ^ k) := by
  have hdisj : Disjoint
      ((Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)))
      ((Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k)) := by
    rw [Finset.disjoint_left]
    intro s hs1 hs2
    rcases Finset.mem_image.mp hs1 with ⟨k₁, _, rfl⟩
    rcases Finset.mem_image.mp hs2 with ⟨k₂, _, hk⟩
    exact hp ((k₁ : ℤ) - k₂) (by push_cast; linear_combination -hk)
  have hinj1 : Function.Injective (fun k : ℕ ↦ -(k : ℂ)) := fun _ _ h ↦
    Nat.cast_injective (neg_inj.mp h)
  have hinj2 : Function.Injective (fun k : ℕ ↦ -p - (k : ℂ)) := fun _ _ h ↦
    Nat.cast_injective (by linear_combination -h)
  rw [Finset.sum_union hdisj, Finset.sum_image (fun _ _ _ _ h ↦ hinj1 h),
    Finset.sum_image (fun _ _ _ _ h ↦ hinj2 h)]
  have hsum1 : ∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊,
      TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) (-(k : ℂ)) =
      π / sin (π * p) *
        ∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦
      residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat_eq_regularizedHGFunCoeff hc hp k
  have hsum2 : ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
      TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) (-p - k) =
      -(π / sin (π * p) * (c ^ p *
        ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
          regularizedHGFunCoeff 0 {1 + p} k * c ^ k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ ↦
      residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat_eq_regularizedHGFunCoeff hp k
  rw [hsum1, hsum2]
  ring

/-- **Raw finite contour shift for `Γ(s) Γ(s + p)`.** For `c ∈ Complex.slitPlane`, arbitrary
`p : ℂ` (including integers, where double poles can occur), and any two pole-avoiding abscissas
`σ₁ ≤ σ₂`, the difference of the vertical integrals along `Re s = σ₂` and `Re s = σ₁` equals
`2π` times the sum of residues of `c ^ (-s) * (Γ(s) * Γ(s + p))` over the union of the pole
sets in the open strip `(σ₁, σ₂)`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral_eq_sum_residue
    {c p : ℂ} (hc : c ∈ slitPlane) {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (hσ₁ : ∀ n : ℕ, σ₁ ≠ -n) (hσ₁p : ∀ n : ℕ, σ₁ + p.re ≠ -n)
    (hσ₂ : ∀ n : ℕ, σ₂ ≠ -n) (hσ₂p : ∀ n : ℕ, σ₂ + p.re ≠ -n) :
    (∫ y : ℝ, c ^ (-(σ₂ + y * I)) * (Gamma (σ₂ + y * I) * Gamma (σ₂ + y * I + p))) -
      (∫ y : ℝ, c ^ (-(σ₁ + y * I)) * (Gamma (σ₁ + y * I) * Gamma (σ₁ + y * I + p))) =
        2 * π * ∑ s ∈
          (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
          (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k),
            TauCeti.Contour.residue (fun z ↦ c ^ (-z) * (Gamma z * Gamma (z + p))) s := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  set f : ℂ → ℂ := fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))
  set P : Finset ℂ :=
    (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
    (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k)
  obtain ⟨ε, _, hstrip_poles⟩ := exists_open_strip_avoiding_poles hσ₁ hσ₁p hσ₂ hσ₂p
  set U : Set ℂ := {s : ℂ | σ₁ - ε < s.re ∧ s.re < σ₂ + ε}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hP : ∀ s ∈ P, σ₁ < s.re ∧ s.re < σ₂ := fun s hs ↦ by
    simp only [P, Finset.mem_union, Finset.mem_image] at hs
    rcases hs with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · obtain ⟨h1, h2⟩ := TauCeti.mem_Ico_ceil_neg_iff.mp hk
      exact ⟨by simpa using h1, by simpa using lt_of_le_of_ne h2 (hσ₂ k).symm⟩
    · obtain ⟨h1, h2⟩ := TauCeti.mem_Ico_ceil_neg_iff.mp hk
      simp only [sub_re, neg_re, natCast_re]
      exact ⟨by linarith, lt_of_le_of_ne (by linarith) (fun h ↦ hσ₂p k (by linarith))⟩
  have hdiff : DifferentiableOn ℂ f (U \ (↑P : Set ℂ)) := fun s ⟨hsU, hsP⟩ ↦
    (differentiableAt_cpow_neg_mul_Gamma_mul_Gamma_add hc0
      (fun k hk ↦ hsP (Finset.mem_coe.mpr (hstrip_poles s hsU.1 hsU.2 (Or.inl ⟨k, hk⟩))))
      (fun k hk ↦ hsP (Finset.mem_coe.mpr (hstrip_poles s hsU.1 hsU.2
        (Or.inr ⟨k, by linear_combination hk⟩))))).differentiableWithinAt
  have htop : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₁..σ₂, f (x + (T : ℝ) * I)) atTop (𝓝 0) := by
    simpa [f] using tendsto_horizontal_cpow_neg_mul_Gamma_mul_Gamma_add hc σ₁ σ₂ 1 (by norm_num)
  have hbot : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₁..σ₂, f (x + (T : ℝ) * I)) atBot (𝓝 0) := by
    simpa [f, Function.comp_def] using
      (tendsto_horizontal_cpow_neg_mul_Gamma_mul_Gamma_add (p := p) hc σ₁ σ₂ (-1)
        (by norm_num)).comp tendsto_neg_atBot_atTop
  exact TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue f hσ hU
    (fun t ⟨ht1, ht2⟩ ↦ ⟨by linarith, by linarith⟩) P hP hdiff
    (fun s _ ↦ meromorphicAt_cpow_neg_mul_Gamma_mul_Gamma_add hc0 s)
    (integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc hσ₂ hσ₂p)
    (integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc hσ₁ hσ₁p) htop hbot

/-- **Finite contour shift for `Γ(s) Γ(s + p)`.** For `c ∈ Complex.slitPlane`, `p ∉ ℤ`, and any
two pole-avoiding abscissas `σ₁ ≤ σ₂`, the difference of the vertical integrals along `Re s = σ₂`
and `Re s = σ₁` equals `2π` times the sum of residues of `c ^ (-s) * (Γ(s) * Γ(s + p))` at the
poles in the open strip `(σ₁, σ₂)`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral
    {c p : ℂ} (hc : c ∈ slitPlane) (hp : ∀ m : ℤ, p ≠ m)
    {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (hσ₁ : ∀ n : ℕ, σ₁ ≠ -n) (hσ₁p : ∀ n : ℕ, σ₁ + p.re ≠ -n)
    (hσ₂ : ∀ n : ℕ, σ₂ ≠ -n) (hσ₂p : ∀ n : ℕ, σ₂ + p.re ≠ -n) :
    (∫ y : ℝ, c ^ (-(σ₂ + y * I)) * (Gamma (σ₂ + y * I) * Gamma (σ₂ + y * I + p))) -
      (∫ y : ℝ, c ^ (-(σ₁ + y * I)) * (Gamma (σ₁ + y * I) * Gamma (σ₁ + y * I + p))) =
        2 * π * (π / sin (π * p) *
          ((∑ k ∈ Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k) -
            c ^ p * ∑ k ∈ Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊,
              regularizedHGFunCoeff 0 {1 + p} k * c ^ k)) := by
  rw [integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral_eq_sum_residue hc hσ hσ₁ hσ₁p hσ₂ hσ₂p,
    sum_residue_strip_cpow_neg_mul_Gamma_mul_Gamma_add (slitPlane_ne_zero hc) hp σ₁ σ₂]

/-! ### Vanishing of the shifted vertical integral as `Re s → -∞` -/

/-- For a fixed pole-avoiding offset `δ ∈ (0, 1)`, the vertical integral along `Re s = -N - δ`
tends to `0` as `N → ∞`, with bound `O(‖c‖ ^ N / N!)`. -/
private lemma tendsto_integral_cpow_neg_mul_Gamma_mul_Gamma_add_left
    {c p : ℂ} (hc : c ∈ slitPlane) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hδ_int : ∀ m : ℤ, -(δ : ℝ) ≠ m) (hpδ : ∀ m : ℤ, p.re - δ ≠ m) :
    Tendsto (fun N : ℕ ↦ ∫ y : ℝ,
        c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
          (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p)))
      atTop (𝓝 0) := by
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  set α : ℝ := π - |c.arg|
  have hα : 0 < α := sub_pos.mpr
    (abs_lt.mpr ⟨neg_pi_lt_arg c, lt_of_le_of_ne (arg_le_pi c) (mem_slitPlane_iff_arg.mp hc).1⟩)
  obtain ⟨C₁, hC₁, hG₁⟩ := TauCeti.exists_norm_Gamma_sub_natCast_le hδ_int
  obtain ⟨C₂, hC₂, hG₂⟩ := TauCeti.exists_norm_Gamma_sub_natCast_le hpδ
  have hceil₀ : ⌈-δ⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith [hδ.1])
  set M : ℕ := ⌈p.re - δ⌉₊
  set C₀ : ℝ := ‖c‖ ^ δ * (C₁ * (C₂ * Real.exp (π * |p.im| / 2)))
  refine squeeze_zero_norm' ?_ (by simpa using
    ((Real.summable_pow_div_factorial ‖c‖).tendsto_atTop_zero.const_mul C₀).mul_const (2 / α))
  filter_upwards [eventually_ge_atTop M] with N hMN
  have hpt : ∀ y : ℝ,
      ‖c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
          (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p))‖ ≤
        C₀ * (‖c‖ ^ N / (N ! : ℝ)) * Real.exp (-(α * |y|)) := fun y ↦ by
    set s : ℂ := ((-(N : ℝ) - δ : ℝ) : ℂ) + y * I
    have hcpow : ‖c ^ (-s)‖ ≤ ‖c‖ ^ δ * ‖c‖ ^ N * Real.exp (|c.arg| * |y|) := by
      refine (norm_cpow_le_mul_exp_arg c (-s)).trans_eq ?_
      have hre : (-s).re = δ + (N : ℝ) := by simp [s]
      have him : |(-s).im| = |y| := by simp [s]
      rw [hre, him, Real.rpow_add (norm_pos_iff.mpr hc0), Real.rpow_natCast]
    have hb₁ : ‖Gamma s‖ ≤ C₁ / (N ! : ℝ) * Real.exp (-(π * |y| / 2)) := by
      have h := hG₁ (N := N) (hceil₀ ▸ Nat.zero_le N) y
      rw [hceil₀, Nat.sub_zero] at h
      refine h.trans_eq' (congrArg (fun z ↦ ‖Gamma z‖) ?_)
      apply Complex.ext
      · simp [s]; ring
      · simp [s]
    have hb₂ : ‖Gamma (s + p)‖ ≤
        C₂ * Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2)) := by
      have h := hG₂ hMN (y + p.im)
      have hfac1 : (1 : ℝ) ≤ (Nat.factorial (N - M) : ℝ) :=
        by exact_mod_cast Nat.factorial_pos (N - M)
      have htri : |y| - |p.im| ≤ |y + p.im| := by
        simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub y (-p.im)
      have hexp_tri : Real.exp (-(π * |y + p.im| / 2)) ≤
          Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by nlinarith [pi_pos, htri])
      have harg : ((p.re - δ : ℝ) : ℂ) - N + (y + p.im : ℝ) * I = s + p := by
        apply Complex.ext
        · simp [s]; ring
        · simp [s]
      rw [harg] at h
      calc ‖Gamma (s + p)‖
          ≤ C₂ / (Nat.factorial (N - M) : ℝ) * Real.exp (-(π * |y + p.im| / 2)) := h
        _ ≤ C₂ * (Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2))) :=
            mul_le_mul (div_le_self hC₂.le hfac1) hexp_tri (Real.exp_pos _).le hC₂.le
        _ = C₂ * Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2)) := by ring
    have hexp_y : Real.exp (|c.arg| * |y|) *
          (Real.exp (-(π * |y| / 2)) * Real.exp (-(π * |y| / 2))) =
        Real.exp (-(α * |y|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [α]
      ring
    rw [norm_mul, norm_mul]
    calc ‖c ^ (-s)‖ * (‖Gamma s‖ * ‖Gamma (s + p)‖)
        ≤ (‖c‖ ^ δ * ‖c‖ ^ N * Real.exp (|c.arg| * |y|)) *
            ((C₁ / (N ! : ℝ) * Real.exp (-(π * |y| / 2))) *
              (C₂ * Real.exp (π * |p.im| / 2) * Real.exp (-(π * |y| / 2)))) := by gcongr
      _ = C₀ * (‖c‖ ^ N / (N ! : ℝ)) *
            (Real.exp (|c.arg| * |y|) *
              (Real.exp (-(π * |y| / 2)) * Real.exp (-(π * |y| / 2)))) := by
          simp only [C₀]; ring
      _ = C₀ * (‖c‖ ^ N / (N ! : ℝ)) * Real.exp (-(α * |y|)) := by rw [hexp_y]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono
    ((integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc
      (fun n h ↦ hδ_int ((N : ℤ) - n) (by push_cast; linarith))
      (fun n h ↦ hpδ ((N : ℤ) - n) (by push_cast; linarith))).norm)
    ((TauCeti.integrable_exp_neg_mul_abs hα).const_mul _) hpt).trans_eq ?_)
  rw [integral_const_mul, TauCeti.integral_exp_neg_mul_abs hα]

/-! ### Main Mellin–Barnes evaluation -/

/-- **Mellin–Barnes integral of `Γ(s) Γ(s + p)` on the slit plane.** For `c ∈ Complex.slitPlane`,
`p ∉ ℤ`, and any abscissa `σ` with `0 < σ` and `0 < σ + Re p`,
`∫ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p) dy` equals
`2π (π / sin (π p)) (₀F₁(; 1 - p; c) - c ^ p · ₀F₁(; 1 + p; c))`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_add
    {c p : ℂ} (hc : c ∈ slitPlane) (hp : ∀ m : ℤ, p ≠ m)
    {σ : ℝ} (hσ : 0 < σ) (hσp : 0 < σ + p.re) :
    ∫ y : ℝ, c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p)) =
      2 * π * (π / sin (π * p) *
        (regularizedHGFun 0 {1 - p} c - c ^ p * regularizedHGFun 0 {1 + p} c)) := by
  obtain ⟨δ, hδ, hpδ⟩ := TauCeti.exists_mem_Ioo_zero_one_sub_ne_intCast p.re
  have hδ_int : ∀ m : ℤ, -(δ : ℝ) ≠ m := fun m hm ↦ by
    have h1 : (m : ℤ) < 0 := by exact_mod_cast (by linarith [hδ.1] : (m : ℝ) < 0)
    have h2 : (-1 : ℤ) < m := by exact_mod_cast (by linarith [hδ.2] : (-1 : ℝ) < m)
    omega
  set Iσ : ℂ := ∫ y : ℝ, c ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (σ + y * I + p))
  set IN : ℕ → ℂ := fun N ↦
    ∫ y : ℝ, c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
      (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p))
  have hshift : ∀ N : ℕ, Iσ - IN N =
      2 * π * (π / sin (π * p) *
        ((∑ k ∈ Finset.range ⌈-(-(N : ℝ) - δ)⌉₊, regularizedHGFunCoeff 0 {1 - p} k * c ^ k) -
          c ^ p * ∑ k ∈ Finset.range ⌈-((-(N : ℝ) - δ) + p.re)⌉₊,
            regularizedHGFunCoeff 0 {1 + p} k * c ^ k)) := by
    intro N
    have h := integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral hc hp
      (by linarith [N.cast_nonneg (α := ℝ), hδ.1] : -(N : ℝ) - δ ≤ σ)
      (fun n h ↦ hδ_int ((N : ℤ) - n) (by push_cast; linarith))
      (fun n h ↦ hpδ ((N : ℤ) - n) (by push_cast; linarith))
      (fun n h ↦ by linarith [n.cast_nonneg (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg (α := ℝ)])
    have hc1 : ⌈-σ⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
    have hc2 : ⌈-(σ + p.re)⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
    simpa only [Iσ, IN, hc1, hc2, Nat.Ico_zero_eq_range] using h
  have hceil_atTop : ∀ a : ℝ, Tendsto (fun N : ℕ ↦ ⌈(N : ℝ) + a⌉₊) atTop atTop := fun a ↦
    tendsto_nat_ceil_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsum1 : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range ⌈-(-(N : ℝ) - δ)⌉₊,
        regularizedHGFunCoeff 0 {1 - p} k * c ^ k)
      atTop (𝓝 (regularizedHGFun 0 {1 - p} c)) := by
    have ht1 : Tendsto (fun N : ℕ ↦ ⌈-(-(N : ℝ) - δ)⌉₊) atTop atTop := by
      convert hceil_atTop δ using 3 with N; ring
    exact (hasSum_regularizedHGFun (a := 0) (b := {1 - p}) (by simp) c).tendsto_sum_nat.comp ht1
  have hsum2 : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.range ⌈-((-(N : ℝ) - δ) + p.re)⌉₊,
        regularizedHGFunCoeff 0 {1 + p} k * c ^ k)
      atTop (𝓝 (regularizedHGFun 0 {1 + p} c)) := by
    have ht2 : Tendsto (fun N : ℕ ↦ ⌈-((-(N : ℝ) - δ) + p.re)⌉₊) atTop atTop := by
      convert hceil_atTop (δ - p.re) using 3 with N; ring
    exact (hasSum_regularizedHGFun (a := 0) (b := {1 + p}) (by simp) c).tendsto_sum_nat.comp ht2
  have hlim_lhs : Tendsto (fun N : ℕ ↦ Iσ - IN N) atTop (𝓝 Iσ) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub
      (tendsto_integral_cpow_neg_mul_Gamma_mul_Gamma_add_left hc hδ hδ_int hpδ)
  have hlim_rhs : Tendsto (fun N : ℕ ↦ Iσ - IN N) atTop
      (𝓝 (2 * π * (π / sin (π * p) *
        (regularizedHGFun 0 {1 - p} c - c ^ p * regularizedHGFun 0 {1 + p} c)))) := by
    simpa only [← hshift] using
      ((hsum1.sub (hsum2.const_mul (c ^ p))).const_mul (π / sin (π * p))).const_mul (2 * (π : ℂ))
  exact tendsto_nhds_unique hlim_lhs hlim_rhs

/-- **Mellin inversion of `Γ(s) Γ(s + p)` as a regularized hypergeometric difference.** For
`p ∉ ℤ`, `0 < σ`, `0 < σ + Re p`, and real `c > 0`,
`mellinInv σ (fun s ↦ Γ(s) Γ(s + p)) c` equals
`(π / sin (π p)) (₀F₁(; 1 - p; c) - c ^ p · ₀F₁(; 1 + p; c))`. -/
theorem mellinInv_Gamma_mul_Gamma_add_eq_regularizedHGFun
    {p : ℂ} (hp : ∀ m : ℤ, p ≠ m)
    {σ : ℝ} (hσ : 0 < σ) (hσp : 0 < σ + p.re)
    {c : ℝ} (hc : 0 < c) :
    mellinInv σ (fun s ↦ Gamma s * Gamma (s + p)) c =
      π / sin (π * p) *
        (regularizedHGFun 0 {1 - p} c - (c : ℂ) ^ p * regularizedHGFun 0 {1 + p} c) := by
  have h := integral_cpow_neg_mul_Gamma_mul_Gamma_add (ofReal_mem_slitPlane.mpr hc) hp hσ hσp
  rw [mellinInv, real_smul]
  simp_rw [smul_eq_mul]
  rw [h]
  have hpi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)
  push_cast
  field_simp [hpi]

end Complex

end
