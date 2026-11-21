/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Residue.Cycle
import TauCeti.Analysis.Contour.Residue.SimplePole
import TauCeti.Analysis.Contour.Winding.Number.Rectangle
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds
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
   `e^{|arg c| |Im s|}` with `|arg c| < π` on `Complex.slitPlane`. Hence the integrand decays
   exponentially in `|Im s|` on every vertical strip, giving both vertical-line integrability
   and vanishing horizontal rectangle caps.
2. **Simple-pole residues.** For `p ∉ ℤ`, the poles of `c^{-s} Γ(s) Γ(s + p)` form two disjoint
   simple-pole lattices `-k` and `-p - k` (`k ∈ ℕ`). Euler's reflection formula converts their
   residues into `(π / sin (π p))` times the terms of `₀F₁(; 1 - p; c)` and
   `-c ^ p · ₀F₁(; 1 + p; c)`.
3. **Contour shifting.** The rectangle residue theorem shifts the vertical line from `σ₂` to any
   pole-avoiding abscissa `σ₁ ≤ σ₂`, picking up the finite sum of residues in `(σ₁, σ₂)`.
4. **Left-tail decay.** Choosing a pole-avoiding offset `δ ∈ (0, 1)` and setting `σ_N = -N - δ`,
   Euler's reflection formula, the reciprocal sine bound `Complex.norm_inv_sin_le`, and the
   factorial decay of `1 / Γ` (`Complex.norm_inv_Gamma_add_natCast_le`) bound the shifted vertical
   integral by `O(‖c‖ ^ N / N!) → 0` as `N → ∞`, so the partial residue sums converge to the full
   `₀F₁` series.

## Main results

* `Complex.integrable_cpow_neg_mul_Gamma_mul_Gamma_add`: vertical-line integrability of
  `y ↦ c^{-(σ + i y)} Γ(σ + i y) Γ(σ + i y + p)` for `c ∈ slitPlane` and pole-avoiding `σ`.
* `Complex.residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_nat` and
  `Complex.residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_nat`: the residues at `-k` and
  `-p - k`, together with their Euler-reflection forms matching `regularizedHGFunCoeff`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_add_sub_integral`: the exact contour-shift
  identity between any two pole-avoiding vertical lines `σ₁ ≤ σ₂`.
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
    rw [norm_cpow_of_ne_zero hc0, neg_re, neg_im, mul_neg, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    refine mul_le_mul ?_ (Real.exp_le_exp.mpr (by rw [← abs_mul]; exact le_abs_self _))
      (Real.exp_pos _).le hM_c
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
  have hsep : ∀ x : ℝ, (∀ n : ℕ, x ≠ -n) → ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ε < |x + n| := by
    intro x hx
    rcases lt_or_ge 0 x with hx0 | hx0
    · exact ⟨x / 2, half_pos hx0, fun n ↦ by
        rw [abs_of_pos (by linarith [n.cast_nonneg (α := ℝ)])]; linarith [n.cast_nonneg (α := ℝ)]⟩
    · have hxZ : x ∈ (Set.range ((↑) : ℤ → ℝ))ᶜ := by
        rintro ⟨m, rfl⟩
        have hm : m ≤ 0 := by exact_mod_cast hx0
        refine hx (-m).toNat ?_
        have hcast : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
        exact_mod_cast (by linarith [hcast] : m = -(((-m).toNat : ℕ) : ℤ))
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Real.isClosed_range_intCast.isOpen_compl x hxZ
      refine ⟨ε / 2, half_pos hε, fun n ↦ ?_⟩
      have hmem : -(n : ℝ) ∉ Metric.ball x ε := fun h ↦ hball h ⟨-(n : ℤ), by simp⟩
      rw [Metric.mem_ball, not_lt, Real.dist_eq] at hmem
      have habs : |-(n : ℝ) - x| = |x + n| := by rw [← abs_neg]; congr 1; ring
      linarith
  obtain ⟨ε₁, hε₁, h1⟩ := hsep σ₁ hσ₁
  obtain ⟨ε₂, hε₂, h2⟩ := hsep σ₂ hσ₂
  obtain ⟨ε₃, hε₃, h3⟩ := hsep (σ₁ + p.re) hσ₁p
  obtain ⟨ε₄, hε₄, h4⟩ := hsep (σ₂ + p.re) hσ₂p
  set ε : ℝ := min (min ε₁ ε₂) (min ε₃ ε₄)
  have hIco : ∀ {x₁ x₂ e₁ e₂ : ℝ} (k : ℕ), ε ≤ e₁ → ε ≤ e₂ →
      (∀ n : ℕ, e₁ < |x₁ + n|) → (∀ n : ℕ, e₂ < |x₂ + n|) →
      x₁ - ε < -(k : ℝ) → -(k : ℝ) < x₂ + ε → k ∈ Finset.Ico ⌈-x₂⌉₊ ⌈-x₁⌉₊ := by
    intro x₁ x₂ e₁ e₂ k he₁ he₂ hx₁ hx₂ hl hu
    refine Finset.mem_Ico.mpr ⟨Nat.ceil_le.mpr ?_, Nat.lt_ceil.mpr ?_⟩
    · rcases lt_or_ge (x₂ + k) 0 with h | h
      · have := hx₂ k; rw [abs_of_neg h] at this; linarith
      · linarith
    · rcases lt_or_ge (x₁ + k) 0 with h | h
      · linarith
      · have := hx₁ k; rw [abs_of_nonneg h] at this; linarith
  refine ⟨ε, lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), fun s hs1 hs2 hpole ↦ ?_⟩
  rcases hpole with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hIco k
      ((min_le_left _ _).trans (min_le_left _ _)) ((min_le_left _ _).trans (min_le_right _ _))
      h1 h2 (by simpa using hs1) (by simpa using hs2), rfl⟩)
  · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hIco k
      ((min_le_right _ _).trans (min_le_left _ _)) ((min_le_right _ _).trans (min_le_right _ _))
      h3 h4 (by simp only [sub_re, neg_re, natCast_re] at hs1; linarith)
      (by simp only [sub_re, neg_re, natCast_re] at hs2; linarith), rfl⟩)

/-- Every pole in the finite strip set `S` lies strictly inside the open rectangle
`(σ₁, σ₂) × (-T, T)` when `T > |Im p|` and `σ₂` avoids the pole lattices. -/
private lemma mem_open_rect_of_mem_strip_poles {p : ℂ} {σ₁ σ₂ T : ℝ} (hT : |p.im| < T)
    (hσ₂ : ∀ n : ℕ, σ₂ ≠ -n) (hσ₂p : ∀ n : ℕ, σ₂ + p.re ≠ -n) {s : ℂ}
    (hs : s ∈ (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
        (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k)) :
    s ∈ Ioo ((σ₁ : ℂ) + (-T : ℝ) * I).re ((σ₂ : ℂ) + (T : ℝ) * I).re ×ℂ
        Ioo ((σ₁ : ℂ) + (-T : ℝ) * I).im ((σ₂ : ℂ) + (T : ℝ) * I).im := by
  have hTpos : 0 < T := (abs_nonneg p.im).trans_lt hT
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico] at hs
  rcases hs with ⟨k, ⟨hk2, hk1⟩, rfl⟩ | ⟨k, ⟨hk2, hk1⟩, rfl⟩
  · have h1 : σ₁ < -(k : ℝ) := by linarith [Nat.lt_ceil.mp hk1]
    have h2 : -(k : ℝ) < σ₂ :=
      lt_of_le_of_ne (by linarith [Nat.ceil_le.mp hk2]) (fun h ↦ hσ₂ k h.symm)
    exact ⟨by simp [h1, h2], by simp [hTpos]⟩
  · have h1 : σ₁ < -p.re - k := by linarith [Nat.lt_ceil.mp hk1]
    have h2 : -p.re - k < σ₂ :=
      lt_of_le_of_ne (by linarith [Nat.ceil_le.mp hk2]) (fun h ↦ hσ₂p k (by linarith))
    obtain ⟨hl, hu⟩ := abs_lt.mp hT
    exact ⟨by simp [h1, h2], by simp; constructor <;> linarith⟩

/-- The rectangle residue identity on `[σ₁, σ₂] × [-T, T]` for `T > |Im p|`. -/
private lemma integral_rectBoundary_cpow_neg_mul_Gamma_mul_Gamma_add
    {c p : ℂ} (hc : c ≠ 0) {σ₁ σ₂ T : ℝ} (hσ : σ₁ < σ₂) (hT : |p.im| < T)
    (hσ₁ : ∀ n : ℕ, σ₁ ≠ -n) (hσ₁p : ∀ n : ℕ, σ₁ + p.re ≠ -n)
    (hσ₂ : ∀ n : ℕ, σ₂ ≠ -n) (hσ₂p : ∀ n : ℕ, σ₂ + p.re ≠ -n) :
    let f : ℂ → ℂ := fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))
    let S : Finset ℂ :=
      (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
      (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k)
    (∫ x : ℝ in σ₁..σ₂, f (x + (-T : ℝ) * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + (T : ℝ) * I)) +
        I * (∫ y : ℝ in (-T)..T, f (σ₂ + y * I)) - I * (∫ y : ℝ in (-T)..T, f (σ₁ + y * I)) =
      2 * (π : ℂ) * I * ∑ s ∈ S, TauCeti.Contour.residue f s := by
  intro f S
  obtain ⟨ε, hε, hstrip⟩ := exists_open_strip_avoiding_poles hσ₁ hσ₁p hσ₂ hσ₂p
  set z : ℂ := (σ₁ : ℂ) + (-T : ℝ) * I
  set w : ℂ := (σ₂ : ℂ) + (T : ℝ) * I
  set U : Set ℂ := {s : ℂ | σ₁ - ε < s.re ∧ s.re < σ₂ + ε}
  have hTpos : 0 < T := (abs_nonneg p.im).trans_lt hT
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  have hRU : Rectangle z w ⊆ U := fun s hs ↦ by
    have hre : s.re ∈ Icc σ₁ σ₂ := by simpa [z, w, uIcc_of_le hσ.le] using hs.1
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  have hS_int : ∀ s ∈ S, s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im :=
    fun s hs ↦ mem_open_rect_of_mem_strip_poles hT hσ₂ hσ₂p hs
  have hS_not_fr : ∀ s ∈ S, s ∉ frontier (Rectangle z w) := fun s hs hfr ↦ by
    have hint : s ∈ interior (Rectangle z w) := by
      rw [interior_rectangle (by simpa [z, w] using hσ.le) (by simpa [z, w] using by linarith)]
      exact hS_int s hs
    exact Set.disjoint_left.mp disjoint_interior_frontier hint hfr
  have hdiff : DifferentiableOn ℂ f (U \ (↑S : Set ℂ)) := fun s ⟨hsU, hsS⟩ ↦
    (differentiableAt_cpow_neg_mul_Gamma_mul_Gamma_add hc
      (fun k hk ↦ hsS (Finset.mem_coe.mpr (hstrip s hsU.1 hsU.2 (Or.inl ⟨k, hk⟩))))
      (fun k hk ↦ hsS (Finset.mem_coe.mpr (hstrip s hsU.1 hsU.2
        (Or.inr ⟨k, by linear_combination hk⟩))))).differentiableWithinAt
  have hres := TauCeti.Contour.classicalResidueTheorem_nullHomologous hU_open hdiff
    (fun s _ _ ↦ meromorphicAt_cpow_neg_mul_Gamma_mul_Gamma_add hc s)
    (isPiecewiseC1On_rectBoundary z w)
    (fun t _ ↦ hRU (rectBoundary_mem_rectangle t)) (by simp)
    (fun t _ ht ↦ hS_not_fr _ (Finset.mem_coe.mp ht) (rectBoundary_mem_frontier t))
    (TauCeti.Contour.isNullHomologous_rectBoundary hRU)
  have hcont_fr : ContinuousOn f (frontier (Rectangle z w)) :=
    hdiff.continuousOn.mono fun s hs ↦
      ⟨hRU ((isClosed_rectangle z w).frontier_subset hs), fun hsS ↦
        hS_not_fr s (Finset.mem_coe.mp hsS) hs⟩
  rw [integral_rectBoundary hcont_fr, Finset.sum_congr rfl fun s hs ↦ by
    rw [TauCeti.Contour.windingNumber_rectBoundary_eq_one (hS_int s hs), one_mul]] at hres
  simpa [z, w, smul_eq_mul] using hres

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
  rcases hσ.eq_or_lt with rfl | hσlt
  · simp
  have hc0 : c ≠ 0 := slitPlane_ne_zero hc
  set f : ℂ → ℂ := fun s ↦ c ^ (-s) * (Gamma s * Gamma (s + p))
  set S : Finset ℂ :=
    (Finset.Ico ⌈-σ₂⌉₊ ⌈-σ₁⌉₊).image (fun k : ℕ ↦ -(k : ℂ)) ∪
    (Finset.Ico ⌈-(σ₂ + p.re)⌉₊ ⌈-(σ₁ + p.re)⌉₊).image (fun k : ℕ ↦ -p - k)
  have hbot : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₁..σ₂, f (x + (-T : ℝ) * I)) atTop (𝓝 0) := by
    simpa [f] using tendsto_horizontal_cpow_neg_mul_Gamma_mul_Gamma_add hc σ₁ σ₂ (-1) (by norm_num)
  have htop : Tendsto (fun T : ℝ ↦ ∫ x : ℝ in σ₁..σ₂, f (x + (T : ℝ) * I)) atTop (𝓝 0) := by
    simpa [f] using tendsto_horizontal_cpow_neg_mul_Gamma_mul_Gamma_add hc σ₁ σ₂ 1 (by norm_num)
  have hright : Tendsto (fun T : ℝ ↦ ∫ y : ℝ in (-T)..T, f (σ₂ + y * I)) atTop
      (𝓝 (∫ y : ℝ, f (σ₂ + y * I))) :=
    intervalIntegral_tendsto_integral (integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc hσ₂ hσ₂p)
      tendsto_neg_atTop_atBot tendsto_id
  have hleft : Tendsto (fun T : ℝ ↦ ∫ y : ℝ in (-T)..T, f (σ₁ + y * I)) atTop
      (𝓝 (∫ y : ℝ, f (σ₁ + y * I))) :=
    intervalIntegral_tendsto_integral (integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc hσ₁ hσ₁p)
      tendsto_neg_atTop_atBot tendsto_id
  have hlim_lhs := ((hbot.sub htop).add (hright.const_mul I)).sub (hleft.const_mul I)
  have hlim_rhs : Tendsto (fun T : ℝ ↦
      (∫ x : ℝ in σ₁..σ₂, f (x + (-T : ℝ) * I)) - (∫ x : ℝ in σ₁..σ₂, f (x + (T : ℝ) * I)) +
        I * (∫ y : ℝ in (-T)..T, f (σ₂ + y * I)) - I * (∫ y : ℝ in (-T)..T, f (σ₁ + y * I)))
      atTop (𝓝 (2 * (π : ℂ) * I * ∑ s ∈ S, TauCeti.Contour.residue f s)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop |p.im|] with T hT
    exact (integral_rectBoundary_cpow_neg_mul_Gamma_mul_Gamma_add
      hc0 hσlt hT hσ₁ hσ₁p hσ₂ hσ₂p).symm
  have heq := tendsto_nhds_unique hlim_lhs hlim_rhs
  have hI : (∫ y : ℝ, f (σ₂ + y * I)) - (∫ y : ℝ, f (σ₁ + y * I)) =
      2 * (π : ℂ) * ∑ s ∈ S, TauCeti.Contour.residue f s := by
    apply mul_left_cancel₀ I_ne_zero
    linear_combination heq
  rw [hI, sum_residue_strip_cpow_neg_mul_Gamma_mul_Gamma_add hc0 hp σ₁ σ₂]

/-! ### Vanishing of the shifted vertical integral as `Re s → -∞` -/

/-- Choose a shift `δ ∈ (0, 1)` so that neither `-δ` nor `Re p - δ` is an integer, ensuring that
every abscissa `-N - δ` (`N : ℕ`) stays uniformly bounded away from the poles of `Γ(s) Γ(s + p)`. -/
private lemma exists_pole_avoiding_shift (p : ℂ) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, (∀ m : ℤ, -(δ : ℝ) ≠ m) ∧ (∀ m : ℤ, p.re - δ ≠ m) := by
  classical
  have hnot_int : ∀ x : ℝ, 0 < x → x < 1 → ∀ m : ℤ, -x ≠ m := fun x hx0 hx1 m hm ↦ by
    have h1 : (m : ℤ) < 0 := by exact_mod_cast (by linarith : (m : ℝ) < 0)
    have h2 : (-1 : ℤ) < m := by exact_mod_cast (by linarith : (-1 : ℝ) < m)
    omega
  by_cases h : ∃ m : ℤ, p.re = (m : ℝ) + 1 / 2
  · obtain ⟨m₀, hm₀⟩ := h
    refine ⟨1 / 4, ⟨by norm_num, by norm_num⟩, hnot_int (1 / 4) (by norm_num) (by norm_num),
      fun m hm ↦ ?_⟩
    have hdiff : ((m - m₀ : ℤ) : ℝ) = 1 / 4 := by push_cast; linarith
    have h1 : (0 : ℤ) < m - m₀ := by exact_mod_cast (by linarith : (0 : ℝ) < (m - m₀ : ℤ))
    have h2 : m - m₀ < 1 := by exact_mod_cast (by linarith : ((m - m₀ : ℤ) : ℝ) < 1)
    omega
  · exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, hnot_int (1 / 2) (by norm_num) (by norm_num),
      fun m hm ↦ h ⟨m, by linarith⟩⟩

/-- Pointwise shifted-line estimate for a single factor `Γ(-N - δ + i y + w)` (`M ≤ N`,
`Re w ≤ M`), combining Euler's reflection formula, `Complex.norm_inv_sin_le`, and
`Complex.norm_inv_Gamma_add_natCast_le`. -/
private lemma norm_Gamma_neg_nat_sub_add_le
    {w : ℂ} {δ K : ℝ} {M N : ℕ} (hδ : 0 < δ) (hwM : w.re ≤ M) (hMN : M ≤ N) (hK : 0 < K)
    (hsin : Real.sin (π * (w.re - δ)) ≠ 0)
    (hinv : ∀ t : ℝ, ‖(Gamma ((1 + δ + M - w.re : ℝ) + t * I))⁻¹‖ ≤ K * Real.exp (π / 2 * |t|))
    (y : ℝ) :
    ‖Gamma (((-(N : ℝ) - δ : ℝ) : ℂ) + y * I + w)‖ ≤
      π * (2 / |Real.sin (π * (w.re - δ))|) * Real.exp (3 * π / 2 * |w.im|) * K /
        ((N - M)! : ℝ) * Real.exp (-(π / 2 * |y|)) := by
  set z : ℂ := (((-(N : ℝ) - δ : ℝ) : ℂ) + y * I) + w
  have hMN' : (M : ℝ) ≤ N := Nat.cast_le.mpr hMN
  have hinv_sin : ‖(sin (π * z))⁻¹‖ ≤
      2 / |Real.sin (π * (w.re - δ))| * Real.exp (π * |w.im|) * Real.exp (-(π * |y|)) := by
    have hre : (π * z).re = π * (w.re - δ) - (N : ℕ) * π := by simp [z]; ring
    have hsin_eq : |Real.sin (π * z).re| = |Real.sin (π * (w.re - δ))| := by
      simp [hre, Real.sin_sub_nat_mul_pi]
    have him : |(π * z).im| = π * |y + w.im| := by simp [z, abs_mul, abs_of_pos pi_pos]
    have htri : |y| - |w.im| ≤ |y + w.im| := by
      simpa [sub_neg_eq_add, abs_neg] using abs_sub_abs_le_abs_sub y (-w.im)
    refine (norm_inv_sin_le (abs_pos.mp (by rw [hsin_eq]; exact abs_pos.mpr hsin))).trans ?_
    rw [hsin_eq, him, mul_assoc, ← Real.exp_add]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [pi_pos, htri])) (by positivity)
  have href : Gamma z = π * (sin (π * z))⁻¹ * (Gamma (1 - z))⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ (Gamma_ne_zero_of_re_pos (by simp [z]; linarith))).mpr
      (by rw [← div_eq_mul_inv]; exact Gamma_mul_Gamma_one_sub z)
  have hinvG : ‖(Gamma (1 - z))⁻¹‖ ≤
      K * Real.exp (π / 2 * |w.im|) * Real.exp (π / 2 * |y|) / ((N - M)! : ℝ) := by
    have hsplit : 1 - z =
        (((1 + δ + M - w.re : ℝ) : ℂ) + (-(y + w.im) : ℝ) * I) + ((N - M : ℕ) : ℂ) := by
      apply Complex.ext <;> simp [z, Nat.cast_sub hMN]; ring
    rw [hsplit]
    refine (norm_inv_Gamma_add_natCast_le (by simp; linarith) (N - M)).trans
      (div_le_div_of_nonneg_right ((hinv (-(y + w.im))).trans ?_) (by positivity))
    rw [mul_assoc, ← Real.exp_add, abs_neg]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [pi_pos, abs_add_le y w.im])) hK.le
  have hexp_w : Real.exp (π * |w.im|) * Real.exp (π / 2 * |w.im|) =
      Real.exp (3 * π / 2 * |w.im|) := by rw [← Real.exp_add]; congr 1; ring
  have hexp_y : Real.exp (-(π * |y|)) * Real.exp (π / 2 * |y|) = Real.exp (-(π / 2 * |y|)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hpi : ‖(π : ℂ)‖ = π := by simp [abs_of_pos pi_pos]
  rw [href, norm_mul, norm_mul, hpi]
  calc π * ‖(sin (π * z))⁻¹‖ * ‖(Gamma (1 - z))⁻¹‖
      ≤ π * (2 / |Real.sin (π * (w.re - δ))| * Real.exp (π * |w.im|) * Real.exp (-(π * |y|))) *
          (K * Real.exp (π / 2 * |w.im|) * Real.exp (π / 2 * |y|) / ((N - M)! : ℝ)) := by gcongr
    _ = π * (2 / |Real.sin (π * (w.re - δ))|) *
          (Real.exp (π * |w.im|) * Real.exp (π / 2 * |w.im|)) * K / ((N - M)! : ℝ) *
          (Real.exp (-(π * |y|)) * Real.exp (π / 2 * |y|)) := by ring
    _ = π * (2 / |Real.sin (π * (w.re - δ))|) * Real.exp (3 * π / 2 * |w.im|) * K /
          ((N - M)! : ℝ) * Real.exp (-(π / 2 * |y|)) := by rw [hexp_w, hexp_y]

/-- Pointwise shifted-line estimate for `Γ(s) Γ(s + p)` on `Re s = -N - δ`
(`N ≥ ⌈max 0 p.re⌉₊`). -/
private lemma norm_Gamma_mul_Gamma_add_left_le
    {p : ℂ} {δ K₁ K₂ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1) (hpδ : ∀ m : ℤ, p.re - δ ≠ m)
    (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hinv₁ : ∀ t : ℝ, ‖(Gamma ((1 + δ : ℝ) + t * I))⁻¹‖ ≤ K₁ * Real.exp (π / 2 * |t|))
    (hinv₂ : ∀ t : ℝ, ‖(Gamma ((1 + δ + ⌈max 0 p.re⌉₊ - p.re : ℝ) + t * I))⁻¹‖ ≤
      K₂ * Real.exp (π / 2 * |t|))
    {N : ℕ} (hMN : ⌈max 0 p.re⌉₊ ≤ N) (y : ℝ) :
    ‖Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p)‖ ≤
      (π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
          Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂)) / (N ! : ℝ) * Real.exp (-(π * |y|)) := by
  set M : ℕ := ⌈max 0 p.re⌉₊
  have hs₁ : Real.sin (π * δ) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos pi_pos hδ.1) (by nlinarith [pi_pos, hδ.2])).ne'
  have hs₂ : Real.sin (π * (p.re - δ)) ≠ 0 := fun h ↦ by
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp h
    exact hpδ m (mul_left_cancel₀ pi_ne_zero (by linarith))
  have h1 : ‖Gamma (((-(N : ℝ) - δ : ℝ) : ℂ) + y * I)‖ ≤
      π * (2 / |Real.sin (π * δ)|) * K₁ / (N ! : ℝ) * Real.exp (-(π / 2 * |y|)) := by
    simpa [Real.sin_neg] using norm_Gamma_neg_nat_sub_add_le (w := 0) (M := 0) hδ.1 (by simp)
      (Nat.zero_le N) hK₁ (by simpa [Real.sin_neg] using hs₁) (by simpa using hinv₁) y
  have h2 : ‖Gamma (((-(N : ℝ) - δ : ℝ) : ℂ) + y * I + p)‖ ≤
      π * (2 / |Real.sin (π * (p.re - δ))|) * Real.exp (3 * π / 2 * |p.im|) * K₂ *
        Real.exp (-(π / 2 * |y|)) := by
    have hfac1 : (1 : ℝ) ≤ ((N - M)! : ℝ) := by exact_mod_cast Nat.factorial_pos (N - M)
    refine (norm_Gamma_neg_nat_sub_add_le hδ.1 ((le_max_right 0 p.re).trans (Nat.le_ceil _))
      hMN hK₂ hs₂ hinv₂ y).trans ?_
    exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) hfac1) (Real.exp_pos _).le
  have hexp : Real.exp (-(π / 2 * |y|)) * Real.exp (-(π / 2 * |y|)) = Real.exp (-(π * |y|)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [norm_mul]
  calc ‖Gamma (((-(N : ℝ) - δ : ℝ) : ℂ) + y * I)‖ *
          ‖Gamma (((-(N : ℝ) - δ : ℝ) : ℂ) + y * I + p)‖
      ≤ (π * (2 / |Real.sin (π * δ)|) * K₁ / (N ! : ℝ) * Real.exp (-(π / 2 * |y|))) *
          (π * (2 / |Real.sin (π * (p.re - δ))|) * Real.exp (3 * π / 2 * |p.im|) * K₂ *
            Real.exp (-(π / 2 * |y|))) := by gcongr
    _ = (π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
            Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂)) / (N ! : ℝ) *
          (Real.exp (-(π / 2 * |y|)) * Real.exp (-(π / 2 * |y|))) := by ring
    _ = (π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
            Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂)) / (N ! : ℝ) *
          Real.exp (-(π * |y|)) := by rw [hexp]

/-- Pointwise shifted-line estimate for the full Mellin–Barnes integrand on `Re s = -N - δ`
(`N ≥ ⌈max 0 p.re⌉₊`). -/
private lemma norm_cpow_neg_mul_Gamma_mul_Gamma_add_left_le
    {c p : ℂ} (hc0 : c ≠ 0) {δ K₁ K₂ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hpδ : ∀ m : ℤ, p.re - δ ≠ m) (hK₁ : 0 < K₁) (hK₂ : 0 < K₂)
    (hinv₁ : ∀ t : ℝ, ‖(Gamma ((1 + δ : ℝ) + t * I))⁻¹‖ ≤ K₁ * Real.exp (π / 2 * |t|))
    (hinv₂ : ∀ t : ℝ, ‖(Gamma ((1 + δ + ⌈max 0 p.re⌉₊ - p.re : ℝ) + t * I))⁻¹‖ ≤
      K₂ * Real.exp (π / 2 * |t|))
    {N : ℕ} (hMN : ⌈max 0 p.re⌉₊ ≤ N) (y : ℝ) :
    ‖c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
        (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p))‖ ≤
      (‖c‖ ^ δ * (π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
          Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂))) *
        (‖c‖ ^ N / (N ! : ℝ)) * Real.exp (-((π - |c.arg|) * |y|)) := by
  set s : ℂ := ((-(N : ℝ) - δ : ℝ) : ℂ) + y * I
  have hcpow : ‖c ^ (-s)‖ ≤ ‖c‖ ^ δ * ‖c‖ ^ N * Real.exp (|c.arg| * |y|) := by
    rw [norm_cpow_of_ne_zero hc0, neg_re, neg_im, mul_neg, div_eq_mul_inv, ← Real.exp_neg, neg_neg]
    have hre : -s.re = δ + (N : ℝ) := by simp [s, add_comm]
    have him : s.im = y := by simp [s]
    rw [hre, him, Real.rpow_add (norm_pos_iff.mpr hc0), Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by rw [← abs_mul]; exact le_abs_self _)) (by positivity)
  have hG := norm_Gamma_mul_Gamma_add_left_le hδ hpδ hK₁ hK₂ hinv₁ hinv₂ hMN y
  have hexp : Real.exp (|c.arg| * |y|) * Real.exp (-(π * |y|)) =
      Real.exp (-((π - |c.arg|) * |y|)) := by rw [← Real.exp_add]; congr 1; ring
  rw [norm_mul]
  calc ‖c ^ (-s)‖ * ‖Gamma s * Gamma (s + p)‖
      ≤ (‖c‖ ^ δ * ‖c‖ ^ N * Real.exp (|c.arg| * |y|)) *
          ((π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
            Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂)) / (N ! : ℝ) *
            Real.exp (-(π * |y|))) := by gcongr
    _ = (‖c‖ ^ δ * (π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
            Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂))) *
          (‖c‖ ^ N / (N ! : ℝ)) * (Real.exp (|c.arg| * |y|) * Real.exp (-(π * |y|))) := by ring
    _ = (‖c‖ ^ δ * (π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
            Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂))) *
          (‖c‖ ^ N / (N ! : ℝ)) * Real.exp (-((π - |c.arg|) * |y|)) := by rw [hexp]

/-- For a fixed pole-avoiding offset `δ ∈ (0, 1)`, the vertical integral along `Re s = -N - δ`
tends to `0` as `N → ∞`, with bound `O(‖c‖ ^ N / N!)`. -/
private lemma tendsto_integral_cpow_neg_mul_Gamma_mul_Gamma_add_left
    {c p : ℂ} (hc : c ∈ slitPlane) {δ : ℝ} (hδ : δ ∈ Ioo (0 : ℝ) 1)
    (hδ_int : ∀ m : ℤ, -(δ : ℝ) ≠ m) (hpδ : ∀ m : ℤ, p.re - δ ≠ m) :
    Tendsto (fun N : ℕ ↦ ∫ y : ℝ,
        c ^ (-((-(N : ℝ) - δ : ℝ) + y * I)) *
          (Gamma ((-(N : ℝ) - δ : ℝ) + y * I) * Gamma ((-(N : ℝ) - δ : ℝ) + y * I + p)))
      atTop (𝓝 0) := by
  set α : ℝ := π - |c.arg|
  have hα : 0 < α := sub_pos.mpr
    (abs_lt.mpr ⟨neg_pi_lt_arg c, lt_of_le_of_ne (arg_le_pi c) (mem_slitPlane_iff_arg.mp hc).1⟩)
  have hinv_line : ∀ a : ℝ, 1 ≤ a →
      ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, ‖(Gamma (a + t * I))⁻¹‖ ≤ K * Real.exp (π / 2 * |t|) := by
    intro a ha
    obtain ⟨C, T, hS⟩ := TauCeti.exists_abs_log_norm_Gamma_vertical_sub_le a a
    set Y : ℝ := max T 1
    set K_hi : ℝ := Real.exp (max C 0 - Real.log (2 * π) / 2)
    obtain ⟨K_lo, hK_lo⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((differentiable_one_div_Gamma.continuous.comp
        (by fun_prop : Continuous fun t : ℝ ↦ (a : ℂ) + t * I)).continuousOn (s := Icc (-Y) Y))
    refine ⟨max K_hi (max K_lo 1), lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _), fun t ↦ ?_⟩
    rcases le_total Y |t| with ht | ht
    · have ht1 : 1 ≤ |t| := (le_max_right T 1).trans ht
      have hlow : -(C / |t|) ≤ Real.log ‖Gamma (a + t * I)‖ -
          ((a - 1 / 2) * Real.log |t| - π * |t| / 2 + Real.log (2 * π) / 2) := by
        simpa using (abs_le.mp (hS (a + t * I) (by simp)
          (by simpa using (le_max_left T 1).trans ht))).1
      have hC_le : C / |t| ≤ max C 0 :=
        (div_le_div_of_nonneg_right (le_max_left C 0) (by positivity)).trans
          (div_le_self (le_max_right C 0) ht1)
      have hpos : 0 ≤ (a - 1 / 2) * Real.log |t| := mul_nonneg (by linarith) (Real.log_nonneg ht1)
      rw [norm_inv]
      refine (inv_le_of_inv_le₀ (by positivity) ?_).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      rw [← Real.exp_log (norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by simp; linarith))), mul_inv]
      simp only [K_hi, ← Real.exp_neg, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    · exact (hK_lo t (abs_le.mp ht)).trans (((le_max_left K_lo 1).trans (le_max_right K_hi _)).trans
        (le_mul_of_one_le_right (le_trans (Real.exp_pos _).le (le_max_left _ _))
          (Real.one_le_exp (by positivity))))
  set M : ℕ := ⌈max 0 p.re⌉₊
  obtain ⟨K₁, hK₁, hinv₁⟩ := hinv_line (1 + δ) (by linarith [hδ.1])
  obtain ⟨K₂, hK₂, hinv₂⟩ := hinv_line (1 + δ + M - p.re)
    (by linarith [hδ.1, (le_max_right 0 p.re).trans (Nat.le_ceil _)])
  set C₀ : ℝ := ‖c‖ ^ δ * (π ^ 2 * (4 / (|Real.sin (π * δ)| * |Real.sin (π * (p.re - δ))|)) *
      Real.exp (3 * π / 2 * |p.im|) * (K₁ * K₂))
  refine squeeze_zero_norm' ?_ (by simpa using
    ((Real.summable_pow_div_factorial ‖c‖).tendsto_atTop_zero.const_mul C₀).mul_const (2 / α))
  filter_upwards [eventually_ge_atTop M] with N hMN
  refine (norm_integral_le_integral_norm _).trans ((integral_mono
    ((integrable_cpow_neg_mul_Gamma_mul_Gamma_add hc
      (fun n h ↦ hδ_int ((N : ℤ) - n) (by push_cast; linarith))
      (fun n h ↦ hpδ ((N : ℤ) - n) (by push_cast; linarith))).norm)
    ((TauCeti.integrable_exp_neg_mul_abs hα).const_mul _)
    (norm_cpow_neg_mul_Gamma_mul_Gamma_add_left_le (slitPlane_ne_zero hc)
      hδ hpδ hK₁ hK₂ hinv₁ hinv₂ hMN)).trans_eq ?_)
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
  obtain ⟨δ, hδ, hδ_int, hpδ⟩ := exists_pole_avoiding_shift p
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
