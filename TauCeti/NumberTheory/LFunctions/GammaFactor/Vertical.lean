/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Archimedean
public import TauCeti.NumberTheory.LFunctions.GammaFactor.Order
public import TauCeti.NumberTheory.LFunctions.Data.AnalyticConductor.Basic
public import TauCeti.NumberTheory.LFunctions.Data.Normalization
public import TauCeti.NumberTheory.LFunctions.Data.RiemannZeta
import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv

/-!
# Vertical-strip asymptotics of archimedean gamma factors and dual gamma quotients

For an analytic L-function record `d : AnalyticLFunctionData` of degree `n = d.degree` with gamma
factor
$$\gamma(s) = \prod_{\mu \in \mathrm{gammaR}} \Gamma_{\mathbb{R}}(s + \mu)
  \prod_{\nu \in \mathrm{gammaC}} \Gamma_{\mathbb{C}}(s + \nu),$$
summing the complex-shifted vertical-strip Stirling estimates of
`TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Archimedean` over the multisets `d.gammaR` and
`d.gammaC` yields, uniformly for `σ ∈ [a, b]` as `|t| → ∞`,
$$\log \|\gamma(\sigma + i t)\| = -\frac{\pi n}{4} |t| + A(\sigma) \log |t| + O(1),$$
where the logarithmic height exponent is
$$A(\sigma) = \sum_{\mu \in \mathrm{gammaR}} \frac{\sigma + \operatorname{Re}\mu - 1}{2}
  + \sum_{\nu \in \mathrm{gammaC}} \left(\sigma + \operatorname{Re}\nu - \frac{1}{2}\right).$$
The implied constant and height threshold can be chosen uniformly across all records of fixed
degree `n` whose spectral shifts are bounded in norm by `M`, independently of the arithmetic
conductor.

For the reflected dual quotient `d.dual.gammaFactor (1 - s) / d.gammaFactor s` governing the
functional equation of the uncompleted L-function, two cancellations occur simultaneously:

* the linear exponential terms `-(π n / 4) |t|` of `d.dual.gammaFactor (1 - s)` and
  `d.gammaFactor s` agree and cancel;
* conjugating the gamma shifts in `d.dual` leaves their real parts unchanged, and those real parts
  enter `1 - s + conj μ` and `s + μ` with the same sign, so `d.dual.gammaLogExponent (1 - σ) -
  d.gammaLogExponent σ = (n / 2) (1 - 2 σ)` depends only on the degree and `σ`.

Consequently, uniformly on every vertical strip `Re s ∈ [a, b]`,
$$\log \left\|\frac{\gamma^{\vee}(1 - s)}{\gamma(s)}\right\| =
  \frac{n}{2} (1 - 2 \operatorname{Re} s) \log |\operatorname{Im} s| + O(1),$$
and along `Re s = -δ` this specializes to `(n / 2) (1 + 2 δ) log |t| + O(1)`. Combining the
resulting polynomial height bound with `AnalyticLFunctionData.conductor_mul_height_pow_le` bounds
the conductor-weighted archimedean functional-equation factor
`‖N ^ (1 / 2 - s) (γ^∨(1 - s) / γ(s))‖` by a constant multiple of
`d.analyticConductorAt s ^ (1 / 2 - s.re)` uniformly in `d.conductor` — both at large height on
arbitrary strips `Re s ∈ [a, 1 / 2]` and for all `t : ℝ` on `Re s = -δ` (`δ > 0`) whenever the
reflected line `Re w = 1 + δ` avoids the shifted gamma poles.

## Main declarations

* `AnalyticLFunctionData.gammaLogExponent`: the exponent `A(σ)` of `log |t|`, with
  `gammaLogExponent_dual` and `gammaLogExponent_one_sub_sub`.
* `AnalyticLFunctionData.exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le`,
  `AnalyticLFunctionData.isBigO_log_norm_gammaFactor_vertical_sub` (and strip / line / two-sided
  norm variants): vertical-strip asymptotics of `d.gammaFactor`.
* `AnalyticLFunctionData.exists_abs_log_norm_dual_gammaFactor_div_le_of_norm_le`,
  `AnalyticLFunctionData.isBigO_log_norm_dual_gammaFactor_div_vertical_sub`,
  `AnalyticLFunctionData.isBigO_log_norm_dual_gammaFactor_div_neg_line_sub`: exponential
  cancellation in `log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖`.
* `exists_norm_conductor_cpow_mul_dual_gammaFactor_div_le_analyticConductorAt`,
  `exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le`:
  conductor-uniform upper bounds in terms of `d.analyticConductorAt`.

## References

* [NIST Digital Library of Mathematical Functions, 5.11.9](https://dlmf.nist.gov/5.11.E9).
* P. Deligne, *Valeurs de fonctions L et périodes d'intégrales*, Proc. Symp. Pure Math. 33 (1979),
  Part 2, §5.3.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §§5.1–5.2.
* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (1986), §§4.12 and 5.1.
-/

public section

open Complex ComplexConjugate Real Filter Set Asymptotics

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-! ### Auxiliary multiset bounds -/

private theorem sum_map_gammaR_linear (m : Multiset ℂ) (σ : ℝ) :
    (m.map fun μ ↦ (σ + μ.re - 1) / 2).sum =
      (m.card : ℝ) / 2 * σ + (m.map fun μ ↦ (μ.re - 1) / 2).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons μ m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, ih]
    ring

private theorem sum_map_gammaC_linear (m : Multiset ℂ) (σ : ℝ) :
    (m.map fun ν ↦ σ + ν.re - 1 / 2).sum =
      (m.card : ℝ) * σ + (m.map fun ν ↦ ν.re - 1 / 2).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons ν m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, ih]
    ring

private theorem abs_multiset_sum_sub_le {ι : Type*} (m : Multiset ι) (f g : ι → ℝ) {C : ℝ}
    (h : ∀ x ∈ m, |f x - g x| ≤ C) : |(m.map f).sum - (m.map g).sum| ≤ (m.card : ℝ) * C := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one]
    have hx : |f x - g x| ≤ C := h x (Multiset.mem_cons_self x m)
    have hm : |(m.map f).sum - (m.map g).sum| ≤ (m.card : ℝ) * C :=
      ih fun y hy ↦ h y (Multiset.mem_cons_of_mem hy)
    rw [show f x + (m.map f).sum - (g x + (m.map g).sum) =
        (f x - g x) + ((m.map f).sum - (m.map g).sum) by ring]
    exact (abs_add_le _ _).trans (by linarith)

private theorem norm_multiset_prod_le_pow {ι : Type*} (m : Multiset ι) (f : ι → ℂ) (B : ℝ)
    (hf : ∀ x ∈ m, ‖f x‖ ≤ B) : ‖(m.map f).prod‖ ≤ B ^ m.card := by
  rw [Multiset.norm_prod, Multiset.map_map]
  simpa using Multiset.prod_map_le_prod_map₀ (fun x ↦ ‖f x‖) (fun _ ↦ B)
    (fun _ _ ↦ norm_nonneg _) hf

/-! ### The logarithmic height exponent `A(σ)` -/

/-- The exponent `A(σ) = ∑_{μ ∈ gammaR} (σ + Re μ - 1)/2 + ∑_{ν ∈ gammaC} (σ + Re ν - 1/2)` of
`log |Im s|` in the vertical-strip asymptotic of `log ‖d.gammaFactor s‖`. -/
noncomputable def gammaLogExponent (d : AnalyticLFunctionData) (σ : ℝ) : ℝ :=
  (d.gammaR.map fun μ ↦ (σ + μ.re - 1) / 2).sum +
    (d.gammaC.map fun ν ↦ σ + ν.re - 1 / 2).sum

theorem gammaLogExponent_def (d : AnalyticLFunctionData) (σ : ℝ) :
    d.gammaLogExponent σ =
      (d.gammaR.map fun μ ↦ (σ + μ.re - 1) / 2).sum +
        (d.gammaC.map fun ν ↦ σ + ν.re - 1 / 2).sum :=
  (rfl)

/-- `d.gammaLogExponent` is affine in `σ` with slope `d.degree / 2`. -/
theorem gammaLogExponent_eq (d : AnalyticLFunctionData) (σ : ℝ) :
    d.gammaLogExponent σ = (d.degree : ℝ) / 2 * σ +
      ((d.gammaR.map fun μ ↦ (μ.re - 1) / 2).sum +
        (d.gammaC.map fun ν ↦ ν.re - 1 / 2).sum) := by
  rw [gammaLogExponent_def, sum_map_gammaR_linear, sum_map_gammaC_linear, degree_def]
  push_cast
  ring

/-- Shifting the real part by `τ` shifts `gammaLogExponent` by `(d.degree / 2) * τ`. -/
theorem gammaLogExponent_add (d : AnalyticLFunctionData) (σ τ : ℝ) :
    d.gammaLogExponent (σ + τ) = d.gammaLogExponent σ + (d.degree : ℝ) / 2 * τ := by
  rw [d.gammaLogExponent_eq (σ + τ), d.gammaLogExponent_eq σ]
  ring

/-- A degree-zero record has vanishing logarithmic gamma exponent. -/
theorem gammaLogExponent_eq_zero_of_degree_eq_zero (d : AnalyticLFunctionData)
    (hd : d.degree = 0) (σ : ℝ) : d.gammaLogExponent σ = 0 := by
  have hR : d.gammaR = 0 := Multiset.card_eq_zero.mp (by rw [degree_def] at hd; omega)
  have hC : d.gammaC = 0 := Multiset.card_eq_zero.mp (by rw [degree_def] at hd; omega)
  simp [gammaLogExponent_def, hR, hC]

/-- Conjugating the shifts in `d.dual` preserves their real parts, leaving `gammaLogExponent`
unchanged. -/
@[simp]
theorem gammaLogExponent_dual (d : AnalyticLFunctionData) (σ : ℝ) :
    d.dual.gammaLogExponent σ = d.gammaLogExponent σ := by
  simp [gammaLogExponent_def, Multiset.map_map]

/-- The reflected exponent difference `A(1 - σ) - A(σ)` cancels all shift real parts, leaving
`(d.degree / 2) * (1 - 2 σ)`. -/
@[simp]
theorem gammaLogExponent_one_sub_sub (d : AnalyticLFunctionData) (σ : ℝ) :
    d.gammaLogExponent (1 - σ) - d.gammaLogExponent σ = (d.degree : ℝ) / 2 * (1 - 2 * σ) := by
  rw [d.gammaLogExponent_eq (1 - σ), d.gammaLogExponent_eq σ]
  ring

/-! ### Nonvanishing off the pole lattices and additive log-norm decomposition -/

/-- `d.gammaFactor s` is nonzero whenever `s + μ` and `s + ν` lie off the real axis for all shifts
`μ ∈ d.gammaR` and `ν ∈ d.gammaC`. -/
theorem gammaFactor_ne_zero_of_forall_im_ne (d : AnalyticLFunctionData) {s : ℂ}
    (hR : ∀ μ ∈ d.gammaR, s.im + μ.im ≠ 0) (hC : ∀ ν ∈ d.gammaC, s.im + ν.im ≠ 0) :
    d.gammaFactor s ≠ 0 := by
  rw [Ne, d.gammaFactor_eq_zero_iff]
  rintro (⟨μ, hμ, n, hn⟩ | ⟨ν, hν, n, hn⟩)
  · exact hR μ hμ (by simpa using congrArg im hn)
  · exact hC ν hν (by simpa using congrArg im hn)

/-- `d.gammaFactor s` is nonzero once `|s.im|` strictly exceeds the imaginary parts of all
shifts. -/
theorem gammaFactor_ne_zero_of_im_gt (d : AnalyticLFunctionData) {s : ℂ}
    (hR : ∀ μ ∈ d.gammaR, |μ.im| < |s.im|) (hC : ∀ ν ∈ d.gammaC, |ν.im| < |s.im|) :
    d.gammaFactor s ≠ 0 := by
  refine d.gammaFactor_ne_zero_of_forall_im_ne (fun μ hμ h0 ↦ ?_) (fun ν hν h0 ↦ ?_)
  · have : |μ.im| = |s.im| := by rw [show μ.im = -s.im by linarith, abs_neg]
    exact (hR μ hμ).ne this
  · have : |ν.im| = |s.im| := by rw [show ν.im = -s.im by linarith, abs_neg]
    exact (hC ν hν).ne this

/-- `d.gammaFactor s` is nonzero whenever every shifted real part `s.re + μ.re` and `s.re + ν.re`
is strictly positive. -/
theorem gammaFactor_ne_zero_of_re_pos (d : AnalyticLFunctionData) {s : ℂ}
    (hR : ∀ μ ∈ d.gammaR, 0 < s.re + μ.re) (hC : ∀ ν ∈ d.gammaC, 0 < s.re + ν.re) :
    d.gammaFactor s ≠ 0 := by
  rw [Ne, d.gammaFactor_eq_zero_iff]
  rintro (⟨μ, hμ, n, hn⟩ | ⟨ν, hν, n, hn⟩)
  · have hre : s.re + μ.re = -(2 * (n : ℝ)) := by simpa using congrArg re hn
    linarith [hR μ hμ, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have hre : s.re + ν.re = -(n : ℝ) := by simpa using congrArg re hn
    linarith [hC ν hν, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- Away from the poles of `d.gammaFactor`, `log ‖d.gammaFactor s‖` is the sum of the logarithms of
the norms of its shifted `Gammaℝ` and `Gammaℂ` factors. -/
theorem log_norm_gammaFactor (d : AnalyticLFunctionData) {s : ℂ} (hs : d.gammaFactor s ≠ 0) :
    Real.log ‖d.gammaFactor s‖ =
      (d.gammaR.map fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖).sum +
        (d.gammaC.map fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖).sum := by
  rw [gammaFactor_def] at hs ⊢
  have hR_ne : (d.gammaR.map fun μ ↦ Gammaℝ (s + μ)).prod ≠ 0 := left_ne_zero_of_mul hs
  have hC_ne : (d.gammaC.map fun ν ↦ Gammaℂ (s + ν)).prod ≠ 0 := right_ne_zero_of_mul hs
  have hR_mem : ∀ x ∈ (d.gammaR.map fun μ ↦ ‖Gammaℝ (s + μ)‖), x ≠ 0 := by
    intro x hx
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_ne_zero_iff.2 fun h0 ↦ hR_ne
      (Multiset.prod_eq_zero (by
        simpa [h0] using Multiset.mem_map_of_mem (fun μ ↦ Gammaℝ (s + μ)) hμ))
  have hC_mem : ∀ x ∈ (d.gammaC.map fun ν ↦ ‖Gammaℂ (s + ν)‖), x ≠ 0 := by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_ne_zero_iff.2 fun h0 ↦ hC_ne
      (Multiset.prod_eq_zero (by
        simpa [h0] using Multiset.mem_map_of_mem (fun ν ↦ Gammaℂ (s + ν)) hν))
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.2 hR_ne) (norm_ne_zero_iff.2 hC_ne),
    Multiset.norm_prod, Multiset.norm_prod]
  simp only [Multiset.map_map, Function.comp_def]
  rw [Real.log_multiset_prod hR_mem, Real.log_multiset_prod hC_mem]
  simp only [Multiset.map_map, Function.comp_def]

/-! ### Vertical-strip Stirling asymptotics for `d.gammaFactor` -/

private theorem gammaFactor_stirling_main_sum (d : AnalyticLFunctionData) (s : ℂ) :
    (d.gammaR.map fun μ ↦ -Real.pi * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|).sum +
    (d.gammaC.map fun ν ↦ -Real.pi * |s.im| / 2 + (s.re + ν.re - 1 / 2) * Real.log |s.im|).sum =
      -(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im| := by
  rw [Multiset.sum_map_add, Multiset.sum_map_add,
    Multiset.map_const', Multiset.sum_replicate, Multiset.map_const', Multiset.sum_replicate,
    Multiset.sum_map_mul_right, Multiset.sum_map_mul_right, gammaLogExponent_def,
    degree_def]
  simp only [nsmul_eq_mul]
  push_cast
  ring

/-- **Uniform vertical-strip asymptotic for `d.gammaFactor`** across all records of degree `n` with
shifts bounded in norm by `M`: the constant `C` and height threshold `T` depend only on `a`, `b`,
`n`, and `M`, not on `d` or `d.conductor`. -/
theorem exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le (a b : ℝ) (n : ℕ) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        d.gammaFactor s ≠ 0 ∧
        |Real.log ‖d.gammaFactor s‖ -
            (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|)| ≤
          C := by
  obtain ⟨CR, hCR0, TR, hTR0, hR_est⟩ := exists_abs_log_norm_Gammaℝ_add_vertical_sub_le a b hM
  obtain ⟨CC, _, TC, _, hC_est⟩ := exists_abs_log_norm_Gammaℂ_add_vertical_sub_le a b hM
  set K := max CR CC
  have hK0 : 0 ≤ K := hCR0.trans (le_max_left _ _)
  refine ⟨(n : ℝ) * K, by positivity, max (max TR TC) (M + 1), by positivity,
    fun d hd hR hC s hs ht ↦ ?_⟩
  have htTR : TR ≤ |s.im| := ((le_max_left _ _).trans (le_max_left _ _)).trans ht
  have htTC : TC ≤ |s.im| := ((le_max_right _ _).trans (le_max_left _ _)).trans ht
  have htM : M + 1 ≤ |s.im| := (le_max_right _ _).trans ht
  have hne : d.gammaFactor s ≠ 0 := d.gammaFactor_ne_zero_of_im_gt
    (fun μ hμ ↦ ((abs_im_le_norm μ).trans (hR μ hμ)).trans_lt (by linarith))
    (fun ν hν ↦ ((abs_im_le_norm ν).trans (hC ν hν)).trans_lt (by linarith))
  refine ⟨hne, ?_⟩
  have hsumR := abs_multiset_sum_sub_le d.gammaR
    (fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖)
    (fun μ ↦ -Real.pi * |s.im| / 4 + (s.re + μ.re - 1) / 2 * Real.log |s.im|)
    (C := K) fun μ hμ ↦ (hR_est μ (hR μ hμ) s hs htTR).trans (le_max_left _ _)
  have hsumC := abs_multiset_sum_sub_le d.gammaC
    (fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖)
    (fun ν ↦ -Real.pi * |s.im| / 2 + (s.re + ν.re - 1 / 2) * Real.log |s.im|)
    (C := K) fun ν hν ↦ (hC_est ν (hC ν hν) s hs htTC).trans (le_max_right _ _)
  rw [d.log_norm_gammaFactor hne, ← d.gammaFactor_stirling_main_sum s]
  rw [show (d.gammaR.map fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖).sum +
        (d.gammaC.map fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖).sum - _ =
      ((d.gammaR.map fun μ ↦ Real.log ‖Gammaℝ (s + μ)‖).sum -
        (d.gammaR.map fun μ ↦ -Real.pi * |s.im| / 4 +
          (s.re + μ.re - 1) / 2 * Real.log |s.im|).sum) +
      ((d.gammaC.map fun ν ↦ Real.log ‖Gammaℂ (s + ν)‖).sum -
        (d.gammaC.map fun ν ↦ -Real.pi * |s.im| / 2 +
          (s.re + ν.re - 1 / 2) * Real.log |s.im|).sum) by ring]
  refine (abs_add_le _ _).trans ((add_le_add hsumR hsumC).trans ?_)
  have hcard : (d.gammaR.card : ℝ) + d.gammaC.card ≤ n := by
    have : d.gammaR.card + d.gammaC.card ≤ n := by rw [← hd, degree_def]; omega
    exact_mod_cast this
  nlinarith

/-- Every record `d` has a finite norm bound on its real and complex gamma shifts. -/
private theorem exists_shift_norm_le (d : AnalyticLFunctionData) :
    ∃ M ≥ 0, (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) ∧ (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) := by
  have hnn (m : Multiset ℂ) : ∀ x ∈ m.map norm, (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨z, -, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_nonneg z
  have hR0 : 0 ≤ (d.gammaR.map norm).sum := Multiset.sum_nonneg (hnn d.gammaR)
  have hC0 : 0 ≤ (d.gammaC.map norm).sum := Multiset.sum_nonneg (hnn d.gammaC)
  refine ⟨(d.gammaR.map norm).sum + (d.gammaC.map norm).sum, add_nonneg hR0 hC0,
    fun μ hμ ↦ ?_, fun ν hν ↦ ?_⟩
  · have h1 := Multiset.single_le_sum (hnn d.gammaR) ‖μ‖ (Multiset.mem_map_of_mem norm hμ)
    linarith
  · have h2 := Multiset.single_le_sum (hnn d.gammaC) ‖ν‖ (Multiset.mem_map_of_mem norm hν)
    linarith

/-- Uniform vertical-strip bound for `log ‖d.gammaFactor s‖` on `Re s ∈ [a, b]`. -/
theorem exists_abs_log_norm_gammaFactor_vertical_sub_le (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C ≥ 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      d.gammaFactor s ≠ 0 ∧
      |Real.log ‖d.gammaFactor s‖ -
          (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|)| ≤
        C := by
  obtain ⟨M, hM0, hR, hC⟩ := d.exists_shift_norm_le
  obtain ⟨C, hC0, T, hT0, h⟩ :=
    exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le a b d.degree hM0
  exact ⟨C, hC0, T, hT0, h d rfl hR hC⟩

/-- **Vertical-strip asymptotic of `d.gammaFactor`**:
`log ‖d.gammaFactor(σ + i t)‖ = -(π d.degree / 4) |t| + d.gammaLogExponent σ * log |t| + O(1)`
uniformly for `σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_gammaFactor_vertical_sub (d : AnalyticLFunctionData) (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖d.gammaFactor (p.1 + p.2 * I)‖ -
        (-(Real.pi * d.degree / 4) * |p.2| + d.gammaLogExponent p.1 * Real.log |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_gammaFactor_vertical_sub_le a b
  refine isBigO_one_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using (h (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)).2

/-- **Vertical-strip asymptotic of `d.gammaFactor`** as a function of `s` on `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_gammaFactor_vertical_strip_sub (d : AnalyticLFunctionData) (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖d.gammaFactor s‖ -
        (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|))
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_gammaFactor_vertical_sub_le a b
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ (h s hs ht).2⟩

/-- Vertical-line asymptotic of `t ↦ log ‖d.gammaFactor (σ + i t)‖` along `cocompact ℝ`. -/
theorem isBigO_log_norm_gammaFactor_vertical_line_sub (d : AnalyticLFunctionData) (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖d.gammaFactor (σ + t * I)‖ -
        (-(Real.pi * d.degree / 4) * |t| + d.gammaLogExponent σ * Real.log |t|))
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  TauCeti.isBigO_cocompact_of_vertical (d.isBigO_log_norm_gammaFactor_vertical_sub σ σ)

/-- Two-sided norm bounds for `‖d.gammaFactor s‖` on a compact vertical strip `Re s ∈ [a, b]`
above the pole heights:
`C₁ exp(-(π n / 4) |t|) |t| ^ A(σ) ≤ ‖γ(s)‖ ≤ C₂ exp(-(π n / 4) |t|) |t| ^ A(σ)`. -/
theorem exists_norm_gammaFactor_vertical_bounds (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      C₁ * Real.exp (-(Real.pi * d.degree / 4) * |s.im|) * |s.im| ^ d.gammaLogExponent s.re ≤
        ‖d.gammaFactor s‖ ∧
      ‖d.gammaFactor s‖ ≤
        C₂ * Real.exp (-(Real.pi * d.degree / 4) * |s.im|) * |s.im| ^ d.gammaLogExponent s.re := by
  obtain ⟨C, -, T, hT0, h⟩ := d.exists_abs_log_norm_gammaFactor_vertical_sub_le a b
  refine ⟨Real.exp (-C), Real.exp_pos _, Real.exp C, Real.exp_pos _, T, hT0, fun s hs ht ↦ ?_⟩
  obtain ⟨hne, hlog⟩ := h s hs ht
  have ht_pos : 0 < |s.im| := hT0.trans_le ht
  have hnorm_pos : 0 < ‖d.gammaFactor s‖ := norm_pos_iff.2 hne
  obtain ⟨hl, hu⟩ := abs_le.1 hlog
  set E := -(Real.pi * d.degree / 4) * |s.im|
  set L := d.gammaLogExponent s.re * Real.log |s.im|
  have hexp_L : Real.exp L = |s.im| ^ d.gammaLogExponent s.re := by
    rw [Real.rpow_def_of_pos ht_pos]
    dsimp only [L]
    ring_nf
  constructor
  · calc Real.exp (-C) * Real.exp E * |s.im| ^ d.gammaLogExponent s.re
        = Real.exp (-C + E + L) := by rw [← hexp_L, ← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (Real.log ‖d.gammaFactor s‖) := Real.exp_le_exp.2 (by linarith)
      _ = ‖d.gammaFactor s‖ := Real.exp_log hnorm_pos
  · calc ‖d.gammaFactor s‖
        = Real.exp (Real.log ‖d.gammaFactor s‖) := (Real.exp_log hnorm_pos).symm
      _ ≤ Real.exp (C + E + L) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp C * Real.exp E * |s.im| ^ d.gammaLogExponent s.re := by
          rw [← hexp_L, ← Real.exp_add, ← Real.exp_add]

/-! ### Exponential cancellation in the dual gamma quotient -/

/-- **Exponential cancellation in the dual gamma quotient**, uniform across all records of degree
`n` with shifts bounded in norm by `M`: the linear exponential terms `-(π n / 4) |Im s|` and all
shift real parts cancel between `d.dual.gammaFactor (1 - s)` and `d.gammaFactor s`, leaving
`(n / 2) * (1 - 2 * s.re) * log |s.im| + O(1)` with constants independent of `d` and
`d.conductor`. -/
theorem exists_abs_log_norm_dual_gammaFactor_div_le_of_norm_le (a b : ℝ) (n : ℕ) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ C ≥ 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        d.gammaFactor s ≠ 0 ∧ d.dual.gammaFactor (1 - s) ≠ 0 ∧
        |Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ -
            ((d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|)| ≤ C := by
  obtain ⟨C₁, hC₁, T₁, hT₁, h₁⟩ :=
    exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le a b n hM
  obtain ⟨C₂, hC₂, T₂, _, h₂⟩ :=
    exists_abs_log_norm_gammaFactor_vertical_sub_le_of_norm_le (1 - b) (1 - a) n hM
  refine ⟨C₁ + C₂, by positivity, max T₁ T₂, by positivity,
    fun d hd hR hC s hs ht ↦ ?_⟩
  have hR_dual : ∀ μ' ∈ d.dual.gammaR, ‖μ'‖ ≤ M := by
    intro μ' hμ'
    rw [dual_gammaR] at hμ'
    obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hμ'
    simpa using hR μ hμ
  have hC_dual : ∀ ν' ∈ d.dual.gammaC, ‖ν'‖ ≤ M := by
    intro ν' hν'
    rw [dual_gammaC] at hν'
    obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hν'
    simpa using hC ν hν
  have hs1 : (1 - s).re ∈ Icc (1 - b) (1 - a) :=
    ⟨by simp; linarith [hs.2], by simp; linarith [hs.1]⟩
  have him1 : |(1 - s).im| = |s.im| := by simp
  obtain ⟨hne₁, hb₁⟩ := h₁ d hd hR hC s hs ((le_max_left _ _).trans ht)
  obtain ⟨hne₂, hb₂⟩ := h₂ d.dual (by simpa using hd) hR_dual hC_dual (1 - s) hs1
    (by rw [him1]; exact (le_max_right _ _).trans ht)
  refine ⟨hne₁, hne₂, ?_⟩
  rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hne₂) (norm_ne_zero_iff.2 hne₁)]
  simp only [degree_dual, sub_re, one_re, him1, gammaLogExponent_dual] at hb₂
  have hexp_cancel :
      Real.log ‖d.dual.gammaFactor (1 - s)‖ - Real.log ‖d.gammaFactor s‖ -
        ((d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|) =
      (Real.log ‖d.dual.gammaFactor (1 - s)‖ -
        (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent (1 - s.re) * Real.log |s.im|)) -
      (Real.log ‖d.gammaFactor s‖ -
        (-(Real.pi * d.degree / 4) * |s.im| + d.gammaLogExponent s.re * Real.log |s.im|)) := by
    rw [← d.gammaLogExponent_one_sub_sub s.re]
    ring
  rw [hexp_cancel]
  exact (abs_sub _ _).trans (by linarith)

/-- Uniform vertical-strip bound for `log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` on
`Re s ∈ [a, b]`. -/
theorem exists_abs_log_norm_dual_gammaFactor_div_le (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C ≥ 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      d.gammaFactor s ≠ 0 ∧ d.dual.gammaFactor (1 - s) ≠ 0 ∧
      |Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ -
          ((d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|)| ≤ C := by
  obtain ⟨M, hM0, hR, hC⟩ := d.exists_shift_norm_le
  obtain ⟨C, hC0, T, hT0, h⟩ :=
    exists_abs_log_norm_dual_gammaFactor_div_le_of_norm_le a b d.degree hM0
  exact ⟨C, hC0, T, hT0, h d rfl hR hC⟩

/-- **Dual gamma-quotient asymptotic on vertical strips**:
`log ‖d.dual.gammaFactor (1 - (σ + i t)) / d.gammaFactor (σ + i t)‖ =
  (d.degree / 2) * (1 - 2 σ) * log |t| + O(1)` uniformly for `σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_vertical_sub (d : AnalyticLFunctionData) (a b : ℝ) :
    (fun p : ℝ × ℝ ↦
        Real.log ‖d.dual.gammaFactor (1 - (p.1 + p.2 * I)) / d.gammaFactor (p.1 + p.2 * I)‖ -
          (d.degree : ℝ) / 2 * (1 - 2 * p.1) * Real.log |p.2|)
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_dual_gammaFactor_div_le a b
  refine isBigO_one_vertical_of_exists ⟨C, T, fun p hσ ht ↦ ?_⟩
  simpa using (h (p.1 + p.2 * I) (by simpa using hσ) (by simpa using ht)).2.2

/-- **Dual gamma-quotient asymptotic** as a function of `s` on `Re s ∈ [a, b]`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_vertical_strip_sub (d : AnalyticLFunctionData)
    (a b : ℝ) :
    (fun s : ℂ ↦ Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ -
        (d.degree : ℝ) / 2 * (1 - 2 * s.re) * Real.log |s.im|)
      =O[cocompact ℂ ⊓ 𝓟 (re ⁻¹' Icc a b)] fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, -, T, -, h⟩ := d.exists_abs_log_norm_dual_gammaFactor_div_le a b
  exact isBigO_one_vertical_strip_of_exists ⟨C, T, fun s hs ht ↦ (h s hs ht).2.2⟩

/-- Dual gamma-quotient asymptotic on a vertical line `Re s = σ`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_vertical_line_sub (d : AnalyticLFunctionData)
    (σ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖d.dual.gammaFactor (1 - (σ + t * I)) / d.gammaFactor (σ + t * I)‖ -
        (d.degree : ℝ) / 2 * (1 - 2 * σ) * Real.log |t|)
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) :=
  TauCeti.isBigO_cocompact_of_vertical (d.isBigO_log_norm_dual_gammaFactor_div_vertical_sub σ σ)

/-- **Dual gamma-quotient asymptotic on `Re s = -δ`**:
`log ‖d.dual.gammaFactor (1 - (-δ + i t)) / d.gammaFactor (-δ + i t)‖ =
  (d.degree / 2) * (1 + 2 δ) * log |t| + O(1)` as `|t| → ∞`. -/
theorem isBigO_log_norm_dual_gammaFactor_div_neg_line_sub (d : AnalyticLFunctionData) (δ : ℝ) :
    (fun t : ℝ ↦
        Real.log ‖d.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
            d.gammaFactor ((-δ : ℝ) + t * I)‖ -
          (d.degree : ℝ) / 2 * (1 + 2 * δ) * Real.log |t|)
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  simpa only [sub_neg_eq_add, mul_neg] using
    d.isBigO_log_norm_dual_gammaFactor_div_vertical_line_sub (-δ)

/-! ### Polynomial norm bounds and comparison with `analyticConductorAt` -/

/-- Two-sided polynomial norm bounds for `‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` on
`Re s ∈ [a, b]` above the pole heights, uniform across all records of degree `n` with shifts
bounded in norm by `M`. -/
theorem exists_norm_dual_gammaFactor_div_bounds_of_norm_le (a b : ℝ) (n : ℕ) {M : ℝ}
    (hM : 0 ≤ M) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
        C₁ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) ≤
          ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ∧
        ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ≤
          C₂ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) := by
  obtain ⟨C, -, T, hT0, h⟩ := exists_abs_log_norm_dual_gammaFactor_div_le_of_norm_le a b n hM
  refine ⟨Real.exp (-C), Real.exp_pos _, Real.exp C, Real.exp_pos _, T, hT0,
    fun d hd hR hC s hs ht ↦ ?_⟩
  obtain ⟨hne₁, hne₂, hlog⟩ := h d hd hR hC s hs ht
  have ht_pos : 0 < |s.im| := hT0.trans_le ht
  have hq_pos : 0 < ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ :=
    norm_pos_iff.2 (div_ne_zero hne₂ hne₁)
  obtain ⟨hl, hu⟩ := abs_le.1 hlog
  set e := (d.degree : ℝ) / 2 * (1 - 2 * s.re)
  have hexp_e : Real.exp (e * Real.log |s.im|) = |s.im| ^ e := by
    rw [Real.rpow_def_of_pos ht_pos, mul_comm]
  constructor
  · calc Real.exp (-C) * |s.im| ^ e
        = Real.exp (-C + e * Real.log |s.im|) := by rw [← hexp_e, Real.exp_add]
      _ ≤ Real.exp (Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖) :=
          Real.exp_le_exp.2 (by linarith)
      _ = ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ := Real.exp_log hq_pos
  · calc ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖
        = Real.exp (Real.log ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖) :=
          (Real.exp_log hq_pos).symm
      _ ≤ Real.exp (C + e * Real.log |s.im|) := Real.exp_le_exp.2 (by linarith)
      _ = Real.exp C * |s.im| ^ e := by rw [← hexp_e, Real.exp_add]

/-- Single-record two-sided polynomial norm bounds for
`‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` on `Re s ∈ [a, b]`. -/
theorem exists_norm_dual_gammaFactor_div_bounds (d : AnalyticLFunctionData) (a b : ℝ) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∃ T > 0, ∀ s : ℂ, s.re ∈ Icc a b → T ≤ |s.im| →
      C₁ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) ≤
        ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ∧
      ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖ ≤
        C₂ * |s.im| ^ ((d.degree : ℝ) / 2 * (1 - 2 * s.re)) := by
  obtain ⟨M, hM0, hR, hC⟩ := d.exists_shift_norm_le
  obtain ⟨C₁, hC₁, C₂, hC₂, T, hT, h⟩ :=
    exists_norm_dual_gammaFactor_div_bounds_of_norm_le a b d.degree hM0
  exact ⟨C₁, hC₁, C₂, hC₂, T, hT, h d rfl hR hC⟩

/-- **Conductor-uniform functional-equation factor bound on vertical strips**: for `a : ℝ`, degree
`n`, and shift norm bound `M`, there exist `C > 0` and `T > 0` (independent of `d` and
`d.conductor`) such that for every `s` with `s.re ∈ [a, 1 / 2]` and `T ≤ |s.im|`,
`‖N ^ (1 / 2 - s) (γ^∨(1 - s) / γ(s))‖ ≤ C * d.analyticConductorAt s ^ (1 / 2 - s.re)`. -/
theorem exists_norm_conductor_cpow_mul_dual_gammaFactor_div_le_analyticConductorAt (a : ℝ)
    (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∃ T > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M) → (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M) →
      ∀ s : ℂ, s.re ∈ Icc a (1 / 2) → T ≤ |s.im| →
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s) *
            (d.dual.gammaFactor (1 - s) / d.gammaFactor s)‖ ≤
          C * d.analyticConductorAt s ^ (1 / 2 - s.re) := by
  obtain ⟨_, _, C₂, hC₂, T, hT0, hbounds⟩ :=
    exists_norm_dual_gammaFactor_div_bounds_of_norm_le a (1 / 2) n hM
  have hM2_one : (1 : ℝ) ≤ (M + 2) ^ n := one_le_pow₀ (by linarith)
  refine ⟨C₂ * ((M + 2) ^ n) ^ (1 / 2 - a), by positivity, T, hT0,
    fun d hd hR hC s hs ht ↦ ?_⟩
  set e : ℝ := 1 / 2 - s.re
  have he_nonneg : 0 ≤ e := sub_nonneg.2 hs.2
  have he_le : e ≤ 1 / 2 - a := sub_le_sub_left hs.1 _
  have hcond_norm : ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖ = (d.conductor : ℝ) ^ e := by
    rw [Complex.norm_natCast_cpow_of_pos d.conductor.pos]
    congr 1
    simp [e]
  have hq := (hbounds d hd hR hC s hs ht).2
  have hexp_eq : (d.degree : ℝ) / 2 * (1 - 2 * s.re) = (n : ℝ) * e := by
    rw [hd]; dsimp only [e]; ring
  rw [hexp_eq] at hq
  have him_le : |s.im| ^ ((n : ℝ) * e) ≤ ((|s.im| + 3) ^ n) ^ e := calc
    |s.im| ^ ((n : ℝ) * e) ≤ (|s.im| + 3) ^ ((n : ℝ) * e) :=
      Real.rpow_le_rpow (abs_nonneg _) (by linarith) (mul_nonneg (Nat.cast_nonneg n) he_nonneg)
    _ = ((|s.im| + 3) ^ n) ^ e := by rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
  have hN_height := d.conductor_mul_height_pow_le hM hR hC s
  rw [hd] at hN_height
  have hcond_nn : 0 ≤ d.analyticConductorAt s := (d.analyticConductorAt_pos s).le
  have hrpow_cond : (d.conductor : ℝ) ^ e * ((|s.im| + 3) ^ n) ^ e ≤
      ((M + 2) ^ n) ^ (1 / 2 - a) * d.analyticConductorAt s ^ e := by
    calc (d.conductor : ℝ) ^ e * ((|s.im| + 3) ^ n) ^ e
        = ((d.conductor : ℝ) * (|s.im| + 3) ^ n) ^ e :=
          (Real.mul_rpow (Nat.cast_nonneg _) (by positivity)).symm
      _ ≤ ((M + 2) ^ n * d.analyticConductorAt s) ^ e :=
          Real.rpow_le_rpow (by positivity) hN_height he_nonneg
      _ = ((M + 2) ^ n) ^ e * d.analyticConductorAt s ^ e :=
          Real.mul_rpow (by positivity) hcond_nn
      _ ≤ ((M + 2) ^ n) ^ (1 / 2 - a) * d.analyticConductorAt s ^ e :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hM2_one he_le)
            (Real.rpow_nonneg hcond_nn e)
  rw [norm_mul, hcond_norm]
  calc (d.conductor : ℝ) ^ e * ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖
      ≤ (d.conductor : ℝ) ^ e * (C₂ * ((|s.im| + 3) ^ n) ^ e) :=
        mul_le_mul_of_nonneg_left (hq.trans (mul_le_mul_of_nonneg_left him_le hC₂.le))
          (by positivity)
    _ = C₂ * ((d.conductor : ℝ) ^ e * ((|s.im| + 3) ^ n) ^ e) := by ring
    _ ≤ C₂ * (((M + 2) ^ n) ^ (1 / 2 - a) * d.analyticConductorAt s ^ e) :=
        mul_le_mul_of_nonneg_left hrpow_cond hC₂.le
    _ = C₂ * ((M + 2) ^ n) ^ (1 / 2 - a) * d.analyticConductorAt s ^ e := by ring

/-- Uniform bound on `‖d.invGammaFactor s‖` when `‖s + μ‖ ≤ R` and `‖s + ν‖ ≤ R` for all shifts. -/
private theorem exists_norm_invGammaFactor_le_of_norm_le (n : ℕ) (R : ℝ) :
    ∃ B > 0, ∀ d : AnalyticLFunctionData, d.degree = n → ∀ s : ℂ,
      (∀ μ ∈ d.gammaR, ‖s + μ‖ ≤ R) → (∀ ν ∈ d.gammaC, ‖s + ν‖ ≤ R) →
        ‖d.invGammaFactor s‖ ≤ B := by
  set K : Set ℂ := Metric.closedBall 0 R
  obtain ⟨bR, hbR⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (f := fun w : ℂ ↦ (Gammaℝ w)⁻¹) differentiable_Gammaℝ_inv.continuous.continuousOn
  obtain ⟨bC, hbC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (f := fun w : ℂ ↦ (Gammaℂ w)⁻¹) differentiable_Gammaℂ_inv.continuous.continuousOn
  set U := max 1 (max bR bC)
  have hU1 : 1 ≤ U := le_max_left _ _
  refine ⟨U ^ n, by positivity, fun d hd s hR hC ↦ ?_⟩
  rw [d.invGammaFactor_eq_prod, norm_mul]
  have hpR := norm_multiset_prod_le_pow d.gammaR (fun μ ↦ (Gammaℝ (s + μ))⁻¹) U fun μ hμ ↦
    (hbR _ (by simpa [K] using hR μ hμ)).trans ((le_max_left bR bC).trans (le_max_right _ _))
  have hpC := norm_multiset_prod_le_pow d.gammaC (fun ν ↦ (Gammaℂ (s + ν))⁻¹) U fun ν hν ↦
    (hbC _ (by simpa [K] using hC ν hν)).trans ((le_max_right bR bC).trans (le_max_right _ _))
  have hcard : d.gammaR.card + d.gammaC.card ≤ n := by rw [← hd, degree_def]; omega
  exact (mul_le_mul hpR hpC (norm_nonneg _) (by positivity)).trans
    ((pow_add U d.gammaR.card d.gammaC.card).symm.le.trans (pow_le_pow_right₀ hU1 hcard))

/-- Uniform bound on `‖d.gammaFactor w‖` when all shifted arguments lie in
`Metric.closedBall 0 R ∩ {z | ε ≤ z.re}` (`ε > 0`). -/
private theorem exists_norm_gammaFactor_le_of_re_ge {ε : ℝ} (hε : 0 < ε) (n : ℕ) (R : ℝ) :
    ∃ B > 0, ∀ d : AnalyticLFunctionData, d.degree = n → ∀ w : ℂ,
      (∀ μ ∈ d.gammaR, ‖w + μ‖ ≤ R ∧ ε ≤ (w + μ).re) →
      (∀ ν ∈ d.gammaC, ‖w + ν‖ ≤ R ∧ ε ≤ (w + ν).re) →
        ‖d.gammaFactor w‖ ≤ B := by
  set K : Set ℂ := Metric.closedBall 0 R ∩ {z : ℂ | ε ≤ z.re}
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right
    (isClosed_le continuous_const Complex.continuous_re)
  obtain ⟨dR, hdR⟩ := hK.exists_bound_of_continuousOn (f := Gammaℝ) fun z hz ↦
    (continuousAt_Gammaℝ (Gammaℝ_ne_zero_of_re_pos (hε.trans_le hz.2))).continuousWithinAt
  obtain ⟨dC, hdC⟩ := hK.exists_bound_of_continuousOn (f := Gammaℂ) fun z hz ↦
    (continuousAt_Gammaℂ (Gammaℂ_ne_zero_of_re_pos (hε.trans_le hz.2))).continuousWithinAt
  set U := max 1 (max dR dC)
  have hU1 : 1 ≤ U := le_max_left _ _
  refine ⟨U ^ n, by positivity, fun d hd w hR hC ↦ ?_⟩
  rw [gammaFactor_def, norm_mul]
  have hpR := norm_multiset_prod_le_pow d.gammaR (fun μ ↦ Gammaℝ (w + μ)) U fun μ hμ ↦
    (hdR _ ⟨by simpa using (hR μ hμ).1, (hR μ hμ).2⟩).trans
      ((le_max_left dR dC).trans (le_max_right _ _))
  have hpC := norm_multiset_prod_le_pow d.gammaC (fun ν ↦ Gammaℂ (w + ν)) U fun ν hν ↦
    (hdC _ ⟨by simpa using (hC ν hν).1, (hC ν hν).2⟩).trans
      ((le_max_right dR dC).trans (le_max_right _ _))
  have hcard : d.gammaR.card + d.gammaC.card ≤ n := by rw [← hd, degree_def]; omega
  exact (mul_le_mul hpR hpC (norm_nonneg _) (by positivity)).trans
    ((pow_add U d.gammaR.card d.gammaC.card).symm.le.trans (pow_le_pow_right₀ hU1 hcard))

/-- Compact-height helper: on `|t| ≤ T` along `Re s = -δ`, if every shifted parameter satisfies
`ε ≤ 1 + δ + Re μ` (`ε > 0`), then `‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖` is bounded by a
constant depending only on `δ`, `ε`, `n`, `M`, and `T`. -/
private theorem exists_compact_dual_gammaFactor_div_bound {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (n : ℕ) (M T : ℝ) :
    ∃ B > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 + δ + ν.re) →
      ∀ t : ℝ, |t| ≤ T →
        ‖d.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
            d.gammaFactor ((-δ : ℝ) + t * I)‖ ≤ B := by
  obtain ⟨B₁, hB₁, hinv⟩ := exists_norm_invGammaFactor_le_of_norm_le n (δ + T + M)
  obtain ⟨B₂, hB₂, hgam⟩ := exists_norm_gammaFactor_le_of_re_ge hε n (1 + δ + T + M)
  refine ⟨B₂ * B₁, mul_pos hB₂ hB₁, fun d hd hR hC t ht ↦ ?_⟩
  set s : ℂ := (-δ : ℝ) + t * I
  have hs_norm : ‖s‖ ≤ δ + T :=
    (norm_add_le _ _).trans (by simpa [abs_of_pos hδ] using add_le_add_left ht δ)
  have h1s_norm : ‖1 - s‖ ≤ 1 + δ + T :=
    (norm_sub_le 1 s).trans (by rw [norm_one]; linarith)
  have hinv_s := hinv d hd s
    (fun μ hμ ↦ (norm_add_le s μ).trans (add_le_add hs_norm (hR μ hμ).1))
    (fun ν hν ↦ (norm_add_le s ν).trans (add_le_add hs_norm (hC ν hν).1))
  have hdual_mem {μ : ℂ} (h : ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) :
      ‖1 - s + conj μ‖ ≤ 1 + δ + T + M ∧ ε ≤ (1 - s + conj μ).re :=
    ⟨(norm_add_le (1 - s) (conj μ)).trans (add_le_add h1s_norm (by simpa using h.1)),
      by simpa [s] using h.2⟩
  have hgam_s := hgam d.dual (by simpa using hd) (1 - s)
    (fun μ' hμ' ↦ by
      rw [dual_gammaR] at hμ'
      obtain ⟨μ, hμ, rfl⟩ := Multiset.mem_map.mp hμ'
      exact hdual_mem (hR μ hμ))
    (fun ν' hν' ↦ by
      rw [dual_gammaC] at hν'
      obtain ⟨ν, hν, rfl⟩ := Multiset.mem_map.mp hν'
      exact hdual_mem (hC ν hν))
  rw [div_eq_mul_inv, ← d.invGammaFactor_def, norm_mul]
  exact mul_le_mul hgam_s hinv_s (norm_nonneg _) hB₂.le

/-- **All-height conductor-uniform edge bound on `Re s = -δ`** (`δ > 0`): when the reflected shifts
stay a positive distance `ε` inside the right half-plane (`ε ≤ 1 + δ + Re μ`), there is a single
constant `C > 0` depending only on `δ`, `ε`, `n`, and `M` (independent of `d` and `d.conductor`)
such that for **every** `t : ℝ`,
`‖N ^ (1 / 2 - (-δ + i t)) (γ^∨(1 - (-δ + i t)) / γ(-δ + i t))‖ ≤
  C * d.analyticConductorAt (-δ + i t) ^ (1 / 2 + δ)`. -/
theorem exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ ε ≤ 1 + δ + μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ ε ≤ 1 + δ + ν.re) →
      ∀ t : ℝ,
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - ((-δ : ℝ) + t * I)) *
            (d.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
              d.gammaFactor ((-δ : ℝ) + t * I))‖ ≤
          C * d.analyticConductorAt ((-δ : ℝ) + t * I) ^ (1 / 2 + δ) := by
  obtain ⟨C_tail, hCt, T, _, htail⟩ :=
    exists_norm_conductor_cpow_mul_dual_gammaFactor_div_le_analyticConductorAt (-δ) n hM
  obtain ⟨B, _, hcomp⟩ := exists_compact_dual_gammaFactor_div_bound hδ hε n M T
  refine ⟨max C_tail B, lt_of_lt_of_le hCt (le_max_left _ _), fun d hd hR hC t ↦ ?_⟩
  set s : ℂ := (-δ : ℝ) + t * I
  have hsre : s.re = -δ := by simp [s]
  have hsim : s.im = t := by simp [s]
  have : 0 < d.analyticConductorAt s := d.analyticConductorAt_pos s
  rcases le_total T |t| with ht | ht
  · have h := htail d hd (fun μ hμ ↦ (hR μ hμ).1) (fun ν hν ↦ (hC ν hν).1) s
      ⟨by linarith [hsre], by linarith [hsre]⟩ (by rwa [hsim])
    rw [hsre, sub_neg_eq_add] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hq := hcomp d hd hR hC t ht
    have hcond_norm : ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)‖ =
        (d.conductor : ℝ) ^ (1 / 2 + δ) := by
      rw [Complex.norm_natCast_cpow_of_pos d.conductor.pos]
      congr 1
      simp [hsre, sub_neg_eq_add]
    have hcond_le : (d.conductor : ℝ) ^ (1 / 2 + δ) ≤
        d.analyticConductorAt s ^ (1 / 2 + δ) := by
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by positivity)
      have h1 : (1 : ℝ) ≤ 3 ^ d.degree := one_le_pow₀ (by norm_num)
      exact (le_mul_of_one_le_right (Nat.cast_nonneg _) h1).trans
        (d.conductor_mul_three_pow_degree_le s)
    rw [norm_mul, hcond_norm]
    calc (d.conductor : ℝ) ^ (1 / 2 + δ) * ‖d.dual.gammaFactor (1 - s) / d.gammaFactor s‖
        ≤ d.analyticConductorAt s ^ (1 / 2 + δ) * B :=
          mul_le_mul hcond_le hq (norm_nonneg _) (by positivity)
      _ = B * d.analyticConductorAt s ^ (1 / 2 + δ) := mul_comm _ _
      _ ≤ max C_tail B * d.analyticConductorAt s ^ (1 / 2 + δ) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- Specialization of `exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le` to records
whose gamma shifts have nonnegative real parts (`0 ≤ Re μ`, `0 ≤ Re ν`), covering Riemann zeta,
Dirichlet characters, Dedekind zeta, unitary Hecke characters, and holomorphic newforms. -/
theorem exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le_of_re_nonneg {δ : ℝ}
    (hδ : 0 < δ) (n : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C > 0, ∀ d : AnalyticLFunctionData, d.degree = n →
      (∀ μ ∈ d.gammaR, ‖μ‖ ≤ M ∧ 0 ≤ μ.re) →
      (∀ ν ∈ d.gammaC, ‖ν‖ ≤ M ∧ 0 ≤ ν.re) →
      ∀ t : ℝ,
        ‖((d.conductor : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - ((-δ : ℝ) + t * I)) *
            (d.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
              d.gammaFactor ((-δ : ℝ) + t * I))‖ ≤
          C * d.analyticConductorAt ((-δ : ℝ) + t * I) ^ (1 / 2 + δ) := by
  obtain ⟨C, hC, h⟩ :=
    exists_norm_conductor_cpow_mul_dual_gammaFactor_div_neg_line_le hδ one_pos n hM
  exact ⟨C, hC, fun d hd hR hC' t ↦ h d hd
    (fun μ hμ ↦ ⟨(hR μ hμ).1, by linarith [(hR μ hμ).2]⟩)
    (fun ν hν ↦ ⟨(hC' ν hν).1, by linarith [(hC' ν hν).2]⟩) t⟩

end AnalyticLFunctionData

/-! ### Normalization translation, `riemannZetaData`, and worked checks -/

/-- Translating an arithmetic record of weight `w` to the analytic normalization shifts
`gammaLogExponent` by `+w / 2`, matching `NormalizationTranslation.analytic_analyticConductorAt`. -/
@[simp]
theorem NormalizationTranslation.analytic_gammaLogExponent (T : NormalizationTranslation)
    (σ : ℝ) :
    T.analytic.gammaLogExponent σ =
      T.arithmetic.toAnalyticLFunctionData.gammaLogExponent (σ + (T.weight : ℝ) / 2) := by
  simp only [AnalyticLFunctionData.gammaLogExponent_def, T.gammaR_eq, T.gammaC_eq,
    Multiset.map_map, Function.comp_def]
  congr 1 <;> congr 1 <;> refine Multiset.map_congr rfl fun z _ ↦ ?_ <;> simp <;> ring

/-- For the Riemann zeta record (`gammaR = {0}`, `gammaC = 0`), the logarithmic height exponent is
`(σ - 1) / 2`. -/
@[simp]
theorem riemannZetaData_gammaLogExponent (σ : ℝ) :
    riemannZetaData.gammaLogExponent σ = (σ - 1) / 2 := by
  simp [AnalyticLFunctionData.gammaLogExponent_def]

/-- Vertical-strip asymptotic of `riemannZetaData.gammaFactor`:
`log ‖Gammaℝ (σ + i t)‖ = -(π / 4) |t| + ((σ - 1) / 2) log |t| + O(1)` uniformly for
`σ ∈ [a, b]` as `|t| → ∞`. -/
theorem isBigO_log_norm_riemannZetaData_gammaFactor_vertical_sub (a b : ℝ) :
    (fun p : ℝ × ℝ ↦ Real.log ‖Gammaℝ (p.1 + p.2 * I)‖ -
        (-(Real.pi / 4) * |p.2| + (p.1 - 1) / 2 * Real.log |p.2|))
      =O[𝓟 (Icc a b) ×ˢ cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  simpa using riemannZetaData.isBigO_log_norm_gammaFactor_vertical_sub a b

/-- Dual gamma-quotient asymptotic for `riemannZetaData` on `Re s = -δ`:
`log ‖Gammaℝ (1 - (-δ + i t)) / Gammaℝ (-δ + i t)‖ = ((1 + 2 δ) / 2) log |t| + O(1)`. -/
theorem isBigO_log_norm_riemannZetaData_dual_gammaFactor_div_neg_line_sub (δ : ℝ) :
    (fun t : ℝ ↦ Real.log ‖Gammaℝ (1 - ((-δ : ℝ) + t * I)) / Gammaℝ ((-δ : ℝ) + t * I)‖ -
        (1 + 2 * δ) / 2 * Real.log |t|)
      =O[cocompact ℝ] fun _ ↦ (1 : ℝ) := by
  have heq : (fun t : ℝ ↦ Real.log ‖Gammaℝ (1 - ((-δ : ℝ) + t * I)) / Gammaℝ ((-δ : ℝ) + t * I)‖ -
      (1 + 2 * δ) / 2 * Real.log |t|) =
      (fun t : ℝ ↦
        Real.log ‖riemannZetaData.dual.gammaFactor (1 - ((-δ : ℝ) + t * I)) /
            riemannZetaData.gammaFactor ((-δ : ℝ) + t * I)‖ -
          (riemannZetaData.degree : ℝ) / 2 * (1 + 2 * δ) * Real.log |t|) := by
    funext t
    simp only [riemannZetaData_dual, riemannZetaData_gammaFactor, riemannZetaData_degree,
      Nat.cast_one]
    ring
  rw [heq]
  exact riemannZetaData.isBigO_log_norm_dual_gammaFactor_div_neg_line_sub δ

-- Duplication check: two real gamma factors with shifts `{0, 1}` interleave into one `Gammaℂ`
-- factor, giving degree `2` (exponential rate `-π |t| / 2`), logarithmic exponent `σ - 1 / 2`,
-- and divisor `-1` at every nonpositive integer.
example (d : AnalyticLFunctionData) (hR : d.gammaR = {0, 1}) (hC : d.gammaC = 0) :
    d.degree = 2 ∧
    (∀ σ : ℝ, d.gammaLogExponent σ = σ - 1 / 2) ∧
    (∀ s : ℂ, d.gammaFactor s = Gammaℂ s) ∧
    (∀ m : ℕ, MeromorphicOn.divisor d.gammaFactor Set.univ (-(m : ℂ)) = -1) := by
  refine ⟨by simp [AnalyticLFunctionData.degree_def, hR, hC], fun σ ↦ ?_, fun s ↦ ?_, fun m ↦ ?_⟩
  · simp [AnalyticLFunctionData.gammaLogExponent_def, hR, hC]
    ring
  · simp [AnalyticLFunctionData.gammaFactor_def, hR, hC, Gammaℝ_mul_Gammaℝ_add_one]
  · have hfg : d.gammaFactor = Gammaℂ := funext fun s ↦ by
      simp [AnalyticLFunctionData.gammaFactor_def, hR, hC, Gammaℝ_mul_Gammaℝ_add_one]
    rw [hfg, meromorphicOn_Gammaℂ.divisor_apply (Set.mem_univ _),
      (meromorphicOrderAt_Gammaℂ_eq_neg_one_iff _).2 ⟨m, rfl⟩]
    rfl

end TauCeti.LFunctions
