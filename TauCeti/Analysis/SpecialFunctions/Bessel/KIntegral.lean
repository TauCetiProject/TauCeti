/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Contour.Residue.ChangeOfVariables
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Residue
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic
import TauCeti.Analysis.SpecialFunctions.MacdonaldIntegral
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The integral `∫₀^∞ s^{p-1} e^{-s - x/s} ds` as a series

For `x > 0` and real `p` the integral

`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = 2 x^{p/2} K_p(2 √x)`

is the Macdonald function in the reduced form of DLMF 10.32.10. This file proves that for
`0 < p < 1` it is the combination of reduced Bessel series

`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = (π / sin pπ) (𝐅(1 - p, x) - x^p 𝐅(1 + p, x))`,

where `𝐅(b, x) = ∑ₙ xⁿ / (n! Γ(b + n))` is Mathlib's regularized `₀F₁`,
`Complex.regularizedHGFun 0 {b}`. In Bessel notation this is
`K_p = π (I_{-p} - I_p) / (2 sin pπ)` (DLMF 10.27.4) at the argument `2 √x`, with
`I_{±p}(2 √x) = x^{±p/2} 𝐅(1 ± p, x)`. Integrals of this shape arise from
`∫₀^∞ e^{-ζ cosh u} cosh(pu) du` by the substitution `s = (ζ/2) eᵘ`, with `x = ζ²/4`; this is how
integral representations of the form `z^{1/2} ∫₀^∞ e^{-ζ cosh u} cosh(pu) du`, such as that of
the generalized Airy functions with `p = 1/(n + 2)`, reduce to series in `𝐅`.

The proof is by Mellin transforms. The Mellin transform of the integral in `x` is
`Γ(t) Γ(t + p)` (DLMF 10.43.19 in reduced form), and
`Complex.mellinInv_Gamma_mul_Gamma_add` in `TauCeti.Analysis.SpecialFunctions.MacdonaldIntegral`
recovers the integral by Mellin inversion on the line `Re t = 1`. This file shifts that line to
`Re t = δ - N` with `δ = (1 - p)/2`, crossing the simple poles at `t = -k` and `t = -p - k` for
`k < N`. Their residues are the terms of the two series, by the reflection formula, and the
integral over the shifted line tends to `0` as `N → ∞`, since `Γ` decays like `1/N!` across a
vertical line `N` units to the left of the strip `0 < Re t < 1`.

## Main results

* `Complex.integral_cpow_mul_exp_neg_add_div_Ioi`: the series evaluation above for `0 < p < 1`.

## References

* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §3.7 (6) and §6.22 (15).
* *NIST Digital Library of Mathematical Functions*, 10.27.4, 10.32.10 and 10.43.19,
  <https://dlmf.nist.gov/10>.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Real Nat Topology
open Complex hiding exp continuous_exp

namespace Complex

/-! ### Residues of `x^{-t} Γ(t) Γ(t + p)` -/

/-- For `0 < p < 1`, no pole `-k - p` of `Γ(t + p)` is a pole `-n` of `Γ(t)`. -/
private lemma neg_natCast_sub_ofReal_ne_neg_natCast {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (k n : ℕ) : -(k : ℂ) - p ≠ -n := fun h ↦
  Real.sub_natCast_ne_neg_natCast hp0 hp1 n k (by
    have := congrArg re h
    simp only [sub_re, neg_re, natCast_re, ofReal_re] at this
    linarith)

/-- The residue of `x^{-t} Γ(t) Γ(t + p)` at the pole `t = -k` of `Γ(t)`, written through the
reflection formula as the `k`th term of `(π / sin pπ) 𝐅(1 - p, x)`. -/
private lemma residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_natCast {p x : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hx : 0 < x) (k : ℕ) :
    TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) (-(k : ℂ)) =
      ((π / Real.sin (π * p) : ℝ) : ℂ) * ((x ^ k / (k ! * Real.Gamma (1 - p + k)) : ℝ) : ℂ) := by
  have hslit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hΓp : ∀ n : ℕ, -(k : ℂ) + p ≠ -n := fun n h ↦
    neg_natCast_sub_ofReal_ne_neg_natCast hp0 hp1 n k (by linear_combination -h)
  have hw : AnalyticAt ℂ (fun z ↦ (x : ℂ) ^ (-z) * Gamma (z + p)) (-(k : ℂ)) :=
    (analyticAt_const.cpow (by fun_prop) hslit).mul
      ((analyticAt_Gamma hΓp).comp (f := fun z : ℂ ↦ z + p) (x := -(k : ℂ)) (by fun_prop))
  have hfun : (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) =
      fun z ↦ Gamma z * ((x : ℂ) ^ (-z) * Gamma (z + p)) := funext fun z ↦ by ring
  rw [hfun, residue_Gamma_mul_neg_nat k hw, neg_neg, cpow_natCast,
    show -(k : ℂ) + p = ((p - k : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal]
  have hsin : Real.sin (π * p) ≠ 0 := (TauCeti.sin_pi_mul_pos_of_pos_of_lt_one hp0 hp1).ne'
  have hreal : (-1) ^ k / (k ! : ℝ) * (x ^ k * Real.Gamma (p - k)) =
      π / Real.sin (π * p) * (x ^ k / (k ! * Real.Gamma (1 - p + k))) := by
    rw [mul_left_comm, Real.neg_one_pow_div_factorial_mul_Gamma_sub_natCast hsin]
    ring
  exact_mod_cast hreal

/-- The residue of `x^{-t} Γ(t) Γ(t + p)` at the pole `t = -p - k` of `Γ(t + p)`, written through
the reflection formula as the `k`th term of `-(π / sin pπ) x^p 𝐅(1 + p, x)`. -/
private lemma residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_natCast {p x : ℝ} (hp0 : 0 < p)
    (hp1 : p < 1) (hx : 0 < x) (k : ℕ) :
    TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) (-(p : ℂ) - k) =
      -(((π / Real.sin (π * p) : ℝ) : ℂ) * (x : ℂ) ^ (p : ℂ)) *
        ((x ^ k / (k ! * Real.Gamma (1 + p + k)) : ℝ) : ℂ) := by
  have hslit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hΓ : ∀ n : ℕ, -(k : ℂ) - p ≠ -n := neg_natCast_sub_ofReal_ne_neg_natCast hp0 hp1 k
  have hw : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-(w - p)) * Gamma (w - p)) (-(k : ℂ)) :=
    (analyticAt_const.cpow (by fun_prop) hslit).mul
      ((analyticAt_Gamma hΓ).comp (f := fun w : ℂ ↦ w - p) (x := -(k : ℂ)) (by fun_prop))
  -- translate by `p`, moving the pole `-p - k` of `Γ(t + p)` to the pole `-k` of `Γ`
  have hfun : (fun z ↦ (x : ℂ) ^ (-z) * (Gamma z * Gamma (z + p))) =
      fun z ↦ Gamma (z + p) * ((x : ℂ) ^ (-(z + p - p)) * Gamma (z + p - p)) :=
    funext fun z ↦ by rw [add_sub_cancel_right]; ring
  rw [hfun, TauCeti.Contour.residue_comp_add_const
      (fun w : ℂ ↦ Gamma w * ((x : ℂ) ^ (-(w - p)) * Gamma (w - p))) (p : ℂ),
    show -(p : ℂ) - k + p = -(k : ℂ) by ring, residue_Gamma_mul_neg_nat k hw,
    show -(-(k : ℂ) - p) = p + k by ring, cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'),
    cpow_natCast, show -(k : ℂ) - p = ((-p - k : ℝ) : ℂ) by push_cast; ring, Gamma_ofReal]
  have hsin : Real.sin (π * -p) ≠ 0 := by
    rw [mul_neg, Real.sin_neg, neg_ne_zero]
    exact (TauCeti.sin_pi_mul_pos_of_pos_of_lt_one hp0 hp1).ne'
  have hreal : (-1) ^ k / (k ! : ℝ) * (x ^ k * Real.Gamma (-p - k)) =
      -(π / Real.sin (π * p)) * (x ^ k / (k ! * Real.Gamma (1 + p + k))) := by
    rw [mul_left_comm, Real.neg_one_pow_div_factorial_mul_Gamma_sub_natCast hsin, mul_neg,
      Real.sin_neg, sub_neg_eq_add]
    ring
  have hc : ((-1 : ℂ) ^ k / (k ! : ℂ)) * ((x : ℂ) ^ k * ((Real.Gamma (-p - k) : ℝ) : ℂ)) =
      -((π / Real.sin (π * p) : ℝ) : ℂ) * ((x ^ k / (k ! * Real.Gamma (1 + p + k)) : ℝ) : ℂ) := by
    exact_mod_cast hreal
  linear_combination (x : ℂ) ^ (p : ℂ) * hc

/-! ### Shifting the Mellin inversion contour -/

/-- In the half-plane `Re t ≥ (1 - p)/2 - N`, the poles of `Γ(t) Γ(t + p)` are the points `-k` and
`-p - k` with `k < N`; away from them the product is analytic. -/
private lemma analyticAt_Gamma_mul_Gamma_add {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {N : ℕ}
    {z : ℂ} (hz : (1 - p) / 2 - N ≤ z.re) (hA : ∀ k < N, z ≠ -(k : ℂ))
    (hB : ∀ k < N, z ≠ -(p : ℂ) - k) :
    AnalyticAt ℂ (fun w ↦ Gamma w * Gamma (w + p)) z := by
  have hlt {n : ℕ} {c : ℝ} (hc : 0 ≤ c) (h : z.re = -(c + n)) : n < N := by
    have : (n : ℝ) < N := by linarith
    exact_mod_cast this
  have hΓ : ∀ n : ℕ, z ≠ -(n : ℂ) := fun n h ↦
    hA n (hlt le_rfl (by simp [h])) h
  have hΓp : ∀ n : ℕ, z + p ≠ -(n : ℂ) := fun n h ↦ by
    have hz' : z = -(p : ℂ) - n := by linear_combination h
    exact hB n (hlt hp0.le (by simp [hz']; ring)) hz'
  exact (analyticAt_Gamma hΓ).mul ((analyticAt_Gamma hΓp).comp (f := fun w : ℂ ↦ w + p)
    (by fun_prop))

/-- `Γ(t) Γ(t + p)` is integrable on the line `Re t = 1` for `0 ≤ p`. -/
private lemma verticalIntegrable_Gamma_mul_Gamma_add_one {p : ℝ} (hp : 0 ≤ p) :
    VerticalIntegrable (fun z ↦ Gamma z * Gamma (z + p)) 1 :=
  verticalIntegrable_Gamma_mul_Gamma_add
    (fun n h ↦ by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    (fun n h ↦ by rw [ofReal_re] at h; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

/-- Shifting the Mellin inversion integral of `Γ(t) Γ(t + p)` from `Re t = 1` to
`Re t = (1 - p)/2 - N` crosses the poles `t = -k` and `t = -p - k` for `k < N`. -/
private lemma mellinInv_Gamma_mul_Gamma_add_eq {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) (N : ℕ) :
    mellinInv 1 (fun z ↦ Gamma z * Gamma (z + p)) x =
      mellinInv ((1 - p) / 2 - N) (fun z ↦ Gamma z * Gamma (z + p)) x +
        ∑ k ∈ Finset.range N,
          (((π / Real.sin (π * p) : ℝ) : ℂ) * ((x ^ k / (k ! * Real.Gamma (1 - p + k)) : ℝ) : ℂ) +
            -(((π / Real.sin (π * p) : ℝ) : ℂ) * (x : ℂ) ^ (p : ℂ)) *
              ((x ^ k / (k ! * Real.Gamma (1 + p + k)) : ℝ) : ℂ)) := by
  set δ : ℝ := (1 - p) / 2 with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; linarith
  have hδp : δ + p < 1 := by rw [hδ_def]; linarith
  set A : Finset ℂ := (Finset.range N).image fun k : ℕ ↦ -(k : ℂ)
  set B : Finset ℂ := (Finset.range N).image fun k : ℕ ↦ -(p : ℂ) - k
  have hAB : Disjoint A B := by
    refine Finset.disjoint_left.mpr fun z hzA hzB ↦ ?_
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hzA
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hzB
    exact neg_natCast_sub_ofReal_ne_neg_natCast hp0 hp1 j k (by linear_combination hj)
  obtain ⟨C, -, hC⟩ := exists_norm_Gamma_mul_Gamma_add_le_div_pow_of_re_mem_Icc p (δ - N) 1 1
  have hshift := TauCeti.mellinInv_eq_mellinInv_add_sum_residue_of_norm_le (S := A ∪ B)
    (σ₀ := δ - N) (σ₁ := 1) (B := fun T ↦ C / T) (f := fun z ↦ Gamma z * Gamma (z + p))
    (by linarith) hx.le
    (fun z hz hzS ↦ analyticAt_Gamma_mul_Gamma_add hp0 hp1 hz.1
      (fun k hk h ↦ hzS (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr hk, h.symm⟩)))
      (fun k hk h ↦ hzS (Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨k, Finset.mem_range.mpr hk, h.symm⟩))))
    (fun z _ ↦ (Meromorphic.Gamma z).mul ((Meromorphic.Gamma _).comp_analyticAt
      (g := fun w : ℂ ↦ w + p) (by fun_prop))) ?_
    (verticalIntegrable_Gamma_mul_Gamma_add
      (Real.sub_natCast_ne_neg_natCast hδ0 (by linarith) N)
      (fun n ↦ by
        rw [ofReal_re, sub_add_eq_add_sub]
        exact Real.sub_natCast_ne_neg_natCast (by linarith) hδp N n))
    (verticalIntegrable_Gamma_mul_Gamma_add_one hp0.le)
    (tendsto_const_nhds.div_atTop tendsto_id)
    (by
      filter_upwards [eventually_ge_atTop 1] with T hT u hu
      have key (z : ℂ) (hz : z.re = u) (him : |z.im| = T) : ‖Gamma z * Gamma (z + p)‖ ≤ C / T := by
        simpa [him] using hC z (hz ▸ hu) (him ▸ hT)
      have hT0 : (0 : ℝ) < T := by linarith
      exact ⟨key _ (by simp) (by simp [abs_of_pos hT0]),
        key _ (by simp) (by simp [abs_of_pos hT0])⟩)
  · rw [hshift, Finset.sum_union hAB, Finset.sum_image (fun _ _ _ _ h ↦ by simpa using h),
      Finset.sum_image (fun _ _ _ _ h ↦ by simpa using h), ← Finset.sum_add_distrib]
    simp only [residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_natCast hp0 hp1 hx,
      residue_cpow_neg_mul_Gamma_mul_Gamma_add_neg_sub_natCast hp0 hp1 hx]
  · -- the poles `A ∪ B` lie inside the strip
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz <;> obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz <;>
      have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    · simp only [neg_re, natCast_re, mem_Ioo]
      constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · simp only [sub_re, neg_re, ofReal_re, natCast_re, mem_Ioo]
      constructor <;> linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- The Mellin inversion integral of `Γ(t) Γ(t + p)` on the line `Re t = (1 - p)/2 - N` tends to
`0` as `N → ∞`. -/
private lemma tendsto_mellinInv_Gamma_mul_Gamma_add {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) :
    Tendsto (fun N : ℕ ↦ mellinInv ((1 - p) / 2 - N) (fun z ↦ Gamma z * Gamma (z + p)) x) atTop
      (𝓝 0) := by
  set δ : ℝ := (1 - p) / 2 with hδ_def
  have hδ0 : 0 < δ := by rw [hδ_def]; linarith
  have hδp : δ + p < 1 := by rw [hδ_def]; linarith
  set κ : ℝ := (1 - δ) * (1 - (δ + p))
  have hκ : 0 < κ := mul_pos (by linarith) (by linarith)
  set A : ℝ := Real.Gamma (δ + 2) * Real.Gamma (δ + p) / (2 * δ * x ^ δ)
  have : 0 ≤ A := by
    have := Real.Gamma_pos_of_pos (by linarith : 0 < δ + 2)
    have := Real.Gamma_pos_of_pos (by linarith : 0 < δ + p)
    positivity
  refine squeeze_zero_norm (a := fun N : ℕ ↦ A * ((x / κ) ^ N / N !)) (fun N ↦ ?_) ?_
  · set M : ℝ := Real.Gamma (δ + 2) * Real.Gamma (δ + p) / (δ * κ ^ N * (N ! : ℝ) ^ 2)
    have hint : ∫ t : ℝ, ‖Gamma (((δ - N : ℝ) : ℂ) + t * I) *
        Gamma (((δ - N : ℝ) : ℂ) + t * I + p)‖ ≤ M * π := by
      rw [← integral_univ_inv_one_add_sq, ← integral_const_mul]
      exact integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
        (integrable_inv_one_add_sq.const_mul M)
        (Eventually.of_forall fun t ↦ by
          simpa using norm_Gamma_mul_Gamma_add_le_of_re_eq_sub_natCast hδ0 hp0 hδp N
            (s := ((δ - N : ℝ) : ℂ) + t * I) (by simp))
    have hfac : (1 : ℝ) ≤ N ! := by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos N)
    calc ‖mellinInv (δ - N) (fun z ↦ Gamma z * Gamma (z + p)) x‖
        ≤ x ^ (-(δ - N)) / (2 * π) * (M * π) :=
          (TauCeti.norm_mellinInv_le _ _ hx.le).trans
            (mul_le_mul_of_nonneg_left hint (by positivity))
      _ = A * ((x / κ) ^ N / N !) * (N ! : ℝ)⁻¹ := by
          rw [neg_sub, Real.rpow_sub hx, Real.rpow_natCast, div_pow]
          have : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
          simp only [M, A]
          field_simp
      _ ≤ A * ((x / κ) ^ N / N !) := by
          refine mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ hfac)
  · simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (x / κ)).const_mul A

/-! ### The series evaluation -/

/-- **The integral `∫₀^∞ s^{p - 1} e^{-s - x/s} ds` as a combination of `₀F₁` series.** For
`0 < p < 1` and `x > 0`,
`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = (π / sin pπ) (𝐅(1 - p, x) - x^p 𝐅(1 + p, x))`, where
`𝐅(b, x) = ∑ₙ xⁿ / (n! Γ(b + n))` is the regularized `₀F₁`. In Bessel notation both sides are
`2 x^{p/2} K_p(2 √x)`, the right side being `(π / sin pπ) x^{p/2} (I_{-p}(2 √x) - I_p(2 √x))`. -/
theorem integral_cpow_mul_exp_neg_add_div_Ioi {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ ((p : ℂ) - 1) * Real.exp (-(s + x / s)) =
      ((π / Real.sin (π * p) : ℝ) : ℂ) * (regularizedHGFun 0 {1 - (p : ℂ)} x -
        (x : ℂ) ^ (p : ℂ) * regularizedHGFun 0 {1 + (p : ℂ)} x) := by
  -- Mellin inversion on the line `Re t = 1`
  have hinv := (mellinInv_Gamma_mul_Gamma_add (a := (p : ℂ)) one_pos
    (by rw [ofReal_re]; linarith) hx).symm
  -- the residue series
  have hA := (hasSum_ofReal_regularizedHGFun_zero_singleton (1 - p) x).mul_left
    ((π / Real.sin (π * p) : ℝ) : ℂ)
  have hB := (hasSum_ofReal_regularizedHGFun_zero_singleton (1 + p) x).mul_left
    (-(((π / Real.sin (π * p) : ℝ) : ℂ) * (x : ℂ) ^ (p : ℂ)))
  have hlim := (tendsto_mellinInv_Gamma_mul_Gamma_add hp0 hp1 hx).add
    (hA.add hB).tendsto_sum_nat
  rw [zero_add] at hlim
  have hG := tendsto_nhds_unique (tendsto_const_nhds.congr fun N ↦
    hinv.trans (mellinInv_Gamma_mul_Gamma_add_eq hp0 hp1 hx N)) (by
      simpa only [← Finset.sum_add_distrib] using hlim)
  refine hG.trans ?_
  rw [show (1 - (p : ℂ)) = ((1 - p : ℝ) : ℂ) by push_cast; ring,
    show (1 + (p : ℂ)) = ((1 + p : ℝ) : ℂ) by push_cast; ring]
  ring

end Complex
