/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Barnes's first lemma

Barnes's first lemma ([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)) evaluates the vertical-line
integral of a product of four shifted Gamma functions: for `a, b, c, d : ℂ` with positive real
parts,

`(1 / 2π) ∫_{-∞}^∞ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`,

and more generally along any vertical line `Re s = σ` separating the left-half-plane poles of
`Γ(a + s) Γ(b + s)` from the right-half-plane poles of `Γ(c - s) Γ(d - s)`.

Rather than closing a contour at infinity, the proof inserts the Mellin–Barnes integral of
`(1 + u)^{-(a + c)}` (`Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`, translated horizontally
to complex shifts in `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma`) into Euler's second Beta
integral (`Complex.hasMellin_one_add_cpow_neg`) and swaps the two integrations by Fubini's theorem.
Because `‖u^{b + i y - 1}‖ = u^{Re b - 1}` for `u > 0`, the modulus of the two-variable integrand
factors into an integrable product on `(0, ∞) × ℝ`.

Stirling's vertical-line exponential bound (`Complex.exists_norm_Gamma_add_mul_I_le_mul_exp`) also
shows that on any pole-free vertical line the four-Gamma product decays as `O(exp (-r |y|))` for
every `r < 2π` (`Complex.exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_exp`), hence is
integrable (`Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`).

## Main results

* `Complex.integrable_Gamma_add_mul_Gamma_sub`: vertical integrability of `Γ(a + i y) Γ(c - i y)`
  for complex parameters `a, c` with `Re a, Re c ∉ -ℕ`.
* `Complex.exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_exp`,
  `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: `O(exp (-r |y|))` decay for every
  `r < 2π` and vertical integrability of four-Gamma products away from `-ℕ`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma`: the Mellin–Barnes binomial integral with complex
  parameters `0 < Re a`, `0 < Re c`.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: **Barnes's first lemma** (DLMF 5.13.3).
* `Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: Barnes's first lemma on a
  separating vertical line `max (-Re a, -Re b) < σ < min (Re c, Re d)`.

## References

* [NIST Digital Library of Mathematical Functions, 5.13.3](https://dlmf.nist.gov/5.13.E3).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.52.
-/

public section

open Real Set MeasureTheory Filter

namespace Complex

/-- Along any vertical line avoiding the poles of both factors, `y ↦ Γ(a + i y) Γ(c - i y)` is
Bochner integrable on `ℝ`. -/
theorem integrable_Gamma_add_mul_Gamma_sub {a c : ℂ} (ha : ∀ n : ℕ, a.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) :
    Integrable fun y : ℝ ↦ Gamma (a + y * I) * Gamma (c - y * I) := by
  have hpi : 0 < Real.pi / 4 := by positivity
  obtain ⟨C₁, _, h₁⟩ := exists_norm_Gamma_add_mul_I_le_mul_exp ha (c := Real.pi / 4)
    (by linarith [Real.pi_pos])
  obtain ⟨C₂, _, h₂⟩ := exists_norm_Gamma_sub_mul_I_le_mul_exp hc (c := 0) (by positivity)
  refine ((TauCeti.integrable_exp_neg_mul_abs hpi).const_mul (C₁ * C₂)).mono'
    ((continuous_Gamma_add_mul_I ha).mul (continuous_Gamma_sub_mul_I hc)).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  rw [norm_mul]
  calc ‖Gamma (a + y * I)‖ * ‖Gamma (c - y * I)‖
      ≤ (C₁ * Real.exp (-(Real.pi / 4) * |y|)) * (C₂ * Real.exp (-0 * |y|)) :=
        mul_le_mul (h₁ y) (h₂ y) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * Real.exp (-(Real.pi / 4 * |y|)) := by
        simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, neg_mul]
        ring

/-- On any vertical line avoiding the poles of all four factors, the product
`Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` is bounded in norm by `C * exp (-r * |y|)` for every
exponent `r < 2π`. -/
theorem exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_exp {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) {r : ℝ} (hr : r < 2 * Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      ‖Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)‖ ≤
        C * Real.exp (-r * |y|) := by
  have hr4 : r / 4 < Real.pi / 2 := by linarith
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_Gamma_add_mul_I_le_mul_exp ha hr4
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_Gamma_add_mul_I_le_mul_exp hb hr4
  obtain ⟨C₃, hC₃, h₃⟩ := exists_norm_Gamma_sub_mul_I_le_mul_exp hc hr4
  obtain ⟨C₄, hC₄, h₄⟩ := exists_norm_Gamma_sub_mul_I_le_mul_exp hd hr4
  refine ⟨C₁ * C₂ * C₃ * C₄, by positivity, fun y ↦ ?_⟩
  rw [norm_mul, norm_mul, norm_mul]
  have h12 : ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ ≤
      (C₁ * Real.exp (-(r / 4) * |y|)) * (C₂ * Real.exp (-(r / 4) * |y|)) :=
    mul_le_mul (h₁ y) (h₂ y) (norm_nonneg _) (by positivity)
  have h123 : ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ * ‖Gamma (c - y * I)‖ ≤
      (C₁ * Real.exp (-(r / 4) * |y|)) * (C₂ * Real.exp (-(r / 4) * |y|)) *
        (C₃ * Real.exp (-(r / 4) * |y|)) :=
    mul_le_mul h12 (h₃ y) (norm_nonneg _) (by positivity)
  calc ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ * ‖Gamma (c - y * I)‖ * ‖Gamma (d - y * I)‖
      ≤ (C₁ * Real.exp (-(r / 4) * |y|)) * (C₂ * Real.exp (-(r / 4) * |y|)) *
          (C₃ * Real.exp (-(r / 4) * |y|)) * (C₄ * Real.exp (-(r / 4) * |y|)) :=
        mul_le_mul h123 (h₄ y) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * C₃ * C₄ * Real.exp (-r * |y|) := by
        have hexp : -r * |y| =
            -(r / 4) * |y| + (-(r / 4) * |y| + (-(r / 4) * |y| + -(r / 4) * |y|)) := by ring
        rw [hexp, Real.exp_add, Real.exp_add, Real.exp_add]
        ring

/-- On any vertical line avoiding the poles of all four factors,
`y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` is Bochner integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨C, _, hC⟩ := exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_exp ha hb hc hd
    (r := Real.pi) (by linarith [Real.pi_pos])
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) :=
    (((continuous_Gamma_add_mul_I ha).mul (continuous_Gamma_add_mul_I hb)).mul
      (continuous_Gamma_sub_mul_I hc)).mul (continuous_Gamma_sub_mul_I hd)
  refine ((TauCeti.integrable_exp_neg_mul_abs Real.pi_pos).const_mul C).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  simpa [neg_mul] using hC y

/-- **The Mellin–Barnes integral of `(1 + u)^{-(a + c)}`** with complex shifts: for `0 < Re a`,
`0 < Re c`, and `0 < u`,
`∫ u^{-(a + i y)} Γ(a + i y) Γ(c - i y) dy = 2π Γ(a + c) (1 + u)^{-(a + c)}`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma {a c : ℂ} (ha : 0 < a.re) (hc : 0 < c.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(a + y * I)) * (Gamma (a + y * I) * Gamma (c - y * I)) =
      2 * π * (Gamma (a + c) * (1 + (u : ℂ)) ^ (-(a + c))) := by
  let f : ℝ → ℂ := fun t ↦
    (u : ℂ) ^ (-((a.re : ℂ) + t * I)) *
      (Gamma ((a.re : ℂ) + t * I) * Gamma ((a + c) - ((a.re : ℂ) + t * I)))
  have hshift (y : ℝ) : (a.re : ℂ) + ((y + a.im : ℝ) : ℂ) * I = a + y * I := by
    conv_rhs => rw [← re_add_im a]
    push_cast; ring
  have hcongr (y : ℝ) :
      (u : ℂ) ^ (-(a + y * I)) * (Gamma (a + y * I) * Gamma (c - y * I)) = f (y + a.im) := by
    dsimp only [f]
    rw [hshift, show a + c - (a + y * I) = c - y * I by ring]
  simp_rw [hcongr]
  rw [MeasureTheory.integral_add_right_eq_self f a.im]
  exact integral_cpow_neg_mul_Gamma_mul_Gamma_sub ha (by simp [hc]) hu

/-- **Barnes's first lemma** ([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)). For complex parameters
`a, b, c, d` with positive real parts,
`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have ha_ne : ∀ n : ℕ, a.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hc_ne : ∀ n : ℕ, c.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  let F : ℝ → ℝ → ℂ := fun u y ↦
    Gamma (a + y * I) * Gamma (c - y * I) *
      ((u : ℂ) ^ (b + y * I - 1) * (1 + (u : ℂ)) ^ (-(b + d)))
  have hF_meas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod MeasurableSet.univ)
    intro p hp
    have hp0 : 0 < p.1 := hp.1
    have hc1 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (a + q.2 * I)) p :=
      ((continuous_Gamma_add_mul_I ha_ne).comp continuous_snd).continuousAt
    have hc2 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (c - q.2 * I)) p :=
      ((continuous_Gamma_sub_mul_I hc_ne).comp continuous_snd).continuousAt
    have hc3 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (b + q.2 * I - 1)) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr hp0)
    have hc4 : ContinuousAt (fun q : ℝ × ℝ ↦ (1 + (q.1 : ℂ)) ^ (-(b + d))) p := by
      refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    exact ((hc1.mul hc2).mul (hc3.mul hc4)).continuousWithinAt
  have hF_int : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hy_int : Integrable (fun y : ℝ ↦ ‖Gamma (a + y * I) * Gamma (c - y * I)‖) volume :=
      (integrable_Gamma_add_mul_Gamma_sub ha_ne hc_ne).norm
    have hu_int := (hasMellin_one_add_cpow_neg (s := (b.re : ℂ))
      (a := ((b.re + d.re : ℝ) : ℂ)) (by simpa using hb) (by simp [hd])).1.norm
    refine (hu_int.mul_prod hy_int).mono' hF_meas ?_
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
    have hu : 0 < p.1 := hp.1
    have h1u : 0 < 1 + p.1 := by linarith
    have h1u_cast : (1 : ℂ) + (p.1 : ℂ) = ((1 + p.1 : ℝ) : ℂ) := by push_cast; ring
    simp only [Function.uncurry_def, F, smul_eq_mul, norm_mul, h1u_cast,
      norm_cpow_eq_rpow_re_of_pos hu, norm_cpow_eq_rpow_re_of_pos h1u]
    have hre1 : (b + (p.2 : ℂ) * I - 1).re = ((b.re : ℂ) - 1).re := by simp
    have hre2 : (-(b + d)).re = (-((b.re + d.re : ℝ) : ℂ)).re := by simp
    rw [hre1, hre2, mul_comm]
  have hswap := integral_integral_swap hF_int
  -- Right-hand iterated integral: Euler's second Beta integral in `u` at `s = b + i y`.
  have hRHS : (∫ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y) =
      (Gamma (b + d))⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only [F]
    rw [integral_const_mul]
    have hm := (hasMellin_one_add_cpow_neg (s := b + y * I) (a := b + d)
      (by simpa using hb) (by simp [hd])).2
    simp only [mellin, smul_eq_mul, show b + d - (b + y * I) = d - y * I by ring] at hm
    rw [hm]
    ring
  -- Left-hand iterated integral: Mellin–Barnes binomial integral in `y`, then Beta in `u`.
  have hLHS : (∫ u in Ioi (0 : ℝ), ∫ y : ℝ, F u y) =
      2 * π * Gamma (a + c) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)) := by
    have hinner : ∀ u ∈ Ioi (0 : ℝ), (∫ y : ℝ, F u y) =
        2 * π * Gamma (a + c) *
          ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
      intro u (hu : 0 < u)
      have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
      have h1u0 : (1 : ℂ) + (u : ℂ) ≠ 0 := by
        rw [← ofReal_one, ← ofReal_add]
        exact ofReal_ne_zero.mpr (by linarith)
      have hsplit (y : ℝ) : F u y =
          ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(b + d))) *
            ((u : ℂ) ^ (-(c - y * I)) * (Gamma (a + y * I) * Gamma (c - y * I))) := by
        dsimp only [F]
        have hpow : (u : ℂ) ^ (b + y * I - 1) =
            (u : ℂ) ^ (b + c - 1) * (u : ℂ) ^ (-(c - y * I)) := by
          rw [← cpow_add _ _ hu0]
          congr 1; ring
        rw [hpow]
        ring
      have hmb : (∫ y : ℝ, (u : ℂ) ^ (-(c - y * I)) * (Gamma (a + y * I) * Gamma (c - y * I))) =
          2 * π * (Gamma (a + c) * (1 + (u : ℂ)) ^ (-(a + c))) := by
        rw [← MeasureTheory.integral_neg_eq_self]
        have heq (y : ℝ) :
            (u : ℂ) ^ (-(c - (-y : ℝ) * I)) *
              (Gamma (a + (-y : ℝ) * I) * Gamma (c - (-y : ℝ) * I)) =
            (u : ℂ) ^ (-(c + y * I)) * (Gamma (c + y * I) * Gamma (a - y * I)) := by
          push_cast
          have h1 : -(c - (-(y : ℂ)) * I) = -(c + y * I) := by ring
          have h2 : a + (-(y : ℂ)) * I = a - y * I := by ring
          have h3 : c - (-(y : ℂ)) * I = c + y * I := by ring
          rw [h1, h2, h3, mul_comm (Gamma (a - y * I))]
        simp_rw [heq]
        rw [integral_cpow_neg_mul_Gamma_mul_Gamma hc ha hu, add_comm c a]
      simp_rw [hsplit]
      rw [integral_const_mul, hmb]
      have hpow1u : (1 + (u : ℂ)) ^ (-(b + d)) * (1 + (u : ℂ)) ^ (-(a + c)) =
          (1 + (u : ℂ)) ^ (-(a + b + c + d)) := by
        rw [← cpow_add _ _ h1u0]
        congr 1; ring
      linear_combination 2 * (π : ℂ) * Gamma (a + c) * (u : ℂ) ^ (b + c - 1) * hpow1u
    rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul]
    have hm := (hasMellin_one_add_cpow_neg (s := b + c) (a := a + b + c + d)
      (by simp; linarith) (by simp; linarith)).2
    simp only [mellin, smul_eq_mul, show a + b + c + d - (b + c) = a + d by ring] at hm
    rw [hm]
  rw [hLHS, hRHS] at hswap
  have hΓbd : Gamma (b + d) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hkey := congrArg (fun z : ℂ ↦ (2 * π : ℂ)⁻¹ * Gamma (b + d) * z) hswap.symm
  rw [mul_assoc ((2 * π : ℂ)⁻¹), mul_inv_cancel_left₀ hΓbd] at hkey
  rw [hkey]
  field_simp [h2pi]

/-- **Barnes's first lemma on a separating vertical line**: if `Re s = σ` separates the poles of
`Γ(a + s) Γ(b + s)` from those of `Γ(c - s) Γ(d - s)` (that is,
`max (-Re a, -Re b) < σ < min (Re c, Re d)`), then
`(1 / 2π) ∫ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(c - (σ + i y)) Γ(d - (σ + i y)) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hbσ : -b.re < σ) (hσc : σ < c.re) (hσd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  convert h using 1
  · congr 1
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    have e1 : a + ((σ : ℂ) + y * I) = a + σ + y * I := by ring
    have e2 : b + ((σ : ℂ) + y * I) = b + σ + y * I := by ring
    have e3 : c - ((σ : ℂ) + y * I) = c - σ - y * I := by ring
    have e4 : d - ((σ : ℂ) + y * I) = d - σ - y * I := by ring
    rw [e1, e2, e3, e4]
  · have h1 : a + (σ : ℂ) + (c - σ) = a + c := by ring
    have h2 : a + (σ : ℂ) + (d - σ) = a + d := by ring
    have h3 : b + (σ : ℂ) + (c - σ) = b + c := by ring
    have h4 : b + (σ : ℂ) + (d - σ) = b + d := by ring
    have h5 : a + (σ : ℂ) + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
    rw [h1, h2, h3, h4, h5]

-- Normalization check at `a = b = c = d = 1 / 2`: all four numerator arguments are `1` and the
-- denominator argument is `2`, so `(1 / 2π) ∫ |Γ(1/2 + i y)|^4 dy = 1`.
example :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (1 / 2 + y * I) * Gamma (1 / 2 + y * I) *
          Gamma (1 / 2 - y * I) * Gamma (1 / 2 - y * I) = 1 := by
  rw [integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_one, Gamma_two]

end Complex
