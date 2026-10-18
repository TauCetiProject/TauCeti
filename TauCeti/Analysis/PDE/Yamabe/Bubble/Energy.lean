/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic
public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Gradient, integrability and energy of the Yamabe bubbles

Let `E` be a real inner product space of dimension `n > 2`, and let
`U = U_{t,b}`, `U(x) = (2 t / (t² + ‖x - b‖²)) ^ ((n - 2) / 2)`, be the bubble of scale `t > 0`
centred at `b` (`TauCeti.Yamabe.bubble`). With `aₙ = 4 (n - 1) / (n - 2)` and
`pₙ = 2 n / (n - 2)`, this file proves:

* the gradient formula `∇U(x) = -((n - 2) / (t² + ‖x - b‖²)) U(x) (x - b)`;
* `U ∈ L^{pₙ}` and `dU ∈ L²` for every additive Haar measure, with
  `U ^ pₙ = (2 t / (t² + ‖x - b‖²)) ^ n`;
* the **energy identity** `aₙ ∫ ‖dU‖² = n (n - 1) ∫ U ^ pₙ`, again for every additive Haar
  measure;
* the value `∫ U ^ pₙ = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)` for Lebesgue measure.

The value is the classical surface area `|Sⁿ|` of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`, as it must be,
since `U ^ (4 / (n - 2))` times the Euclidean metric is the pullback of the round metric of `Sⁿ`;
neither the sphere nor the stereographic projection is formalized here. Classically, the two
identities together say that `aₙ ∫ ‖dU‖² = n (n - 1) |Sⁿ|`, so that the Sobolev quotient of `U`
is `n (n - 1) |Sⁿ| ^ (2 / n)`, the Yamabe invariant of the round sphere; this is the equality case
of the sharp Euclidean Sobolev inequality, which is not proved here.

The energy identity is proved in polar coordinates. Both integrands are radial about `b`, and
the radial integrals are related by integrating the derivative of
`r ↦ r ^ n (t² + r²) (2 t / (t² + r²)) ^ n`, which vanishes at `0` and at infinity exactly
because `n > 2`. This avoids integrating `U ΔU` by parts on the whole space, which is not
absolutely convergent in dimension three. The value of `∫ U ^ pₙ` follows from the integral of
the Japanese bracket and Legendre's duplication formula.

## Main declarations

* `TauCeti.Yamabe.hasGradientAt_bubble`, `TauCeti.Yamabe.norm_fderiv_bubble_sq`: the gradient of
  a bubble and the square of its norm.
* `TauCeti.Yamabe.bubble_rpow_criticalExponent`: `U ^ pₙ = (2 t / (t² + ‖x - b‖²)) ^ n`.
* `TauCeti.Yamabe.memLp_bubble`, `TauCeti.Yamabe.memLp_fderiv_bubble`: `U ∈ L^{pₙ}`, `dU ∈ L²`.
* `TauCeti.Yamabe.conformalCoefficient_mul_integral_norm_fderiv_bubble_sq`: the energy identity.
* `TauCeti.Yamabe.integral_bubble_rpow_criticalExponent`: the value of `∫ U ^ pₙ`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
* T. Aubin, *Problèmes isopérimétriques et espaces de Sobolev*, J. Differential Geom. 11 (1976).
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open Filter InnerProductSpace MeasureTheory Metric Module Real Set Topology
open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- In dimension `n ≠ 2`, the critical power of a bubble is
`U_{t,b} ^ pₙ = (2 t / (t² + ‖x - b‖²)) ^ n`. -/
theorem bubble_rpow_criticalExponent (hn : finrank ℝ E ≠ 2) {t : ℝ} (ht : 0 < t) (b x : E) :
    bubble t b x ^ criticalExponent (finrank ℝ E) =
      (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E := by
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  rw [bubble_apply, criticalExponent_def, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast _ (finrank ℝ E)]
  congr 1
  field_simp

section Gradient

variable [CompleteSpace E]

/-- **The gradient of a bubble**:
`∇U_{t,b}(x) = -((n - 2) / (t² + ‖x - b‖²)) U_{t,b}(x) (x - b)`, where `n` is the dimension of
`E`. -/
theorem hasGradientAt_bubble {t : ℝ} (ht : 0 < t) (b x : E) :
    HasGradientAt (bubble t b)
      (-(((finrank ℝ E : ℝ) - 2) / (t ^ 2 + ‖x - b‖ ^ 2) * bubble t b x) • (x - b)) x := by
  set k : ℝ := ((finrank ℝ E : ℝ) - 2) / 2
  have hQ : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  -- Write the bubble as `F ∘ q` with `q y = t² + ‖y - b‖²` and `F s = (2 t s⁻¹) ^ k`.
  have hq : HasFDerivAt (fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2) (toDual ℝ E ((2 : ℝ) • (x - b))) x := by
    refine (((hasStrictFDerivAt_norm_sq (x - b)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const b)).const_add (t ^ 2)).congr_fderiv ?_
    ext v
    simp
  have hF : HasDerivAt (fun s : ℝ ↦ (2 * t * s⁻¹) ^ k)
      (2 * t * -((t ^ 2 + ‖x - b‖ ^ 2) ^ 2)⁻¹ * k * (2 * t * (t ^ 2 + ‖x - b‖ ^ 2)⁻¹) ^ (k - 1))
      (t ^ 2 + ‖x - b‖ ^ 2) :=
    ((hasDerivAt_inv hQ.ne').const_mul (2 * t)).rpow_const (Or.inl (by positivity))
  have hU : bubble t b = (fun s : ℝ ↦ (2 * t * s⁻¹) ^ k) ∘ fun y : E ↦ t ^ 2 + ‖y - b‖ ^ 2 := by
    funext y
    simp [bubble_apply, div_eq_mul_inv, k]
  have h := hF.comp_hasFDerivAt x hq
  rw [← hU, ← map_smul, smul_smul] at h
  rw [hasGradientAt_iff_hasFDerivAt]
  refine h.congr_fderiv ?_
  congr 2
  rw [bubble_apply, div_eq_mul_inv,
    Real.rpow_sub_one (by positivity : 2 * t * (t ^ 2 + ‖x - b‖ ^ 2)⁻¹ ≠ 0)]
  simp only [k]
  field_simp

/-- The gradient of a bubble, as a value of `gradient`. -/
theorem gradient_bubble {t : ℝ} (ht : 0 < t) (b x : E) :
    ∇ (bubble t b) x =
      -(((finrank ℝ E : ℝ) - 2) / (t ^ 2 + ‖x - b‖ ^ 2) * bubble t b x) • (x - b) :=
  (hasGradientAt_bubble ht b x).gradient

/-- The squared norm of the differential of a bubble is the radial function
`((n - 2) / (2 t)) ² ‖x - b‖² (2 t / (t² + ‖x - b‖²)) ^ n`. -/
theorem norm_fderiv_bubble_sq {t : ℝ} (ht : 0 < t) (b x : E) :
    ‖fderiv ℝ (bubble t b) x‖ ^ 2 = (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * ‖x - b‖ ^ 2 *
      (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E := by
  have hQ : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  have hU2 : bubble t b x ^ 2 =
      (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E / (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ 2 := by
    have ha : 0 < 2 * t / (t ^ 2 + ‖x - b‖ ^ 2) := by positivity
    rw [bubble_apply, ← Real.rpow_mul_natCast ha.le, show ((finrank ℝ E : ℝ) - 2) / 2 * (2 : ℕ) =
      (finrank ℝ E : ℝ) - 2 by push_cast; ring, Real.rpow_sub ha, Real.rpow_natCast, Real.rpow_two]
  rw [(hasGradientAt_bubble ht b x).hasFDerivAt.fderiv, LinearIsometryEquiv.norm_map, norm_smul,
    mul_pow, norm_neg, Real.norm_eq_abs, sq_abs, mul_pow, hU2]
  field_simp

end Gradient

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

/-- In dimension `n > 2`, the critical power `U_{t,b} ^ pₙ` of a bubble is integrable for every
additive Haar measure. -/
theorem integrable_bubble_rpow_criticalExponent (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t)
    (b : E) : Integrable (fun x ↦ bubble t b x ^ criticalExponent (finrank ℝ E)) μ := by
  have hr : (finrank ℝ E : ℝ) < 2 * finrank ℝ E := by
    have : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
    linarith
  have hint := ((integrable_rpow_neg_sq_add_norm_sq μ ht.ne' hr).const_mul
    ((2 * t) ^ finrank ℝ E)).comp_sub_right b
  refine hint.congr (.of_forall fun x ↦ ?_)
  have hQ : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  beta_reduce
  rw [bubble_rpow_criticalExponent hn.ne' ht, show -(2 * (finrank ℝ E : ℝ)) / 2 =
    -(finrank ℝ E : ℝ) by ring, Real.rpow_neg hQ.le, Real.rpow_natCast, div_pow, div_eq_mul_inv]

/-- In dimension `n > 2`, the squared norm of the differential of a bubble is integrable for
every additive Haar measure. -/
theorem integrable_norm_fderiv_bubble_sq (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    Integrable (fun x ↦ ‖fderiv ℝ (bubble t b) x‖ ^ 2) μ := by
  set n := finrank ℝ E with hn_def
  have hr : (n : ℝ) < 2 * ((n : ℝ) - 1) := by
    have : (2 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hint := ((integrable_rpow_neg_sq_add_norm_sq μ ht.ne' hr).const_mul
    ((((n : ℝ) - 2) / (2 * t)) ^ 2 * (2 * t) ^ n)).comp_sub_right b
  refine hint.mono' ((((contDiff_bubble (m := 1) ht.ne' b).continuous_fderiv
    one_ne_zero).norm.pow 2).aestronglyMeasurable) (.of_forall fun x ↦ ?_)
  have hQ : 0 < t ^ 2 + ‖x - b‖ ^ 2 := by positivity
  -- Bound `‖x - b‖²` by `t² + ‖x - b‖²`, which lowers the decay rate from `2 n` to `2 (n - 1)`.
  have hpow : (t ^ 2 + ‖x - b‖ ^ 2) ^ (-(2 * ((n : ℝ) - 1)) / 2) =
      (t ^ 2 + ‖x - b‖ ^ 2) / (t ^ 2 + ‖x - b‖ ^ 2) ^ n := by
    rw [show -(2 * ((n : ℝ) - 1)) / 2 = 1 - n by ring, Real.rpow_sub hQ, Real.rpow_one,
      Real.rpow_natCast]
  have key : ‖x - b‖ ^ 2 * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ n ≤
      (2 * t) ^ n * ((t ^ 2 + ‖x - b‖ ^ 2) / (t ^ 2 + ‖x - b‖ ^ 2) ^ n) := by
    rw [div_pow, mul_div_assoc', mul_div_assoc']
    gcongr ?_ / _
    rw [mul_comm]
    gcongr
    linarith [sq_nonneg t]
  rw [Real.norm_of_nonneg (by positivity), norm_fderiv_bubble_sq ht, ← hn_def, hpow]
  calc _ = (((n : ℝ) - 2) / (2 * t)) ^ 2 *
        (‖x - b‖ ^ 2 * (2 * t / (t ^ 2 + ‖x - b‖ ^ 2)) ^ n) := by ring
    _ ≤ _ := by
      rw [mul_assoc _ ((2 * t) ^ n)]
      gcongr

/-- In dimension `n > 2`, a bubble lies in `L^{pₙ}` for every additive Haar measure. -/
theorem memLp_bubble (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    MemLp (bubble t b) (ENNReal.ofReal (criticalExponent (finrank ℝ E))) μ := by
  have hp : 0 < criticalExponent (finrank ℝ E) := by
    have : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
    rw [criticalExponent_def]
    exact div_pos (by linarith) (by linarith)
  refine (integrable_norm_rpow_iff
    (contDiff_bubble (m := 0) ht.ne' b).continuous.aestronglyMeasurable
    (by simpa using hp) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal hp.le]
  refine (integrable_bubble_rpow_criticalExponent μ hn ht b).congr (.of_forall fun x ↦ ?_)
  simp only [Real.norm_of_nonneg (bubble_pos ht b x).le]

/-- In dimension `n > 2`, the differential of a bubble lies in `L²` for every additive Haar
measure. -/
theorem memLp_fderiv_bubble (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t) (b : E) :
    MemLp (fderiv ℝ (bubble t b)) 2 μ :=
  (memLp_two_iff_integrable_sq_norm ((contDiff_bubble (m := 1) ht.ne' b).continuous_fderiv
    one_ne_zero).aestronglyMeasurable).mpr (integrable_norm_fderiv_bubble_sq μ hn ht b)

/-- The radial identity behind the energy identity: for `n > 2` and
`ψ(r) = (2 t / (t² + r²)) ^ n`, `(n - 2) ∫₀^∞ r ^ (n - 1) r² ψ(r) = n t² ∫₀^∞ r ^ (n - 1) ψ(r)`.
It comes from integrating the derivative of `r ↦ r ^ n (t² + r²) ψ(r)`, which vanishes at `0` and
at infinity. -/
private theorem sub_two_mul_integral_radial {n : ℕ} (hn : 2 < n) {t : ℝ} (ht : 0 < t)
    (h₁ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ n) (Ioi 0))
    (h₂ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ n))
      (Ioi 0)) :
    ((n : ℝ) - 2) * ∫ r in Ioi 0, r ^ (n - 1) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ n) =
      n * t ^ 2 * ∫ r in Ioi 0, r ^ (n - 1) * (2 * t / (t ^ 2 + r ^ 2)) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  simp only [show m + 3 - 1 = m + 2 by omega] at h₁ h₂ ⊢
  have hQ : ∀ r : ℝ, 0 < t ^ 2 + r ^ 2 := fun r ↦ by positivity
  set F : ℝ → ℝ := fun r ↦ r ^ (m + 3) * (t ^ 2 + r ^ 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)
  have hderiv : ∀ r ∈ Ici (0 : ℝ), HasDerivAt F
      (((m + 3 : ℕ) : ℝ) * t ^ 2 * (r ^ (m + 2) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)) -
        (((m + 3 : ℕ) : ℝ) - 2) *
          (r ^ (m + 2) * (r ^ 2 * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3)))) r := by
    intro r _
    have hQr : t ^ 2 + r ^ 2 ≠ 0 := (hQ r).ne'
    have hq : HasDerivAt (fun r : ℝ ↦ t ^ 2 + r ^ 2) (2 * r) r := by
      simpa using (hasDerivAt_pow 2 r).const_add (t ^ 2)
    have hψ : HasDerivAt (fun r : ℝ ↦ (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
        (-(2 * ((m + 3 : ℕ) : ℝ) * r / (t ^ 2 + r ^ 2)) * (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3))
        r := by
      convert ((hasDerivAt_const r (2 * t)).div hq hQr).pow (m + 3) using 1
      simp only [Pi.div_apply, show m + 3 - 1 = m + 2 by omega]
      rw [pow_succ _ (m + 2)]
      generalize (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 2) = X
      field_simp
      ring
    convert ((hasDerivAt_pow (m + 3) r).mul hq).mul hψ using 1
    simp only [Pi.mul_apply, show m + 3 - 1 = m + 2 by omega]
    rw [pow_succ r (m + 2)]
    generalize (2 * t / (t ^ 2 + r ^ 2)) ^ (m + 3) = P
    generalize r ^ (m + 2) = R
    push_cast
    field_simp
    ring
  -- For `r > 0`, `F r = (2 t) ^ (m + 3) (r / (t² + r²)) ^ (m + 1) (r² / (t² + r²))`, which is at
  -- most `(2 t) ^ (m + 3) r⁻¹ ^ (m + 1)`.
  have htend : Tendsto F atTop (𝓝 0) := by
    have hlim : Tendsto (fun r : ℝ ↦ (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.pow (m + 1)).const_mul ((2 * t) ^ (m + 3))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      ((eventually_gt_atTop 0).mono fun r hr ↦ by positivity)
      ((eventually_gt_atTop 0).mono fun r hr ↦ ?_)
    · have hF : F r = (2 * t) ^ (m + 3) * (r / (t ^ 2 + r ^ 2)) ^ (m + 1) *
          (r ^ 2 / (t ^ 2 + r ^ 2)) := by
        have := (hQ r).ne'
        simp only [F]
        rw [div_pow, div_pow]
        field_simp
        ring
      have h₁ : r / (t ^ 2 + r ^ 2) ≤ r⁻¹ := by
        rw [div_le_iff₀ (hQ r), inv_mul_eq_div, le_div_iff₀ hr]
        nlinarith [sq_nonneg t]
      have h₂ : r ^ 2 / (t ^ 2 + r ^ 2) ≤ 1 := by
        rw [div_le_one (hQ r)]
        nlinarith [sq_nonneg t]
      rw [hF]
      calc (2 * t) ^ (m + 3) * (r / (t ^ 2 + r ^ 2)) ^ (m + 1) * (r ^ 2 / (t ^ 2 + r ^ 2))
          ≤ (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1) * 1 := by gcongr
        _ = (2 * t) ^ (m + 3) * r⁻¹ ^ (m + 1) := mul_one _
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    ((h₁.const_mul _).sub (h₂.const_mul _)) htend
  rw [integral_sub (h₁.const_mul _) (h₂.const_mul _), integral_const_mul, integral_const_mul,
    show F 0 = 0 by simp [F], sub_zero] at h
  push_cast at h ⊢
  linarith

/-- **The energy identity of a bubble**: in dimension `n > 2`,
`aₙ ∫ ‖dU_{t,b}‖² = n (n - 1) ∫ U_{t,b} ^ pₙ` for every additive Haar measure. -/
theorem conformalCoefficient_mul_integral_norm_fderiv_bubble_sq (hn : 2 < finrank ℝ E) {t : ℝ}
    (ht : 0 < t) (b : E) :
    conformalCoefficient (finrank ℝ E) * ∫ x, ‖fderiv ℝ (bubble t b) x‖ ^ 2 ∂μ =
      (finrank ℝ E : ℝ) * (finrank ℝ E - 1) *
        ∫ x, bubble t b x ^ criticalExponent (finrank ℝ E) ∂μ := by
  -- Translate `b` to the origin, pass to polar coordinates, and compare the two radial integrals
  -- with `sub_two_mul_integral_radial`.
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  set n := finrank ℝ E with hn_def
  -- Both integrands are radial about `b`, with profiles `φ` and `ψ`.
  set ψ : ℝ → ℝ := fun r ↦ (2 * t / (t ^ 2 + r ^ 2)) ^ n
  set C : ℝ := (((n : ℝ) - 2) / (2 * t)) ^ 2 with hC
  set φ : ℝ → ℝ := fun r ↦ C * (r ^ 2 * ψ r) with hφ
  have hgrad (b : E) : (fun x ↦ ‖fderiv ℝ (bubble t b) x‖ ^ 2) = fun x ↦ φ ‖x - b‖ := by
    funext x
    rw [norm_fderiv_bubble_sq ht, ← hn_def]
    ring
  have hpow (b : E) : (fun x ↦ bubble t b x ^ criticalExponent n) = fun x ↦ ψ ‖x - b‖ := by
    funext x
    exact bubble_rpow_criticalExponent hn.ne' ht b x
  -- The radial profiles are integrable, by integrability on `E` of the bubble centred at `0`.
  have hC0 : C ≠ 0 := by
    have : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    positivity
  have h₁ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * ψ r) (Ioi 0) := by
    have h := integrable_bubble_rpow_criticalExponent μ hn ht 0
    rw [hpow 0] at h
    simp only [sub_zero] at h
    simpa using (integrable_fun_norm_addHaar μ (f := ψ)).mp h
  have h₂ : IntegrableOn (fun r : ℝ ↦ r ^ (n - 1) * (r ^ 2 * ψ r)) (Ioi 0) := by
    have h := integrable_norm_fderiv_bubble_sq μ hn ht 0
    rw [hgrad 0] at h
    simp only [sub_zero] at h
    refine IntegrableOn.congr_fun (((integrable_fun_norm_addHaar μ (f := φ)).mp h).const_mul C⁻¹)
      (fun r _ ↦ ?_) measurableSet_Ioi
    simp only [hφ, smul_eq_mul, ← hn_def]
    field_simp
  have hrad : ((n : ℝ) - 2) * ∫ r in Ioi 0, r ^ (n - 1) * (r ^ 2 * ψ r) =
      n * t ^ 2 * ∫ r in Ioi 0, r ^ (n - 1) * ψ r :=
    sub_two_mul_integral_radial hn ht h₁ h₂
  have hI₂ : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) • φ r =
      C * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
    simp only [hφ, smul_eq_mul]
    ring
  have hφb := integral_sub_right_eq_self (μ := μ) (fun y ↦ φ ‖y‖) b
  have hψb := integral_sub_right_eq_self (μ := μ) (fun y ↦ ψ ‖y‖) b
  rw [hgrad b, hpow b, hφb, hψb, integral_fun_norm_addHaar μ φ, integral_fun_norm_addHaar μ ψ,
    ← hn_def, hI₂]
  have haC : conformalCoefficient n * C = ((n : ℝ) - 1) * ((n : ℝ) - 2) / t ^ 2 := by
    have : (n : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn.ne')
    rw [conformalCoefficient_def, hC]
    field_simp
    ring
  simp only [nsmul_eq_mul, smul_eq_mul]
  calc conformalCoefficient n * (n * (μ.real (ball 0 1) *
        (C * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r)))) =
      ((n : ℝ) - 1) / t ^ 2 * n * μ.real (ball 0 1) *
        (((n : ℝ) - 2) * ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r)) := by
        linear_combination (n * μ.real (ball 0 1) *
          ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (r ^ 2 * ψ r)) * haC
    _ = _ := by
      rw [hrad]
      field_simp

/-- **The critical norm of a bubble**: in dimension `n > 2`, for Lebesgue measure,
`∫ U_{t,b} ^ pₙ = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`, independently of the scale and the
centre. The right-hand side is the classical surface area of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹`. -/
theorem integral_bubble_rpow_criticalExponent (hn : 2 < finrank ℝ E) {t : ℝ} (ht : 0 < t)
    (b : E) :
    ∫ x, bubble t b x ^ criticalExponent (finrank ℝ E) =
      2 * π ^ (((finrank ℝ E : ℝ) + 1) / 2) / Gamma (((finrank ℝ E : ℝ) + 1) / 2) := by
  set n := finrank ℝ E with hn_def
  have hn0 : (0 : ℝ) < n := by positivity
  set ψ : ℝ → ℝ := fun r ↦ (2 * t / (t ^ 2 + r ^ 2)) ^ n with hψ
  have hpow : (fun x ↦ bubble t b x ^ criticalExponent n) = fun x ↦ ψ ‖x - b‖ := by
    funext x
    exact bubble_rpow_criticalExponent hn.ne' ht b x
  -- Rescale: `ψ ‖y‖ = (2 / t) ^ n (1 + ‖t⁻¹ • y‖²) ^ (-n)`.
  have hscale (y : E) : ψ ‖y‖ =
      (2 / t) ^ n * (1 + ‖t⁻¹ • y‖ ^ 2) ^ (-(2 * (n : ℝ)) / 2) := by
    have hQ : 0 < t ^ 2 + ‖y‖ ^ 2 := by positivity
    simp only [hψ]
    rw [show -(2 * (n : ℝ)) / 2 = -(n : ℝ) by ring, Real.rpow_neg (by positivity),
      Real.rpow_natCast, norm_smul, norm_inv, Real.norm_of_nonneg ht.le, div_pow, div_pow,
      mul_pow]
    field_simp
    rw [div_pow, ← pow_mul, ← pow_mul, mul_comm 2 n]
    field_simp
  have hψb := integral_sub_right_eq_self (μ := volume) (fun y ↦ ψ ‖y‖) b
  have hr : (n : ℝ) < 2 * n := by linarith
  rw [hpow, hψb, integral_congr_ae (.of_forall hscale), integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun z : E ↦ (1 + ‖z‖ ^ 2) ^ (-(2 * (n : ℝ)) / 2)) ht.le,
    integral_rpow_neg_one_add_norm_sq hr,
    show (2 * (n : ℝ) - n) / 2 = n / 2 by ring, show 2 * (n : ℝ) / 2 = n by ring, smul_eq_mul]
  -- Legendre's duplication formula at `n / 2`.
  have hdup := Real.Gamma_mul_Gamma_add_half ((n : ℝ) / 2)
  rw [show 2 * ((n : ℝ) / 2) = n by ring, show (n : ℝ) / 2 + 1 / 2 = (n + 1) / 2 by ring] at hdup
  have h2 : (2 : ℝ) ^ n * 2 ^ (1 - (n : ℝ)) = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add two_pos]
    ring_nf
    exact Real.rpow_one 2
  have hπ : π ^ ((n : ℝ) / 2) * √π = π ^ (((n : ℝ) + 1) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add pi_pos]
    ring_nf
  have hΓn := Gamma_pos_of_pos hn0
  have hΓ := Gamma_pos_of_pos (show 0 < ((n : ℝ) + 1) / 2 by positivity)
  rw [← hn_def]
  calc (2 / t) ^ n * (t ^ n * (π ^ ((n : ℝ) / 2) * Gamma (n / 2) / Gamma n)) =
      2 ^ n * π ^ ((n : ℝ) / 2) * Gamma (n / 2) / Gamma n := by
        rw [div_pow]
        field_simp
    _ = _ := by
      rw [div_eq_div_iff hΓn.ne' hΓ.ne']
      linear_combination (2 ^ n * π ^ ((n : ℝ) / 2)) * hdup +
        (Gamma n * π ^ ((n : ℝ) / 2) * √π) * h2 + (2 * Gamma n) * hπ

end TauCeti.Yamabe
