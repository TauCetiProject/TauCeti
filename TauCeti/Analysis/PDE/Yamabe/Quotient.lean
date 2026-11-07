/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Energy
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Integral.AbsRpow

/-!
# The Yamabe quotient and its Euler–Lagrange equation

On a Riemannian manifold `(M, g)` of dimension `n`, the *Yamabe quotient* of a function `u` is

`Q_g(u) = (∫ (aₙ |grad u|² + Scal_g u²) dV_g) / (∫ |u| ^ pₙ dV_g) ^ (2 / pₙ)`,

with `aₙ = 4 (n - 1) / (n - 2)` and `pₙ = 2 n / (n - 2)` (`TauCeti.Yamabe.yamabeQuotient`). It is
invariant under multiplication of `u` by a nonzero constant. For a positive function `u` on a
closed manifold, `Q_g(u)` is the volume-normalized total scalar curvature of the conformal metric
`u ^ (4 / (n - 2)) g`, by
`TauCeti.Yamabe.integral_scalarCurvature_rescale_div_riemannianTotalVolume_rpow` together with the
energy identity `TauCeti.Yamabe.integral_mul_conformalLaplacian_self`, and the Yamabe problem asks
for a minimizer.

This file computes the first variation of `Q_g` on a compact manifold. Write
`N(u) = ∫ |u| ^ pₙ dV`. For `C¹` functions `u ≠ 0` and `v`,

`d/dt Q_g(u + t v) |_(t = 0) =
  2 ((∫ (aₙ ⟪grad v, grad u⟫ + Scal_g v u) dV) / N(u) ^ (2 / pₙ) -
    Q_g(u) (∫ |u| ^ (pₙ - 2) u v dV) / N(u))`.

The energy is quadratic in `t`, and `|·| ^ pₙ` is differentiable with derivative
`pₙ |s| ^ (pₙ - 2) s` because `pₙ > 1`, so `N(u + t v)` is differentiated under the integral
sign. On a closed manifold, integration by parts turns the first term into `∫ v L_g u dV`, where
`L_g` is the conformal Laplacian. Since smooth functions separate continuous functions under
integration, this gives the **Euler–Lagrange equation**: a nonzero `C²` function `u` is a critical
point of `Q_g` in every smooth direction exactly when it solves

`L_g u = λ |u| ^ (pₙ - 2) u`

for some constant `λ`. Integrating the equation against `u` identifies the constant:
`Q_g(u) = λ N(u) ^ (1 - 2 / pₙ)`, so `λ = Q_g(u)` when `u` has unit `L^pₙ` norm. For a nonnegative
`u` the equation is the Yamabe equation `L_g u = λ u ^ (pₙ - 1)`; for a positive smooth `u` it says
that `u ^ (4 / (n - 2)) g` has constant scalar curvature `λ`
(`TauCeti.Yamabe.scalarCurvature_rescale_eq_iff_conformalLaplacian_eq`).

The quotient is defined for every function, through the Riemannian gradient and Bochner integrals;
its classical meaning, and the variational results here, concern differentiable functions; scale
invariance (`yamabeQuotient_smul`) holds for every function. The metric is the
`RiemannianBundle` instance of the tangent bundle and the volume is `TauCeti.riemannianVolume`, as
for `TauCeti.Yamabe.conformalLaplacian`.

## Main declarations

All in the namespace `TauCeti.Yamabe`.

* `yamabeQuotient`: the Yamabe quotient `Q_g(u)`.
* `yamabeQuotient_smul`: `Q_g(c u) = Q_g(u)` for `c ≠ 0`.
* `hasDerivAt_yamabeQuotient_add_smul`: the first variation of `Q_g`.
* `forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_conformalLaplacian_eq`: the Euler–Lagrange
  equation `L_g u = λ |u| ^ (pₙ - 2) u` characterizes the critical points of `Q_g`.
* `forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_conformalLaplacian_eq_of_nonneg`:
  for `u ≥ 0` it is the Yamabe equation `L_g u = λ u ^ (pₙ - 1)`.
* `yamabeQuotient_eq_of_conformalLaplacian_eq`: a solution of the Euler–Lagrange equation has
  `Q_g(u) = λ N(u) ^ (1 - 2 / pₙ)`, and
  `yamabeQuotient_eq_of_conformalLaplacian_eq_of_integral_eq_one`: `Q_g(u) = λ` at unit norm.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2 (the
  Yamabe functional, its Euler–Lagrange equation and the identification of the multiplier).
-/

public section

open Bundle MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The **Yamabe quotient**
`Q_g(u) = (∫ (aₙ |grad u|² + Scal_g u²) dV_g) / (∫ |u| ^ pₙ dV_g) ^ (2 / pₙ)` of a function `u`
on a Riemannian manifold of dimension `n`, where `aₙ = 4 (n - 1) / (n - 2)` and
`pₙ = 2 n / (n - 2)`. Its classical meaning is for differentiable `u`. -/
def yamabeQuotient (u : M → ℝ) : ℝ :=
  (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
      ∂riemannianVolume I M) /
    (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
      (2 / criticalExponent (finrank ℝ E))

/-- Unfolding lemma for `TauCeti.Yamabe.yamabeQuotient`. -/
theorem yamabeQuotient_def (u : M → ℝ) :
    yamabeQuotient I u =
      (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
          ∂riemannianVolume I M) /
        (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
          (2 / criticalExponent (finrank ℝ E)) :=
  (rfl)

variable {I}

/-- **Scale invariance of the Yamabe quotient.** In dimension `n > 2`, multiplying a
function by a nonzero constant does not change its Yamabe quotient. -/
theorem yamabeQuotient_smul (hn : 2 < finrank ℝ E) {u : M → ℝ} {c : ℝ} (hc : c ≠ 0) :
    yamabeQuotient I (c • u) = yamabeQuotient I u := by
  have hp := criticalExponent_pos hn
  have hnum : ∀ x, conformalCoefficient (finrank ℝ E) * ‖mgradient I (c • u) x‖ ^ 2 +
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (c • u) x ^ 2 =
      c ^ 2 * (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2) := by
    intro x
    rw [mgradient_smul c, Pi.smul_apply, Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, smul_eq_mul]
    ring
  have hden : ∀ x, |(c • u) x| ^ criticalExponent (finrank ℝ E) =
      |c| ^ criticalExponent (finrank ℝ E) * |u x| ^ criticalExponent (finrank ℝ E) := by
    intro x
    rw [Pi.smul_apply, smul_eq_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  have hc2 : (|c| ^ criticalExponent (finrank ℝ E)) ^ (2 / criticalExponent (finrank ℝ E)) =
      c ^ 2 := by
    rw [← Real.rpow_mul (abs_nonneg _), mul_div_cancel₀ _ hp.ne', Real.rpow_two, sq_abs]
  simp only [yamabeQuotient_def, hnum, hden, integral_const_mul]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
      (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _), hc2,
    mul_div_mul_left _ _ (pow_ne_zero 2 hc)]

/-! ### The first variation -/

section FirstVariation

variable [CompactSpace M]

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- A continuous function on a compact Riemannian manifold is integrable. -/
private theorem integrable_of_continuous {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianVolume I M) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The energy `∫ (aₙ |grad (u + t v)|² + Scal_g (u + t v)²) dV` of `u + t v` is a quadratic
polynomial in `t`, with derivative `2 ∫ (aₙ ⟪grad v, grad u⟫ + Scal_g v u) dV` at `t = 0`. -/
private theorem hasDerivAt_integral_energy_add_smul {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 1 u)
    (hv : ContMDiff I 𝓘(ℝ) 1 v) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, (conformalCoefficient (finrank ℝ E) *
        ‖mgradient I (u + t • v) x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
        ∂riemannianVolume I M)
      (2 * ∫ x, (conformalCoefficient (finrank ℝ E) *
          inner ℝ (mgradient I v x) (mgradient I u x) +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (v x * u x))
        ∂riemannianVolume I M) 0 := by
  set a := conformalCoefficient (finrank ℝ E)
  set S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  set μ := riemannianVolume I M
  have hS : Continuous S :=
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous
  set eu : M → ℝ := fun x ↦ a * ‖mgradient I u x‖ ^ 2 + S x * u x ^ 2
  set b : M → ℝ := fun x ↦ a * inner ℝ (mgradient I v x) (mgradient I u x) + S x * (v x * u x)
  set ev : M → ℝ := fun x ↦ a * ‖mgradient I v x‖ ^ 2 + S x * v x ^ 2
  have hgrad (t : ℝ) : mgradient I (u + t • v) = mgradient I u + t • mgradient I v := by
    rw [mgradient_add (hu.mdifferentiable one_ne_zero)
      ((hv.mdifferentiable one_ne_zero).const_smul t), mgradient_smul t]
  have hpt (t : ℝ) (x : M) : a * ‖mgradient I (u + t • v) x‖ ^ 2 + S x * (u + t • v) x ^ 2 =
      eu x + 2 * t * b x + t ^ 2 * ev x := by
    simp only [hgrad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, eu, b, ev, norm_add_sq_real,
      norm_smul, inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_comm]
    ring
  have hnorm (w : M → ℝ) (hw : ContMDiff I 𝓘(ℝ) 1 w) :
      Continuous fun x ↦ ‖mgradient I w x‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using continuous_inner_mgradient hw hw
  have heu : Integrable eu μ := integrable_of_continuous
    ((continuous_const.mul (hnorm u hu)).add (hS.mul (hu.continuous.pow 2)))
  have hb : Integrable b μ := integrable_of_continuous
    ((continuous_const.mul (continuous_inner_mgradient hv hu)).add
      (hS.mul (hv.continuous.mul hu.continuous)))
  have hev : Integrable ev μ := integrable_of_continuous
    ((continuous_const.mul (hnorm v hv)).add (hS.mul (hv.continuous.pow 2)))
  have hEt (t : ℝ) : ∫ x, (a * ‖mgradient I (u + t • v) x‖ ^ 2 + S x * (u + t • v) x ^ 2) ∂μ =
      (∫ x, eu x ∂μ) + 2 * t * (∫ x, b x ∂μ) + t ^ 2 * ∫ x, ev x ∂μ := by
    simp only [hpt]
    rw [integral_add (f := fun x ↦ eu x + 2 * t * b x) (g := fun x ↦ t ^ 2 * ev x)
      (heu.add (hb.const_mul _)) (hev.const_mul _),
      integral_add (f := eu) (g := fun x ↦ 2 * t * b x) heu (hb.const_mul _), integral_const_mul,
      integral_const_mul]
  simp only [hEt]
  have h := (((hasDerivAt_id (0 : ℝ)).const_mul (2 * ∫ x, b x ∂μ)).const_add
    (∫ x, eu x ∂μ)).add ((hasDerivAt_pow 2 (0 : ℝ)).const_mul (∫ x, ev x ∂μ))
  convert h using 1
  · funext t
    simp only [Pi.add_apply, id]
    ring
  · simp

/-- **The first variation of the Yamabe quotient.** On a compact manifold of dimension `n > 2`,
let `u ≠ 0` and `v` be `C¹` functions, and write `N(u) = ∫ |u| ^ pₙ dV`. Then
`t ↦ Q_g(u + t v)` has derivative
`2 ((∫ (aₙ ⟪grad v, grad u⟫ + Scal_g v u) dV) / N(u) ^ (2 / pₙ) -
  Q_g(u) (∫ |u| ^ (pₙ - 2) u v dV) / N(u))` at `t = 0`. -/
theorem hasDerivAt_yamabeQuotient_add_smul (hn : 2 < finrank ℝ E) {u v : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 1 u) (hv : ContMDiff I 𝓘(ℝ) 1 v) (hu0 : u ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ yamabeQuotient I (u + t • v))
      (2 * ((∫ x, (conformalCoefficient (finrank ℝ E) *
              inner ℝ (mgradient I v x) (mgradient I u x) +
            (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (v x * u x))
            ∂riemannianVolume I M) /
          (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
            (2 / criticalExponent (finrank ℝ E)) -
        yamabeQuotient I u *
          (∫ x, |u x| ^ (criticalExponent (finrank ℝ E) - 2) * u x * v x
            ∂riemannianVolume I M) /
          ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M)) 0 := by
  set p := criticalExponent (finrank ℝ E)
  set μ := riemannianVolume I M
  have hp : 2 < p := two_lt_criticalExponent hn
  -- The numerator `E(t)` and the denominator `N(t) ^ (2 / p)` of `Q_g(u + t v)`.
  set E₀ := ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2) ∂μ
  set B := ∫ x, (conformalCoefficient (finrank ℝ E) *
      inner ℝ (mgradient I v x) (mgradient I u x) +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (v x * u x)) ∂μ
  set N := ∫ x, |u x| ^ p ∂μ
  set J := ∫ x, |u x| ^ (p - 2) * u x * v x ∂μ
  have hN0 : 0 < N := integral_abs_rpow_pos hu.continuous hu0 (by linarith)
  have hE := hasDerivAt_integral_energy_add_smul hu hv
  have hN := hasDerivAt_integral_abs_add_mul_rpow (μ := μ) hu.continuous hv.continuous
    (p := p) (by linarith)
  have h0 : ∫ x, |u x + 0 * v x| ^ p ∂μ = N := by
    simp only [zero_mul, add_zero]
    rfl
  have hD := hN.rpow_const (p := 2 / p) (Or.inl (h0 ▸ hN0.ne'))
  have hQ := hE.div hD (h0 ▸ (Real.rpow_pos_of_pos hN0 _).ne')
  have hE0 : ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I (u + (0 : ℝ) • v) x‖ ^ 2 +
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x *
        (u + (0 : ℝ) • v) x ^ 2) ∂μ = E₀ := by
    simp only [zero_smul, add_zero]
    rfl
  have hB : ∫ x, (conformalCoefficient (finrank ℝ E) *
      inner ℝ (mgradient I v x) (mgradient I u x) +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (v x * u x)) ∂μ = B := rfl
  have hJ : ∫ x, |u x| ^ (p - 2) * u x * v x ∂μ = J := rfl
  rw [h0, hE0, hB, hJ] at hQ
  have hfun : (fun t : ℝ ↦ yamabeQuotient I (u + t • v)) = fun t ↦
      (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I (u + t • v) x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
        ∂μ) / (∫ x, |u x + t * v x| ^ p ∂μ) ^ (2 / p) := by
    funext t
    exact yamabeQuotient_def I (u + t • v)
  rw [hfun]
  convert hQ using 1
  have hQu : yamabeQuotient I u = E₀ / N ^ (2 / p) := yamabeQuotient_def I u
  rw [hQu, Real.rpow_sub_one hN0.ne']
  have hpos : 0 < N ^ (2 / p) := Real.rpow_pos_of_pos hN0 _
  have hp0 : p ≠ 0 := by linarith
  field_simp

variable [I.Boundaryless]

/-- **The multiplier of the Euler–Lagrange equation.** On a closed manifold of dimension `n > 2`,
if a `C²` function `u` solves `L_g u = λ |u| ^ (pₙ - 2) u`, then
`Q_g(u) = λ (∫ |u| ^ pₙ dV) ^ (1 - 2 / pₙ)`. -/
theorem yamabeQuotient_eq_of_conformalLaplacian_eq (hn : 2 < finrank ℝ E) {u : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) {c : ℝ}
    (h : ∀ x, conformalLaplacian I u x =
      c * (|u x| ^ (criticalExponent (finrank ℝ E) - 2) * u x)) :
    yamabeQuotient I u =
      c * (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
        (1 - 2 / criticalExponent (finrank ℝ E)) := by
  have hp := two_lt_criticalExponent hn
  -- Integrating the equation against `u` gives `∫ u L_g u dV = λ ∫ |u| ^ pₙ dV`.
  have hpt (x : M) : u x * conformalLaplacian I u x =
      c * |u x| ^ criticalExponent (finrank ℝ E) := by
    have hsq : |u x| ^ (criticalExponent (finrank ℝ E) - 2) * u x ^ 2 =
        |u x| ^ criticalExponent (finrank ℝ E) := by
      rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add' (abs_nonneg _) (by linarith),
        sub_add_cancel]
    rw [h x, ← hsq]
    ring
  rw [yamabeQuotient_def, ← integral_mul_conformalLaplacian_self hu
    (HasCompactSupport.of_compactSpace u)]
  simp only [hpt, integral_const_mul]
  rcases (integral_nonneg fun x ↦ Real.rpow_nonneg (abs_nonneg (u x))
    (criticalExponent (finrank ℝ E)) : 0 ≤ ∫ x, |u x| ^ criticalExponent (finrank ℝ E)
      ∂riemannianVolume I M).eq_or_lt with hN | hN
  · rw [← hN, Real.zero_rpow (by positivity), Real.zero_rpow]
    · simp
    · have : 2 / criticalExponent (finrank ℝ E) < 1 := (div_lt_one (by linarith)).2 hp
      linarith
  · rw [Real.rpow_sub hN, Real.rpow_one, mul_div_assoc]

/-- **The multiplier at unit norm.** On a closed manifold of dimension `n > 2`, if a `C²` function
`u` with `∫ |u| ^ pₙ dV = 1` solves `L_g u = λ |u| ^ (pₙ - 2) u`, then `λ = Q_g(u)`. -/
theorem yamabeQuotient_eq_of_conformalLaplacian_eq_of_integral_eq_one (hn : 2 < finrank ℝ E)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) {c : ℝ}
    (h : ∀ x, conformalLaplacian I u x =
      c * (|u x| ^ (criticalExponent (finrank ℝ E) - 2) * u x))
    (h1 : ∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M = 1) :
    yamabeQuotient I u = c := by
  rw [yamabeQuotient_eq_of_conformalLaplacian_eq hn hu h, h1, Real.one_rpow, mul_one]

/-- The first variation of the Yamabe quotient on a closed manifold, as the integral of `v`
against `L_g u - λ |u| ^ (pₙ - 2) u` with `λ = Q_g(u) N(u) ^ (2 / pₙ) / N(u)`. -/
private theorem hasDerivAt_yamabeQuotient_add_smul_eq_integral (hn : 2 < finrank ℝ E)
    {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (hv : ContMDiff I 𝓘(ℝ) 1 v) (hu0 : u ≠ 0) :
    HasDerivAt (fun t : ℝ ↦ yamabeQuotient I (u + t • v))
      (2 / (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
          (2 / criticalExponent (finrank ℝ E)) *
        ∫ x, v x * (conformalLaplacian I u x -
          yamabeQuotient I u *
            (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
              (2 / criticalExponent (finrank ℝ E)) /
            (∫ x, |u x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) *
            (|u x| ^ (criticalExponent (finrank ℝ E) - 2) * u x)) ∂riemannianVolume I M) 0 := by
  have hp := two_lt_criticalExponent hn
  convert hasDerivAt_yamabeQuotient_add_smul hn (hu.of_le one_le_two) hv hu0 using 1
  set p := criticalExponent (finrank ℝ E)
  set N := ∫ x, |u x| ^ p ∂riemannianVolume I M
  have hN0 : 0 < N := integral_abs_rpow_pos hu.continuous hu0 (by linarith)
  have hL : Integrable (fun x ↦ v x * conformalLaplacian I u x) (riemannianVolume I M) :=
    integrable_of_continuous (hv.continuous.mul
      (contMDiff_conformalLaplacian (k := 0) (by simp) (by simpa using hu)).continuous)
  have hJ : Integrable (fun x ↦ |u x| ^ (p - 2) * u x * v x) (riemannianVolume I M) :=
    integrable_of_continuous (((hu.continuous.abs.rpow_const fun _ ↦ Or.inr (by linarith)).mul
      hu.continuous).mul hv.continuous)
  have hsplit : (fun x ↦ v x * (conformalLaplacian I u x -
      yamabeQuotient I u * N ^ (2 / p) / N * (|u x| ^ (p - 2) * u x))) =
      fun x ↦ v x * conformalLaplacian I u x -
        yamabeQuotient I u * N ^ (2 / p) / N * (|u x| ^ (p - 2) * u x * v x) := by
    funext x
    ring
  rw [hsplit, integral_sub hL (hJ.const_mul _), integral_const_mul,
    ← integral_mul_conformalLaplacian hv (HasCompactSupport.of_compactSpace v) hu]
  have hpos : 0 < N ^ (2 / p) := Real.rpow_pos_of_pos hN0 _
  field_simp

/-- **The Euler–Lagrange equation of the Yamabe quotient.** On a closed manifold of dimension
`n > 2`, a nonzero `C²` function `u` is a critical point of the Yamabe quotient, in the sense that
`t ↦ Q_g(u + t v)` has derivative `0` at `t = 0` for every smooth `v`, exactly when it solves
`L_g u = λ |u| ^ (pₙ - 2) u` for some constant `λ`. -/
theorem forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_conformalLaplacian_eq
    (hn : 2 < finrank ℝ E) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu0 : u ≠ 0) :
    (∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
        HasDerivAt (fun t : ℝ ↦ yamabeQuotient I (u + t • v)) 0 0) ↔
      ∃ c : ℝ, ∀ x, conformalLaplacian I u x =
        c * (|u x| ^ (criticalExponent (finrank ℝ E) - 2) * u x) := by
  have hp := two_lt_criticalExponent hn
  set p := criticalExponent (finrank ℝ E)
  set N := ∫ x, |u x| ^ p ∂riemannianVolume I M
  have hN0 : 0 < N := integral_abs_rpow_pos hu.continuous hu0 (by linarith)
  have hpos : 0 < N ^ (2 / p) := Real.rpow_pos_of_pos hN0 _
  set c₀ := yamabeQuotient I u * N ^ (2 / p) / N with hc₀_def
  constructor
  · intro hcrit
    have hcont : Continuous fun x ↦
        conformalLaplacian I u x - c₀ * (|u x| ^ (p - 2) * u x) :=
      (contMDiff_conformalLaplacian (k := 0) (by simp) (by simpa using hu)).continuous.sub
        (continuous_const.mul ((hu.continuous.abs.rpow_const fun _ ↦ Or.inr (by linarith)).mul
          hu.continuous))
    -- The defect of the equation integrates to zero against every smooth function.
    have hae : ∀ᵐ x ∂riemannianVolume I M,
        conformalLaplacian I u x - c₀ * (|u x| ^ (p - 2) * u x) = 0 := by
      refine ae_eq_zero_of_integral_contMDiff_smul_eq_zero I hcont.locallyIntegrable
        fun v hv _ ↦ ?_
      have h := (hasDerivAt_yamabeQuotient_add_smul_eq_integral hn hu (hv.of_le (by simp))
        hu0).unique (hcrit v hv)
      rcases mul_eq_zero.1 h with h | h
      · exact absurd h (div_ne_zero two_ne_zero hpos.ne')
      · exact h
    refine ⟨c₀, fun x ↦ sub_eq_zero.1 ?_⟩
    exact congrFun ((hcont.ae_eq_iff_eq _ continuous_zero).1 hae) x
  · rintro ⟨c, hc⟩ v hv
    -- The multiplier of a solution is `c₀`.
    -- `Q_g(u) = c N ^ (1 - 2 / p)`, so `c₀ = c N ^ (1 - 2 / p) N ^ (2 / p) / N = c N / N = c`.
    have hpow : N ^ (1 - 2 / p) * N ^ (2 / p) = N := by
      rw [← Real.rpow_add hN0, sub_add_cancel, Real.rpow_one]
    have hc₀ : c₀ = c := by
      rw [hc₀_def, yamabeQuotient_eq_of_conformalLaplacian_eq hn hu hc, mul_assoc, hpow,
        mul_div_cancel_right₀ c hN0.ne']
    have hint (x : M) : v x * (conformalLaplacian I u x - c₀ * (|u x| ^ (p - 2) * u x)) = 0 := by
      rw [hc x, hc₀, sub_self, mul_zero]
    convert hasDerivAt_yamabeQuotient_add_smul_eq_integral hn hu (hv.of_le (by simp)) hu0 using 1
    exact (mul_eq_zero_of_right _ ((integral_congr_ae (ae_of_all _ hint)).trans
      (integral_zero M ℝ))).symm

/-- **The Euler–Lagrange equation for nonnegative functions.** On a closed manifold of dimension
`n > 2`, a nonzero nonnegative `C²` function `u` is a critical point of the Yamabe quotient
exactly when it solves the Yamabe equation `L_g u = λ u ^ (pₙ - 1)` for some constant `λ`. -/
theorem forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_conformalLaplacian_eq_of_nonneg
    (hn : 2 < finrank ℝ E) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu0 : u ≠ 0)
    (hnn : 0 ≤ u) :
    (∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
        HasDerivAt (fun t : ℝ ↦ yamabeQuotient I (u + t • v)) 0 0) ↔
      ∃ c : ℝ, ∀ x, conformalLaplacian I u x =
        c * u x ^ (criticalExponent (finrank ℝ E) - 1) := by
  have hp := two_lt_criticalExponent hn
  have hpow (x : M) : |u x| ^ (criticalExponent (finrank ℝ E) - 2) * u x =
      u x ^ (criticalExponent (finrank ℝ E) - 1) := by
    rw [abs_of_nonneg (hnn x), ← Real.rpow_add_one' (hnn x) (by linarith)]
    ring_nf
  simpa only [hpow] using
    forall_hasDerivAt_yamabeQuotient_add_smul_iff_exists_conformalLaplacian_eq hn hu hu0

end FirstVariation

end TauCeti.Yamabe
