/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Energy
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.RPow
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# The Euler–Lagrange equation of the Yamabe quotient

Let `(M, g)` be a closed Riemannian manifold of dimension `n`, write `aₙ = 4 (n - 1) / (n - 2)`,
`L_g = aₙ Δ⁺_g + Scal_g` for the conformal Laplacian, and

`E(w) = ∫ (aₙ |grad w|² + Scal_g w²) dV_g`

for the energy of a function `w`. For a real exponent `q ≠ 0` the Yamabe quotient of exponent `q`
is `Q_q(w) = E(w) / (∫ |w| ^ q dV_g) ^ (2 / q)`; the Yamabe quotient proper is the critical case
`q = pₙ = 2 n / (n - 2)`, and the subcritical exponents `2 < q < pₙ` give the approximating
problems of the variational method.

This file computes the first variation of `Q_q` at a positive function and identifies its
critical points. The energy is a quadratic form whose polarization is `∫ v L_g u dV_g` (Green's
identity for `L_g`), so `E(u + t v) = E(u) + 2 t ∫ v L_g u dV_g + t² E(v)`. The first variation of
the denominator at a positive `u` is `q ∫ u ^ (q - 1) v dV_g`. Combining the two, for positive
`C²` functions `u` and `C²` directions `v`,

`d/dt|_{t = 0} Q_q(u + t v) = 2 (∫ u ^ q dV_g) ^ (-2 / q) ∫ v (L_g u - λ u ^ (q - 1)) dV_g`,
`λ = E(u) / ∫ u ^ q dV_g`.

Consequently a smooth positive `u` is a critical point of `Q_q`, in the sense that this derivative
vanishes in every smooth direction, exactly when it solves the Euler–Lagrange equation
`L_g u = λ u ^ (q - 1)`. The constant of any positive solution of `L_g u = c u ^ (q - 1)` is
forced to be `λ`, and `λ = Q_q(u)` when `∫ u ^ q dV_g = 1`. For the critical exponent `q = pₙ`
the Euler–Lagrange equation is the Yamabe equation, so a smooth positive `u` is a critical point
of the Yamabe quotient of `g` exactly when `u ^ (4 / (n - 2)) g` has constant scalar curvature.

These are the classical smooth statements. The variational theory works on the Sobolev space
`H¹(M)`, where critical points are weak solutions of `L_g u = λ |u| ^ (q - 2) u`; the smooth
positive case here is the form in which a regular positive minimizer yields a constant scalar
curvature metric.

The metric is the `RiemannianBundle` instance of the tangent bundle, as for
`TauCeti.Yamabe.conformalLaplacian`, except in the final scalar-curvature statement, which, like
`TauCeti.Yamabe.scalarCurvature_rescale_eq_iff_conformalLaplacian_eq`, names the metric `g`
explicitly so that `g` and `u ^ (4 / (n - 2)) g` can be compared.

## Main results

* `TauCeti.Yamabe.integral_energy_add_smul`: `E(u + t v) = E(u) + 2 t ∫ v L_g u + t² E(v)`.
* `TauCeti.Yamabe.hasDerivAt_integral_energy_add_smul`: the first variation `2 ∫ v L_g u` of
  the energy.
* `TauCeti.Yamabe.hasDerivAt_yamabe_quotient_add_smul`: the first variation of `Q_q` at a
  positive function.
* `TauCeti.Yamabe.forall_hasDerivAt_yamabe_quotient_iff_conformalLaplacian_eq`: a smooth
  positive `u` is critical for `Q_q` iff `L_g u = λ u ^ (q - 1)`.
* `TauCeti.Yamabe.eq_of_conformalLaplacian_eq_mul_rpow`: a positive solution of
  `L_g u = c u ^ (q - 1)` has `c = λ`.
* `TauCeti.Yamabe.forall_hasDerivAt_yamabe_quotient_iff_exists_conformalLaplacian_eq`: a smooth
  positive `u` is critical for `Q_q` iff it solves `L_g u = c u ^ (q - 1)` for some constant `c`.
* `TauCeti.Yamabe.conformalLaplacian_eq_yamabe_quotient_mul_rpow`: at unit `L^q` norm the
  Lagrange multiplier of a critical point is `Q_q(u)`.
* `TauCeti.Yamabe.forall_hasDerivAt_yamabe_quotient_iff_exists_scalarCurvature_rescale_eq`: for
  `q = pₙ` and `n > 2`, a smooth positive `u` is critical for the Yamabe quotient of `g` iff
  `u ^ (4 / (n - 2)) g` has constant scalar curvature.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §1 (the
  Yamabe functional and its Euler–Lagrange equation) and §4 (the subcritical quotients).
-/

public section

open Bundle MeasureTheory Module TauCeti.Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Yamabe

section FirstVariation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- A continuous function on a closed manifold is integrable for the Riemannian volume. -/
private theorem integrable_of_continuous {f : M → ℝ} (hf : Continuous f) :
    Integrable f (riemannianVolume I M) :=
  hf.integrable_of_hasCompactSupport (.of_compactSpace f)

/-- The integral of a real power of a positive continuous function on a nonempty closed manifold is
positive. -/
private theorem integral_rpow_pos [Nonempty M] {u : M → ℝ} (hu : Continuous u)
    (hu_pos : ∀ x, 0 < u x) (q : ℝ) : 0 < ∫ x, u x ^ q ∂riemannianVolume I M :=
  (hu.rpow_const fun x ↦ Or.inl (hu_pos x).ne').integral_pos_of_hasCompactSupport_nonneg_nonzero
    (.of_compactSpace _) (fun x ↦ (Real.rpow_pos_of_pos (hu_pos x) q).le)
    (Real.rpow_pos_of_pos (hu_pos (Classical.arbitrary M)) q).ne'

variable [I.Boundaryless] [T2Space M]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **Expansion of the Yamabe energy along a line.** On a closed manifold, for `C²` functions
`u`, `v` and every `t : ℝ`, `E(u + t v) = E(u) + 2 t ∫ v L_g u dV + t² E(v)`, where
`E(w) = ∫ (aₙ |grad w|² + Scal_g w²) dV` and `L_g` is the conformal Laplacian. -/
theorem integral_energy_add_smul {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 2 v) (t : ℝ) :
    ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I (u + t • v) x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
        ∂riemannianVolume I M =
      ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
          ∂riemannianVolume I M +
        2 * t * ∫ x, v x * conformalLaplacian I u x ∂riemannianVolume I M +
        t ^ 2 * ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I v x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * v x ^ 2)
          ∂riemannianVolume I M := by
  have htv : ContMDiff I 𝓘(ℝ) 2 (t • v) :=
    ((contMDiff_const (c := t)).mul hv).congr fun x ↦ by simp
  have hw : ContMDiff I 𝓘(ℝ) 2 (u + t • v) := hu.add htv
  rw [← integral_mul_conformalLaplacian_self hw (.of_compactSpace _),
    ← integral_mul_conformalLaplacian_self hu (.of_compactSpace _),
    ← integral_mul_conformalLaplacian_self hv (.of_compactSpace _)]
  have huc := hu.continuous
  have hvc := hv.continuous
  have hLu := (contMDiff_conformalLaplacian (k := 0) (by simp) (by simpa using hu)).continuous
  have hLv := (contMDiff_conformalLaplacian (k := 0) (by simp) (by simpa using hv)).continuous
  have hpt (x : M) : (u + t • v) x * conformalLaplacian I (u + t • v) x =
      u x * conformalLaplacian I u x +
        t * (u x * conformalLaplacian I v x + v x * conformalLaplacian I u x) +
        t ^ 2 * (v x * conformalLaplacian I v x) := by
    rw [conformalLaplacian_add I hu htv, conformalLaplacian_smul I t hv]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  -- Green's identity `∫ u L_g v = ∫ (L_g u) v` merges the two cross terms.
  have hsym := integral_mul_conformalLaplacian_right_eq_left hu (.of_compactSpace _) hv
  simp only [mul_comm (conformalLaplacian I u _) (v _)] at hsym
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)),
    integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)),
    integral_const_mul, integral_const_mul,
    integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)), hsym]
  ring

/-- **First variation of the Yamabe energy.** On a closed manifold, for `C²` functions `u` and
`v`, the energy `E(u + t v) = ∫ (aₙ |grad (u + t v)|² + Scal_g (u + t v)²) dV` has derivative
`2 ∫ v L_g u dV` at `t = 0`, where `L_g` is the conformal Laplacian. -/
theorem hasDerivAt_integral_energy_add_smul {u v : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u)
    (hv : ContMDiff I 𝓘(ℝ) 2 v) :
    HasDerivAt (fun t : ℝ ↦ ∫ x, (conformalCoefficient (finrank ℝ E) *
        ‖mgradient I (u + t • v) x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
        ∂riemannianVolume I M)
      (2 * ∫ x, v x * conformalLaplacian I u x ∂riemannianVolume I M) 0 := by
  simp only [integral_energy_add_smul hu hv]
  set A := ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
    ∂riemannianVolume I M
  set B := ∫ x, v x * conformalLaplacian I u x ∂riemannianVolume I M
  set C := ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I v x‖ ^ 2 +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * v x ^ 2)
    ∂riemannianVolume I M
  have h := ((hasDerivAt_id (0 : ℝ)).const_mul (2 * B)).const_add A |>.add
    ((hasDerivAt_pow 2 (0 : ℝ)).const_mul C)
  convert h using 1
  · funext t
    simp only [Pi.add_apply, id]
    ring
  · simp

/-- **First variation of the Yamabe quotient.** On a nonempty closed manifold, let `q ≠ 0`, let
`u` be a positive `C²` function and `v` a `C²` function. Then the Yamabe quotient of exponent `q`,
`Q_q(w) = E(w) / (∫ |w| ^ q dV) ^ (2 / q)` with `E(w) = ∫ (aₙ |grad w|² + Scal_g w²) dV`, satisfies

`d/dt|_{t = 0} Q_q(u + t v) = 2 (∫ u ^ q dV) ^ (-2 / q) ∫ v (L_g u - λ u ^ (q - 1)) dV`,

where `L_g` is the conformal Laplacian and `λ = E(u) / ∫ u ^ q dV`. -/
theorem hasDerivAt_yamabe_quotient_add_smul [Nonempty M] {q : ℝ} (hq : q ≠ 0) {u v : M → ℝ}
    (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu_pos : ∀ x, 0 < u x) (hv : ContMDiff I 𝓘(ℝ) 2 v) :
    HasDerivAt (fun t : ℝ ↦ (∫ x, (conformalCoefficient (finrank ℝ E) *
        ‖mgradient I (u + t • v) x‖ ^ 2 +
        (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
        ∂riemannianVolume I M) / (∫ x, |(u + t • v) x| ^ q ∂riemannianVolume I M) ^ (2 / q))
      (2 / (∫ x, u x ^ q ∂riemannianVolume I M) ^ (2 / q) *
        ∫ x, v x * (conformalLaplacian I u x -
          (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
            (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
            ∂riemannianVolume I M) / (∫ x, u x ^ q ∂riemannianVolume I M) * u x ^ (q - 1))
          ∂riemannianVolume I M) 0 := by
  set N := ∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
    ∂riemannianVolume I M with hN
  set D := ∫ x, u x ^ q ∂riemannianVolume I M
  set B := ∫ x, v x * conformalLaplacian I u x ∂riemannianVolume I M with hB
  set C := ∫ x, u x ^ (q - 1) * v x ∂riemannianVolume I M with hC
  have huc := hu.continuous
  have hvc := hv.continuous
  have hLu := (contMDiff_conformalLaplacian (k := 0) (by simp) (by simpa using hu)).continuous
  have hpow : Continuous fun x ↦ u x ^ (q - 1) := huc.rpow_const fun x ↦ Or.inl (hu_pos x).ne'
  have hD : 0 < D := integral_rpow_pos huc hu_pos q
  -- The denominator and its power `2 / q`.
  have hden := hasDerivAt_integral_abs_add_mul_rpow (μ := riemannianVolume I M) huc hvc hu_pos q
  have hD0 : ∫ x, |u x + 0 * v x| ^ q ∂riemannianVolume I M = D := by
    simp only [zero_mul, add_zero, abs_of_pos (hu_pos _), D]
  have hden' := hden.rpow_const (p := 2 / q) (Or.inl (hD0 ▸ hD.ne'))
  have h := (hasDerivAt_integral_energy_add_smul hu hv).div hden'
    (hD0 ▸ (Real.rpow_pos_of_pos hD _).ne')
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert h using 1
  -- The two expressions for the derivative agree by algebra.
  have hsplit : ∫ x, v x * (conformalLaplacian I u x - N / D * u x ^ (q - 1))
      ∂riemannianVolume I M = B - N / D * C := by
    simp only [mul_sub]
    rw [integral_sub (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)), ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only
    ring
  simp only [zero_smul, add_zero, hD0, ← hN, ← hB, ← hC]
  rw [hsplit, Real.rpow_sub_one hD.ne']
  have hR := (Real.rpow_pos_of_pos hD (2 / q)).ne'
  field_simp

/-- **Critical points of the Yamabe quotient are solutions of the Euler–Lagrange equation.** On a
nonempty closed manifold, let `q ≠ 0` and let `u` be a smooth positive function. The derivative of
`t ↦ Q_q(u + t v)` at `t = 0` vanishes for every smooth `v` if and only if
`L_g u = λ u ^ (q - 1)`, where `Q_q(w) = E(w) / (∫ |w| ^ q dV) ^ (2 / q)`,
`E(w) = ∫ (aₙ |grad w|² + Scal_g w²) dV`, `L_g` is the conformal Laplacian and
`λ = E(u) / ∫ u ^ q dV`. -/
theorem forall_hasDerivAt_yamabe_quotient_iff_conformalLaplacian_eq [Nonempty M] {q : ℝ}
    (hq : q ≠ 0) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x) :
    (∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
      HasDerivAt (fun t : ℝ ↦ (∫ x, (conformalCoefficient (finrank ℝ E) *
          ‖mgradient I (u + t • v) x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
          ∂riemannianVolume I M) / (∫ x, |(u + t • v) x| ^ q ∂riemannianVolume I M) ^ (2 / q))
        0 0) ↔
      ∀ x, conformalLaplacian I u x =
        (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
          ∂riemannianVolume I M) / (∫ x, u x ^ q ∂riemannianVolume I M) * u x ^ (q - 1) := by
  set c := (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
    (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
    ∂riemannianVolume I M) / (∫ x, u x ^ q ∂riemannianVolume I M) with hc
  have hu2 : ContMDiff I 𝓘(ℝ) 2 u := hu.of_le (by simp)
  have hR : 0 < (∫ x, u x ^ q ∂riemannianVolume I M) ^ (2 / q) :=
    Real.rpow_pos_of_pos (integral_rpow_pos hu.continuous hu_pos q) _
  refine ⟨fun h x ↦ ?_, fun h v hv ↦ ?_⟩
  · -- Test the criticality against the defect `w = L_g u - λ u ^ (q - 1)` itself.
    set w : M → ℝ := fun x ↦ conformalLaplacian I u x - c * u x ^ (q - 1) with hw_def
    have hw : ContMDiff I 𝓘(ℝ) ∞ w :=
      (contMDiff_conformalLaplacian (k := ∞) le_rfl
        (by rwa [show ((∞ : ℕ∞ω) + 2) = ∞ from rfl])).sub
        (contMDiff_const.mul (hu.rpow_const_of_ne (fun x ↦ (hu_pos x).ne') _))
    have h0 := (hasDerivAt_yamabe_quotient_add_smul hq hu2 hu_pos (hw.of_le (by simp))).unique
      (h w hw)
    have hint : ∫ x, w x * w x ∂riemannianVolume I M = 0 := by
      simpa [hR.ne'] using h0
    have hcont : Continuous fun x ↦ w x * w x := hw.continuous.mul hw.continuous
    have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ mul_self_nonneg (w x))
      (integrable_of_continuous hcont)).1 hint
    have hwx : w x * w x = 0 :=
      congrFun ((hcont.ae_eq_iff_eq (riemannianVolume I M) continuous_const).1 hae) x
    exact sub_eq_zero.1 (mul_self_eq_zero.1 hwx)
  · convert hasDerivAt_yamabe_quotient_add_smul hq hu2 hu_pos (hv.of_le (by simp)) using 1
    simp only [← hc, h, sub_self, mul_zero, integral_zero]

/-- **The Lagrange multiplier is determined by the energy.** On a nonempty closed manifold, if a
positive `C²` function `u` solves `L_g u = c u ^ (q - 1)`, where `L_g` is the conformal Laplacian,
then `c = E(u) / ∫ u ^ q dV` with `E(u) = ∫ (aₙ |grad u|² + Scal_g u²) dV`. -/
theorem eq_integral_energy_div_integral_rpow_of_conformalLaplacian_eq [Nonempty M] {q c : ℝ}
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) 2 u) (hu_pos : ∀ x, 0 < u x)
    (h : ∀ x, conformalLaplacian I u x = c * u x ^ (q - 1)) :
    c = (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
          ∂riemannianVolume I M) / (∫ x, u x ^ q ∂riemannianVolume I M) := by
  have hD := integral_rpow_pos (I := I) hu.continuous hu_pos q
  rw [← integral_mul_conformalLaplacian_self hu (.of_compactSpace _), eq_div_iff hD.ne',
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  have hpow := Real.rpow_add (hu_pos x) 1 (q - 1)
  rw [Real.rpow_one, add_sub_cancel] at hpow
  simp only [h, hpow]
  ring

/-- **Critical points of the Yamabe quotient are the positive solutions of the Euler–Lagrange
equation.** On a nonempty closed manifold, let `q ≠ 0` and let `u` be a smooth positive function.
The derivative of `t ↦ Q_q(u + t v)` at `t = 0` vanishes for every smooth `v` if and only if
`L_g u = c u ^ (q - 1)` for some constant `c`, where `Q_q(w) = E(w) / (∫ |w| ^ q dV) ^ (2 / q)`,
`E(w) = ∫ (aₙ |grad w|² + Scal_g w²) dV` and `L_g` is the conformal Laplacian. -/
theorem forall_hasDerivAt_yamabe_quotient_iff_exists_conformalLaplacian_eq [Nonempty M] {q : ℝ}
    (hq : q ≠ 0) {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x) :
    (∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
      HasDerivAt (fun t : ℝ ↦ (∫ x, (conformalCoefficient (finrank ℝ E) *
          ‖mgradient I (u + t • v) x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
          ∂riemannianVolume I M) / (∫ x, |(u + t • v) x| ^ q ∂riemannianVolume I M) ^ (2 / q))
        0 0) ↔
      ∃ c : ℝ, ∀ x, conformalLaplacian I u x = c * u x ^ (q - 1) := by
  rw [forall_hasDerivAt_yamabe_quotient_iff_conformalLaplacian_eq hq hu hu_pos]
  refine ⟨fun h ↦ ⟨_, h⟩, fun ⟨c, h⟩ ↦ ?_⟩
  rwa [← eq_integral_energy_div_integral_rpow_of_conformalLaplacian_eq (hu.of_le (by simp))
    hu_pos h]

/-- **At unit `L^q` norm the Lagrange multiplier is the Yamabe quotient.** On a nonempty closed
manifold, let `q ≠ 0` and let `u` be a smooth positive critical point of the Yamabe quotient
`Q_q(w) = E(w) / (∫ |w| ^ q dV) ^ (2 / q)`, with `E(w) = ∫ (aₙ |grad w|² + Scal_g w²) dV`,
normalized by `∫ u ^ q dV = 1`. Then `L_g u = Q_q(u) u ^ (q - 1)`, where `L_g` is the conformal
Laplacian. -/
theorem conformalLaplacian_eq_yamabe_quotient_mul_rpow [Nonempty M] {q : ℝ} (hq : q ≠ 0)
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hu_pos : ∀ x, 0 < u x)
    (hcrit : ∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
      HasDerivAt (fun t : ℝ ↦ (∫ x, (conformalCoefficient (finrank ℝ E) *
          ‖mgradient I (u + t • v) x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
          ∂riemannianVolume I M) / (∫ x, |(u + t • v) x| ^ q ∂riemannianVolume I M) ^ (2 / q))
        0 0)
    (hnorm : ∫ x, u x ^ q ∂riemannianVolume I M = 1) (x : M) :
    conformalLaplacian I u x =
      (∫ x, (conformalCoefficient (finrank ℝ E) * ‖mgradient I u x‖ ^ 2 +
          (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * u x ^ 2)
          ∂riemannianVolume I M) / (∫ x, |u x| ^ q ∂riemannianVolume I M) ^ (2 / q) *
        u x ^ (q - 1) := by
  have h := (forall_hasDerivAt_yamabe_quotient_iff_conformalLaplacian_eq hq hu hu_pos).1 hcrit x
  simp only [abs_of_pos (hu_pos _), hnorm, Real.one_rpow, div_one] at h ⊢
  exact h

end FirstVariation

section ScalarCurvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M] [Nonempty M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]

/-- **Critical points of the Yamabe quotient give constant scalar curvature.** On a nonempty
closed manifold of dimension `n > 2` with a smooth metric `g`, let `u` be a positive function such
that `ĝ = u ^ (4 / (n - 2)) g` is a smooth metric. Then `u` is a critical point of the Yamabe
quotient `Q_g(w) = E_g(w) / (∫ |w| ^ pₙ dV_g) ^ (2 / pₙ)` of `g`, with
`E_g(w) = ∫ (aₙ |grad_g w|² + Scal_g w²) dV_g` and `pₙ = 2 n / (n - 2)`, in the sense that the
derivative of `t ↦ Q_g(u + t v)` at `t = 0` vanishes for every smooth `v`, if and only if `ĝ` has
constant scalar curvature. -/
theorem forall_hasDerivAt_yamabe_quotient_iff_exists_scalarCurvature_rescale_eq
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hn : 2 < finrank ℝ E) {u : M → ℝ} (hu_pos : ∀ x, 0 < u x)
    {hf : ContMDiff I 𝓘(ℝ) ∞ fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))}
    {hf_pos : ∀ x, 0 < u x ^ (4 / ((finrank ℝ E : ℝ) - 2))} :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
      ∀ v : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ v →
        HasDerivAt (fun t : ℝ ↦ (∫ x, (conformalCoefficient (finrank ℝ E) *
            ‖mgradient I (u + t • v) x‖ ^ 2 +
            (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x * (u + t • v) x ^ 2)
            ∂riemannianVolume I M) /
            (∫ x, |(u + t • v) x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
              (2 / criticalExponent (finrank ℝ E)))
          0 0) ↔
      ∃ c : ℝ, ∀ x, (g.rescale (fun x ↦ u x ^ (4 / ((finrank ℝ E : ℝ) - 2))) hf
        hf_pos).scalarCurvature x = c := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have hn' : (finrank ℝ E : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < finrank ℝ E := by exact_mod_cast hn
    linarith
  have hu : ContMDiff I 𝓘(ℝ) ∞ u := hf.of_rpow_const (div_ne_zero four_ne_zero hn') hu_pos
  refine (forall_hasDerivAt_yamabe_quotient_iff_exists_conformalLaplacian_eq
    (criticalExponent_pos hn).ne' hu hu_pos).trans
    (exists_congr fun c ↦ forall_congr' fun x ↦ ?_)
  exact (scalarCurvature_rescale_eq_iff_conformalLaplacian_eq g hn.ne' hu_pos c x).symm

end ScalarCurvature

end TauCeti.Yamabe
