/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature
public import TauCeti.Geometry.Euclidean.Volume.Polar
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
import TauCeti.Analysis.Calculus.DifferentialForm.KahlerFlux
import TauCeti.Geometry.Euclidean.Volume.Sphere
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Taubes's monotonicity inequality for the defect energy

In the large-parameter analysis of the Seiberg–Witten equations on a symplectic four-manifold, a
solution at parameter `r` has normalized spinor `ψ = φ + β`, with `φ` in the canonical line and `β`
in its complement, and curvature `F = i F_a` of the connection on the twisting line. Its **defect
energy** on a ball is

`E(σ) = μ(closedBall x σ)`,  `μ = (r / 4) |1 - |φ|² - |β|²| dvol`.

This file derives Taubes's differential inequality

`E(σ) ≤ (σ / 2) (1 + C r^(-1/2)) E'(σ) + K σ⁴`  for almost every `σ ∈ (0, R)`

in a flat chart, from the curvature equation `F + ⋆F = (r / 4) ω - q(√r ψ) - η` and the coarse
bounds `|φ|² + |β|² ≤ 1 + C / r`, `|β|² ≤ (C / r) w₊ + C / r²` and
`|F⁻| ≤ (r / (4 √2)) (1 + C r^(-1/2)) w₊ + C`, `w₊ = max (1 - |φ|²) 0`, taken as hypotheses on the
ball `ball x R`. The constant `K` is chosen before `r`, `R`, the centre and the solution, so it is
independent of them; it depends only on `C`, the bound `N` on the forcing `η` and the ambient space,
through the volume of its unit ball
(`TauCeti.SeibergWitten.exists_ae_measure_closedBall_le_mul_deriv_add`). This is the hypothesis of
the quadratic lower bound `E(σ) ≥ c σ²` at a zero of `φ` and of the covering bound for the zero set
(`TauCeti.exists_forall_ofReal_mul_sq_le_measure_closedBall_of_ae_le`,
`TauCeti.exists_forall_coveringNumber_le_of_ae_le`), with no curvature correction `C σ` since the
chart is flat.

The argument is Taubes's. The flux identity for the `ω`-component of the closed form `F`
(`TauCeti.AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq`) expresses
`∫_{ball x σ} ⟪ω, F⟫` as `(σ / 2)` times the integral over the sphere of `B(w, w)`, the Hermitian
part of `F` on a unit vector `w` orthogonal to the radial direction and its `J`-image. Two pointwise
consequences of the curvature equation and the coarse bounds, from
`TauCeti.Analysis.PDE.SeibergWitten.LargeParameterCurvature`, then compare both sides with the
defect density:

* in the interior, `(r / 4) |1 - |φ|² - |β|²| ≤ ⟪ω, F⟫ + (√2 N + C) / 2`, because
  `⟪ω, F⟫ = (r / 4) (1 - |φ|² + |β|²) - ⟪ω, η⟫ / 2`
  (`TauCeti.SeibergWitten.mul_abs_one_sub_sub_le_inner_add`);
* on the sphere, `B(w, w) ≤ ⟪ω, F⟫ / 2 + |F⁻| / √2`, the largest value of the Hermitian part, is at
  most `(1 + C r^(-1/2))` times the defect density plus a constant
  (`TauCeti.SeibergWitten.mul_inner_kahlerForm_sub_hermitianForm_le`).

The sphere integral of the defect density is the derivative `E'(σ)` for almost every `σ`
(`TauCeti.ae_hasDerivAt_setIntegral_ball`), and the Hausdorff measure of the sphere is `4 |B₁| σ³`
(`TauCeti.euclideanHausdorffMeasure_sphere`).

The fields only need to be defined on the ball: the curvature `F` is a closed `C¹` two-form on
`ball x R`, the input of the flux identity, such as `F = -db` for a `C²` connection form `b` as in
`TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent`, and `φ`, `β` are continuous on `ball x R`.
Deriving the coarse bounds from the equations, and the curvature corrections `(1 + C σ)` on a curved
four-manifold, are not done here.

## Main results

* `TauCeti.SeibergWitten.exists_ae_measure_closedBall_le_mul_deriv_add`: the monotonicity
  inequality for the defect energy.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
* C. H. Taubes, *Seiberg–Witten invariants and pseudo-holomorphic subvarieties for self-dual,
  harmonic 2-forms*, Geom. Topol. 3 (1999), 167–210.
-/

public section

noncomputable section

open CliffordAlgebra Module Metric MeasureTheory Filter Set exteriorPower
open scoped RealInnerProductSpace Topology

namespace TauCeti.SeibergWitten

section Integrated

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  [MeasurableSpace V] [BorelSpace V]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

attribute [local instance] finiteDimensional_of_finrank_four

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂₃ : J (e 2) = e 3) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
  (hkl : 2 + 2 = finrank ℝ V) (he : e.toBasis.orientation = o)

include h₀ h₂₃ hQ he

/-- **Taubes's monotonicity inequality for the defect energy**, in a flat chart. Work in an
oriented four-dimensional inner product space with a constant unitary frame `e`, `J e₀ = e₁`,
`J e₂ = e₃`, and Kähler two-vector `ω`. Fix constants `C, N ≥ 0`. There is `K ≥ 0` such that for
every `r ≥ 1`, every ball `ball x R` and every solution on it of the large-parameter curvature
equation `F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`, with `φ` in the canonical line and `β` in its
complement, `|η| ≤ N` and the coarse bounds `|φ|² + |β|² ≤ 1 + C / r`,
`|β|² ≤ (C / r) w₊ + C / r²` and `|F⁻| ≤ (r / (4 √2)) (1 + C / √r) w₊ + C`, where
`w₊ = max (1 - |φ|²) 0`, the defect energy `E(σ) = μ(closedBall x σ)` of
`μ = (r / 4) |1 - |φ|² - |β|²| dvol` satisfies

`E(σ) ≤ (σ / 2) (1 + C / √r) E'(σ) + K σ⁴`

for almost every `σ ∈ (0, R)`. Here `F` is the curvature `i F_a`, read as a two-vector, which is
`C¹` and closed on `ball x R` (for instance `-db` for a `C²` connection form `b`), and `φ`, `β`
are continuous on `ball x R`. -/
theorem exists_ae_measure_closedBall_le_mul_deriv_add {C N : ℝ} (hC : 0 ≤ C) (hN : 0 ≤ N) :
    ∃ K, 0 ≤ K ∧ ∀ ⦃r : ℝ⦄ ⦃F η : V → ⋀[ℝ]^2 V⦄ ⦃φ β : V → positiveHalfSpinors o ρ⦄ ⦃x : V⦄
      ⦃R : ℝ⦄, 1 ≤ r → ContDiffOn ℝ 1 F (ball x R) →
      (∀ y ∈ ball x R, extDeriv (fun z ↦ alternatingFormEquiv V 2 (F z)) y = 0) →
      ContinuousOn φ (ball x R) → ContinuousOn β (ball x R) →
      (∀ y ∈ ball x R, cliffordProjection o ρ J.kahlerForm (φ y) = φ y) →
      (∀ y ∈ ball x R, cliffordProjection o ρ J.kahlerForm (β y) = 0) →
      (∀ y ∈ ball x R, F y + o.hodgeStar hkl (F y) = (r / 4) • J.kahlerForm -
        (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ y + β y)) : ⋀[ℝ]^2 V) - η y) →
      (∀ y ∈ ball x R, ‖η y‖ ≤ N) →
      (∀ y ∈ ball x R, ‖(2⁻¹ : ℝ) • (F y - o.hodgeStar hkl (F y))‖ ≤
        r / (4 * √2) * (1 + C / √r) * max (1 - ‖φ y‖ ^ 2) 0 + C) →
      (∀ y ∈ ball x R, ‖φ y‖ ^ 2 + ‖β y‖ ^ 2 ≤ 1 + C / r) →
      (∀ y ∈ ball x R, ‖β y‖ ^ 2 ≤ C / r * max (1 - ‖φ y‖ ^ 2) 0 + C / r ^ 2) →
      ∀ᵐ σ, σ ∈ Ioo 0 R →
        ((volume : Measure V).withDensity (fun y ↦ ENNReal.ofReal
            (r / 4 * |1 - ‖φ y‖ ^ 2 - ‖β y‖ ^ 2|)) (closedBall x σ)).toReal ≤
          σ / 2 * (1 + C / √r) * deriv (fun σ ↦ ((volume : Measure V).withDensity
            (fun y ↦ ENNReal.ofReal (r / 4 * |1 - ‖φ y‖ ^ 2 - ‖β y‖ ^ 2|))
              (closedBall x σ)).toReal) σ + K * σ ^ 4 := by
  set N₁ := (√2 * N + C) / 2
  set K₂ := (1 + C) * C / 2 + C / 4 + √2 * N / 4 + C / √2
  set V₁ := (volume : Measure V).real (ball 0 1)
  refine ⟨V₁ * (N₁ + 2 * K₂), by positivity, ?_⟩
  intro r F η φ β x R hr hF hdF hφc hβc hφ hβ hFeq hη hFm hφβ hβK
  -- Writing `E(σ) = ∫_{ball x σ} d` for the defect density `d`, the flux identity gives
  -- `∫_{ball x σ} ⟪ω, F⟫ = (2 σ)⁻¹ ∫_{sphere x σ} Q` for almost every `σ`. The interior bound
  -- `d ≤ ⟪ω, F⟫ + N₁` and the sphere bound `Q ≤ σ² ((1 + δ) d + K₂)` combine with
  -- `∫_{sphere x σ} d = E'(σ)` and `μH(sphere x σ) = 4 V₁ σ³` at almost every radius.
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  have hr0 : 0 < r := by linarith
  have hJ := AlmostComplexStructure.inner_apply_apply_of_orthonormalBasis h₀ h₂₃
  have hω := AlmostComplexStructure.hodgeStar_kahlerForm h₀ h₂₃ hkl he
  have hω₂ : ‖J.kahlerForm‖ ^ 2 = 2 := AlmostComplexStructure.norm_kahlerForm_sq_eq_two hJ
  set δ := C / √r
  set d : V → ℝ := fun y ↦ r / 4 * |1 - ‖φ y‖ ^ 2 - ‖β y‖ ^ 2|
  have hsx : Continuous fun y : V ↦ y - x := continuous_id.sub continuous_const
  have hdc : ContinuousOn d (ball x R) :=
    continuousOn_const.mul ((continuousOn_const.sub (hφc.norm.pow 2)).sub (hβc.norm.pow 2)).abs
  have hd0 (y : V) : 0 ≤ d y := by positivity
  have hg : ContinuousOn (fun y ↦ ⟪J.kahlerForm, F y⟫) (ball x R) :=
    continuousOn_const.inner hF.continuousOn
  set g : V → ℝ := fun y ↦ ⟪J.kahlerForm, F y⟫
  set Qf : V → ℝ := fun y ↦ ‖y - x‖ ^ 2 * g y - J.hermitianForm (F y) (y - x) (y - x)
  have hQc : ContinuousOn Qf (ball x R) :=
    ((hsx.norm.pow 2).continuousOn.mul hg).sub
      (hF.continuousOn.hermitianForm_apply hsx.continuousOn hsx.continuousOn)
  -- On `ball x R` the density is bounded, so its cutoff `dR` outside the ball is integrable.
  set dR := (ball x R).indicator d
  have hdR : Integrable dR := by
    have : IsFiniteMeasure ((volume : Measure V).restrict (ball x R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    refine (integrable_indicator_iff measurableSet_ball).2
      ⟨hdc.aestronglyMeasurable measurableSet_ball, HasFiniteIntegral.of_bounded
        (C := r / 4 * (1 + C / r)) ((ae_restrict_iff' measurableSet_ball).2
          (Eventually.of_forall fun y hy ↦ ?_))⟩
    have hCr : 0 ≤ C / r := by positivity
    have h1 := hφβ y hy
    have h2 := sq_nonneg ‖φ y‖
    have h3 := sq_nonneg ‖β y‖
    rw [Real.norm_of_nonneg (hd0 y)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) (by positivity)
  -- The defect energy of a ball inside `ball x R` is the integral of `dR` over the open ball.
  have hE (s : ℝ) (hs : s ≤ R) : ((volume : Measure V).withDensity
      (fun y ↦ ENNReal.ofReal (d y)) (closedBall x s)).toReal = ∫ y in ball x s, dR y := by
    have hdR0 (y : V) : 0 ≤ dR y := indicator_nonneg (fun y _ ↦ hd0 y) y
    rw [withDensity_apply _ measurableSet_closedBall,
      setLIntegral_congr ((volume : Measure V).addHaar_closedBall_ae_eq_ball x s),
      setLIntegral_congr_fun (g := fun y ↦ ENNReal.ofReal (dR y)) measurableSet_ball fun y hy ↦
        congrArg ENNReal.ofReal (indicator_of_mem (ball_subset_ball hs hy) d).symm,
      ← ofReal_integral_eq_lintegral_ofReal hdR.integrableOn (Eventually.of_forall hdR0),
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_ball fun y _ ↦ hdR0 y)]
  -- The two pointwise bounds on the ball.
  have hint (y : V) (hy : y ∈ ball x R) : d y ≤ g y + N₁ := by
    have h := mul_abs_one_sub_sub_le_inner_add hQ hkl hω hω₂ (hφ y hy) (hβ y hy) hr0 hC
      (hFeq y hy) (hφβ y hy)
    have hηN := mul_le_mul_of_nonneg_left (hη y hy) (Real.sqrt_nonneg 2)
    simp only [d, g, N₁]
    linarith
  have hbd (y : V) (hy : y ∈ ball x R) : Qf y ≤ ‖y - x‖ ^ 2 * ((1 + δ) * d y + K₂) := by
    refine (mul_inner_kahlerForm_sub_hermitianForm_le h₀ h₂₃ hQ hkl he (hφ y hy) (hβ y hy) hr hC
      (hFeq y hy) (hFm y hy) (hβK y hy) (y - x)).trans
      (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have hηN := mul_le_mul_of_nonneg_left (hη y hy) (Real.sqrt_nonneg 2)
    simp only [d, K₂, δ]
    linarith
  filter_upwards [AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq h₀ h₂₃ hkl he
      hF hdF, ae_hasDerivAt_setIntegral_ball x hdR.locallyIntegrable] with σ h1 h2 hσ
  obtain ⟨hσ0, hσR⟩ := hσ
  have hsph : sphere x σ ⊆ ball x R := fun y hy ↦ by rw [mem_ball, mem_sphere.1 hy]; exact hσR
  have hsub : ball x σ ⊆ ball x R := ball_subset_ball hσR.le
  have hμS : μHE[finrank ℝ V - 1] (sphere x σ) ≠ ⊤ := by
    rw [euclideanHausdorffMeasure_sphere x hσ0]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) measure_ball_lt_top.ne) (by simp)
  have hsphI {f : V → ℝ} (hf : ContinuousOn f (ball x R)) :
      IntegrableOn f (sphere x σ) μHE[finrank ℝ V - 1] :=
    (hf.mono hsph).integrableOn_of_subset_isCompact (isCompact_sphere x σ)
      isClosed_sphere.measurableSet subset_rfl hμS
  have hballI {f : V → ℝ} (hf : ContinuousOn f (ball x R)) : IntegrableOn f (ball x σ) :=
    ((hf.mono (closedBall_subset_ball hσR)).integrableOn_compact
      (isCompact_closedBall x σ)).mono_set ball_subset_closedBall
  have h1' : ∫ y in ball x σ, g y =
      (2 * σ)⁻¹ * ∫ y in sphere x σ, Qf y ∂μHE[finrank ℝ V - 1] := h1 ⟨hσ0, hσR⟩
  have hEσ : ((volume : Measure V).withDensity (fun y ↦ ENNReal.ofReal (d y))
      (closedBall x σ)).toReal = ∫ y in ball x σ, d y :=
    (hE σ hσR.le).trans
      (setIntegral_congr_fun measurableSet_ball fun y hy ↦ indicator_of_mem (hsub hy) d)
  have hderiv : deriv (fun s ↦ ((volume : Measure V).withDensity
      (fun y ↦ ENNReal.ofReal (d y)) (closedBall x s)).toReal) σ =
      ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] := by
    rw [(h2.congr_of_eventuallyEq ((eventually_lt_nhds hσR).mono fun s hs ↦ hE s hs.le)).deriv]
    exact setIntegral_congr_fun isClosed_sphere.measurableSet fun y hy ↦
      indicator_of_mem (hsph hy) d
  rw [hEσ, hderiv]
  have hS1 : ∫ _ in sphere x σ, (1 : ℝ) ∂μHE[finrank ℝ V - 1] = V₁ * (4 * σ ^ 3) := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      euclideanHausdorffMeasure_sphere x hσ0, (Fact.out : finrank ℝ V = 4)]
    simp only [V₁, measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hσ0.le, ENNReal.toReal_natCast]
    norm_num
    ring
  have hvol : ∫ _ in ball x σ, (1 : ℝ) = V₁ * σ ^ 4 := by
    rw [setIntegral_const, smul_eq_mul, mul_one,
      (volume : Measure V).addHaar_real_ball_of_pos x hσ0, (Fact.out : finrank ℝ V = 4)]
    ring
  -- The defect energy of the ball is at most the `ω`-component of the curvature, plus an error.
  have hball : ∫ y in ball x σ, d y ≤ (∫ y in ball x σ, g y) + N₁ * (V₁ * σ ^ 4) := by
    have hgi : IntegrableOn g (ball x σ) := hballI hg
    have h1i : IntegrableOn (fun _ ↦ (1 : ℝ)) (ball x σ) := hballI continuousOn_const
    calc ∫ y in ball x σ, d y ≤ ∫ y in ball x σ, (g y + N₁ * 1) :=
          setIntegral_mono_on (hballI hdc) (hgi.add (h1i.const_mul N₁)) measurableSet_ball
            fun y hy ↦ by simpa using hint y (hsub hy)
      _ = (∫ y in ball x σ, g y) + N₁ * (V₁ * σ ^ 4) := by
          rw [integral_add hgi (h1i.const_mul N₁), integral_const_mul, hvol]
  -- The flux through the sphere is controlled by the derivative of the defect energy.
  have hsphere : ∫ y in sphere x σ, Qf y ∂μHE[finrank ℝ V - 1] ≤
      σ ^ 2 * ((1 + δ) * ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] +
        K₂ * (V₁ * (4 * σ ^ 3))) := by
    have hds := hsphI hdc
    have h1s : IntegrableOn (fun _ ↦ (1 : ℝ)) (sphere x σ) μHE[finrank ℝ V - 1] :=
      hsphI continuousOn_const
    have hki : IntegrableOn (fun y ↦ σ ^ 2 * ((1 + δ) * d y + K₂ * 1)) (sphere x σ)
        μHE[finrank ℝ V - 1] :=
      ((hds.const_mul (1 + δ)).add (h1s.const_mul K₂)).const_mul (σ ^ 2)
    calc ∫ y in sphere x σ, Qf y ∂μHE[finrank ℝ V - 1]
        ≤ ∫ y in sphere x σ, σ ^ 2 * ((1 + δ) * d y + K₂ * 1) ∂μHE[finrank ℝ V - 1] :=
          setIntegral_mono_on (hsphI hQc) hki isClosed_sphere.measurableSet fun y hy ↦ by
            have h := hbd y (hsph hy)
            rw [mem_sphere, dist_eq_norm] at hy
            rw [hy] at h
            simpa using h
      _ = σ ^ 2 * ((1 + δ) * ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] +
            K₂ * (V₁ * (4 * σ ^ 3))) := by
          rw [integral_const_mul, integral_add (hds.const_mul (1 + δ)) (h1s.const_mul K₂),
            integral_const_mul (1 + δ), integral_const_mul K₂, hS1]
  rw [h1'] at hball
  have hmul := mul_le_mul_of_nonneg_left hsphere (by positivity : (0 : ℝ) ≤ (2 * σ)⁻¹)
  have e1 : (2 * σ)⁻¹ * (σ ^ 2 * ((1 + δ) * ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] +
      K₂ * (V₁ * (4 * σ ^ 3)))) = σ / 2 * (1 + δ) *
        ∫ y in sphere x σ, d y ∂μHE[finrank ℝ V - 1] + 2 * K₂ * V₁ * σ ^ 4 := by
    field_simp
    ring
  rw [e1] at hmul
  linarith

end Integrated

end TauCeti.SeibergWitten
