/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalConstancy
public import TauCeti.Analysis.Distribution.TestFunction.DualEquiv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.Integral
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv

/-!
# Constancy of distributions with vanishing derivatives

Let `Ω` be a connected nonempty open subset of a finite-dimensional real normed space `E` and let
`μ` be an additive Haar measure on `E`. A Banach-valued distribution on `Ω` all of whose
directional derivatives vanish is integration against a unique constant with respect to `μ`.
No order-zero or finite-mass assumption is made. Conversely, integration against a constant has
vanishing derivatives, so this characterizes the constant distributions. The corresponding
statement for finite-dimensional vector-valued tests identifies a functional annihilating all
derivatives of tests with integration against one fixed continuous linear map; with tests valued
in alternating forms, this is the coordinate form of the constancy theorem for currents. The
hypothesis quantifies over all directions; by linearity of `v ↦ ∂_v T` it amounts to the vanishing
of the coordinate derivatives along any basis. On the real line,
`TauCeti.Analysis.Distribution.Constancy.Line` states the result for the derivative `∂_1`; its
local statement has an elementary proof by primitives.

The proof is by regularization. On a ball `B(x, r)` with `B(x, 2r) ⊆ Ω`, let `ρ` be a normalized
bump of radius at most `r`. Since the derivatives of `T` vanish, its regularization
`y ↦ T (ρ (· - y))` is constant on `B(x, r)`
(`Distribution.translatePairing_eq_of_lineDerivOp_eq_zero`), and pairing it with a test `φ`
supported in `B(x, r)` gives `T (ρ ⋆ φ)` (`Distribution.apply_eq_integral_smul_translatePairing`).
Hence `T (ρ ⋆ φ) = (∫ φ) • T (ρ ⋆ χ)` for a test `χ` of integral one. As the radius of `ρ` tends to
zero, the mollifications converge in the test-function topology (`TestFunction.tendsto_mollify`),
so `T φ = (∫ φ) • T χ`. These local constants glue on the connected domain
(`Distribution.existsUnique_eq_ofFun_const_of_locally`).

## Main declarations

* `Distribution.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero`: a distribution with
  vanishing derivatives on a connected nonempty open set is integration against a unique
  constant.
* `Distribution.lineDerivOp_ofFun_const`: integration against a constant has vanishing
  derivatives; `Distribution.forall_lineDerivOp_eq_zero_iff` is the resulting characterization.
* `Distribution.existsUnique_sub_eq_ofFun_const_of_forall_lineDerivOp_eq`: two distributions with
  the same derivatives differ by integration against a unique constant.
* `TestFunction.existsUnique_eq_integralAgainstBilinCLM_of_forall_lineDeriv_eq_zero`: the version
  for functionals on finite-dimensional vector-valued tests.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1 (distributions
  with vanishing derivatives) and §4.1 (regularization).
-/

public section

open Set MeasureTheory TopologicalSpace Metric Filter LineDeriv
open ContinuousLinearMap (lsmul)
open scoped Distributions Topology Convolution Pointwise

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E}

/-- On a ball whose double lies in `Ω`, a distribution with vanishing derivatives evaluates a test
by its integral and its value on any integral-one test supported in that ball. -/
private theorem apply_eq_integral_smul_of_forall_lineDerivOp_eq_zero (μ : Measure E)
    [μ.IsAddHaarMeasure] {T : 𝓓'(Ω, F)} (hT : ∀ v : E, ∂_{v} T = 0) {x : E} {r : ℝ}
    (hr : ball x (2 * r) ⊆ Ω) {χ : 𝓓(Ω, ℝ)} (hχ : tsupport χ ⊆ ball x r)
    (hχint : ∫ y, χ y ∂μ = 1) {φ : 𝓓(Ω, ℝ)} (hφ : tsupport φ ⊆ ball x r) :
    T φ = (∫ y, φ y ∂μ) • T χ := by
  -- Translating `closedBall 0 s`, for `s ≤ r`, by a point of `ball x r` stays inside `Ω`.
  have hadd {s : ℝ} (hs : s ≤ r) {z y : E} (hz : z ∈ closedBall (0 : E) s)
      (hy : y ∈ ball x r) : z + y ∈ Ω := by
    refine hr (mem_ball.2 ?_)
    calc dist (z + y) x ≤ ‖z‖ + dist y x := by
          rw [dist_eq_norm, dist_eq_norm, add_sub_assoc]
          exact norm_add_le _ _
      _ < s + r := add_lt_add_of_le_of_lt (mem_closedBall_zero_iff.1 hz) (mem_ball.1 hy)
      _ ≤ 2 * r := by linarith
  -- For a bump `ρ` of radius at most `r`, pairing `T` with a mollification of `ψ` gives the
  -- integral of `ψ` times the constant value of the regularization on `ball x r`.
  let bump (ρ : ContDiffBump (0 : E)) : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨ρ.normed μ, ρ.contDiff_normed, ρ.hasCompactSupport_normed, by simp⟩
  have hmoll (ρ : ContDiffBump (0 : E)) (hρ : ρ.rOut ≤ r) {ψ : 𝓓(Ω, ℝ)}
      (hψ : tsupport ψ ⊆ ball x r) (h : closedBall (0 : E) ρ.rOut + tsupport ψ ⊆ (Ω : Set E)) :
      T (TestFunction.mollify ψ μ ρ h) = (∫ y, ψ y ∂μ) • T.translatePairing (bump ρ) x := by
    set ρ' := bump ρ
    have hρ' : (ρ' : E → ℝ) = ρ.normed μ := rfl
    have htsupp : tsupport ρ' = closedBall 0 ρ.rOut := by
      rw [hρ']
      exact ρ.tsupport_normed_eq
    have hU (y : E) (hy : y ∈ ball x r) : MapsTo (· + y) (tsupport ρ') Ω := fun z hz =>
      hadd hρ (htsupp ▸ hz) hy
    have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
      ext
      simp
    rw [T.apply_eq_integral_smul_translatePairing ρ'
      (ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport) ψ.hasCompactSupport
      (fun y hy => hU y (hψ hy)) (by rw [TestFunction.coe_mollify, hρ', ← convolution_flip, hflip]),
      ← integral_smul_const]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    by_cases hy : y ∈ ball x r
    · rw [T.translatePairing_eq_of_lineDerivOp_eq_zero hT ρ' isOpen_ball
        (convex_ball x r).isPreconnected hU hy (mem_ball_self (pos_of_mem_ball hy))]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hy (hψ h)]
  -- Let the bumps shrink: the mollifications converge in the test-function topology.
  have hr0 : 0 < r := by
    rcases (tsupport χ).eq_empty_or_nonempty with h | ⟨y, hy⟩
    · have hχ0 : (χ : E → ℝ) = 0 := funext fun y =>
        image_eq_zero_of_notMem_tsupport (h ▸ notMem_empty y)
      simp [hχ0] at hχint
    · exact pos_of_mem_ball (hχ hy)
  let ρ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨r / (n + 2) / 2, r / (n + 2), by positivity, half_lt_self (by positivity)⟩
  have hle (n : ℕ) : (ρ n).rOut ≤ r :=
    div_le_self hr0.le (by linarith [n.cast_nonneg (α := ℝ)])
  have hlim : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hsub {ψ : 𝓓(Ω, ℝ)} (hψ : tsupport ψ ⊆ ball x r) (n : ℕ) :
      closedBall (0 : E) (ρ n).rOut + tsupport ψ ⊆ (Ω : Set E) := by
    rintro _ ⟨z, hz, y, hy, rfl⟩
    exact hadd (hle n) hz (hψ hy)
  have hTφ : Tendsto (fun n => (∫ y, φ y ∂μ) • T.translatePairing (bump (ρ n)) x) atTop
      (𝓝 (T φ)) :=
    (((T : 𝓓(Ω, ℝ) →L[ℝ] F).continuous.tendsto φ).comp
      (TestFunction.tendsto_mollify φ μ hlim (hsub hφ))).congr fun n =>
        hmoll (ρ n) (hle n) hφ (hsub hφ n)
  have hTχ : Tendsto (fun n => T.translatePairing (bump (ρ n)) x) atTop (𝓝 (T χ)) :=
    (((T : 𝓓(Ω, ℝ) →L[ℝ] F).continuous.tendsto χ).comp
      (TestFunction.tendsto_mollify χ μ hlim (hsub hχ))).congr fun n =>
        (hmoll (ρ n) (hle n) hχ (hsub hχ n)).trans (by rw [hχint, one_smul])
  exact tendsto_nhds_unique hTφ (hTχ.const_smul _)

/-- **Constancy of distributions.** A Banach-valued distribution on a connected nonempty open
subset of a finite-dimensional real normed space whose directional derivatives all vanish is
integration against a unique constant, for any additive Haar measure `μ`. -/
theorem existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero (T : 𝓓'(Ω, F))
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsConnected (Ω : Set E))
    (hT : ∀ v : E, ∂_{v} T = 0) :
    ∃! c : F, T = ofFun Ω (fun _ ↦ c) μ ⊤ := by
  apply T.existsUnique_eq_ofFun_const_of_locally hΩ
  intro x hx
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  have hball : ball x (2 * (r / 2)) ⊆ Ω := by rwa [mul_div_cancel₀ _ two_ne_zero]
  obtain ⟨χ, hχ, -, hχint⟩ := TestFunction.exists_nonneg_integral_eq_one (μ := μ) (n := ⊤)
    isOpen_ball (nonempty_ball.2 (half_pos hr)) ((ball_subset_ball (half_le_self hr.le)).trans hrΩ)
  exact ⟨ball x (r / 2), isOpen_ball, mem_ball_self (half_pos hr), T χ, fun φ hφ =>
    apply_eq_integral_smul_of_forall_lineDerivOp_eq_zero μ hT hball hχ hχint hφ⟩

/-- Integration against a constant has vanishing directional derivatives. -/
@[simp]
theorem lineDerivOp_ofFun_const (μ : Measure E) [μ.IsAddHaarMeasure] (c : F) (v : E) :
    ∂_{v} (ofFun Ω (fun _ ↦ c) μ ⊤) = 0 := by
  ext φ
  have hd : ∫ x, lineDeriv ℝ φ x v ∂μ = 0 := TestFunction.integral_lineDeriv_eq_zero φ v
  simp [lineDerivOp_apply_apply, ofFun_apply (locallyIntegrableOn_const c), integral_smul_const,
    integral_neg, hd]

/-- On a connected nonempty open domain, vanishing of all directional derivatives characterizes
the distributions given by integration against a constant, which is then unique. -/
theorem forall_lineDerivOp_eq_zero_iff (T : 𝓓'(Ω, F)) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hΩ : IsConnected (Ω : Set E)) :
    (∀ v : E, ∂_{v} T = 0) ↔ ∃! c : F, T = ofFun Ω (fun _ ↦ c) μ ⊤ := by
  refine ⟨T.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero μ hΩ, ?_⟩
  rintro ⟨c, rfl, -⟩ v
  exact lineDerivOp_ofFun_const μ c v

/-- Two distributions with the same directional derivatives on a connected nonempty open domain
differ by integration against a unique constant. -/
theorem existsUnique_sub_eq_ofFun_const_of_forall_lineDerivOp_eq (T S : 𝓓'(Ω, F))
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsConnected (Ω : Set E))
    (hTS : ∀ v : E, ∂_{v} T = ∂_{v} S) :
    ∃! c : F, T - S = ofFun Ω (fun _ ↦ c) μ ⊤ := by
  refine (T - S).existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero μ hΩ fun v ↦ ?_
  simpa only [lineDerivOp_eq_lineDerivCLM, map_sub, sub_eq_zero] using hTS v

end Distribution

namespace TestFunction

open ContinuousLinearMap
open scoped CompactConvergenceCLM

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {Ω : Opens E}

/-- A functional on finite-dimensional vector-valued tests on a connected nonempty open domain
that annihilates all their directional derivatives is integration against a unique fixed linear
map, for any additive Haar measure `μ`. -/
theorem existsUnique_eq_integralAgainstBilinCLM_of_forall_lineDeriv_eq_zero
    (T : 𝓓(Ω, F) →L_c[ℝ] V) (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsConnected (Ω : Set E))
    (hT : ∀ (v : E) (φ : 𝓓(Ω, F)), T (∂_{v} φ) = 0) :
    ∃! A : F →L[ℝ] V, T = toUniformConvergenceCLM _ V _
      (integralAgainstBilinCLM (apply ℝ V) μ (fun _ ↦ A) : 𝓓(Ω, F) →L[ℝ] V) := by
  obtain ⟨A, hA, hu⟩ := (dualEquivDistribution T
    ).existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero μ hΩ fun v =>
      lineDeriv_dualEquivDistribution_eq_zero (hT v)
  refine ⟨A, ?_, fun B hB ↦ hu B ?_⟩
  · apply dualEquivDistribution.injective
    exact hA.trans (dualEquivDistribution_integralAgainstBilinCLM _ _).symm
  · rw [hB, dualEquivDistribution_integralAgainstBilinCLM]

end TestFunction
