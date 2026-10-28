/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.LocalConstancy
public import TauCeti.Analysis.Distribution.TestFunction.DualEquiv
import TauCeti.Analysis.Distribution.Regularization
import TauCeti.Analysis.Distribution.TestFunction.Convolution
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Topology.Algebra.Monoid

/-!
# Distributions with vanishing derivatives

Let `Ω` be a connected nonempty open subset of a finite-dimensional real normed space `E` and `μ`
an additive Haar measure on `E`. A Banach-valued distribution on `Ω` has vanishing directional
derivatives exactly when it is integration against `μ` of a unique constant. No order-zero or
finite-mass assumption is made.

The local statement holds on every convex open `U ⊆ Ω`. For a small normalized bump `ρ`, the
regularization `y ↦ T (ρ (· - y))` has zero derivative, so it is constant on the convex open set of
translations `y` keeping `ρ (· - y)` supported in `U`. Pairing `T` with a mollified test function,
`Distribution.apply_eq_integral_smul_translatePairing`, then evaluates `T (ρ ⋆ φ)` as `∫ φ dμ`
times this constant. As the bumps shrink, mollification converges in the test-function topology,
which identifies the constant with `T η` for any integral-one test `η` supported in `U`. The local
formulas glue on the connected domain by `Distribution.existsUnique_eq_ofFun_const_of_locally`.

The corresponding theorem for finite-dimensional vector-valued tests identifies a functional
annihilating every derivative `∂_v φ` with integration against one fixed continuous linear map.
With `F` the top-degree alternating forms, this is the coordinate input to the constancy theorem
for currents with zero boundary.

## Main statements

* `Distribution.apply_eq_integral_smul_of_forall_lineDerivOp_eq_zero`: on a convex open subset,
  a distribution with vanishing derivatives evaluates a test by its integral.
* `Distribution.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero`: on a connected
  nonempty open set, such a distribution is integration against a unique constant.
* `Distribution.forall_lineDerivOp_eq_zero_iff`: the characterization of constant distributions.
* `TestFunction.existsUnique_eq_integralAgainstBilinCLM_of_forall_lineDeriv_eq_zero`: the version
  for functionals on finite-dimensional vector-valued tests.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §3.1
  (distributions with vanishing first derivatives) and §4.1 (regularization).
-/

public section

open Set Filter MeasureTheory TopologicalSpace LineDeriv Metric
open scoped Distributions Topology Convolution Pointwise

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {Ω : Opens E}

/-- On a convex open subset `U` of the domain, a distribution with vanishing derivatives
evaluates a test supported in `U` by its integral and its value on any integral-one test supported
in `U`. -/
theorem apply_eq_integral_smul_of_forall_lineDerivOp_eq_zero {μ : Measure E} [μ.IsAddHaarMeasure]
    {T : 𝓓'(Ω, F)} (hT : ∀ v : E, ∂_{v} T = 0) {U : Set E} (hUo : IsOpen U)
    (hUc : Convex ℝ U) (hUΩ : U ⊆ Ω) (η : 𝓓(Ω, ℝ)) (hη : tsupport η ⊆ U)
    (hηint : ∫ x, η x ∂μ = 1) (φ : 𝓓(Ω, ℝ)) (hφ : tsupport φ ⊆ U) :
    T φ = (∫ x, φ x ∂μ) • T η := by
  set K := tsupport φ ∪ tsupport η
  have hK : IsCompact K := φ.hasCompactSupport.isCompact.union η.hasCompactSupport.isCompact
  obtain ⟨s, hs, hsU⟩ := hK.exists_cthickening_subset_open hUo (union_subset hφ hη)
  -- The translations moving `closedBall 0 s` into `U` form a convex open neighbourhood of `K`.
  set W := {y | MapsTo (· + y) (closedBall (0 : E) s) U}
  have hWo : IsOpen W := (isCompact_closedBall _ _).isOpen_setOf_mapsTo_add hUo
  have hWc : IsPreconnected W := by
    refine Convex.isPreconnected fun y₁ hy₁ y₂ hy₂ a b ha hb hab z hz ↦ ?_
    have h := hUc (hy₁ hz) (hy₂ hz) ha hb hab
    rwa [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul] at h
  have hKW : K ⊆ W := fun y hy z hz ↦ hsU <|
    mem_cthickening_of_dist_le _ y s K hy (by simpa [dist_eq_norm] using hz)
  obtain ⟨y₀, hy₀⟩ : (tsupport η).Nonempty := by
    by_contra h
    have hη0 : (η : E → ℝ) = 0 := tsupport_eq_empty_iff.1 (not_nonempty_iff_eq_empty.1 h)
    simp [hη0] at hηint
  -- Normalized bumps of outer radius `s / (k + 1)`, as test functions on the whole space.
  let ρ : ℕ → ContDiffBump (0 : E) := fun k ↦
    ⟨s / (k + 1) / 2, s / (k + 1), by positivity, half_lt_self (by positivity)⟩
  have hρs (k : ℕ) : (ρ k).rOut ≤ s := div_le_self hs.le (by simp)
  have hρlim : Tendsto (fun k ↦ (ρ k).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  let ρ' (k : ℕ) : 𝓓((⊤ : Opens E), ℝ) :=
    ⟨(ρ k).normed μ, (ρ k).contDiff_normed, (ρ k).hasCompactSupport_normed, by simp⟩
  have htρ (k : ℕ) : tsupport (ρ' k) = closedBall 0 (ρ k).rOut := by
    simp [ρ', (ρ k).tsupport_normed_eq]
  have hadm (k : ℕ) (y : E) (hy : y ∈ W) : MapsTo (· + y) (tsupport (ρ' k)) Ω := fun z hz ↦
    hUΩ (hy (closedBall_subset_closedBall (hρs k) (htρ k ▸ hz)))
  have hmol (k : ℕ) (χ : 𝓓(Ω, ℝ)) (hχ : tsupport χ ⊆ K) :
      closedBall (0 : E) (ρ k).rOut + tsupport χ ⊆ Ω := by
    rintro _ ⟨z, hz, y, hy, rfl⟩
    exact hUΩ (hKW (hχ hy) (closedBall_subset_closedBall (hρs k) hz))
  -- Pairing `T` with a mollified test function gives its integral times a constant.
  have key (k : ℕ) (χ : 𝓓(Ω, ℝ)) (hχ : tsupport χ ⊆ K) :
      T (TestFunction.mollify χ μ (ρ k) (hmol k χ hχ)) =
        (∫ x, χ x ∂μ) • T.translatePairing (ρ' k) y₀ := by
    rw [apply_eq_integral_smul_translatePairing T (ρ' k) χ.continuous χ.hasCompactSupport
      (fun y hy ↦ hadm k y (hKW (hχ hy))) (μ := μ) fun x ↦ ?_, ← integral_smul_const]
    · refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      by_cases hy : y ∈ tsupport χ
      · exact congrArg (χ y • ·) (translatePairing_eq_of_lineDerivOp_eq_zero hT (ρ' k) hWo hWc
          (hadm k) (hKW (hχ hy)) (hKW (subset_union_right hy₀)))
      · simp [image_eq_zero_of_notMem_tsupport hy]
    · rw [TestFunction.mollify_apply, convolution_lsmul_swap]
      simp [ρ', mul_comm]
  have hlim (χ : 𝓓(Ω, ℝ)) (hχ : tsupport χ ⊆ K) :
      Tendsto (fun k ↦ T (TestFunction.mollify χ μ (ρ k) (hmol k χ hχ))) atTop (𝓝 (T χ)) :=
    (T.continuous.tendsto χ).comp (TestFunction.tendsto_mollify χ μ hρlim _)
  have hc : Tendsto (fun k ↦ T.translatePairing (ρ' k) y₀) atTop (𝓝 (T η)) := by
    simpa only [key _ η subset_union_right, hηint, one_smul] using hlim η subset_union_right
  refine tendsto_nhds_unique (hlim φ subset_union_left) ?_
  simpa only [key _ φ subset_union_left] using hc.const_smul (∫ x, φ x ∂μ)

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Constancy of distributions.** A distribution with vanishing directional derivatives on a
connected nonempty open subset of a finite-dimensional real normed space is integration against a
Haar measure of a unique constant. -/
theorem existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero (T : 𝓓'(Ω, F))
    (hΩ : IsConnected (Ω : Set E)) (hT : ∀ v : E, ∂_{v} T = 0) :
    ∃! c : F, T = ofFun Ω (fun _ ↦ c) μ ⊤ := by
  apply T.existsUnique_eq_ofFun_const_of_locally hΩ
  intro x hx
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hx
  obtain ⟨η, hη, -, hηint⟩ := TestFunction.exists_nonneg_integral_eq_one
    (μ := μ) (n := ⊤) isOpen_ball ⟨x, mem_ball_self hr⟩ hrΩ
  exact ⟨ball x r, isOpen_ball, mem_ball_self hr, T η, fun φ hφ ↦
    apply_eq_integral_smul_of_forall_lineDerivOp_eq_zero hT isOpen_ball (convex_ball x r) hrΩ
      η hη hηint φ hφ⟩

/-- Integration against a constant has vanishing directional derivatives. -/
@[simp]
theorem lineDerivOp_ofFun_const (c : F) (v : E) :
    ∂_{v} (ofFun Ω (fun _ ↦ c) μ ⊤) = 0 := by
  ext φ
  have hd : ∫ x, (∂_{v} φ) x ∂μ = 0 := by
    simpa only [TestFunction.lineDerivOp_apply] using TestFunction.integral_lineDeriv_eq_zero
      (μ := μ) φ v
  simp only [lineDerivOp_apply_apply, ofFun_apply (locallyIntegrableOn_const c),
    integral_smul_const, FunLike.coe_neg, Pi.neg_apply, integral_neg, zero_apply]
  exact smul_eq_zero_of_left (neg_eq_zero.2 hd) c

/-- On a connected nonempty open domain, vanishing of all directional derivatives characterizes
the distributions which are integration against a constant. -/
theorem forall_lineDerivOp_eq_zero_iff (T : 𝓓'(Ω, F)) (hΩ : IsConnected (Ω : Set E)) :
    (∀ v : E, ∂_{v} T = 0) ↔ ∃! c : F, T = ofFun Ω (fun _ ↦ c) μ ⊤ := by
  refine ⟨T.existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero μ hΩ, ?_⟩
  rintro ⟨c, rfl, -⟩ v
  exact lineDerivOp_ofFun_const μ c v

/-- Two distributions with the same directional derivatives on a connected nonempty open domain
differ by integration against a unique constant. -/
theorem existsUnique_sub_eq_ofFun_const_of_forall_lineDerivOp_eq (T S : 𝓓'(Ω, F))
    (hΩ : IsConnected (Ω : Set E)) (hTS : ∀ v : E, ∂_{v} T = ∂_{v} S) :
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
  {Ω : Opens E} (μ : Measure E) [μ.IsAddHaarMeasure]

/-- A functional on finite-dimensional vector-valued tests on a connected nonempty open domain
that annihilates all their directional derivatives is integration against a unique fixed linear
map. -/
theorem existsUnique_eq_integralAgainstBilinCLM_of_forall_lineDeriv_eq_zero
    (T : 𝓓(Ω, F) →L_c[ℝ] V) (hΩ : IsConnected (Ω : Set E))
    (hT : ∀ (v : E) (φ : 𝓓(Ω, F)), T (∂_{v} φ) = 0) :
    ∃! A : F →L[ℝ] V, T = toUniformConvergenceCLM _ V _
      (integralAgainstBilinCLM (apply ℝ V) μ (fun _ ↦ A) : 𝓓(Ω, F) →L[ℝ] V) := by
  obtain ⟨A, hA, hu⟩ := (dualEquivDistribution T
    ).existsUnique_eq_ofFun_const_of_forall_lineDerivOp_eq_zero μ hΩ
      fun v ↦ lineDeriv_dualEquivDistribution_eq_zero (hT v)
  refine ⟨A, ?_, fun B hB ↦ hu B ?_⟩
  · apply dualEquivDistribution.injective
    exact hA.trans (dualEquivDistribution_integralAgainstBilinCLM _ _).symm
  · rw [hB, dualEquivDistribution_integralAgainstBilinCLM]

end TestFunction
