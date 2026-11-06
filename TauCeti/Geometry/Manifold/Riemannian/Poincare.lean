/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ChartCutoff
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support
import TauCeti.MeasureTheory.Function.Lp.LIntegralRpow
import TauCeti.MeasureTheory.Function.LpSeminorm.Oscillation
import TauCeti.MeasureTheory.Integral.Average

/-!
# The Poincaré–Wirtinger inequality on a closed Riemannian manifold

Let `M` be a compact connected manifold without boundary with a continuous Riemannian metric and
its Riemannian volume `dV`. For `1 ≤ p < ∞`, the **Poincaré–Wirtinger inequality** says that there
is a constant `C` with

`‖u - ⨍ u‖_{Lᵖ} ≤ C ‖∇u‖_{Lᵖ}`

for every `C¹` function `u`, where `⨍ u` is the mean of `u` with respect to `dV`
(`TauCeti.Manifold.exists_eLpNorm_sub_average_le_mul_eLpNorm_mgradient`). It is the coercivity
estimate of variational problems on `M` normalized by the mean: on functions of mean zero the
Dirichlet energy `∫ |∇u|² dV` controls the full `H¹` norm. This is the estimate needed to invert the
Laplacian on functions of mean zero, and to minimize functionals such as
`∫ (|∇u|² / 2 + K u + e^(2u) / 2) dV`, whose critical points solve the Gaussian curvature equation
`Δ⁺u + K + e^(2u) = 0` on a closed surface.

The proof first localizes the Poincaré–Wirtinger inequality on a ball of the model space,
`TauCeti.lintegral_enorm_sub_setAverage_rpow_le_of_convex`. Near each point `c`, in a coordinate
ball around the chart image of `c`, the chart density is comparable to its value at `c` and the
coordinate derivative of every function is bounded by a fixed multiple of the length of its
gradient, so on the chart preimage of the ball `u` is within a fixed multiple of `‖∇u‖_{Lᵖ(M)}`
of a constant in `Lᵖ`
(`TauCeti.Manifold.exists_isOpen_eLpNorm_restrict_sub_le_mul_eLpNorm_mgradient`). Finitely many
such neighbourhoods cover `M`, and since `M` is connected the local constants chain together to a
single one (`TauCeti.exists_eLpNorm_sub_const_le_of_isOpen_cover`). Replacing that constant by the
mean costs at most a factor `2` (`TauCeti.eLpNorm_sub_setAverage_le`).

Connectedness cannot be dropped: on a disjoint union of two closed manifolds a function equal to
different constants on the two components has vanishing gradient but is not equal to its mean.

## Main results

* `TauCeti.Manifold.exists_isOpen_eLpNorm_restrict_sub_le_mul_eLpNorm_mgradient`: the local
  local estimate, near any point of a manifold without boundary, of the `Lᵖ` oscillation of `u`
  on a neighbourhood `V` by the `Lᵖ` norm of `∇u` over all of `M`.
* `TauCeti.Manifold.exists_eLpNorm_sub_average_le_mul_eLpNorm_mgradient`: the Poincaré–Wirtinger
  inequality on a closed connected Riemannian manifold.

## References

* T. Aubin, *Some Nonlinear Problems in Riemannian Geometry*, Springer (1998), Chapter 2.
* E. Hebey, *Nonlinear Analysis on Manifolds: Sobolev Spaces and Inequalities*, Courant Lecture
  Notes 5 (1999), Chapter 3.
* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer (2001), Lemma 7.16 and §7.8.
-/

public section

open Bundle MeasureTheory Metric Module Set
open scoped ENNReal NNReal Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable [MeasurableSpace M] [BorelSpace M]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- **A local oscillation bound near a point.** Let `1 ≤ p < ∞`, on a manifold without boundary with
a continuous Riemannian metric. Every point `c` lies in an open set `V` with a constant `C` such
that every `C¹` function `u` satisfies `‖u - a‖_{Lᵖ(V)} ≤ C ‖∇u‖_{Lᵖ(M)}` for some constant `a`.
The gradient norm on the right is taken over all of `M`, not only over `V`. -/
theorem exists_isOpen_eLpNorm_restrict_sub_le_mul_eLpNorm_mgradient [LindelofSpace M]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) (c : M) :
    ∃ V, IsOpen V ∧ c ∈ V ∧ ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      ∃ a : ℝ, eLpNorm (fun x ↦ u x - a) p ((riemannianVolume I M).restrict V) ≤
        C * eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M) := by
  -- A coordinate ball `B` around the chart image of `c`, adapted to the metric.
  obtain ⟨C₁, hC₁, r, hr, hrt, hball⟩ :=
    exists_ball_norm_fderiv_le_and_chartVolumeDensity_mem_Ioo (I := I) (M := M) c
  set φ := extChartAt I c
  set μ := (Module.finBasis ℝ E).addHaar
  set ρ := chartVolumeDensity (I := I) c
  set dV := riemannianVolume I M
  set B := ball (φ c) r
  set q := p.toReal
  have hρc : 0 < ρ c := chartVolumeDensity_pos c (FiberBundle.mem_baseSet_trivializationAt' c)
  have hq : 1 ≤ q := by simpa using ENNReal.toReal_mono hp' hp
  have hq0 : 0 < q := one_pos.trans_le hq
  -- `K` is the constant of the flat Poincaré–Wirtinger inequality on `B`.
  set K := μ.real (ball 0 1) * diam B ^ (finrank ℝ E + 1) / μ.real B
  have hK : 0 ≤ K := by positivity
  refine ⟨φ.source ∩ φ ⁻¹' B, isOpen_extChartAt_preimage' c isOpen_ball,
    ⟨mem_extChartAt_source c, mem_ball_self hr⟩, NNReal.mk (4 * K * C₁) (by positivity), fun u hu ↦
      ⟨⨍ y in B, u (φ.symm y) ∂μ, ?_⟩⟩
  set a := ⨍ y in B, u (φ.symm y) ∂μ
  have hv : ContDiffOn ℝ 1 (fun y ↦ u (φ.symm y)) B :=
    (hu.comp_contMDiffOn (contMDiffOn_extChartAt_symm c)).contDiffOn.mono hrt
  rw [← ENNReal.ofReal_eq_coe_nnreal]
  refine eLpNorm_le_eLpNorm_of_lintegral_rpow_le (by positivity) (zero_lt_one.trans_le hp).ne' hp'
    (hu.continuous.sub continuous_const).aestronglyMeasurable ?_
  simp only [enorm_norm]
  -- The density and the derivative comparisons on `B` contribute the factor
  -- `2 ρ(c) · C₁ ^ q · (ρ(c) / 2)⁻¹ = 4 C₁ ^ q`.
  have hscal : ENNReal.ofReal (2 * ρ c) * (ENNReal.ofReal (K ^ q) *
      (ENNReal.ofReal C₁ ^ q * ENNReal.ofReal (ρ c / 2)⁻¹)) ≤
        ENNReal.ofReal ((4 * K * C₁) ^ q) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hC₁.le hq0.le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : (4 : ℝ) ≤ 4 ^ q := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hq
    calc 2 * ρ c * (K ^ q * (C₁ ^ q * (ρ c / 2)⁻¹)) = 4 * (K ^ q * C₁ ^ q) := by
          field_simp
          ring
      _ ≤ 4 ^ q * (K ^ q * C₁ ^ q) := by gcongr
      _ = (4 * K * C₁) ^ q := by
          rw [Real.mul_rpow (by positivity) hC₁.le, Real.mul_rpow (by norm_num) hK, mul_assoc]
  calc ∫⁻ x in φ.source ∩ φ ⁻¹' B, ‖u x - a‖ₑ ^ q ∂dV
      = ∫⁻ y in B, ENNReal.ofReal (ρ (φ.symm y)) * ‖u (φ.symm y) - a‖ₑ ^ q ∂μ :=
        setLIntegral_riemannianVolume_inter_preimage c isOpen_ball hrt _
    _ ≤ ∫⁻ y in B, ENNReal.ofReal (2 * ρ c) * ‖u (φ.symm y) - a‖ₑ ^ q ∂μ :=
        setLIntegral_mono' measurableSet_ball fun y hy ↦ by
          gcongr
          exact (hball y hy).2.2.le
    _ = ENNReal.ofReal (2 * ρ c) * ∫⁻ y in B, ‖u (φ.symm y) - a‖ₑ ^ q ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 * ρ c) *
          (ENNReal.ofReal (K ^ q) * ∫⁻ y in B, ‖fderiv ℝ (fun y ↦ u (φ.symm y)) y‖ₑ ^ q ∂μ) := by
        gcongr
        exact lintegral_enorm_sub_setAverage_rpow_le_of_convex isOpen_ball (convex_ball _ _)
          isBounded_ball hv subset_rfl (measure_ball_pos μ _ hr).ne' hq
    _ ≤ ENNReal.ofReal (2 * ρ c) * (ENNReal.ofReal (K ^ q) *
          ∫⁻ y in B, ENNReal.ofReal C₁ ^ q * ‖mgradient I u (φ.symm y)‖ₑ ^ q ∂μ) := by
        gcongr ENNReal.ofReal (2 * ρ c) * (ENNReal.ofReal (K ^ q) * ?_)
        refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ?_
        rw [← ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ofReal_norm, ← ofReal_norm,
          ← ENNReal.ofReal_mul hC₁.le]
        gcongr
        exact (hball y hy).1 u
    _ = ENNReal.ofReal (2 * ρ c) * (ENNReal.ofReal (K ^ q) *
          (ENNReal.ofReal C₁ ^ q * ∫⁻ y in B, ‖mgradient I u (φ.symm y)‖ₑ ^ q ∂μ)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
    _ ≤ ENNReal.ofReal (2 * ρ c) * (ENNReal.ofReal (K ^ q) * (ENNReal.ofReal C₁ ^ q *
          (ENNReal.ofReal (ρ c / 2)⁻¹ * ∫⁻ x, ‖mgradient I u x‖ₑ ^ q ∂dV))) := by
        gcongr
        exact setLIntegral_comp_extChartAt_symm_le_mul_lintegral c isOpen_ball hrt (by positivity)
          (fun y hy ↦ (hball y hy).2.1.le) fun x ↦ ‖mgradient I u x‖ₑ ^ q
    _ ≤ ENNReal.ofReal ((4 * K * C₁) ^ q) * ∫⁻ x, ‖mgradient I u x‖ₑ ^ q ∂dV := by
        simp only [← mul_assoc] at hscal ⊢
        gcongr

/-- **The Poincaré–Wirtinger inequality on a closed Riemannian manifold.** Let `1 ≤ p < ∞`, on a
compact connected manifold without boundary with a continuous Riemannian metric. There is a
constant `C` such that `‖u - ⨍ u‖_{Lᵖ} ≤ C ‖∇u‖_{Lᵖ}` for every `C¹` function `u`, where `⨍ u` is
the mean of `u` with respect to the Riemannian volume. -/
theorem exists_eLpNorm_sub_average_le_mul_eLpNorm_mgradient [CompactSpace M]
    [PreconnectedSpace M] {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u : M → ℝ, ContMDiff I 𝓘(ℝ) 1 u →
      eLpNorm (fun x ↦ u x - ⨍ y, u y ∂riemannianVolume I M) p (riemannianVolume I M) ≤
        C * eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M) := by
  choose V hV hcV C hC using
    exists_isOpen_eLpNorm_restrict_sub_le_mul_eLpNorm_mgradient (I := I) (M := M) hp hp'
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover V fun c _ ↦ (hV c).mem_nhds (hcV c)
  -- The local constants on the finitely many neighbourhoods chain together, as `M` is connected.
  obtain ⟨K, hK⟩ := exists_eLpNorm_sub_const_le_of_isOpen_cover (F := ℝ)
    (μ := riemannianVolume I M) hp t (fun c _ ↦ hV c) (fun x ↦ by simpa using ht (mem_univ x)) C
  refine ⟨2 * K, fun u hu ↦ ?_⟩
  choose a ha using fun c ↦ hC c u hu
  obtain ⟨b, hb⟩ := hK u a _ fun c _ ↦ ha c
  -- Replacing the constant by the mean costs a factor `2`.
  have hmean := eLpNorm_sub_setAverage_le (μ := riemannianVolume I M) (s := univ) (f := u)
    (measure_ne_top _ _) hp hp' b
  rw [Measure.restrict_univ] at hmean
  calc _ ≤ 2 * eLpNorm (fun x ↦ u x - b) p (riemannianVolume I M) := hmean
    _ ≤ 2 * (K * eLpNorm (fun x ↦ ‖mgradient I u x‖) p (riemannianVolume I M)) := by gcongr
    _ = _ := by push_cast; ring

end TauCeti.Manifold
