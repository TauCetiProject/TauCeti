/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Elliptic.Basic
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.Positivity
import TauCeti.Geometry.Manifold.Measure.Chart

/-!
# Positive pseudodifferential operators on a manifold have positive principal symbols

Let `M` be a manifold modelled on `ℝⁿ` with a positive continuous density measure `μ`
(`TauCeti.IsPositiveDensityMeasure`), for instance a Riemannian volume, and let `P` be a classical
pseudodifferential operator of order `m` on `M` (`TauCeti.classicalPseudodifferentialOperators`).
If `P` is positive on the compactly supported smooth functions supported in an open set `U`,

`0 ≤ ∫ ⟪P f (x), f (x)⟫ dμ(x)`

(a complex number that is real and nonnegative), then its principal symbol `σ_m(P)(x, ξ)` is real
and nonnegative at every point `x ∈ U` and every covector `ξ ∈ T*ₓM`
(`TauCeti.classicalPrincipalSymbol_nonneg`). Where `P` is moreover elliptic it is positive at every
nonzero covector (`TauCeti.IsClassicalEllipticAt.classicalPrincipalSymbol_pos`). So a positive
elliptic operator, such as a strictly positive self-adjoint elliptic operator on a compact manifold,
has a principal symbol that is positive off the zero section
(`TauCeti.IsClassicalElliptic.classicalPrincipalSymbol_pos`); this is what makes its real powers
`σ_m(P) ^ z` well defined.

The proof reads `P` in the preferred chart `e` at `x`, with both cutoffs equal to `1` on a closed
ball `K` around `e x` inside the image of `U`. For a Schwartz function `u` supported in the interior
of `K`, the function `f = u ∘ e` on `M` satisfies

`∫ ⟪P f, f⟫ dμ = ∫ w(y) ⟪Op(a) u (y), u (y)⟫ dy`,

where `a` is the chart symbol of `P` and `w` the continuous density of `μ` in the chart
(`TauCeti.integral_eq_setIntegral_smul_extChartAt_symm`). So `Op(a)` is positive near `e x` for the
pairing weighted by `w`, and testing on high-frequency wave packets shows that its principal symbol
is positive there (`TauCeti.ClassicalSymbol.isPositive_coefficient_principal_of_weight`). The
principal symbol of `a` at `e x` is `σ_m(P)` read at the corresponding covector
(`TauCeti.coefficient_principal_apply_eq_classicalPrincipalSymbol`).

## Main results

* `TauCeti.classicalPrincipalSymbol_nonneg`: an operator that is positive on the functions
  supported in an open set `U` has a nonnegative principal symbol over `U`.
* `TauCeti.IsClassicalEllipticAt.classicalPrincipalSymbol_pos`: where it is moreover elliptic, the
  principal symbol is positive at nonzero covectors.
* `TauCeti.IsClassicalElliptic.classicalPrincipalSymbol_pos`: a positive elliptic operator has a
  positive principal symbol at every nonzero covector.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators acting on rapidly oscillating functions `exp(i t ⟪y, ξ⟫) φ(y)`).
-/

public section

open Filter Set MeasureTheory
open scoped ContDiff Manifold Distributions SchwartzMap Topology ComplexOrder InnerProductSpace

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} {m : ℝ}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **The pairing of `P` read in a chart.** In the preferred chart `e` at `x`, let `a` be the
symbol of the compression of `P` by a cutoff `χ` on both sides, and `w ≥ 0` the continuous density
of `μ` in the chart. For a Schwartz function `u` with `χ = 1` wherever `u ≠ 0`, the pairing of `P`
with `f = u ∘ e` on `M` is the pairing of `Op(a)` with `u` weighted by `w`. -/
private theorem integral_inner_complexCutoffPullback_eq {x : M}
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (hext : extChartAt 𝓘(ℝ, CoordinateSpace n) x = e.toPartialEquiv)
    {χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)} {a : ClassicalSymbol n ℂ ℂ m}
    (ha : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        e.complexChartCompression he χ χ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) y)
    {w : CoordinateSpace n → ℝ} (hwc : ContinuousOn w (extChartAt 𝓘(ℝ, CoordinateSpace n) x).target)
    (hw0 : ∀ y ∈ (extChartAt 𝓘(ℝ, CoordinateSpace n) x).target, 0 ≤ w y)
    (hw : (μ.restrict (extChartAt 𝓘(ℝ, CoordinateSpace n) x).source).map
        (extChartAt 𝓘(ℝ, CoordinateSpace n) x) =
      (volume.restrict (extChartAt 𝓘(ℝ, CoordinateSpace n) x).target).withDensity
        fun y ↦ ENNReal.ofReal (w y))
    {u : 𝓢(CoordinateSpace n, ℂ)} (hu : ∀ y, u y ≠ 0 → χ y = 1) :
    ∫ z, ⟪P (e.complexCutoffPullback he χ (ContMDiffMap.ofContDiff u (u.smooth ⊤))) z,
      e.complexCutoffPullback he χ (ContMDiffMap.ofContDiff u (u.smooth ⊤)) z⟫_ℂ ∂μ =
      ∫ y, w y • ⟪quantizeSchwartzValue a.toSymbol.coefficient u y, u y⟫_ℂ := by
  set f := e.complexCutoffPullback he χ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
  -- On the chart target, `f ∘ e⁻¹ = χ u = u` and `Op(a) u = χ (P f ∘ e⁻¹)`.
  have hf : ∀ y ∈ e.target, f (e.symm y) = u y := fun y hy ↦ by
    rw [OpenPartialHomeomorph.complexCutoffPullback_apply_of_mem he _ _ (e.map_target hy),
      e.right_inv hy]
    by_cases huy : u y = 0
    · simp [huy]
    · simp [hu y huy]
  have hOp : ∀ y ∈ e.target, w y • ⟪P f (e.symm y), f (e.symm y)⟫_ℂ =
      w y • ⟪quantizeSchwartzValue a.toSymbol.coefficient u y, u y⟫_ℂ := fun y hy ↦ by
    rw [ha, OpenPartialHomeomorph.complexChartCompression_apply, hf y hy]
    by_cases huy : u y = 0
    · simp [huy]
    · rw [hu y huy, one_smul]
  -- Off the chart target `u` vanishes, since `χ = 1` wherever `u ≠ 0`.
  have h0 : ∀ y ∉ e.target,
      w y • ⟪quantizeSchwartzValue a.toSymbol.coefficient u y, u y⟫_ℂ = 0 := fun y hy ↦ by
    by_cases huy : u y = 0
    · rw [huy, inner_zero_right, smul_zero]
    · exact absurd (χ.tsupport_subset (subset_tsupport _ (by simp [hu y huy]))) hy
  have hint := integral_eq_setIntegral_smul_extChartAt_symm (F := fun z ↦ ⟪P f z, f z⟫_ℂ) hwc hw0
    hw ((P f).contMDiff.continuous.inner f.contMDiff.continuous).continuousOn fun z hz ↦ by
      rw [hext] at hz
      simp [OpenPartialHomeomorph.complexCutoffPullback_apply_of_notMem he _ _ hz, f]
  rw [hext] at hint
  simp only [OpenPartialHomeomorph.coe_toPartialEquiv_symm] at hint
  rw [hint, ← setIntegral_eq_integral_of_forall_compl_eq_zero h0,
    setIntegral_congr_fun e.open_target.measurableSet hOp]

/-- **A positive operator has a nonnegative principal symbol.** Let `μ` be a positive continuous
density measure on `M`, `U` an open set and `P` an operator on `C^∞(M, ℂ)`. If
`0 ≤ ∫ ⟪P f (x), f (x)⟫ dμ(x)` for every compactly supported smooth function `f` supported in `U`
(a real nonnegative number), then the principal symbol `σ_m(P)(x, ξ)` is real and nonnegative at
every `x ∈ U` and every covector `ξ ∈ T*ₓM`. This is the content when `P` is a classical
pseudodifferential operator of order `m`; otherwise `σ_m(P)` is `0` by convention. -/
theorem classicalPrincipalSymbol_nonneg
    (hμ : IsPositiveDensityMeasure 𝓘(ℝ, CoordinateSpace n) μ) {U : Set M} (hU : IsOpen U)
    (hpos : ∀ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport f →
      tsupport f ⊆ U → 0 ≤ ∫ x, ⟪P f x, f x⟫_ℂ ∂μ)
    {x : M} (hx : x ∈ U) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    0 ≤ classicalPrincipalSymbol m P x ξ := by
  refine (em (P ∈ classicalPseudodifferentialOperators m)).elim (fun hP ↦ ?_)
    fun hP ↦ (classicalPrincipalSymbol_of_notMem hP x ξ).ge
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hxe : x ∈ e.source := mem_chart_source _ x
  -- A closed ball `K` around `e x` inside the chart image of `U`, and a cutoff `χ` equal to `1`
  -- on `K`.
  have hV : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hxV : e x ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source hxe, by rwa [mem_preimage, e.left_inv hxe]⟩
  obtain ⟨r, hr, hrV⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (hV.mem_nhds hxV)
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) (isCompact_closedBall (e x) r) (hrV.trans inter_subset_left)
  have hχ1 : ∀ y ∈ Metric.closedBall (e x) r, χ y = 1 := fun y hy ↦ hχ.self_of_nhdsSet y hy
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ
  -- The density `w` of `μ` in the chart.
  obtain ⟨w, hwc, hwpos, hw⟩ := (isPositiveDensityMeasure_iff_of_isAddHaarMeasure volume).1 hμ x
  have hext : extChartAt 𝓘(ℝ, CoordinateSpace n) x = e.toPartialEquiv := by
    rw [extChartAt, OpenPartialHomeomorph.extend_modelWithCornersSelf]
  -- `Op(a)` is positive near `e x` for the pairing weighted by `w`: it is the pairing of `P` with
  -- `u ∘ e`, a function supported in `U`.
  have hpos' : ∀ u : 𝓢(CoordinateSpace n, ℂ), HasCompactSupport u →
      tsupport u ⊆ Metric.ball (e x) r →
        0 ≤ ∫ y, w y • ⟪quantizeSchwartzValue a.toSymbol.coefficient u y, u y⟫_ℂ := by
    intro u _ huB
    have huK : tsupport u ⊆ Metric.closedBall (e x) r := huB.trans Metric.ball_subset_closedBall
    set f := e.complexCutoffPullback he χ (ContMDiffMap.ofContDiff u (u.smooth ⊤))
    have hfU : tsupport f ⊆ U := (e.tsupport_complexCutoffPullback_subset_inter he χ _).trans
      (image_subset_iff.2 fun y hy ↦
        (hrV (huK (by rw [ContMDiffMap.coe_ofContDiff] at hy; exact hy.2))).2)
    have hfc : HasCompactSupport f := (e.isCompact_symm_image_tsupport χ).of_isClosed_subset
      (isClosed_tsupport _) (e.tsupport_complexCutoffPullback_subset he χ _)
    rw [← integral_inner_complexCutoffPullback_eq he hext ha hwc (fun y hy ↦ (hwpos y hy).le) hw
      fun y hy ↦ hχ1 y (huK (subset_tsupport _ hy))]
    exact hpos f hfc hfU
  -- Hence the principal symbol of `a` is a positive operator at `e x`; at the frequency of `ξ`
  -- it is `σ_m(P)(x, ξ)`, since `χ (e x) = 1`.
  rw [hext] at hwc hwpos
  have hσ := a.isPositive_coefficient_principal_of_weight Metric.isOpen_ball
    (hwc.mono (Metric.ball_subset_closedBall.trans (hrV.trans inter_subset_left))) hpos'
    (Metric.mem_ball_self hr) (hwpos _ hxV.1) ((InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
      (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse))
  have hprin := coefficient_principal_apply_eq_classicalPrincipalSymbol hP he χ χ ha hxe ξ
  simp [hχ1 _ (Metric.mem_closedBall_self hr.le)] at hprin
  simpa [RCLike.inner_apply, hprin] using hσ.inner_nonneg_right 1

/-- **A positive operator elliptic at a point has a positive principal symbol there.** Let `μ` be
a positive continuous density measure on `M`, `U` an open set and `P` an operator on `C^∞(M, ℂ)`
with `0 ≤ ∫ ⟪P f (x), f (x)⟫ dμ(x)` for every compactly supported smooth function `f` supported in
`U`. If `P` is elliptic of order `m` at `x ∈ U`, then `σ_m(P)(x, ξ)` is real and positive at every
nonzero covector `ξ ∈ T*ₓM`. -/
theorem IsClassicalEllipticAt.classicalPrincipalSymbol_pos {x : M}
    (hPx : IsClassicalEllipticAt m P x) (hμ : IsPositiveDensityMeasure 𝓘(ℝ, CoordinateSpace n) μ)
    {U : Set M} (hU : IsOpen U)
    (hpos : ∀ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport f →
      tsupport f ⊆ U → 0 ≤ ∫ x, ⟪P f x, f x⟫_ℂ ∂μ)
    (hx : x ∈ U) {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    0 < classicalPrincipalSymbol m P x ξ :=
  (classicalPrincipalSymbol_nonneg hμ hU hpos hx ξ).lt_of_ne
    (isClassicalEllipticAt_iff.1 hPx ξ hξ).symm

/-- **A positive elliptic operator has a positive principal symbol.** Let `μ` be a positive
continuous density measure on `M` and `P` an operator on `C^∞(M, ℂ)`, elliptic of order `m`, with
`0 ≤ ∫ ⟪P f (x), f (x)⟫ dμ(x)` for every compactly supported smooth function `f`. Then
`σ_m(P)(x, ξ)` is real and positive at every point `x` and every nonzero covector `ξ ∈ T*ₓM`. -/
theorem IsClassicalElliptic.classicalPrincipalSymbol_pos (hPe : IsClassicalElliptic m P)
    (hμ : IsPositiveDensityMeasure 𝓘(ℝ, CoordinateSpace n) μ)
    (hpos : ∀ f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯, HasCompactSupport f →
      0 ≤ ∫ x, ⟪P f x, f x⟫_ℂ ∂μ)
    (x : M) {ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
    0 < classicalPrincipalSymbol m P x ξ :=
  (isClassicalElliptic_iff.1 hPe x).classicalPrincipalSymbol_pos hμ isOpen_univ
    (fun f hf _ ↦ hpos f hf) (mem_univ x) hξ

end TauCeti
