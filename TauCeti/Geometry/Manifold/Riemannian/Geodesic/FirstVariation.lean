/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.FirstVariation
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Geodesics are the critical points of the energy

The first variation formula `TauCeti.Manifold.IsFixedEndpointVariation.hasDerivAt_energy` of
`TauCeti.Geometry.Manifold.Riemannian.FirstVariation` expresses the derivative at `s = 0` of the
energy of a fixed-endpoint variation `F` of `γ = F 0` as `-∫_a^b ⟪V(t), D_t γ'(t)⟫ dt`.  This file
proves the variational characterization of geodesics: on a boundaryless `C^n` manifold with
`2 ≤ n ≤ ∞`, a curve which is `C^n` near `[a, b]` is a critical point of the energy between `a`
and `b` among `C^n` variations (`TauCeti.Manifold.IsEnergyCritical`) exactly when it is a geodesic
on the open interval between `a` and `b`.  In particular, for `n = ∞`, a smooth curve is critical
among smooth variations with fixed endpoints exactly when it is a geodesic.

Along a geodesic the covariant acceleration `D_t γ'` vanishes, so the first variation vanishes.
Conversely, suppose `D_t γ'(t₀) ≠ 0` at an interior parameter `t₀`.  In the extended chart at
`γ t₀`, pushing `γ` in the direction of a fixed coordinate vector `e`, with a bump function `φ`
supported near `t₀` as profile, is a fixed-endpoint variation, as regular as `γ` and the
manifold, whose variation field is `φ` times
the coordinate field of `e`.  For `e` the coordinate vector of `D_t γ'(t₀)`, the pairing `g` of
that coordinate field with `D_t γ'` is positive at `t₀`; it is continuous there, because the
first-variation integrand of such a variation is
(`TauCeti.Manifold.continuousAt_inner_variationField_acceleration`).  A bump supported where
`g > 0` then gives a variation whose first variation `-∫_a^b φ g` is nonzero.

## Main definitions and results

* `TauCeti.Manifold.IsGeodesicCurveOn.isEnergyCritical`: **geodesics are critical points of the
  energy** among `C^n` variations with fixed endpoints, for every `2 ≤ n`.
* `TauCeti.Manifold.IsEnergyCritical.isGeodesicCurveOn`: **critical points of the energy are
  geodesics**, for `2 ≤ n ≤ ∞`.
* `TauCeti.Manifold.isEnergyCritical_iff_isGeodesicCurveOn`: the two combined.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 9, §2, Propositions 2.4 and 2.5.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §12,
  Corollary 12.3.
-/

public section

open Bundle CovariantDerivative Filter Metric MeasureTheory Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {a b : ℝ}

/-! ### Geodesics are critical -/

/-- **Geodesics are critical points of the energy.** For `2 ≤ n`, a geodesic on the open interval
between `a` and `b` which is `C^n` at every point of `[a, b]` is a critical point of the energy
between `a` and `b` among `C^n` variations with fixed endpoints. -/
theorem IsGeodesicCurveOn.isEnergyCritical {n : WithTop ℕ∞} (hn : 2 ≤ n)
    (h : IsGeodesicCurveOn I γ (uIoo a b)) (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t) :
    IsEnergyCritical I n γ a b := by
  refine (isEnergyCritical_iff_integral_inner_eq_zero hn hγ).mpr fun F hF0 _ ↦ ?_
  subst hF0
  refine (intervalIntegral.integral_congr_uIoo (g := fun _ ↦ (0 : ℝ)) fun t ht ↦ ?_).trans
    intervalIntegral.integral_zero
  simp only [((isGeodesicCurveOn_iff_of_isOpen isOpen_Ioo).mp h).2 t ht, inner_zero_right]

/-! ### Critical points are geodesics -/

section Converse

variable [I.Boundaryless] {n : ℕ∞} {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E}

open scoped Classical in
variable (I) in
/-- The variation of `γ` which, at the parameters of `J`, pushes `γ t` in the direction of the
coordinate vector `e` of the extended chart at `x₀`, with profile `φ`:
`(s, t) ↦ ψ⁻¹ (ψ (γ t) + (s φ(t)) • e)` for `ψ = extChartAt I x₀`.  Outside `J` it is `γ`. -/
private def chartVariation (γ : ℝ → M) (x₀ : M) (J : Set ℝ) (φ : ℝ → ℝ) (e : E) (s t : ℝ) : M :=
  if t ∈ J then (extChartAt I x₀).symm (extChartAt I x₀ (γ t) + (s * φ t) • e) else γ t

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless] in
/-- Outside `J`, the chart variation is `γ`. -/
private theorem chartVariation_of_notMem {t : ℝ} (ht : t ∉ J) (s : ℝ) :
    chartVariation I γ x₀ J φ e s t = γ t := by
  simp [chartVariation, ht]

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless] in
/-- Where the displacement `s φ(t)` vanishes, the chart variation is `γ`. -/
private theorem chartVariation_of_mul_eq_zero (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    {s t : ℝ} (h : s * φ t = 0) : chartVariation I γ x₀ J φ e s t = γ t := by
  by_cases htJ : t ∈ J
  · simp only [chartVariation, htJ, ↓reduceIte, h, zero_smul, add_zero]
    exact (extChartAt I x₀).left_inv (hJ t htJ)
  · exact chartVariation_of_notMem htJ s

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] [I.Boundaryless] in
/-- The central curve of the chart variation is `γ`. -/
private theorem chartVariation_zero (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) :
    chartVariation I γ x₀ J φ e 0 = γ :=
  funext fun _ ↦ chartVariation_of_mul_eq_zero hJ (zero_mul _)

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- On a `C^n` manifold, the chart variation of a curve which is `C^n` at `t` is `C^n` at `(0, t)`,
for a `C^n` profile supported in the open set `J`. -/
private theorem contMDiffAt_chartVariation [IsManifold I n M] (hJo : IsOpen J)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J)
    {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (fun z : ℝ × ℝ ↦ chartVariation I γ x₀ J φ e z.1 z.2) (0, t) := by
  by_cases htJ : t ∈ J
  · -- near `(0, t)` the family is given by the chart formula
    have hc : ContDiffAt ℝ n (extChartAt I x₀ ∘ γ) t :=
      contMDiffAt_iff_contDiffAt.mp
        ((contMDiffAt_extChartAt' (by simpa using hJ t htJ)).comp t hγ)
    have hg : ContDiffAt ℝ n (fun z : ℝ × ℝ ↦ extChartAt I x₀ (γ z.2) + (z.1 * φ z.2) • e)
        (0, t) :=
      (hc.comp (0, t) contDiffAt_snd).add
        ((contDiffAt_fst.mul (hφ.contDiffAt.comp (0, t) contDiffAt_snd)).smul contDiffAt_const)
    have hmem : extChartAt I x₀ (γ t) + ((0 : ℝ) * φ t) • e ∈ (extChartAt I x₀).target := by
      simpa using (extChartAt I x₀).map_source (hJ t htJ)
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I x₀).symm
        (extChartAt I x₀ (γ t) + ((0 : ℝ) * φ t) • e) :=
      (contMDiffOn_extChartAt_symm x₀ _ hmem).contMDiffAt
        ((isOpen_extChartAt_target x₀).mem_nhds hmem)
    refine (hsymm.comp (0, t) (contMDiffAt_iff_contDiffAt.mpr hg)).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hJo.mem_nhds htJ)] with z hz
    simp [chartVariation, show z.2 ∈ J from hz]
  · -- away from the support of `φ` the family is `γ`, which is `C^n` near `t`
    have hev : φ =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp fun h ↦ htJ (hφJ h)
    refine (hγ.comp (0, t) contDiff_snd.contMDiff.contMDiffAt).congr_of_eventuallyEq ?_
    filter_upwards [continuousAt_snd.preimage_mem_nhds hev] with z hz
    exact chartVariation_of_mul_eq_zero hJ (by rw [hz, Pi.zero_apply, mul_zero])

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- On a `C^n` manifold, the chart variation of a curve which is `C^n` on `[a, b]`, for a `C^n`
profile supported in an open set `J ⊆ uIoo a b`, is a `C^n` variation with fixed endpoints between
`a` and `b`. -/
private theorem isFixedEndpointVariation_chartVariation [IsManifold I n M] (hJo : IsOpen J)
    (hJab : J ⊆ uIoo a b) (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ n φ)
    (hφJ : tsupport φ ⊆ J) (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t) :
    IsFixedEndpointVariation I n (chartVariation I γ x₀ J φ e) a b := by
  have hend : ∀ c ∉ uIoo a b, ∀ᶠ s in 𝓝 (0 : ℝ),
      chartVariation I γ x₀ J φ e s c = chartVariation I γ x₀ J φ e 0 c :=
    fun c hc ↦ .of_forall fun s ↦ by
      rw [chartVariation_of_notMem (fun hcJ ↦ hc (hJab hcJ)),
        chartVariation_of_notMem (fun hcJ ↦ hc (hJab hcJ))]
  exact ⟨fun t ht ↦ contMDiffAt_chartVariation hJo hJ hφ hφJ (hγ t ht),
    hend a left_notMem_uIoo, hend b right_notMem_uIoo⟩

omit [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [FiniteDimensional ℝ E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)] in
/-- At a parameter of `J`, the variation field of the chart variation is `φ t` times the tangent
vector at `γ t` with coordinates `e` in the tangent-bundle trivialization at `x₀`. -/
private theorem variationField_chartVariation (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    {t : ℝ} (htJ : t ∈ J) :
    variationField I (chartVariation I γ x₀ J φ e) t =
      φ t • (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e := by
  have hmem : extChartAt I x₀ (γ t) ∈ (extChartAt I x₀).target :=
    (extChartAt I x₀).map_source (hJ t htJ)
  have hfun : (fun s ↦ chartVariation I γ x₀ J φ e s t) =
      (extChartAt I x₀).symm ∘ fun s : ℝ ↦ extChartAt I x₀ (γ t) + (s * φ t) • e := by
    funext s
    simp only [chartVariation, htJ, ↓reduceIte, Function.comp_apply]
  have hderiv : HasDerivAt (fun s : ℝ ↦ extChartAt I x₀ (γ t) + (s * φ t) • e) (φ t • e) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const (φ t)).smul_const e).const_add
      (extChartAt I x₀ (γ t))
  have hmd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ (γ t)) :=
    (mdifferentiableWithinAt_extChartAt_symm hmem).mdifferentiableAt
      (by rw [I.range_eq_univ]; exact univ_mem)
  -- the chain rule, with the base point `ψ (γ t) + (0 * φ t) • e` of the transverse curve
  -- normalized to `ψ (γ t)`
  have hvel : ∀ y, extChartAt I x₀ (γ t) + ((0 : ℝ) * φ t) • e = y →
      curveVelocity I ((extChartAt I x₀).symm ∘ fun s : ℝ ↦ extChartAt I x₀ (γ t) + (s * φ t) • e)
        0 = mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y (φ t • e) := by
    rintro y rfl
    exact MDifferentiableAt.curveVelocity_comp_mfderiv (by simpa using hmd) hderiv
  rw [variationField_apply, hfun, hvel (extChartAt I x₀ (γ t)) (by simp),
    TangentBundle.symmL_trivializationAt (by simpa using hJ t htJ), I.range_eq_univ,
    mfderivWithin_univ]
  exact (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm (extChartAt I x₀ (γ t))).map_smul (φ t) e

/-- The first-variation integrand of the chart variation: `φ t` times the pairing of the tangent
vector with trivialization coordinates `e` against the covariant acceleration of `γ`. -/
private theorem inner_variationField_chartVariation
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (hφJ : Function.support φ ⊆ J) (t : ℝ) :
    inner ℝ (variationField I (chartVariation I γ x₀ J φ e) t)
        (acceleration (leviCivitaConnection I M) (chartVariation I γ x₀ J φ e 0) t) =
      φ t * inner ℝ ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e)
        (acceleration (leviCivitaConnection I M) γ t) := by
  by_cases htJ : t ∈ J
  · rw [chartVariation_zero hJ, variationField_chartVariation hJ htJ, real_inner_smul_left]
  · have hφt : φ t = 0 := Function.notMem_support.mp fun h ↦ htJ (hφJ h)
    rw [variationField_eq_zero (Eventually.of_forall fun s ↦ by
      rw [chartVariation_of_notMem htJ, chartVariation_of_notMem htJ]), inner_zero_left, hφt,
      zero_mul]

/-- **The chart variations of a critical point.** On a `C^n` manifold with `2 ≤ n`, let `γ` be a
critical point of the energy among `C^n` variations between `a` and `b`, and let `φ` be a `C^n`
profile supported in an open set `J ⊆ uIoo a b` on which `γ` stays in the chart at `x₀`.  Write
`g t` for the pairing of the tangent vector with trivialization coordinates `e` at `γ t` against
the covariant acceleration of `γ`.  Then `∫_a^b φ g = 0`, and `φ g` is continuous at every point
of `[a, b]`. -/
private theorem IsEnergyCritical.integral_mul_inner_eq_zero [IsManifold I n M] (hn : 2 ≤ n)
    (h : IsEnergyCritical I n γ a b) (hJo : IsOpen J) (hJab : J ⊆ uIoo a b)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source) (hφ : ContDiff ℝ n φ) (hφJ : tsupport φ ⊆ J)
    (e : E) :
    (∫ t in a..b, φ t * inner ℝ ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e)
        (acceleration (leviCivitaConnection I M) γ t)) = 0 ∧
      ∀ t ∈ uIcc a b, ContinuousAt (fun t ↦ φ t * inner ℝ
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e)
        (acceleration (leviCivitaConnection I M) γ t)) t := by
  have hn' : (2 : WithTop ℕ∞) ≤ n := WithTop.coe_le_coe.mpr hn
  have hF : IsFixedEndpointVariation I n (chartVariation I γ x₀ J φ e) a b :=
    isFixedEndpointVariation_chartVariation hJo hJab hJ hφ hφJ h.contMDiffAt
  have hpt := inner_variationField_chartVariation (e := e) hJ
    ((subset_tsupport φ).trans hφJ)
  refine ⟨?_, fun t ht ↦ ?_⟩
  · simpa only [hpt] using (isEnergyCritical_iff_integral_inner_eq_zero hn' h.contMDiffAt).mp h
      _ (chartVariation_zero hJ) hF
  · simpa only [hpt] using
      continuousAt_inner_variationField_acceleration ((hF.of_le hn').contMDiffAt t ht)

/-- **Critical points of the energy are geodesics.** On a boundaryless `C^n` manifold with
`2 ≤ n ≤ ∞`, a critical point of the energy between `a` and `b` among `C^n` variations with fixed
endpoints is a geodesic on the open interval between `a` and `b`.  For `n = ∞` this is the
statement for smooth curves and smooth variations. -/
theorem IsEnergyCritical.isGeodesicCurveOn [IsManifold I n M] (hn : 2 ≤ n)
    (h : IsEnergyCritical I n γ a b) : IsGeodesicCurveOn I γ (uIoo a b) := by
  have hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t :=
    fun t ht ↦ (h.contMDiffAt t ht).of_le (WithTop.coe_le_coe.mpr hn)
  refine (isGeodesicCurveOn_iff_of_isOpen isOpen_Ioo).mpr
    ⟨fun t ht ↦ (hγ t (uIoo_subset_uIcc_self ht)).contMDiffWithinAt, fun t₀ ht₀ ↦ ?_⟩
  by_contra hA
  set A := acceleration (leviCivitaConnection I M) γ
  -- `g t` pairs the vector with the coordinates `e` of `A t₀` in the trivialization at `γ t₀`
  -- against `A t`; it is positive at `t₀`
  set e : E := (trivializationAt E (TangentSpace I) (γ t₀)).continuousLinearMapAt ℝ (γ t₀) (A t₀)
  set g : ℝ → ℝ := fun t ↦
    inner ℝ ((trivializationAt E (TangentSpace I) (γ t₀)).symmL ℝ (γ t) e) (A t)
  have hg₀ : 0 < g t₀ := by
    simp only [g, e, Trivialization.symmL_continuousLinearMapAt _
      (FiberBundle.mem_baseSet_trivializationAt' (γ t₀)), real_inner_self_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hA) 2
  -- a ball `J` around `t₀` inside `uIoo a b` on which `γ` stays in the chart at `γ t₀`
  obtain ⟨δ, hδ, hδJ⟩ := Metric.mem_nhds_iff.mp (inter_mem (isOpen_Ioo.mem_nhds ht₀)
    ((hγ t₀ (uIoo_subset_uIcc_self ht₀)).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := I) (γ t₀)).mem_nhds (mem_extChartAt_source (γ t₀)))))
  have hJab : ball t₀ δ ⊆ uIoo a b := fun t ht ↦ (hδJ ht).1
  have hJ : ∀ t ∈ ball t₀ δ, γ t ∈ (extChartAt I (γ t₀)).source := fun t ht ↦ (hδJ ht).2
  have hbump : ∀ φ : ContDiffBump t₀, φ.rOut < δ →
      (∫ t in a..b, φ t * g t) = 0 ∧ ∀ t ∈ uIcc a b, ContinuousAt (fun t ↦ φ t * g t) t :=
    fun φ hφ ↦ h.integral_mul_inner_eq_zero hn isOpen_ball hJab hJ φ.contDiff
      (φ.tsupport_eq ▸ closedBall_subset_ball hφ) e
  -- `g` is continuous at `t₀`, since it agrees there with `φ g` for a bump `φ` equal to `1`
  -- near `t₀`
  let φ₁ : ContDiffBump t₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hgcont : ContinuousAt g t₀ := by
    refine ((hbump φ₁ (by dsimp only [φ₁]; linarith)).2 t₀
      (uIoo_subset_uIcc_self ht₀)).congr ?_
    filter_upwards [ball_mem_nhds t₀ (by positivity : 0 < δ / 4)] with t ht
    rw [φ₁.one_of_mem_closedBall (ball_subset_closedBall ht), one_mul]
  -- a bump `φ₂` supported where `g > 0` gives a nonnegative continuous `φ₂ g` with zero integral,
  -- which must vanish on `uIoo a b`; but it is positive at `t₀`
  obtain ⟨ε, hε, hεg⟩ := Metric.eventually_nhds_iff.mp (hgcont.eventually (lt_mem_nhds hg₀))
  set r := min ε (δ / 2)
  have hr : 0 < r := lt_min hε (by positivity)
  let φ₂ : ContDiffBump t₀ := ⟨r / 2, r, by positivity, by linarith⟩
  obtain ⟨hint, hcont⟩ := hbump φ₂ (by dsimp only [φ₂]; linarith [min_le_right ε (δ / 2)])
  have hnn : ∀ t, 0 ≤ φ₂ t * g t := fun t ↦ by
    by_cases ht : t ∈ ball t₀ r
    · exact mul_nonneg φ₂.nonneg (hεg (lt_of_lt_of_le ht (min_le_left _ _))).le
    · have hφt : φ₂ t = 0 := Function.notMem_support.mp (by rwa [φ₂.support_eq])
      rw [hφt, zero_mul]
  have hzero := (intervalIntegral.integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall hnn) (ContinuousOn.intervalIntegrable fun t ht ↦
      (hcont t ht).continuousWithinAt)).mp hint
  have hsub : uIoo a b ⊆ Ioc a b ∪ Ioc b a := by
    rw [← uIoc_eq_union]
    exact Ioo_subset_Ioc_self
  have heq : φ₂ t₀ * g t₀ = 0 :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hsub hzero) isOpen_Ioo
      (fun t ht ↦ (hcont t (uIoo_subset_uIcc_self ht)).continuousWithinAt) continuousOn_const ht₀
  rw [φ₂.one_of_mem_closedBall (mem_closedBall_self (by positivity)), one_mul] at heq
  exact hg₀.ne' heq

/-- **The variational characterization of geodesics.** On a boundaryless `C^n` manifold with
`2 ≤ n ≤ ∞`, a curve which is `C^n` near every point of `[a, b]` is a critical point of the energy
between `a` and `b` among `C^n` variations with fixed endpoints exactly when it is a geodesic on
the open interval between `a` and `b`.  For `n = ∞`: a smooth curve is critical among smooth
variations exactly when it is a geodesic. -/
theorem isEnergyCritical_iff_isGeodesicCurveOn [IsManifold I n M] (hn : 2 ≤ n)
    (hγ : ∀ t ∈ uIcc a b, ContMDiffAt 𝓘(ℝ, ℝ) I n γ t) :
    IsEnergyCritical I n γ a b ↔ IsGeodesicCurveOn I γ (uIoo a b) :=
  ⟨IsEnergyCritical.isGeodesicCurveOn hn,
    fun h ↦ h.isEnergyCritical (WithTop.coe_le_coe.mpr hn) hγ⟩

end Converse

end TauCeti.Manifold

end
