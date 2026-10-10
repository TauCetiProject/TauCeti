/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.InnerProductSpace.Harmonic.Convergence
import TauCeti.Analysis.InnerProductSpace.Harmonic.MeanValue.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Convolution
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Weyl's lemma

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`, and
let `Ω ⊆ E` be open. A locally integrable function `u : E → ℝ` is **weakly harmonic** on `Ω` if

`∫ Δφ • u ∂μ = 0` for every test function `φ ∈ 𝓓(Ω)`,

that is, if its distributional Laplacian vanishes on `Ω`. Every harmonic function is weakly
harmonic (`InnerProductSpace.HarmonicOnNhd.integral_laplacian_smul_eq_zero`). **Weyl's lemma** is
the converse: a weakly harmonic function agrees almost everywhere on `Ω` with a function harmonic
on `Ω`, that is, twice continuously differentiable with vanishing Laplacian. No differentiability
of `u` is assumed, so a locally integrable distributional solution of `Δu = 0` is, after
modification on a null set, a classical one.

For a function continuous on `Ω` no modification is needed, and harmonicity on `Ω` is equivalent
to weak harmonicity there (`TauCeti.harmonicOnNhd_iff_integral_laplacian_smul_eq_zero`).

## The argument

Fix a closed ball `closedBall x (3R) ⊆ Ω`, let `f` be `u` cut off to it, and mollify:
`uₙ = ρₙ ⋆ f` with `ρₙ` a normalized smooth bump of radius `rₙ → 0`, `rₙ ≤ R`. Each `uₙ` is
smooth, and on `ball x (2R)` its Laplacian is `∫ Δρₙ(y - t) u(t) dt`, the pairing of `u` with the
Laplacian of the test function `t ↦ ρₙ(y - t)`, so it vanishes: `uₙ` is harmonic there. By the
mean-value property, `uₙ y` is the average of `uₙ` over `ball y R` for `y ∈ ball x R`, so

`|uₙ y - ⨍_{ball y R} f| ≤ ‖uₙ - f‖_{L¹} / μ(ball 0 R)`,

and `uₙ → f` in `L¹` makes the convergence of `uₙ` to `y ↦ ⨍_{ball y R} f` uniform on `ball x R`.
A locally uniform limit of harmonic functions is harmonic, and since also `uₙ → f` almost
everywhere (Lebesgue differentiation), this limit is a harmonic function equal to `u` almost
everywhere on `ball x R`.

These local harmonic representatives are glued by the limit of the ball averages of `u`: near
each point, the average of `u` over every small ball about `y` equals the value at `y` of the
local representative, by its mean-value property. This defines a single function, harmonic on `Ω`
and equal to `u` almost everywhere on `Ω`.

## Main declarations

* `TauCeti.exists_harmonicOnNhd_ae_eq_of_integral_laplacian_smul_eq_zero`: **Weyl's lemma**.
* `TauCeti.harmonicOnNhd_iff_integral_laplacian_smul_eq_zero`: a continuous function is harmonic
  on `Ω` if and only if it is weakly harmonic there.

## References

* H. Weyl, *The method of orthogonal projection in potential theory*, Duke Math. J. **7** (1940),
  411–444.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Theorem 4.4.1.
* G. B. Folland, *Introduction to Partial Differential Equations*, 2nd ed., Corollary 2.20.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian MeasureTheory Metric Set Filter Topology TopologicalSpace
  ContinuousLinearMap
open scoped Distributions Convolution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ}

/-- The Laplacian of a mollification of `u` vanishes at `y` when `u` is weakly harmonic on `Ω`:
if the closed ball of radius `φ.rOut` about `y` lies in `Ω` and `f` agrees with `u` there, then
`Δ (ρ ⋆ f) y = ∫ Δρ(y - t) f(t) dt` is the pairing of `u` with the Laplacian of the test function
`t ↦ ρ(y - t)` on `Ω`, where `ρ` is the normalized bump `φ.normed μ`. -/
private theorem laplacian_normed_convolution_eq_zero
    (hΔ : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = 0) (φ : ContDiffBump (0 : E))
    {f : E → ℝ} (hf : Integrable f μ) {y : E} (hyΩ : closedBall y φ.rOut ⊆ Ω)
    (hfu : EqOn f u (closedBall y φ.rOut)) :
    Δ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) y = 0 := by
  set ρ : E → ℝ := φ.normed μ with hρ_def
  -- The test function `ψ t = ρ (y - t)`, supported in `closedBall y φ.rOut ⊆ Ω`.
  set g : E → ℝ := fun t ↦ ρ (y - t) with hg_def
  have hg_supp : tsupport g ⊆ closedBall y φ.rOut := by
    refine closure_minimal (fun t ht ↦ ?_) isClosed_closedBall
    have : y - t ∈ Function.support ρ := ht
    rw [hρ_def, φ.support_normed_eq, mem_ball_zero_iff, ← dist_eq_norm] at this
    exact (mem_closedBall'.2 this.le)
  let ψ : 𝓓(Ω, ℝ) := ⟨g, φ.contDiff_normed.comp (contDiff_const.sub contDiff_id),
    (isCompact_closedBall y φ.rOut).of_isClosed_subset (isClosed_tsupport _) hg_supp,
    hg_supp.trans hyΩ⟩
  have hψ : (ψ : E → ℝ) = g := rfl
  -- `Δψ t = Δρ (y - t)`, by invariance of the Laplacian under `t ↦ -t` and translations.
  have hΔg : ∀ t, Δ g t = Δ ρ (y - t) := by
    have hcomp : g = (fun s ↦ ρ (s + y)) ∘ (LinearIsometryEquiv.neg ℝ (E := E)) := by
      ext t
      simp [hg_def, neg_add_eq_sub]
    intro t
    rw [hcomp, laplacian_comp_linearIsometryEquiv_right, laplacian_comp_add_right]
    simp [neg_add_eq_sub]
  -- Move the Laplacian onto the bump, then recognize the pairing of `u` with `Δψ`.
  rw [← convolution_flip, HasCompactSupport.laplacian_convolution_right _ φ.hasCompactSupport_normed
    hf.locallyIntegrable φ.contDiff_normed, convolution_def, ← hΔ ψ]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  simp only [flip_apply, lsmul_apply, smul_eq_mul]
  rw [hψ, hΔg]
  by_cases ht : t ∈ closedBall y φ.rOut
  · rw [hfu ht]
  · have hρ0 : Δ ρ (y - t) = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun h ↦ ht ?_
      have h' := tsupport_laplacian_subset ρ h
      rw [hρ_def, φ.tsupport_normed_eq, mem_closedBall_zero_iff, ← dist_eq_norm] at h'
      exact mem_closedBall'.2 h'
    rw [hρ0, zero_mul, zero_mul]

/-- A mollification of `u` is harmonic on every open set `s` whose points `y` have
`closedBall y φ.rOut ⊆ Ω`, provided the mollified function `f` agrees with `u` on those balls and
`u` is weakly harmonic on `Ω`. -/
private theorem harmonicOnNhd_normed_convolution
    (hΔ : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = 0) (φ : ContDiffBump (0 : E))
    {f : E → ℝ} (hf : Integrable f μ) {s : Set E} (hs : IsOpen s)
    (hsΩ : ∀ y ∈ s, closedBall y φ.rOut ⊆ Ω) (hfu : ∀ y ∈ s, EqOn f u (closedBall y φ.rOut)) :
    HarmonicOnNhd (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) s := fun _ hy ↦
  ⟨(φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hf.locallyIntegrable).contDiffAt,
    eventually_of_mem (hs.mem_nhds hy) fun z hz ↦
      laplacian_normed_convolution_eq_zero hΔ φ hf (hsΩ z hz) (hfu z hz)⟩

/-- The mean-value property turns `L¹` closeness into uniform closeness: if `U` is harmonic near
`closedBall y R`, then `U y` differs from the average of `f` over `ball y R` by at most
`‖U - f‖₁ / μ(ball 0 R)`. -/
private theorem dist_setAverage_ball_le_of_harmonicOnNhd {U f : E → ℝ} {y : E} {R : ℝ}
    (hR : 0 < R) (hU : HarmonicOnNhd U (closedBall y R)) (hf : Integrable f μ)
    (hUf : Integrable (U - f) μ) :
    dist (⨍ z in ball y R, f z ∂μ) (U y) ≤
      (μ.real (ball (0 : E) R))⁻¹ * (eLpNorm (U - f) 1 μ).toReal := by
  have hUi : IntegrableOn U (ball y R) μ :=
    (hU.contDiffOn.continuousOn.integrableOn_compact (isCompact_closedBall y R)).mono_set
      ball_subset_closedBall
  rw [← hU.setAverage_ball_eq (μ := μ) hR, dist_eq_norm, ← average_sub hf.integrableOn hUi,
    setAverage_eq, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 measureReal_nonneg),
    Measure.addHaar_real_ball_center]
  gcongr
  calc ‖∫ z in ball y R, f z - U z ∂μ‖ ≤ ∫ z in ball y R, ‖(U - f) z‖ ∂μ :=
        (norm_integral_le_integral_norm _).trans_eq
          (integral_congr_ae (ae_of_all _ fun z ↦ by simp [norm_sub_rev]))
    _ ≤ ∫ z, ‖(U - f) z‖ ∂μ := setIntegral_le_integral hUf.norm (ae_of_all _ fun _ ↦ norm_nonneg _)
    _ = (eLpNorm (U - f) 1 μ).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm hUf.aestronglyMeasurable]
        exact integral_norm_eq_lintegral_enorm hUf.aestronglyMeasurable

/-- The normalized bumps of outer radius `R / (n + 1)` and inner radius half of that, which shrink
to the origin. -/
private noncomputable def shrinkingBump {R : ℝ} (hR : 0 < R) (n : ℕ) : ContDiffBump (0 : E) where
  rIn := R / (2 * (n + 1))
  rOut := R / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := div_lt_div_of_pos_left hR (by positivity) (by linarith)

/-- **Weyl's lemma near a point.** If `u` is weakly harmonic on `Ω` and
`closedBall x (3 * R) ⊆ Ω`, then `u` agrees almost everywhere on `ball x R` with a function
harmonic on `ball x R`. -/
private theorem exists_harmonicOnNhd_ball_ae_eq (hu : LocallyIntegrableOn u Ω μ)
    (hΔ : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = 0) {x : E} {R : ℝ} (hR : 0 < R)
    (hxΩ : closedBall x (3 * R) ⊆ Ω) :
    ∃ h : E → ℝ, HarmonicOnNhd h (ball x R) ∧ u =ᵐ[μ.restrict (ball x R)] h := by
  set K := closedBall x (3 * R)
  set f := K.indicator u
  have hf : Integrable f μ :=
    (hu.integrableOn_compact_subset hxΩ (isCompact_closedBall x _)).integrable_indicator
      measurableSet_closedBall
  set φ : ℕ → ContDiffBump (0 : E) := shrinkingBump hR
  have hφR : ∀ n, (φ n).rOut ≤ R := fun n ↦
    div_le_self hR.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hφ0 : Tendsto (fun n ↦ (φ n).rOut) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  set U : ℕ → E → ℝ := fun n ↦ (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] f
  -- Each mollification is harmonic on `ball x (2R)`, where it only sees `u` on `K ⊆ Ω`.
  have hsub : ∀ n, ∀ y ∈ ball x (2 * R), closedBall y (φ n).rOut ⊆ ball x (3 * R) :=
    fun n y hy z hz ↦ by
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle z y x, mem_closedBall.1 hz, hφR n]
  have hUh : ∀ n, HarmonicOnNhd (U n) (ball x (2 * R)) := fun n ↦
    harmonicOnNhd_normed_convolution hΔ (φ n) hf isOpen_ball
      (fun y hy ↦ (hsub n y hy).trans (ball_subset_closedBall.trans hxΩ))
      fun y hy z hz ↦ indicator_of_mem (ball_subset_closedBall (hsub n y hy hz)) u
  -- The mollifications converge to `f` in `L¹`, hence, by the mean-value property, uniformly on
  -- `ball x R` to the averages `h y` of `f` over the balls `ball y R`.
  set h : E → ℝ := fun y ↦ ⨍ z in ball y R, f z ∂μ
  have hL1 : Tendsto (fun n ↦ (μ.real (ball (0 : E) R))⁻¹ * (eLpNorm (U n - f) 1 μ).toReal)
      atTop (𝓝 0) := by
    simpa using ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (tendsto_eLpNorm_normed_convolution_sub ENNReal.one_ne_top hφ0
        (memLp_one_iff_integrable.2 hf))).const_mul (μ.real (ball (0 : E) R))⁻¹
  have hunif : TendstoUniformlyOn U h atTop (ball x R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hL1.eventually (gt_mem_nhds hε)] with n hn y hy
    have hyB : closedBall y R ⊆ ball x (2 * R) := fun z hz ↦ by
      rw [mem_ball] at hy ⊢
      linarith [dist_triangle z y x, mem_closedBall.1 hz]
    exact (dist_setAverage_ball_le_of_harmonicOnNhd hR ((hUh n).mono hyB) hf
      (((φ n).integrable_normed.integrable_convolution (lsmul ℝ ℝ) hf).sub hf)).trans_lt hn
  refine ⟨h, harmonicOnNhd_of_tendstoLocallyUniformlyOn isOpen_ball
    (Eventually.of_forall fun n ↦ (hUh n).mono (ball_subset_ball (by linarith)))
    hunif.tendstoLocallyUniformlyOn, ?_⟩
  -- By Lebesgue differentiation, `U n → f` almost everywhere, so `h = f = u` a.e. on `ball x R`.
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := μ) (K := 2) hφ0
    (Eventually.of_forall fun n ↦ le_of_eq (by
      simp only [φ, shrinkingBump]
      field_simp))
    hf.locallyIntegrable
  rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
  filter_upwards [hae] with y hy hyx
  have hyK : y ∈ K := ball_subset_closedBall (ball_subset_ball (by linarith) hyx)
  rw [← indicator_of_mem hyK u]
  exact tendsto_nhds_unique hy (hunif.tendsto_at hyx)

/-- **Weyl's lemma.** Let `u` be locally integrable on the open set `Ω` and weakly harmonic there:
`∫ Δφ • u ∂μ = 0` for every test function `φ ∈ 𝓓(Ω)`. Then `u` agrees almost everywhere on `Ω`
with a function harmonic on `Ω`. -/
theorem exists_harmonicOnNhd_ae_eq_of_integral_laplacian_smul_eq_zero
    (hu : LocallyIntegrableOn u Ω μ)
    (hΔ : ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = 0) :
    ∃ v : E → ℝ, HarmonicOnNhd v Ω ∧ u =ᵐ[μ.restrict Ω] v := by
  -- Around each point of `Ω`, a ball on which `u` has a harmonic representative.
  have hloc : ∀ x ∈ (Ω : Set E), ∃ R > 0, ∃ h : E → ℝ,
      HarmonicOnNhd h (ball x R) ∧ u =ᵐ[μ.restrict (ball x R)] h := fun x hx ↦ by
    obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (Ω.isOpen.mem_nhds hx)
    exact ⟨r / 3, by positivity,
      exists_harmonicOnNhd_ball_ae_eq hu hΔ (by positivity)
        (by rwa [mul_div_cancel₀ _ three_ne_zero])⟩
  choose! R hR h hh hhu using hloc
  -- The glued function: the limit of the averages of `u` over shrinking balls.
  set v : E → ℝ := fun y ↦ limUnder (𝓝[>] (0 : ℝ)) fun r ↦ ⨍ z in ball y r, u z ∂μ
  -- Near `x`, `v` is the local representative `h x`, by its mean-value property.
  have hv : ∀ x ∈ (Ω : Set E), EqOn v (h x) (ball x (R x / 2)) := by
    intro x hx y hy
    have hlim : Tendsto (fun r ↦ ⨍ z in ball y r, u z ∂μ) (𝓝[>] 0) (𝓝 (h x y)) := by
      refine tendsto_const_nhds.congr' (eventually_of_mem (Ioo_mem_nhdsGT (half_pos (hR x hx)))
        fun r hr ↦ ?_)
      have hsub : closedBall y r ⊆ ball x (R x) := fun z hz ↦ by
        rw [mem_ball] at hy ⊢
        linarith [dist_triangle z y x, mem_closedBall.1 hz, hr.2]
      dsimp only
      rw [setAverage_congr_fun measurableSet_ball ((ae_restrict_iff' measurableSet_ball).1
        (ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hsub) (hhu x hx))),
        ((hh x hx).mono hsub).setAverage_ball_eq hr.1]
    exact hlim.limUnder_eq
  refine ⟨v, fun x hx ↦ ?_, ?_⟩
  · have hev : v =ᶠ[𝓝 x] h x :=
      eventually_of_mem (ball_mem_nhds x (half_pos (hR x hx))) (hv x hx)
    exact (harmonicAt_congr_nhds hev).2 (hh x hx x (mem_ball_self (hR x hx)))
  · -- `u = v` almost everywhere near each point of `Ω`, hence on `Ω`.
    rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet, ae_iff]
    refine measure_null_of_locally_null _ fun x hx ↦ ?_
    obtain ⟨hxΩ, -⟩ := Classical.not_imp.1 hx
    refine ⟨_ ∩ ball x (R x / 2),
      inter_mem_nhdsWithin _ (ball_mem_nhds x (half_pos (hR x hxΩ))), ?_⟩
    have hx' := (ae_restrict_iff' measurableSet_ball).1 (hhu x hxΩ)
    rw [ae_iff] at hx'
    refine measure_mono_null (fun y ⟨hy, hyB⟩ ↦ ?_) hx'
    obtain ⟨-, hyuv⟩ := Classical.not_imp.1 hy
    refine Classical.not_imp.2 ⟨ball_subset_ball (half_le_self (hR x hxΩ).le) hyB, ?_⟩
    rwa [← hv x hxΩ hyB]

/-- **Weyl's lemma for continuous functions.** A function continuous on the open set `Ω` is
harmonic on `Ω` if and only if it is weakly harmonic there: `∫ Δφ • u ∂μ = 0` for every test
function `φ ∈ 𝓓(Ω)`. -/
theorem harmonicOnNhd_iff_integral_laplacian_smul_eq_zero (hu : ContinuousOn u Ω) :
    HarmonicOnNhd u Ω ↔ ∀ φ : 𝓓(Ω, ℝ), ∫ x, Δ (φ : E → ℝ) x • u x ∂μ = 0 := by
  refine ⟨fun h φ ↦ h.integral_laplacian_smul_eq_zero φ, fun hΔ ↦ ?_⟩
  obtain ⟨v, hv, huv⟩ := exists_harmonicOnNhd_ae_eq_of_integral_laplacian_smul_eq_zero
    (hu.locallyIntegrableOn Ω.isOpen.measurableSet) hΔ
  have heq : EqOn u v Ω :=
    Measure.eqOn_open_of_ae_eq huv Ω.isOpen hu hv.contDiffOn.continuousOn
  exact fun x hx ↦ (harmonicAt_congr_nhds
    (eventually_of_mem (Ω.isOpen.mem_nhds hx) heq)).2 (hv x hx)

end TauCeti
