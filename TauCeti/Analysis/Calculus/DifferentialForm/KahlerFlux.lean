/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.InnerProductSpace.AlternatingForm
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Hermitian
public import TauCeti.Geometry.Euclidean.Volume.Polar
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Const
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.Analysis.Calculus.RadialPrimitive
import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Geometry.Symplectic.Liouville.Linear
import TauCeti.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.Algebra.GroupWithZero.DivId
import TauCeti.Topology.Instances.Real.TSupport

/-!
# The flux of a closed two-form through spheres in a Hermitian four-space

Let `V` be an oriented real inner product space of dimension four with an orthogonal complex
structure `J` inducing the orientation, and Kähler form `ω(u, w) = ⟪J u, w⟫`. On the ball about a
point `x`, the form `ω` has the primitive `λ = (1 / 2) ι_{y - x} ω`, since `ω` has constant
coefficients. For a closed two-form `F`, Stokes's theorem on the ball `ball x σ` therefore reads

`∫_{ball x σ} ⟪ω, F⟫ = ∫_{ball x σ} ω ∧ F = ∫_{sphere x σ} λ ∧ F`,

and on the sphere `λ ∧ F` is `(σ / 2) B(w, w)` times the area element, where
`B(v, v) = F(v, J v)` is the Hermitian part of `F` and `w` is a unit vector orthogonal to `y - x`
and `J (y - x)`. Equivalently, since `⋆((y - x) ∧ J (y - x)) = ‖y - x‖² ω - (y - x) ∧ J (y - x)`
(`TauCeti.AlmostComplexStructure.hodgeStar_ιMulti_self_apply_self`),

`∫_{ball x σ} ⟪ω, F⟫ = (2 σ)⁻¹ ∫_{sphere x σ} (‖y - x‖² ⟪ω, F⟫ - B(y - x, y - x))`

for almost every `σ ∈ (0, R)` when `F` is a closed `C¹` two-form on `ball x R`
(`TauCeti.AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq`).
The sphere carries `3`-dimensional Hausdorff measure, as in
`TauCeti.Geometry.Euclidean.Volume.Polar`. In Taubes's analysis of the Seiberg–Witten equations
at large parameter, `F` is the curvature `i F_a` of the connection on the twisting line, the left
side is essentially the defect energy of the ball, and bounding `B(w, w)` on the sphere by the
defect density turns this identity into the monotonicity inequality for the defect energy
(`TauCeti.SeibergWitten.exists_ae_measure_closedBall_le_mul_deriv_add`).

The proof uses no divergence theorem on balls. For a radial cutoff `χ = H ‖· - x‖`, constant near
`x` and vanishing outside a closed ball inside `ball x R`, the form `F ∧ χ λ`, with `λ` the
Liouville primitive `ContinuousLinearMap.liouvilleFormCLM` of `ω` at `y - x`, is a compactly
supported `C¹` form on the whole space. Integration by parts for such forms
(`Module.Basis.integral_extDeriv_eq_zero`) gives

`∫ χ ⟪ω, F⟫ = -∫ (H'(‖y - x‖) / (2 ‖y - x‖)) (‖y - x‖² ⟪ω, F⟫ - B(y - x, y - x))`.

Taking `H(t) = ∫_t^∞ ϕ` for a test function `ϕ` on `(0, R)`
(`Continuous.exists_contDiff_deriv_eq_neg_of_tsupport_subset_Ioi`), the left side is
`∫ ϕ(s) ∫_{ball x s} ⟪ω, F⟫ ds` by slicing into balls
(`TauCeti.integral_setIntegral_Ioi_dist_smul_eq_integral_smul_setIntegral_ball`) and the right
side is `∫ ϕ(s) (2 s)⁻¹ ∫_{sphere x s} (…) ds` by polar integration
(`TauCeti.integral_eq_integral_Ioi_setIntegral_sphere`). The fundamental lemma of the calculus of
variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) then identifies the two
integrands for almost every `s ∈ (0, R)`.

The two-form `F` is a family of two-vectors, `C¹` on `ball x R`, whose form under
`TauCeti.alternatingFormEquiv` is closed there. The curvature `F = -db` of a `C²` connection form
`b`, which is how the statements of `TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent` present
`i F_a` in a chart, is such a form.

## Main results

* `TauCeti.AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq`: the ball-sphere
  identity for the `ω`-component of a closed two-form on a ball.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

open Module exteriorPower Filter MeasureTheory Metric Set ContinuousAlternatingMap
open scoped RealInnerProductSpace Topology

namespace TauCeti.AlmostComplexStructure

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The radial primitive of the Kähler form -/

/-- The one-form `y ↦ (H ‖y - x‖ / 2) ⟪J (y - x), ·⟫`, the radial cutoff `H ‖y - x‖` times the
Liouville primitive `λ = (1 / 2) ι_{y - x} ω` of the Kähler form. -/
private noncomputable def radialForm (J : AlmostComplexStructure V) (H : ℝ → ℝ) (x y : V) :
    V [⋀^Fin 1]→L[ℝ] ℝ :=
  H ‖y - x‖ • ContinuousLinearMap.liouvilleFormCLM
    ((innerSL ℝ).comp (LinearMap.toContinuousLinearMap J.toLinearMap)) (y - x)

private theorem radialForm_apply (J : AlmostComplexStructure V) (H : ℝ → ℝ) (x y : V)
    (w : Fin 1 → V) :
    J.radialForm H x y w = 2⁻¹ * (H ‖y - x‖ * ⟪J (y - x), w 0⟫) := by
  simp only [radialForm, ContinuousAlternatingMap.smul_apply,
    ContinuousLinearMap.liouvilleFormCLM_apply, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', innerSL_apply_apply, smul_eq_mul]
  ring

private theorem hasFDerivAt_radialForm_apply {J : AlmostComplexStructure V} {H : ℝ → ℝ}
    {x y : V} (hH : DifferentiableAt ℝ H ‖y - x‖) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0)
    (w : Fin 1 → V) :
    HasFDerivAt (fun z ↦ J.radialForm H x z w)
      ((deriv H ‖y - x‖ / ‖y - x‖ / 2 * ⟪J (y - x), w 0⟫) • innerSL ℝ (y - x) +
        (H ‖y - x‖ / 2) • ((innerSL ℝ (w 0)).comp
          (LinearMap.toContinuousLinearMap J.toLinearMap))) y := by
  simp only [radialForm_apply]
  set Jc : V →L[ℝ] V := LinearMap.toContinuousLinearMap J.toLinearMap
  have hJ : HasFDerivAt (fun z ↦ ⟪J (z - x), w 0⟫) ((innerSL ℝ (w 0)).comp Jc) y := by
    have := ((innerSL ℝ (w 0)).comp Jc).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
    convert this using 1
    · funext z; simp [Jc, real_inner_comm]
    · ext a; simp
  convert ((hH.hasFDerivAt_comp_norm_sub hH₀).mul hJ).const_mul 2⁻¹ using 1
  ext a
  simp [Jc, smul_eq_mul]
  ring

private theorem contDiff_radialForm {J : AlmostComplexStructure V} {H : ℝ → ℝ}
    {n : WithTop ℕ∞} (hH : ContDiff ℝ n H) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0) (x : V) :
    ContDiff ℝ n (J.radialForm H x) := by
  have hL : ContDiff ℝ n fun y ↦ ContinuousLinearMap.liouvilleFormCLM
      ((innerSL ℝ).comp (LinearMap.toContinuousLinearMap J.toLinearMap)) (y - x) :=
    (ContinuousLinearMap.liouvilleFormCLM ((innerSL ℝ).comp
      (LinearMap.toContinuousLinearMap J.toLinearMap))).contDiff.comp
        (contDiff_id.sub contDiff_const)
  exact (hH.comp_norm_sub hH₀ x).smul hL

private theorem extDeriv_radialForm {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0) (x y : V) :
    extDeriv (J.radialForm H x) y = alternatingFormEquiv V 2
      (H ‖y - x‖ • J.kahlerForm +
        (deriv H ‖y - x‖ / (2 * ‖y - x‖)) • ιMulti ℝ 2 ![y - x, J (y - x)]) := by
  have hd : DifferentiableAt ℝ H ‖y - x‖ := hH.differentiable one_ne_zero _
  ext v
  obtain ⟨a, b, rfl⟩ : ∃ a b, v = ![a, b] :=
    ⟨v 0, v 1, by ext i; fin_cases i <;> rfl⟩
  rw [extDeriv_apply_pair_of_differentiableAt
      ((contDiff_radialForm hH hH₀ x).differentiable one_ne_zero y),
    (hasFDerivAt_radialForm_apply hd hH₀ _).fderiv, (hasFDerivAt_radialForm_apply hd hH₀ _).fderiv,
    alternatingFormEquiv_apply]
  have hab : ⟪a, J b⟫ = -⟪J a, b⟫ := by rw [inner_apply_left hJ, neg_neg]
  simp only [inner_add_left, real_inner_smul_left, inner_kahlerForm_ιMulti hJ, inner_ιMulti_two,
    _root_.add_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, LinearMap.coe_toContinuousLinearMap', smul_eq_mul]
  rw [real_inner_comm b (J a), hab, real_inner_comm (J a) b]
  ring

/-! ### Cutting off at a closed ball inside `ball x R` -/

/-- A function continuous on `ball x R` is integrable once cut off outside a closed ball
`closedBall x M` with `M < R`. -/
private theorem integrable_indicator_closedBall [MeasurableSpace V] [BorelSpace V] {f : V → ℝ}
    {x : V} {R M : ℝ} (hf : ContinuousOn f (ball x R)) (hM : M < R) :
    Integrable ((closedBall x M).indicator f) :=
  (integrable_indicator_iff measurableSet_closedBall).2
    ((hf.mono (closedBall_subset_ball hM)).integrableOn_compact (isCompact_closedBall x M))

/-- Below the cutoff radius `M`, the ball integrals of the cutoff of `f` are those of `f`. -/
private theorem setIntegral_ball_indicator_closedBall [MeasurableSpace V] [BorelSpace V]
    (f : V → ℝ) (x : V) {σ M : ℝ} (hσ : σ ≤ M) :
    ∫ y in ball x σ, (closedBall x M).indicator f y = ∫ y in ball x σ, f y :=
  setIntegral_congr_fun measurableSet_ball fun _ hy ↦
    indicator_of_mem (ball_subset_closedBall.trans (closedBall_subset_closedBall hσ) hy) f

/-! ### Integration by parts and the flux identity -/

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)

include h₀ h₂ hkl he in
/-- **Integration by parts against a radial cutoff.** For a closed `C¹` two-form `F` on
`ball x R` and a `C¹` radial cutoff `χ = H ‖· - x‖` constant near `x` and vanishing outside
`closedBall x R'`, `R' < R`,
`∫ χ ⟪ω, F⟫ = -∫ (H' / (2 ‖y - x‖)) (‖y - x‖² ⟪ω, F⟫ - F(y - x, J (y - x)))`:
the primitive `λ = ι_{y - x} ω / 2` of `ω` moves the derivative onto `χ`. -/
private theorem integral_inner_kahlerForm_add_eq_zero [MeasurableSpace V] [BorelSpace V]
    {F : V → ⋀[ℝ]^2 V} {x : V} {R : ℝ} (hF : ContDiffOn ℝ 1 F (ball x R))
    (hdF : ∀ y ∈ ball x R, extDeriv (fun z ↦ alternatingFormEquiv V 2 (F z)) y = 0)
    {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0) {R' : ℝ} (hR' : R' < R)
    (hHR : ∀ t, R' ≤ t → H t = 0) :
    ∫ y, (H ‖y - x‖ * ⟪J.kahlerForm, F y⟫ + deriv H ‖y - x‖ / (2 * ‖y - x‖) *
      (‖y - x‖ ^ 2 * ⟪J.kahlerForm, F y⟫ - J.hermitianForm (F y) (y - x) (y - x))) = 0 := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  set φ : V → V [⋀^Fin 2]→L[ℝ] ℝ := fun z ↦ alternatingFormEquiv V 2 (F z)
  have hφ : ContDiffOn ℝ 1 φ (ball x R) :=
    (alternatingFormEquiv V 2).toContinuousLinearEquiv.contDiff.comp_contDiffOn hF
  have hrf := contDiff_radialForm (J := J) hH hH₀ x
  -- Beyond `R'` the cutoff vanishes on a neighbourhood, so `F` matters only on `ball x R`.
  have hfar (y : V) (hy : R' < ‖y - x‖) : ∀ᶠ z in 𝓝 y, R' < ‖z - x‖ :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hy
  have hzero (z : V) (hz : R' < ‖z - x‖) : J.radialForm H x z = 0 := by
    simp [radialForm, hHR _ hz.le]
  have hout (y : V) (hy : y ∉ ball x R) : R' < ‖y - x‖ := by
    rw [mem_ball, dist_eq_norm, not_lt] at hy; exact hR'.trans_le hy
  have hwedge0 (y : V) (hy : R' < ‖y - x‖) :
      (fun z ↦ wedge (φ z) (J.radialForm H x z)) =ᶠ[𝓝 y] 0 :=
    (hfar y hy).mono fun z hz ↦ by simp [hzero z hz, wedge_def]
  have hc : HasCompactSupport (J.radialForm H x) :=
    HasCompactSupport.intro (isCompact_closedBall x R') fun y hy ↦
      hzero y (by rwa [mem_closedBall, dist_eq_norm, not_le] at hy)
  have hψ : ContDiff ℝ 1 fun y ↦ wedge (φ y) (J.radialForm H x y) := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ ball x R
    · simpa only [wedge_def] using contDiffAt_const.pairedWedge
        (hφ.contDiffAt (isOpen_ball.mem_nhds hy)) hrf.contDiffAt
    · exact (contDiffAt_const (c := (0 : V [⋀^Fin 3]→L[ℝ] ℝ))).congr_of_eventuallyEq
        (hwedge0 y (hout y hy))
  obtain ⟨-, h⟩ := e.toBasis.integral_extDeriv_eq_zero hψ (hc.wedge_left (φ := φ))
  rw [e.addHaar_eq_volume] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  by_cases hy : y ∈ ball x R
  · have hL := extDeriv_pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
      ((hφ.differentiableOn one_ne_zero).differentiableAt (isOpen_ball.mem_nhds hy))
      ((hrf.differentiable one_ne_zero) y) e.toBasis
    simp only [← wedge_def] at hL
    refine Eq.trans ?_ hL.symm
    rw [hdF y hy]
    simp only [wedge_def, pairedWedge_zero_left]
    simp only [← wedge_def, extDeriv_radialForm hJ hH hH₀ x y]
    have hsymm (z : ⋀[ℝ]^2 V) : (o.hodgeStar hkl).symm z = o.hodgeStar hkl z := by
      rw [LinearEquiv.symm_apply_eq, o.hodgeStar_hodgeStar_of_even even_two]
    rw [o.alternatingFormEquiv_wedge_alternatingFormEquiv_apply hkl, hsymm]
    have hvol : o.volumeForm ((⇑e.toBasis ∘ Fin.cast (by omega)) ∘
        ⇑(finCongr (hkl.trans (Fact.out : finrank ℝ V = 4)).symm)) = 1 := by
      rw [o.volumeForm_robust e he]
      exact e.toBasis.det_self
    rw [hvol, map_add, map_smul, map_smul, hodgeStar_kahlerForm h₀ h₂ hkl he,
      hodgeStar_ιMulti_self_apply_self h₀ h₂ hkl he]
    simp only [inner_add_right, inner_smul_right, inner_sub_right, real_inner_comm (F y),
      hermitianForm_apply_self, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_one,
      zero_add]
    rw [real_inner_comm]
    ring
  · -- Outside `ball x R` both the cutoff and its derivative vanish, and so does the form.
    have hyR := hout y hy
    have hH0 : H =ᶠ[𝓝 ‖y - x‖] fun _ ↦ 0 :=
      (eventually_gt_nhds hyR).mono fun t ht ↦ hHR t ht.le
    have hd : extDeriv (fun y ↦ wedge (φ y) (J.radialForm H x y)) y = 0 := by
      rw [Filter.EventuallyEq.extDeriv_eq (ω₂ := fun _ ↦ 0) (hwedge0 y hyR),
        ContinuousAlternatingMap.extDeriv_const]
      rfl
    rw [hd, hHR _ hyR.le, hH0.deriv_eq, deriv_const]
    simp

include h₀ h₂ hkl he in
/-- **The flux identity tested against a test function.** For a closed `C¹` two-form `F` on
`ball x R` and a test function `ϕ` supported in `(0, R)`, the difference between the ball
integrals of `⟪ω, F⟫` and `(2 σ)⁻¹` times the sphere integrals of the radial Hermitian integrand
integrates to zero against `ϕ`. -/
private theorem integral_smul_setIntegral_ball_sub_eq_zero [MeasurableSpace V] [BorelSpace V]
    {F : V → ⋀[ℝ]^2 V} {x : V} {R : ℝ} (hF : ContDiffOn ℝ 1 F (ball x R))
    (hdF : ∀ y ∈ ball x R, extDeriv (fun z ↦ alternatingFormEquiv V 2 (F z)) y = 0)
    {ϕ : ℝ → ℝ} (hϕ : ContDiff ℝ (⊤ : ℕ∞) ϕ) (hc : HasCompactSupport ϕ)
    (hs : tsupport ϕ ⊆ Ioo 0 R) :
    ∫ σ, ϕ σ • ((∫ y in ball x σ, ⟪J.kahlerForm, F y⟫) - (2 * σ)⁻¹ *
      ∫ y in sphere x σ, (‖y - x‖ ^ 2 * ⟪J.kahlerForm, F y⟫ -
        J.hermitianForm (F y) (y - x) (y - x)) ∂μHE[finrank ℝ V - 1]) = 0 := by
  set g : V → ℝ := fun y ↦ ⟪J.kahlerForm, F y⟫ with hgdef
  set Q : V → ℝ := fun y ↦ ‖y - x‖ ^ 2 * g y - J.hermitianForm (F y) (y - x) (y - x) with hQdef
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  rcases le_or_gt R 0 with hR | hR
  · have h0 (σ : ℝ) : ϕ σ = 0 := image_eq_zero_of_notMem_tsupport fun h ↦
      not_lt.2 hR ((hs h).1.trans (hs h).2)
    simp [h0]
  -- `ϕ` lives in `(ε, R')` with `0 < ε` and `R' < R`; its tail integral `H` is the cutoff.
  obtain ⟨R', -, hR'R, hsR'⟩ := exists_lt_tsupport_subset_Ioo hR hs
  have hϕc := hϕ.continuous
  have hsI : tsupport ϕ ⊆ Ioi 0 := hsR'.trans Ioo_subset_Ioi_self
  obtain ⟨ε, hε, -, hlow, -⟩ := hc.exists_pos_forall_eq_zero_of_tsupport_subset_Ioi hsI
  have hhigh (t : ℝ) (ht : R' ≤ t) : ϕ t = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ not_lt.2 ht (hsR' h).2
  obtain ⟨H, hH1, hHd, hH0, -, hHI⟩ :=
    hϕc.exists_contDiff_deriv_eq_neg_of_tsupport_subset_Ioi hc hsI
  have hHR (t : ℝ) (ht : R' ≤ t) : H t = 0 := by
    rw [hHI]
    exact setIntegral_eq_zero_of_forall_eq_zero fun s hs ↦ hhigh s (ht.trans (le_of_lt hs))
  have hstar := integral_inner_kahlerForm_add_eq_zero h₀ h₂ hkl he hF hdF hH1 hH0 hR'R hHR
  simp only [hHd] at hstar
  -- `g` and `Q` are continuous on `ball x R`, which contains `closedBall x R'`.
  have hsub : closedBall x R' ⊆ ball x R := closedBall_subset_ball hR'R
  have hsx : Continuous fun y : V ↦ y - x := continuous_id.sub continuous_const
  have hFc : ContinuousOn F (ball x R) := hF.continuousOn
  have hg : ContinuousOn g (ball x R) := by fun_prop
  have hQ : ContinuousOn Q (ball x R) := by fun_prop
  have hgR := integrable_indicator_closedBall hg hR'R
  -- The weight `t ↦ ϕ t / (2 t)` is continuous and vanishes beyond `R'`.
  have hk : Continuous fun t ↦ ϕ t / (2 * t) := by
    simp_rw [div_mul_eq_div_div_swap]
    exact (hϕc.div_id_of_eventuallyEq_zero
      ((eventually_lt_nhds hε).mono fun t ht ↦ hlow t ht)).div_const 2
  have hI₁ : Integrable fun y ↦ H ‖y - x‖ * g y :=
    ((((hH1.continuous.comp hsx.norm).continuousOn).mul (hg.mono hsub)).integrableOn_compact
      (isCompact_closedBall x R')).integrable_of_forall_notMem_eq_zero fun y hy ↦ by
        rw [mem_closedBall, dist_eq_norm, not_le] at hy
        simp [hHR _ hy.le]
  have hI₂ : Integrable fun y ↦ ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y :=
    ((((hk.comp hsx.norm).continuousOn).mul (hQ.mono hsub)).integrableOn_compact
      (isCompact_closedBall x R')).integrable_of_forall_notMem_eq_zero fun y hy ↦ by
        rw [mem_closedBall, dist_eq_norm, not_le] at hy
        simp [hhigh _ hy.le]
  -- The identity `∫ H(‖y - x‖) g = ∫ ϕ(‖y - x‖) / (2 ‖y - x‖) Q` from integration by parts.
  have hIBP : ∫ y, H ‖y - x‖ * g y = ∫ y, ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y := by
    have hfun : (fun y ↦ H ‖y - x‖ * ⟪J.kahlerForm, F y⟫ + -ϕ ‖y - x‖ / (2 * ‖y - x‖) *
        (‖y - x‖ ^ 2 * ⟪J.kahlerForm, F y⟫ - J.hermitianForm (F y) (y - x) (y - x))) =
        fun y ↦ H ‖y - x‖ * g y - ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y := by
      funext y
      simp only [hgdef, hQdef]
      ring
    rwa [hfun, integral_sub hI₁ hI₂, sub_eq_zero] at hstar
  -- Slicing the left side into balls and the right side into spheres.
  have hL : ∫ y, H ‖y - x‖ * g y = ∫ σ, ϕ σ * ∫ y in ball x σ, g y := by
    simpa only [hHI, dist_eq_norm, smul_eq_mul] using
      integral_setIntegral_Ioi_dist_smul_eq_integral_smul_setIntegral_ball x
        (hϕc.integrable_of_hasCompactSupport hc) hhigh
        (((hg.mono hsub).integrableOn_compact (isCompact_closedBall x R')).mono_set
          ball_subset_closedBall)
  have hT (r : ℝ) (_ : r ∈ Ioi 0) :
      ∫ y in sphere x r, ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y ∂μHE[finrank ℝ V - 1] =
        ϕ r * ((2 * r)⁻¹ * ∫ y in sphere x r, Q y ∂μHE[finrank ℝ V - 1]) := by
    rw [setIntegral_congr_fun isClosed_sphere.measurableSet
      (g := fun y ↦ ϕ r / (2 * r) * Q y) fun y hy ↦ by
        rw [mem_sphere, dist_eq_norm] at hy
        simp only [hy], integral_const_mul]
    ring
  have hϕ0 (r : ℝ) (hr : r ∉ Ioi 0) : ϕ r = 0 := hlow r ((not_lt.1 hr).trans_lt hε)
  have hTint : Integrable fun r ↦
      ϕ r * ((2 * r)⁻¹ * ∫ y in sphere x r, Q y ∂μHE[finrank ℝ V - 1]) :=
    ((integrableOn_Ioi_setIntegral_sphere x hI₂).congr_fun hT measurableSet_Ioi)
      |>.integrable_of_forall_notMem_eq_zero fun r hr ↦ by simp [hϕ0 r hr]
  have hR : ∫ y, ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y =
      ∫ σ, ϕ σ * ((2 * σ)⁻¹ * ∫ y in sphere x σ, Q y ∂μHE[finrank ℝ V - 1]) := by
    rw [integral_eq_integral_Ioi_setIntegral_sphere x hI₂,
      setIntegral_congr_fun measurableSet_Ioi hT,
      setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr ↦ by simp [hϕ0 r hr]]
  -- Below `R'` the ball integrals of `g` are those of its cutoff, which are continuous.
  have hGint : Integrable fun σ ↦ ϕ σ * ∫ y in ball x σ, g y := by
    refine ((hϕc.mul (hgR.continuous_setIntegral_ball x)).integrable_of_hasCompactSupport
      (hc.mul_right (f' := fun σ ↦ ∫ y in ball x σ, (closedBall x R').indicator g y))).congr
      (Eventually.of_forall fun σ ↦ ?_)
    rcases le_or_gt σ R' with hσ | hσ
    · exact congrArg (ϕ σ * ·) (setIntegral_ball_indicator_closedBall g x hσ)
    · simp [hhigh σ hσ.le]
  simp only [smul_eq_mul, mul_sub]
  rw [integral_sub hGint hTint, ← hL, ← hR, hIBP, sub_self]

include h₀ h₂ hkl he in
/-- **The flux of a closed two-form through spheres.** Let `F` be a two-form on `ball x R`, read
as a two-vector through `TauCeti.alternatingFormEquiv`, which is `C¹` and closed there, on an
oriented four-dimensional inner product space with a positively oriented unitary frame for `J`.
For almost every radius `σ ∈ (0, R)`, the integral of the `ω`-component of `F` over the ball
`ball x σ` is the flux

`∫_{ball x σ} ⟪ω, F⟫ = (2 σ)⁻¹ ∫_{sphere x σ} (‖y - x‖² ⟪ω, F y⟫ - F(y)(y - x, J (y - x)))`

through its boundary sphere, against `3`-dimensional Hausdorff measure. Here
`F(y)(u, J u) = B(u, u)` is the Hermitian part of `F`
(`TauCeti.AlmostComplexStructure.hermitianForm`).
The integrand on the sphere is `σ² B(w, w)` for a unit vector `w` orthogonal to `y - x` and
`J (y - x)`. -/
theorem ae_setIntegral_ball_inner_kahlerForm_eq [MeasurableSpace V] [BorelSpace V]
    {F : V → ⋀[ℝ]^2 V} {x : V} {R : ℝ} (hF : ContDiffOn ℝ 1 F (ball x R))
    (hdF : ∀ y ∈ ball x R, extDeriv (fun z ↦ alternatingFormEquiv V 2 (F z)) y = 0) :
    ∀ᵐ σ : ℝ, σ ∈ Ioo 0 R → ∫ y in ball x σ, ⟪J.kahlerForm, F y⟫ =
      (2 * σ)⁻¹ * ∫ y in sphere x σ, (‖y - x‖ ^ 2 * ⟪J.kahlerForm, F y⟫ -
        J.hermitianForm (F y) (y - x) (y - x)) ∂μHE[finrank ℝ V - 1] := by
  -- With `G(σ) = ∫_{ball x σ} ⟪ω, F⟫` and `S(σ) = ∫_{sphere x σ} Q`, `G - (2 σ)⁻¹ S` integrates
  -- to zero against every test function on `(0, R)` and is locally integrable there, so it
  -- vanishes almost everywhere on `(0, R)`.
  set g : V → ℝ := fun y ↦ ⟪J.kahlerForm, F y⟫
  set Q : V → ℝ := fun y ↦ ‖y - x‖ ^ 2 * g y - J.hermitianForm (F y) (y - x) (y - x)
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  have hFc : ContinuousOn F (ball x R) := hF.continuousOn
  have hg : ContinuousOn g (ball x R) := by fun_prop
  have hQ : ContinuousOn Q (ball x R) := by fun_prop
  have hloc : LocallyIntegrableOn (fun σ ↦ (∫ y in ball x σ, g y) -
      (2 * σ)⁻¹ * ∫ y in sphere x σ, Q y ∂μHE[finrank ℝ V - 1]) (Ioo 0 R) := by
    refine (locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed).2 fun K hK hKc ↦ ?_
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact integrableOn_empty
    -- On `K ⊆ (0, M)`, `M < R`, cut `g` and `Q` off outside `closedBall x M`.
    obtain ⟨m, hmK, hmax⟩ := hKc.exists_isGreatest hne
    obtain ⟨M, hmM, hMR⟩ := exists_between (hK hmK).2
    have hKM (r : ℝ) (hr : r ∈ K) : r < M := (hmax hr).trans_lt hmM
    refine IntegrableOn.sub ?_ ?_
    · refine (((integrable_indicator_closedBall hg hMR).continuous_setIntegral_ball
        x).continuousOn.integrableOn_compact hKc).congr_fun
        (fun r hr ↦ setIntegral_ball_indicator_closedBall g x (hKM r hr).le) hKc.measurableSet
    · refine (((integrableOn_Ioi_setIntegral_sphere x
        (integrable_indicator_closedBall hQ hMR)).mono_set
        fun r hr ↦ (hK hr).1).congr_fun (fun r hr ↦ setIntegral_congr_fun
          isClosed_sphere.measurableSet fun y hy ↦ indicator_of_mem ?_ Q)
          hKc.measurableSet).continuousOn_mul
        ((continuousOn_const.mul continuousOn_id).inv₀ fun r hr ↦
          mul_ne_zero two_ne_zero (ne_of_gt (hK hr).1)) hKc
      rw [mem_closedBall, mem_sphere.1 hy]
      exact (hKM r hr).le
  filter_upwards [isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    fun ϕ hϕ hc hs ↦ integral_smul_setIntegral_ball_sub_eq_zero h₀ h₂ hkl he hF hdF hϕ hc hs]
    with σ hσ hmem
  exact sub_eq_zero.1 (hσ hmem)

end TauCeti.AlmostComplexStructure
