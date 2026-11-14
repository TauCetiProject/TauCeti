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
import TauCeti.Analysis.Calculus.DifferentialForm.Integral
import TauCeti.Analysis.Calculus.DifferentialForm.Wedge
import TauCeti.Analysis.Calculus.RadialPrimitive
import TauCeti.Analysis.InnerProductSpace.HodgeStar.AlternatingForm
import TauCeti.Analysis.InnerProductSpace.NormPow
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
(`TauCeti.AlmostComplexStructure.hodgeStar_ιMulti_apply`),

`∫_{ball x σ} ⟪ω, F⟫ = (2 σ)⁻¹ ∫_{sphere x σ} (‖y - x‖² ⟪ω, F⟫ - B(y - x, y - x))`

for almost every `σ > 0` (`TauCeti.AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq`).
The sphere carries `3`-dimensional Hausdorff measure, as in
`TauCeti.Geometry.Euclidean.Volume.Polar`. In Taubes's analysis of the Seiberg–Witten equations
at large parameter, `F` is the curvature `i F_a` of the connection on the twisting line, the left
side is essentially the defect energy of the ball, and bounding `B(w, w)` on the sphere by the
defect density turns this identity into the monotonicity inequality for the defect energy
(`TauCeti.SeibergWitten.exists_ae_measure_closedBall_le_mul_deriv_add`).

The proof uses no divergence theorem on balls. For a radial cutoff `χ = H ‖· - x‖`, constant near
`x` and compactly supported, integration by parts for compactly supported forms
(`Module.Basis.integral_extDeriv_eq_zero`) applied to `F ∧ χ λ` gives

`∫ χ ⟪ω, F⟫ = -∫ (H'(‖y - x‖) / (2 ‖y - x‖)) (‖y - x‖² ⟪ω, F⟫ - B(y - x, y - x))`.

Taking `H(t) = ∫_t^∞ ϕ` for a test function `ϕ` on `(0, ∞)`
(`TauCeti.exists_contDiff_deriv_eq_neg_of_tsupport_subset_Ioi`), the left side is
`∫ ϕ(s) ∫_{ball x s} ⟪ω, F⟫ ds` by slicing into balls
(`TauCeti.integral_setIntegral_Ioi_norm_sub_mul_eq_integral_mul_setIntegral_ball`) and the right
side is `∫ ϕ(s) (2 s)⁻¹ ∫_{sphere x s} (…) ds` by polar integration
(`TauCeti.integral_eq_integral_Ioi_setIntegral_sphere`). The fundamental lemma of the calculus of
variations (`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`) then identifies the two
integrands for almost every `s`.

The two-form `F` is a `C¹` family of two-vectors whose form under `TauCeti.alternatingFormEquiv`
is closed. The curvature `F = -db` of a `C²` connection form `b`, which is how the statements of
`TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent` present `i F_a` in a chart, is such a form.

## Main results

* `TauCeti.AlmostComplexStructure.ae_setIntegral_ball_inner_kahlerForm_eq`: the ball-sphere
  identity for the `ω`-component of a closed two-form.
* `TauCeti.AlmostComplexStructure.continuous_hermitianForm_apply_sub_apply_sub`: continuity of
  the radial Hermitian integrand.

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
primitive `λ = (1 / 2) ι_{y - x} ω` of the Kähler form. -/
private noncomputable def radialForm (J : AlmostComplexStructure V) (H : ℝ → ℝ) (x y : V) :
    V [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)
    (innerSL ℝ ((H ‖y - x‖ / 2) • J (y - x)))

omit [FiniteDimensional ℝ V] in
private theorem radialForm_apply (J : AlmostComplexStructure V) (H : ℝ → ℝ) (x y : V)
    (w : Fin 1 → V) :
    J.radialForm H x y w = 2⁻¹ * (H ‖y - x‖ * ⟪J (y - x), w 0⟫) := by
  simp only [radialForm, ContinuousAlternatingMap.ofSubsingletonLIE_apply,
    ContinuousAlternatingMap.ofSubsingleton_apply_apply, innerSL_apply_apply, real_inner_smul_left]
  ring

private theorem hasFDerivAt_radialForm_apply {J : AlmostComplexStructure V} {H : ℝ → ℝ}
    (hH : Differentiable ℝ H) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0) (x y : V) (w : Fin 1 → V) :
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
  have hχ := hasFDerivAt_comp_norm_sub hH hH₀ x y
  convert (hχ.mul hJ).const_mul 2⁻¹ using 1
  ext a
  simp [Jc, smul_eq_mul]
  ring


private theorem contDiff_radialForm {J : AlmostComplexStructure V} {H : ℝ → ℝ} {n : ℕ∞}
    (hH : ContDiff ℝ n H) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0) (x : V) :
    ContDiff ℝ n (J.radialForm H x) := by
  have hχ : ContDiff ℝ n (fun z : V ↦ H ‖z - x‖) := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    rcases eq_or_ne y x with rfl | hyx
    · have ht : Tendsto (fun z ↦ ‖z - y‖) (𝓝 y) (𝓝 0) := by
        simpa using (((continuous_id.sub continuous_const).norm.tendsto y) :
          Tendsto (fun z : V ↦ ‖z - y‖) (𝓝 y) (𝓝 ‖y - y‖))
      exact contDiffAt_const.congr_of_eventuallyEq (ht.eventually hH₀)
    · exact hH.contDiffAt.comp y ((contDiffAt_norm ℝ (sub_ne_zero.2 hyx)).comp y
        (contDiffAt_id.sub contDiffAt_const))
  have hJ : ContDiff ℝ n (fun z : V ↦ J (z - x)) :=
    (LinearMap.toContinuousLinearMap J.toLinearMap).contDiff.comp
      (contDiff_id.sub contDiff_const)
  exact (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.comp
    ((innerSL ℝ).contDiff.comp ((hχ.div_const 2).smul hJ))

private theorem extDeriv_radialForm {J : AlmostComplexStructure V} (hJ : ∀ v w, ⟪J v, J w⟫ = ⟪v, w⟫)
    {H : ℝ → ℝ} (hH : ContDiff ℝ 1 H) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0) (x y : V) :
    extDeriv (J.radialForm H x) y = alternatingFormEquiv V 2
      (H ‖y - x‖ • J.kahlerForm +
        (deriv H ‖y - x‖ / (2 * ‖y - x‖)) • ιMulti ℝ 2 ![y - x, J (y - x)]) := by
  have hd : Differentiable ℝ H := hH.differentiable one_ne_zero
  ext v
  obtain ⟨a, b, rfl⟩ : ∃ a b, v = ![a, b] :=
    ⟨v 0, v 1, by ext i; fin_cases i <;> rfl⟩
  rw [extDeriv_apply ((contDiff_radialForm hH hH₀ x).differentiable one_ne_zero y),
    Fin.sum_univ_two, (hasFDerivAt_radialForm_apply hd hH₀ x y _).fderiv,
    (hasFDerivAt_radialForm_apply hd hH₀ x y _).fderiv, alternatingFormEquiv_apply]
  simp only [inner_add_left, real_inner_smul_left, inner_kahlerForm_ιMulti hJ, inner_ιMulti_two]
  have hr₁ : Fin.removeNth 1 ![a, b] 0 = a := rfl
  have hab : ⟪a, J b⟫ = -⟪J a, b⟫ := by rw [inner_apply_left hJ, neg_neg]
  simp only [Int.reduceNeg, Nat.reduceAdd, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    pow_zero, Nat.succ_eq_add_one, Fin.removeNth_zero, Fin.tail_vecCons,
    Matrix.cons_val_fin_one, map_sub, Matrix.cons_val_zero, _root_.add_apply, _root_.smul_apply,
    _root_.sub_apply, coe_innerSL_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    LinearMap.coe_toContinuousLinearMap', smul_add, one_smul, Nat.mod_succ, pow_one,
    Matrix.cons_val_one, neg_smul]
  rw [hr₁, real_inner_comm b, hab]
  simp only [inner_sub_right, real_inner_comm b, real_inner_comm a]
  ring

/-! ### Continuity of the integrands -/

/-- The Hermitian part of a continuous family of two-vectors, evaluated on the radial vector
`y - x`, is continuous in `y`. -/
theorem continuous_hermitianForm_apply_sub_apply_sub {J : AlmostComplexStructure V}
    {F : V → ⋀[ℝ]^2 V} (hF : Continuous F) (x : V) :
    Continuous fun y ↦ J.hermitianForm (F y) (y - x) (y - x) := by
  have hJc : Continuous fun y : V ↦ J (y - x) :=
    (LinearMap.toContinuousLinearMap J.toLinearMap).continuous.comp
      (continuous_id.sub continuous_const)
  simp only [hermitianForm_apply_self, ← alternatingFormEquiv_apply]
  exact ((alternatingFormEquiv V 2).toContinuousLinearEquiv.continuous.comp hF).eval
    (continuous_pi fun i ↦ by
      fin_cases i
      · exact continuous_id.sub continuous_const
      · exact hJc)

/-! ### Integration by parts and the flux identity -/

variable {e : OrthonormalBasis (Fin 4) ℝ V} {J : AlmostComplexStructure V}
  (h₀ : J (e 0) = e 1) (h₂ : J (e 2) = e 3)
  [Fact (finrank ℝ V = 4)] {o : Orientation ℝ V (Fin 4)} (hkl : 2 + 2 = finrank ℝ V)
  (he : e.toBasis.orientation = o)

include h₀ h₂ hkl he in
/-- **Integration by parts against a radial cutoff.** For a closed `C¹` two-form `F` and a `C¹`
radial cutoff `χ = H ‖· - x‖` constant near `x` and compactly supported,
`∫ χ ⟪ω, F⟫ = -∫ (H' / (2 ‖y - x‖)) (‖y - x‖² ⟪ω, F⟫ - F(y - x, J (y - x)))`:
the primitive `λ = ι_{y - x} ω / 2` of `ω` moves the derivative onto `χ`. -/
private theorem integral_inner_kahlerForm_add_eq_zero [MeasurableSpace V] [BorelSpace V]
    {F : V → ⋀[ℝ]^2 V} (hF : ContDiff ℝ 1 F)
    (hdF : ∀ y, extDeriv (fun z ↦ alternatingFormEquiv V 2 (F z)) y = 0) {H : ℝ → ℝ}
    (hH : ContDiff ℝ 1 H) (hH₀ : ∀ᶠ t in 𝓝 0, H t = H 0) {R : ℝ} (hHR : ∀ t, R ≤ t → H t = 0)
    (x : V) :
    ∫ y, (H ‖y - x‖ * ⟪J.kahlerForm, F y⟫ + deriv H ‖y - x‖ / (2 * ‖y - x‖) *
      (‖y - x‖ ^ 2 * ⟪J.kahlerForm, F y⟫ - J.hermitianForm (F y) (y - x) (y - x))) = 0 := by
  have hJ := inner_apply_apply_of_orthonormalBasis h₀ h₂
  have hφ : ContDiff ℝ 1 fun z ↦ alternatingFormEquiv V 2 (F z) :=
    (alternatingFormEquiv V 2).toContinuousLinearEquiv.contDiff.comp hF
  have hrf := contDiff_radialForm (J := J) hH hH₀ x
  have hc : HasCompactSupport (J.radialForm H x) := by
    refine HasCompactSupport.intro (isCompact_closedBall x R) fun y hy ↦ ?_
    have hR : R ≤ ‖y - x‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hy; exact hy.le
    simp [radialForm, hHR _ hR]
    rfl
  obtain ⟨-, h⟩ := e.toBasis.integral_extDeriv_eq_zero (hφ.wedge hrf)
    (hc.wedge_left (φ := fun z ↦ alternatingFormEquiv V 2 (F z)))
  rw [e.addHaar_eq_volume] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  have hL := extDeriv_pairedWedge (ContinuousLinearMap.mul ℝ ℝ)
    ((hφ.differentiable one_ne_zero) y) ((hrf.differentiable one_ne_zero) y) e.toBasis
  simp only [← wedge_def] at hL
  refine Eq.trans ?_ hL.symm
  rw [hdF y]
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
    hodgeStar_ιMulti_apply h₀ h₂ hkl he]
  simp only [inner_add_right, inner_smul_right, inner_sub_right, real_inner_comm (F y),
    hermitianForm_apply_self, ContinuousAlternatingMap.coe_zero, Pi.zero_apply, mul_one, zero_add]
  rw [real_inner_comm]
  ring

include h₀ h₂ hkl he in
/-- **The flux of a closed two-form through spheres.** Let `F` be a closed `C¹` two-form, read as
a two-vector through `TauCeti.alternatingFormEquiv`, on an oriented four-dimensional inner product
space with a positively oriented unitary frame for `J`. For almost every radius `σ > 0`, the
integral of the `ω`-component of `F` over the ball `ball x σ` is the flux

`∫_{ball x σ} ⟪ω, F⟫ = (2 σ)⁻¹ ∫_{sphere x σ} (‖y - x‖² ⟪ω, F y⟫ - F(y)(y - x, J (y - x)))`

through its boundary sphere, against `3`-dimensional Hausdorff measure. Here
`F(y)(u, J u) = B(u, u)` is the Hermitian part of `F`
(`TauCeti.AlmostComplexStructure.hermitianForm`).
The integrand on the sphere is `σ² B(w, w)` for a unit vector `w` orthogonal to `y - x` and
`J (y - x)`. -/
theorem ae_setIntegral_ball_inner_kahlerForm_eq [MeasurableSpace V] [BorelSpace V]
    {F : V → ⋀[ℝ]^2 V} (hF : ContDiff ℝ 1 F)
    (hdF : ∀ y, extDeriv (fun z ↦ alternatingFormEquiv V 2 (F z)) y = 0) (x : V) :
    ∀ᵐ σ : ℝ, 0 < σ → ∫ y in ball x σ, ⟪J.kahlerForm, F y⟫ =
      (2 * σ)⁻¹ * ∫ y in sphere x σ, (‖y - x‖ ^ 2 * ⟪J.kahlerForm, F y⟫ -
        J.hermitianForm (F y) (y - x) (y - x)) ∂μHE[finrank ℝ V - 1] := by
  -- With `G(σ) = ∫_{ball x σ} ⟪ω, F⟫` and `S(σ) = ∫_{sphere x σ} Q`, integration by parts
  -- against the radial cutoff `H(‖y - x‖)`, `H(t) = ∫_t^∞ ϕ`, shows `∫ ϕ (G - (2 σ)⁻¹ S) = 0`
  -- for every test function `ϕ` on `(0, ∞)`; `G - (2 σ)⁻¹ S` is locally integrable there, so it
  -- vanishes almost everywhere.
  have hFc : Continuous F := hF.continuous
  set g : V → ℝ := fun y ↦ ⟪J.kahlerForm, F y⟫ with hgdef
  set Q : V → ℝ := fun y ↦ ‖y - x‖ ^ 2 * g y - J.hermitianForm (F y) (y - x) (y - x) with hQdef
  have hg : Continuous g := continuous_const.inner hFc
  have hQ : Continuous Q :=
    (((continuous_id.sub continuous_const).norm.pow 2).mul hg).sub
      (continuous_hermitianForm_apply_sub_apply_sub hFc x)
  set G : ℝ → ℝ := fun σ ↦ ∫ y in ball x σ, g y with hGdef
  set S : ℝ → ℝ := fun σ ↦ ∫ y in sphere x σ, Q y ∂μHE[finrank ℝ V - 1]
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  have hgR (R : ℝ) : IntegrableOn g (ball x R) :=
    (hg.continuousOn.integrableOn_compact (isCompact_closedBall x R)).mono_set
      ball_subset_closedBall
  -- The ball integrals `G` are fibre integrals over `V × ℝ`, hence measurable in the radius.
  have hGm : StronglyMeasurable G := by
    have hS : MeasurableSet {p : V × ℝ | ‖p.1 - x‖ < p.2} :=
      (isOpen_lt (continuous_fst.sub continuous_const).norm continuous_snd).measurableSet
    have h := StronglyMeasurable.integral_prod_left' (μ := (volume : Measure V))
      ((hg.comp continuous_fst).stronglyMeasurable.indicator hS)
    convert h using 1
    funext σ
    simp only [hGdef]
    rw [← integral_indicator measurableSet_ball]
    congr 1
    funext y
    simp only [indicator, mem_ball, dist_eq_norm, mem_ofPred_eq, Function.comp_apply]
  have hGb (R σ : ℝ) (hσ : σ ≤ R) : ‖G σ‖ ≤ ∫ y in ball x R, ‖g y‖ :=
    (norm_integral_le_integral_norm _).trans (setIntegral_mono_set (hgR R).norm
      (Eventually.of_forall fun _ ↦ norm_nonneg _) (ball_subset_ball hσ).eventuallySubset)
  -- On `(0, M)` the sphere integrals `S` are those of `Q` cut off outside `ball x M`.
  have hSM (M : ℝ) : IntegrableOn S (Ioo 0 M) := by
    have hf : Integrable ((ball x M).indicator Q) := (integrable_indicator_iff measurableSet_ball).2
      ((hQ.continuousOn.integrableOn_compact (isCompact_closedBall x M)).mono_set
        ball_subset_closedBall)
    refine ((integrableOn_Ioi_setIntegral_sphere x hf).mono_set Ioo_subset_Ioi_self).congr_fun
      (fun r hr ↦ setIntegral_congr_fun isClosed_sphere.measurableSet fun y hy ↦ ?_)
      measurableSet_Ioo
    refine indicator_of_mem ?_ Q
    rw [mem_sphere] at hy
    rw [mem_ball, hy]
    exact hr.2
  have key (ϕ : ℝ → ℝ) (hϕ : ContDiff ℝ (⊤ : ℕ∞) ϕ) (hc : HasCompactSupport ϕ)
      (hs : tsupport ϕ ⊆ Ioi 0) :
      ∫ σ, ϕ σ • (G σ - (2 * σ)⁻¹ * S σ) = 0 := by
    obtain ⟨ε, hε, R, hlow, hhigh⟩ := hc.exists_pos_forall_eq_zero_of_tsupport_subset_Ioi hs
    obtain ⟨H, hH1, hHd, hH0, ⟨R', hHR⟩, hHI⟩ :=
      exists_contDiff_deriv_eq_neg_of_tsupport_subset_Ioi hϕ.continuous hc hs
    have hstar := integral_inner_kahlerForm_add_eq_zero h₀ h₂ hkl he hF hdF hH1 hH0 hHR x
    simp only [hHd] at hstar
    -- The weight `t ↦ ϕ t / (2 t)` is continuous and vanishes beyond `R`.
    have hk : Continuous fun t ↦ ϕ t / (2 * t) := by
      simp_rw [div_mul_eq_div_div_swap]
      exact (hϕ.continuous.div_id_of_eventuallyEq_zero
        ((eventually_lt_nhds hε).mono fun t ht ↦ hlow t ht)).div_const 2
    have hI₁ : Integrable fun y ↦ H ‖y - x‖ * g y := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hH1.continuous.comp (continuous_id.sub continuous_const).norm).mul hg) ?_
      refine HasCompactSupport.intro (isCompact_closedBall x R') fun y hy ↦ ?_
      rw [mem_closedBall, dist_eq_norm, not_le] at hy
      simp [hHR _ hy.le]
    have hI₂ : Integrable fun y ↦ ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y := by
      refine Continuous.integrable_of_hasCompactSupport
        ((hk.comp (continuous_id.sub continuous_const).norm).mul hQ) ?_
      refine HasCompactSupport.intro (isCompact_closedBall x R) fun y hy ↦ ?_
      rw [mem_closedBall, dist_eq_norm, not_le] at hy
      simp [hhigh _ hy.le]
    -- The identity `∫ H(‖y - x‖) g = ∫ ϕ(‖y - x‖) / (2 ‖y - x‖) Q` from integration by parts.
    have hIBP : ∫ y, H ‖y - x‖ * g y = ∫ y, ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y := by
      have h := hstar
      have hfun : (fun y ↦ H ‖y - x‖ * ⟪J.kahlerForm, F y⟫ + -ϕ ‖y - x‖ / (2 * ‖y - x‖) *
          (‖y - x‖ ^ 2 * ⟪J.kahlerForm, F y⟫ - J.hermitianForm (F y) (y - x) (y - x))) =
          fun y ↦ H ‖y - x‖ * g y - ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y := by
        funext y
        simp only [hgdef, hQdef]
        ring
      rw [hfun, integral_sub hI₁ hI₂, sub_eq_zero] at h
      exact h
    -- Slicing the left side into balls and the right side into spheres.
    have hL : ∫ y, H ‖y - x‖ * g y = ∫ σ, ϕ σ * G σ := by
      simp only [hHI]
      exact integral_setIntegral_Ioi_norm_sub_mul_eq_integral_mul_setIntegral_ball x
        (hϕ.continuous.integrable_of_hasCompactSupport hc) hhigh
        (hgR R)
    have hT (r : ℝ) (_ : r ∈ Ioi 0) :
        ∫ y in sphere x r, ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y ∂μHE[finrank ℝ V - 1] =
          ϕ r * ((2 * r)⁻¹ * S r) := by
      rw [setIntegral_congr_fun isClosed_sphere.measurableSet
        (g := fun y ↦ ϕ r / (2 * r) * Q y) fun y hy ↦ by
          rw [mem_sphere, dist_eq_norm] at hy
          simp only [hy], integral_const_mul]
      ring
    have hϕ0 (r : ℝ) (hr : r ∉ Ioi 0) : ϕ r = 0 := hlow r ((not_lt.1 hr).trans_lt hε)
    have hTint : Integrable fun r ↦ ϕ r * ((2 * r)⁻¹ * S r) :=
      ((integrableOn_Ioi_setIntegral_sphere x hI₂).congr_fun hT measurableSet_Ioi)
        |>.integrable_of_forall_notMem_eq_zero fun r hr ↦ by simp [hϕ0 r hr]
    have hR : ∫ y, ϕ ‖y - x‖ / (2 * ‖y - x‖) * Q y = ∫ σ, ϕ σ * ((2 * σ)⁻¹ * S σ) := by
      rw [integral_eq_integral_Ioi_setIntegral_sphere x hI₂,
        setIntegral_congr_fun measurableSet_Ioi hT,
        setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr ↦ by simp [hϕ0 r hr]]
    have hGint : Integrable fun σ ↦ ϕ σ * G σ := by
      refine ((hϕ.continuous.integrable_of_hasCompactSupport hc).norm.const_mul
        (∫ y in ball x R, ‖g y‖)).mono' (hϕ.continuous.aestronglyMeasurable.mul
          hGm.aestronglyMeasurable) (Eventually.of_forall fun σ ↦ ?_)
      rcases le_or_gt R σ with hσ | hσ
      · simp [hhigh σ hσ]
      · rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hGb R σ hσ.le) (norm_nonneg _)
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub hGint hTint, ← hL, ← hR, hIBP, sub_self]
  have hloc : LocallyIntegrableOn (fun σ ↦ G σ - (2 * σ)⁻¹ * S σ) (Ioi 0) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun K hK hKc ↦ ?_
    obtain ⟨M, hM⟩ := hKc.bddAbove
    have hKM : K ⊆ Ioo 0 (M + 1) := fun r hr ↦ ⟨hK hr, (hM hr).trans_lt (lt_add_one M)⟩
    refine IntegrableOn.sub ?_ ?_
    · refine Measure.integrableOn_of_bounded (M := ∫ y in ball x (M + 1), ‖g y‖)
        hKc.measure_lt_top.ne hGm.aestronglyMeasurable ?_
      exact (ae_restrict_iff' hKc.measurableSet).2 (Eventually.of_forall fun r hr ↦
        hGb (M + 1) r (hKM hr).2.le)
    · exact ((hSM (M + 1)).mono_set hKM).continuousOn_mul
        ((continuousOn_const.mul continuousOn_id).inv₀ fun r hr ↦
          mul_ne_zero two_ne_zero (ne_of_gt (hK hr))) hKc
  filter_upwards [isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc key] with σ hσ hpos
  exact sub_eq_zero.1 (hσ hpos)

end TauCeti.AlmostComplexStructure
