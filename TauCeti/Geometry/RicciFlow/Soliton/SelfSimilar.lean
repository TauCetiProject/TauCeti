/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Pullback
public import TauCeti.Geometry.Manifold.Riemannian.Scaling
public import TauCeti.Geometry.RicciFlow.Soliton.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.IntegralCurve
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Self-similar flows of gradient Ricci solitons

For a smooth potential satisfying `Ric + Hess f = c g` with complete gradient, construct the
metric obtained by pulling back along its gradient flow at time `-log (1 - 2 c t) / (2 c)`
and multiplying by `1 - 2 c t`. For `c = 0` use autonomous time `t`. On `2 c t < 1` the smooth
metric slices satisfy the pointwise Ricci flow equation, and their initial metric is `g`.
Conversely, satisfying the Ricci equation at time zero forces the soliton equation.

The flow is defined using the original metric outside the positive-scale interval. All time
PDE statements concern its interior; no joint smoothness of the metric family is asserted.

## Main results

* `SatisfiesGradientRicciSolitonEquation`: the native soliton equation;
  `satisfiesGradientRicciSolitonEquation_add_const_iff` shows invariance under potential shifts.
* `gradientSolitonDiffeomorph` and `gradientSolitonFlow`: the reparametrized gradient flow and
  the rescaled pullback metric.
* `ricciTensor_gradientSolitonFlow`: Ricci naturality for this construction.
* `hasDerivAt_inner_gradientSolitonFlow`: its pointwise Ricci flow equation.
* `hasDerivAt_inner_gradientSolitonFlow_zero_iff`: the converse at the initial time.

## References

* P. Topping, *Lectures on the Ricci flow*, §1.2.
* The public formalizations https://github.com/frenzymath/lean-eval-submissions and
  https://github.com/frenzymath/PoincareConjecture.
-/

public section

noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

namespace TauCeti

/-- The autonomous time of the soliton flow with metric scale `1 - 2 c t`. -/
def ricciSolitonTime (c t : ℝ) : ℝ :=
  if c = 0 then t else -Real.log (1 - 2 * c * t) / (2 * c)

@[simp]
theorem ricciSolitonTime_zero (c : ℝ) : ricciSolitonTime c 0 = 0 := by
  simp [ricciSolitonTime]

@[simp]
theorem ricciSolitonTime_zero_left (t : ℝ) : ricciSolitonTime 0 t = t := by
  simp [ricciSolitonTime]

/-- For nonzero soliton constant, the autonomous time is the logarithmic clock. -/
@[simp]
theorem ricciSolitonTime_of_ne_zero {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    ricciSolitonTime c t = -Real.log (1 - 2 * c * t) / (2 * c) := by
  simp [ricciSolitonTime, hc]

/-- The logarithmic soliton time has velocity equal to the inverse metric scale. -/
theorem hasDerivAt_ricciSolitonTime {c t : ℝ} (ht : 1 - 2 * c * t ≠ 0) :
    HasDerivAt (ricciSolitonTime c) (1 - 2 * c * t)⁻¹ t := by
  by_cases hc : c = 0
  · subst c
    have hfun : ricciSolitonTime 0 = id := funext ricciSolitonTime_zero_left
    simpa only [hfun, zero_mul, mul_zero, sub_zero, inv_one] using hasDerivAt_id t
  · have h := ((((hasDerivAt_id t).const_mul (2 * c)).const_sub 1).log ht).neg.div_const
      (2 * c)
    simp only [id_eq, mul_one] at h
    have hfun : ricciSolitonTime c = fun s ↦ -Real.log (1 - 2 * c * s) / (2 * c) := by
      funext s
      exact ricciSolitonTime_of_ne_zero hc s
    rw [hfun]
    convert h using 1
    field_simp [ht, hc]

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Express infinite manifold regularity at the successor smoothness order. -/
private local instance instIsManifoldInfinityAddOne : IsManifold I ((∞ : ℕ∞ω) + 1) M :=
  IsManifold.of_le (n := ∞) (by simp)

variable [BoundarylessManifold I M]

/-- The time-dependent diffeomorphism obtained from the complete gradient flow and soliton
time change. -/
def gradientSolitonDiffeomorph {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) (c t : ℝ) : M ≃ₘ^∞⟮I, I⟯ M :=
  globalFlowDiffeomorph hc (by simp)
    (contMDiff_mgradient (n := ∞) (by simpa using hf)) (ricciSolitonTime c t)

/-- As a function, the soliton diffeomorphism is the maximal gradient flow at soliton time. -/
theorem coe_gradientSolitonDiffeomorph {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) (c t : ℝ) :
    ⇑(gradientSolitonDiffeomorph hf hc c t) =
      flowOf (mgradient I f) (ricciSolitonTime c t) := by
  rw [gradientSolitonDiffeomorph, coe_globalFlowDiffeomorph, ← flowOf_eq_globalFlow]

/-- The inverse soliton diffeomorphism follows the gradient flow backwards in soliton time. -/
@[simp]
theorem gradientSolitonDiffeomorph_symm_apply {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : IsCompleteVectorField (mgradient I f))
    (c t : ℝ) (x : M) :
    (gradientSolitonDiffeomorph hf hc c t).symm x =
      flowOf (mgradient I f) (-ricciSolitonTime c t) x := by
  rw [gradientSolitonDiffeomorph, globalFlowDiffeomorph_symm_apply, ← flowOf_eq_globalFlow]

/-- The soliton diffeomorphism is the identity at the initial time. -/
@[simp]
theorem gradientSolitonDiffeomorph_zero {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) (c : ℝ) :
    gradientSolitonDiffeomorph hf hc c 0 = Diffeomorph.refl I M ∞ := by
  ext x
  simp [gradientSolitonDiffeomorph]

/-- Rescale the metric pulled back by its gradient flow on the positive-scale interval.
Outside that interval use the original metric. -/
def gradientSolitonFlow {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) (c t : ℝ) :
    ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) :=
  if ht : 2 * c * t < 1 then
    let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
      (IB := I) (n := ∞) (F := E)
    let Φ := gradientSolitonDiffeomorph hf hc c t
    (g.pullback Φ (by simpa using Φ.contMDiff)
      (fun x ↦ (Φ.isInvertible_mfderiv (by simp)).injective)).rescale
      (fun _ ↦ 1 - 2 * c * t) contMDiff_const (fun _ ↦ sub_pos.mpr ht)
  else ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E)

/-- When the scale is nonpositive, the soliton family uses the original metric. -/
@[simp]
theorem gradientSolitonFlow_of_one_le {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) {c t : ℝ} (ht : 1 ≤ 2 * c * t) :
    gradientSolitonFlow hf hc c t =
      ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E) := by
  simp [gradientSolitonFlow, not_lt.mpr ht]

/-- On the positive-scale interval, the flow is the actual rescaled gradient pullback. -/
theorem gradientSolitonFlow_inner {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) {c t : ℝ} (ht : 2 * c * t < 1)
    (x : M) (v w : TangentSpace I x) :
    (gradientSolitonFlow hf hc c t).inner x v w =
      (1 - 2 * c * t) * inner ℝ
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v)
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x w) := by
  simp only [gradientSolitonFlow, ht, ↓reduceDIte,
    ContMDiffRiemannianMetric.rescale_inner, ContMDiffRiemannianMetric.pullback_inner,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

/-- The self-similar family starts at the original smooth Riemannian metric. -/
@[simp]
theorem gradientSolitonFlow_zero {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) (c : ℝ) :
    gradientSolitonFlow hf hc c 0 =
      ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := I) (n := ∞) (F := E) := by
  ext x v w
  rw [gradientSolitonFlow_inner hf hc (by simp)]
  rw [gradientSolitonDiffeomorph_zero]
  simp only [Diffeomorph.coe_refl, mfderiv_id,
    mul_zero, sub_zero, one_mul,
    ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]
  rfl

/-- Constant metric rescaling and pullback transport the Ricci tensor of a soliton family
without introducing a scale factor. -/
theorem ricciTensor_gradientSolitonFlow {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hc : IsCompleteVectorField (mgradient I f)) {c t : ℝ} (ht : 2 * c * t < 1)
    (x : M) (v w : TangentSpace I x) :
    (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
      ⟨(gradientSolitonFlow hf hc c t).toRiemannianMetric⟩;
      (leviCivitaConnection I M).ricciTensor x v w) =
      (leviCivitaConnection I M).ricciTensor
        (gradientSolitonDiffeomorph hf hc c t x)
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v)
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x w) := by
  let r₀ : RiemannianBundle (fun y : M ↦ TangentSpace I y) := inferInstance
  let g₀ := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle
    (IB := I) (n := ∞) (F := E) (V := fun y : M ↦ TangentSpace I y)
  let Φ := gradientSolitonDiffeomorph hf hc c t
  have hΦ : ContMDiff I I (∞ + 1) Φ := by simpa using Φ.contMDiff
  have hΦinv : ∀ y, (mfderiv I I Φ y).IsInvertible := fun _ ↦
    Φ.isInvertible_mfderiv (by simp)
  let gp := g₀.pullback Φ hΦ (fun y ↦ (hΦinv y).injective)
  have hmetric : gradientSolitonFlow hf hc c t =
      gp.rescale (fun _ ↦ 1 - 2 * c * t) contMDiff_const (fun _ ↦ sub_pos.mpr ht) := by
    simp only [gradientSolitonFlow, ht, ↓reduceDIte, gp, g₀, Φ]
  rw [hmetric, ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_rescale_const
    gp (sub_pos.mpr ht)]
  have hbundle : (⟨g₀.toRiemannianMetric⟩ : RiemannianBundle
      (fun y : M ↦ TangentSpace I y)) = r₀ :=
    congrArg RiemannianBundle.mk
      (ContMDiffRiemannianMetric.toRiemannianMetric_ofIsContMDiffRiemannianBundle
        (IB := I) (n := ∞) (F := E))
  have hlocal := g₀.isLocalRiemannianIsometry_pullback_of_isInvertible hΦ hΦinv
  -- The source and target have the same carrier but different metrics, so supply both bundles.
  have hr := @IsLocalRiemannianIsometry.ricciTensor_mfderiv
    E _ _ _ H _ I M _ _ _ ⟨gp.toRiemannianMetric⟩ _
    E _ _ _ H _ I M _ _ _ ⟨g₀.toRiemannianMetric⟩ _ Φ _ _ hlocal x v w
  have hRic (r : RiemannianBundle (fun y : M ↦ TangentSpace I y))
      (heq : r = r₀)
      (hsm : letI := r; IsContMDiffRiemannianBundle I ∞ E
        (fun y : M ↦ TangentSpace I y)) :
      (letI := r; letI := hsm; (leviCivitaConnection I M).ricciTensor
        (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)) =
        (letI := r₀; (leviCivitaConnection I M).ricciTensor
          (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x w)) := by
    subst r
    rfl
  exact hr.symm.trans (hRic _ hbundle (by infer_instance))

private theorem hasDerivAt_inner_gradientSolitonFlow_self_hessian {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : IsCompleteVectorField (mgradient I f))
    {c t : ℝ} (ht : 2 * c * t < 1)
    (x : M) (v : TangentSpace I x) :
    HasDerivAt (fun s ↦ (gradientSolitonFlow hf hc c s).inner x v v)
      (2 * (hessian I f
        (gradientSolitonDiffeomorph hf hc c t x)
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v)
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v) - c * inner ℝ
          (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v)
          (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v))) t := by
  let τ := ricciSolitonTime c t
  have hX : CMDiff ∞ (T% (mgradient I f)) :=
    contMDiff_mgradient (n := ∞) (by simpa using hf)
  obtain ⟨γ, hγ0, hγ, hvel⟩ := exists_contMDiffAt_curveVelocity_eq (I := I)
    (n := 2) (by norm_num) x BoundarylessManifold.isInteriorPoint v (0 : ℝ)
  subst x
  let F (q s : ℝ) := flowOf (mgradient I f) s (γ q)
  have hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (0, τ) :=
    contMDiffAt_flowOf_comp (by norm_num) (hX.of_le (by simp))
      (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffAt
      (hγ.comp (0, τ) (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffAt)
      (hc.mem_flowDomain τ (γ 0))
  have hcurve : ∀ᶠ q in 𝓝 0, curveVelocity I (F q) τ = mgradient I f (F q τ) :=
    Eventually.of_forall fun q ↦ curveVelocity_flowOf (hX.of_le (by simp))
      (hc.mem_flowDomain τ (γ q))
  have hp := (isMetricCompatible_leviCivitaConnection (M := M) I)
    |>.hasDerivAt_inner_curveVelocity_self_of_integralCurve
      ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I)) hF
      (hX.mdifferentiableAt (by simp)) hcurve
  have hmap (s : ℝ) : curveVelocity I (fun q ↦ F q s) 0 =
      mfderiv I I (flowOf (mgradient I f) s) (γ 0) v := by
    have hs : MDifferentiableAt I I (flowOf (mgradient I f) s) (γ 0) :=
      (contMDiffAt_flowOf_comp (by simp) hX contMDiffAt_const contMDiffAt_id
        (hc.mem_flowDomain s (γ 0))).mdifferentiableAt (by simp)
    have hm := curveVelocityWithin_map hs uniqueDiffWithinAt_univ
      (hγ.mdifferentiableAt (by norm_num)).mdifferentiableWithinAt
    simp only [curveVelocityWithin_univ] at hm
    simpa only [F, Function.comp_def, hvel] using hm
  simp only [hmap, F, ← hessian_def] at hp
  have hcomp := hp.comp t (hasDerivAt_ricciSolitonTime (ne_of_gt (sub_pos.mpr ht)))
  have hmul := (((hasDerivAt_id t).const_mul (2 * c)).const_sub 1).mul hcomp
  have heq : ∀ᶠ s in 𝓝 t, (gradientSolitonFlow hf hc c s).inner (γ 0) v v =
      (1 - 2 * c * s) * inner ℝ
        (mfderiv I I (flowOf (mgradient I f) (ricciSolitonTime c s)) (γ 0) v)
        (mfderiv I I (flowOf (mgradient I f) (ricciSolitonTime c s)) (γ 0) v) := by
    filter_upwards [(isOpen_lt (by fun_prop : Continuous fun s : ℝ ↦ 2 * c * s)
      continuous_const).mem_nhds ht] with s hs
    rw [gradientSolitonFlow_inner hf hc hs, coe_gradientSolitonDiffeomorph]
  have hd := hmul.congr_of_eventuallyEq heq
  simp only [id_eq, mul_one, Function.comp_apply, τ] at hd
  convert hd using 1
  rw [coe_gradientSolitonDiffeomorph]
  have ha : 1 - 2 * c * t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  field_simp [ha]
  ring

private theorem hasDerivAt_inner_gradientSolitonFlow_hessian {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : IsCompleteVectorField (mgradient I f))
    {c t : ℝ} (ht : 2 * c * t < 1)
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt (fun s ↦ (gradientSolitonFlow hf hc c s).inner x v w)
      (2 * (hessian I f
        (gradientSolitonDiffeomorph hf hc c t x)
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v)
        (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x w) - c * inner ℝ
          (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v)
          (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x w))) t := by
  have hd := (((hasDerivAt_inner_gradientSolitonFlow_self_hessian hf hc ht x (v + w)).sub
    (hasDerivAt_inner_gradientSolitonFlow_self_hessian hf hc ht x v)).sub
    (hasDerivAt_inner_gradientSolitonFlow_self_hessian hf hc ht x w)).div_const 2
  simp only [Pi.sub_apply] at hd
  have hfun : (fun s ↦ (((gradientSolitonFlow hf hc c s).inner x (v + w) (v + w) -
      (gradientSolitonFlow hf hc c s).inner x v v) -
      (gradientSolitonFlow hf hc c s).inner x w w) / 2) =
      (fun s ↦ (gradientSolitonFlow hf hc c s).inner x v w) := by
    funext s
    simp only [map_add, add_apply, (gradientSolitonFlow hf hc c s).symm]
    ring
  rw [hfun] at hd
  convert hd using 1
  simp only [map_add, hessian_add_left, hessian_add_right, inner_add_left, inner_add_right]
  rw [hessian_symm _ ((hf.of_le (by simp)).contMDiffAt)
    (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x w)
    (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v), real_inner_comm]
  ring

/-- A smooth gradient Ricci soliton with complete gradient generates smooth metric slices
satisfying the pointwise Ricci flow equation on the positive-scale time interval. -/
theorem hasDerivAt_inner_gradientSolitonFlow {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : IsCompleteVectorField (mgradient I f))
    {c t : ℝ} (ht : 2 * c * t < 1)
    (hsol : SatisfiesGradientRicciSolitonEquation (I := I) f c)
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt (fun s ↦ (gradientSolitonFlow hf hc c s).inner x v w)
      (-2 * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
        ⟨(gradientSolitonFlow hf hc c t).toRiemannianMetric⟩;
        (leviCivitaConnection I M).ricciTensor x v w)) t := by
  rw [ricciTensor_gradientSolitonFlow hf hc ht]
  have hd := hasDerivAt_inner_gradientSolitonFlow_hessian hf hc ht x v w
  convert hd using 1
  have hs := satisfiesGradientRicciSolitonEquation_iff.mp hsol
    (gradientSolitonDiffeomorph hf hc c t x)
    (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x v)
    (mfderiv I I (gradientSolitonDiffeomorph hf hc c t) x w)
  linarith

/-- The rescaled gradient pullback is a Ricci flow at its initial time exactly when the
original metric and potential satisfy the gradient Ricci soliton equation. -/
theorem hasDerivAt_inner_gradientSolitonFlow_zero_iff {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hc : IsCompleteVectorField (mgradient I f)) (c : ℝ) :
    (∀ (x : M) (v w : TangentSpace I x),
      HasDerivAt (fun s ↦ (gradientSolitonFlow hf hc c s).inner x v w)
        (-2 * (letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) :=
          ⟨(gradientSolitonFlow hf hc c 0).toRiemannianMetric⟩;
          (leviCivitaConnection I M).ricciTensor x v w)) 0) ↔
      SatisfiesGradientRicciSolitonEquation (I := I) f c := by
  rw [satisfiesGradientRicciSolitonEquation_iff]
  constructor
  · intro h x v w
    have hd := hasDerivAt_inner_gradientSolitonFlow_hessian hf hc (c := c) (t := 0)
      (by simp) x v w
    have hr := h x v w
    rw [ricciTensor_gradientSolitonFlow hf hc (by simp)] at hr
    have heq := hd.unique hr
    rw [gradientSolitonDiffeomorph_zero] at heq
    simp only [Diffeomorph.coe_refl, mfderiv_id, id_eq] at heq
    have heq' : 2 * (hessian I f x v w - c * inner ℝ v w) =
        -2 * (leviCivitaConnection I M).ricciTensor x v w := heq
    linarith only [heq']
  · intro h x v w
    exact hasDerivAt_inner_gradientSolitonFlow hf hc (by simp)
      (satisfiesGradientRicciSolitonEquation_iff.mpr h) x v w

end Manifold

end TauCeti
