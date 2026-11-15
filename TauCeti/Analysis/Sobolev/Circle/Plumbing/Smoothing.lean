/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.Plumbing.Basic
import TauCeti.Analysis.Analytic.Inverse
import TauCeti.Analysis.Analytic.ConstantOrder.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The smoothing coordinate of a nonlinear neck map

For logarithmic neck data `p(a,t) = (F,G)`, the target smoothing coordinate is
`b = a exp(F₀ + G₀)`. Even when the data vary with `a`, this is a holomorphic local change
of the smoothing coordinate at `a = 0`, retaining the additional parameter `t`. Its normal
derivative is nonzero, rather than tending to zero with `a`.

The smoothing-coordinate change commutes with ambient neck evaluation, where the argument of
`p` is `(xy,t)`. Local injectivity of this base change then identifies the source equation
`xy = s(t)` with the target equation `XY = b(s(t),t)` near the node, for every holomorphic `s`
vanishing at the central parameter. In particular no nonzero derivative of `s` is required.
For holomorphic `s`, Hadamard division also factors the difference `b(a,t) - b(s(t),t)` as
`(a - s(t)) u(a,t)`, with `u` holomorphic and nonzero at the node. The quotient-sheaf comparison
and global Hardy matching are separate statements.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §§10–12.
-/

public noncomputable section

open Complex Filter Topology

namespace TauCeti.CircleSobolev

variable {s : ℝ} {A : Type*}

/-- The target smoothing coordinate of the neck map, together with the unchanged parameter.
The logarithmic data are evaluated at the source smoothing coordinate. -/
def neckSmoothingMap (p : ℂ × A → CircleSobolev s ℂ × CircleSobolev s ℂ)
    (w : ℂ × A) : ℂ × A :=
  (w.1 * exp ((p w).1.coeff 0 + (p w).2.coeff 0), w.2)

/-- The formula for the smoothing-coordinate change. -/
@[simp]
theorem neckSmoothingMap_apply (p : ℂ × A → CircleSobolev s ℂ × CircleSobolev s ℂ)
    (w : ℂ × A) :
    neckSmoothingMap p w = (w.1 * exp ((p w).1.coeff 0 + (p w).2.coeff 0), w.2) := (rfl)

/-- Ambient neck evaluation lies over the smoothing-coordinate change. In this square the
smoothing argument of the logarithmic data is the ambient product `xy`. -/
theorem neckSmoothingMap_mul
    (p : ℂ × A → CircleSobolev s ℂ × CircleSobolev s ℂ) (w : (ℂ × ℂ) × A) :
    neckSmoothingMap p (w.1.1 * w.1.2, w.2) =
      ((neckEvaluation (p (w.1.1 * w.1.2, w.2)) w.1).1 *
        (neckEvaluation (p (w.1.1 * w.1.2, w.2)) w.1).2, w.2) := by
  rw [neckSmoothingMap_apply, neckEvaluation_fst_mul_snd]

variable [NormedAddCommGroup A] [NormedSpace ℂ A]
  {p : ℂ × A → CircleSobolev s ℂ × CircleSobolev s ℂ} {t : A}

/-- Holomorphic logarithmic data give a jointly holomorphic smoothing-coordinate change. -/
theorem analyticAt_neckSmoothingMap {w : ℂ × A} (hp : AnalyticAt ℂ p w) :
    AnalyticAt ℂ (neckSmoothingMap p) w := by
  have hF := ((coeffCLM 0).analyticAt _).comp (analyticAt_fst.comp hp)
  have hG := ((coeffCLM 0).analyticAt _).comp (analyticAt_snd.comp hp)
  convert (analyticAt_fst.mul (hF.add hG).cexp').prod analyticAt_snd using 1
  funext z
  simp [neckSmoothingMap, Function.comp_def]

/-- The derivative is scaling by the exponential of the constant modes in the smoothing
direction and the identity in the parameter directions. -/
def neckSmoothingLinearEquiv (q : CircleSobolev s ℂ × CircleSobolev s ℂ) :
    (ℂ × A) ≃L[ℂ] (ℂ × A) :=
  (ContinuousLinearEquiv.smulLeft (R₁ := ℂ) (M₁ := ℂ)
    (Units.mk0 (exp (q.1.coeff 0 + q.2.coeff 0)) (exp_ne_zero _))).prodCongr
      (ContinuousLinearEquiv.refl ℂ A)

/-- The smoothing derivative scales only the smoothing coordinate. -/
@[simp]
theorem neckSmoothingLinearEquiv_apply (q : CircleSobolev s ℂ × CircleSobolev s ℂ)
    (w : ℂ × A) :
    neckSmoothingLinearEquiv q w = (exp (q.1.coeff 0 + q.2.coeff 0) * w.1, w.2) := by
  simp [neckSmoothingLinearEquiv]

/-- The inverse smoothing derivative scales by the reciprocal exponential. -/
@[simp]
theorem neckSmoothingLinearEquiv_symm_apply (q : CircleSobolev s ℂ × CircleSobolev s ℂ)
    (w : ℂ × A) :
    (neckSmoothingLinearEquiv q).symm w =
      (exp (-(q.1.coeff 0 + q.2.coeff 0)) * w.1, w.2) := by
  apply (neckSmoothingLinearEquiv q).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, neckSmoothingLinearEquiv_apply, exp_neg]
  ext <;> simp

/-- Derivatives of the moving data do not contribute at the zero smoothing coordinate. -/
theorem hasFDerivAt_neckSmoothingMap (hp : DifferentiableAt ℂ p (0, t)) :
    HasFDerivAt (neckSmoothingMap p)
      (neckSmoothingLinearEquiv (A := A) (p (0, t)) : (ℂ × A) →L[ℂ] (ℂ × A)) (0, t) := by
  have hF := (coeffCLM 0).differentiableAt.comp _ (differentiableAt_fst.comp _ hp)
  have hG := (coeffCLM 0).differentiableAt.comp _ (differentiableAt_snd.comp _ hp)
  have h := (hasFDerivAt_fst (𝕜 := ℂ) (p := ((0 : ℂ), t))).mul
    (hF.add hG).hasFDerivAt.cexp
  convert h.prodMk (hasFDerivAt_snd (𝕜 := ℂ) (p := ((0 : ℂ), t))) using 1
  · funext w
    simp [neckSmoothingMap, Function.comp_def]
  · ext w <;> simp [neckSmoothingLinearEquiv_apply, mul_comm]

/-- Holomorphic moving data give the same strict derivative at the zero smoothing coordinate. -/
theorem hasStrictFDerivAt_neckSmoothingMap (hp : AnalyticAt ℂ p (0, t)) :
    HasStrictFDerivAt (neckSmoothingMap p)
      (neckSmoothingLinearEquiv (A := A) (p (0, t)) : (ℂ × A) →L[ℂ] (ℂ × A)) (0, t) :=
  (hasFDerivAt_neckSmoothingMap hp.differentiableAt).fderiv ▸
    (analyticAt_neckSmoothingMap hp).hasStrictFDerivAt

/-- The difference of the target smoothing coordinates at `a` and `σ(t)` is the source
difference times a holomorphic unit. Its value at the node is the product of the two branch
derivatives. This retains the defining ideals, not just their zero sets. -/
theorem exists_analyticAt_neckSmoothingMap_sub_mul (hp : AnalyticAt ℂ p (0, t))
    {σ : A → ℂ} (hσ : AnalyticAt ℂ σ t) (hσ0 : σ t = 0) :
    ∃ u : ℂ × A → ℂ, AnalyticAt ℂ u (0, t) ∧
      u (0, t) = exp ((p (0, t)).1.coeff 0 + (p (0, t)).2.coeff 0) ∧
      ∀ᶠ w in 𝓝 (0, t),
        (neckSmoothingMap p w).1 - (neckSmoothingMap p (σ w.2, w.2)).1 =
          (w.1 - σ w.2) * u w := by
  let B : ℂ × A → ℂ := fun w ↦ (neckSmoothingMap p w).1
  have hB : AnalyticAt ℂ B (0, t) := analyticAt_fst.comp (analyticAt_neckSmoothingMap hp)
  let G : A × ℂ → ℂ := fun z ↦ B (z.2, z.1) - B (σ z.1, z.1)
  have hG : AnalyticAt ℂ G (t, σ t) := by
    apply AnalyticAt.sub
    · exact hB.comp_of_eq (analyticAt_snd.prod analyticAt_fst) (by simp [hσ0])
    · exact hB.comp_of_eq ((hσ.comp analyticAt_fst).prod analyticAt_fst) (by simp [hσ0])
  obtain ⟨v, hv, hGv⟩ := hG.exists_eventuallyEq_sub_smul_of_graph hσ
    (Eventually.of_forall fun _ ↦ sub_self _)
  rw [hσ0] at hv hGv
  have hvt : AnalyticAt ℂ (fun a : ℂ ↦ v (t, a)) 0 :=
    hv.comp (analyticAt_const.prod analyticAt_id)
  have hd := (hasFDerivAt_neckSmoothingMap hp.differentiableAt).fst.comp_hasDerivAt (0 : ℂ)
    ((hasDerivAt_id (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) t))
  have hd' : HasDerivAt (fun a : ℂ ↦ B (a, t))
      (exp ((p (0, t)).1.coeff 0 + (p (0, t)).2.coeff 0)) 0 := by
    convert hd using 1
    · funext a
      simp [B]
    · simp [neckSmoothingLinearEquiv_apply]
  have heq : (fun a : ℂ ↦ B (a, t)) =ᶠ[𝓝 0] fun a ↦ a * v (t, a) := by
    have ht : Tendsto (fun a : ℂ ↦ (t, a)) (𝓝 0) (𝓝 (t, 0)) :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [ht.eventually hGv] with a ha
    simpa [G, B, hσ0] using ha
  have hv0 : v (t, 0) = exp ((p (0, t)).1.coeff 0 + (p (0, t)).2.coeff 0) := by
    have hdv : HasDerivAt (fun a : ℂ ↦ a * v (t, a)) (v (t, 0)) 0 := by
      convert (hasDerivAt_id (0 : ℂ)).mul hvt.differentiableAt.hasDerivAt using 1
      · funext a
        simp
      · simp
    exact ((hd'.congr_of_eventuallyEq heq.symm).unique hdv).symm
  refine ⟨fun w ↦ v w.swap,
    hv.comp (f := Prod.swap) (x := (0, t)) (analyticAt_snd.prod analyticAt_fst), hv0, ?_⟩
  have hswap : Tendsto (Prod.swap : ℂ × A → A × ℂ) (𝓝 (0, t)) (𝓝 (t, 0)) :=
    continuousAt_snd.prodMk continuousAt_fst
  filter_upwards [hswap.eventually hGv] with w hw
  simpa only [G, B, Prod.fst_swap, Prod.snd_swap, smul_eq_mul] using hw

variable [CompleteSpace A]

/-- A local holomorphic change from the source to the target smoothing coordinate near a node.
It fixes the additional parameters and requires no smallness of the constant logarithmic modes. -/
def neckSmoothingChart (hp : AnalyticAt ℂ p (0, t)) :
    OpenPartialHomeomorph (ℂ × A) (ℂ × A) :=
  (hasStrictFDerivAt_neckSmoothingMap hp).toOpenPartialHomeomorph _

/-- The forward chart is the actual target smoothing map. -/
@[simp]
theorem coe_neckSmoothingChart (hp : AnalyticAt ℂ p (0, t)) :
    (neckSmoothingChart hp : (ℂ × A) → ℂ × A) = neckSmoothingMap p :=
  (hasStrictFDerivAt_neckSmoothingMap hp).toOpenPartialHomeomorph_coe

/-- The source of the smoothing chart contains the node. -/
theorem node_mem_neckSmoothingChart_source (hp : AnalyticAt ℂ p (0, t)) :
    (0, t) ∈ (neckSmoothingChart hp).source :=
  (hasStrictFDerivAt_neckSmoothingMap hp).mem_toOpenPartialHomeomorph_source

/-- The target of the smoothing chart contains the node. -/
theorem node_mem_neckSmoothingChart_target (hp : AnalyticAt ℂ p (0, t)) :
    (0, t) ∈ (neckSmoothingChart hp).target := by
  simpa only [neckSmoothingChart, neckSmoothingMap_apply, zero_mul] using
    (hasStrictFDerivAt_neckSmoothingMap hp).image_mem_toOpenPartialHomeomorph_target

/-- The inverse chart fixes the central node. -/
@[simp]
theorem neckSmoothingChart_symm_node (hp : AnalyticAt ℂ p (0, t)) :
    (neckSmoothingChart hp).symm (0, t) = (0, t) := by
  simpa only [neckSmoothingChart, HasStrictFDerivAt.localInverse_def,
    neckSmoothingMap_apply, zero_mul] using
    (hasStrictFDerivAt_neckSmoothingMap hp).localInverse_apply_image

/-- The inverse chart scales the smoothing direction by the reciprocal exponential and fixes
parameter directions at the node. -/
theorem hasStrictFDerivAt_neckSmoothingChart_symm (hp : AnalyticAt ℂ p (0, t)) :
    HasStrictFDerivAt (neckSmoothingChart hp).symm
      ((neckSmoothingLinearEquiv (A := A) (p (0, t))).symm : (ℂ × A) →L[ℂ] (ℂ × A))
      (0, t) := by
  simpa only [neckSmoothingChart, HasStrictFDerivAt.localInverse_def,
    neckSmoothingMap_apply, zero_mul] using
    (hasStrictFDerivAt_neckSmoothingMap hp).to_localInverse

/-- The inverse smoothing coordinate is jointly holomorphic. -/
theorem analyticAt_neckSmoothingChart_symm (hp : AnalyticAt ℂ p (0, t)) :
    AnalyticAt ℂ (neckSmoothingChart hp).symm (0, t) := by
  simpa only [neckSmoothingChart, HasStrictFDerivAt.localInverse_def,
    neckSmoothingMap_apply, zero_mul] using
    (hasStrictFDerivAt_neckSmoothingMap hp).analyticAt_localInverse (analyticAt_neckSmoothingMap hp)

/-- The inverse smoothing chart preserves the additional parameter. -/
@[simp]
theorem neckSmoothingChart_symm_snd (hp : AnalyticAt ℂ p (0, t))
    {w : ℂ × A} (hw : w ∈ (neckSmoothingChart hp).target) :
    ((neckSmoothingChart hp).symm w).2 = w.2 := by
  have h := congrArg Prod.snd ((neckSmoothingChart hp).right_inv hw)
  simpa using h

/-- The inverse chart preserves exactly the zero smoothing locus. -/
@[simp]
theorem neckSmoothingChart_symm_fst_eq_zero_iff (hp : AnalyticAt ℂ p (0, t))
    {w : ℂ × A} (hw : w ∈ (neckSmoothingChart hp).target) :
    ((neckSmoothingChart hp).symm w).1 = 0 ↔ w.1 = 0 := by
  have h := congrArg Prod.fst ((neckSmoothingChart hp).right_inv hw)
  rw [← h, coe_neckSmoothingChart]
  simp

/-- On the chosen smoothing-chart source, the ambient neck map identifies every pulled-back
node equation with its transformed equation. The parameter `σ` need not have nonzero derivative. -/
theorem neckEvaluation_mul_eq_iff (hp : AnalyticAt ℂ p (0, t))
    (σ : A → ℂ) {w : (ℂ × ℂ) × A}
    (hw : (w.1.1 * w.1.2, w.2) ∈ (neckSmoothingChart hp).source)
    (hσ : (σ w.2, w.2) ∈ (neckSmoothingChart hp).source) :
    (neckEvaluation (p (w.1.1 * w.1.2, w.2)) w.1).1 *
        (neckEvaluation (p (w.1.1 * w.1.2, w.2)) w.1).2 =
      (neckSmoothingMap p (σ w.2, w.2)).1 ↔ w.1.1 * w.1.2 = σ w.2 := by
  have hinj := (neckSmoothingChart hp).injOn.eq_iff hw hσ
  rw [coe_neckSmoothingChart, neckSmoothingMap_mul, neckSmoothingMap_apply,
    Prod.mk.injEq, Prod.mk.injEq] at hinj
  simpa only [and_true, neckSmoothingMap_apply] using hinj

/-- For any continuous smoothing function vanishing at the central parameter, the ambient neck
map identifies the pulled-back equations on a whole neighborhood of the node. In particular this
applies to holomorphic smoothing functions with arbitrary orders of vanishing. -/
theorem eventually_neckEvaluation_mul_eq_iff (hp : AnalyticAt ℂ p (0, t))
    {σ : A → ℂ} (hσ : ContinuousAt σ t) (hσ0 : σ t = 0) :
    ∀ᶠ w : (ℂ × ℂ) × A in 𝓝 (0, t),
      (neckEvaluation (p (w.1.1 * w.1.2, w.2)) w.1).1 *
          (neckEvaluation (p (w.1.1 * w.1.2, w.2)) w.1).2 =
        (neckSmoothingMap p (σ w.2, w.2)).1 ↔ w.1.1 * w.1.2 = σ w.2 := by
  have hsource := (neckSmoothingChart hp).open_source.mem_nhds
    (node_mem_neckSmoothingChart_source hp)
  have hm : ContinuousAt (fun w : (ℂ × ℂ) × A ↦ (w.1.1 * w.1.2, w.2)) (0, t) := by
    fun_prop
  have hgraph : ContinuousAt (fun w : (ℂ × ℂ) × A ↦ (σ w.2, w.2)) (0, t) :=
    (hσ.comp continuousAt_snd).prodMk continuousAt_snd
  have hm0 : (fun w : (ℂ × ℂ) × A ↦ (w.1.1 * w.1.2, w.2)) (0, t) = (0, t) := by simp
  have hg0 : (fun w : (ℂ × ℂ) × A ↦ (σ w.2, w.2)) (0, t) = (0, t) := by simp [hσ0]
  filter_upwards [hm (hm0.symm ▸ hsource), hgraph (hg0.symm ▸ hsource)] with w hw hg
  exact neckEvaluation_mul_eq_iff hp σ hw hg

end TauCeti.CircleSobolev
