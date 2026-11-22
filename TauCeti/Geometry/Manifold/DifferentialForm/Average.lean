/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.Algebra.SMul
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.ExtChartAt.Basic
/-!
# Averaging differential forms over a compact group action

Let a group `G`, which is a compact smooth manifold, act smoothly on a boundaryless smooth
manifold `M`, and let `μ` be a finite measure on `G`. For a smooth differential form `α` on `M`
with values in a Banach space, `TauCeti.SmoothForm.measureAverage J μ α` is the form

`(avg α)_x (v₁, …, vₖ) = ∫ α_{a • x}(d(a •)_x v₁, …, d(a •)_x vₖ) dμ(a)`,

the integral over `G` of the pullbacks `(a •)^* α`. It is smooth because, read in a bundle chart,
the pullbacks depend smoothly on the point and the group element
(`ContMDiffAt.mpullback_form_family`), so their average is smooth by differentiation under the
integral over the compact parameter manifold `G` (`TauCeti.contMDiffAt_parametric_integral`).

Averaging is the basic tool for producing invariant forms. When `μ` is right-invariant, for
instance the normalized Haar measure `TauCeti.haarProb`, every element of `G` preserves the
averaged form (`TauCeti.SmoothForm.mpullback_smul_measureAverage`), and when `μ` is moreover a
right-invariant probability measure, averaging fixes exactly the invariant forms
(`TauCeti.SmoothForm.measureAverage_eq_self_iff`). Averaging commutes with the exterior derivative
(`TauCeti.SmoothForm.mextDerivₗ_measureAverage`): in a chart, the coordinate expression of the
average is the integral of the coordinate expressions of the pullbacks, which are jointly smooth in
the chart point and the group element, and the exterior derivative can be taken under the integral
(`TauCeti.extDeriv_integral_of_contMDiffOn`). Hence the average of a closed form is closed
(`TauCeti.SmoothForm.IsClosed.measureAverage`), and the average of an exact form `d β` is the
exact form `d (avg β)`. A form vanishing at every point of an orbit has average
vanishing there (`TauCeti.SmoothForm.measureAverage_eq_zero_of_forall_smul`), so averaging
preserves vanishing on an invariant subset. These are the properties used to make the forms and
primitives of an equivariant Moser argument invariant under a compact group.

The construction follows `TauCeti.measureAverageRiemannianMetric` in
`TauCeti/Geometry/Manifold/Riemannian/Invariant.lean`, which averages Riemannian metrics in the
same way.

## Main definitions

* `TauCeti.SmoothForm.measureAverage J μ`: the average over a compact group action against a
  finite measure `μ` on the group, as a linear map on smooth forms.

## Main results

* `TauCeti.SmoothForm.measureAverage_apply`: the averaged form is the integral of the pulled-back
  forms.
* `TauCeti.SmoothForm.mpullback_smul_measureAverage`: for right-invariant `μ`, the averaged form is
  invariant.
* `TauCeti.SmoothForm.measureAverage_eq_self_iff`: for a right-invariant probability measure,
  averaging fixes exactly the invariant forms.
* `TauCeti.SmoothForm.mextDerivₗ_measureAverage`: averaging commutes with the exterior derivative.
* `TauCeti.SmoothForm.IsClosed.measureAverage`: the average of a closed form is closed.
* `TauCeti.SmoothForm.measureAverage_eq_zero_of_forall_smul`: a form vanishing along an orbit has
  average vanishing there.

## References

* G. E. Bredon, *Introduction to Compact Transformation Groups*, Academic Press (1972),
  Chapter VI, for averaging over smooth compact transformation groups.
-/

public noncomputable section

open Bundle MeasureTheory Function Filter Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {G : Type*} [Group G] [MulAction G M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The pullback of `α` by the action of `a`, at `x`, read as an alternating map on the model
vector space. -/
private def pullbackSMulForm (α : SmoothForm I M F k) (a : G) (x : M) : E [⋀^Fin k]→L[ℝ] F :=
  -- `TangentSpace I x` is definitionally `E` and `Trivial M F x` is `F`. The `@id` ascription reads
  -- the value as an alternating map on `E`, so that it can be integrated in the fixed normed space
  -- `E [⋀^Fin k]→L[ℝ] F`, which carries the norm that the fibre `T_x M [⋀^Fin k]→L[ℝ] F` lacks.
  @id (E [⋀^Fin k]→L[ℝ] F) (mpullback I I (a • ·) α.val x)

variable (I) in
/-- At a point `x` of the chart domain at `x₀`, the trivialization at `x₀` of the bundle of
alternating maps, read on the model space, is a continuous linear automorphism of the fibre. -/
private def trivializationAtEquiv (x₀ : M) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    (E [⋀^Fin k]→L[ℝ] F) ≃L[ℝ] (E [⋀^Fin k]→L[ℝ] F) :=
  (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
    (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) x₀).continuousLinearEquivAt ℝ x
    (by simpa using hx)

section Rough

variable [MeasurableSpace G] (μ : Measure G)

/-- The average of the pullbacks of a form, as an alternating map on the model vector space. -/
private def averageModel (α : SmoothForm I M F k) (x : M) : E [⋀^Fin k]→L[ℝ] F :=
  ∫ a, pullbackSMulForm α a x ∂μ

/-- The average of the pullbacks of a form, as a rough form. -/
private def averageForm (α : SmoothForm I M F k) : RoughForm I M F k :=
  -- The value `averageModel μ α x` lies in the fibre `T_x M [⋀^Fin k]→L[ℝ] F`, definitionally.
  averageModel μ α

/-- In the trivialization at `x₀`, the averaged form is the integral of the trivialized
pullbacks. -/
private theorem trivializationAt_averageForm (α : SmoothForm I M F k) (x₀ : M) {x : M}
    (hx : x ∈ (chartAt H x₀).source) :
    (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
        (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) x₀
        ⟨x, averageForm μ α x⟩).2 =
      ∫ a, (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
        (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) x₀
        ⟨x, mpullback I I (a • ·) α.val x⟩).2 ∂μ :=
  ((trivializationAtEquiv I x₀ hx).integral_comp_comm fun a ↦ pullbackSMulForm α a x).symm

/-- Averaging the pullbacks is homogeneous. -/
private theorem averageModel_smul (c : ℝ) (α : SmoothForm I M F k) (x : M) :
    averageModel μ (c • α) x = c • averageModel μ α x := by
  have h (a : G) : pullbackSMulForm (c • α) a x = c • pullbackSMulForm α a x := by
    unfold pullbackSMulForm
    rw [Submodule.coe_smul, mpullback_smul, Pi.smul_apply]
    -- The sides differ only by the `@id` ascription in `pullbackSMulForm`, which reads the
    -- fibre `T_x M [⋀^Fin k]→L[ℝ] F` as `E [⋀^Fin k]→L[ℝ] F` definitionally.
    exact id_eq _
  simp only [averageModel, h]
  exact integral_smul c _

end Rough

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
  [TopologicalSpace G] [ChartedSpace H' G] [IsManifold J ∞ G] [ContMDiffSMul J I ∞ G M]

include J

omit [IsManifold I ∞ M] [IsManifold J ∞ G] in
/-- Each element of the group acts by a smooth map. -/
private theorem contMDiff_smul_left (a : G) : ContMDiff I I ∞ (a • · : M → M) :=
  ContMDiffSMul.contMDiff_const_smul (I := J) (I' := I) a

/-- The pullbacks of a smooth form by the action are jointly smooth in the point and the group
element, as a section of the bundle of alternating maps along `(x, a) ↦ x`. -/
private theorem contMDiff_mpullback_smul (α : SmoothForm I M F k) :
    ContMDiff (I.prod J) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun p : M × G ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.1
        (mpullback I I (p.2 • ·) α.val p.1)) := fun p₀ ↦ by
  have hsmul : ContMDiff ((I.prod J).prod I) I ∞
      (uncurry fun (p : M × G) (y : M) ↦ p.2 • y) :=
    (contMDiff_smul (I := J) (I' := I)).comp
      ((contMDiff_snd.comp contMDiff_fst).prodMk contMDiff_snd)
  exact ContMDiffAt.mpullback_form_family (α.contMDiff _) hsmul.contMDiffAt contMDiffAt_fst
    (by simp)

/-- In the trivialization at `x₀`, the pullbacks of a smooth form by the action are jointly smooth
in the point and the group element, at every point over the trivializing set. -/
private theorem contMDiffAt_trivializationAt_mpullback_smul (α : SmoothForm I M F k) (x₀ : M)
    {p : M × G} (hp : p.1 ∈ (chartAt H x₀).source) :
    ContMDiffAt (I.prod J) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) ∞
      (fun q : M × G ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
        (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) x₀
        ⟨q.1, mpullback I I (q.2 • ·) α.val q.1⟩).2) p :=
  ((Trivialization.contMDiffAt_iff (by simpa using hp)).1
    (contMDiff_mpullback_smul J α p)).2

/-- The pullbacks of a smooth form by the action depend continuously on the group element. -/
private theorem continuous_pullbackSMulForm (α : SmoothForm I M F k) (x : M) :
    Continuous fun a : G ↦ pullbackSMulForm α a x := by
  let L := trivializationAtEquiv (F := F) (k := k) I x (mem_chart_source H x)
  have h : Continuous fun a : G ↦ L (pullbackSMulForm α a x) :=
    continuous_iff_continuousAt.2 fun a ↦
      (contMDiffAt_trivializationAt_mpullback_smul J α x (p := (x, a))
        (mem_chart_source H x)).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt
  exact (L.symm.continuous.comp h).congr fun a ↦ L.symm_apply_apply _

variable [MeasurableSpace G] [CompactSpace G] [T2Space G] [OpensMeasurableSpace G]
  (μ : Measure G) [IsFiniteMeasure μ]

/-- The pullbacks of a smooth form by the action are integrable in the group element. -/
private theorem integrable_pullbackSMulForm (α : SmoothForm I M F k) (x : M) :
    Integrable (fun a : G ↦ pullbackSMulForm α a x) μ :=
  integrableOn_univ.1 <|
    (continuous_pullbackSMulForm J α x).continuousOn.integrableOn_compact isCompact_univ

/-- Averaging the pullbacks is additive. -/
private theorem averageModel_add (α β : SmoothForm I M F k) (x : M) :
    averageModel μ (α + β) x = averageModel μ α x + averageModel μ β x := by
  have h (a : G) :
      pullbackSMulForm (α + β) a x = pullbackSMulForm α a x + pullbackSMulForm β a x := by
    unfold pullbackSMulForm
    rw [Submodule.coe_add, mpullback_add, Pi.add_apply]
    -- The sides differ only by the `@id` ascription in `pullbackSMulForm`, which reads the
    -- fibre `T_x M [⋀^Fin k]→L[ℝ] F` as `E [⋀^Fin k]→L[ℝ] F` definitionally.
    exact id_eq _
  simp only [averageModel, h]
  exact integral_add (integrable_pullbackSMulForm J μ α x) (integrable_pullbackSMulForm J μ β x)

variable [I.Boundaryless]

omit [MeasurableSpace G] [CompactSpace G] [T2Space G] [OpensMeasurableSpace G] in
/-- In the chart at `x₀`, the coordinate expressions of the pullbacks of a smooth form by the
action are jointly smooth in the chart point and the group element. -/
private theorem contMDiffOn_inChartAt_mpullback_smul (α : SmoothForm I M F k) (x₀ : M) :
    ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) 1
      (uncurry fun (z : E) (a : G) ↦ RoughForm.inChartAt (F := F) (mpullback I I
          (a • ·) α.val) x₀ z)
      ((extChartAt I x₀).target ×ˢ univ) := by
  have hopen : IsOpen ((extChartAt I x₀).target ×ˢ (univ : Set G)) :=
    (isOpen_extChartAt_target x₀).prod isOpen_univ
  intro p hp
  have hsymm : ContMDiffAt (𝓘(ℝ, E).prod J) (I.prod J) ∞
      (fun q : E × G ↦ ((extChartAt I x₀).symm q.1, q.2)) p :=
    (((contMDiffOn_extChartAt_symm x₀).contMDiffAt
      ((isOpen_extChartAt_target x₀).mem_nhds hp.1)).comp p contMDiffAt_fst).prodMk
      contMDiffAt_snd
  refine (((contMDiffAt_trivializationAt_mpullback_smul J α x₀
    (extChartAt_symm_mem_chart_source hp.1)).comp p hsymm).of_le
    (by simp)).contMDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hp)] with q hq
    exact RoughForm.inChartAt_eq_trivializationAt _ x₀ hq.1
  · exact RoughForm.inChartAt_eq_trivializationAt _ x₀ hp.1

/-- The averaged form is a smooth section of the bundle of alternating maps. -/
private theorem contMDiff_averageForm (α : SmoothForm I M F k) :
    ContMDiff I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) ∞
      (fun x ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) x
        (averageForm μ α x)) := by
  intro x₀
  refine contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_id, ?_⟩
  refine (contMDiffAt_parametric_integral (μ := μ) (J := J)
    (f := fun x (a : G) ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) x₀
      ⟨x, mpullback I I (a • ·) α.val x⟩).2)
    fun a ↦ contMDiffAt_trivializationAt_mpullback_smul J α x₀ (p := (x₀, a))
      (mem_chart_source H x₀)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)] with x hx
  exact trivializationAt_averageForm μ α x₀ hx

namespace SmoothForm

/-- **The average of a differential form over a compact group action.** For a group `G` that is
a compact smooth manifold acting smoothly on a boundaryless smooth manifold `M`, and a finite
measure `μ` on `G`, this sends a smooth form `α` to the smooth form

`(avg α)_x (v₁, …, vₖ) = ∫ α_{a • x}(d(a •)_x v₁, …, d(a •)_x vₖ) dμ(a)`.

When `μ` is right-invariant, for instance the normalized Haar measure `TauCeti.haarProb`, every
element of `G` preserves the averaged form (`TauCeti.SmoothForm.mpullback_smul_measureAverage`). -/
def measureAverage : SmoothForm I M F k →ₗ[ℝ] SmoothForm I M F k where
  toFun α := ⟨averageForm μ α,
    mem_smoothBundleForms.mpr ((isSmoothBundleForm_def ∞ _).mpr (contMDiff_averageForm J μ α))⟩
  map_add' α β := Subtype.ext <| funext fun x ↦ averageModel_add J μ α β x
  map_smul' c α := Subtype.ext <| funext fun x ↦ averageModel_smul μ c α x

/-- The underlying rough form of the averaged form is `averageForm`. -/
private theorem val_measureAverage (α : SmoothForm I M F k) :
    (measureAverage J μ α).val = averageForm μ α :=
  rfl

variable [CompleteSpace F]

/-- The averaged form is the integral of the pulled-back forms. -/
@[simp]
theorem measureAverage_apply (α : SmoothForm I M F k) (x : M) (v : Fin k → TangentSpace I x) :
    (measureAverage J μ α).val x v =
      ∫ a, α.val (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i)) ∂μ := by
  refine (ContinuousLinearMap.integral_comp_comm (ContinuousAlternatingMap.apply ℝ E F v)
    (integrable_pullbackSMulForm J μ α x)).symm.trans ?_
  -- The integrands agree by unfolding `pullbackSMulForm`, its `@id` ascription and `mpullback`.
  exact integral_congr_ae (Eventually.of_forall fun a ↦ TauCeti.mpullback_apply _ _ _ _)

/-- **Averaged forms are invariant.** For a right-invariant measure on the group, for instance the
normalized Haar measure, every element of the group preserves the averaged form. -/
@[simp]
theorem mpullback_smul_measureAverage [MeasurableMul G] [μ.IsMulRightInvariant]
    (α : SmoothForm I M F k) (b : G) :
    TauCeti.mpullback (F := F) I I (b • ·) (measureAverage J μ α).val = (measureAverage J μ α).val
        := by
  funext x
  ext v
  rw [TauCeti.mpullback_apply, measureAverage_apply, measureAverage_apply]
  refine Eq.trans ?_ (integral_mul_right_eq_self (μ := μ) (fun a : G ↦
    α.val (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i))) b)
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  have h := mpullback_comp_at (F := F)
    (ContMDiffSMul.mdifferentiable_const_smul (I := J) (n := ∞) (by simp) b x)
    (ContMDiffSMul.mdifferentiable_const_smul (I := J) (n := ∞) (by simp) a (b • x)) α.val
  rw [show (fun y : M ↦ a • y) ∘ (b • ·) = ((a * b) • ·) from
    funext fun y ↦ (mul_smul a b y).symm] at h
  simpa only [TauCeti.mpullback_apply] using (DFunLike.congr_fun h v).symm

/-- **Averaging fixes exactly the invariant forms.** For a right-invariant probability measure on
the group, a form is unchanged by averaging exactly when every element of the group preserves
it. -/
theorem measureAverage_eq_self_iff [IsProbabilityMeasure μ] [MeasurableMul G]
    [μ.IsMulRightInvariant] (α : SmoothForm I M F k) :
    measureAverage J μ α = α ↔ ∀ a : G, TauCeti.mpullback (F := F) I I (a • ·) α.val = α.val := by
  refine ⟨fun h a ↦ ?_, fun h ↦ ?_⟩
  · rw [← h]
    exact mpullback_smul_measureAverage J μ α a
  · refine Subtype.ext <| funext fun x ↦ ?_
    ext v
    have h' (a : G) : α.val (a • x) (fun i ↦ mfderiv I I (a • ·) x (v i)) = α.val x v := by
      rw [← TauCeti.mpullback_apply (F := F) (I := I) (I' := I) (fun y ↦ a • y) α.val x v, h a]
    simp [measureAverage_apply, h']

/-- Averaging twice over a right-invariant probability measure is averaging once. -/
@[simp]
theorem measureAverage_measureAverage [IsProbabilityMeasure μ] [MeasurableMul G]
    [μ.IsMulRightInvariant] (α : SmoothForm I M F k) :
    measureAverage J μ (measureAverage J μ α) = measureAverage J μ α :=
  (measureAverage_eq_self_iff J μ _).mpr (mpullback_smul_measureAverage J μ α)

/-- A form vanishing at every point of the orbit of `x` has average vanishing at `x`. In
particular, averaging preserves vanishing on an invariant subset. -/
theorem measureAverage_eq_zero_of_forall_smul (α : SmoothForm I M F k) {x : M}
    (h : ∀ a : G, α.val (a • x) = 0) : (measureAverage J μ α).val x = 0 := by
  ext v
  rw [measureAverage_apply]
  simp_rw [h]
  simp

end SmoothForm

variable [CompleteSpace F]

namespace SmoothForm

/-- **Averaging commutes with the exterior derivative.** The exterior derivative of the average of a
smooth form is the average of its exterior derivative, `d (avg α) = avg (d α)`. -/
theorem mextDerivₗ_measureAverage (α : SmoothForm I M F k) :
    mextDerivₗ I k (measureAverage J μ α) = measureAverage J μ (mextDerivₗ I k α) := by
  refine Subtype.ext <| funext fun x ↦ ?_
  have htarget : (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  -- In the chart at `x`, the average is the integral of the coordinate expressions of the
  -- pullbacks.
  have hchart : RoughForm.inChartAt (F := F) (measureAverage J μ α).val x =ᶠ[𝓝 (extChartAt I x x)]
      fun z ↦ ∫ a, (TauCeti.mpullback (F := F) I I (a • ·) α.val).inChartAt x z ∂μ := by
    filter_upwards [htarget] with z hz
    rw [RoughForm.inChartAt_eq_trivializationAt _ x hz, val_measureAverage]
    refine (trivializationAt_averageForm μ α x
      (extChartAt_symm_mem_chart_source hz)).trans ?_
    exact integral_congr_ae (Eventually.of_forall fun a ↦
      (RoughForm.inChartAt_eq_trivializationAt _ x hz).symm)
  have hpull (a : G) : TauCeti.mpullback (F := F) I I (a • ·) (mextDeriv α.val) =
      mextDeriv (TauCeti.mpullback (F := F) I I (a • ·) α.val) :=
    mpullback_mextDeriv ((contMDiff_smul_left J a).of_le (by simp))
      ((isSmoothBundleForm_def 1 α.val).mpr (α.contMDiff.of_le (by simp)))
  rw [mextDerivₗ_apply, mextDeriv_eq_extDeriv_inChartAt, hchart.extDeriv_eq,
    extDeriv_integral_of_contMDiffOn (isOpen_extChartAt_target x) (mem_extChartAt_target x)
      (contMDiffOn_inChartAt_mpullback_smul J α x)]
  have key : (∫ a, extDeriv (fun z ↦ RoughForm.inChartAt (F := F)
        (TauCeti.mpullback (F := F) I I (a • ·) α.val) x z) (extChartAt I x x) ∂μ :
        E [⋀^Fin (k + 1)]→L[ℝ] F) =
      averageForm μ (mextDerivₗ I k α) x := by
    rw [averageForm, averageModel]
    refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
    dsimp only
    unfold pullbackSMulForm
    rw [mextDerivₗ_apply, hpull, mextDeriv_eq_extDeriv_inChartAt]
    -- The sides differ by the `@id` ascription in `pullbackSMulForm` and an eta-expansion.
    exact (id_eq _).symm
  rw [val_measureAverage]
  exact key

/-- The average of a closed form is closed. -/
theorem IsClosed.measureAverage {α : SmoothForm I M F k} (hα : α.IsClosed) :
    (measureAverage J μ α).IsClosed := by
  have h0 : mextDerivₗ I k α = 0 :=
    Subtype.ext (by rw [mextDerivₗ_apply, (isClosed_def α).mp hα, Submodule.coe_zero])
  have h := congrArg Subtype.val (mextDerivₗ_measureAverage J μ α)
  rw [h0, map_zero, mextDerivₗ_apply] at h
  exact (isClosed_def _).mpr h

end SmoothForm

end TauCeti
