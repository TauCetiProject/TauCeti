/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Calculus.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral
import TauCeti.Geometry.Manifold.ContMDiff.PartialDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Integrals of families of differential forms over a compact parameter manifold

Let `η : N → RoughForm I M F k` be a family of differential forms on `M`, indexed by the points of
a manifold `N` carrying a measure `μ`. Its integral `TauCeti.parametricIntegralForm μ η` is the
form whose value at `x` is the Bochner integral `∫ a, η a x ∂μ` in the normed space of continuous
alternating maps on the model fibre.

When `N` is compact, `μ` is finite and the family is jointly `C^n` in `(a, x)`, that is, the map
`(a, x) ↦ η a x` is a `C^n` map into the bundle of alternating maps over the projection
`(a, x) ↦ x`, the integral is a `C^n` form (`TauCeti.IsSmoothForm.parametricIntegralForm`). When
the family is jointly `C¹` on a boundaryless `C²` manifold, the coordinate expressions of the
integral are differentiated under the integral sign
(`TauCeti.hasFDerivAt_inChartAt_parametricIntegralForm`), and so the exterior derivative of the
integral is the integral of the exterior derivatives
(`TauCeti.mextDeriv_parametricIntegralForm`).

Both statements are proved in a local trivialization of the bundle of alternating maps, in
which the fibre coordinate of the integral is the integral of the fibre coordinates. Smoothness
then follows from `TauCeti.contMDiffAt_parametric_integral`, and differentiation under the
integral sign in a chart from `TauCeti.hasFDerivAt_integral_smul_of_continuousOn_fderiv`, with the
joint continuity of the partial derivatives supplied by
`ContMDiffOn.continuousOn_iteratedFDeriv_partial`.

The main application is the average of a form over the action of a compact group, in
`TauCeti.Geometry.Manifold.DifferentialForm.Average`.

## Main declarations

* `TauCeti.parametricIntegralForm`: the integral of a family of forms.
* `TauCeti.parametricIntegralForm_apply`: its value on tangent vectors is the integral of the
  values.
* `TauCeti.IsSmoothForm.parametricIntegralForm`: the integral of a jointly `C^n` family is `C^n`.
* `TauCeti.hasFDerivAt_inChartAt_parametricIntegralForm`: in a chart, the derivative of the
  coordinate expression of the integral of a jointly `C¹` family is the integral of the
  derivatives of the coordinate expressions.
* `TauCeti.mextDeriv_parametricIntegralForm`: the exterior derivative commutes with integration
  of a jointly `C¹` family.
-/

public section

noncomputable section

open Bundle Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M EN HN N F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

section Defs

variable [MeasurableSpace N] {μ : Measure N}

variable (μ) in
/-- The integral `x ↦ ∫ a, η a x ∂μ` of a family of forms `η` indexed by a measure space `N`. The
integral is taken in the normed space `E [⋀^Fin k]→L[ℝ] F` of alternating maps on the model
fibre, which is the fibre at every point of the bundle of alternating maps on tangent spaces. -/
def parametricIntegralForm (η : N → RoughForm I M F k) : RoughForm I M F k :=
  fun x ↦ (∫ a, η a x ∂μ : E [⋀^Fin k]→L[ℝ] F)

theorem parametricIntegralForm_def (η : N → RoughForm I M F k) (x : M) :
    parametricIntegralForm μ η x = (∫ a, η a x ∂μ : E [⋀^Fin k]→L[ℝ] F) :=
  (rfl)

end Defs

variable [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I 1 M]

/-- The trivialization at `x₀` of the bundle of alternating maps on tangent spaces. -/
local notation "𝔱" x₀ => trivializationAt (E [⋀^Fin k]→L[ℝ] F)
  (fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) x₀

/-- In the trivialization of the bundle of alternating maps at `x₀`, the fibre coordinate of a
jointly `C^n` family of forms is `C^n` at every point `(a, x₀)`. -/
private theorem contMDiffAt_trivializationAt_family {n : WithTop ℕ∞} {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x₀ : M) (a : N) :
    ContMDiffAt (J.prod I) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) n
      (fun p : N × M ↦ ((𝔱 x₀) ⟨p.2, η p.1 p.2⟩).2) (a, x₀) :=
  (contMDiffAt_totalSpace_iff.1 (hη (a, x₀))).2

/-- The forms of a jointly continuous family at a fixed point depend continuously on the
parameter. -/
private theorem continuous_family {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 0
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) :
    Continuous fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x) := by
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  have h := ((contMDiffAt_trivializationAt_family hη x a).continuousAt).comp
    (f := fun a : N ↦ (a, x)) (continuous_id.prodMk continuous_const).continuousAt
  refine h.congr (Eventually.of_forall fun b ↦ ?_)
  ext v
  simp [FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd, Function.comp_def,
    Manifold.symmL_trivializationAt_self]
  rfl

/-- The chart target at `x` is mapped into the base set of the trivialization at `x` of the
bundle of alternating maps. -/
private theorem symm_mem_baseSet_trivializationAt (x : M) {z : E}
    (hz : z ∈ (extChartAt I x).target) : (extChartAt I x).symm z ∈ (𝔱 x).baseSet := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_baseSet,
    TangentBundle.trivializationAt_baseSet]
  refine ⟨?_, by simp⟩
  simpa only [extChartAt_source] using (extChartAt I x).map_target hz

section Chart

variable [I.Boundaryless] [IsManifold I 2 M]

/-- On the chart target at `x`, the coordinate expressions of a jointly `C¹` family of forms are
jointly `C¹` in the chart coordinate and the parameter. -/
private theorem contMDiffOn_inChartAt_family {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) :
    ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) 1
      (fun q : E × N ↦ (η q.2).inChartAt x q.1) ((extChartAt I x).target ×ˢ univ) := by
  have hT : IsOpen (extChartAt I x).target := isOpen_extChartAt_target x
  intro q hq
  -- Near `q`, the coordinate expression is the fibre coordinate in the trivialization at `x`.
  have hsymm : ContMDiffAt (𝓘(ℝ, E).prod J) (J.prod I) 1
      (fun q : E × N ↦ (q.2, (extChartAt I x).symm q.1)) q :=
    contMDiffAt_snd.prodMk (((contMDiffOn_extChartAt_symm (n := 1) x).contMDiffAt
      (hT.mem_nhds hq.1)).comp q contMDiffAt_fst)
  have hbase := symm_mem_baseSet_trivializationAt (F := F) (k := k) x hq.1
  have htriv : ContMDiffAt (J.prod I) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) 1
      (fun p : N × M ↦ ((𝔱 x) ⟨p.2, η p.1 p.2⟩).2) (q.2, (extChartAt I x).symm q.1) :=
    ((𝔱 x).contMDiffAt_iff ((𝔱 x).mem_source.2 hbase)).1 (hη _) |>.2
  refine (htriv.comp q hsymm).contMDiffWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds ((hT.prod isOpen_univ).mem_nhds hq)] with q' hq'
    exact RoughForm.inChartAt_eq_trivializationAt _ x hq'.1
  · exact RoughForm.inChartAt_eq_trivializationAt _ x hq.1

end Chart

variable [MeasurableSpace N] [OpensMeasurableSpace N] [CompactSpace N] {μ : Measure N}
  [IsFiniteMeasure μ]

/-- A jointly continuous family of forms is integrable at every point. -/
private theorem integrable_family {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 0
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) :
    Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x)) μ :=
  (continuous_family hη x).integrable_of_hasCompactSupport (.of_compactSpace _)

variable [CompleteSpace F]

/-- Over a point `y` of the base set of the trivialization at `x₀` of the bundle of alternating
maps, the fibre coordinate of the integral of a jointly continuous family of forms is the integral
of the fibre coordinates. -/
private theorem trivializationAt_parametricIntegralForm {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 0
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x₀ : M) {y : M} (hy : y ∈ (𝔱 x₀).baseSet) :
    ((𝔱 x₀) ⟨y, parametricIntegralForm μ η y⟩).2 = ∫ a, ((𝔱 x₀) ⟨y, η a y⟩).2 ∂μ := by
  -- The fibre coordinate over `y` is a continuous linear map, which commutes with the integral.
  let L : (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] (E [⋀^Fin k]→L[ℝ] F) := (𝔱 x₀).continuousLinearMapAt ℝ y
  have hL (φ : TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) : ((𝔱 x₀) ⟨y, φ⟩).2 = L φ :=
    ((𝔱 x₀).continuousLinearMapAt_apply_of_mem (R := ℝ) hy φ).symm
  simp only [hL]
  exact (L.integral_comp_comm (integrable_family hη y)).symm

/-- The value of the integral of a jointly continuous family of forms on tangent vectors is the
integral of the values. -/
theorem parametricIntegralForm_apply {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 0
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) (v : Fin k → TangentSpace I x) :
    parametricIntegralForm μ η x v = ∫ a, η a x v ∂μ :=
  ((ContinuousAlternatingMap.apply ℝ E F v).integral_comp_comm (integrable_family hη x)).symm

/-- **Integrals of smooth families of forms are smooth.** If the family `η` of forms on a
boundaryless manifold `M`, indexed by a compact manifold `N` with a finite measure `μ`, is jointly
`C^n` in the parameter and the point, then its integral is a `C^n` form. -/
theorem IsSmoothForm.parametricIntegralForm [I.Boundaryless] {n : ℕ∞} [IsManifold I n M]
    [IsManifold J n N] [T2Space N] {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2))) :
    IsSmoothForm I n (parametricIntegralForm μ η) := by
  have hη₀ := hη.of_le zero_le
  rw [isSmoothForm_def]
  intro x₀
  refine (contMDiffAt_section_iff x₀).2 ?_
  -- In the trivialization at `x₀`, the integral is the integral of the fibre coordinates.
  refine (contMDiffAt_parametric_integral (μ := μ) (J := J)
    (f := fun x a ↦ ((𝔱 x₀) ⟨x, η a x⟩).2) fun a ↦ by
      have hs : ContMDiffAt (I.prod J) (J.prod I) n (fun q : M × N ↦ (q.2, q.1)) (x₀, a) :=
        contMDiffAt_snd.prodMk contMDiffAt_fst
      have h := (contMDiffAt_trivializationAt_family hη x₀ a).comp (x₀, a) hs
      exact h).congr_of_eventuallyEq ?_
  filter_upwards [(𝔱 x₀).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x₀)]
    with x hx
  exact trivializationAt_parametricIntegralForm hη₀ x₀ hx

section ExtDeriv

variable [I.Boundaryless] [J.Boundaryless] [IsManifold I 2 M] [IsManifold J 1 N]

-- Cache the canonical normed instances on alternating maps: instance search for the normed
-- structure on the operator space `E →L[ℝ] E [⋀^Fin k]→L[ℝ] F` otherwise fails.
private local instance : NormedAddCommGroup (E [⋀^Fin k]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedAddCommGroup
private local instance : NormedSpace ℝ (E [⋀^Fin k]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedSpace

/-- The coordinate expressions of a jointly `C¹` family of forms have partial derivatives that
are integrable in the parameter, and the coordinate expression of the integral has as derivative
the integral of these partial derivatives. -/
private theorem integrable_fderiv_inChartAt_and_hasFDerivAt {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) :
    Integrable (fun a ↦ fderiv ℝ ((η a).inChartAt x) (extChartAt I x x)) μ ∧
      HasFDerivAt ((parametricIntegralForm μ η).inChartAt x)
        (∫ a, fderiv ℝ ((η a).inChartAt x) (extChartAt I x x) ∂μ) (extChartAt I x x) := by
  set T := (extChartAt I x).target
  have hT : IsOpen T := isOpen_extChartAt_target x
  have hxT : extChartAt I x x ∈ T := mem_extChartAt_target x
  set Φ : E × N → E [⋀^Fin k]→L[ℝ] F := fun q ↦ (η q.2).inChartAt x q.1
  have hΦ := contMDiffOn_inChartAt_family hη x
  -- The partial derivatives of the coordinate expressions are jointly continuous.
  have hD : ContinuousOn (fun q : E × N ↦ fderiv ℝ (fun z ↦ Φ (z, q.2)) q.1) (T ×ˢ univ) := by
    refine ((continuousMultilinearCurryFin1 ℝ E _).continuous.comp_continuousOn
      (hΦ.continuousOn_iteratedFDeriv_partial (hT.prod isOpen_univ) (k := 1) le_rfl)).congr
      fun q _ ↦ ?_
    ext v
    simp [Φ]
  have hdiff (a : N) : DifferentiableOn ℝ (fun z ↦ Φ (z, a)) T :=
    (contMDiffOn_iff_contDiffOn.1 (hΦ.comp (contMDiffOn_id.prodMk contMDiffOn_const)
      fun z hz ↦ ⟨hz, mem_univ a⟩)).differentiableOn one_ne_zero
  refine ⟨(hD.comp_continuous (continuous_const.prodMk continuous_id) fun a ↦ ⟨hxT, mem_univ a⟩
      ).integrable_of_hasCompactSupport (.of_compactSpace _), ?_⟩
  -- In the chart at `x`, the integral of the forms is the integral of their coordinates, which
  -- is differentiated under the integral sign.
  have hint : (parametricIntegralForm μ η).inChartAt x =ᶠ[𝓝 (extChartAt I x x)]
      fun z ↦ ∫ a, Φ (z, a) ∂μ := by
    filter_upwards [hT.mem_nhds hxT] with z hz
    rw [RoughForm.inChartAt_eq_trivializationAt _ x hz,
      trivializationAt_parametricIntegralForm (hη.of_le zero_le) x
        (symm_mem_baseSet_trivializationAt (F := F) (k := k) x hz)]
    exact integral_congr_ae (Eventually.of_forall fun a ↦
      (RoughForm.inChartAt_eq_trivializationAt _ x hz).symm)
  refine HasFDerivAt.congr_of_eventuallyEq ?_ hint
  simpa only [one_smul] using hasFDerivAt_integral_smul_of_continuousOn_fderiv (μ := μ)
    (g := fun _ ↦ (1 : ℝ)) (integrable_const _) hT hΦ.continuousOn hdiff hD hxT

/-- **Differentiation under the integral sign in a chart.** For a jointly `C¹` family `η` of
forms on a boundaryless `C²` manifold, indexed by a compact boundaryless manifold with a finite
measure, the coordinate expression in the chart at `x` of the integral of the family has, at the
chart point of `x`, the integral of the derivatives of the coordinate expressions as its
derivative. -/
theorem hasFDerivAt_inChartAt_parametricIntegralForm {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) :
    HasFDerivAt ((parametricIntegralForm μ η).inChartAt x)
      (∫ a, fderiv ℝ ((η a).inChartAt x) (extChartAt I x x) ∂μ) (extChartAt I x x) :=
  (integrable_fderiv_inChartAt_and_hasFDerivAt hη x).2

/-- **Exterior differentiation under the integral sign.** For a jointly `C¹` family `η` of forms on
a boundaryless `C²` manifold, indexed by a compact boundaryless manifold with a finite measure,
the exterior derivative of the integral is the integral of the exterior derivatives. -/
theorem mextDeriv_parametricIntegralForm {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2))) :
    mextDeriv (parametricIntegralForm μ η) = parametricIntegralForm μ fun a ↦ mextDeriv (η a) := by
  funext x
  obtain ⟨hDint, hderiv⟩ := integrable_fderiv_inChartAt_and_hasFDerivAt (μ := μ) hη x
  rw [mextDeriv_def, I.range_eq_univ, extDerivWithin_univ, extDeriv, hderiv.fderiv,
    parametricIntegralForm_def, ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm _ hDint]
  congr 1
  funext a
  rw [mextDeriv_def, I.range_eq_univ, extDerivWithin_univ, extDeriv,
    ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]

end ExtDeriv

end TauCeti
