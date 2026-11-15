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
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic

/-!
# Integrals of families of differential forms over a compact parameter manifold

Let `η : N → RoughForm I M F k` be a family of differential forms on `M`, indexed by the points of
a manifold `N` carrying a measure `μ`. Its integral `TauCeti.parametricIntegralForm μ η` is the
form whose value at `x` is the Bochner integral `∫ a, η a x ∂μ` in the normed space of continuous
alternating maps on the model fibre.

The integral is linear in the family (`TauCeti.parametricIntegralForm_add`,
`TauCeti.parametricIntegralForm_smul`, …), and where the family is integrable at `x` its value on
tangent vectors at `x` is the integral of the values (`TauCeti.parametricIntegralForm_apply`).

When `N` is compact, `μ` is finite and the family is jointly continuous, the family is integrable
at every point (`TauCeti.integrable_family_apply`). When moreover the family is jointly `C^n` in
`(a, x)`, that is, the map `(a, x) ↦ η a x` is a `C^n` map into the bundle of alternating maps
over the projection `(a, x) ↦ x`, and `M` is boundaryless and `N` Hausdorff, the integral is a
`C^n` form (`TauCeti.IsSmoothForm.parametricIntegralForm`). When the family is jointly `C¹` and
`M` is a boundaryless `C²` manifold, the coordinate expressions of the integral are differentiated
under the integral sign (`TauCeti.hasFDerivAt_inChartAt_parametricIntegralForm`), and so the
exterior derivative of the integral is the integral of the exterior derivatives
(`TauCeti.mextDeriv_parametricIntegralForm`). The parameter manifold `N` may have boundary.

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
* `TauCeti.parametricIntegralForm_apply`: for an integrable family, its value on tangent vectors
  is the integral of the values.
* `TauCeti.mpullback_parametricIntegralForm`: pullback commutes with the integral of an
  integrable family.
* `TauCeti.integrable_family_apply`: a jointly continuous family over a compact parameter
  manifold with a finite measure is integrable at every point.
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

/-- The integral of a family of forms vanishes at a point where every form of the family
vanishes. -/
theorem parametricIntegralForm_apply_eq_zero {η : N → RoughForm I M F k} {x : M}
    (h : ∀ a, η a x = 0) : parametricIntegralForm μ η x = 0 := by
  -- The zero of the fibre at `x` is the zero of the model fibre.
  simp only [parametricIntegralForm_def, h]
  exact integral_zero N (E [⋀^Fin k]→L[ℝ] F)

/-- The integral of the zero family is zero. -/
@[simp]
theorem parametricIntegralForm_zero :
    parametricIntegralForm μ (fun _ : N ↦ (0 : RoughForm I M F k)) = 0 :=
  funext fun _ ↦ parametricIntegralForm_apply_eq_zero fun _ ↦ rfl

/-- The integral of the negated family is the negated integral. -/
@[simp]
theorem parametricIntegralForm_neg (η : N → RoughForm I M F k) :
    parametricIntegralForm μ (fun a ↦ -η a) = -parametricIntegralForm μ η :=
  funext fun x ↦ integral_neg fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x)

/-- The integral of a scaled family is the scaled integral. -/
@[simp]
theorem parametricIntegralForm_smul (c : ℝ) (η : N → RoughForm I M F k) :
    parametricIntegralForm μ (fun a ↦ c • η a) = c • parametricIntegralForm μ η :=
  funext fun x ↦ integral_smul c fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x)

/-- The integral of a sum of families integrable at every point is the sum of the integrals. -/
theorem parametricIntegralForm_add {η η' : N → RoughForm I M F k}
    (hη : ∀ x, Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x)) μ)
    (hη' : ∀ x, Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η' a x)) μ) :
    parametricIntegralForm μ (fun a ↦ η a + η' a) =
      parametricIntegralForm μ η + parametricIntegralForm μ η' :=
  funext fun x ↦ by
    have h := integral_add (hη x) (hη' x)
    exact h

/-- The integral of a difference of families integrable at every point is the difference of the
integrals. -/
theorem parametricIntegralForm_sub {η η' : N → RoughForm I M F k}
    (hη : ∀ x, Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x)) μ)
    (hη' : ∀ x, Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η' a x)) μ) :
    parametricIntegralForm μ (fun a ↦ η a - η' a) =
      parametricIntegralForm μ η - parametricIntegralForm μ η' :=
  funext fun x ↦ by
    have h := integral_sub (hη x) (hη' x)
    exact h

variable [CompleteSpace F]

/-- The integral of a constant family is the form scaled by the total mass. -/
@[simp]
theorem parametricIntegralForm_const (φ : RoughForm I M F k) :
    parametricIntegralForm μ (fun _ : N ↦ φ) = μ.real univ • φ :=
  funext fun x ↦ integral_const (E := E [⋀^Fin k]→L[ℝ] F) (φ x)

/-- The value of the integral of a family of forms integrable at `x` on tangent vectors at `x` is
the integral of the values. -/
theorem parametricIntegralForm_apply {η : N → RoughForm I M F k} {x : M}
    (hη : Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x)) μ)
    (v : Fin k → TangentSpace I x) :
    parametricIntegralForm μ η x v = ∫ a, η a x v ∂μ :=
  -- Evaluation at `v` is continuous linear on the model fibre, to which the fibre at `x` unfolds.
  ((ContinuousAlternatingMap.apply ℝ E F v).integral_comp_comm hη).symm

/-- Pulling back the integral of a family of forms along `f`, where the family is integrable at
every point of the image of `f`, gives the integral of the pulled-back forms. -/
theorem mpullback_parametricIntegralForm {E' H' M' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']
    {I' : ModelWithCorners ℝ E' H'} {η : N → RoughForm I M F k} {f : M' → M}
    (hη : ∀ y, Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a (f y))) μ) :
    mpullback I' I f (parametricIntegralForm μ η) =
      parametricIntegralForm μ fun a ↦ mpullback I' I f (η a) := by
  funext y
  -- Precomposition with the differential of `f` is continuous linear on the model fibres, so it
  -- commutes with the integral.
  rw [mpullback_apply_eq_compContinuousLinearMapCLM, parametricIntegralForm_def,
    parametricIntegralForm_def]
  let L : (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] E' [⋀^Fin k]→L[ℝ] F :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM (mfderiv I' I f y : E' →L[ℝ] E)
  refine (L.integral_comp_comm (hη y)).symm.trans
    (integral_congr_ae (Eventually.of_forall fun a ↦ ?_))
  exact (mpullback_apply_eq_compContinuousLinearMapCLM (I := I') f (η a) y).symm

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
theorem continuous_family_apply {η : N → RoughForm I M F k}
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
  simp only [Function.comp_apply, FiberBundle.trivializationAt_continuousAlternatingMap_apply_snd,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    Manifold.symmL_trivializationAt_self]
  -- The trivialization at `x` is the identity over `x`: both sides are `η b x v`, once the
  -- tangent space at `x` and the fibre `Trivial M F x` are unfolded to `E` and `F`.
  rfl

section Chart

variable [I.Boundaryless] [IsManifold I 2 M]

/-- On the chart target at `x`, the coordinate expressions of a jointly `C¹` family of forms are
jointly `C¹` in the chart coordinate and the parameter. -/
theorem contMDiffOn_inChartAt_family {η : N → RoughForm I M F k}
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
  have hbase : (extChartAt I x).symm q.1 ∈ (𝔱 x).baseSet := by
    rw [FiberBundle.trivializationAt_continuousAlternatingMap_baseSet]
    exact ⟨TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hq.1, mem_univ _⟩
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

/-- A jointly continuous family of forms over a compact parameter manifold with a finite measure
is integrable at every point. -/
theorem integrable_family_apply {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 0
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) :
    Integrable (fun a ↦ @id (E [⋀^Fin k]→L[ℝ] F) (η a x)) μ :=
  (continuous_family_apply hη x).integrable_of_hasCompactSupport (.of_compactSpace _)

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
  -- The forms take values in the fibres over `y`, which unfold to the model fibre on which `L`
  -- and the integral act.
  let L : (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] (E [⋀^Fin k]→L[ℝ] F) := (𝔱 x₀).continuousLinearMapAt ℝ y
  have hL (φ : TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) : ((𝔱 x₀) ⟨y, φ⟩).2 = L φ :=
    ((𝔱 x₀).continuousLinearMapAt_apply_of_mem (R := ℝ) hy φ).symm
  simp only [hL]
  exact (L.integral_comp_comm (integrable_family_apply hη y)).symm

/-- **Integrals of smooth families of forms are smooth.** If the family `η` of forms on a
boundaryless manifold `M`, indexed by a compact Hausdorff manifold `N` with a finite measure `μ`,
is jointly `C^n` in the parameter and the point, then its integral is a `C^n` form. -/
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

variable [I.Boundaryless] [IsManifold I 2 M] [IsManifold J 1 N]

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
    intro q hq
    -- Swap the variables to read `Φ` as a jointly `C¹` family of maps on `E` indexed by `N`.
    have hswap : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) 1
        (Function.uncurry fun (a : N) (z : E) ↦ Φ (z, a)) (q.2, q.1) :=
      (hΦ.contMDiffAt ((hT.prod isOpen_univ).mem_nhds hq)).comp (q.2, q.1)
        (contMDiffAt_snd.prodMk contMDiffAt_fst)
    have h := ((ContMDiffAt.fderiv_right hswap (n := 0) (by norm_num)).continuousAt).comp
      (f := Prod.swap) continuous_swap.continuousAt
    exact h.continuousWithinAt
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
    have hbase : (extChartAt I x).symm z ∈ (𝔱 x).baseSet := by
      rw [FiberBundle.trivializationAt_continuousAlternatingMap_baseSet]
      exact ⟨TangentBundle.extChartAt_symm_mem_trivializationAt_baseSet hz, mem_univ _⟩
    rw [RoughForm.inChartAt_eq_trivializationAt _ x hz,
      trivializationAt_parametricIntegralForm (hη.of_le zero_le) x hbase]
    exact integral_congr_ae (Eventually.of_forall fun a ↦
      (RoughForm.inChartAt_eq_trivializationAt _ x hz).symm)
  refine HasFDerivAt.congr_of_eventuallyEq ?_ hint
  simpa only [one_smul] using hasFDerivAt_integral_smul_of_continuousOn_fderiv (μ := μ)
    (g := fun _ ↦ (1 : ℝ)) (integrable_const _) hT hΦ.continuousOn hdiff hD hxT

/-- **Differentiation under the integral sign in a chart.** For a jointly `C¹` family `η` of
forms on a boundaryless `C²` manifold, indexed by a compact `C¹` manifold with a finite measure,
the coordinate expression in the chart at `x` of the integral of the family has, at the chart
point of `x`, the integral of the derivatives of the coordinate expressions as its derivative. -/
theorem hasFDerivAt_inChartAt_parametricIntegralForm {η : N → RoughForm I M F k}
    (hη : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun p : N × M ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y : M ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] Trivial M F y) p.2 (η p.1 p.2)))
    (x : M) :
    HasFDerivAt ((parametricIntegralForm μ η).inChartAt x)
      (∫ a, fderiv ℝ ((η a).inChartAt x) (extChartAt I x x) ∂μ) (extChartAt I x x) :=
  (integrable_fderiv_inChartAt_and_hasFDerivAt hη x).2

/-- **Exterior differentiation under the integral sign.** For a jointly `C¹` family `η` of forms on
a boundaryless `C²` manifold, indexed by a compact `C¹` manifold with a finite measure,
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
