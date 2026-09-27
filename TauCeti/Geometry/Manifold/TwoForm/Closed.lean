/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Const
public import TauCeti.Geometry.Manifold.TwoForm.Basic
import TauCeti.Analysis.Normed.Module.Alternating.Bilinear

/-!
# Closed smooth two-forms on manifolds

Mathlib defines the exterior derivative `extDerivWithin` of a differential form on a normed
space, and proves that it commutes with pullback along `C²` maps. This file uses it to say when a
smooth two-form `form : SmoothTwoForm I M` on a manifold is **closed**.

The two-form is first read in the preferred extended chart `extChartAt I x₀` at a point `x₀`:
`form.inChartAt x₀` is the differential two-form on the model space `E` whose value at a chart
coordinate `z` is the value of `form` at `(extChartAt I x₀).symm z`, pulled back along the
inverse of the canonical tangent-bundle trivialization at `x₀`. In other words, tangent vectors at
`(extChartAt I x₀).symm z` are fed to `form` in the coordinates of the chart at `x₀`. This
coordinate expression is smooth on the chart target, and the expressions in two charts differ by
pullback along the change of coordinates (`inChartAt_eq_compContinuousLinearMap`), so their
exterior derivatives are related by the same pullback (`extDerivWithin_inChartAt_eq`).

`form.IsClosed` asks that every coordinate expression have vanishing exterior derivative, within
`range I`, at every point of its chart target. The pullback relation shows that this is equivalent
to checking each chart at its own centre only
(`isClosed_iff_forall_extDerivWithin_inChartAt_self`), which is the statement that closedness is a
pointwise, chart-independent condition. On the model
space itself it is the vanishing of Mathlib's exterior derivative of the two-form
(`isClosed_iff_extDeriv_altAt`); in particular every constant two-form is closed. Closed forms are
stable under sums, negation, and real scalar multiples.

## Main declarations

* `TauCeti.SmoothTwoForm.inChartAt`: the coordinate expression of a smooth two-form in the
  preferred chart at a point.
* `TauCeti.SmoothTwoForm.contDiffWithinAt_inChartAt`: the coordinate expression is smooth on the
  chart target.
* `TauCeti.SmoothTwoForm.inChartAt_eq_compContinuousLinearMap` and
  `TauCeti.SmoothTwoForm.extDerivWithin_inChartAt_eq`: change of chart is pullback, for the form
  and for its exterior derivative.
* `TauCeti.SmoothTwoForm.IsClosed`: a smooth two-form is closed.
* `TauCeti.SmoothTwoForm.isClosed_iff_forall_extDerivWithin_inChartAt_self`: closedness is
  checked at the centre of each chart.
* `TauCeti.SmoothTwoForm.isClosed_iff_extDeriv_altAt` and `TauCeti.SmoothTwoForm.isClosed_const`:
  closedness on a normed space is the vanishing of the exterior derivative, and constant two-forms
  are closed.
* `TauCeti.SmoothTwoForm.IsClosed.add`, `IsClosed.neg`, `IsClosed.smul`, `IsClosed.sub` and
  `TauCeti.SmoothTwoForm.isClosed_zero`: closed forms are a real subspace.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2.
-/

public section

open Bundle Set Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace SmoothTwoForm

variable (form : SmoothTwoForm I M)

/-! ### The coordinate expression in a chart -/

/-- The coordinate expression of a smooth two-form in the preferred chart at `x₀`: at the chart
coordinate `z`, it is the value of the form at the point `y = (extChartAt I x₀).symm z`, composed
with the tangent coordinate change `tangentCoordChange I x₀ y y` from the chart at `x₀` to the
chart at `y`. Thus tangent vectors at `y` are fed to the form in the coordinates of the chart at
`x₀`. Outside the chart target the value is junk. -/
def inChartAt (x₀ : M) (z : E) : E [⋀^Fin 2]→L[ℝ] ℝ :=
  (form.altAt ((extChartAt I x₀).symm z)).compContinuousLinearMap
    (tangentCoordChange I x₀ ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z))

lemma inChartAt_apply (x₀ : M) (z : E) (v : Fin 2 → E) :
    form.inChartAt x₀ z v =
      form ((extChartAt I x₀).symm z)
        (tangentCoordChange I x₀ ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z) (v 0))
        (tangentCoordChange I x₀ ((extChartAt I x₀).symm z) ((extChartAt I x₀).symm z) (v 1)) := by
  rw [inChartAt]
  exact form.altAt_apply _ _

/-- At the centre of its chart, the coordinate expression of a two-form is its value there. -/
lemma inChartAt_extChartAt_self (x : M) : form.inChartAt x (extChartAt I x x) = form.altAt x := by
  ext v
  rw [inChartAt_apply, extChartAt_to_inv, altAt_apply]
  simp only [tangentCoordChange_self (mem_extChartAt_source x)]

@[simp]
lemma inChartAt_zero (x₀ : M) : (0 : SmoothTwoForm I M).inChartAt x₀ = 0 := by
  ext z v
  rw [inChartAt_apply, Pi.zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  exact zero_apply _ _ _

@[simp]
lemma inChartAt_add (form' : SmoothTwoForm I M) (x₀ : M) :
    (form + form').inChartAt x₀ = form.inChartAt x₀ + form'.inChartAt x₀ := by
  ext z v
  rw [Pi.add_apply, ContinuousAlternatingMap.add_apply, inChartAt_apply, inChartAt_apply,
    inChartAt_apply]
  exact add_apply form form' _ _ _

@[simp]
lemma inChartAt_neg (x₀ : M) : (-form).inChartAt x₀ = -form.inChartAt x₀ := by
  ext z v
  rw [Pi.neg_apply, ContinuousAlternatingMap.neg_apply, inChartAt_apply, inChartAt_apply]
  exact neg_apply form _ _ _

@[simp]
lemma inChartAt_sub (form' : SmoothTwoForm I M) (x₀ : M) :
    (form - form').inChartAt x₀ = form.inChartAt x₀ - form'.inChartAt x₀ := by
  ext z v
  rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, inChartAt_apply, inChartAt_apply,
    inChartAt_apply]
  exact sub_apply form form' _ _ _

@[simp]
lemma inChartAt_smul (c : ℝ) (x₀ : M) : (c • form).inChartAt x₀ = c • form.inChartAt x₀ := by
  ext z v
  rw [Pi.smul_apply, ContinuousAlternatingMap.smul_apply, inChartAt_apply, inChartAt_apply,
    smul_eq_mul]
  exact smul_apply c form _ _ _

/-- On a normed space with its self model, the coordinate expression of a two-form is the form
itself. -/
@[simp]
lemma inChartAt_modelSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (form : SmoothTwoForm 𝓘(ℝ, V) V) (x₀ : V) : form.inChartAt x₀ = form.altAt := by
  ext z v
  rw [inChartAt_apply, altAt_apply, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id]
  simp only [TangentBundle.coordChange_model_space, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_apply]

/-! ### Change of chart -/

/-- Read in two charts, a two-form transforms by pullback along the change of coordinates: at a
coordinate `z` of the chart at `x₀` whose point lies in the chart at `x`, the expression in the
chart at `x₀` is the expression in the chart at `x` at the corresponding coordinate, composed with
the derivative of the change of coordinates. -/
theorem inChartAt_eq_compContinuousLinearMap {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target) (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    form.inChartAt x₀ z =
      (form.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
  have hy₀ : (extChartAt I x₀).symm z ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hz
  -- the derivative of the change of coordinates is the tangent coordinate change at the point
  have hD : fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z =
      tangentCoordChange I x₀ x ((extChartAt I x₀).symm z) := by
    rw [tangentCoordChange_def, (extChartAt I x₀).right_inv hz]
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, inChartAt_apply, inChartAt_apply,
    (extChartAt I x).left_inv hx, hD]
  -- the cocycle identity for tangent coordinate changes
  simp only [Function.comp_apply,
    tangentCoordChange_comp ⟨⟨hy₀, hx⟩, mem_extChartAt_source ((extChartAt I x₀).symm z)⟩]

/-! ### Smoothness of the coordinate expression -/

/-- In the hom-bundle trivialization at `x₀`, the fibre component of the bilinear section
underlying `form` at a point `y` of the chart source is the bilinear form transported along the
inverse tangent trivialization. -/
private lemma trivializationAt_toContMDiffSection_snd_apply (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) (v w : E) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun b : M ↦ TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀
        ⟨y, form.toContMDiffSection y⟩).2 v w =
      form y (tangentCoordChange I x₀ y y v) (tangentCoordChange I x₀ y y w) := by
  have hhom : y ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun b : M ↦ TangentSpace I b →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨by simpa using hy, by simp⟩
  rw [hom_trivializationAt_apply]
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.continuousLinearMapAt_apply, Trivialization.coe_linearMapAt_of_mem _ hhom,
    hom_trivializationAt_apply, Trivial.fiberBundle_trivializationAt',
    Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  -- `tangentCoordChange` is by definition this coordinate change of the tangent bundle core
  rfl

/-- On the chart source, the coordinate expression of `form` composed with the chart is half the
alternatization of the fibre component of the hom-bundle trivialization of its bilinear section,
through the continuous linear map `(2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ`;
this is the identity through which smoothness of the section is transferred. -/
private lemma inChartAt_extChartAt_eq_smul_alternatizeBilinCLM (x₀ : M) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    form.inChartAt x₀ (extChartAt I x₀ y) =
      ((2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ)
        ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun b : M ↦ TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀
            ⟨y, form.toContMDiffSection y⟩).2) := by
  have hy' : y ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  ext v
  rw [_root_.smul_apply, ContinuousAlternatingMap.smul_apply,
    ContinuousAlternatingMap.alternatizeBilinCLM_apply, smul_eq_mul,
    form.trivializationAt_toContMDiffSection_snd_apply x₀ hy,
    form.trivializationAt_toContMDiffSection_snd_apply x₀ hy, inChartAt_apply,
    (extChartAt I x₀).left_inv hy']
  -- antisymmetry of the alternating form; the evaluation lemma is instantiated by hand because
  -- its arguments are read as vectors of the model space `E` rather than of the tangent space
  set a := tangentCoordChange I x₀ y y (v 0)
  set b := tangentCoordChange I x₀ y y (v 1)
  have hneg := (form.isAlt_bilinFormAt y).neg_eq b a
  rw [bilinFormAt_apply form y b a, bilinFormAt_apply form y a b] at hneg
  rw [← hneg]
  ring

/-- The coordinate expression of a smooth two-form, composed with the chart, is smooth on the
chart source. -/
theorem contMDiffAt_inChartAt_comp_extChartAt (x₀ : M) {y : M}
    (hy : y ∈ (extChartAt I x₀).source) :
    ContMDiffAt I 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ) ∞
      (fun y' ↦ form.inChartAt x₀ (extChartAt I x₀ y')) y := by
  have hy' : y ∈ (chartAt H x₀).source := by rwa [← extChartAt_source I]
  have hbase : y ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun b : M ↦ TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    exact ⟨by simpa using hy', by simpa using hy'⟩
  have hsec := (Trivialization.contMDiffAt_section_iff (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun b : M ↦ TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ) x₀) hbase).1
    (form.toContMDiffSection.contMDiff y)
  refine (((2⁻¹ : ℝ) • ContinuousAlternatingMap.alternatizeBilinCLM ℝ E ℝ).contMDiffAt.comp y
    hsec).congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds' hy] with y' hy''
  exact form.inChartAt_extChartAt_eq_smul_alternatizeBilinCLM x₀ (by rwa [← extChartAt_source I])

/-- The coordinate expression of a smooth two-form is smooth, within `range I`, at every point of
the chart target. -/
theorem contDiffWithinAt_inChartAt (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt ℝ ∞ (form.inChartAt x₀) (range I) z := by
  have hcomp := (form.contMDiffAt_inChartAt_comp_extChartAt x₀
    ((extChartAt I x₀).map_target hz)).comp_contMDiffWithinAt z
      (contMDiffWithinAt_extChartAt_symm_range x₀ hz)
  refine (hcomp.congr_of_eventuallyEq ?_ ?_).contDiffWithinAt
  · filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with z' hz'
    rw [Function.comp_apply, (extChartAt I x₀).right_inv hz']
  · rw [Function.comp_apply, (extChartAt I x₀).right_inv hz]

/-- The coordinate expression of a smooth two-form is differentiable, within `range I`, at every
point of the chart target. -/
theorem differentiableWithinAt_inChartAt (x₀ : M) {z : E} (hz : z ∈ (extChartAt I x₀).target) :
    DifferentiableWithinAt ℝ (form.inChartAt x₀) (range I) z :=
  (form.contDiffWithinAt_inChartAt x₀ hz).differentiableWithinAt (by simp)

/-- **Change of chart for the exterior derivative.** The exterior derivative of the coordinate
expression in the chart at `x₀` is the pullback, along the change of coordinates, of the exterior
derivative of the coordinate expression in the chart at `x`. -/
theorem extDerivWithin_inChartAt_eq {x₀ x : M} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    extDerivWithin (form.inChartAt x₀) (range I) z =
      (extDerivWithin (form.inChartAt x) (range I)
        (extChartAt I x ((extChartAt I x₀).symm z))).compContinuousLinearMap
          (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
  have hzr : z ∈ range I := extChartAt_target_subset_range x₀ hz
  -- the coordinate expressions agree, as forms, near `z` within `range I`
  have heq : form.inChartAt x₀ =ᶠ[𝓝[range I] z] fun ζ ↦
      (form.inChartAt x (extChartAt I x ((extChartAt I x₀).symm ζ))).compContinuousLinearMap
        (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) ζ) := by
    have h₁ : (extChartAt I x₀).target ∈ 𝓝[range I] z := extChartAt_target_mem_nhdsWithin_of_mem hz
    have h₂ : (extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝[range I] z :=
      (continuousAt_extChartAt_symm'' hz).continuousWithinAt.preimage_mem_nhdsWithin
        (extChartAt_source_mem_nhds' hx)
    filter_upwards [h₁, h₂] with ζ hζ hζx
    exact form.inChartAt_eq_compContinuousLinearMap hζ hζx
  rw [heq.extDerivWithin_eq (heq.self_of_nhdsWithin hzr)]
  refine extDerivWithin_pullback (r := ∞) (form.differentiableWithinAt_inChartAt x
    ((extChartAt I x).map_source hx)) (contDiffWithinAt_ext_coord_change x x₀ ?_) (by simp)
    I.uniqueDiffOn (I.range_subset_closure_interior hzr) hzr fun ζ _ ↦ ?_
  · rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hz, hx⟩
  · rw [extChartAt_coe, Function.comp_apply]
    exact mem_range_self _

/-! ### Closed two-forms -/

/-- A smooth two-form is **closed** when its coordinate expression in every preferred chart has
vanishing exterior derivative, within the model range, at every point of the chart target. By
`isClosed_iff_forall_extDerivWithin_inChartAt_self`, it suffices to check each chart at its
centre. -/
def IsClosed : Prop :=
  ∀ x₀ : M, ∀ z ∈ (extChartAt I x₀).target, extDerivWithin (form.inChartAt x₀) (range I) z = 0

variable {form}

/-- **Closedness is a pointwise, chart-independent condition**: a smooth two-form is closed as soon
as, at every point, the exterior derivative of its coordinate expression in the chart centred at
that point vanishes there. -/
theorem isClosed_iff_forall_extDerivWithin_inChartAt_self :
    form.IsClosed ↔
      ∀ x : M, extDerivWithin (form.inChartAt x) (range I) (extChartAt I x x) = 0 := by
  refine ⟨fun h x ↦ h x _ (mem_extChartAt_target x), fun h x₀ z hz ↦ ?_⟩
  rw [form.extDerivWithin_inChartAt_eq hz (mem_extChartAt_source ((extChartAt I x₀).symm z)), h]
  ext v
  simp

/-- Closedness of a smooth two-form, when the model has no boundary: the exterior derivative of
every coordinate expression vanishes on its chart target. -/
theorem isClosed_iff_extDeriv [I.Boundaryless] :
    form.IsClosed ↔
      ∀ x₀ : M, ∀ z ∈ (extChartAt I x₀).target, extDeriv (form.inChartAt x₀) z = 0 := by
  simp only [IsClosed, I.range_eq_univ, extDerivWithin_univ]

/-- On a normed space with its self model, a smooth two-form is closed exactly when Mathlib's
exterior derivative of its pointwise alternating form vanishes everywhere. -/
theorem isClosed_iff_extDeriv_altAt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {form : SmoothTwoForm 𝓘(ℝ, V) V} :
    form.IsClosed ↔ ∀ x : V, extDeriv form.altAt x = 0 := by
  simp only [isClosed_iff_forall_extDerivWithin_inChartAt_self, inChartAt_modelSpace,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id, modelWithCornersSelf_coe,
    range_id, extDerivWithin_univ]

/-- A constant two-form on a normed space is closed. -/
theorem isClosed_const {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ v, B v v = 0) : (const B hB).IsClosed := by
  rw [isClosed_iff_extDeriv_altAt]
  intro x
  have h : ∀ (y : V) (v : Fin 2 → V), (const B hB).altAt y v = B (v 0) (v 1) := fun y v ↦
    (altAt_apply _ y v).trans <| congrArg (fun B' : V →L[ℝ] V →L[ℝ] ℝ ↦ B' (v 0) (v 1))
      (const_toContMDiffSection_apply B hB y)
  have : (const B hB).altAt = fun _ ↦ (const B hB).altAt x := by
    ext y v
    rw [h, h]
  rw [this, ContinuousAlternatingMap.extDeriv_const]

/-- The zero two-form is closed. -/
theorem isClosed_zero : (0 : SmoothTwoForm I M).IsClosed := by
  intro x₀ z hz
  rw [inChartAt_zero]
  exact ContinuousAlternatingMap.extDerivWithin_const 0 _ z

/-- The sum of two closed two-forms is closed. -/
theorem IsClosed.add {form' : SmoothTwoForm I M} (h : form.IsClosed) (h' : form'.IsClosed) :
    (form + form').IsClosed := by
  intro x₀ z hz
  rw [inChartAt_add, extDerivWithin_add (I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ hz))
    (form.differentiableWithinAt_inChartAt x₀ hz) (form'.differentiableWithinAt_inChartAt x₀ hz),
    h x₀ z hz, h' x₀ z hz, add_zero]

/-- A real scalar multiple of a closed two-form is closed. -/
theorem IsClosed.smul (c : ℝ) (h : form.IsClosed) : (c • form).IsClosed := by
  intro x₀ z hz
  rw [inChartAt_smul,
    extDerivWithin_smul _ _ (I.uniqueDiffOn _ (extChartAt_target_subset_range x₀ hz)),
    h x₀ z hz, smul_zero]

/-- The negative of a closed two-form is closed. -/
theorem IsClosed.neg (h : form.IsClosed) : (-form).IsClosed := by
  rw [← neg_one_smul ℝ form]
  exact h.smul (-1)

/-- The difference of two closed two-forms is closed. -/
theorem IsClosed.sub {form' : SmoothTwoForm I M} (h : form.IsClosed) (h' : form'.IsClosed) :
    (form - form').IsClosed := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

end SmoothTwoForm

end TauCeti

end
