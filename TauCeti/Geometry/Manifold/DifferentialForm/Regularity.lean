/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Analysis.Calculus.DifferentialForm.Regularity
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap

/-!
# Regularity of differential forms in charts

The fibre coordinate of a fixed-coefficient form in the alternating-map bundle is its pullback
along the inverse extended chart. This transfers smooth-section regularity to the flat
regularity needed for exterior differentiation, including within subsets at boundary points.

Conversely, flat regularity of a coordinate expression gives regularity of the section. The
manifold exterior derivative takes
`C^p` sections to `C^n` sections whenever `n + 1 ≤ p`, on any manifold of class `C²` over any
model with corners.
In particular it maps smooth `k`-forms to smooth `(k+1)`-forms. A form supported compactly inside
a chart extends by zero with the same regularity within the model range, and exterior
differentiation commutes with this extension.

## Main declarations

* `TauCeti.RoughForm.contDiffWithinAt_inChartAt`: a `C^n` section has `C^n` chart expressions.
* `TauCeti.contMDiffOn_mextDerivWithin`, `TauCeti.isSmoothBundleForm_mextDeriv`: the exterior
  derivative lowers regularity by one.
* `TauCeti.mextDeriv_mem_smoothForms`: the exterior derivative preserves smooth forms.
* `TauCeti.mextDerivₗ`: the exterior derivative as a linear map on smooth fixed-coefficient forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
* Mathlib's alternating-bundle coordinates (`ContinuousAlternatingMap.inCoordinates`) and
  inverse tangent coordinates (`TangentBundle.symmL_trivializationAt`).
-/

public section

noncomputable section

open Set Filter Bundle
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

namespace RoughForm

/-- The alternating-bundle fibre coordinate of a form is its inverse-chart pullback. -/
theorem inCoordinates_eq_inChartAt [IsManifold I 1 M] (φ : RoughForm I M F k)
    {x₀ x : M} (hx : x ∈ (extChartAt I x₀).source) :
    ContinuousAlternatingMap.inCoordinates E F x₀ x x₀ x (φ x) =
      φ.inChartAt x₀ (extChartAt I x₀ x) := by
  simp only [ContinuousAlternatingMap.inCoordinates,
    Bundle.Trivial.eq_trivialization M F (trivializationAt F (Trivial M F) x₀),
    Bundle.Trivial.continuousLinearMapAt_trivialization]
  ext v
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, inChartAt_apply]
  simp only [Function.comp_apply, ContinuousLinearMap.id_apply]
  rw [TangentBundle.symmL_trivializationAt (by simpa only [extChartAt_source] using hx)]
  -- The model tangent fibre is canonically E; evaluate before identifying the base point.
  change φ x (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm
      (range I) (extChartAt I x₀ x) (v i)) = _
  rw [(extChartAt I x₀).left_inv hx]

/-- A differentiable section has a differentiable coordinate expression in the preferred chart,
with derivatives taken within the inverse image of the subset intersected with the model range. -/
theorem differentiableWithinAt_inChartAt [IsManifold I 1 M]
    (φ : RoughForm I M F k) {s : Set M} {x : M}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s x) :
    DifferentiableWithinAt ℝ (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) := by
  have hc := (mdifferentiableWithinAt_section I φ).mp hφ
  have hflat := hc.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.comp_def, id_eq,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply] at hflat
  have heq : (fun z ↦ ContinuousAlternatingMap.inCoordinates E F x
      ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
        (φ ((extChartAt I x).symm z))) =ᶠ[𝓝[range I] (extChartAt I x x)] φ.inChartAt x := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    rw [φ.inCoordinates_eq_inChartAt ((extChartAt I x).map_target hz),
      (extChartAt I x).right_inv hz]
  exact hflat.congr_of_eventuallyEq (heq.symm.filter_mono (nhdsWithin_mono _ inter_subset_right))
    (by
      rw [extChartAt_to_inv]
      exact (φ.inCoordinates_eq_inChartAt (mem_extChartAt_source x)).symm)

/-- Section regularity within a subset implies flat regularity in the chart centred at the
point. The derivative set is the inverse image of the subset intersected with the model range. -/
theorem contDiffWithinAt_inChartAt [IsManifold I 1 M] {n : WithTop ℕ∞}
    (φ : RoughForm I M F k) {s : Set M} {x : M}
    (hφ : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s x) :
    ContDiffWithinAt ℝ n (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) := by
  have hc := contMDiffWithinAt_section.mp hφ
  rw [contMDiffWithinAt_iff] at hc
  have hflat := hc.2
  simp only [extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.comp_def, id_eq,
    FiberBundle.trivializationAt_continuousAlternatingMap_apply]
    at hflat
  have heq : (fun z ↦ ContinuousAlternatingMap.inCoordinates E F x
      ((extChartAt I x).symm z) x ((extChartAt I x).symm z)
        (φ ((extChartAt I x).symm z))) =ᶠ[𝓝[range I] (extChartAt I x x)] φ.inChartAt x := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with z hz
    rw [φ.inCoordinates_eq_inChartAt ((extChartAt I x).map_target hz),
      (extChartAt I x).right_inv hz]
  exact hflat.congr_of_eventuallyEq (heq.symm.filter_mono (nhdsWithin_mono _ inter_subset_right))
    (by
      rw [extChartAt_to_inv]
      exact (φ.inCoordinates_eq_inChartAt (mem_extChartAt_source x)).symm)

/-- Near the chart point, the coordinate expression of `mextDerivWithin φ s` in the chart centred
at `x` is the flat exterior derivative of the coordinate expression of `φ` within the coordinate
set. The form is `C¹` as a section on `s`, which has unique derivatives and is contained in the
closure of its interior. -/
theorem inChartAt_mextDerivWithin_eventuallyEq [IsManifold I 2 M] (φ : RoughForm I M F k)
    {s : Set M}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s)
    (hs : UniqueMDiffOn I s) (hsc : s ⊆ closure (interior s)) (x : M) :
    RoughForm.inChartAt (I := I) (mextDerivWithin φ s) x
      =ᶠ[𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x x)]
        extDerivWithin (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I) := by
  filter_upwards [nhdsWithin_mono _ inter_subset_right
    (extChartAt_target_mem_nhdsWithin (I := I) x), self_mem_nhdsWithin] with z hz hzt
  exact φ.inChartAt_mextDerivWithin hs hz hzt.1 (hsc hzt.1)
    ((φ.contDiffWithinAt_inChartAt (hφ _ hzt.1)).differentiableWithinAt one_ne_zero)

end RoughForm

/-- The exterior derivative within a subset costs one derivative: if `φ` is a `C^(n+1)` section on
`s`, then `mextDerivWithin φ s` is a `C^n` section on `s`. The subset has unique derivatives and is
contained in the closure of its interior; it may contain boundary and corner points. -/
theorem contMDiffOn_mextDerivWithin [IsManifold I 2 M] (φ : RoughForm I M F k) {s : Set M}
    {n : WithTop ℕ∞}
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) (n + 1)
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s)
    (hs : UniqueMDiffOn I s) (hsc : s ⊆ closure (interior s)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (mextDerivWithin φ s y)) s := by
  intro x hx
  let t : Set E := (extChartAt I x).symm ⁻¹' s ∩ range I
  let a : Set E := (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target
  have hxs : (extChartAt I x).symm (extChartAt I x x) ∈ s := by
    simpa only [extChartAt_to_inv] using hx
  have hta : t =ᶠ[𝓝 (extChartAt I x x)] a := by
    filter_upwards [extChartAt_target_eventuallyEqSet_of_mem (mem_extChartAt_target (I := I) x)]
      with z hz
    simp only [t, a, mem_inter_iff, hz]
  -- The flat exterior derivative is `C^n` on the chart image of `s`, which has unique derivatives.
  have ha : ContDiffWithinAt ℝ n (extDerivWithin (φ.inChartAt x) a) a (extChartAt I x x) :=
    contDiffWithinAt_extDerivWithin ((φ.contDiffWithinAt_inChartAt (hφ x hx)).mono
        (inter_subset_inter_right _ (extChartAt_target_subset_range x)))
      (by simpa only [a, inter_comm] using hs.uniqueDiffOn_target_inter x) le_rfl
      ⟨hxs, mem_extChartAt_target x⟩
  have ht : ContDiffWithinAt ℝ n (extDerivWithin (φ.inChartAt x) t) t (extChartAt I x x) := by
    rw [contDiffWithinAt_congr_set hta]
    refine ha.congr_of_eventuallyEq_of_mem ?_ ⟨hxs, mem_extChartAt_target x⟩
    filter_upwards [nhdsWithin_le_nhds hta.eventuallyEq_nhds] with z hz
    exact extDerivWithin_congr_set hz
  -- Read the section in the bundle chart at `x`; there it is the coordinate expression above.
  rw [contMDiffWithinAt_section, contMDiffWithinAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt]
  refine ht.congr_of_eventuallyEq_of_mem ?_ ⟨hxs, mem_range_self _⟩
  filter_upwards [φ.inChartAt_mextDerivWithin_eventuallyEq (hφ.of_le le_add_self) hs hsc x,
    nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin (I := I) x)]
    with z hz hzT
  simp only [Function.comp_apply, FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  rw [RoughForm.inCoordinates_eq_inChartAt _ ((extChartAt I x).map_target hzT),
    (extChartAt I x).right_inv hzT, hz]

/-- The exterior derivative takes `C^p` fixed-coefficient forms to `C^n` forms when `n + 1 ≤ p`,
including infinite regularity, over any model with corners. -/
theorem isSmoothBundleForm_mextDeriv [IsManifold I 2 M] {p n : WithTop ℕ∞}
    (φ : RoughForm I M F k)
    (hφ : IsSmoothBundleForm (I := I) (F := F) (V := Trivial M F) p φ)
    (hnp : n + 1 ≤ p) :
    IsSmoothBundleForm (I := I) (F := F) (V := Trivial M F) n (mextDeriv φ) := by
  rw [isSmoothBundleForm_def] at hφ ⊢
  simp only [← mextDerivWithin_univ, ← contMDiffOn_univ]
  exact contMDiffOn_mextDerivWithin φ (hφ.of_le hnp).contMDiffOn
    (uniqueMDiffOn_univ (I := I)) (by simp)

/-- The exterior derivative of a `C¹` form is a continuous section. -/
theorem IsSmoothForm.continuous_mextDeriv [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) :
    IsSmoothForm I 0 (mextDeriv φ) := by
  rw [isSmoothForm_def]
  exact (isSmoothBundleForm_def 0 _).mp
    (isSmoothBundleForm_mextDeriv φ ((isSmoothBundleForm_def 1 _).mpr hφ.contMDiff)
      (n := 0) (by simp))

/-- The exterior derivative of a smooth fixed-coefficient form is smooth. -/
theorem mextDeriv_mem_smoothForms [IsManifold I 2 M] {φ : RoughForm I M F k}
    (hφ : φ ∈ smoothForms I M F k) : mextDeriv φ ∈ smoothForms I M F (k + 1) :=
  mem_smoothForms.mpr <| isSmoothBundleForm_mextDeriv (n := ∞) φ
    (mem_smoothForms.mp hφ) (by simp)

section Regularity

/-- In the form's own preferred chart, its section regularity is its coordinate regularity
within the model range at the chart center. -/
theorem IsSmoothForm.contDiffWithinAt_inChartAt_self [IsManifold I 1 M]
    {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) (x : M) :
    ContDiffWithinAt ℝ n (φ.inChartAt x) (range I) (extChartAt I x x) := by
  have hc := φ.contDiffWithinAt_inChartAt (s := univ)
    (hφ.contMDiff x).contMDiffWithinAt
  simpa only [preimage_univ, univ_inter] using hc

/-- Exterior differentiation commutes with finite sums of C1 forms. The differentiability
hypotheses ensure additivity of the coordinate derivatives. -/
theorem mextDeriv_sum [IsManifold I 1 M] {ι : Type*}
    (φ : ι → RoughForm I M F k) (s : Finset ι) (hφ : ∀ i ∈ s, IsSmoothForm I 1 (φ i)) :
    TauCeti.mextDeriv (∑ i ∈ s, φ i) = ∑ i ∈ s, TauCeti.mextDeriv (φ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hrest := fun j hj ↦ hφ j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    funext x
    have hi' := (hφ i (Finset.mem_insert_self i s)).contDiffWithinAt_inChartAt_self x
    have hs' := (IsSmoothForm.sum φ s hrest).contDiffWithinAt_inChartAt_self x
    rw [TauCeti.mextDeriv_add
      (hi'.differentiableWithinAt one_ne_zero) (hs'.differentiableWithinAt one_ne_zero)]
    exact congrArg (fun ψ : RoughForm I M F (k + 1) ↦ TauCeti.mextDeriv (φ i) x + ψ x)
      (ih hrest)

/-- A C1 form has C1 coefficients at every point of each preferred chart target on a C2
manifold. The coordinate cocycle transports both the form and the chart derivative. -/
theorem IsSmoothForm.contDiffWithinAt_inChartAt [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    ContDiffWithinAt ℝ 1 (φ.inChartAt α) (range I) z := by
  let y := (extChartAt I α).symm z
  let T := extChartAt I y ∘ (extChartAt I α).symm
  have hzr : z ∈ range I := extChartAt_target_subset_range α hz
  have hsource : z ∈ ((extChartAt I α).symm ≫ extChartAt I y).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hz, mem_extChartAt_source y⟩
  have hT : ContDiffWithinAt ℝ 2 T (range I) z :=
    contDiffWithinAt_ext_coord_change y α hsource
  have hmap : MapsTo T (range I) (range I) := fun ζ _ ↦
    ⟨chartAt H y ((extChartAt I α).symm ζ), rfl⟩
  have hcomp := (hφ.contDiffWithinAt_inChartAt_self y).comp z (hT.of_le (by norm_num)) hmap
  have hD := hT.fderivWithin_right I.uniqueDiffOn (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2) hzr
  have hp := ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (ι := Fin k) (G := F) 1).comp_contDiffWithinAt hD).clm_apply hcomp
  have heq : φ.inChartAt α =ᶠ[𝓝[range I] z] fun ζ ↦
      (φ.inChartAt y (T ζ)).compContinuousLinearMap (fderivWithin ℝ T (range I) ζ) := by
    have h₁ := extChartAt_target_mem_nhdsWithin_of_mem hz
    have h₂ : (extChartAt I α).symm ⁻¹' (extChartAt I y).source ∈ 𝓝[range I] z :=
      (continuousAt_extChartAt_symm'' hz).continuousWithinAt.preimage_mem_nhdsWithin
        (extChartAt_source_mem_nhds' (mem_extChartAt_source y))
    filter_upwards [h₁, h₂] with ζ hζ hζy
    exact φ.inChartAt_eq_compContinuousLinearMap hζ hζy
  exact hp.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hzr)

/-- On a `C²` manifold, the actual exterior derivative read in any preferred chart is the
flat exterior derivative of the original coordinate expression. -/
theorem IsSmoothForm.inChartAt_mextDeriv_eq [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    (TauCeti.mextDeriv φ).inChartAt α z = extDerivWithin (φ.inChartAt α) (range I) z :=
  φ.inChartAt_mextDeriv hz
    ((hφ.contDiffWithinAt_inChartAt_self _).differentiableWithinAt one_ne_zero)

/-- Regularity of the coordinate expression in each point's own preferred chart implies
regularity of the differential-form section. -/
theorem IsSmoothForm.of_contDiffWithinAt_inChartAt_self [IsManifold I 1 M]
    {r : WithTop ℕ∞} {φ : RoughForm I M F k}
    (hφ : ∀ x, ContDiffWithinAt ℝ r (φ.inChartAt x) (range I) (extChartAt I x x)) :
    IsSmoothForm I r φ := by
  rw [isSmoothForm_def]
  intro x
  rw [contMDiffAt_section x, contMDiffAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt]
  have heq : (fun z ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
      (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x
        ⟨(extChartAt I x).symm z, φ ((extChartAt I x).symm z)⟩).2) =ᶠ[
          𝓝[range I] (extChartAt I x x)] φ.inChartAt x := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
    exact (φ.inChartAt_eq_trivializationAt x hz).symm
  exact (hφ x).congr_of_eventuallyEq heq (heq.self_of_nhdsWithin
    (extChartAt_target_subset_range x (mem_extChartAt_target x)))

end Regularity

/-- Every zero-dimensional form is smooth: its coordinate functions have singleton domain. -/
theorem isSmoothForm_zeroDim {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Subsingleton E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) 1 M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {n : WithTop ℕ∞}
    (φ : RoughForm 𝓘(ℝ, E) M F k) :
    IsSmoothForm 𝓘(ℝ, E) n φ := by
  rw [isSmoothForm_def]
  intro x
  rw [Bundle.contMDiffAt_section x, contMDiffAt_iff_source,
    contMDiffWithinAt_iff_contDiffWithinAt]
  have hflat (f : E →
      E [⋀^Fin k]→L[ℝ] F)
      (s : Set (E)) (z : E) :
      ContDiffWithinAt ℝ n f s z := by
    have he : f = fun _ ↦ f 0 := funext fun y ↦ congrArg f (Subsingleton.elim y 0)
    rw [he]
    exact contDiffWithinAt_const
  exact hflat _ _ _

variable (I) in
/-- The exterior derivative as a real linear map on smooth fixed-coefficient forms. -/
def mextDerivₗ [IsManifold I 2 M] (k : ℕ) :
    SmoothForm I M F k →ₗ[ℝ] SmoothForm I M F (k + 1) where
  toFun φ := ⟨mextDeriv φ.1, mextDeriv_mem_smoothForms φ.2⟩
  map_add' φ ψ := by
    apply Subtype.ext
    funext x
    apply mextDeriv_add
    · simpa using φ.1.differentiableWithinAt_inChartAt (s := Set.univ) (x := x)
        (((isSmoothBundleForm_def ∞ φ.1).mp (mem_smoothForms.mp φ.2)).mdifferentiable
          (by simp)).mdifferentiableAt.mdifferentiableWithinAt
    · simpa using ψ.1.differentiableWithinAt_inChartAt (s := Set.univ) (x := x)
        (((isSmoothBundleForm_def ∞ ψ.1).mp (mem_smoothForms.mp ψ.2)).mdifferentiable
          (by simp)).mdifferentiableAt.mdifferentiableWithinAt
  map_smul' c φ := Subtype.ext (mextDeriv_smul c φ.1)

variable (I) in
/-- The bundled derivative has the usual rough exterior derivative as its underlying form. -/
@[simp]
theorem mextDerivₗ_apply [IsManifold I 2 M] (k : ℕ) (φ : SmoothForm I M F k) :
    (mextDerivₗ I k φ : RoughForm I M F (k + 1)) = mextDeriv φ.1 :=
  (rfl)

/-- A coordinate form supported compactly inside the chart extends with the same regularity
within the model range. Regularity outside the model range is unnecessary. -/
theorem RoughForm.contDiffOn_indicator_inChartAt {r : WithTop ℕ∞}
    (φ : RoughForm I M F k) (α : M)
    (hφ : ∀ z ∈ (extChartAt I α).target,
      ContDiffWithinAt ℝ r (φ.inChartAt α) (range I) z)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    ContDiffOn ℝ r ((extChartAt I α).target.indicator (φ.inChartAt α)) (range I) := by
  classical
  intro z hz
  by_cases ht : z ∈ (extChartAt I α).target
  · exact (hφ z ht).congr_of_eventuallyEq (φ.indicator_inChartAt_eventuallyEq α ht)
      (indicator_of_mem ht _)
  · have hn : z ∉ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) :=
      φ.notMem_tsupport_indicator_inChartAt α hc hs ht
    have he : (extChartAt I α).target.indicator (φ.inChartAt α) =ᶠ[𝓝 z] 0 := by
      filter_upwards [(_root_.isClosed_tsupport _).isOpen_compl.mem_nhds hn] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

/-- For a form supported inside one chart, exterior differentiation of its zero extension
is the zero extension of its actual manifold exterior derivative, throughout the model range. -/
theorem IsSmoothForm.extDerivWithin_indicator_inChartAt [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    EqOn (extDerivWithin ((extChartAt I α).target.indicator (φ.inChartAt α)) (range I))
      ((extChartAt I α).target.indicator ((TauCeti.mextDeriv φ).inChartAt α)) (range I) := by
  classical
  intro z hz
  by_cases ht : z ∈ (extChartAt I α).target
  · rw [indicator_of_mem ht, hφ.inChartAt_mextDeriv_eq α ht, extDerivWithin,
      extDerivWithin]
    exact congrArg ContinuousAlternatingMap.alternatizeUncurryFin
      ((φ.indicator_inChartAt_eventuallyEq α ht).fderivWithin_eq (indicator_of_mem ht _))
  · rw [indicator_of_notMem ht]
    have hn : z ∉ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) :=
      φ.notMem_tsupport_indicator_inChartAt α hc hs ht
    rw [extDerivWithin,
      (HasFDerivWithinAt.of_notMem_tsupport ℝ (s := range I) hn).fderivWithin
        (I.uniqueDiffOn z hz)]
    exact map_zero _

/-- A compact chart-supported `C¹` form whose support avoids the boundary has a globally `C¹`
coordinate extension by zero. No integration or finite-dimensional hypothesis is required. -/
theorem IsSmoothForm.contDiff_indicator_inChartAt [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source)
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) (I.boundary M)) :
    ContDiff ℝ 1 ((extChartAt I α).target.indicator (φ.inChartAt α)) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α))
  · have ht := mem_interior_iff_mem_nhds.mp
      (φ.tsupport_indicator_inChartAt_subset_interior α hc hs hd hy)
    have hr : range I ∈ 𝓝 y := mem_of_superset ht (extChartAt_target_subset_range α)
    have he : (extChartAt I α).target.indicator (φ.inChartAt α) =ᶠ[𝓝 y] φ.inChartAt α := by
      filter_upwards [ht] with z hz
      exact indicator_of_mem hz _
    have hy := (hφ.contDiffWithinAt_inChartAt α (mem_of_mem_nhds ht)).contDiffAt hr
    exact hy.congr_of_eventuallyEq he
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)

end TauCeti
