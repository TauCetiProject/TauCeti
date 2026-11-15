/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Density.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Density
public import TauCeti.LinearAlgebra.Density.Pullback
public import TauCeti.MeasureTheory.Integral.Bochner.Density
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Basic
public import TauCeti.Geometry.Manifold.Orientation.Lift

/-!
# Coordinate expressions and chart coefficients of rough densities

In the preferred extended chart at `α`, a rough density `μ` has coordinate expression
`μ.inChartAt α : E → Density E m`, obtained by evaluating `μ` along the within-range derivative
of `(extChartAt I α).symm`. On an overlap of two preferred charts, `inChartAt` transforms by the
absolute determinant of the coordinate-change derivative within `range I`, with no orientation
data and including boundary and corner points.

For a model basis `b`, `μ.coeffInChartAt b α : E → ℝ` evaluates `μ.inChartAt α` on `b`
inside the chart target and extends by zero outside it. Unlike `RoughForm.signedInChartAt`, no
source-indexed chart sign is needed. Against the normalized Haar measure `b.addHaar`, both
integrability and the integral of `μ.coeffInChartAt b α` are independent of `b`, and on chart
overlaps they are invariant under change of preferred chart by the Jacobian theorem.

For a top form `φ` on an oriented manifold with lift `l`, the density `φ.toDensity` has the same
topological support as `φ`, and its zero-extended chart coefficient equals the signed top-form
coefficient `φ.signedInChartAt` weighted by the model-basis sign.

## Main definitions

* `TauCeti.RoughDensity.inChartAt`: coordinate expression of a rough density in a preferred chart.
* `TauCeti.RoughDensity.coeffInChartAt`: scalar chart coefficient in a model basis, extended by
  zero outside the chart target.

## Main results

* `TauCeti.RoughDensity.inChartAt_eq_compEnd`,
  `TauCeti.RoughDensity.inChartAt_apply_eq_abs_det_mul`:
  transformation of coordinate expressions across overlapping preferred charts.
* `TauCeti.RoughDensity.coeffInChartAt_changeChart`: equality of set integrals and equivalence of
  integrability across chart overlaps.
* `TauCeti.RoughDensity.continuousOn_inChartAt_of_continuous_section`: coordinate continuity of
  continuous sections of `TauCeti.DensityBundle`.
* `TauCeti.RoughForm.coeffInChartAt_toDensity`: pointwise identity relating the chart coefficient
  of `φ.toDensity` to `φ.signedInChartAt`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 16, Densities.
* The chart-overlap Jacobian and support localization API parallel the oriented top-form
  constructions in `TauCeti.RoughForm.signedInChartAt_changeChart` and
  `TauCeti.RoughForm.exists_finset_partition_eq`, using
  `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` and
  `MeasureTheory.integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`.
-/

public section

noncomputable section

open Bundle Set Filter MeasureTheory Module
open scoped Manifold Topology

namespace TauCeti

namespace RoughDensity

section InChartAt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- Coordinate expression of a rough density in the preferred extended chart at `α`, using the
within-range derivative of `(extChartAt I α).symm`. Outside `(extChartAt I α).target` the value is
unspecified. -/
def inChartAt (μ : RoughDensity I M m) (α : M) (z : E) : Density E m :=
  (μ ((extChartAt I α).symm z)).compLinearMapOfEquiv
    (tangentSpaceCastModel I ((extChartAt I α).symm z)).symm.toLinearEquiv
    ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z).toLinearMap.comp
      (tangentSpaceCastModel 𝓘(ℝ, E) z).symm.toLinearMap)

/-- Evaluation of `inChartAt` on a tuple of model vectors. -/
theorem inChartAt_apply (μ : RoughDensity I M m) (α : M) (z : E) (v : Fin m → E) :
    μ.inChartAt α z v =
      μ ((extChartAt I α).symm z)
        (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z (v i)) := by
  rw [inChartAt, Density.compLinearMapOfEquiv_apply]
  rfl

/-- The zero rough density has zero coordinate expression in every chart. -/
@[simp]
theorem inChartAt_zero (α : M) : (0 : RoughDensity I M m).inChartAt α = 0 := by
  funext z
  ext v
  rw [inChartAt_apply]
  rfl

/-- Coordinate expressions distribute over addition of rough densities. -/
@[simp]
theorem inChartAt_add (μ ν : RoughDensity I M m) (α : M) :
    (μ + ν).inChartAt α = μ.inChartAt α + ν.inChartAt α := by
  funext z
  ext v
  simp only [Pi.add_apply, Density.add_apply, inChartAt_apply]

/-- Coordinate expressions commute with constant scalar multiplication. -/
@[simp]
theorem inChartAt_smul (c : ℝ) (μ : RoughDensity I M m) (α : M) :
    (c • μ).inChartAt α = c • μ.inChartAt α := by
  funext z
  ext v
  simp only [Pi.smul_apply, Density.smul_apply, inChartAt_apply]

/-- Coordinate expressions commute with negation. -/
@[simp]
theorem inChartAt_neg (μ : RoughDensity I M m) (α : M) :
    (-μ).inChartAt α = -μ.inChartAt α := by
  rw [← neg_one_smul ℝ μ, inChartAt_smul, neg_one_smul]

/-- Coordinate expressions distribute over subtraction of rough densities. -/
@[simp]
theorem inChartAt_sub (μ ν : RoughDensity I M m) (α : M) :
    (μ - ν).inChartAt α = μ.inChartAt α - ν.inChartAt α := by
  rw [sub_eq_add_neg, inChartAt_add, inChartAt_neg, sub_eq_add_neg]

/-- Scalar localization of a rough density multiplies its coordinate expression by the pulled-back
scalar function. -/
theorem inChartAt_fun_smul (f : M → ℝ) (μ : RoughDensity I M m) (α : M) (z : E) :
    inChartAt (I := I) (fun x ↦ f x • μ x) α z =
      f ((extChartAt I α).symm z) • μ.inChartAt α z := by
  ext v
  simp only [inChartAt_apply, Density.smul_apply]

/-- Evaluating a chart expression at the chart image of `x` transports each argument through the
tangent coordinate change. -/
theorem inChartAt_chart_apply [IsManifold I 1 M] (μ : RoughDensity I M m) (α : M) {x : M}
    (hx : x ∈ (extChartAt I α).source) (v : Fin m → E) :
    μ.inChartAt α (extChartAt I α x) v =
      μ x (fun i ↦ tangentCoordChange I α x x (v i)) := by
  rw [inChartAt_apply]
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  rw [← TangentBundle.symmL_trivializationAt hx',
    TangentBundle.symmL_trivializationAt_eq_core hx', (extChartAt I α).left_inv hx]
  rfl

/-- Evaluating `μ.inChartAt α` at a target point `y` on a model basis `b` equals evaluating `μ`
at `(extChartAt I α).symm y` on the corresponding inverse trivialization tangent basis. -/
theorem inChartAt_apply_eq_eval_tangentBasis [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    ∃ b' : Basis (Fin m) ℝ (TangentSpace I ((extChartAt I α).symm y)),
      μ.inChartAt α y b = μ ((extChartAt I α).symm y) b' := by
  set x := (extChartAt I α).symm y
  have hx : x ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  let e : TangentSpace I x ≃ₗ[ℝ] E :=
    (trivializationAt E (TangentSpace I) α).linearEquivAt ℝ x hx'
  refine ⟨b.map e.symm, ?_⟩
  rw [inChartAt_apply]
  congr 1
  funext i
  simp only [Basis.map_apply, Trivialization.linearEquivAt_symm_apply, e]
  rw [← (trivializationAt E (TangentSpace I) α).symmL_apply (R := ℝ) hx',
    TangentBundle.symmL_trivializationAt hx, (extChartAt I α).right_inv hy]
  rfl

/-- On an overlap of two preferred charts, the coordinate expression in the first chart is the
endomorphism pullback of the coordinate expression in the second chart along the within-range
derivative of the coordinate change. -/
theorem inChartAt_eq_compEnd [IsManifold I 1 M] (μ : RoughDensity I M m) {x₀ x : M} {z : E}
    (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) :
    μ.inChartAt x₀ z =
      (μ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z))).compEnd
        (fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm)
          (range I) z).toLinearMap := by
  have hleft : (extChartAt I x).symm (extChartAt I x ((extChartAt I x₀).symm z)) =
      (extChartAt I x₀).symm z := (extChartAt I x).left_inv hx
  have hpre : (extChartAt I x₀).symm ⁻¹' (extChartAt I x).source ∈ 𝓝[range I] z :=
    (continuousAt_extChartAt_symm'' hz).continuousWithinAt.preimage_mem_nhdsWithin
      (extChartAt_source_mem_nhds' hx)
  have hcoord : ((extChartAt I x).symm ∘ (extChartAt I x ∘ (extChartAt I x₀).symm))
      =ᶠ[𝓝[range I] z] (extChartAt I x₀).symm := by
    filter_upwards [hpre] with a ha
    exact (extChartAt I x).left_inv ha
  have hcomp :
      mfderivWithin 𝓘(ℝ, E) I ((extChartAt I x).symm ∘
        (extChartAt I x ∘ (extChartAt I x₀).symm)) (range I) z =
        (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
          (extChartAt I x ((extChartAt I x₀).symm z))).comp
          (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ, E)
            (extChartAt I x ∘ (extChartAt I x₀).symm) (range I) z) := by
    apply mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
      (I' := 𝓘(ℝ, E)) (I'' := I) (u := range I) z
    · exact mdifferentiableWithinAt_extChartAt_symm ((extChartAt I x).map_source hx)
    · exact ((contDiffWithinAt_ext_coord_change (𝕜 := ℝ) (n := 1) x x₀ (by
        rw [PartialEquiv.trans_source]
        exact ⟨by simpa only [PartialEquiv.symm_source] using hz, hx⟩)).differentiableWithinAt
          (by simp)).mdifferentiableWithinAt
    · filter_upwards [hpre] with a ha
      exact extChartAt_target_subset_range x ((extChartAt I x).map_source ha)
    · exact (I.uniqueDiffOn.uniqueDiffWithinAt
        (extChartAt_target_subset_range x₀ hz)).uniqueMDiffWithinAt
    · rfl
  rw [hcoord.mfderivWithin_eq hleft, mfderivWithin_eq_fderivWithin] at hcomp
  ext v
  rw [inChartAt_apply, Density.compEnd_apply, inChartAt_apply, hleft]
  congr 1
  funext i
  exact congrArg (fun L ↦ L (v i)) hcomp

/-- Between overlapping preferred charts, evaluating a density's coordinate expression on any tuple
transforms by the absolute Jacobian determinant within `range I`, including boundary and corner
points. -/
theorem inChartAt_apply_eq_abs_det_mul [IsManifold I 1 M] (μ : RoughDensity I M m)
    {x₀ x : M} {z : E} (hz : z ∈ (extChartAt I x₀).target)
    (hx : (extChartAt I x₀).symm z ∈ (extChartAt I x).source) (v : Fin m → E) :
    μ.inChartAt x₀ z v =
      |(fderivWithin ℝ (extChartAt I x ∘ (extChartAt I x₀).symm)
        (range I) z).toLinearMap.det| *
        μ.inChartAt x (extChartAt I x ((extChartAt I x₀).symm z)) v := by
  rw [μ.inChartAt_eq_compEnd hz hx, Density.compEnd_apply_eq_abs_det_mul]

end InChartAt

section Support

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- Pointwise multiplication by a scalar function does not enlarge the topological support of a
rough density. -/
theorem tsupport_fun_smul_subset (f : M → ℝ) (μ : RoughDensity I M m) :
    _root_.tsupport (α := Density E m) (fun x ↦ f x • μ x : RoughDensity I M m) ⊆
      _root_.tsupport (α := Density E m) μ :=
  -- `TangentSpace I x` is definitionally `E`, so `tsupport_smul_subset_right` applies.
  _root_.tsupport_smul_subset_right f (show M → Density E m from μ)

/-- Pointwise multiplication by a scalar function has support contained in the support of the
scalar factor. -/
theorem tsupport_fun_smul_subset_left (f : M → ℝ) (μ : RoughDensity I M m) :
    _root_.tsupport (α := Density E m) (fun x ↦ f x • μ x : RoughDensity I M m) ⊆
      _root_.tsupport f :=
  -- `TangentSpace I x` is definitionally `E`, so `tsupport_smul_subset_left` applies.
  _root_.tsupport_smul_subset_left f (show M → Density E m from μ)

/-- Constant scalar multiplication does not enlarge the support of a rough density. -/
theorem tsupport_smul_subset (c : ℝ) (μ : RoughDensity I M m) :
    _root_.tsupport (α := Density E m) (c • μ) ⊆ _root_.tsupport (α := Density E m) μ :=
  tsupport_fun_smul_subset (fun _ ↦ c) μ

/-- Multiplication by a nonzero constant preserves the support of a rough density. -/
theorem tsupport_smul (c : ℝ) (μ : RoughDensity I M m) (hc : c ≠ 0) :
    _root_.tsupport (α := Density E m) (c • μ) = _root_.tsupport (α := Density E m) μ :=
  Subset.antisymm (tsupport_smul_subset c μ) <| by
    simpa only [inv_smul_smul₀ hc] using tsupport_smul_subset c⁻¹ (c • μ)

/-- The zero density has compact topological support. -/
theorem isCompact_tsupport_zero :
    IsCompact (_root_.tsupport (α := Density E m) (0 : RoughDensity I M m)) := by
  -- Identify the dependent zero section with a fixed-codomain zero function so `tsupport_zero`
  -- applies.
  change IsCompact (_root_.tsupport (0 : M → Density E m))
  simp

/-- The sum of two compactly supported rough densities has compact topological support. -/
theorem isCompact_tsupport_add {μ ν : RoughDensity I M m}
    (hμ : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hν : IsCompact (_root_.tsupport (α := Density E m) ν)) :
    IsCompact (_root_.tsupport (α := Density E m) (μ + ν)) :=
  -- `TangentSpace I x` is definitionally `E`, so `HasCompactSupport.add` applies at fixed codomain.
  HasCompactSupport.add (f := (show M → Density E m from μ)) hμ hν

/-- A partition of unity localizes any compactly supported rough density into finitely many terms,
with all terms outside the finite set vanishing identically. -/
theorem exists_finset_partition_eq {ι : Type*} (μ : RoughDensity I M m)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (ρ : PartitionOfUnity ι M univ) :
    ∃ s : Finset ι,
      μ = (fun x ↦ ∑ i ∈ s, ρ i x • μ x) ∧
        ∀ i ∉ s, (fun x ↦ ρ i x • μ x : RoughDensity I M m) = 0 := by
  classical
  have hfin := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hc
  let s := hfin.toFinset
  have hmem (i : ι) (x : M) (hρ : ρ i x ≠ 0) (hμ : μ x ≠ 0) : i ∈ s :=
    hfin.mem_toFinset.mpr ⟨x, subset_tsupport (ρ i) hρ,
      _root_.subset_tsupport (α := Density E m) μ hμ⟩
  refine ⟨s, ?_, ?_⟩
  · funext x
    by_cases hx : μ x = 0
    · simp [hx]
    · have hs : ρ.finsupport x ⊆ s := fun i hi ↦
        hmem i x (by simpa only [PartitionOfUnity.mem_finsupport, Function.mem_support] using hi) hx
      rw [← Finset.sum_smul, ρ.sum_finsupport' (mem_univ x) hs, one_smul]
  · intro i hi
    funext x
    by_cases hμ : μ x = 0
    · simp [hμ]
    · have hρ : ρ i x = 0 := by
        by_contra h
        exact hi (hmem i x h hμ)
      simp [hρ]

end Support

section CoeffInChartAt

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] {m : ℕ}

/-- Scalar chart coefficient of a rough density in a model basis `b`, extended by zero outside
`(extChartAt I α).target`. -/
def coeffInChartAt (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) : E → ℝ :=
  (extChartAt I α).target.indicator fun y ↦ μ.inChartAt α y b

/-- `coeffInChartAt` agrees with evaluating the zero-extended coordinate density on `b`. -/
theorem coeffInChartAt_eq_indicator_apply (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    μ.coeffInChartAt b α y = ((extChartAt I α).target.indicator (μ.inChartAt α) y) b := by
  classical
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [coeffInChartAt, indicator_of_mem hy, indicator_of_mem hy]
  · rw [coeffInChartAt, indicator_of_notMem hy, indicator_of_notMem hy]
    rfl

open scoped Classical in
/-- Pointwise formula for `coeffInChartAt`, zero outside `(extChartAt I α).target`. -/
theorem coeffInChartAt_apply (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    μ.coeffInChartAt b α y =
      if y ∈ (extChartAt I α).target then μ.inChartAt α y b else 0 := by
  rw [coeffInChartAt, Set.indicator_apply]

/-- Inside the chart target, `coeffInChartAt` evaluates `inChartAt` on `b`. -/
theorem coeffInChartAt_apply_of_mem_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (hy : y ∈ (extChartAt I α).target) :
    μ.coeffInChartAt b α y = μ.inChartAt α y b :=
  indicator_of_mem hy _

/-- Outside the chart target, `coeffInChartAt` vanishes. -/
theorem coeffInChartAt_apply_of_notMem_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) {y : E} (hy : y ∉ (extChartAt I α).target) :
    μ.coeffInChartAt b α y = 0 :=
  indicator_of_notMem hy _

/-- At the chart image of a source point, `coeffInChartAt` evaluates `inChartAt` on `b`. -/
theorem coeffInChartAt_apply_of_mem_source (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) {x : M} (hx : x ∈ (extChartAt I α).source) :
    μ.coeffInChartAt b α (extChartAt I α x) = μ.inChartAt α (extChartAt I α x) b :=
  μ.coeffInChartAt_apply_of_mem_target b α ((extChartAt I α).map_source hx)

/-- The zero rough density has zero chart coefficient everywhere. -/
@[simp]
theorem coeffInChartAt_zero (b : Basis (Fin m) ℝ E) (α : M) :
    (0 : RoughDensity I M m).coeffInChartAt b α = 0 := by
  funext y
  simp [coeffInChartAt]

/-- `coeffInChartAt` is additive in the rough density. -/
theorem coeffInChartAt_add (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    (μ + ν).coeffInChartAt b α y = μ.coeffInChartAt b α y + ν.coeffInChartAt b α y := by
  classical
  simp only [coeffInChartAt_apply]
  split_ifs <;> simp

/-- Pointwise multiplication by a scalar function multiplies `coeffInChartAt` by the pulled-back
scalar factor, including outside the chart target. -/
theorem coeffInChartAt_fun_smul (f : M → ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    coeffInChartAt (I := I) (fun x ↦ f x • μ x) b α y =
      f ((extChartAt I α).symm y) * μ.coeffInChartAt b α y := by
  classical
  simp only [coeffInChartAt_apply]
  split_ifs
  · rw [inChartAt_fun_smul, Density.smul_apply, smul_eq_mul]
  · simp

/-- `coeffInChartAt` commutes with constant scalar multiplication. -/
@[simp]
theorem coeffInChartAt_smul (c : ℝ) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    (c • μ).coeffInChartAt b α y = c * μ.coeffInChartAt b α y :=
  coeffInChartAt_fun_smul (fun _ ↦ c) μ b α y

/-- `coeffInChartAt` commutes with negation. -/
@[simp]
theorem coeffInChartAt_neg (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    (-μ).coeffInChartAt b α y = -μ.coeffInChartAt b α y := by
  rw [← neg_one_smul ℝ μ, coeffInChartAt_smul, neg_one_mul]

/-- `coeffInChartAt` respects subtraction of rough densities. -/
theorem coeffInChartAt_sub (μ ν : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    (μ - ν).coeffInChartAt b α y = μ.coeffInChartAt b α y - ν.coeffInChartAt b α y := by
  rw [sub_eq_add_neg, coeffInChartAt_add, coeffInChartAt_neg, sub_eq_add_neg]

/-- Restricting a rough density by an indicator restricts its chart coefficient to the
corresponding coordinate piece. -/
theorem coeffInChartAt_indicator (s : Set M) (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) (y : E) :
    coeffInChartAt (I := I) (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ)) x • μ x) b α y =
      ((extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s).indicator
        (μ.coeffInChartAt b α) y := by
  classical
  rw [coeffInChartAt_fun_smul]
  by_cases hy : y ∈ (extChartAt I α).target
  · by_cases hs : (extChartAt I α).symm y ∈ s
    · have hys : y ∈ (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s := ⟨hy, hs⟩
      rw [indicator_of_mem hs, indicator_of_mem hys, one_mul]
    · have hys : y ∉ (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s :=
        fun h ↦ hs h.2
      rw [indicator_of_notMem hs, indicator_of_notMem hys, zero_mul]
  · have hys : y ∉ (extChartAt I α).target ∩ (extChartAt I α).symm ⁻¹' s :=
      fun h ↦ hy h.1
    rw [μ.coeffInChartAt_apply_of_notMem_target b α hy, mul_zero, indicator_of_notMem hys]

/-- Two rough densities agreeing on a subset of a chart source have equal chart coefficients on
its coordinate image. -/
theorem eqOn_coeffInChartAt_image {μ ν : RoughDensity I M m} {s : Set M}
    (h : ∀ x ∈ s, μ x = ν x) (b : Basis (Fin m) ℝ E) (α : M)
    (hs : s ⊆ (extChartAt I α).source) :
    EqOn (μ.coeffInChartAt b α) (ν.coeffInChartAt b α) ((extChartAt I α) '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [coeffInChartAt_apply_of_mem_source _ _ _ (hs hx),
    coeffInChartAt_apply_of_mem_source _ _ _ (hs hx), inChartAt_apply, inChartAt_apply,
    (extChartAt I α).left_inv (hs hx), h x hx]

/-- Chart coefficients vanish outside the coordinate target. -/
theorem support_coeffInChartAt_subset_target (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E)
    (α : M) :
    Function.support (μ.coeffInChartAt b α) ⊆ (extChartAt I α).target :=
  support_indicator_subset

/-- The chart coefficient is supported inside the coordinate image of the density's topological
support. -/
theorem support_coeffInChartAt_subset (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M) :
    Function.support (μ.coeffInChartAt b α) ⊆
      (extChartAt I α) '' (_root_.tsupport (α := Density E m) μ) := by
  intro y hy
  have ht : y ∈ (extChartAt I α).target := μ.support_coeffInChartAt_subset_target b α hy
  have hne : μ ((extChartAt I α).symm y) ≠ 0 := by
    intro h0
    apply Function.mem_support.mp hy
    rw [μ.coeffInChartAt_apply_of_mem_target b α ht, inChartAt_apply, h0]
    rfl
  exact ⟨(extChartAt I α).symm y, _root_.subset_tsupport (α := Density E m) μ hne,
    (extChartAt I α).right_inv ht⟩

/-- Continuity of `μ.inChartAt α` on the chart target implies continuity of
`μ.coeffInChartAt b α` on the chart target. -/
theorem continuousOn_coeffInChartAt (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (hμ : ContinuousOn (μ.inChartAt α) (extChartAt I α).target) :
    ContinuousOn (μ.coeffInChartAt b α) (extChartAt I α).target := by
  refine ((Density.continuous_eval b).comp_continuousOn hμ).congr fun y hy ↦ ?_
  exact μ.coeffInChartAt_apply_of_mem_target b α hy

variable [MeasurableSpace E] [BorelSpace E]

/-- Integrability of a density's chart coefficient against normalized basis Haar measure is
independent of the chosen model basis. -/
theorem integrable_coeffInChartAt_basis_iff (μ : RoughDensity I M m)
    (b b' : Basis (Fin m) ℝ E) (α : M) :
    Integrable (μ.coeffInChartAt b' α) b'.addHaar ↔
      Integrable (μ.coeffInChartAt b α) b.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.integrable_density_apply_iff b' ((extChartAt I α).target.indicator (μ.inChartAt α))

/-- Set integrability of a density's chart coefficient against normalized basis Haar measure is
independent of the chosen model basis. -/
theorem integrableOn_coeffInChartAt_basis_iff (μ : RoughDensity I M m)
    (b b' : Basis (Fin m) ℝ E) (α : M) (s : Set E) :
    IntegrableOn (μ.coeffInChartAt b' α) s b'.addHaar ↔
      IntegrableOn (μ.coeffInChartAt b α) s b.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.integrableOn_density_apply_iff b' ((extChartAt I α).target.indicator (μ.inChartAt α)) s

/-- The normalized Haar integral of a density's chart coefficient is independent of the model
basis, with no orientation sign and including dimension zero. -/
theorem integral_coeffInChartAt_basis_eq (μ : RoughDensity I M m)
    (b b' : Basis (Fin m) ℝ E) (α : M) :
    (∫ y, μ.coeffInChartAt b α y ∂b.addHaar) =
      ∫ y, μ.coeffInChartAt b' α y ∂b'.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.integral_density_apply_eq b' ((extChartAt I α).target.indicator (μ.inChartAt α))

/-- The normalized Haar set integral of a density's chart coefficient is independent of the model
basis. -/
theorem setIntegral_coeffInChartAt_basis_eq (μ : RoughDensity I M m)
    (b b' : Basis (Fin m) ℝ E) (α : M) (s : Set E) :
    (∫ y in s, μ.coeffInChartAt b α y ∂b.addHaar) =
      ∫ y in s, μ.coeffInChartAt b' α y ∂b'.addHaar := by
  simp_rw [fun c ↦ funext (μ.coeffInChartAt_eq_indicator_apply c α)]
  exact b.setIntegral_density_apply_eq b' ((extChartAt I α).target.indicator (μ.inChartAt α)) s

/-- A density supported compactly inside a single chart with continuous coordinate expression on
that chart's target has an integrable chart coefficient against any additive Haar measure. -/
theorem integrable_coeffInChartAt (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α : M)
    (hμ : ContinuousOn (μ.inChartAt α) (extChartAt I α).target)
    (hc : IsCompact (_root_.tsupport (α := Density E m) μ))
    (hs : _root_.tsupport (α := Density E m) μ ⊆ (extChartAt I α).source)
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    Integrable (μ.coeffInChartAt b α) ν := by
  have hK : IsCompact ((extChartAt I α) '' (_root_.tsupport (α := Density E m) μ)) :=
    hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs)
  have htarget :
      (extChartAt I α) '' (_root_.tsupport (α := Density E m) μ) ⊆ (extChartAt I α).target :=
    (image_mono hs).trans (extChartAt I α).image_source_eq_target.subset
  exact (integrableOn_iff_integrable_of_support_subset
    (μ.support_coeffInChartAt_subset b α)).mp
      (((μ.continuousOn_coeffInChartAt b α hμ).mono htarget).integrableOn_compact hK)

/-- On a measurable overlap piece of two preferred charts, both the Haar set integral and
integrability of a rough density's chart coefficient are invariant under change of chart, with no
orientation compatibility condition. -/
theorem coeffInChartAt_changeChart [IsManifold I 1 M] (μ : RoughDensity I M m)
    (b : Basis (Fin m) ℝ E) (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hs : MeasurableSet ((extChartAt I α) '' s))
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    ((∫ y in (extChartAt I α) '' s, μ.coeffInChartAt b α y ∂ν) =
        ∫ y in (extChartAt I β) '' s, μ.coeffInChartAt b β y ∂ν) ∧
      (IntegrableOn (μ.coeffInChartAt b α) ((extChartAt I α) '' s) ν ↔
        IntegrableOn (μ.coeffInChartAt b β) ((extChartAt I β) '' s) ν) := by
  have : FiniteDimensional ℝ E := Module.Finite.of_basis b
  let A := (extChartAt I α) '' s
  let e := (extChartAt I α).symm ≫ extChartAt I β
  let D := fun y ↦ fderivWithin ℝ (extChartAt I β ∘ (extChartAt I α).symm) (range I) y
  have himage := TauCeti.extChartAt_coordChange_image α β hsub
  have hinj := TauCeti.injOn_extChartAt_coordChange α β hsub
  have hderiv := TauCeti.hasFDerivWithinAt_extChartAt_coordChange α β hsub
  have hcoef : ∀ y ∈ A, |(D y).toLinearMap.det| • μ.coeffInChartAt b β (e y) =
      μ.coeffInChartAt b α y := by
    rintro _ ⟨x, hx, rfl⟩
    have he : e (extChartAt I α x) = extChartAt I β x :=
      congrArg (extChartAt I β) ((extChartAt I α).left_inv (hsub hx).1)
    rw [he, μ.coeffInChartAt_apply_of_mem_source b α (hsub hx).1,
      μ.coeffInChartAt_apply_of_mem_source b β (hsub hx).2]
    have hβ : (extChartAt I α).symm (extChartAt I α x) ∈ (extChartAt I β).source := by
      rw [(extChartAt I α).left_inv (hsub hx).1]
      exact (hsub hx).2
    have hc := μ.inChartAt_apply_eq_abs_det_mul ((extChartAt I α).map_source (hsub hx).1) hβ b
    rw [(extChartAt I α).left_inv (hsub hx).1] at hc
    rw [hc, smul_eq_mul]
  constructor
  · rw [← himage, integral_image_eq_integral_abs_det_fderiv_smul ν hs hderiv hinj]
    exact setIntegral_congr_fun hs fun y hy ↦ (hcoef y hy).symm
  · rw [← himage, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul ν hs hderiv hinj]
    exact (integrableOn_congr_fun (fun y hy ↦ hcoef y hy) hs).symm

/-- A rough density supported in two preferred charts has the same chart-coefficient integral in
both charts. -/
theorem integral_coeffInChartAt_eq_of_tsupport_subset [IsManifold I 1 M]
    (μ : RoughDensity I M m) (b : Basis (Fin m) ℝ E) (α β : M)
    (hsub : _root_.tsupport (α := Density E m) μ ⊆
      (extChartAt I α).source ∩ (extChartAt I β).source)
    (ν : Measure E) [ν.IsAddHaarMeasure] :
    (∫ y, μ.coeffInChartAt b α y ∂ν) = ∫ y, μ.coeffInChartAt b β y ∂ν := by
  have := b.finiteDimensional_of_finite
  let U := (extChartAt I α).source ∩ (extChartAt I β).source
  have hm : MeasurableSet ((extChartAt I α) '' U) :=
    IsOpen.measurableSet_image_extChartAt_source_inter
      (I := I) (isOpen_extChartAt_source (I := I) β) α
  have hα : (∫ y in (extChartAt I α) '' U, μ.coeffInChartAt b α y ∂ν) =
      ∫ y, μ.coeffInChartAt b α y ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      by_contra hn
      exact hy (image_mono hsub
        (μ.support_coeffInChartAt_subset b α (Function.mem_support.mpr hn)))
  have hβ : (∫ y in (extChartAt I β) '' U, μ.coeffInChartAt b β y ∂ν) =
      ∫ y, μ.coeffInChartAt b β y ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by
      by_contra hn
      exact hy (image_mono hsub
        (μ.support_coeffInChartAt_subset b β (Function.mem_support.mpr hn)))
  exact hα.symm.trans ((μ.coeffInChartAt_changeChart b α β Subset.rfl hm ν).1.trans hβ)

end CoeffInChartAt

section BundleContinuity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

/-- On an extended chart target, evaluating `μ.inChartAt α` on `Module.finBasis ℝ E` gives the
fiber coordinate of `μ` in the preferred trivialization of `TauCeti.DensityBundle`. -/
theorem inChartAt_finBasis_eq_trivializationAt
    (μ : (x : M) → DensityBundle I M x) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    inChartAt (I := I) μ α z (finBasis ℝ E) =
      (trivializationAt ℝ (DensityBundle I M) α
        ⟨(extChartAt I α).symm z, μ ((extChartAt I α).symm z)⟩).2 := by
  have hy : (extChartAt I α).symm z ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hz
  have hy' : (extChartAt I α).symm z ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  rw [Density.trivializationAt_eq, Trivialization.density_apply]
  simp only [inChartAt_apply]
  congr 1
  funext i
  rw [← (trivializationAt E (TangentSpace I) α).symmL_apply (R := ℝ) hy',
    TangentBundle.symmL_trivializationAt hy, (extChartAt I α).right_inv hz]
  rfl

/-- Every continuous section of `TauCeti.DensityBundle` has a continuous coordinate expression on
each preferred extended chart target, including at boundary and corner points. -/
theorem continuousOn_inChartAt_of_continuous_section
    {μ : (x : M) → DensityBundle I M x}
    (hμ : Continuous fun x ↦ TotalSpace.mk' ℝ x (μ x)) (α : M) :
    ContinuousOn (inChartAt (I := I) μ α) (extChartAt I α).target := by
  let e := trivializationAt ℝ (DensityBundle I M) α
  have hmap : MapsTo (fun x ↦ TotalSpace.mk' ℝ x (μ x))
      (extChartAt I α).source e.source := by
    intro x hx
    rw [e.mem_source]
    dsimp only [TotalSpace.mk', e]
    rw [Density.trivializationAt_eq, Trivialization.density_baseSet,
      TangentBundle.trivializationAt_baseSet]
    simpa only [extChartAt_source] using hx
  have hc : ContinuousOn (fun x ↦ (e ⟨x, μ x⟩).2) (extChartAt I α).source :=
    (e.continuousOn.comp hμ.continuousOn hmap).snd
  have hcoord : ContinuousOn
      (fun z ↦ inChartAt (I := I) μ α z (finBasis ℝ E)) (extChartAt I α).target :=
    (hc.comp (continuousOn_extChartAt_symm α) (extChartAt I α).mapsTo_symm).congr
      fun z hz ↦ inChartAt_finBasis_eq_trivializationAt μ α hz
  refine ((finBasis ℝ E).continuous_density.comp_continuousOn hcoord).congr fun z _ ↦ ?_
  simpa only [Function.comp_apply, Basis.densityEquiv_apply, Basis.densityEquiv_symm_apply] using
    ((finBasis ℝ E).densityEquiv.symm_apply_apply (inChartAt (I := I) μ α z)).symm

end BundleContinuity

end RoughDensity

namespace RoughForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {m : ℕ}

/-- Evaluating `φ.toDensity o x` on any tangent basis gives `φ x` on that basis weighted by its
sign relative to `o.orientationAt x`, including in dimension zero. -/
theorem toDensity_apply_basis (φ : RoughForm I M ℝ m)
    (o : Manifold.Orientation I M (Fin m)) (x : M)
    (b : Basis (Fin m) ℝ (TangentSpace I x)) :
    φ.toDensity o x b = (Orientation.signBasis (o.orientationAt x) b : ℝ) * φ x b := by
  rcases b.orientation_eq_or_eq_neg (o.orientationAt x) with hb | hb
  · rw [φ.toDensity_apply_of_orientation_eq hb.symm, hb, Orientation.signBasis_orientation,
      Units.val_one, Int.cast_one, one_mul]
  · have hb' : b.orientation = -o.orientationAt x := by
      rw [hb, _root_.neg_neg b.orientation]
    rw [φ.toDensity_apply_of_orientation_eq_neg hb', hb,
      Orientation.signBasis_neg, Orientation.signBasis_orientation, Units.val_neg, Units.val_one,
      Int.cast_neg, Int.cast_one, neg_one_mul]

/-- Passing from a top form to its density preserves the topological support. -/
@[simp]
theorem tsupport_toDensity (φ : RoughForm I M ℝ m) (o : Manifold.Orientation I M (Fin m)) :
    _root_.tsupport (α := Density E m) (φ.toDensity o) =
      _root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ) φ := by
  simp only [_root_.tsupport]
  congr 1
  ext x
  -- Both supports check nonvanishing in the fibre at `x`.
  change φ.toDensity o x ≠ 0 ↔ φ x ≠ 0
  let b : Basis (Fin m) ℝ (TangentSpace I x) :=
    finBasisOfFinrankEq ℝ (TangentSpace I x) (o.fact_finrank_tangentSpace x).out
  have hsign : (Orientation.signBasis (o.orientationAt x) b : ℝ) ≠ 0 := by
    rcases Int.units_eq_one_or (Orientation.signBasis (o.orientationAt x) b) with h | h <;>
      simp [h]
  apply not_congr
  rw [← (φ.toDensity o x).apply_basis_eq_zero_iff b,
    φ.toDensity_apply_basis o x b, mul_eq_zero, or_iff_right hsign]
  exact not_iff_not.mp ((φ x).map_basis_ne_zero_iff b)

/-- On an extended chart target, the coordinate expression of `φ.toDensity (Orientation.mk l)` on
a model basis `b` is the coordinate expression of `φ` on `b` weighted by the model-basis sign and
the source chart sign of `l`. -/
theorem inChartAt_toDensity_apply_basis (φ : RoughForm I M ℝ m)
    (l : Manifold.OrientationLift I M (Fin m)) (b : Basis (Fin m) ℝ E) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    (φ.toDensity (Manifold.Orientation.mk l)).inChartAt α y b =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        (l.signAt α ((extChartAt I α).symm y) : ℝ) * φ.inChartAt α y b := by
  set x := (extChartAt I α).symm y
  have hx : x ∈ (chartAt H α).source := by
    simpa only [extChartAt_source] using (extChartAt I α).map_target hy
  have hx' : x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rwa [TangentBundle.trivializationAt_baseSet]
  let e : TangentSpace I x ≃ₗ[ℝ] E :=
    (trivializationAt E (TangentSpace I) α).linearEquivAt ℝ x hx'
  let b' : Basis (Fin m) ℝ (TangentSpace I x) := b.map e.symm
  have hb' : (b' : Fin m → TangentSpace I x) =
      fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) y (b i) := by
    funext i
    simp only [b', e, Basis.map_apply, Trivialization.linearEquivAt_symm_apply]
    rw [← (trivializationAt E (TangentSpace I) α).symmL_apply (R := ℝ) hx',
      TangentBundle.symmL_trivializationAt hx, (extChartAt I α).right_inv hy]
    rfl
  have hin : (φ.toDensity (Manifold.Orientation.mk l)).inChartAt α y b =
      φ.toDensity (Manifold.Orientation.mk l) x b' := by
    rw [RoughDensity.inChartAt_apply, ← hb']
  have hφin : φ.inChartAt α y b = φ x b' := by
    rw [RoughForm.inChartAt_apply, ← hb']
  have hmap : b'.map e = b := by
    ext i
    simp [b']
  have hsign : (Orientation.signBasis (l.orientationAt x) b' : ℝ) =
      (Orientation.signBasis l.modelOrientation b : ℝ) * (l.signAt α x : ℝ) := by
    have h₁ := Orientation.signBasis_map (l.orientationAt x) b' e
    have h₂ := l.mapOrientation_orientationAt hx
    rw [Trivialization.mapOrientation_apply] at h₂
    rw [← h₁, hmap, h₂, l.chartOrientation_eq_ite, l.signAt_of_mem hx]
    rcases Int.units_eq_one_or (l.sign α ⟨x, hx⟩) with hs | hs <;>
      simp [hs, Orientation.signBasis_neg]
  rw [hin, φ.toDensity_apply_basis, Manifold.Orientation.orientationAt_mk, hsign, hφin]

/-- At every point of the model space, the zero-extended chart coefficient of
`φ.toDensity (Orientation.mk l)` equals the signed top-form chart coefficient weighted by the
model-basis sign. -/
theorem coeffInChartAt_toDensity (φ : RoughForm I M ℝ m)
    (l : Manifold.OrientationLift I M (Fin m)) (b : Basis (Fin m) ℝ E) (α : M) (y : E) :
    (φ.toDensity (Manifold.Orientation.mk l)).coeffInChartAt b α y =
      (Orientation.signBasis l.modelOrientation b : ℝ) *
        φ.signedInChartAt b α (fun x ↦ l.signAt α x) y := by
  classical
  by_cases hy : y ∈ (extChartAt I α).target
  · rw [RoughDensity.coeffInChartAt_apply_of_mem_target _ b α hy,
      φ.inChartAt_toDensity_apply_basis l b α hy, RoughForm.signedInChartAt_apply,
      dite_eq_left hy, mul_assoc]
  · rw [RoughDensity.coeffInChartAt_apply_of_notMem_target _ b α hy,
      RoughForm.signedInChartAt_apply, dite_eq_right hy, mul_zero]

end RoughForm

end TauCeti
