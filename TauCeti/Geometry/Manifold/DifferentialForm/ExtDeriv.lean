/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Calculus.DifferentialForm.Const
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The exterior derivative of differential forms on manifolds

A rough form `φ : RoughForm I M F k` with values in a fixed normed space is read in the
preferred extended chart at `x₀` as the flat form `φ.inChartAt x₀ : E → E [⋀^Fin k]→L[ℝ] F`:
its pullback along `(extChartAt I x₀).symm`, with derivatives taken within `range I`. The
exterior derivative `mextDerivWithin φ s x` is Mathlib's flat exterior derivative
`extDerivWithin` of the coordinate expression in the chart at `x` itself, taken within
`(extChartAt I x).symm ⁻¹' s ∩ range I` at the chart point of `x`; tangent vectors at `x` are
read in that same chart. `mextDeriv φ` is the version on the whole manifold. This is the
construction of Mathlib's manifold Lie bracket `VectorField.mlieBracketWithin`, transposed to
forms. Like `mfderiv`, both are total, with junk values where the form is not differentiable;
the real hypotheses are carried by the theorems. Working within `range I` makes the
definition meaningful at boundary and corner points.

The file proves the basic calculus of this operator: locality in the set and in the form,
additivity and homogeneity, agreement with Mathlib's `extDerivWithin` over the model space
`𝓘(ℝ, E)`, and the identification of the exterior derivative of the `0`-form of a function with
the manifold derivative `mvfderivWithin` of the function.

## Main declarations

* `TauCeti.RoughForm.inChartAt`: the coordinate expression of a rough form in a chart.
* `TauCeti.mextDerivWithin`, `TauCeti.mextDeriv`: the exterior derivative of a rough form.
* `TauCeti.mextDerivWithin_congr_of_eventuallyEq`, `TauCeti.mextDerivWithin_congr_set`: locality.
* `TauCeti.mextDerivWithin_add`, `TauCeti.mextDerivWithin_smul`: linearity.
* `TauCeti.mextDerivWithin_eq_extDerivWithin`, `TauCeti.mextDeriv_eq_extDeriv`: over the model
  space, the manifold exterior derivative is the flat one.
* `TauCeti.mextDerivWithin_ofFunction`, `TauCeti.mextDeriv_ofFunction`: the exterior derivative
  of a function is its manifold derivative.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-! ### The coordinate expression of a form in a chart -/

namespace RoughForm

/-- The coordinate expression of a rough form in the preferred extended chart at `x₀`: its
pullback along `(extChartAt I x₀).symm`, with the derivative taken within `range I`. At a
chart coordinate `z`, tangent vectors at `(extChartAt I x₀).symm z` are thus fed to the form in
the coordinates of the chart at `x₀`. Outside the chart target the value is junk. -/
def inChartAt (φ : RoughForm I M F k) (x₀ : M) : E → E [⋀^Fin k]→L[ℝ] F :=
  bundleMpullbackWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) φ

theorem inChartAt_apply (φ : RoughForm I M F k) (x₀ : M) (z : E) (v : Fin k → E) :
    φ.inChartAt x₀ z v =
      φ ((extChartAt I x₀).symm z)
        (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I x₀).symm (range I) z (v i)) :=
  bundleMpullbackWithin_apply _ _ φ z v

@[simp]
theorem inChartAt_zero (x₀ : M) : (0 : RoughForm I M F k).inChartAt x₀ = 0 :=
  bundleMpullbackWithin_zero _ _

@[simp]
theorem inChartAt_add (φ η : RoughForm I M F k) (x₀ : M) :
    (φ + η).inChartAt x₀ = φ.inChartAt x₀ + η.inChartAt x₀ :=
  bundleMpullbackWithin_add _ _ φ η

@[simp]
theorem inChartAt_smul (c : ℝ) (φ : RoughForm I M F k) (x₀ : M) :
    (c • φ).inChartAt x₀ = c • φ.inChartAt x₀ :=
  bundleMpullbackWithin_smul _ _ c φ

@[simp]
theorem inChartAt_neg (φ : RoughForm I M F k) (x₀ : M) :
    (-φ).inChartAt x₀ = -φ.inChartAt x₀ := by
  rw [← neg_one_smul ℝ φ, inChartAt_smul, neg_one_smul]

@[simp]
theorem inChartAt_sub (φ η : RoughForm I M F k) (x₀ : M) :
    (φ - η).inChartAt x₀ = φ.inChartAt x₀ - η.inChartAt x₀ := by
  rw [sub_eq_add_neg, inChartAt_add, inChartAt_neg, sub_eq_add_neg]

/-- At the centre of its own chart, the coordinate expression of a form is its value there. -/
theorem inChartAt_extChartAt_self [IsManifold I 1 M] (φ : RoughForm I M F k) (x : M) :
    φ.inChartAt x (extChartAt I x x) = φ x := by
  ext v
  rw [inChartAt_apply, mfderivWithin_range_extChartAt_symm, extChartAt_to_inv]
  rfl

end RoughForm

/-! ### The exterior derivative -/

/-- The exterior derivative of a rough form within a set `s`, at a point `x`: the flat exterior
derivative of the coordinate expression of the form in the chart at `x`, within
`(extChartAt I x).symm ⁻¹' s ∩ range I` at the chart point of `x`. Tangent vectors at `x` are
read in the chart at `x`. Total, with junk values where the form is not differentiable. -/
def mextDerivWithin (φ : RoughForm I M F k) (s : Set M) (x : M) :
    TangentSpace I x [⋀^Fin (k + 1)]→L[ℝ] F :=
  extDerivWithin (E := E) (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x)

/-- The exterior derivative of a rough form. -/
def mextDeriv (φ : RoughForm I M F k) : RoughForm I M F (k + 1) :=
  fun x ↦ mextDerivWithin φ univ x

variable {φ η : RoughForm I M F k} {s t : Set M} {x : M}

theorem mextDerivWithin_def (φ : RoughForm I M F k) (s : Set M) (x : M) :
    mextDerivWithin φ s x =
      extDerivWithin (E := E) (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        (extChartAt I x x) := (rfl)

@[simp]
theorem mextDerivWithin_univ (φ : RoughForm I M F k) :
    mextDerivWithin φ univ = mextDeriv φ := (rfl)

theorem mextDeriv_def (φ : RoughForm I M F k) (x : M) :
    mextDeriv φ x = extDerivWithin (E := E) (φ.inChartAt x) (range I) (extChartAt I x x) := by
  rw [← mextDerivWithin_univ, mextDerivWithin_def, preimage_univ, univ_inter]

/-! ### Locality -/

/-- The exterior derivative within a set does not change when the set is modified away from a
point `y`, as long as it is unchanged near `x` (punctured at `y`). -/
theorem mextDerivWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mextDerivWithin φ s x = mextDerivWithin φ t x :=
  extDerivWithin_congr_set' _ (preimage_extChartAt_eventuallyEqSet_compl_singleton y h)

/-- The exterior derivative within a set only depends on the germ of the set. -/
theorem mextDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mextDerivWithin φ s x = mextDerivWithin φ t x :=
  mextDerivWithin_congr_set' x <| h.filter_mono inf_le_left

theorem mextDerivWithin_inter (ht : t ∈ 𝓝 x) :
    mextDerivWithin φ (s ∩ t) x = mextDerivWithin φ s x := by
  apply mextDerivWithin_congr_set
  filter_upwards [ht] with y hy
  simp [hy]

theorem mextDerivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : mextDerivWithin φ s x = mextDeriv φ x := by
  rw [← mextDerivWithin_univ, ← univ_inter s, mextDerivWithin_inter h]

theorem mextDerivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mextDerivWithin φ s x = mextDeriv φ x :=
  mextDerivWithin_of_mem_nhds (hs.mem_nhds hx)

/-- The exterior derivative within a set only depends on the form near the point within the
set, and at the point. -/
theorem mextDerivWithin_congr_of_eventuallyEq (h : ∀ᶠ y in 𝓝[s] x, φ y = η y)
    (hx : φ x = η x) :
    mextDerivWithin φ s x = mextDerivWithin η s x := by
  rw [mextDerivWithin_def, mextDerivWithin_def]
  apply Filter.EventuallyEq.extDerivWithin_eq
  · apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      h (by simp)] with z hz
    ext v
    simp only [RoughForm.inChartAt_apply]
    rw [hz]
  -- at the chart point, `(extChartAt I x).symm (extChartAt I x x) = x`
  · ext v
    simp only [RoughForm.inChartAt_apply]
    rw [show φ ((extChartAt I x).symm (extChartAt I x x)) =
        η ((extChartAt I x).symm (extChartAt I x x)) by rw [extChartAt_to_inv]; exact hx]

theorem mextDerivWithin_congr_of_eventuallyEq_of_mem (h : ∀ᶠ y in 𝓝[s] x, φ y = η y)
    (hx : x ∈ s) : mextDerivWithin φ s x = mextDerivWithin η s x :=
  mextDerivWithin_congr_of_eventuallyEq h (h.self_of_nhdsWithin hx)

theorem mextDerivWithin_congr (h : ∀ y ∈ s, φ y = η y) (hx : φ x = η x) :
    mextDerivWithin φ s x = mextDerivWithin η s x :=
  mextDerivWithin_congr_of_eventuallyEq (eventually_nhdsWithin_of_forall h) hx

/-- The exterior derivative only depends on the germ of the form. -/
theorem mextDeriv_congr_of_eventuallyEq (h : ∀ᶠ y in 𝓝 x, φ y = η y) :
    mextDeriv φ x = mextDeriv η x := by
  rw [← mextDerivWithin_univ, ← mextDerivWithin_univ]
  exact mextDerivWithin_congr_of_eventuallyEq (h.filter_mono nhdsWithin_le_nhds) h.self_of_nhds

/-! ### Linearity -/

@[simp]
theorem mextDerivWithin_zero (s : Set M) (x : M) :
    mextDerivWithin (0 : RoughForm I M F k) s x = 0 := by
  rw [mextDerivWithin_def, RoughForm.inChartAt_zero]
  exact ContinuousAlternatingMap.extDerivWithin_const 0 _ _

@[simp]
theorem mextDeriv_zero : mextDeriv (0 : RoughForm I M F k) = 0 :=
  funext fun x ↦ mextDerivWithin_zero univ x

/-- The exterior derivative is additive on forms whose coordinate expressions in the chart at the
point are differentiable there. -/
theorem mextDerivWithin_add (hs : UniqueMDiffWithinAt I s x)
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x))
    (hη : DifferentiableWithinAt ℝ (η.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x)) :
    mextDerivWithin (φ + η) s x = mextDerivWithin φ s x + mextDerivWithin η s x := by
  rw [mextDerivWithin_def, RoughForm.inChartAt_add]
  exact extDerivWithin_add hs hφ hη

/-- The exterior derivative is additive on forms whose coordinate expressions in the chart at the
point are differentiable within `range I` there. -/
theorem mextDeriv_add
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) (range I) (extChartAt I x x))
    (hη : DifferentiableWithinAt ℝ (η.inChartAt x) (range I) (extChartAt I x x)) :
    mextDeriv (φ + η) x = mextDeriv φ x + mextDeriv η x := by
  simp only [← mextDerivWithin_univ]
  exact mextDerivWithin_add (uniqueMDiffWithinAt_univ I) (by simpa using hφ) (by simpa using hη)

/-- The exterior derivative commutes with real scalars wherever derivatives within the set are
unique; no differentiability of the form is needed. -/
@[simp]
theorem mextDerivWithin_smul (c : ℝ) (hs : UniqueMDiffWithinAt I s x) :
    mextDerivWithin (c • φ) s x = c • mextDerivWithin φ s x := by
  rw [mextDerivWithin_def, RoughForm.inChartAt_smul]
  exact extDerivWithin_smul c _ hs

@[simp]
theorem mextDeriv_smul (c : ℝ) (φ : RoughForm I M F k) : mextDeriv (c • φ) = c • mextDeriv φ :=
  funext fun _ ↦ mextDerivWithin_smul c (uniqueMDiffWithinAt_univ I)

@[simp]
theorem mextDerivWithin_neg (hs : UniqueMDiffWithinAt I s x) :
    mextDerivWithin (-φ) s x = -mextDerivWithin φ s x := by
  rw [← neg_one_smul ℝ φ, mextDerivWithin_smul _ hs, neg_one_smul]

@[simp]
theorem mextDeriv_neg (φ : RoughForm I M F k) : mextDeriv (-φ) = -mextDeriv φ := by
  rw [← neg_one_smul ℝ φ, mextDeriv_smul, neg_one_smul]

/-- The exterior derivative within a set is subtractive on forms whose coordinate expressions in
the chart at the point are differentiable there, wherever derivatives within the set are
unique. -/
theorem mextDerivWithin_sub (hs : UniqueMDiffWithinAt I s x)
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x))
    (hη : DifferentiableWithinAt ℝ (η.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x)) :
    mextDerivWithin (φ - η) s x = mextDerivWithin φ s x - mextDerivWithin η s x := by
  rw [sub_eq_add_neg, mextDerivWithin_add hs hφ (by simpa using hη.neg),
    mextDerivWithin_neg hs, sub_eq_add_neg]

/-! ### The model space -/

/-- Over the model space `𝓘(ℝ, E)`, the coordinate expression of a form is the form itself. -/
@[simp]
theorem RoughForm.inChartAt_modelSpace (φ : RoughForm 𝓘(ℝ, E) E F k) (x : E) :
    φ.inChartAt x = φ := by
  funext z
  ext v
  rw [RoughForm.inChartAt_apply, extChartAt_model_space_eq_id]
  simp only [PartialEquiv.refl_symm, PartialEquiv.refl_coe, modelWithCornersSelf_coe, range_id,
    mfderivWithin_univ]
  rw [mfderiv_id]
  rfl

/-- Over the model space `𝓘(ℝ, E)`, the manifold exterior derivative within a set is the flat
exterior derivative `extDerivWithin`. -/
theorem mextDerivWithin_eq_extDerivWithin (φ : RoughForm 𝓘(ℝ, E) E F k) (s : Set E) (x : E) :
    mextDerivWithin φ s x = extDerivWithin (E := E) (F := F) φ s x := by
  simp only [mextDerivWithin_def, RoughForm.inChartAt_modelSpace, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.refl_coe, preimage_id, modelWithCornersSelf_coe,
    range_id, inter_univ, id_eq]
  rfl

/-- Over the model space `𝓘(ℝ, E)`, the manifold exterior derivative is the flat exterior
derivative `extDeriv`. -/
theorem mextDeriv_eq_extDeriv (φ : RoughForm 𝓘(ℝ, E) E F k) (x : E) :
    mextDeriv φ x = extDeriv (E := E) (F := F) φ x := by
  rw [← mextDerivWithin_univ, mextDerivWithin_eq_extDerivWithin]
  exact congrFun (extDerivWithin_univ (𝕜 := ℝ) (E := E) (F := F) φ) x

/-! ### Functions -/

/-- The coordinate expression of the `0`-form of a function is the `0`-form of the function
written in the chart. -/
@[simp]
theorem RoughForm.inChartAt_ofFunction (f : M → F) (x₀ : M) :
    (RoughForm.ofFunction I f).inChartAt x₀ = fun z ↦
      ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f ((extChartAt I x₀).symm z)) := by
  funext z
  ext v
  rw [inChartAt_apply, ofFunction_apply, ContinuousAlternatingMap.constOfIsEmpty_apply]

/-- The exterior derivative of the `0`-form of a function is its manifold derivative, read as a
`1`-form. -/
theorem mextDerivWithin_ofFunction (f : M → F) (hs : UniqueMDiffWithinAt I s x) :
    mextDerivWithin (RoughForm.ofFunction I f) s x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) F (0 : Fin 1)
        (mvfderivWithin I f s x) := by
  rw [mextDerivWithin_def, RoughForm.inChartAt_ofFunction]
  refine (extDerivWithin_constOfIsEmpty (f ∘ (extChartAt I x).symm) hs).trans ?_
  congr 1
  ext v
  by_cases hf : MDifferentiableWithinAt I 𝓘(ℝ, F) f s x
  · -- the identifications of tangent spaces with model spaces inside `mfderivWithin` are the
    -- identity maps
    simp [mvfderivWithin, mfderivWithin, hf, writtenInExtChartAt]
    rfl
  · have hd : ¬DifferentiableWithinAt ℝ (f ∘ (extChartAt I x).symm)
        ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := fun hd ↦
      hf (mdifferentiableWithinAt_iff.2 ⟨continuousWithinAt_iff_source.2 hd.continuousWithinAt,
        by simpa [extChartAt_model_space_eq_id] using hd⟩)
    rw [fderivWithin_zero_of_not_differentiableWithinAt hd]
    simp only [mvfderivWithin, mfderivWithin_zero_of_not_mdifferentiableWithinAt hf,
      ContinuousLinearMap.comp_zero]
    rfl

/-- The exterior derivative of the `0`-form of a function is its manifold derivative, read as a
`1`-form. -/
theorem mextDeriv_ofFunction (f : M → F) (x : M) :
    mextDeriv (RoughForm.ofFunction I f) x =
      ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) F (0 : Fin 1)
        (mvfderiv I f x) := by
  rw [← mextDerivWithin_univ, mextDerivWithin_ofFunction f (uniqueMDiffWithinAt_univ I),
    mvfderivWithin_univ]

end TauCeti
