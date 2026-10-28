/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Interior
public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The Lie derivative of differential forms on manifolds

The Lie derivative `mlieDerivFormWithin V φ s x` of a rough fixed-coefficient form `φ` along a
vector field `V` is the flat Lie derivative `TauCeti.lieDerivFormWithin` of the coordinate
expressions of `φ` and `V` in the preferred chart at `x`, with derivatives taken within
`(extChartAt I x).symm ⁻¹' s ∩ range I`. This is the construction of `mextDerivWithin` and of
Mathlib's `VectorField.mlieBracketWithin`, so it is meaningful at boundary and corner points.
Like them, it is total, with junk values where `φ` or `V` is not differentiable, and needs no
flow.

The two characterizations below show that the definition is intrinsic.

* **The bracket formula** [Lee, Cor. 12.33]: on differentiable vector fields `X₀, …, Xₖ₋₁`,
  `L_V φ (X₀, …, Xₖ₋₁) = V (φ (X₀, …, Xₖ₋₁)) - ∑ i, φ (X₀, …, [V, Xᵢ], …, Xₖ₋₁)`.
* **Cartan's magic formula** [Lee, Thm. 14.35]: `L_V φ = ι_V dφ + d (ι_V φ)` for a
  differentiable form and a differentiable vector field, and `L_V f = ι_V df` in degree zero
  without hypotheses. On a closed form it reads `L_V φ = d (ι_V φ)`.

## Main declarations

* `TauCeti.mlieDerivFormWithin`, `TauCeti.mlieDerivForm`: the Lie derivative of a rough form.
* `TauCeti.mlieDerivFormWithin_add`, `TauCeti.mlieDerivFormWithin_smul`: linearity in the form.
* `TauCeti.mlieDerivFormWithin_apply_vectorField`, `TauCeti.mlieDerivForm_apply_vectorField`:
  the bracket formula.
* `TauCeti.mlieDerivFormWithin_eq_interior_mextDerivWithin_add`,
  `TauCeti.mlieDerivForm_eq_interior_mextDeriv_add`: Cartan's magic formula.
* `TauCeti.mlieDerivFormWithin_eq_mextDerivWithin_interior`,
  `TauCeti.mlieDerivForm_eq_mextDeriv_interior`: on closed forms, `L_V φ = d (ι_V φ)`.
* `TauCeti.mlieDerivFormWithin_eq_lieDerivFormWithin`: over the model space, the manifold Lie
  derivative is the flat one.
* `TauCeti.SmoothForm.mlieDerivForm_eq_interior_mextDeriv_add`,
  `TauCeti.SmoothForm.mlieDerivForm_eq_mextDeriv_interior`: bundled smooth-form entry points.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Corollary 12.33 and Theorem 14.35.
-/

public section

noncomputable section

open Set Filter Bundle VectorField
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The Lie derivative of a rough form along a vector field within a set `s`, at a point `x`: the
flat Lie derivative of the coordinate expressions of the form and of the field in the chart at
`x`, within `(extChartAt I x).symm ⁻¹' s ∩ range I` at the chart point of `x`. Tangent vectors at
`x` are read in that same chart. Total, with junk values where the form or the field is not
differentiable. -/
def mlieDerivFormWithin (V : (x : M) → TangentSpace I x) (φ : RoughForm I M F k) (s : Set M)
    (x : M) : TangentSpace I x [⋀^Fin k]→L[ℝ] F :=
  lieDerivFormWithin (E := E)
    (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I))
    (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x)

/-- The Lie derivative of a rough form along a vector field. -/
def mlieDerivForm (V : (x : M) → TangentSpace I x) (φ : RoughForm I M F k) :
    RoughForm I M F k :=
  fun x ↦ mlieDerivFormWithin V φ univ x

variable {V : (x : M) → TangentSpace I x} {s : Set M} {x : M}

theorem mlieDerivFormWithin_def (V : (x : M) → TangentSpace I x) (φ : RoughForm I M F k)
    (s : Set M) (x : M) :
    mlieDerivFormWithin V φ s x =
      lieDerivFormWithin (E := E)
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I))
        (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := (rfl)

@[simp]
theorem mlieDerivFormWithin_univ (V : (x : M) → TangentSpace I x) (φ : RoughForm I M F k) :
    mlieDerivFormWithin V φ univ = mlieDerivForm V φ := (rfl)

theorem mlieDerivForm_def (V : (x : M) → TangentSpace I x) (φ : RoughForm I M F k) (x : M) :
    mlieDerivForm V φ x =
      lieDerivFormWithin (E := E)
        (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I))
        (φ.inChartAt x) (range I) (extChartAt I x x) := by
  rw [← mlieDerivFormWithin_univ, mlieDerivFormWithin_def, preimage_univ, univ_inter]

/-! ### Linearity in the form -/

@[simp]
theorem mlieDerivFormWithin_zero (V : (x : M) → TangentSpace I x) (s : Set M) (x : M) :
    mlieDerivFormWithin V (0 : RoughForm I M F k) s x = 0 := by
  rw [mlieDerivFormWithin_def, RoughForm.inChartAt_zero]
  exact lieDerivFormWithin_zero _ _ _

@[simp]
theorem mlieDerivForm_zero (V : (x : M) → TangentSpace I x) :
    mlieDerivForm V (0 : RoughForm I M F k) = 0 :=
  funext (mlieDerivFormWithin_zero V univ)

/-- The Lie derivative within a set is additive on forms whose coordinate expressions in the
chart at the point are differentiable there. -/
theorem mlieDerivFormWithin_add {φ η : RoughForm I M F k} (hs : UniqueMDiffWithinAt I s x)
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x))
    (hη : DifferentiableWithinAt ℝ (η.inChartAt x) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x)) :
    mlieDerivFormWithin V (φ + η) s x =
      mlieDerivFormWithin V φ s x + mlieDerivFormWithin V η s x := by
  rw [mlieDerivFormWithin_def, RoughForm.inChartAt_add]
  exact lieDerivFormWithin_add hs hφ hη

/-- The Lie derivative is additive on forms whose coordinate expressions in the chart at the point
are differentiable within `range I` there. -/
theorem mlieDerivForm_add {φ η : RoughForm I M F k}
    (hφ : DifferentiableWithinAt ℝ (φ.inChartAt x) (range I) (extChartAt I x x))
    (hη : DifferentiableWithinAt ℝ (η.inChartAt x) (range I) (extChartAt I x x)) :
    mlieDerivForm V (φ + η) x = mlieDerivForm V φ x + mlieDerivForm V η x := by
  simp only [← mlieDerivFormWithin_univ]
  exact mlieDerivFormWithin_add (uniqueMDiffWithinAt_univ I) (by simpa using hφ)
    (by simpa using hη)

/-- The Lie derivative within a set commutes with real scalars wherever derivatives within the set
are unique; no differentiability of the form is needed. -/
@[simp]
theorem mlieDerivFormWithin_smul (c : ℝ) (φ : RoughForm I M F k)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivFormWithin V (c • φ) s x = c • mlieDerivFormWithin V φ s x := by
  rw [mlieDerivFormWithin_def, RoughForm.inChartAt_smul]
  exact lieDerivFormWithin_smul c _ hs

@[simp]
theorem mlieDerivForm_smul (c : ℝ) (φ : RoughForm I M F k) :
    mlieDerivForm V (c • φ) = c • mlieDerivForm V φ :=
  funext fun _ ↦ mlieDerivFormWithin_smul c φ (uniqueMDiffWithinAt_univ I)

/-! ### The model space -/

/-- Over the model space `𝓘(ℝ, E)`, the manifold Lie derivative within a set is the flat Lie
derivative `lieDerivFormWithin`. -/
theorem mlieDerivFormWithin_eq_lieDerivFormWithin (V : (x : E) → TangentSpace 𝓘(ℝ, E) x)
    (φ : RoughForm 𝓘(ℝ, E) E F k) (s : Set E) (x : E) :
    mlieDerivFormWithin V φ s x = lieDerivFormWithin (𝕜 := ℝ) V φ s x := by
  simp only [mlieDerivFormWithin_def, RoughForm.inChartAt_modelSpace,
    extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, preimage_id,
    modelWithCornersSelf_coe, range_id, inter_univ, id_eq, VectorField.mpullbackWithin_univ,
    VectorField.mpullback_id]
  rfl

/-- Over the model space `𝓘(ℝ, E)`, the manifold Lie derivative is the flat Lie derivative
`lieDerivForm`. -/
theorem mlieDerivForm_eq_lieDerivForm (V : (x : E) → TangentSpace 𝓘(ℝ, E) x)
    (φ : RoughForm 𝓘(ℝ, E) E F k) (x : E) :
    mlieDerivForm V φ x = lieDerivForm (𝕜 := ℝ) V φ x := by
  rw [← mlieDerivFormWithin_univ, mlieDerivFormWithin_eq_lieDerivFormWithin]
  exact congrFun (lieDerivFormWithin_univ (𝕜 := ℝ) V φ) x

variable [IsManifold I 1 M]

/-! ### The bracket formula -/

/-- **The bracket formula** within a set: evaluated on differentiable vector fields
`X₀, …, Xₖ₋₁`, the Lie derivative of a differentiable form is the derivative of
`φ (X₀, …, Xₖ₋₁)` along `V` minus the evaluations of `φ` with one field `Xᵢ` replaced by the
bracket `[V, Xᵢ]`. No regularity of `V` is needed. -/
theorem mlieDerivFormWithin_apply_vectorField {φ : RoughForm I M F k}
    {X : Fin k → (y : M) → TangentSpace I y}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) s x)
    (hX : ∀ i, MDifferentiableWithinAt I I.tangent (fun y ↦ (X i y : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivFormWithin V φ s x (X · x) =
      mvfderivWithin I (fun y ↦ φ y (X · y)) s x (V x) -
        ∑ i, φ x (Function.update (X · x) i (mlieBracketWithin I V (X i) s x)) := by
  let X' : Fin k → E → E := fun i ↦
    VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm (X i) (range I)
  have hφ' := φ.differentiableWithinAt_inChartAt hφ
  have hX' (i : Fin k) := (hX i).differentiableWithinAt_mpullbackWithin_extChartAt_symm
  have hvalues : (X' · (extChartAt I x x)) = (X · x) :=
    funext fun i ↦ VectorField.mpullbackWithin_extChartAt_symm_self (X i) x
  have hflat := lieDerivFormWithin_apply_vectorField
    (V := VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I)) X' hφ' hX' hs
  rw [hvalues] at hflat
  rw [mlieDerivFormWithin_def]
  refine hflat.trans ?_
  rw [fderivWithin_inChartAt_apply_mpullbackWithin φ X hφ' hX',
    VectorField.mpullbackWithin_extChartAt_symm_self, RoughForm.inChartAt_extChartAt_self]
  simp only [X', VectorField.lieBracketWithin_mpullbackWithin_extChartAt_symm]
  rfl

/-- **The bracket formula**: evaluated on differentiable vector fields `X₀, …, Xₖ₋₁`, the Lie
derivative of a differentiable form is the derivative of `φ (X₀, …, Xₖ₋₁)` along `V` minus the
evaluations of `φ` with one field `Xᵢ` replaced by the bracket `[V, Xᵢ]`. -/
theorem mlieDerivForm_apply_vectorField {φ : RoughForm I M F k}
    {X : Fin k → (y : M) → TangentSpace I y}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F) y (φ y)) x)
    (hX : ∀ i, MDifferentiableAt I I.tangent (fun y ↦ (X i y : TangentBundle I M)) x) :
    mlieDerivForm V φ x (X · x) =
      mvfderiv I (fun y ↦ φ y (X · y)) x (V x) -
        ∑ i, φ x (Function.update (X · x) i (mlieBracket I V (X i) x)) := by
  simpa only [mlieDerivFormWithin_univ, mvfderivWithin_univ, mlieBracketWithin_univ] using
    mlieDerivFormWithin_apply_vectorField (V := V) hφ.mdifferentiableWithinAt
      (fun i ↦ (hX i).mdifferentiableWithinAt) (uniqueMDiffWithinAt_univ I)

/-! ### Cartan's magic formula -/

/-- **Cartan's magic formula** within a set, `L_V φ = ι_V dφ + d (ι_V φ)`, for a form and a vector
field differentiable within the set at the point. -/
theorem mlieDerivFormWithin_eq_interior_mextDerivWithin_add {φ : RoughForm I M F (k + 1)}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (φ y)) s x)
    (hV : MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) :
    mlieDerivFormWithin V φ s x =
      RoughForm.interior V (mextDerivWithin φ s) x + mextDerivWithin (φ.interior V) s x := by
  rw [mlieDerivFormWithin_def, lieDerivFormWithin_eq_curryLeft_extDerivWithin_add
    (φ.differentiableWithinAt_inChartAt hφ)
    hV.differentiableWithinAt_mpullbackWithin_extChartAt_symm hs,
    VectorField.mpullbackWithin_extChartAt_symm_self, RoughForm.interior_apply_eq_curryLeft,
    mextDerivWithin_def, mextDerivWithin_def]
  congr 1
  refine Filter.EventuallyEq.extDerivWithin_eq ?_
    (φ.inChartAt_interior V (mem_extChartAt_target x)).symm
  filter_upwards [nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x)]
    with z hz
  exact (φ.inChartAt_interior V hz).symm

/-- **Cartan's magic formula** at a point, `L_V φ = ι_V dφ + d (ι_V φ)`, for a form and a vector
field differentiable at the point. -/
theorem mlieDerivForm_eq_interior_mextDeriv_add_apply {φ : RoughForm I M F (k + 1)}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (φ y)) x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x) :
    mlieDerivForm V φ x = (mextDeriv φ).interior V x + mextDeriv (φ.interior V) x := by
  simpa only [mlieDerivFormWithin_univ, mextDerivWithin_univ] using
    mlieDerivFormWithin_eq_interior_mextDerivWithin_add hφ.mdifferentiableWithinAt
      hV.mdifferentiableWithinAt (uniqueMDiffWithinAt_univ I)

/-- **Cartan's magic formula** `L_V = ι_V ∘ d + d ∘ ι_V` on differentiable forms, along a
differentiable vector field. -/
theorem mlieDerivForm_eq_interior_mextDeriv_add {φ : RoughForm I M F (k + 1)}
    (hφ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (φ y)))
    (hV : MDifferentiable I I.tangent (fun y ↦ (V y : TangentBundle I M))) :
    mlieDerivForm V φ = (mextDeriv φ).interior V + mextDeriv (φ.interior V) :=
  funext fun x ↦ mlieDerivForm_eq_interior_mextDeriv_add_apply (hφ x) (hV x)

/-- For a form whose exterior derivative within the set vanishes at the point, **Cartan's
formula** within the set reduces to `L_V φ = d (ι_V φ)`. -/
theorem mlieDerivFormWithin_eq_mextDerivWithin_interior {φ : RoughForm I M F (k + 1)}
    (hφ : MDifferentiableWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (φ y)) s x)
    (hV : MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x)
    (hs : UniqueMDiffWithinAt I s x) (hdφ : mextDerivWithin φ s x = 0) :
    mlieDerivFormWithin V φ s x = mextDerivWithin (φ.interior V) s x := by
  rw [mlieDerivFormWithin_eq_interior_mextDerivWithin_add hφ hV hs, add_eq_right]
  ext v
  simp [hdφ]

/-- For a form whose exterior derivative vanishes at the point, **Cartan's formula** reduces to
`L_V φ = d (ι_V φ)`. -/
theorem mlieDerivForm_eq_mextDeriv_interior_apply {φ : RoughForm I M F (k + 1)}
    (hφ : MDifferentiableAt I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (φ y)) x)
    (hV : MDifferentiableAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) x)
    (hdφ : mextDeriv φ x = 0) :
    mlieDerivForm V φ x = mextDeriv (φ.interior V) x := by
  rw [mlieDerivForm_eq_interior_mextDeriv_add_apply hφ hV, add_eq_right]
  ext v
  simp [hdφ]

/-- On a differentiable closed form, along a differentiable vector field, **Cartan's formula**
reduces to `L_V φ = d (ι_V φ)`. -/
theorem mlieDerivForm_eq_mextDeriv_interior {φ : RoughForm I M F (k + 1)}
    (hφ : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] F))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] F) y (φ y)))
    (hV : MDifferentiable I I.tangent (fun y ↦ (V y : TangentBundle I M)))
    (hdφ : mextDeriv φ = 0) :
    mlieDerivForm V φ = mextDeriv (φ.interior V) :=
  funext fun x ↦ mlieDerivForm_eq_mextDeriv_interior_apply (hφ x) (hV x) (congrFun hdφ x)

/-- Cartan's formula in degree zero within a set, `L_V f = ι_V df`, holds for every rough
`0`-form and every vector field. -/
theorem mlieDerivFormWithin_eq_interior_mextDerivWithin (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F 0) (s : Set M) (x : M) :
    mlieDerivFormWithin V φ s x = RoughForm.interior V (mextDerivWithin φ s) x := by
  rw [mlieDerivFormWithin_def]
  refine (lieDerivFormWithin_eq_curryLeft_extDerivWithin _ _ _ _).trans ?_
  rw [VectorField.mpullbackWithin_extChartAt_symm_self, RoughForm.interior_apply_eq_curryLeft,
    mextDerivWithin_def]

/-- Cartan's formula in degree zero, `L_V f = ι_V df`, holds for every rough `0`-form and every
vector field. -/
theorem mlieDerivForm_eq_interior_mextDeriv (V : (x : M) → TangentSpace I x)
    (φ : RoughForm I M F 0) : mlieDerivForm V φ = (mextDeriv φ).interior V := by
  funext x
  simpa only [mlieDerivFormWithin_univ, mextDerivWithin_univ] using
    mlieDerivFormWithin_eq_interior_mextDerivWithin V φ univ x

namespace SmoothForm

/-- Cartan's magic formula for a smooth fixed-coefficient form, exposed through the bundled
`SmoothForm` carrier. The vector field is supplied as a differentiable tangent-valued map. -/
theorem mlieDerivForm_eq_interior_mextDeriv_add {φ : SmoothForm I M F (k + 1)}
    {V : (x : M) → TangentSpace I x}
    (hV : MDifferentiable I I.tangent (fun y ↦ (V y : TangentBundle I M))) :
    mlieDerivForm V φ.1 = (mextDeriv φ.1).interior V + mextDeriv (φ.1.interior V) := by
  exact TauCeti.mlieDerivForm_eq_interior_mextDeriv_add φ.mdifferentiable hV

/-- On a smooth closed form, along a differentiable vector field, the Lie derivative is the exterior
derivative of its contraction. -/
theorem mlieDerivForm_eq_mextDeriv_interior {φ : SmoothForm I M F (k + 1)}
    {V : (x : M) → TangentSpace I x}
    (hV : MDifferentiable I I.tangent (fun y ↦ (V y : TangentBundle I M)))
    (hφ : φ.IsClosed) :
    mlieDerivForm V φ.1 = mextDeriv (φ.1.interior V) := by
  exact TauCeti.mlieDerivForm_eq_mextDeriv_interior φ.mdifferentiable hV
    ((SmoothForm.isClosed_def φ).mp hφ)

end SmoothForm

end TauCeti
