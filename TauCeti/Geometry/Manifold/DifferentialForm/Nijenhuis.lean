/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.AlmostComplexType
public import TauCeti.Geometry.Manifold.DifferentialForm.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.Nijenhuis
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The Nijenhuis tensor and the exterior derivative of one-forms

Let `J` be a smooth almost complex structure on a finite-dimensional manifold and let `F` be a
complex normed space. The exterior derivative of a complex-valued smooth one-form `α` of type
`(1,0)` has components of types `(2,0)`, `(1,1)` and `(0,2)`, and its `(0,2)` component, the
component of bidegree `(-1,2)`, involves no derivative of `α` at all: it is the tensor
`(v, w) ↦ α (N_J (v, w)) / 4`, where `N_J` is the Nijenhuis tensor
`TauCeti.SmoothAlmostComplexStructure.nijenhuis`. Symmetrically, the `(2,0)` component of the
exterior derivative of a one-form `α` of type `(0,1)`, of bidegree `(2,-1)`, is
`(v, w) ↦ α (N_J (v, w)) / 4`.

Consequently these components vanish exactly when `α ∘ N_J = 0`, and in particular whenever
`N_J = 0`: then, by the decomposition of `d` into its four bidegrees, the exterior derivative of a
one-form of type `(1,0)` has only components of types `(2,0)` and `(1,1)`, and that of a one-form
of type `(0,1)` only components of types `(1,1)` and `(0,2)`, as on a complex manifold.

## Main declarations

* `TauCeti.SmoothForm.IsOfType.typeProjection_zero_two_mextDerivₗ_apply`: the `(0,2)` component
  of the exterior derivative of a `(1,0)`-form `α` is `α ∘ N_J / 4`.
* `TauCeti.SmoothForm.IsOfType.typeProjection_two_zero_mextDerivₗ_apply`: the `(2,0)` component
  of the exterior derivative of a `(0,1)`-form `α` is `α ∘ N_J / 4`.
* `TauCeti.SmoothForm.IsOfType.typeProjection_zero_two_mextDerivₗ_eq_zero_iff`,
  `TauCeti.SmoothForm.IsOfType.typeProjection_two_zero_mextDerivₗ_eq_zero_iff`: these components
  vanish exactly when `α ∘ N_J = 0`.
* `TauCeti.SmoothForm.IsOfType.typeProjection_zero_two_mextDerivₗ_eq_zero`,
  `TauCeti.SmoothForm.IsOfType.typeProjection_two_zero_mextDerivₗ_eq_zero`: they vanish when
  `N_J = 0`.

## Implementation notes

Both sides are evaluated on vector fields extending the given tangent vectors. By the invariant
formula `dα(X, Y) = X (α Y) - Y (α X) - α [X, Y]`, the combination
`dα(X, Y) - dα(JX, JY) + c • (dα(JX, Y) + dα(X, JY))`, where `α (J v) = c • α v` and `c² = -1`,
has no derivative terms left, and its bracket terms are `α (N_J (X, Y))`. By the fibrewise
formulas `ContinuousLinearMap.typeProjection_zero_two_apply` and
`ContinuousLinearMap.typeProjection_two_zero_apply`, this combination is four times the `(0,2)`
component of `dα` when `c = I`, and four times its `(2,0)` component when `c = -I`.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005,
  Section 2.6.
-/

public section

noncomputable section

open Bundle FiberBundle VectorField
open scoped Manifold ContDiff

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TauCeti

namespace SmoothForm

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm I M F 1}

/-- If `α (J v) = c • α v` with `c² = -1`, then
`dα(v, w) - dα(Jv, Jw) + c • (dα(Jv, w) + dα(v, Jw)) = α (N_J (v, w))`. -/
private theorem mextDeriv_sub_add_smul_eq_nijenhuis {c : ℂ} (hc : c * c = -1)
    (hα : ∀ y z, α.1 y ![J y z] = c • α.1 y ![z]) (x : M) (v w : TangentSpace I x) :
    mextDeriv α.1 x ![v, w] - mextDeriv α.1 x ![J x v, J x w] +
        c • (mextDeriv α.1 x ![J x v, w] + mextDeriv α.1 x ![v, J x w]) =
      α.1 x ![J.nijenhuis x v w] := by
  -- Extend `v` and `w` to vector fields and expand the four exterior derivatives and the
  -- Nijenhuis tensor through vector fields.
  obtain ⟨X, hX, rfl⟩ : ∃ X : (y : M) → TangentSpace I y,
      MDifferentiableAt I I.tangent (fun y ↦ (X y : TangentBundle I M)) x ∧ X x = v :=
    ⟨extend E v, mdifferentiableAt_extend I E v, extend_apply_self E v⟩
  obtain ⟨Y, hY, rfl⟩ : ∃ Y : (y : M) → TangentSpace I y,
      MDifferentiableAt I I.tangent (fun y ↦ (Y y : TangentBundle I M)) x ∧ Y x = w :=
    ⟨extend E w, mdifferentiableAt_extend I E w, extend_apply_self E w⟩
  have hJX : MDifferentiableAt I I.tangent
      (fun y ↦ ((J y (X y) : TangentSpace I y) : TangentBundle I M)) x :=
    J.mdifferentiableAt_apply mdifferentiableAt_id hX
  have hJY : MDifferentiableAt I I.tangent
      (fun y ↦ ((J y (Y y) : TangentSpace I y) : TangentBundle I M)) x :=
    J.mdifferentiableAt_apply mdifferentiableAt_id hY
  -- The derivative of `α (J Z)` is `c` times the derivative of `α Z`.
  have hd (Z : (y : M) → TangentSpace I y)
      (hZ : MDifferentiableAt I I.tangent (fun y ↦ (Z y : TangentBundle I M)) x) :
      mvfderiv I (fun y ↦ α.1 y ![J y (Z y)]) x = c • mvfderiv I (fun y ↦ α.1 y ![Z y]) x := by
    have hαZ : MDifferentiableAt I 𝓘(ℝ, F) (fun y ↦ α.1 y ![Z y]) x := by
      have h := α.mdifferentiableAt_apply_vectorField (V := ![Z]) (x := x)
        (fun i ↦ by fin_cases i; exact hZ)
      convert h using 3 with y
      funext i
      fin_cases i
      rfl
    simp only [hα]
    exact mvfderiv_const_smul hαZ c
  rw [J.nijenhuis_apply hX hY, mextDeriv_apply_one hX hY, mextDeriv_apply_one hJX hJY,
    mextDeriv_apply_one hJX hY, mextDeriv_apply_one hX hJY, hd Y hY, hd X hX]
  -- What remains is linear algebra in the values of `α x` on tangent vectors, where the
  -- derivative terms cancel because `1 + c² = 0`.
  set ℓ := (ContinuousAlternatingMap.ofSubsingleton ℝ (TangentSpace I x) F (0 : Fin 1)).symm
    (α.1 x)
  have hℓ (u : TangentSpace I x) : α.1 x ![u] = ℓ u := by
    rw [ContinuousAlternatingMap.ofSubsingleton_symm_apply_apply]
    congr 1
    funext i
    fin_cases i
    rfl
  have hJℓ (u : TangentSpace I x) : ℓ (J x u) = c • ℓ u := by rw [← hℓ, ← hℓ, hα]
  simp only [hℓ, map_sub, hJℓ, smul_apply]
  linear_combination (norm := module) hc • (mvfderiv I (fun y ↦ α.1 y ![Y y]) x (X x) -
    mvfderiv I (fun y ↦ α.1 y ![X y]) x (Y x))

/-- **The `(-1,2)` component of `d` on `(1,0)`-forms is the Nijenhuis tensor.** For a smooth
one-form `α` of type `(1,0)`, the `(0,2)` component of `dα` is `(v, w) ↦ α (N_J (v, w)) / 4`. -/
theorem IsOfType.typeProjection_zero_two_mextDerivₗ_apply (hα : α.IsOfType J 1 0) (x : M)
    (v w : TangentSpace I x) :
    (J.typeProjection 0 2 (mextDerivₗ I 1 α)).1 x ![v, w] =
      (4 : ℂ)⁻¹ • α.1 x ![J.nijenhuis x v w] := by
  rw [SmoothAlmostComplexStructure.coe_typeProjection, mextDerivₗ_apply,
    ContinuousLinearMap.typeProjection_zero_two_apply (J.apply_apply x),
    ← mextDeriv_sub_add_smul_eq_nijenhuis Complex.I_mul_I (isOfType_one_zero_iff.1 hα)]

/-- **The `(2,-1)` component of `d` on `(0,1)`-forms is the Nijenhuis tensor.** For a smooth
one-form `α` of type `(0,1)`, the `(2,0)` component of `dα` is `(v, w) ↦ α (N_J (v, w)) / 4`. -/
theorem IsOfType.typeProjection_two_zero_mextDerivₗ_apply (hα : α.IsOfType J 0 1) (x : M)
    (v w : TangentSpace I x) :
    (J.typeProjection 2 0 (mextDerivₗ I 1 α)).1 x ![v, w] =
      (4 : ℂ)⁻¹ • α.1 x ![J.nijenhuis x v w] := by
  rw [SmoothAlmostComplexStructure.coe_typeProjection, mextDerivₗ_apply,
    ContinuousLinearMap.typeProjection_two_zero_apply (J.apply_apply x),
    ← mextDeriv_sub_add_smul_eq_nijenhuis (by simp) (isOfType_zero_one_iff.1 hα)]
  module

/-- The exterior derivative of a smooth one-form `α` of type `(1,0)` has no `(0,2)` component
exactly when `α ∘ N_J = 0`. -/
theorem IsOfType.typeProjection_zero_two_mextDerivₗ_eq_zero_iff (hα : α.IsOfType J 1 0) :
    J.typeProjection 0 2 (mextDerivₗ I 1 α) = 0 ↔
      ∀ x (v w : TangentSpace I x), α.1 x ![J.nijenhuis x v w] = 0 := by
  refine ⟨fun h x v w ↦ ?_, fun h ↦ SmoothForm.ext fun x v w ↦ ?_⟩
  · have hx := hα.typeProjection_zero_two_mextDerivₗ_apply x v w
    rw [h] at hx
    simpa using hx.symm
  · rw [eval₂_apply, hα.typeProjection_zero_two_mextDerivₗ_apply, h, smul_zero]
    simp

/-- The exterior derivative of a smooth one-form `α` of type `(0,1)` has no `(2,0)` component
exactly when `α ∘ N_J = 0`. -/
theorem IsOfType.typeProjection_two_zero_mextDerivₗ_eq_zero_iff (hα : α.IsOfType J 0 1) :
    J.typeProjection 2 0 (mextDerivₗ I 1 α) = 0 ↔
      ∀ x (v w : TangentSpace I x), α.1 x ![J.nijenhuis x v w] = 0 := by
  refine ⟨fun h x v w ↦ ?_, fun h ↦ SmoothForm.ext fun x v w ↦ ?_⟩
  · have hx := hα.typeProjection_two_zero_mextDerivₗ_apply x v w
    rw [h] at hx
    simpa using hx.symm
  · rw [eval₂_apply, hα.typeProjection_two_zero_mextDerivₗ_apply, h, smul_zero]
    simp

/-- If the Nijenhuis tensor vanishes, the exterior derivative of a smooth one-form of type
`(1,0)` has no `(0,2)` component. -/
theorem IsOfType.typeProjection_zero_two_mextDerivₗ_eq_zero (hα : α.IsOfType J 1 0)
    (hJ : J.nijenhuis = 0) : J.typeProjection 0 2 (mextDerivₗ I 1 α) = 0 :=
  hα.typeProjection_zero_two_mextDerivₗ_eq_zero_iff.2 fun x v w ↦ by
    rw [hJ]
    exact (α.1 x).map_coord_zero 0 rfl

/-- If the Nijenhuis tensor vanishes, the exterior derivative of a smooth one-form of type
`(0,1)` has no `(2,0)` component. -/
theorem IsOfType.typeProjection_two_zero_mextDerivₗ_eq_zero (hα : α.IsOfType J 0 1)
    (hJ : J.nijenhuis = 0) : J.typeProjection 2 0 (mextDerivₗ I 1 α) = 0 :=
  hα.typeProjection_two_zero_mextDerivₗ_eq_zero_iff.2 fun x v w ↦ by
    rw [hJ]
    exact (α.1 x).map_coord_zero 0 rfl

end SmoothForm

end TauCeti
