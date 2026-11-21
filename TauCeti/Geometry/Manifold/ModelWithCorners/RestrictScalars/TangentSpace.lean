/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import TauCeti.Geometry.Manifold.ModelWithCorners.RestrictScalars.Basic

/-!
# Restricting the scalars of maps between tangent spaces

Let `E` and `E'` be normed spaces over two fields `𝕜` and `𝕜'`, compatibly: for instance `𝕜'` is an
algebra over `𝕜` and the actions form scalar towers. For a boundaryless model `I` over `𝕜'`, the
tangent spaces `TangentSpace I x` and `TangentSpace (I.restrictScalars 𝕜) x` are both the model
space `E`, but they are distinct types carrying module structures over different fields. This file
compares maps and vectors in the two tangent spaces, fibre by fibre; the derivatives of maps between
manifolds are compared in `TauCeti.Geometry.Manifold.MFDeriv.RestrictScalars`.

`ContinuousLinearMap.restrictScalarsTangent` turns a `𝕜'`-linear map between tangent spaces for
boundaryless models `I` and `I'` into the same map, `𝕜`-linear between the tangent spaces for their
scalar restrictions. Like `ContinuousLinearMap.restrictScalars`, it and its laws assume
`LinearMap.CompatibleSMul`, which scalar towers provide. The two scalar laws also assume a scalar
tower `IsScalarTower 𝕜 𝕜' E'` on the target model space, and either an algebra `Algebra 𝕜 𝕜'` (for
scalars `algebraMap 𝕜 𝕜' c`) or an action of `𝕜` on the `𝕜'`-linear maps factoring through `𝕜'`
(for scalars `c : 𝕜`).

For the self models over a normed algebra, a separate fibrewise linear equivalence identifies the
tangent space over the larger field, with scalars restricted through `RestrictScalars`, with the
native tangent space over the smaller field.

## Main definitions

* `ContinuousLinearMap.restrictScalarsTangent`: the scalar restriction of a map between tangent
  spaces, as a map between the tangent spaces for the scalar restrictions of the models.
* `TauCeti.tangentSpaceRestrictScalarsSelfLinearEquiv`: the comparison of
  `RestrictScalars R A (TangentSpace 𝓘(A, E) x)` with the native smaller-field self-model tangent
  fibre `TangentSpace 𝓘(R, E) x`.

## Main results

* `ContinuousLinearMap.coe_restrictScalarsTangent`: as a function, the scalar restriction of a map
  between tangent spaces is the map.
* `ContinuousLinearMap.restrictScalarsTangent_inj`: restricting the scalars of maps between tangent
  spaces is injective.
* `ContinuousLinearMap.tangentSpaceCastModel_comp_restrictScalarsTangent_comp`: read in the model
  spaces, it is `ContinuousLinearMap.restrictScalars`.
* `ContinuousLinearMap.restrictScalarsTangent_comp`, `_id`, `_zero`, `_add`, `_neg`, `_sub`: it
  preserves composition, identities, zero, addition, negation and subtraction;
  `ContinuousLinearMap.restrictScalarsTangent_algebraMap_smul` and
  `ContinuousLinearMap.restrictScalarsTangent_smul`: under a scalar tower on the target, it
  preserves multiplication by scalars of the base field.
* `ContinuousLinearMap.restrictScalarsTangent_modelWithCornersSelf`: for the self models it is
  `ContinuousLinearMap.restrictScalars`.
-/

public section

open scoped Manifold

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedSpace 𝕜' E']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜' E H} {I' : ModelWithCorners 𝕜' E' H'} [I.Boundaryless] [I'.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : Type*} [TopologicalSpace N]
  [ChartedSpace H' N] {x : M}

variable (𝕜)

/- As for `ContinuousLinearMap.restrictScalars`, the scalar restriction of tangent maps only needs
`𝕜`-scalars to commute with `𝕜'`-linear maps; scalar towers provide this. -/
variable [LinearMap.CompatibleSMul E E' 𝕜 𝕜']

/-- The scalar restriction to `𝕜` of a `𝕜'`-linear map between tangent spaces for boundaryless
models over `𝕜'`, as a `𝕜`-linear map between the tangent spaces for their scalar restrictions.
The tangent spaces for a model and for its scalar restriction are both the model space, and
`f'.restrictScalarsTangent 𝕜` is `f'` with scalars restricted to `𝕜`
(`ContinuousLinearMap.restrictScalarsTangent_apply`). -/
noncomputable def ContinuousLinearMap.restrictScalarsTangent {y : N}
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    TangentSpace (I.restrictScalars 𝕜) x →L[𝕜] TangentSpace (I'.restrictScalars 𝕜) y :=
  (ContinuousLinearEquiv.arrowCongrEquiv (tangentSpaceCastModel (I.restrictScalars 𝕜) x)
      (tangentSpaceCastModel (I'.restrictScalars 𝕜) y)).symm
    ((ContinuousLinearEquiv.arrowCongrEquiv (tangentSpaceCastModel I x)
      (tangentSpaceCastModel I' y) f').restrictScalars 𝕜)

variable {𝕜} in
/-- As a function, the scalar restriction of a map between tangent spaces is the map: both tangent
spaces are the model space. -/
@[simp]
theorem ContinuousLinearMap.coe_restrictScalarsTangent {y : N}
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    ⇑(f'.restrictScalarsTangent 𝕜) = ⇑f' :=
  (rfl)

variable {𝕜} in
/-- The scalar restriction of a map between tangent spaces acts as the map: both tangent spaces
are the model space. -/
theorem ContinuousLinearMap.restrictScalarsTangent_apply {y : N}
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) (v : TangentSpace (I.restrictScalars 𝕜) x) :
    f'.restrictScalarsTangent 𝕜 v = f' v :=
  congrFun (coe_restrictScalarsTangent f') v

variable {𝕜} in
/-- The scalar restriction of a map between tangent spaces is injective if and only if the map is
injective. -/
theorem ContinuousLinearMap.injective_restrictScalarsTangent_iff {y : N}
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    Function.Injective (f'.restrictScalarsTangent 𝕜) ↔ Function.Injective f' := by
  rw [coe_restrictScalarsTangent]
  exact Iff.rfl

/-- Restricting the scalars of maps between tangent spaces is injective. This is the tangent-space
version of `LinearMap.restrictScalars_injective`. -/
theorem ContinuousLinearMap.restrictScalarsTangent_injective {y : N} :
    Function.Injective (restrictScalarsTangent 𝕜 :
      (TangentSpace I x →L[𝕜'] TangentSpace I' y) →
        TangentSpace (I.restrictScalars 𝕜) x →L[𝕜] TangentSpace (I'.restrictScalars 𝕜) y) :=
  fun f' g' h ↦ DFunLike.coe_injective ((coe_restrictScalarsTangent f').symm.trans
    ((congrArg DFunLike.coe h).trans (coe_restrictScalarsTangent g')))

/-- Two maps between tangent spaces have the same scalar restriction if and only if they are
equal. This is the tangent-space version of `LinearMap.restrictScalars_inj`. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_inj {y : N}
    (f' g' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    f'.restrictScalarsTangent 𝕜 = g'.restrictScalarsTangent 𝕜 ↔ f' = g' :=
  (restrictScalarsTangent_injective 𝕜).eq_iff

/-- Read in the model spaces through `tangentSpaceCastModel`, the scalar restriction of a map
between tangent spaces is the ordinary scalar restriction `ContinuousLinearMap.restrictScalars` of
the map read in the model spaces. -/
theorem ContinuousLinearMap.tangentSpaceCastModel_comp_restrictScalarsTangent_comp {y : N}
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    (tangentSpaceCastModel (I'.restrictScalars 𝕜) y : _ →L[𝕜] E') ∘L f'.restrictScalarsTangent 𝕜 ∘L
        ((tangentSpaceCastModel (I.restrictScalars 𝕜) x).symm : E →L[𝕜] _) =
      ((tangentSpaceCastModel I' y : _ →L[𝕜'] E') ∘L f' ∘L
        ((tangentSpaceCastModel I x).symm : E →L[𝕜'] _)).restrictScalars 𝕜 :=
  (ContinuousLinearEquiv.arrowCongrEquiv _ _).apply_symm_apply _

/-- Restricting the scalars of maps between tangent spaces preserves composition. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_comp {E'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace 𝕜 E''] [NormedSpace 𝕜' E''] [LinearMap.CompatibleSMul E' E'' 𝕜 𝕜']
    [LinearMap.CompatibleSMul E E'' 𝕜 𝕜'] {H'' : Type*}
    [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜' E'' H''} [I''.Boundaryless] {P : Type*}
    [TopologicalSpace P] [ChartedSpace H'' P] {y : N} {z : P}
    (g' : TangentSpace I' y →L[𝕜'] TangentSpace I'' z)
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    (g' ∘L f').restrictScalarsTangent 𝕜 =
      g'.restrictScalarsTangent 𝕜 ∘L f'.restrictScalarsTangent 𝕜 :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [restrictScalarsTangent_apply, comp_apply (g'.restrictScalarsTangent 𝕜),
      restrictScalarsTangent_apply, restrictScalarsTangent_apply]
    exact comp_apply g' f' v

/-- Restricting the scalars of the identity of a tangent space gives the identity. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_id [LinearMap.CompatibleSMul E E 𝕜 𝕜'] :
    (ContinuousLinearMap.id 𝕜' (TangentSpace I x)).restrictScalarsTangent 𝕜 =
      ContinuousLinearMap.id 𝕜 (TangentSpace (I.restrictScalars 𝕜) x) :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [restrictScalarsTangent_apply, id_apply (R₁ := 𝕜)]
    exact id_apply (R₁ := 𝕜') (M₁ := TangentSpace I x) v

/-- Restricting the scalars of the zero map between tangent spaces gives the zero map. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_zero {y : N} :
    (0 : TangentSpace I x →L[𝕜'] TangentSpace I' y).restrictScalarsTangent 𝕜 = 0 :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [restrictScalarsTangent_apply, _root_.zero_apply]
    exact _root_.zero_apply (F := TangentSpace I x →L[𝕜'] TangentSpace I' y) v

/-- Restricting the scalars of maps between tangent spaces preserves addition. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_add {y : N}
    (f' g' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    (f' + g').restrictScalarsTangent 𝕜 =
      f'.restrictScalarsTangent 𝕜 + g'.restrictScalarsTangent 𝕜 :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [restrictScalarsTangent_apply, _root_.add_apply (f'.restrictScalarsTangent 𝕜),
      restrictScalarsTangent_apply, restrictScalarsTangent_apply]
    exact _root_.add_apply f' g' v

/-- Restricting the scalars of maps between tangent spaces preserves negation. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_neg {y : N}
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    (-f').restrictScalarsTangent 𝕜 = -f'.restrictScalarsTangent 𝕜 :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [restrictScalarsTangent_apply, _root_.neg_apply (f'.restrictScalarsTangent 𝕜),
      restrictScalarsTangent_apply]
    exact _root_.neg_apply f' v

/-- Restricting the scalars of maps between tangent spaces preserves subtraction. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_sub {y : N}
    (f' g' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    (f' - g').restrictScalarsTangent 𝕜 =
      f'.restrictScalarsTangent 𝕜 - g'.restrictScalarsTangent 𝕜 :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [restrictScalarsTangent_apply, _root_.sub_apply (f'.restrictScalarsTangent 𝕜),
      restrictScalarsTangent_apply, restrictScalarsTangent_apply]
    exact _root_.sub_apply f' g' v

/-- Restricting the scalars of maps between tangent spaces turns multiplication by the image
`algebraMap 𝕜 𝕜' c` of a scalar `c` of the base field into multiplication by `c`. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_algebraMap_smul [Algebra 𝕜 𝕜']
    [IsScalarTower 𝕜 𝕜' E'] {y : N} (c : 𝕜)
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    (algebraMap 𝕜 𝕜' c • f').restrictScalarsTangent 𝕜 = c • f'.restrictScalarsTangent 𝕜 :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [restrictScalarsTangent_apply, _root_.smul_apply (f'.restrictScalarsTangent 𝕜) c,
      restrictScalarsTangent_apply]
    exact (_root_.smul_apply f' _ v).trans (algebraMap_smul (M := E') 𝕜' c (f' v))

/-- Restricting the scalars of maps between tangent spaces commutes with multiplication by a scalar
`c` of the base field, for any action of `𝕜` on the `𝕜'`-linear maps between tangent spaces that
factors through `𝕜'`. For instance, `ℝ` acts on complex linear maps through `ℂ`. -/
@[simp]
theorem ContinuousLinearMap.restrictScalarsTangent_smul [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E']
    {y : N} [SMul 𝕜 (TangentSpace I x →L[𝕜'] TangentSpace I' y)]
    [IsScalarTower 𝕜 𝕜' (TangentSpace I x →L[𝕜'] TangentSpace I' y)] (c : 𝕜)
    (f' : TangentSpace I x →L[𝕜'] TangentSpace I' y) :
    (c • f').restrictScalarsTangent 𝕜 = c • f'.restrictScalarsTangent 𝕜 :=
  ContinuousLinearMap.ext fun v ↦ by
    rw [← smul_one_smul 𝕜' c f', restrictScalarsTangent_apply,
      _root_.smul_apply (f'.restrictScalarsTangent 𝕜) c, restrictScalarsTangent_apply]
    exact (_root_.smul_apply f' _ v).trans (smul_one_smul (α := E') 𝕜' c (f' v))

/-- For the self models `𝓘(𝕜', E)` and `𝓘(𝕜', E')`, whose tangent spaces are `E` and `E'`, the
scalar restriction of a map between tangent spaces is its ordinary scalar restriction
`ContinuousLinearMap.restrictScalars`. This is not a simp lemma: `simp` would leave the
`restrictScalarsTangent` API, whose composition, identity and cancellation laws have no counterparts
for `ContinuousLinearMap.restrictScalars`. -/
theorem ContinuousLinearMap.restrictScalarsTangent_modelWithCornersSelf {M₀ : Type*}
    [TopologicalSpace M₀] [ChartedSpace E M₀] {N₀ : Type*} [TopologicalSpace N₀]
    [ChartedSpace E' N₀] {x₀ : M₀} {y₀ : N₀} (f' : E →L[𝕜'] E') :
    ContinuousLinearMap.restrictScalarsTangent (I := 𝓘(𝕜', E)) (I' := 𝓘(𝕜', E')) (x := x₀)
      (y := y₀) 𝕜 f' = f'.restrictScalars 𝕜 :=
  ContinuousLinearMap.ext fun v ↦
    (restrictScalarsTangent_apply (I := 𝓘(𝕜', E)) (I' := 𝓘(𝕜', E')) (x := x₀) (y := y₀) f' v).trans
      (congrFun (coe_restrictScalars' (R := 𝕜) f') v).symm

noncomputable section

namespace TauCeti

variable (R : Type*) {A : Type*}
  [NontriviallyNormedField R] [NontriviallyNormedField A] [Algebra R A]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace A E] [NormedSpace R E]
  [IsScalarTower R A E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Scalar restriction identifies a self-model tangent fibre with the native self-model
fibre over the smaller field. -/
def tangentSpaceRestrictScalarsSelfLinearEquiv (x : M) :
    RestrictScalars R A (TangentSpace 𝓘(A, E) x) ≃ₗ[R] TangentSpace 𝓘(R, E) x where
  toFun v := (tangentSpaceCastModel 𝓘(R, E) x).symm
    (tangentSpaceCastModel 𝓘(A, E) x (RestrictScalars.addEquiv R A _ v))
  invFun v := (RestrictScalars.addEquiv R A _).symm
    ((tangentSpaceCastModel 𝓘(A, E) x).symm (tangentSpaceCastModel 𝓘(R, E) x v))
  left_inv v := by simp
  right_inv v := by simp
  map_add' v w := by simp only [map_add]
  map_smul' c v := by
    simp only [RestrictScalars.addEquiv_map_smul, map_smul, RingHom.id_apply, algebraMap_smul]

/-- Native self-model scalar restriction preserves preferred tangent coordinates. -/
@[simp]
theorem tangentSpaceRestrictScalarsSelfLinearEquiv_apply (x : M)
    (v : RestrictScalars R A (TangentSpace 𝓘(A, E) x)) :
    tangentSpaceRestrictScalarsSelfLinearEquiv R x v = (tangentSpaceCastModel 𝓘(R, E) x).symm
      (tangentSpaceCastModel 𝓘(A, E) x (RestrictScalars.addEquiv R A _ v)) := by
  rfl

/-- The inverse native self-model comparison preserves preferred tangent coordinates. -/
@[simp]
theorem tangentSpaceRestrictScalarsSelfLinearEquiv_symm_apply (x : M) (v : TangentSpace 𝓘(R, E) x) :
    (tangentSpaceRestrictScalarsSelfLinearEquiv R (A := A) x).symm v =
      (RestrictScalars.addEquiv R A _).symm
        ((tangentSpaceCastModel 𝓘(A, E) x).symm (tangentSpaceCastModel 𝓘(R, E) x v)) := by
  rfl

end TauCeti

end
