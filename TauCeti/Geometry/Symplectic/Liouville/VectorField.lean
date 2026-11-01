/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.LieDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Squared
public import TauCeti.Geometry.Symplectic.Cotangent.Fiberwise
public import TauCeti.Geometry.Symplectic.Liouville.Plane
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Liouville vector fields

A vector field `Z` on a manifold carrying a two-form `ω` is a **Liouville vector field** when
`L_Z ω = ω`. For a closed form, Cartan's formula `L_Z ω = ι_Z dω + d (ι_Z ω)` shows that this
holds exactly when `ι_Z ω` is a primitive of `ω`
(`TauCeti.isLiouvilleVectorField_iff_mextDeriv_interior_eq`). In particular, if `λ` is a
primitive of `ω` and `ι_Z ω = λ`, then `Z` is a Liouville vector field
(`TauCeti.isLiouvilleVectorField_mextDeriv_of_interior_eq`). This is the Liouville field of the
primitive `λ`, the kind of vector field used to define Liouville domains and hypersurfaces of
contact type. On a normed space the same characterization is stated with the flat exterior
derivative (`TauCeti.isLiouvilleVectorField_extDeriv_iff`).

The converse fails for a fixed primitive: a Liouville vector field `Z` only determines its own
primitive `ι_Z ω`, which need not be the given one. On the plane, with `λ = x dy` and
`ω = dλ = dx ∧ dy`, the field `Z = x ∂_x + ∂_y` is a Liouville vector field, but
`ι_Z ω = λ - dx` (`Prod.isLiouvilleVectorField_extDeriv_realPlaneXDy`,
`Prod.curryLeft_extDeriv_realPlaneXDy`). In cotangent notation, with `(x, y) = (p, q)`, this
is `λ = p dq` and `Z = p ∂_p + ∂_q`.

On the linear cotangent space, with the tautological form `λ = p dq` and the canonical symplectic
form `-dλ`, the radial field `p ∂_p` is the Liouville field of the primitive `-λ`
(`TauCeti.isLiouvilleVectorField_cotangentLiouvilleField`).

## Main declarations

* `TauCeti.IsLiouvilleVectorField`: the property `L_Z ω = ω`.
* `TauCeti.isLiouvilleVectorField_iff_mextDeriv_interior_eq`: for a closed form, `Z` is a
  Liouville vector field exactly when `d (ι_Z ω) = ω`.
* `TauCeti.isLiouvilleVectorField_mextDeriv_of_interior_eq`: `ι_Z dλ = λ` implies
  `L_Z dλ = dλ`.
* `TauCeti.mlieDerivForm_eq_self_of_interior_eq`: `ι_Z dλ = λ` implies `L_Z λ = λ`.
* `TauCeti.isLiouvilleVectorField_extDeriv_iff`: the characterization on a normed space.
* `TauCeti.isLiouvilleVectorField_cotangentLiouvilleField`: the radial field of the linear
  cotangent space.
* `Prod.isLiouvilleVectorField_extDeriv_realPlaneXDy`, `Prod.curryLeft_extDeriv_realPlaneXDy_ne`:
  a Liouville vector field of `d(x dy)` that is not the Liouville field of `x dy`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Chapter 3 (Liouville vector fields and hypersurfaces of contact type).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

noncomputable section

open Bundle
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- A vector field `Z` is a **Liouville vector field** for a two-form `ω` when the Lie derivative
of `ω` along `Z` is `ω` itself, `L_Z ω = ω`. -/
def IsLiouvilleVectorField (ω : RoughForm I M ℝ 2) (Z : (x : M) → TangentSpace I x) : Prop :=
  mlieDerivForm Z ω = ω

/-- The defining characterization of a Liouville vector field. -/
theorem isLiouvilleVectorField_iff {ω : RoughForm I M ℝ 2} {Z : (x : M) → TangentSpace I x} :
    IsLiouvilleVectorField ω Z ↔ mlieDerivForm Z ω = ω :=
  Iff.rfl

/-- For a differentiable closed two-form `ω` and a differentiable vector field `Z`, `Z` is a
Liouville vector field exactly when `ι_Z ω` is a primitive of `ω`. -/
theorem isLiouvilleVectorField_iff_mextDeriv_interior_eq [IsManifold I 1 M]
    {ω : RoughForm I M ℝ 2} {Z : (x : M) → TangentSpace I x}
    (hω : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) y (ω y)))
    (hZ : MDifferentiable I I.tangent (fun y ↦ (Z y : TangentBundle I M)))
    (hdω : mextDeriv ω = 0) :
    IsLiouvilleVectorField ω Z ↔ mextDeriv (ω.interior Z) = ω := by
  rw [isLiouvilleVectorField_iff, mlieDerivForm_eq_mextDeriv_interior hω hZ hdω]

/-- For a `C²` one-form `α` and a differentiable vector field `Z`, `Z` is a Liouville vector
field of `dα` exactly when `ι_Z dα` is again a primitive of `dα`. -/
theorem isLiouvilleVectorField_mextDeriv_iff [IsManifold I 2 M] {α : RoughForm I M ℝ 1}
    {Z : (x : M) → TangentSpace I x} (hα : IsSmoothForm I 2 α)
    (hZ : MDifferentiable I I.tangent (fun y ↦ (Z y : TangentBundle I M))) :
    IsLiouvilleVectorField (mextDeriv α) Z ↔
      mextDeriv ((mextDeriv α).interior Z) = mextDeriv α :=
  have hα' : IsSmoothBundleForm (I := I) (F := ℝ) (V := Trivial M ℝ) 2 α :=
    (isSmoothBundleForm_def 2 α).mpr hα.contMDiff
  isLiouvilleVectorField_iff_mextDeriv_interior_eq
    (((isSmoothBundleForm_def 1 _).mp
      (isSmoothBundleForm_mextDeriv α hα' (n := 1) (by norm_num))).mdifferentiable one_ne_zero) hZ
    (mextDeriv_mextDeriv α hα')

/-- **The Liouville field of a primitive.** If `α` is a `C²` one-form and the differentiable
vector field `Z` satisfies `ι_Z dα = α`, then `Z` is a Liouville vector field of `dα`. -/
theorem isLiouvilleVectorField_mextDeriv_of_interior_eq [IsManifold I 2 M]
    {α : RoughForm I M ℝ 1} {Z : (x : M) → TangentSpace I x} (hα : IsSmoothForm I 2 α)
    (hZ : MDifferentiable I I.tangent (fun y ↦ (Z y : TangentBundle I M)))
    (h : (mextDeriv α).interior Z = α) :
    IsLiouvilleVectorField (mextDeriv α) Z := by
  rw [isLiouvilleVectorField_mextDeriv_iff hα hZ, h]

/-- **A primitive has Lie derivative equal to itself along its Liouville field.** If the
differentiable vector field `Z` satisfies `ι_Z dλ = λ` for a differentiable one-form `λ`, then
`L_Z λ = λ`: by Cartan's formula `L_Z λ = ι_Z dλ + d (ι_Z λ)`, and `ι_Z λ = dλ (Z, Z) = 0`. -/
theorem mlieDerivForm_eq_self_of_interior_eq [IsManifold I 1 M] {α : RoughForm I M ℝ 1}
    {Z : (x : M) → TangentSpace I x}
    (hα : MDifferentiable I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ))
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)))
    (hZ : MDifferentiable I I.tangent (fun y ↦ (Z y : TangentBundle I M)))
    (h : (mextDeriv α).interior Z = α) :
    mlieDerivForm Z α = α := by
  have h0 : α.interior Z = 0 := by
    rw [← h]
    exact RoughForm.interior_self Z (mextDeriv α)
  rw [mlieDerivForm_eq_interior_mextDeriv_add hα hZ, h0, mextDeriv_zero, add_zero, h]

/-! ### Normed spaces -/

section ModelSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- On a normed space, for a `C²` one-form `α` and a differentiable vector field `Z`, `Z` is a
Liouville vector field of `dα` exactly when the one-form `x ↦ ι_{Z x} dα_x` is again a primitive
of `dα`. -/
theorem isLiouvilleVectorField_extDeriv_iff {α : E → E [⋀^Fin 1]→L[ℝ] ℝ} {Z : E → E}
    (hα : ContDiff ℝ 2 α) (hZ : Differentiable ℝ Z) :
    IsLiouvilleVectorField (I := 𝓘(ℝ, E)) (extDeriv α) Z ↔
      extDeriv (fun x ↦ (extDeriv α x).curryLeft (Z x)) = extDeriv α := by
  have hd : mextDeriv (I := 𝓘(ℝ, E)) (M := E) (F := ℝ) α = extDeriv α :=
    funext (mextDeriv_eq_extDeriv α)
  have hι : (mextDeriv (I := 𝓘(ℝ, E)) (M := E) (F := ℝ) α).interior Z =
      fun x ↦ (extDeriv α x).curryLeft (Z x) := by
    rw [hd]
    exact RoughForm.interior_modelSpace Z _
  have h := isLiouvilleVectorField_mextDeriv_iff (isSmoothForm_modelSpace_iff.mpr hα)
    fun x ↦ mdifferentiableAt_vectorSpace_iff_differentiableAt.mpr (hZ x)
  have he := funext (mextDeriv_eq_extDeriv (fun x ↦ (extDeriv α x).curryLeft (Z x)))
  rw [hι, hd] at h
  rw [h]
  exact ⟨fun h' ↦ he.symm.trans h', fun h' ↦ he.trans h'⟩

end ModelSpace

/-! ### The radial field of the linear cotangent space -/

section Cotangent

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- On the linear cotangent space, the radial field `p ∂_p` is a Liouville vector field of the
canonical symplectic form `d(-λ) = -dλ`, as the Liouville field of its primitive `-λ`. -/
theorem isLiouvilleVectorField_cotangentLiouvilleField :
    IsLiouvilleVectorField (I := 𝓘(ℝ, V × StrongDual ℝ V)) (extDeriv (-cotangentLiouvilleForm))
      cotangentLiouvilleField :=
  (isLiouvilleVectorField_extDeriv_iff contDiff_cotangentLiouvilleForm.neg
    cotangentLiouvilleField.differentiable).mpr <| congrArg extDeriv <| funext fun x ↦
      (curryLeft_extDeriv_neg_cotangentLiouvilleForm x).trans
        (Pi.neg_apply cotangentLiouvilleForm x).symm

end Cotangent

end TauCeti

/-! ### A Liouville vector field that is not the Liouville field of a given primitive -/

namespace Prod

/-- On the plane, the vector field `Z = x ∂_x + ∂_y` is a Liouville vector field of
`d(x dy) = dx ∧ dy`, although it is not the Liouville field of the primitive `x dy`
(`Prod.curryLeft_extDeriv_realPlaneXDy_ne`): it is the Liouville field of the primitive
`x dy - dx`. -/
theorem isLiouvilleVectorField_extDeriv_realPlaneXDy :
    TauCeti.IsLiouvilleVectorField (I := 𝓘(ℝ, ℝ × ℝ)) (extDeriv realPlaneXDy)
      fun p ↦ (p.1, 1) := by
  rw [TauCeti.isLiouvilleVectorField_extDeriv_iff contDiff_realPlaneXDy
    (differentiable_fst.prodMk (differentiable_const _)), funext curryLeft_extDeriv_realPlaneXDy]
  -- Write `x dy - dx` as a linear combination of forms, so that `d` splits over it.
  have hsub : (fun x ↦ realPlaneXDy x - realPlaneDx x) =
      realPlaneXDy + (-1 : ℝ) • realPlaneDx := by
    funext x
    simp only [Pi.add_apply, Pi.smul_apply]
    module
  funext p
  rw [hsub,
    extDeriv_add ((contDiff_realPlaneXDy (n := 1)).differentiable one_ne_zero).differentiableAt
      (((contDiff_realPlaneDx (n := 1)).differentiable one_ne_zero).differentiableAt.const_smul _)]
  simp [extDeriv_smul]

end Prod
