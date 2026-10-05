/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Scalar extension of an affine Weierstrass coordinate ring

For a homomorphism `f : R →+* S`, the coordinate ring of `W.map f` is the scalar extension of
the coordinate ring of `W` along the coefficientwise map `Polynomial.map f : R[X] → S[X]`.  More
precisely, `CoordinateRing.map` induces an `S[X]`-linear isomorphism
`S[X] ⊗[R[X]] W.CoordinateRing ≃ₗ[S[X]] (W.map f).CoordinateRing` sending `p ⊗ₜ z` to
`p • CoordinateRing.map W f z`.  This coordinate-ring comparison is an input to a later
comparison of the function fields of `W` and `W.map f`, used to compare degrees of isogenies
under base change.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.mapLinear`: `CoordinateRing.map`, viewed as a linear map
  over the coefficientwise map `R[X] → S[X]`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.isBaseChange_mapLinear`: the target coordinate ring is
  the module base change of the source coordinate ring.

-/

public section

open Polynomial
open scoped TensorProduct

namespace TauCeti

open _root_.WeierstrassCurve.Affine
open _root_.WeierstrassCurve.Affine.CoordinateRing

variable {R S : Type*} [CommRing R] [CommRing S]
variable (W : _root_.WeierstrassCurve.Affine R) (f : R →+* S)

/-- `CoordinateRing.map`, as a linear map over the coefficientwise homomorphism
`R[X] → S[X]`. -/
noncomputable def _root_.WeierstrassCurve.Affine.CoordinateRing.mapLinear :
    let _ : Module R[X] (W.map f).CoordinateRing :=
      Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f)
    W.CoordinateRing →ₗ[R[X]] (W.map f).CoordinateRing := by
  letI : Module R[X] (W.map f).CoordinateRing :=
    Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f)
  exact
    { toFun := map W f
      map_add' := map_add _
      map_smul' := fun p z ↦ CoordinateRing.map_smul f p z }

@[simp]
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.mapLinear_apply
    (z : W.CoordinateRing) : mapLinear W f z = map W f z := by
  unfold mapLinear
  rfl

private theorem mapScalarTower :
    @IsScalarTower R[X] S[X] (W.map f).CoordinateRing
      (Polynomial.mapRingHom f).toAlgebra.toSMul inferInstance
      ((Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f)).toDistribMulAction
        |>.toMulAction.toSemigroupAction.toSMul) := by
  algebraize [Polynomial.mapRingHom f]
  exact IsScalarTower.of_compHom R[X] S[X] (W.map f).CoordinateRing

/-- The coordinate ring of `W.map f` is the module base change of the coordinate ring of `W`
along the coefficientwise map `R[X] → S[X]`. -/
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.isBaseChange_mapLinear :
    @IsBaseChange R[X] W.CoordinateRing (W.map f).CoordinateRing S[X]
      inferInstance inferInstance inferInstance inferInstance
      (Polynomial.mapRingHom f).toAlgebra inferInstance
      (Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f)) inferInstance
      (by exact mapScalarTower W f)
      (mapLinear W f) := by
  algebraize [Polynomial.mapRingHom f]
  let bₜ :=
    (TensorProduct.isBaseChange R[X] W.CoordinateRing S[X]).basis (CoordinateRing.basis W)
  let e : S[X] ⊗[R[X]] W.CoordinateRing ≃ₗ[S[X]] (W.map f).CoordinateRing :=
    bₜ.equiv (CoordinateRing.basis (W.map f)) (Equiv.refl (Fin 2))
  refine @IsBaseChange.of_equiv R[X] W.CoordinateRing (W.map f).CoordinateRing S[X]
    inferInstance inferInstance inferInstance inferInstance (Polynomial.mapRingHom f).toAlgebra
    inferInstance (Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f))
    inferInstance (mapScalarTower W f) (mapLinear W f) e ?_
  intro z
  let : Module R[X] (W.map f).CoordinateRing :=
    Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f)
  -- `z ↦ e (1 ⊗ₜ z)` as an `R[X]`-linear map, so that it can be compared with `mapLinear` on
  -- the basis `{1, Y}` of `R[W]`.
  let g : W.CoordinateRing →ₗ[R[X]] (W.map f).CoordinateRing :=
    { toFun := fun x ↦ e (1 ⊗ₜ x)
      map_add' := fun x y ↦ by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun p x ↦ by
        -- The tower is named explicitly: instance search would find `AdjoinRoot`'s `R[X]`-action.
        rw [TensorProduct.tmul_smul, ← smul_one_smul S[X] p, map_smul, RingHom.id_apply,
          (mapScalarTower W f).smul_assoc, one_smul] }
  have hg : ∀ x, g x = e (1 ⊗ₜ x) := fun _ ↦ rfl
  rw [← hg]
  refine LinearMap.congr_fun ((CoordinateRing.basis W).ext fun i ↦ ?_) z
  have hb : e (bₜ i) = CoordinateRing.basis (W.map f) i := by simp [e]
  rw [hg, ← TensorProduct.mk_apply,
    ← IsBaseChange.basis_apply (CoordinateRing.basis W)
      (TensorProduct.isBaseChange R[X] W.CoordinateRing S[X]) i, hb]
  fin_cases i <;> simp [basis_one, map_mk, -AdjoinRoot.mk_X]

end TauCeti

end
