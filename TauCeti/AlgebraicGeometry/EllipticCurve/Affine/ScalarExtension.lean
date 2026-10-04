/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRingMap
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Scalar extension of an affine Weierstrass coordinate ring

For a homomorphism `f : R →+* S`, the coordinate ring of `W.map f` is the scalar extension of
the coordinate ring of `W`.  More precisely, the underlying module square

```text
                 Polynomial.map f
          R[X] --------------------> S[X]
           |                          |
           |                          |
           v                          v
          R[W] -------------------> S[W.map f]
                  CoordinateRing.map
```

is a pushout.  The proof uses the canonical bases `{1, Y}` on both sides: the coordinate-ring map
sends the first basis to the second, so the induced map from the tensor product sends a basis to a
basis.

This is the coordinate-ring comparison needed for invariance of isogeny degree under base change.
The remaining step is to localise this pushout compatibly with the two function-field pullbacks.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.mapLinear`: `CoordinateRing.map`, viewed as a linear map
  over the coefficientwise map `R[X] → S[X]`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.isBaseChange_mapLinear`: the target coordinate ring is
  the module base change of the source coordinate ring.

## Roadmap

`TauCetiRoadmap/EllipticCurves/README.md`, **Layer 0.5**, asks for base change of coordinate rings,
function fields and isogenies compatible with degree.  This file supplies the coordinate-ring
pushout required before the corresponding fraction-field degree comparison.
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
@[expose]
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
    (z : W.CoordinateRing) : mapLinear W f z = map W f z := rfl

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
  let g :
      let _ : Module R[X] (W.map f).CoordinateRing :=
        Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f)
      W.CoordinateRing →ₗ[R[X]] (W.map f).CoordinateRing := by
    letI : Module R[X] (W.map f).CoordinateRing :=
      Module.compHom (W.map f).CoordinateRing (Polynomial.mapRingHom f)
    haveI : IsScalarTower R[X] S[X] (W.map f).CoordinateRing := mapScalarTower W f
    exact
      { toFun := fun x ↦ e (1 ⊗ₜ[R[X]] x)
        map_add' := fun x y ↦ by simp only [TensorProduct.tmul_add, map_add]
        map_smul' := fun p x ↦ by
          change e ((TensorProduct.mk R[X] S[X] W.CoordinateRing 1) (p • x)) =
            p • e ((TensorProduct.mk R[X] S[X] W.CoordinateRing 1) x)
          rw [(TensorProduct.mk R[X] S[X] W.CoordinateRing 1).map_smul]
          rw [← IsScalarTower.algebraMap_smul S[X] p
            ((TensorProduct.mk R[X] S[X] W.CoordinateRing 1) x)]
          rw [e.map_smul]
          exact IsScalarTower.algebraMap_smul S[X] p _ }
  change g z = mapLinear W f z
  apply LinearMap.congr_fun
  apply (CoordinateRing.basis W).ext
  intro i
  change e ((TensorProduct.mk R[X] S[X] W.CoordinateRing 1) (CoordinateRing.basis W i)) =
    mapLinear W f (CoordinateRing.basis W i)
  rw [← IsBaseChange.basis_apply (CoordinateRing.basis W)
    (TensorProduct.isBaseChange R[X] W.CoordinateRing S[X]) i]
  change e (bₜ i) = mapLinear W f (CoordinateRing.basis W i)
  rw [show e (bₜ i) = CoordinateRing.basis (W.map f) i by simp [e]]
  fin_cases i
  · simp
  · simp

end TauCeti

end
