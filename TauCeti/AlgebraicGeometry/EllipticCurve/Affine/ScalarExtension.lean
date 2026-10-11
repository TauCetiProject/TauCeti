/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.Basis
-- Proof-only: `CoordinateRing.map` fixes the coordinates and is compatible with the scalars.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRingMap
-- `RingHom.Flat`, the hypothesis of `CoordinateRing.linearIndependent_map`.
public import Mathlib.RingTheory.RingHom.Flat
-- Proof-only: the basis of a scalar extension `S ⊗_R M` induced by a basis of `M`.
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Scalar extension of an affine Weierstrass coordinate ring

For a homomorphism `f : R →+* S`, the coordinate ring of `W.map f` is the scalar extension of
the coordinate ring of `W` along the coefficientwise map `Polynomial.map f : R[X] → S[X]`.  More
precisely, `CoordinateRing.map` induces an `S[X]`-linear isomorphism
`S[X] ⊗[R[X]] W.CoordinateRing ≃ₗ[S[X]] (W.map f).CoordinateRing` sending `p ⊗ₜ z` to
`p • CoordinateRing.map W f z`.

Over the base ring itself the same holds: `CoordinateRing.map` sends the monomial basis
`{xⁱ, xⁱy}` of `R[W]` over `R` to that of `S[W.map f]` over `S`. This identifies `S[W.map f]` with
`S ⊗_R R[W]`, so when `f` is flat, `R`-linearly independent elements of `R[W]` stay `S`-linearly
independent in `S[W.map f]`. For a homomorphism of fields `f : F →+* K`, this linear disjointness
of `F[W]` and `K` is the input to the comparison of the function fields of `W` and `W.map f`, and
through it of the degrees of isogenies under base change.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.mapLinear`: `CoordinateRing.map`, viewed as a linear map
  over the coefficientwise map `R[X] → S[X]`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.isBaseChange_mapLinear`: the target coordinate ring is
  the module base change of the source coordinate ring.
* `WeierstrassCurve.Affine.CoordinateRing.map_basisMonomials`: `CoordinateRing.map` sends the
  monomial basis to the monomial basis.
* `WeierstrassCurve.Affine.CoordinateRing.linearIndependent_map`: for flat `f`, `R`-linearly
  independent elements of `R[W]` stay `S`-linearly independent in `S[W.map f]`.

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

/-- **`CoordinateRing.map` sends the monomial `xⁱyʲ` of `R[W]` to the monomial `xⁱyʲ` of
`S[W.map f]`**: it sends the monomial basis to the monomial basis. -/
@[simp]
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.map_basisMonomials (i : ℕ × Fin 2) :
    map W f (CoordinateRing.basisMonomials W i) = CoordinateRing.basisMonomials (W.map f) i := by
  obtain ⟨i, j⟩ := i
  simp [map_of_X, map_root]

/-- **`R[W]` and `S` are linearly disjoint over `R` in `S[W.map f]`**: for a flat `f : R →+* S`,
`CoordinateRing.map` sends `R`-linearly independent elements of `R[W]` to `S`-linearly independent
elements of `S[W.map f]`. -/
theorem _root_.WeierstrassCurve.Affine.CoordinateRing.linearIndependent_map {ι : Type*}
    (hf : f.Flat) {v : ι → W.CoordinateRing} (hv : LinearIndependent R v) :
    LinearIndependent S (map W f ∘ v) := by
  algebraize [f]
  -- The monomial bases correspond, so `S[W.map f]` is the scalar extension `S ⊗_R R[W]`, through
  -- the `S`-linear isomorphism `e` below, and `S` is flat over `R`.
  let e : S ⊗[R] W.CoordinateRing ≃ₗ[S] (W.map f).CoordinateRing :=
    (Algebra.TensorProduct.basis S (CoordinateRing.basisMonomials W)).equiv
      (CoordinateRing.basisMonomials (W.map f)) (Equiv.refl _)
  have he (z : W.CoordinateRing) : e (1 ⊗ₜ z) = map W f z := by
    obtain ⟨c, rfl⟩ := (CoordinateRing.basisMonomials W).repr.symm.surjective z
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, TensorProduct.tmul_add, hc, hd]
    | single j a =>
      rw [Module.Basis.repr_symm_single, TensorProduct.tmul_smul, ← algebraMap_smul S a,
        map_smul, ← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply,
        Equiv.refl_apply, Algebra.smul_def, Algebra.smul_def a, map_mul, map_algebraMap,
        map_basisMonomials, RingHom.algebraMap_toAlgebra]
  have h := (Module.Flat.linearIndependent_one_tmul (S := S) hv).map' e.toLinearMap e.ker
  convert h using 1
  ext i
  simp [he]

end TauCeti

end
