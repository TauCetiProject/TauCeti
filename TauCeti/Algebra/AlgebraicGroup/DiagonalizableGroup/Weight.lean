/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Corestrict
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Matrix
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic

/-!
# Weight spaces by corestriction to a monoid algebra

Given a right `C`-comodule `V` and a coalgebra morphism `π : C → R[X]`, corestriction along `π`
makes `V` an `R[X]`-comodule. The resulting comodule decomposes into the weight submodules of
`TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Basic`. This file names that decomposition:

`TauCeti.DiagonalizableGroup.weightSpace V π x` is the `x`-weight submodule of the corestricted
comodule, and `V` is the internal direct sum of these submodules.

When `X` is a commutative group, `C` is the coordinate bialgebra of an affine group scheme `G`,
and `π` underlies a bialgebra morphism, it is the coordinate morphism of a homomorphism
`D(X) → G`, and these are the weight spaces of a representation restricted along that
homomorphism. The statement identifying the action of a point of `D(X)` as multiplication by the
value of the character therefore takes a `BialgHom`.

The roots of a split pair `(G, T)` are the nonzero weights of the adjoint representation of `G`
restricted along the split maximal torus `T`. This file supplies that restriction for an
arbitrary homomorphism from a diagonalizable group, carrying no torus, maximality or
closed-immersion hypotheses; `TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace` performs the
specialization to the adjoint representation.

## Main definitions

* `TauCeti.DiagonalizableGroup.weightSpace`: the `x`-weight submodule after corestricting a
  comodule along a coalgebra morphism to `R[X]`.

## Main results

* `TauCeti.DiagonalizableGroup.isInternal_weightSpace`: **the corestricted comodule is the internal
  direct sum of its weight submodules.**
* `TauCeti.DiagonalizableGroup.finite_setOf_weightSpace_ne_bot`: a comodule that is finitely
  generated as a module has finitely many nonzero weight submodules after corestriction.
* `TauCeti.DiagonalizableGroup.mem_weightSpace_iff_endOfPoint`: the universal point detects
  membership in a weight space.
* `TauCeti.DiagonalizableGroup.endOfPoint_tmul_of_mem_weightSpace`: a monoid-algebra point acts on
  the `x`-weight submodule by multiplication by its value on `x`; for a commutative group `X`,
  this is the corresponding action of a point of `D(X)`.
* `TauCeti.DiagonalizableGroup.map_matrixCoefficient_of_mem_weightSpace`: the matrix coefficients
  of an `x`-weight vector restrict to multiples of `x`.
* `TauCeti.DiagonalizableGroup.map_matrixCoefficient_mem_span_single`: every matrix coefficient
  restricts into the span of the occurring weights.
* `TauCeti.DiagonalizableGroup.map_det_coefficientMatrix_of_forall_mem_weightSpace`: the
  determinant of a finite free comodule of pure weight `x` restricts to `x ^ n`, where `n` is the
  rank.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §12.c and §21.
-/

public section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace DiagonalizableGroup

attribute [local instance] Classical.decEq

section Decomposition

variable {R : Type*} [CommSemiring R]
variable {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {X : Type*}
variable (V : Type*) [AddCommMonoid V] [Module R V] [Comodule R C V]

/-- The `x`-weight submodule obtained by corestricting a right `C`-comodule `V` along a coalgebra
morphism `π : C →ₗc[R] R[X]`.

If `X` is a commutative group, `π` underlies the coordinate-bialgebra morphism of a homomorphism
`D(X) → G`, and `V` is a representation of `G`, this is the submodule on which `D(X)` acts
through the character `x`. -/
noncomputable def weightSpace (π : C →ₗc[R] MonoidAlgebra R X) (x : X) :
    Submodule R V :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.weightSpace R X V x

variable {V}

/-- Membership in the `x`-weight submodule, in terms of the coaction of the original comodule:
pushing the coaction of `v` through `π` must give `v ⊗ x`. -/
@[simp]
theorem mem_weightSpace {π : C →ₗc[R] MonoidAlgebra R X} {x : X} {v : V} :
    v ∈ weightSpace V π x ↔
      TensorProduct.map LinearMap.id π.toLinearMap
          (Comodule.coact (R := R) (C := C) (M := V) v) =
        v ⊗ₜ[R] MonoidAlgebra.single x (1 : R) :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.mem_weightSpace

variable (V)

/-- **A comodule corestricted along a coalgebra morphism to `R[X]` is the internal direct sum of
its weight submodules.** -/
theorem isInternal_weightSpace (π : C →ₗc[R] MonoidAlgebra R X) :
    DirectSum.IsInternal (weightSpace V π) :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.isInternal_weightSpace R X V

/-- **A comodule that is finitely generated as a module has only finitely many nonzero weight
submodules after corestriction.** -/
theorem finite_setOf_weightSpace_ne_bot [Module.Finite R V] (π : C →ₗc[R] MonoidAlgebra R X) :
    {x : X | weightSpace V π x ≠ ⊥}.Finite :=
  letI : Comodule R (MonoidAlgebra R X) V := Comodule.Corestrict (M := V) π
  Comodule.finite_setOf_weightSpace_ne_bot R X V

end Decomposition

section Points

variable {R : Type*} [CommSemiring R]
variable {C : Type*} [Semiring C] [Bialgebra R C]
variable {X : Type*} [Monoid X]
variable (V : Type*) [AddCommMonoid V] [Module R V] [Comodule R C V]
variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- Acting through a composite point agrees on pure tensors with first corestricting the coaction
along the bialgebra morphism and then applying the point. -/
theorem endOfPoint_tmul_comp (π : C →ₐc[R] MonoidAlgebra R X)
    (f : MonoidAlgebra R X →ₐ[R] A) (a : A) (v : V) :
    Comodule.endOfPoint V (f.comp (π : C →ₐ[R] MonoidAlgebra R X)) (a ⊗ₜ[R] v) =
      a • TensorProduct.comm R V A
        (LinearMap.lTensor V f.toLinearMap
          (TensorProduct.map LinearMap.id (π : C →ₗc[R] MonoidAlgebra R X).toLinearMap
            (Comodule.coact (R := R) (C := C) (M := V) v))) := by
  have hπ : (π : C →ₐ[R] MonoidAlgebra R X).toLinearMap =
      (π : C →ₗc[R] MonoidAlgebra R X).toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_ofClass]
    exact BialgHom.toAlgHom_toLinearMap π
  rw [Comodule.endOfPoint_tmul]
  congr 2
  rw [LinearMap.lTensor_map, AlgHom.comp_toLinearMap, hπ, LinearMap.lTensor_def]

/-- A monoid-algebra weight is detected by the universal point, even over a nonreduced
base ring. -/
theorem mem_weightSpace_iff_endOfPoint {X' : Type*} [CommMonoid X']
    (π : C →ₐc[R] MonoidAlgebra R X') (x : X') (v : V) :
    v ∈ weightSpace V π.toCoalgHom x ↔
      Comodule.endOfPoint V π.toAlgHom (1 ⊗ₜ[R] v) =
        MonoidAlgebra.single x 1 ⊗ₜ[R] v := by
  rw [mem_weightSpace, Comodule.endOfPoint_tmul, one_smul]
  have hπ : π.toAlgHom.toLinearMap = π.toCoalgHom.toLinearMap := by
    rw [CoalgHom.toLinearMap_eq_ofClass]
    exact BialgHom.toAlgHom_toLinearMap π
  rw [hπ, LinearMap.lTensor_def]
  constructor
  · intro h
    rw [h, TensorProduct.comm_tmul]
  · intro h
    apply (TensorProduct.comm R V (MonoidAlgebra R X')).injective
    simpa only [TensorProduct.comm_tmul] using h

/-- **A monoid-algebra point acts on the `x`-weight submodule by its value on `x`.**

When `X` is a commutative group and the bialgebras are coordinate rings, the point of `G` in
question is the composite of the homomorphism `D(X) → G` with the given point of `D(X)`, whose
coordinate morphism is `f ∘ π`. -/
theorem endOfPoint_tmul_of_mem_weightSpace (π : C →ₐc[R] MonoidAlgebra R X)
    (f : MonoidAlgebra R X →ₐ[R] A) (a : A) {x : X} {v : V}
    (hv : v ∈ weightSpace V (π : C →ₗc[R] MonoidAlgebra R X) x) :
    Comodule.endOfPoint V (f.comp (π : C →ₐ[R] MonoidAlgebra R X)) (a ⊗ₜ[R] v) =
      (a * f (MonoidAlgebra.single x (1 : R))) ⊗ₜ[R] v := by
  rw [endOfPoint_tmul_comp, mem_weightSpace.mp hv]
  simp [TensorProduct.smul_tmul']

end Points

section MatrixCoefficient

variable {R C X W : Type*} [CommRing R]

/-- Under `π`, a matrix coefficient of an `x`-weight vector `w` becomes the multiple `φ w • x` of
the basis element `x` of `R[X]`. -/
theorem map_matrixCoefficient_of_mem_weightSpace [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid W] [Module R W] [Comodule R C W] (π : C →ₗc[R] MonoidAlgebra R X)
    {x : X} {w : W} (hw : w ∈ weightSpace W π x) (φ : Module.Dual R W) :
    π (Comodule.matrixCoefficient (R := R) (C := C) φ w) = φ w • MonoidAlgebra.single x 1 := by
  rw [mem_weightSpace] at hw
  let _ : Comodule R (MonoidAlgebra R X) W := Comodule.Corestrict π
  rw [← CoalgHom.matrixCoefficient_corestrict, Comodule.matrixCoefficient_def,
    Comodule.corestrict_coact_apply, hw]
  simp

/-- Under `π`, every matrix coefficient lies in the span of the weights whose weight spaces are
nonzero. -/
theorem map_matrixCoefficient_mem_span_single [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid W] [Module R W] [Comodule R C W] (π : C →ₗc[R] MonoidAlgebra R X)
    (φ : Module.Dual R W) (w : W) :
    π (Comodule.matrixCoefficient (R := R) (C := C) φ w) ∈
      Submodule.span R
        ((fun x ↦ MonoidAlgebra.single x (1 : R)) '' {x | weightSpace W π x ≠ ⊥}) := by
  have hw : w ∈ ⨆ x, weightSpace W π x := by
    rw [(isInternal_weightSpace W π).submodule_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction (weightSpace W π)
    (motive := fun w ↦ π (Comodule.matrixCoefficient (R := R) (C := C) φ w) ∈ _) hw
    (fun x w hw ↦ ?_) (by simp [Comodule.matrixCoefficient_def]) (fun w w' hw hw' ↦ ?_)
  · by_cases hx : weightSpace W π x = ⊥
    · have hw0 : w = 0 := by simpa [hx] using hw
      simp [hw0, Comodule.matrixCoefficient_def]
    · rw [map_matrixCoefficient_of_mem_weightSpace π hw]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_image_of_mem _ hx))
  · rw [Comodule.matrixCoefficient_add, map_add]
    exact add_mem hw hw'

/-- If every vector of a finite free comodule has weight `x`, the determinant of its coefficient
matrix restricts to the character `x ^ n`, where `n` is the rank. -/
theorem map_det_coefficientMatrix_of_forall_mem_weightSpace [CommRing C] [Bialgebra R C]
    [CommMonoid X] [AddCommMonoid W] [Module R W] [Comodule R C W] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (π : C →ₐc[R] MonoidAlgebra R X) {x : X}
    (hW : ∀ w : W, w ∈ weightSpace W π.toCoalgHom x) (b : Module.Basis ι R W) :
    π (Comodule.coefficientMatrix (C := C) b).det =
      MonoidAlgebra.single (x ^ Fintype.card ι) 1 := by
  have hmap : (Comodule.coefficientMatrix (C := C) b).map π.toAlgHom =
      Matrix.diagonal fun _ ↦ MonoidAlgebra.single x 1 := Matrix.ext fun i j ↦ by
    have h := map_matrixCoefficient_of_mem_weightSpace π.toCoalgHom (hW (b j)) (b.coord i)
    rw [BialgHom.toCoalgHom_apply] at h
    rw [Matrix.map_apply, Comodule.coefficientMatrix_apply, BialgHom.coe_toAlgHom, h,
      Module.Basis.coord_apply, Module.Basis.repr_self, Matrix.diagonal_apply,
      Finsupp.single_apply]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij, hij.symm]
  rw [← BialgHom.coe_toAlgHom, AlgHom.map_det, AlgHom.mapMatrix_apply, hmap, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, MonoidAlgebra.single_pow, one_pow]

end MatrixCoefficient

end DiagonalizableGroup

end TauCeti
