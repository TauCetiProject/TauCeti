/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.CentralSimple
public import TauCeti.Algebra.Quaternion.SquareSplit
public import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Algebra.CentralSimple.TensorProduct
import TauCeti.Algebra.Quaternion.Basis
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tensor products of quaternion algebras with a common slot

Two quaternion algebras `ℍ[R,a,b]` and `ℍ[R,a,c]` sharing their first parameter have a tensor
product that is again a quaternion algebra up to a matrix factor:

```text
ℍ[K,a,b] ⊗[K] ℍ[K,a,c] ≃ₐ[K] ℍ[K,a,bc] ⊗[K] M₂(K)
```

This is the *common slot lemma* (Lam III.2.11, Gille–Szamuely Lemma 1.5.2). In the Brauer group
it says that the quaternion symbol is multiplicative in each argument, which is what
`TauCeti/Algebra/Quaternion/BrauerClass.lean` proves from it.

The construction is the classical one. Writing `i₁, j₁` and `i₂, j₂` for the generators of the
two factors, the elements `i₁ ⊗ 1` and `j₁ ⊗ j₂` satisfy the relations of `ℍ[R,a,bc]`
(`TauCeti.QuaternionAlgebra.linkedBasis`), the elements `i₁ ⊗ i₂` and `1 ⊗ j₂` satisfy those of
`ℍ[R,a²,c]` (`TauCeti.QuaternionAlgebra.squareBasis`), and the two pairs commute. The universal
property `QuaternionAlgebra.Basis.liftHom`, its compatibility with commuting generators
(`QuaternionAlgebra.Basis.commute_liftHom` in `TauCeti/Algebra/Quaternion/Basis.lean`) and
`Algebra.TensorProduct.lift` then produce an algebra map
`ℍ[R,a,bc] ⊗[R] ℍ[R,a²,c] → ℍ[R,a,b] ⊗[R] ℍ[R,a,c]`, defined over any commutative ring. Over a
field with `2` invertible and unit parameters both sides are `16`-dimensional and the source is a
simple ring, so the map is bijective; the factor `ℍ[K,a²,c]` is split because its first parameter
is a square.

## Main results

* `TauCeti.QuaternionAlgebra.linkedTensorHom`: the algebra map
  `ℍ[R,a,bc] ⊗[R] ℍ[R,a²,c] →ₐ[R] ℍ[R,a,b] ⊗[R] ℍ[R,a,c]` over a commutative ring.
* `TauCeti.QuaternionAlgebra.linkedTensorAlgEquiv`: over a field with `2` invertible and unit
  parameters, that map is an isomorphism.
* `TauCeti.QuaternionAlgebra.tensorAlgEquivTensorMatrix`: **the common slot lemma**
  `ℍ[K,a,b] ⊗[K] ℍ[K,a,c] ≃ₐ[K] ℍ[K,a,bc] ⊗[K] M₂(K)`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter III, Theorem 2.11.
* P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology* (2006), Lemma 1.5.2.
-/

public section

open scoped Quaternion TensorProduct

namespace TauCeti

namespace QuaternionAlgebra

open _root_.QuaternionAlgebra (Basis)

section CommRing

variable {R : Type*} [CommRing R] (a b c : R)

/-- In `ℍ[R,a,b] ⊗[R] ℍ[R,a,c]` the elements `i ⊗ 1`, `j ⊗ j` and `k ⊗ j` satisfy the relations of
`ℍ[R,a,bc]`: they form a quaternion basis of type `(a, bc)`. -/
def linkedBasis : Basis (ℍ[R,a,b] ⊗[R] ℍ[R,a,c]) a 0 (b * c) where
  i := (Basis.self R).i ⊗ₜ 1
  j := (Basis.self R).j ⊗ₜ (Basis.self R).j
  k := (Basis.self R).k ⊗ₜ (Basis.self R).j
  i_mul_i := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.i_mul_i, zero_smul, add_zero, mul_one,
      TensorProduct.smul_tmul', Algebra.TensorProduct.one_def]
  j_mul_j := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.j_mul_j, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, smul_smul, Algebra.TensorProduct.one_def, mul_comm c b]
  i_mul_j := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.i_mul_j, one_mul]
  j_mul_i := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.j_mul_i, zero_smul, zero_sub, mul_one,
      TensorProduct.neg_tmul]

/-- In `ℍ[R,a,b] ⊗[R] ℍ[R,a,c]` the elements `i ⊗ i`, `1 ⊗ j` and `i ⊗ k` satisfy the relations of
`ℍ[R,a²,c]`: they form a quaternion basis of type `(a², c)`. -/
def squareBasis : Basis (ℍ[R,a,b] ⊗[R] ℍ[R,a,c]) (a ^ 2) 0 c where
  i := (Basis.self R).i ⊗ₜ (Basis.self R).i
  j := 1 ⊗ₜ (Basis.self R).j
  k := (Basis.self R).i ⊗ₜ (Basis.self R).k
  i_mul_i := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.i_mul_i, zero_smul, add_zero,
      TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, Algebra.TensorProduct.one_def,
      sq]
  j_mul_j := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.j_mul_j, one_mul,
      TensorProduct.tmul_smul, Algebra.TensorProduct.one_def]
  i_mul_j := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.i_mul_j, mul_one]
  j_mul_i := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, Basis.j_mul_i, zero_smul, zero_sub, one_mul,
      TensorProduct.tmul_neg]

@[simp] theorem linkedBasis_i : (linkedBasis a b c).i = (Basis.self R).i ⊗ₜ 1 := (rfl)

@[simp] theorem linkedBasis_j :
    (linkedBasis a b c).j = (Basis.self R).j ⊗ₜ (Basis.self R).j := (rfl)

@[simp] theorem linkedBasis_k :
    (linkedBasis a b c).k = (Basis.self R).k ⊗ₜ (Basis.self R).j := (rfl)

@[simp] theorem squareBasis_i :
    (squareBasis a b c).i = (Basis.self R).i ⊗ₜ (Basis.self R).i := (rfl)

@[simp] theorem squareBasis_j : (squareBasis a b c).j = 1 ⊗ₜ (Basis.self R).j := (rfl)

@[simp] theorem squareBasis_k :
    (squareBasis a b c).k = (Basis.self R).i ⊗ₜ (Basis.self R).k := (rfl)

/-- The two quaternion bases `linkedBasis` and `squareBasis` of `ℍ[R,a,b] ⊗[R] ℍ[R,a,c]` induce
commuting algebra maps. -/
private theorem commute_linkedBasis_liftHom_squareBasis_liftHom
    (x : ℍ[R,a,b * c]) (y : ℍ[R,a ^ 2,c]) :
    Commute ((linkedBasis a b c).liftHom x) ((squareBasis a b c).liftHom y) := by
  refine Basis.commute_liftHom _ _ ?_ ?_ ?_ ?_ x y
  · exact (Commute.refl _).tmul (Commute.one_left _)
  · exact (Commute.one_right _).tmul (Commute.one_left _)
  · simp only [Commute, SemiconjBy, linkedBasis_j, squareBasis_i,
      Algebra.TensorProduct.tmul_mul_tmul, Basis.j_mul_i, Basis.i_mul_j, zero_smul, zero_sub,
      TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]
  · exact (Commute.one_right _).tmul (Commute.refl _)

/-- The algebra map `ℍ[R,a,bc] ⊗[R] ℍ[R,a²,c] → ℍ[R,a,b] ⊗[R] ℍ[R,a,c]` of the common slot lemma,
sending the generators `i ⊗ 1, j ⊗ 1` of the first factor to `i ⊗ 1, j ⊗ j` and the generators
`1 ⊗ i, 1 ⊗ j` of the second factor to `i ⊗ i, 1 ⊗ j`. -/
def linkedTensorHom : ℍ[R,a,b * c] ⊗[R] ℍ[R,a ^ 2,c] →ₐ[R] ℍ[R,a,b] ⊗[R] ℍ[R,a,c] :=
  Algebra.TensorProduct.lift (linkedBasis a b c).liftHom (squareBasis a b c).liftHom
    (commute_linkedBasis_liftHom_squareBasis_liftHom a b c)

@[simp]
theorem linkedTensorHom_tmul (x : ℍ[R,a,b * c]) (y : ℍ[R,a ^ 2,c]) :
    linkedTensorHom a b c (x ⊗ₜ y) =
      (linkedBasis a b c).liftHom x * (squareBasis a b c).liftHom y := by
  rw [linkedTensorHom, Algebra.TensorProduct.lift_tmul]

end CommRing

section Field

variable {K : Type*} [Field K] [Invertible (2 : K)] (a b c : Kˣ)

/-- Over a field with `2` invertible and unit parameters, the common-slot map
`ℍ[K,a,bc] ⊗[K] ℍ[K,a²,c] → ℍ[K,a,b] ⊗[K] ℍ[K,a,c]` is bijective. -/
theorem linkedTensorHom_bijective :
    Function.Bijective (linkedTensorHom (a : K) (b : K) (c : K)) := by
  -- The source is a simple ring, so the map is injective; both sides have dimension `16`.
  have : IsSimpleRing ℍ[K,(a : K),(b : K) * (c : K)] := instIsSimpleRing a (b * c)
  have : Algebra.IsCentral K ℍ[K,(a : K),(b : K) * (c : K)] := instIsCentral (a : K) (b * c)
  have : IsSimpleRing ℍ[K,(a : K) ^ 2,(c : K)] :=
    IsSimpleRing.of_ringEquiv (firstSquareEquivMatrix a c).symm.toRingEquiv inferInstance
  have hinj : Function.Injective (linkedTensorHom (a : K) (b : K) (c : K)) :=
    (linkedTensorHom (a : K) (b : K) (c : K)).toRingHom.injective
  refine ⟨hinj, ?_⟩
  have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (linkedTensorHom (a : K) (b : K) (c : K)).toLinearMap) (by
      simp only [Module.finrank_tensorProduct, _root_.QuaternionAlgebra.finrank_eq_four])).1 hinj
  exact h

/-- **The common slot lemma, first form.** Over a field with `2` invertible and unit parameters,
`ℍ[K,a,bc] ⊗[K] ℍ[K,a²,c] ≃ₐ[K] ℍ[K,a,b] ⊗[K] ℍ[K,a,c]`. -/
noncomputable def linkedTensorAlgEquiv :
    ℍ[K,(a : K),(b : K) * (c : K)] ⊗[K] ℍ[K,(a : K) ^ 2,(c : K)] ≃ₐ[K]
      ℍ[K,(a : K),(b : K)] ⊗[K] ℍ[K,(a : K),(c : K)] :=
  AlgEquiv.ofBijective _ (linkedTensorHom_bijective a b c)

@[simp]
theorem linkedTensorAlgEquiv_apply
    (x : ℍ[K,(a : K),(b : K) * (c : K)] ⊗[K] ℍ[K,(a : K) ^ 2,(c : K)]) :
    linkedTensorAlgEquiv a b c x = linkedTensorHom (a : K) (b : K) (c : K) x := by
  rw [linkedTensorAlgEquiv, AlgEquiv.ofBijective_apply]

/-- **The common slot lemma** (Lam III.2.11, Gille–Szamuely 1.5.2): for units `a b c` of a field
with `2` invertible, `ℍ[K,a,b] ⊗[K] ℍ[K,a,c] ≃ₐ[K] ℍ[K,a,bc] ⊗[K] M₂(K)`. In the Brauer group this
is the multiplicativity of the quaternion symbol in its second argument. -/
noncomputable def tensorAlgEquivTensorMatrix :
    ℍ[K,(a : K),(b : K)] ⊗[K] ℍ[K,(a : K),(c : K)] ≃ₐ[K]
      ℍ[K,(a : K),(b : K) * (c : K)] ⊗[K] Matrix (Fin 2) (Fin 2) K :=
  (linkedTensorAlgEquiv a b c).symm.trans
    (Algebra.TensorProduct.congr AlgEquiv.refl (firstSquareEquivMatrix a c))

/-- The inverse of the common slot equivalence on a pure tensor: pull the matrix back to
`ℍ[K,a²,c]` through `firstSquareEquivMatrix` and multiply the images of the two factors. -/
@[simp]
theorem tensorAlgEquivTensorMatrix_symm_tmul (x : ℍ[K,(a : K),(b : K) * (c : K)])
    (M : Matrix (Fin 2) (Fin 2) K) :
    (tensorAlgEquivTensorMatrix a b c).symm (x ⊗ₜ M) =
      (linkedBasis (a : K) (b : K) (c : K)).liftHom x *
        (squareBasis (a : K) (b : K) (c : K)).liftHom ((firstSquareEquivMatrix a c).symm M) := by
  simp only [tensorAlgEquivTensorMatrix, AlgEquiv.symm_trans_apply,
    Algebra.TensorProduct.congr_symm_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.refl_symm,
    AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, AlgEquiv.symm_symm, linkedTensorAlgEquiv_apply,
    linkedTensorHom_tmul]

end Field

end QuaternionAlgebra

end TauCeti
