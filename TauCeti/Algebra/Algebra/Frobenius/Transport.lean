/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Algebra.Frobenius.Basic
public import TauCeti.Algebra.Algebra.Frobenius.Coalgebra

/-!
# Transport, tensor products, and scalar extension of perfect Frobenius traces

This file supplies the functorial operations on trace-reconstructed Frobenius coalgebras:

* **Transport along trace-preserving algebra equivalences**: an algebra isomorphism `f : A ≃ₐ[R] B`
  intertwining functionals `εB ∘ f = εA` preserves perfectness of the multiplication pairing, maps
  `traceDualBasis` to `traceDualBasis`, upgrades to a coalgebra equivalence
  `AlgEquiv.frobeniusCoalgEquiv` between the reconstructed Frobenius coalgebras, and carries the
  handle element of `A` to that of `B`.
* **Tensor products**: for finite projective commutative `R`-algebras `A` and `B` with perfect
  traces `εA` and `εB`, the product trace `TensorProduct.dualDistrib R A B (εA ⊗ₜ εB)` on
  `A ⊗[R] B` has a perfect multiplication pairing, its reconstructed Frobenius coalgebra is the
  tensor-product coalgebra, its trace-dual basis is the tensor product of the trace-dual bases, and
  its handle element is `handle A ⊗ₜ handle B`.
* **Scalar extension**: for any commutative `R`-algebra `S` and finite projective commutative
  `R`-algebra `A` with perfect trace `ε`, the extended trace `Module.Dual.baseChange S ε` on
  `S ⊗[R] A` has a perfect multiplication pairing over `S`, its reconstructed Frobenius coalgebra
  is the base-changed coalgebra, its trace-dual basis is the base-changed trace-dual basis, and its
  handle element is `1 ⊗ₜ handle A`.

## Main definitions and results

* `LinearMap.isPerfPair_compr₂_mul_of_algEquiv`, `LinearMap.isPerfPair_compr₂_mul_iff_of_algEquiv`:
  perfectness of the multiplication pairing is invariant under trace-preserving algebra
  equivalences.
* `LinearMap.traceDualBasis_map`: `traceDualBasis` commutes with trace-preserving algebra
  equivalences.
* `AlgEquiv.frobeniusCoalgEquiv`, `AlgEquiv.map_frobeniusCoalgebra_handle`: a trace-preserving
  algebra equivalence upgrades to a coalgebra equivalence between reconstructed Frobenius
  coalgebras and preserves the handle element.
* `LinearMap.isPerfPair_compr₂_mul_dualDistrib_tmul`,
  `LinearMap.frobeniusCoalgebra_dualDistrib_tmul`,
  `LinearMap.traceDualBasis_tensorProduct`,
  `LinearMap.frobeniusCoalgebra_handle_dualDistrib_tmul`: tensor products of perfect Frobenius
  traces.
* `LinearMap.isPerfPair_compr₂_mul_baseChange`, `LinearMap.frobeniusCoalgebra_baseChange`,
  `LinearMap.traceDualBasis_baseChange`, `LinearMap.frobeniusCoalgebra_handle_baseChange`:
  scalar extension of perfect Frobenius traces.

## References

* J. Kock, *Frobenius Algebras and 2D Topological Quantum Field Theories*, Chapter 2.
-/

public section

noncomputable section

open TensorProduct

section Transport

namespace LinearMap

section Semiring

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- Transporting a perfect multiplication pairing along an algebra equivalence that intertwines the
functionals gives a perfect multiplication pairing. -/
theorem isPerfPair_compr₂_mul_of_algEquiv {εA : A →ₗ[R] R} {εB : B →ₗ[R] R}
    [hA : ((mul R A).compr₂ εA).IsPerfPair] (f : A ≃ₐ[R] B) (hf : ∀ a, εB (f a) = εA a) :
    ((mul R B).compr₂ εB).IsPerfPair := by
  have h (x : B) : εA (f.symm x) = εB x := by simpa using (hf (f.symm x)).symm
  have hleft : (mul R B).compr₂ εB =
      (Module.Dual.congr f.toLinearEquiv).toLinearMap ∘ₗ
        ((mul R A).compr₂ εA) ∘ₗ f.symm.toLinearEquiv.toLinearMap := by
    ext b₁ b₂
    simp [← map_mul, h]
  have hright : ((mul R B).compr₂ εB).flip =
      (Module.Dual.congr f.toLinearEquiv).toLinearMap ∘ₗ
        ((mul R A).compr₂ εA).flip ∘ₗ f.symm.toLinearEquiv.toLinearMap := by
    ext b₁ b₂
    simp [← map_mul, h]
  refine ⟨?_, ?_⟩
  · rw [hleft]
    exact (Module.Dual.congr f.toLinearEquiv).bijective.comp
      (hA.bijective_left.comp f.symm.bijective)
  · rw [hright]
    exact (Module.Dual.congr f.toLinearEquiv).bijective.comp
      (hA.bijective_right.comp f.symm.bijective)

/-- A trace-preserving algebra equivalence preserves and reflects perfectness of the multiplication
pairing. -/
theorem isPerfPair_compr₂_mul_iff_of_algEquiv {εA : A →ₗ[R] R} {εB : B →ₗ[R] R}
    (f : A ≃ₐ[R] B) (hf : ∀ a, εB (f a) = εA a) :
    ((mul R A).compr₂ εA).IsPerfPair ↔ ((mul R B).compr₂ εB).IsPerfPair :=
  ⟨fun h => @isPerfPair_compr₂_mul_of_algEquiv R A B _ _ _ _ _ _ _ h f hf,
    fun h => @isPerfPair_compr₂_mul_of_algEquiv R B A _ _ _ _ _ _ _ h f.symm fun b => by
      simpa using (hf (f.symm b)).symm⟩

/-- Pushing a functional forward along an algebra equivalence via `Module.Dual.congr` preserves
perfectness of the multiplication pairing. -/
instance isPerfPair_compr₂_mul_dualCongr (εA : A →ₗ[R] R)
    [((mul R A).compr₂ εA).IsPerfPair] (f : A ≃ₐ[R] B) :
    ((mul R B).compr₂ (Module.Dual.congr f.toLinearEquiv εA)).IsPerfPair :=
  isPerfPair_compr₂_mul_of_algEquiv (εA := εA) f fun a => by simp

end Semiring

section CommSemiring

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]

/-- Mapping a finite basis across a trace-preserving algebra equivalence commutes with forming the
trace-dual basis. -/
theorem traceDualBasis_map {ι : Type*} [Finite ι] (b : Module.Basis ι R A)
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]
    (f : A ≃ₐ[R] B) (hf : ∀ a, εB (f a) = εA a) :
    traceDualBasis εB (b.map f.toLinearEquiv) = (traceDualBasis εA b).map f.toLinearEquiv := by
  ext i
  apply ((mul R B).compr₂ εB).toPerfPair.injective
  ext x
  simp only [toLinearMap_toPerfPair, compr₂_apply, mul_apply_apply, traceDualBasis_mul,
    Module.Basis.map_repr, LinearEquiv.trans_apply,
    Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply]
  conv_rhs => rw [← f.apply_symm_apply x, ← map_mul, hf, traceDualBasis_mul]
  rfl

/-- Pointwise form of `LinearMap.traceDualBasis_map`. -/
theorem traceDualBasis_map_apply {ι : Type*} [Finite ι] (b : Module.Basis ι R A)
    (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]
    (f : A ≃ₐ[R] B) (hf : ∀ a, εB (f a) = εA a) (i : ι) :
    traceDualBasis εB (b.map f.toLinearEquiv) i = f (traceDualBasis εA b i) := by
  rw [traceDualBasis_map b εA εB f hf, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply]

end CommSemiring

end LinearMap

namespace AlgEquiv

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]

/-- A trace-preserving algebra equivalence upgrades to a coalgebra equivalence between the
reconstructed Frobenius coalgebras. -/
def frobeniusCoalgEquiv (f : A ≃ₐ[R] B) (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hf : ∀ a, εB (f a) = εA a) :
    letI := εA.frobeniusCoalgebra
    letI := εB.frobeniusCoalgebra
    A ≃ₗc[R] B :=
  letI := εA.frobeniusCoalgebra
  letI := εB.frobeniusCoalgebra
  { f.toLinearEquiv with
    counit_comp := by
      ext a
      simpa using hf a
    map_comp_comul := by
      ext a
      apply (LinearMap.traceTensorEquiv εB).injective
      apply TensorProduct.ext'
      intro x y
      have hmap (t : A ⊗[R] A) :
          LinearMap.traceTensorEquiv εB (TensorProduct.map f.toLinearMap f.toLinearMap t)
              (x ⊗ₜ[R] y) =
            LinearMap.traceTensorEquiv εA t (f.symm x ⊗ₜ[R] f.symm y) := by
        induction t using TensorProduct.inductionOn with
        | tmul u v =>
          simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply,
            LinearMap.traceTensorEquiv_tmul]
          conv_lhs =>
            rw [← f.apply_symm_apply x, ← map_mul f, hf, ← f.apply_symm_apply y, ← map_mul f, hf]
        | add t u ht hu => simp_all
      simp only [LinearMap.comp_apply, AlgEquiv.toLinearEquiv_toLinearMap]
      rw [hmap, LinearMap.traceTensorEquiv_frobeniusCoalgebra_comul,
        LinearMap.traceTensorEquiv_frobeniusCoalgebra_comul, ← hf]
      simp [map_mul] }

/-- The underlying map of `AlgEquiv.frobeniusCoalgEquiv` is the algebra equivalence itself. -/
@[simp] theorem coe_frobeniusCoalgEquiv (f : A ≃ₐ[R] B) (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hf : ∀ a, εB (f a) = εA a) :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      ⇑(f.frobeniusCoalgEquiv εA εB hf)) = ⇑f := (rfl)

/-- The underlying linear equivalence of `AlgEquiv.frobeniusCoalgEquiv` is `f.toLinearEquiv`. -/
@[simp] theorem toLinearEquiv_frobeniusCoalgEquiv (f : A ≃ₐ[R] B) (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hf : ∀ a, εB (f a) = εA a) :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      (f.frobeniusCoalgEquiv εA εB hf : A ≃ₗ[R] B)) = f.toLinearEquiv := (rfl)

/-- The underlying linear map of `AlgEquiv.frobeniusCoalgEquiv` is `f.toLinearMap`. -/
theorem toLinearMap_frobeniusCoalgEquiv (f : A ≃ₐ[R] B) (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hf : ∀ a, εB (f a) = εA a) :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      (f.frobeniusCoalgEquiv εA εB hf).toLinearMap) = f.toLinearMap := (rfl)

/-- The inverse of `AlgEquiv.frobeniusCoalgEquiv` is the Frobenius coalgebra equivalence induced by
`f.symm`. -/
@[simp] theorem symm_frobeniusCoalgEquiv (f : A ≃ₐ[R] B) (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hf : ∀ a, εB (f a) = εA a) :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      (f.frobeniusCoalgEquiv εA εB hf).symm) =
    (letI := εB.frobeniusCoalgebra; letI := εA.frobeniusCoalgebra;
      f.symm.frobeniusCoalgEquiv εB εA fun b => by simpa using (hf (f.symm b)).symm) := by
  let := εA.frobeniusCoalgebra
  let := εB.frobeniusCoalgebra
  ext b
  rfl

/-- A trace-preserving algebra equivalence sends the reconstructed handle element of `A` to that
of `B`. -/
theorem map_frobeniusCoalgebra_handle (f : A ≃ₐ[R] B) (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
    [((LinearMap.mul R A).compr₂ εA).IsPerfPair] [((LinearMap.mul R B).compr₂ εB).IsPerfPair]
    (hf : ∀ a, εB (f a) = εA a) :
    f (letI := εA.frobeniusCoalgebra; Coalgebra.handle R A) =
      (letI := εB.frobeniusCoalgebra; Coalgebra.handle R B) := by
  let := εA.frobeniusCoalgebra
  let := εB.frobeniusCoalgebra
  let e := f.frobeniusCoalgEquiv εA εB hf
  have he (a : A) : e a = f a := rfl
  have hcomul : CoalgebraStruct.comul (R := R) (1 : B) =
      TensorProduct.map (e : A →ₗ[R] B) (e : A →ₗ[R] B)
        (CoalgebraStruct.comul (R := R) (1 : A)) := by
    simp [← map_one f, ← he 1]
  rw [Coalgebra.handle_def, Coalgebra.handle_def, hcomul]
  generalize CoalgebraStruct.comul (R := R) (1 : A) = t
  induction t using TensorProduct.inductionOn with
  | tmul x y => simp [he, map_mul]
  | add t u ht hu => simp_all

end AlgEquiv

end Transport

namespace LinearMap

section TensorProduct

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
  [Algebra R A] [Algebra R B]
  [Module.Finite R A] [Module.Projective R A]
  [Module.Finite R B] [Module.Projective R B]
  (εA : A →ₗ[R] R) (εB : B →ₗ[R] R)
  [((mul R A).compr₂ εA).IsPerfPair] [((mul R B).compr₂ εB).IsPerfPair]

private theorem counit_tensorProduct_frobeniusCoalgebra :
    (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
      Coalgebra.counit (R := R) (A := A ⊗[R] B)) =
      TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB) := by
  let := εA.frobeniusCoalgebra
  let := εB.frobeniusCoalgebra
  ext a b
  simp [mul_comm]

/-- Tensoring two perfect traces on finite projective commutative algebras produces a perfect trace
on their tensor product. -/
theorem isPerfPair_compr₂_mul_dualDistrib_tmul :
    ((mul R (A ⊗[R] B)).compr₂ (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).IsPerfPair := by
  let := εA.frobeniusCoalgebra
  let := εB.frobeniusCoalgebra
  have := εA.frobeniusCoalgebra_isFrobenius
  have := εB.frobeniusCoalgebra_isFrobenius
  rw [← counit_tensorProduct_frobeniusCoalgebra εA εB]
  infer_instance

/-- The Frobenius coalgebra reconstructed from the tensor product of two perfect traces is the
tensor product of their reconstructed Frobenius coalgebras. -/
theorem frobeniusCoalgebra_dualDistrib_tmul :
    (letI := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB;
      (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra) =
      (letI := εA.frobeniusCoalgebra; letI := εB.frobeniusCoalgebra;
        (inferInstance : Coalgebra R (A ⊗[R] B))) := by
  let := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB
  let := εA.frobeniusCoalgebra
  let := εB.frobeniusCoalgebra
  have := εA.frobeniusCoalgebra_isFrobenius
  have := εB.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)) inferInstance
    (counit_tensorProduct_frobeniusCoalgebra εA εB) inferInstance

omit [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B] in
/-- The trace-dual basis of a tensor-product basis for a tensor-product trace is the tensor product
of the trace-dual bases. -/
theorem traceDualBasis_tensorProduct {ι κ : Type*} [Finite ι] [Finite κ]
    (bA : Module.Basis ι R A) (bB : Module.Basis κ R B)
    [hAB : ((mul R (A ⊗[R] B)).compr₂
      (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).IsPerfPair] :
    traceDualBasis (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)) (bA.tensorProduct bB) =
      (traceDualBasis εA bA).tensorProduct (traceDualBasis εB bB) := by
  ext ⟨i, j⟩
  apply ((mul R (A ⊗[R] B)).compr₂
    (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB))).toPerfPair.injective
  refine TensorProduct.ext' fun a b ↦ ?_
  simp only [toLinearMap_toPerfPair, compr₂_apply, mul_apply_apply, traceDualBasis_mul,
    Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_apply,
    Algebra.TensorProduct.tmul_mul_tmul, dualDistrib_apply, smul_eq_mul]
  rw [mul_comm]

/-- The handle element of a tensor product of perfect Frobenius traces is the tensor product of
their handle elements. -/
theorem frobeniusCoalgebra_handle_dualDistrib_tmul :
    (letI := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB;
      letI := (TensorProduct.dualDistrib R A B (εA ⊗ₜ[R] εB)).frobeniusCoalgebra;
      Coalgebra.handle R (A ⊗[R] B)) =
      (letI := εA.frobeniusCoalgebra; Coalgebra.handle R A) ⊗ₜ[R]
        (letI := εB.frobeniusCoalgebra; Coalgebra.handle R B) := by
  let := isPerfPair_compr₂_mul_dualDistrib_tmul εA εB
  let := εA.frobeniusCoalgebra
  let := εB.frobeniusCoalgebra
  have h := Coalgebra.handle_tensorProduct (R := R) (S := R) (A := A) (B := B)
  rw [frobeniusCoalgebra_dualDistrib_tmul εA εB]
  exact h

end TensorProduct

section BaseChange

variable {R : Type*} (S : Type*) {A : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring A] [Algebra R A] [Module.Finite R A] [Module.Projective R A]
  (ε : A →ₗ[R] R) [((mul R A).compr₂ ε).IsPerfPair]

private theorem counit_baseChange_frobeniusCoalgebra :
    (letI := ε.frobeniusCoalgebra; Coalgebra.counit (R := S) (A := S ⊗[R] A)) =
      Module.Dual.baseChange S ε := by
  let := ε.frobeniusCoalgebra
  ext a
  simp

/-- Extending scalars of a perfect trace on a finite projective commutative algebra gives a perfect
trace over the target commutative algebra. -/
instance isPerfPair_compr₂_mul_baseChange :
    ((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).IsPerfPair := by
  let := ε.frobeniusCoalgebra
  have := ε.frobeniusCoalgebra_isFrobenius
  rw [← counit_baseChange_frobeniusCoalgebra S ε]
  infer_instance

/-- Reconstructing the Frobenius coalgebra from the base-changed trace gives the base change of the
reconstructed Frobenius coalgebra. -/
theorem frobeniusCoalgebra_baseChange :
    (Module.Dual.baseChange S ε).frobeniusCoalgebra =
      (letI := ε.frobeniusCoalgebra; (inferInstance : Coalgebra S (S ⊗[R] A))) := by
  let := ε.frobeniusCoalgebra
  have := ε.frobeniusCoalgebra_isFrobenius
  exact frobeniusCoalgebra_eq (Module.Dual.baseChange S ε) inferInstance
    (counit_baseChange_frobeniusCoalgebra S ε) inferInstance

omit [Module.Finite R A] [Module.Projective R A] in
/-- Forming the trace-dual basis commutes with scalar extension of a finite basis. -/
theorem traceDualBasis_baseChange {ι : Type*} [Finite ι] (b : Module.Basis ι R A)
    [((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).IsPerfPair] :
    traceDualBasis (Module.Dual.baseChange S ε) (b.baseChange S) =
      (traceDualBasis ε b).baseChange S := by
  ext i
  apply ((mul S (S ⊗[R] A)).compr₂ (Module.Dual.baseChange S ε)).toPerfPair.injective
  refine TensorProduct.AlgebraTensorModule.ext fun s a ↦ ?_
  simp

/-- Scalar extension carries the reconstructed handle element `h` to `1 ⊗ₜ h`. -/
theorem frobeniusCoalgebra_handle_baseChange :
    (letI := (Module.Dual.baseChange S ε).frobeniusCoalgebra; Coalgebra.handle S (S ⊗[R] A)) =
      1 ⊗ₜ[R] (letI := ε.frobeniusCoalgebra; Coalgebra.handle R A) := by
  let := ε.frobeniusCoalgebra
  have h := Coalgebra.handle_baseChange (R := R) (S := S) (B := A)
  rw [frobeniusCoalgebra_baseChange S ε]
  exact h

end BaseChange

end LinearMap
