/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricAlgebra.GradedMap
public import TauCeti.RingTheory.GradedAlgebra.Polynomial
public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Scalar-equivariant morphisms of symmetric algebras

The universal scalar action on the affine scheme `Spec (Sym M)` has comorphism
`scalarCoaction : Sym M →ₐ[R] (Sym M)[X]`, sending `ι m` to `(ι m) X`. It records the standard
grading: an element of degree `n` maps to its product with `Xⁿ`.

An algebra homomorphism `Sym M → Sym N` intertwines these scalar coactions if and only if it
preserves the grading, and if and only if it is induced by a unique linear map `M →ₗ[R] N`.
This is the affine algebraic recognition of linear morphisms between linear schemes. No
freeness, finiteness, or characteristic assumption is needed. Equivariance is an identity in a
polynomial ring; testing only the scalars in `R` would not suffice over finite rings.

The construction uses the universal property of `SymmetricAlgebra.lift` and the identification
`TauCeti.SymmetricAlgebra.homogeneousSubmoduleOneEquiv` of the degree-one part with the module.

## References

* The Stacks Project, [Tag 01M1](https://stacks.math.columbia.edu/tag/01M1).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.7.
-/

public section

noncomputable section

namespace SymmetricAlgebra

open Polynomial TauCeti.SymmetricAlgebra TauCeti.GradedAlgebra

variable (R : Type*) [CommSemiring R]
variable (M : Type*) [AddCommMonoid M] [Module R M]

/-- The comorphism of universal scalar multiplication on `Spec (Sym M)`, sending a generator
`ι m` to the polynomial `(ι m) X`. -/
def scalarCoaction : SymmetricAlgebra R M →ₐ[R] (SymmetricAlgebra R M)[X] :=
  lift (((monomial 1).restrictScalars R).comp (ι R M))

/-- Universal scalar multiplication multiplies a generator by the indeterminate. -/
@[simp]
theorem scalarCoaction_ι (m : M) :
    scalarCoaction R M (ι R M m) = monomial 1 (ι R M m) := by
  simp [scalarCoaction]

/-- The scalar coaction records the homogeneous components of the standard grading. -/
theorem scalarCoaction_apply (a : SymmetricAlgebra R M) :
    scalarCoaction R M a = toPolynomial (homogeneousSubmodule R M) a := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [AlgHom.commutes, toPolynomial_of_mem
      (SetLike.algebraMap_mem_graded (homogeneousSubmodule R M) r)]
    simp
  | ι m => rw [scalarCoaction_ι, toPolynomial_of_mem (ι_mem_homogeneousSubmodule R M m)]
  | add a b ha hb => simp only [map_add, ha, hb]
  | mul a b ha hb => simp only [map_mul, ha, hb]

/-- A homogeneous element of degree `n` transforms by the `n`th power of the universal scalar. -/
theorem scalarCoaction_of_mem {n : ℕ} {a : SymmetricAlgebra R M}
    (ha : a ∈ homogeneousSubmodule R M n) :
    scalarCoaction R M a = monomial n a := by
  rw [scalarCoaction_apply, toPolynomial_of_mem ha]

/-- On points valued in any commutative `R`-algebra, specializing the universal scalar to `c`
multiplies the corresponding linear functional by `c`. -/
@[simp]
theorem eval₂_scalarCoaction {S : Type*} [CommSemiring S] [Algebra R S]
    (φ : SymmetricAlgebra R M →ₐ[R] S) (c : S) (a : SymmetricAlgebra R M) :
    Polynomial.eval₂ (φ : SymmetricAlgebra R M →+* S) c (scalarCoaction R M a) =
      lift (c • (φ.toLinearMap.comp (ι R M))) a := by
  have h : (Polynomial.eval₂AlgHom φ c (fun _ ↦ Commute.all _ _)).comp
      (scalarCoaction R M) = lift (c • (φ.toLinearMap.comp (ι R M))) := by
    apply algHom_ext
    ext m
    simp [mul_comm]
  exact AlgHom.congr_fun h a

variable {M} {N : Type*} [AddCommMonoid N] [Module R N]

/-- An algebra homomorphism of symmetric algebras intertwines universal scalar multiplication
exactly when it preserves every homogeneous component. -/
theorem map_scalarCoaction_eq_iff (φ : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N) :
    (∀ a, Polynomial.map φ.toRingHom (scalarCoaction R M a) = scalarCoaction R N (φ a)) ↔
      ∀ (n : ℕ) (a : SymmetricAlgebra R M), a ∈ homogeneousSubmodule R M n →
        φ a ∈ homogeneousSubmodule R N n := by
  simp only [scalarCoaction_apply]
  exact φ.toRingHom.map_toPolynomial_eq_iff

/-- An algebra homomorphism of symmetric algebras intertwines universal scalar multiplication
if and only if it is induced by a unique linear map. In particular no separate additivity
hypothesis on the associated affine-scheme morphism is necessary. -/
theorem map_scalarCoaction_eq_iff_existsUnique
    (φ : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R N) :
    (∀ a, Polynomial.map φ.toRingHom (scalarCoaction R M a) = scalarCoaction R N (φ a)) ↔
      ∃! f : M →ₗ[R] N, map R f = φ := by
  rw [map_scalarCoaction_eq_iff]
  constructor
  · intro hφ
    exact (existsUnique_map_eq_iff R φ).mpr fun m ↦
      hφ 1 _ (ι_mem_homogeneousSubmodule R M m)
  · rintro ⟨f, rfl, _⟩ n a ha
    simpa using (gradedMap R f).map_mem ha

end SymmetricAlgebra
