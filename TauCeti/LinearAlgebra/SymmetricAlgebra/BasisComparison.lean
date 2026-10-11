/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Data.Sym.NatCard
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear
public import TauCeti.RingTheory.MvPolynomial.Finrank

/-!
# Homogeneous symmetric polynomials in a basis

A basis identifies a symmetric algebra with a multivariate polynomial ring. This file records that
the equivalence sends a generator to the linear form with the same coordinates, and that it carries
each homogeneous submodule of the symmetric algebra to the corresponding total-degree submodule of
the polynomial ring.

## Main results

* `SymmetricAlgebra.equivMvPolynomial_ι`: the basis-induced equivalence sends the generator of `x`
  to the linear form `∑ᵢ (b.repr x i) Xᵢ`.
* `map_homogeneousSubmodule_equivMvPolynomial`: the basis-induced equivalence carries the degree
  `n` part of a symmetric algebra to the degree `n` part of a multivariate polynomial ring.
* `SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff`: the degreewise form of that comparison.
* `Sym.equivFinsuppDegree`: degree-`n` multisets are exponent vectors of total degree `n`.
* `Module.Basis.symmetricAlgebraHomogeneous`: the monomial basis of a homogeneous component of a
  symmetric algebra induced by a basis of the generating module.
-/

public section

namespace TauCeti.SymmetricAlgebra

open Module

universe u v w

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

variable {R M} in
/-- The algebra equivalence induced by a basis sends the generator of `x` to the linear form with
the coordinates of `x`. -/
@[simp]
theorem _root_.SymmetricAlgebra.equivMvPolynomial_ι {ι : Type w} (b : Basis ι R M) (x : M) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M x) =
      b.constr R MvPolynomial.X x := by
  have : (SymmetricAlgebra.equivMvPolynomial b).toLinearMap ∘ₗ SymmetricAlgebra.ι R M =
      b.constr R MvPolynomial.X := b.ext fun i ↦ by simp
  exact LinearMap.congr_fun this x

/-- The algebra equivalence induced by a basis preserves homogeneous degree. -/
@[simp]
theorem map_homogeneousSubmodule_equivMvPolynomial {ι : Type w} (b : Basis ι R M) (n : ℕ) :
    (homogeneousSubmodule R M n).map
        (SymmetricAlgebra.equivMvPolynomial b).toLinearMap =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, ← AlgEquiv.toLinearEquiv_toLinearMap,
    ← AlgEquiv.toAlgHom_toLinearMap,
    Submodule.map_pow (LinearMap.range (SymmetricAlgebra.ι R M))
      (SymmetricAlgebra.equivMvPolynomial b).toAlgHom n]
  congr 1
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, LinearMap.range_eq_map, ← b.span_eq,
    Submodule.map_span, Submodule.map_span, ← Set.image_comp, ← Set.range_comp]
  simp only [Function.comp_def, AlgHom.toLinearMap_apply, AlgEquiv.coe_toAlgHom,
    SymmetricAlgebra.equivMvPolynomial_ι_apply]

/-- An element of a symmetric algebra is homogeneous of degree `n` exactly when its image under
the polynomial equivalence induced by a basis is. -/
@[simp]
theorem _root_.SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff {ι : Type w}
    (b : Basis ι R M) (n : ℕ) (p : SymmetricAlgebra R M) :
    (SymmetricAlgebra.equivMvPolynomial b p).IsHomogeneous n ↔ p ∈ homogeneousSubmodule R M n := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, ← map_homogeneousSubmodule_equivMvPolynomial R M b n,
    Submodule.mem_map_equiv (e := (SymmetricAlgebra.equivMvPolynomial b).toLinearEquiv)]
  simp

/-- The restriction of the polynomial equivalence induced by `b` to homogeneous components. -/
noncomputable def homogeneousSubmoduleEquivMvPolynomial {ι : Type w} (b : Basis ι R M) (n : ℕ) :
    homogeneousSubmodule R M n ≃ₗ[R] MvPolynomial.homogeneousSubmodule ι R n :=
  (Submodule.equivMapOfInjective (SymmetricAlgebra.equivMvPolynomial b).toLinearMap
      (SymmetricAlgebra.equivMvPolynomial b).injective _).trans
    (LinearEquiv.ofEq _ _ (map_homogeneousSubmodule_equivMvPolynomial R M b n))

/-- The homogeneous-component equivalence is the restriction of
`SymmetricAlgebra.equivMvPolynomial`. -/
@[simp]
theorem coe_homogeneousSubmoduleEquivMvPolynomial_apply {ι : Type w} (b : Basis ι R M)
    (n : ℕ) (x : homogeneousSubmodule R M n) :
    ((homogeneousSubmoduleEquivMvPolynomial R M b n x :
      MvPolynomial.homogeneousSubmodule ι R n) : MvPolynomial ι R) =
        SymmetricAlgebra.equivMvPolynomial b x := by
  rfl

/-- Degree-`n` multisets of basis indices are equivalent to exponent vectors of total degree
`n`. -/
noncomputable def _root_.Sym.equivFinsuppDegree (ι : Type w) (n : ℕ) :
    Sym ι n ≃ {d : ι →₀ ℕ // d.degree = n} := by
  classical
  exact (Sym.equivNatSum ι n).trans
    (Equiv.subtypeEquiv (Equiv.refl _) (fun d => by
      simp [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Function.id_def]))

variable {R M} in
/-- A basis of a module induces the monomial basis on each homogeneous component of its
symmetric algebra. The basis vectors are indexed by degree-`n` multisets of basis indices. -/
noncomputable def _root_.Module.Basis.symmetricAlgebraHomogeneous {ι : Type w}
    (b : Basis ι R M) (n : ℕ) :
    Basis (Sym ι n) R (homogeneousSubmodule R M n) := by
  exact ((TauCeti.homogeneousMonomialBasis (R := R) n).map
    (homogeneousSubmoduleEquivMvPolynomial R M b n).symm).reindex
      (Sym.equivFinsuppDegree ι n).symm

/-- Under the polynomial equivalence, a homogeneous symmetric-algebra basis vector is the
corresponding monomial. -/
@[simp]
theorem equivMvPolynomial_symmetricAlgebraHomogeneous_apply {ι : Type w}
    (b : Basis ι R M) (n : ℕ)
    (d : Sym ι n) :
    SymmetricAlgebra.equivMvPolynomial b
        (Module.Basis.symmetricAlgebraHomogeneous b n d : SymmetricAlgebra R M) =
      MvPolynomial.monomial (Sym.equivFinsuppDegree ι n d).1 1 := by
  classical
  rw [← coe_homogeneousSubmoduleEquivMvPolynomial_apply R M b n]
  simp [Module.Basis.symmetricAlgebraHomogeneous]

section Semilinear

variable {S : Type*} [CommSemiring S] {N : Type*} [AddCommMonoid N] [Module S N]
  {φ : R →+* S}

/-- A semilinear map carrying one basis to another acts on their symmetric algebras by applying
the scalar homomorphism to polynomial coefficients. -/
theorem _root_.SymmetricAlgebra.equivMvPolynomial_mapₛₗ {ι : Type w}
    (b : Basis ι R M) (c : Basis ι S N)
    (f : M →ₛₗ[φ] N) (h : ∀ i, f (b i) = c i) (x : SymmetricAlgebra R M) :
    SymmetricAlgebra.equivMvPolynomial c (SymmetricAlgebra.mapₛₗ f x) =
      MvPolynomial.map φ (SymmetricAlgebra.equivMvPolynomial b x) := by
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => simp
  | ι x =>
      rw [SymmetricAlgebra.mapₛₗ_ι, SymmetricAlgebra.equivMvPolynomial_ι,
        SymmetricAlgebra.equivMvPolynomial_ι]
      let lhs : M →ₛₗ[φ] MvPolynomial ι S :=
        { toFun := fun y ↦ c.constr S MvPolynomial.X (f y)
          map_add' := fun y z ↦ by simp
          map_smul' := fun r y ↦ by simp }
      let rhs : M →ₛₗ[φ] MvPolynomial ι S :=
        { toFun := fun y ↦ MvPolynomial.map φ (b.constr R MvPolynomial.X y)
          map_add' := fun y z ↦ by simp
          map_smul' := fun r y ↦ by simp [Algebra.smul_def] }
      have hmaps : lhs = rhs := b.ext fun i ↦ by
        simp [lhs, rhs, h i]
      exact DFunLike.congr_fun hmaps x
  | mul x y hx hy => simp [hx, hy]
  | add x y hx hy => simp [hx, hy]

/-- A semilinear map carrying one basis to another carries each induced homogeneous basis vector
to the basis vector with the same exponent vector. -/
theorem homogeneousSubmoduleMapₛₗ_symmetricAlgebraHomogeneous {ι : Type w}
    (b : Basis ι R M)
    (c : Basis ι S N) (f : M →ₛₗ[φ] N) (h : ∀ i, f (b i) = c i) (n : ℕ)
    (d : Sym ι n) :
    homogeneousSubmoduleMapₛₗ f n (Module.Basis.symmetricAlgebraHomogeneous b n d) =
      Module.Basis.symmetricAlgebraHomogeneous c n d := by
  apply Subtype.ext
  apply (SymmetricAlgebra.equivMvPolynomial c).injective
  rw [coe_homogeneousSubmoduleMapₛₗ_apply,
    SymmetricAlgebra.equivMvPolynomial_mapₛₗ (R := R) (M := M) b c f h,
    equivMvPolynomial_symmetricAlgebraHomogeneous_apply,
    equivMvPolynomial_symmetricAlgebraHomogeneous_apply]
  simp

end Semilinear

end TauCeti.SymmetricAlgebra
