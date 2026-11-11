/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.Algebra.Ring.Hom.InjSurj
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Algebra endomorphisms, orbits of algebraic elements, and eigenvector independence

Let `A` be a commutative integral domain that is a faithful algebra over a commutative ring `R`,
and let `σ : A →ₐ[R] A` be an `R`-algebra endomorphism. This file proves two general criteria
linking the dynamics of `σ` to algebraicity and algebraic independence over `R`:

1. **Finite orbits of algebraic elements.** Every element `x : A` algebraic over `R` satisfies a
   nonzero polynomial over `R`, whose root set in the domain `A` is finite and `σ`-invariant.
   Consequently the iterates `(σ ^ n) x` repeat (`IsAlgebraic.exists_pow_apply_eq_of_algHom`), and
   if `σ` is an `R`-algebra automorphism (`A ≃ₐ[R] A`), some positive iterate fixes `x`
   (`IsAlgebraic.exists_pow_apply_eq_self_of_algEquiv`). Equivalently, an element with no
   nontrivial fixing power of `σ` is transcendental over `R`
   (`AlgEquiv.transcendental_of_forall_pow_algEquiv_ne_self`).

2. **Algebraic independence of multiplicatively independent eigenvectors.** Suppose `(yᵢ)` is a
   family of nonzero elements of `A` satisfying `σ (yᵢ) = algebraMap R A (uᵢ) * yᵢ` for scalars
   `uᵢ : R`. If the monomial-eigenvalue map `d ↦ ∏ᵢ uᵢ ^ (d i)` on finitely supported exponent
   tuples `ι →₀ ℕ` is injective, then distinct monomials in the `yᵢ` are nonzero `σ`-eigenvectors
   with distinct eigenvalues, hence `R`-linearly independent by
   `Module.End.eigenvectors_linearIndependent'`, so `(yᵢ)` is algebraically independent over `R`
   (`AlgHom.algebraicIndependent_of_algHom_eigenvectors`).

## Main results

* `IsAlgebraic.exists_pow_apply_eq_of_algHom`: iterates of an `R`-algebra endomorphism on an
  algebraic element of a domain eventually collide.
* `IsAlgebraic.exists_pow_apply_eq_self_of_algEquiv`: every algebraic element of a domain is fixed
  by some positive power of any `R`-algebra automorphism.
* `AlgEquiv.transcendental_of_forall_pow_algEquiv_ne_self`: an element moved by every positive
  power of an `R`-algebra automorphism is transcendental over `R`.
* `AlgHom.algebraicIndependent_of_algHom_eigenvectors`: nonzero `σ`-eigenvectors whose eigenvalues
  have injective monomial products are algebraically independent over `R`.
-/

public section

namespace IsAlgebraic

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

private theorem pow_algHom_mem_rootSet {p : Polynomial R} (hp0 : p ≠ 0) {x : A}
    (hx : Polynomial.aeval x p = 0) (σ : A →ₐ[R] A) :
    ∀ n : ℕ, (σ ^ n) x ∈ p.rootSet A
  | 0 => by
      rw [pow_zero, AlgHom.one_apply, Polynomial.mem_rootSet',
        Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R A)]
      exact ⟨hp0, hx⟩
  | n + 1 => by
      rw [pow_succ', AlgHom.mul_apply]
      exact Polynomial.rootSet_maps_to' id σ (pow_algHom_mem_rootSet hp0 hx σ n)

/-- In a domain `A` faithful over `R`, the iterates of an `R`-algebra endomorphism `σ : A →ₐ[R] A`
on an algebraic element `x` eventually repeat. -/
theorem exists_pow_apply_eq_of_algHom {x : A} (hx : IsAlgebraic R x) (σ : A →ₐ[R] A) :
    ∃ i j : ℕ, i < j ∧ (σ ^ i) x = (σ ^ j) x := by
  obtain ⟨p, hp0, hpx⟩ := hx
  obtain ⟨i, j, hij⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun n : ℕ ↦ (⟨(σ ^ n) x, pow_algHom_mem_rootSet hp0 hpx σ n⟩ : p.rootSet A))
  rcases lt_or_gt_of_ne hij.1 with hlt | hgt
  · exact ⟨i, j, hlt, congrArg Subtype.val hij.2⟩
  · exact ⟨j, i, hgt, (congrArg Subtype.val hij.2).symm⟩

/-- In a domain `A` faithful over `R`, every element algebraic over `R` is fixed by some nonzero
power of any `R`-algebra automorphism `σ : A ≃ₐ[R] A`. -/
theorem exists_pow_apply_eq_self_of_algEquiv {x : A} (hx : IsAlgebraic R x) (σ : A ≃ₐ[R] A) :
    ∃ n : ℕ, n ≠ 0 ∧ (σ ^ n) x = x := by
  have hpow (m : ℕ) (y : A) : (σ.toAlgHom ^ m) y = (σ ^ m) y := by
    induction m generalizing y with
    | zero => rfl
    | succ m ih => rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgEquiv.mul_apply, ih]; rfl
  obtain ⟨i, j, hij, heq⟩ := hx.exists_pow_apply_eq_of_algHom σ.toAlgHom
  refine ⟨j - i, Nat.sub_ne_zero_of_lt hij, (σ ^ i).injective ?_⟩
  rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_of_le hij.le, ← hpow, ← hpow, heq]

end IsAlgebraic

namespace AlgEquiv

variable {R A : Type*} [CommRing R] [CommRing A] [IsDomain A] [Algebra R A] [FaithfulSMul R A]

/-- In a domain `A` faithful over `R`, an element moved by every positive power of an `R`-algebra
automorphism `σ : A ≃ₐ[R] A` is transcendental over `R`. -/
theorem transcendental_of_forall_pow_algEquiv_ne_self (σ : A ≃ₐ[R] A) {x : A}
    (h : ∀ n : ℕ, n ≠ 0 → (σ ^ n) x ≠ x) : Transcendental R x :=
  fun hx ↦ let ⟨n, hn0, hnx⟩ := hx.exists_pow_apply_eq_self_of_algEquiv σ; h n hn0 hnx

end AlgEquiv

namespace AlgHom

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Algebraic independence of eigenvectors with multiplicatively independent eigenvalues.**
Let `σ : A →ₐ[R] A` be an `R`-algebra endomorphism of a domain `A` faithful over `R`, and let
`y : ι → A` be nonzero elements satisfying `σ (y i) = algebraMap R A (u i) * y i`. If distinct
monomial exponent tuples `d : ι →₀ ℕ` produce distinct products `∏ i, u i ^ d i` in `R`, then `y`
is algebraically independent over `R`. -/
theorem algebraicIndependent_of_algHom_eigenvectors [IsDomain A] [FaithfulSMul R A]
    (σ : A →ₐ[R] A) {u : ι → R} {y : ι → A}
    (hy0 : ∀ i, y i ≠ 0) (hσ : ∀ i, σ (y i) = algebraMap R A (u i) * y i)
    (hu : Function.Injective fun d : ι →₀ ℕ ↦ d.prod fun i k ↦ u i ^ k) :
    AlgebraicIndependent R y := by
  classical
  have : IsDomain R := Function.Injective.isDomain _ (FaithfulSMul.algebraMap_injective R A)
  let f : Module.End R A := σ.toLinearMap
  let μ : (ι →₀ ℕ) → R := fun d ↦ d.prod fun i k ↦ u i ^ k
  let v : (ι →₀ ℕ) → A := fun d ↦ d.prod fun i k ↦ y i ^ k
  have heig (d : ι →₀ ℕ) : f.HasEigenvector (μ d) (v d) := by
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, ?_⟩
    · rw [AlgHom.toLinearMap_apply, Algebra.smul_def, map_finsuppProd, map_finsuppProd,
        ← Finsupp.prod_mul]
      exact Finsupp.prod_congr fun i _ ↦ by rw [map_pow, hσ, mul_pow, map_pow]
    · exact d.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (hy0 i)
  have hli : LinearIndependent R v := f.eigenvectors_linearIndependent' μ hu v heig
  rw [_root_.algebraicIndependent_iff]
  intro P hP
  have hsum : ∑ d ∈ P.support, P.coeff d • v d = 0 := by
    conv at hP => rw [P.as_sum]
    simpa only [map_sum, MvPolynomial.aeval_monomial, Algebra.smul_def, v] using hP
  ext d
  by_cases hd : d ∈ P.support
  · simpa using linearIndependent_iff'.1 hli P.support P.coeff hsum d hd
  · simpa using MvPolynomial.notMem_support_iff.1 hd

end AlgHom
