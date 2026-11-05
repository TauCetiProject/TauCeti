/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The symmetric homogeneous polynomials of a fixed degree

The symmetric polynomials of `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs` are graded by total
degree, each graded piece being the intersection of `MvPolynomial.symmetricSubalgebra` with the
homogeneous polynomials `MvPolynomial.homogeneousSubmodule` of that degree.  This file names that
intersection, `TauCeti.symmetricHomogeneousSubmodule`; it is the module the classical families of
symmetric polynomials are bases of, one degree at a time: the monomial symmetric polynomials over
any commutative semiring, and the Schur polynomials over a commutative ring.  Under the fundamental
theorem of symmetric polynomials (`MvPolynomial.esymmAlgEquiv`), a symmetric polynomial homogeneous
of degree `m` corresponds to a polynomial in `e₁, …, eₙ` that is weighted homogeneous of weight `m`
for the weights `i ↦ i + 1`.

## Main definitions

* `TauCeti.symmetricHomogeneousSubmodule σ R n`: the polynomials in `σ` over `R` that are both
  symmetric and homogeneous of degree `n`.

## Main results

* `TauCeti.prod_map_mem_symmetricHomogeneousSubmodule`: a multiset product of symmetric
  homogeneous factors has degree the sum of their degrees.

* `MvPolynomial.isHomogeneous_esymm`: the elementary symmetric polynomial `eₖ` is homogeneous of
  degree `k`.
* `MvPolynomial.isHomogeneous_hsymm`: the complete homogeneous symmetric polynomial `hₖ` is
  homogeneous of degree `k`.
* `MvPolynomial.isWeightedHomogeneous_esymmAlgEquiv_symm`: the expression of a degree-`m`
  homogeneous symmetric polynomial in `e₁, …, eₙ` is weighted homogeneous of weight `m` for weights
  `i ↦ i + 1`.
-/

public section

namespace TauCeti

open MvPolynomial

variable (σ : Type*) (R : Type*) [CommSemiring R] (n : ℕ)

/-- **The symmetric polynomials of degree `n`**: those polynomials in the alphabet `σ` over `R`
that are both symmetric and homogeneous of degree `n`.  The monomial symmetric polynomials of the
partitions of `n` are a basis of this module over any commutative semiring; the Schur polynomials
of those partitions are a basis of it over a commutative ring. -/
noncomputable def symmetricHomogeneousSubmodule : Submodule R (MvPolynomial σ R) :=
  (symmetricSubalgebra σ R).toSubmodule ⊓ homogeneousSubmodule σ R n

variable {σ R n}

/-- Membership in `TauCeti.symmetricHomogeneousSubmodule` is the conjunction of the two
conditions defining it. -/
@[simp]
theorem mem_symmetricHomogeneousSubmodule {p : MvPolynomial σ R} :
    p ∈ symmetricHomogeneousSubmodule σ R n ↔ p.IsSymmetric ∧ p.IsHomogeneous n :=
  Iff.rfl

/-- A multiset product of symmetric polynomials, with the factor indexed by `k` homogeneous
of degree `k`, is symmetric and homogeneous of degree the sum of the indices. -/
theorem prod_map_mem_symmetricHomogeneousSubmodule (f : ℕ → MvPolynomial σ R)
    (hf : ∀ k, f k ∈ symmetricHomogeneousSubmodule σ R k) (s : Multiset ℕ) :
    (s.map f).prod ∈ symmetricHomogeneousSubmodule σ R s.sum := by
  apply mem_symmetricHomogeneousSubmodule.mpr
  induction s using Multiset.induction_on with
  | empty => exact ⟨IsSymmetric.one, isHomogeneous_one σ R⟩
  | cons k s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have hk := mem_symmetricHomogeneousSubmodule.mp (hf k)
    exact ⟨hk.1.mul ih.1, hk.2.mul ih.2⟩

end TauCeti

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The elementary symmetric polynomial `eₖ` is homogeneous of degree `k`. -/
theorem isHomogeneous_esymm [Fintype σ] (k : ℕ) : (esymm σ R k).IsHomogeneous k := by
  rw [esymm_eq_sum_subtype]
  refine IsHomogeneous.sum _ _ _ fun t _ => ?_
  have h := IsHomogeneous.prod (t : Finset σ) (fun i => (X i : MvPolynomial σ R)) (fun _ => 1)
    fun i _ => isHomogeneous_X R i
  rwa [Finset.sum_const, smul_eq_mul, mul_one, t.2] at h

/-- The complete homogeneous symmetric polynomial `hₖ` is homogeneous of degree `k`. -/
theorem isHomogeneous_hsymm [Fintype σ] [DecidableEq σ] (k : ℕ) :
    (hsymm σ R k).IsHomogeneous k := by
  have h (t : Multiset σ) : ((t.map X).prod : MvPolynomial σ R).IsHomogeneous t.card := by
    induction t using Multiset.induction_on with
    | empty => simpa using isHomogeneous_one σ R
    | cons a t ih => simpa [add_comm] using (isHomogeneous_X R a).mul ih
  exact IsHomogeneous.sum _ _ _ fun s _ => by simpa [s.2] using h s.1

/-- If `p ∈ symmetricSubalgebra σ R` is homogeneous of degree `m`, then its unique expression in the
elementary symmetric polynomials `e₁, …, eₙ` (`n = Fintype.card σ`) is weighted homogeneous of
weight `m` for the weights `i ↦ i + 1`. -/
theorem isWeightedHomogeneous_esymmAlgEquiv_symm {σ R : Type*} [Fintype σ] [CommRing R] {n : ℕ}
    (hn : Fintype.card σ = n) {p : symmetricSubalgebra σ R} {m : ℕ}
    (hp : (p : MvPolynomial σ R).IsHomogeneous m) :
    ((esymmAlgEquiv σ R hn).symm p).IsWeightedHomogeneous (fun i : Fin n ↦ (i : ℕ) + 1) m := by
  have hinj : Function.Injective
      (aeval (R := R) fun i : Fin n ↦ esymm σ R ((i : ℕ) + 1)) := by
    intro q₁ q₂ hq
    exact esymmAlgHom_injective R hn.ge (Subtype.ext (by simpa [esymmAlgHom_apply] using hq))
  refine isWeightedHomogeneous_of_isHomogeneous_aeval
    (fun i : Fin n ↦ isHomogeneous_esymm (σ := σ) (R := R) ((i : ℕ) + 1)) hinj ?_
  have happly : aeval (fun i : Fin n ↦ esymm σ R ((i : ℕ) + 1))
      ((esymmAlgEquiv σ R hn).symm p) = (p : MvPolynomial σ R) := by
    rw [← esymmAlgHom_apply, ← esymmAlgEquiv_apply σ R hn, AlgEquiv.apply_symm_apply]
  rwa [happly]

end MvPolynomial
