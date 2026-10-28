/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The homogeneous components of an `ℕ`-graded ring as a polynomial

Let `A` be a ring graded by `𝒜 : ℕ → σ`. Recording the homogeneous components `aₙ` of `a ∈ A` as
the coefficients of a polynomial gives a ring homomorphism

  `A →+* A[X]`, `a ↦ ∑ₙ aₙ Xⁿ`.

An element `a` is homogeneous of degree `n` exactly when it is sent to the monomial `a Xⁿ`. This
turns homogeneity into an equation in a ring, so that it can be transported along constructions
which commute with ring homomorphisms. Under it, a family of elements `a_d` with `a_d ∈ 𝒜 (w d)`
becomes the family `a_d X^(w d)`: the grading is the action of a polynomial variable.

## Main definitions

* `TauCeti.GradedAlgebra.toPolynomial`: the ring homomorphism `a ↦ ∑ₙ aₙ Xⁿ`.

## Main results

* `TauCeti.GradedAlgebra.coeff_toPolynomial`: the coefficient of `Xⁿ` is the component of
  degree `n`.
* `TauCeti.GradedAlgebra.toPolynomial_eq_monomial_iff`: `a` is sent to `a Xⁿ` exactly when `a` is
  homogeneous of degree `n`.
-/

public section

noncomputable section

namespace TauCeti.GradedAlgebra

open DirectSum Polynomial

variable {A σ : Type*} [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ℕ → σ)
  [GradedRing 𝒜]

/-- The ring homomorphism `A →+* A[X]` sending an element `a` of an `ℕ`-graded ring to the
polynomial `∑ₙ aₙ Xⁿ` whose coefficients are its homogeneous components. -/
def toPolynomial : A →+* A[X] where
  toFun a := toSemiring (fun n ↦ (monomial n).toAddMonoidHom.comp (AddSubmonoidClass.subtype (𝒜 n)))
    (by simp) (fun ai aj ↦ by simp [monomial_mul_monomial]) (decompose 𝒜 a)
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp

variable {𝒜}

/-- A homogeneous element `a` of degree `n` is sent to the monomial `a Xⁿ`. -/
theorem toPolynomial_of_mem {a : A} {n : ℕ} (ha : a ∈ 𝒜 n) : toPolynomial 𝒜 a = monomial n a := by
  simp only [toPolynomial, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, decompose_of_mem 𝒜 ha]
  exact toSemiring_of (A := fun i ↦ 𝒜 i) _ _ _ n ⟨a, ha⟩

variable (𝒜)

/-- The coefficient of `Xⁿ` in the image of `a` is the homogeneous component of `a` of degree
`n`. -/
@[simp]
theorem coeff_toPolynomial (a : A) (n : ℕ) : (toPolynomial 𝒜 a).coeff n = decompose 𝒜 a n := by
  induction a using Decomposition.inductionOn 𝒜 with
  | zero => simp
  | @homogeneous i a =>
    obtain ⟨a, ha⟩ := a
    rw [toPolynomial_of_mem ha, coeff_monomial]
    split_ifs with h
    · subst h
      rw [decompose_of_mem_same 𝒜 ha]
    · rw [decompose_of_mem_ne 𝒜 ha h]
  | add a b ha hb => simp [ha, hb]

variable {𝒜}

/-- **Homogeneity as an equation**: `a` is sent to the monomial `a Xⁿ` exactly when it is
homogeneous of degree `n`. -/
theorem toPolynomial_eq_monomial_iff {a : A} {n : ℕ} :
    toPolynomial 𝒜 a = monomial n a ↔ a ∈ 𝒜 n := by
  refine ⟨fun h ↦ ?_, toPolynomial_of_mem⟩
  have := congrArg (coeff · n) h
  simp only [coeff_toPolynomial, coeff_monomial_same] at this
  exact this ▸ SetLike.coe_mem _

end TauCeti.GradedAlgebra
