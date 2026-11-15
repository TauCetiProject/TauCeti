/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Module.Rat
public import TauCeti.RingTheory.DividedPowers.Associative

/-!
# Primitive elements in a bialgebra

This file records integral-coefficient formulas for the comultiplication of powers, divided
powers, and binomial coefficients of a primitive element. The two tensor factors commute even
when the bialgebra itself is noncommutative. It also computes the counit of the latter two
families when the underlying element has counit zero.

A nonzero square-zero primitive element in a bialgebra over a field forces
characteristic two. Thus a square-zero differential cannot be modeled by an
ordinary primitive Hopf-algebra generator in other characteristics: its tensor
product differential needs a sign, rather than the ordinary tensor multiplication.
Neither an antipode nor finite dimensionality is needed for the obstruction.
The calculation uses `TauCeti.Bialgebra.comul_pow_of_primitive`: the two mixed
terms in the coproduct of the square are both `d ⊗ d`. A linear functional
taking value one on `d` detects their sum without a choice of basis.

## Main results

* `TauCeti.Bialgebra.comul_pow_of_primitive`: the comultiplication of a power of a primitive
  element is its binomial expansion.
* `TauCeti.Bialgebra.comul_dividedPower_of_primitive`: the comultiplication of a divided power
  has coefficient one on every antidiagonal term.
* `TauCeti.Bialgebra.comul_choose_of_primitive`: the comultiplication of a binomial coefficient
  has the same coefficient-one formula.
* `Bialgebra.IsPrimitiveElem.two_eq_zero_of_sq_eq_zero`: a nonzero square-zero primitive
  element forces characteristic two.
* `Bialgebra.IsPrimitiveElem.eq_zero_of_sq_eq_zero`: outside characteristic two, every
  square-zero primitive element is zero.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity:
  the first steps*, §1, for the characteristic-two square-zero Hopf algebra
  and its relation to complexes.
-/

public section

open scoped TensorProduct

namespace TauCeti.Bialgebra

universe u w

/-- The comultiplication of a power of a primitive element is its binomial expansion. -/
theorem comul_pow_of_primitive
    {R : Type u} {A : Type w} [CommSemiring R] [Semiring A] [Bialgebra R A]
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a) (n : ℕ) :
    (Coalgebra.comul (R := R)) (a ^ n) =
      ∑ mn ∈ Finset.antidiagonal n, n.choose mn.1 •
        ((a ^ mn.1) ⊗ₜ[R] (a ^ mn.2)) := by
  rw [Bialgebra.comul_pow, h]
  have hcomm : Commute (a ⊗ₜ[R] 1) (1 ⊗ₜ[R] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [hcomm.add_pow']
  simp only [Algebra.TensorProduct.tmul_pow, one_pow,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end TauCeti.Bialgebra

namespace Bialgebra.IsPrimitiveElem

variable {k A : Type*} [Field k] [Ring A] [Bialgebra k A] {d : A}

/-- A nonzero square-zero primitive element forces characteristic two. -/
theorem two_eq_zero_of_sq_eq_zero (hd : Bialgebra.IsPrimitiveElem k d)
    (hd0 : d ≠ 0) (hsq : d ^ 2 = 0) : (2 : k) = 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hd0
  have hΔ := TauCeti.Bialgebra.comul_pow_of_primitive d
    (by simpa only [add_comm] using hd.comul_eq_tmul_add_tmul) 2
  have h := congrArg (fun t : A ⊗[k] A =>
    TensorProduct.lid k k (TensorProduct.map f f t)) hΔ
  simpa [hsq, Finset.Nat.antidiagonal_succ, ← Nat.cast_smul_eq_nsmul k, hf] using h.symm

/-- Outside characteristic two a square-zero primitive element is zero.
In particular, the usual square-zero differential generator cannot be primitive
in an ordinary Hopf algebra over such a field. -/
theorem eq_zero_of_sq_eq_zero (hd : Bialgebra.IsPrimitiveElem k d)
    (h2 : (2 : k) ≠ 0) (hsq : d ^ 2 = 0) : d = 0 := by
  by_contra hd0
  exact h2 (hd.two_eq_zero_of_sq_eq_zero hd0 hsq)

end Bialgebra.IsPrimitiveElem

namespace TauCeti.Bialgebra

attribute [local instance] TauCeti.moduleNNRat

section DividedPower

variable {A : Type w} [Semiring A] [Bialgebra ℚ A]

/-- The comultiplication of a divided power of a primitive element has integral structure
constants:
`Δ(a⁽ⁿ⁾) = ∑ i+j=n, a⁽ⁱ⁾ ⊗ a⁽ʲ⁾`.

This is the formula used for the divided-power generators of a Kostant integral form. -/
theorem comul_dividedPower_of_primitive
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] a) (n : ℕ) :
    (Coalgebra.comul (R := ℚ)) (Associative.dividedPower n a) =
      ∑ ij ∈ Finset.antidiagonal n,
        Associative.dividedPower ij.1 a ⊗ₜ[ℚ] Associative.dividedPower ij.2 a := by
  rw [← Bialgebra.comulAlgHom_apply, Associative.map_dividedPower,
    Bialgebra.comulAlgHom_apply, h]
  have hcomm : Commute (a ⊗ₜ[ℚ] 1) (1 ⊗ₜ[ℚ] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [Associative.dividedPower_add hcomm]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← Algebra.TensorProduct.includeLeft_apply (S := ℚ) a,
    ← Algebra.TensorProduct.includeRight_apply (R := ℚ) (A := A) a]
  rw [← Associative.map_dividedPower
      (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] A),
    ← Associative.map_dividedPower
      (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] A ⊗[ℚ] A)]
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- A counit that kills an element also kills all its positive divided powers. -/
theorem counit_dividedPower_of_counit_eq_zero
    (a : A) (h : Coalgebra.counit (R := ℚ) a = 0) (n : ℕ) :
    (Coalgebra.counit (R := ℚ)) (Associative.dividedPower (n + 1) a) = 0 := by
  rw [← Bialgebra.counitAlgHom_apply, Associative.map_dividedPower,
    Bialgebra.counitAlgHom_apply, h]
  exact Associative.dividedPower_eval_zero (Nat.succ_ne_zero n)

end DividedPower

section Choose

variable {A : Type w} [Ring A] [Bialgebra ℚ A]

/-- The comultiplication of a binomial coefficient in a primitive element has integral
structure constants:
`Δ((a choose n)) = ∑ i+j=n, (a choose i) ⊗ (a choose j)`.

This is the formula used for the Cartan generators of a Kostant integral form. -/
theorem comul_choose_of_primitive
    (a : A) (h : Coalgebra.comul a = a ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] a) (n : ℕ) :
    (Coalgebra.comul (R := ℚ)) (Ring.choose a n) =
      ∑ ij ∈ Finset.antidiagonal n,
        Ring.choose a ij.1 ⊗ₜ[ℚ] Ring.choose a ij.2 := by
  rw [← Bialgebra.comulAlgHom_apply, Ring.map_choose, Bialgebra.comulAlgHom_apply, h]
  have hcomm : Commute (a ⊗ₜ[ℚ] 1) (1 ⊗ₜ[ℚ] a) :=
    (Commute.one_right _).tmul (Commute.one_left _)
  rw [Ring.add_choose_eq n hcomm]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← Algebra.TensorProduct.includeLeft_apply (S := ℚ) a,
    ← Algebra.TensorProduct.includeRight_apply (R := ℚ) (A := A) a]
  rw [← Ring.map_choose
      (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ] A ⊗[ℚ] A),
    ← Ring.map_choose
      (Algebra.TensorProduct.includeRight : A →ₐ[ℚ] A ⊗[ℚ] A)]
  simp only [Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- A counit that kills an element also kills all its positive binomial coefficients. -/
theorem counit_choose_of_counit_eq_zero
    (a : A) (h : Coalgebra.counit (R := ℚ) a = 0) (n : ℕ) :
    (Coalgebra.counit (R := ℚ)) (Ring.choose a (n + 1)) = 0 := by
  rw [← Bialgebra.counitAlgHom_apply, Ring.map_choose, Bialgebra.counitAlgHom_apply, h]
  exact Ring.choose_zero_succ ℚ n

end Choose

end TauCeti.Bialgebra
