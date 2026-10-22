/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Basic properties of derivations

A derivation vanishes on the image `(n : A)` of a natural number (`Derivation.map_natCast`). A
numeric literal `(OfNat.ofNat n : A)` with `2 ≤ n` is not syntactically such a cast, so `simp`
does not apply that lemma to it. This file adds the literal form `Derivation.map_ofNat`, so that
`simp` differentiates polynomial expressions with numeric coefficients, for instance partial
derivatives `MvPolynomial.pderiv i (3 * X 0 ^ 2)`.

Iterates of a derivation remain linear over the scalars, so they commute with finite scalar
linear combinations. On products they satisfy the general Leibniz rule
`Dⁿ (a * b) = ∑ (n choose i) Dⁱ a Dⁿ⁻ⁱ b`.

## Main results

* `Derivation.map_ofNat`: a derivation vanishes on numeric literals.
* `Derivation.iterate_sum_smul`: iterated differentiation commutes with scalar linear combinations.
* `Derivation.iterate_apply_mul`: the general Leibniz rule for iterates of a derivation.
-/

public section

namespace Derivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A]
  [Module A M] [Module R M] (D : Derivation R A M)

/-- A derivation vanishes on numeric literals. -/
@[simp]
theorem map_ofNat (n : ℕ) [n.AtLeastTwo] : D (no_index (OfNat.ofNat n : A)) = 0 := by
  rw [← Nat.cast_ofNat, map_natCast]

/-- Iterated differentiation commutes with finite scalar linear combinations. -/
theorem iterate_sum_smul {ι : Type*} (D : Derivation R A A) (m : ℕ) (s : Finset ι)
    (c : ι → R) (f : ι → A) :
    (D : A → A)^[m] (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • (D : A → A)^[m] (f i) := by
  simpa only [LinearMap.map_smul, Module.End.pow_apply, coeFn_coe] using
    map_sum (D.toLinearMap ^ m) (fun i ↦ c i • f i) s

/-- **General Leibniz rule** for iterates of a derivation of a commutative algebra.

The statement and proof are adapted from Mathlib's `LieDerivation.iterate_apply_lie`
(`Mathlib/Algebra/Lie/Derivation/Basic.lean`). -/
theorem iterate_apply_mul (D : Derivation R A A) (n : ℕ) (a b : A) :
    D^[n] (a * b) =
      ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul (M := A) (fun i j => D^[i] a * D^[j] b) n]
    simp only [Function.iterate_succ_apply', ih, map_sum, map_nsmul, leibniz, smul_eq_mul,
      nsmul_add, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [n.choose_symm_of_eq_add (Finset.mem_antidiagonal.1 hij).symm, mul_comm]

end Derivation
