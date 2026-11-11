/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.Ultra
public import Mathlib.Analysis.Normed.Ring.Finite
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Distances from roots of unity to one

In an ultrametric normed field, primitive roots of the same order have the same distance
from one. Factoring the cyclotomic polynomial at one therefore computes a power of that
distance. In prime order `p`, this gives `‖ζ - 1‖ ^ (p - 1) = ‖p‖`, the identity used to
compute the radius of cyclotomic translations in p-adic analysis.

The factorization and the enumeration of primitive roots are Mathlib's
`Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots` and
`IsPrimitiveRoot.card_primitiveRoots`.
-/

public section

namespace IsPrimitiveRoot

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {n : ℕ} [NeZero n] {ζ ξ : K}

/-- Primitive roots of the same nonzero order have equal distance from one in an
ultrametric normed field. -/
theorem norm_sub_one_eq (hζ : IsPrimitiveRoot ζ n) (hξ : IsPrimitiveRoot ξ n) :
    ‖ζ - 1‖ = ‖ξ - 1‖ := by
  have hle {a b : K} (ha : IsPrimitiveRoot a n) (hb : IsPrimitiveRoot b n) :
      ‖b - 1‖ ≤ ‖a - 1‖ := by
    obtain ⟨i, _, rfl⟩ := ha.eq_pow_of_pow_eq_one hb.pow_eq_one
    have hnorm := (ha.isOfFinOrder (NeZero.ne n)).norm_eq_one
    simpa using TauCeti.norm_prod_sub_prod_le (s := Finset.range i)
      (f := fun _ => a) (g := fun _ => (1 : K)) (by norm_num : (0 : ℝ) ≤ 1)
      (norm_nonneg (a - 1)) (by simp [hnorm]) (by simp) (by simp)
  exact le_antisymm (hle hξ hζ) (hle hζ hξ)

/-- Evaluating the cyclotomic polynomial at one computes a power of the distance from
a primitive root to one. -/
theorem norm_sub_one_pow_totient (hζ : IsPrimitiveRoot ζ n) :
    ‖ζ - 1‖ ^ n.totient = ‖(Polynomial.cyclotomic n K).eval 1‖ := by
  classical
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
    Polynomial.eval_prod, norm_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  calc
    ‖ζ - 1‖ ^ n.totient = ∏ _ ∈ primitiveRoots n K, ‖ζ - 1‖ := by
      rw [Finset.prod_const, hζ.card_primitiveRoots]
    _ = ∏ ξ ∈ primitiveRoots n K, ‖1 - ξ‖ := by
      apply Finset.prod_congr rfl
      intro ξ hξ
      exact (hζ.norm_sub_one_eq ((mem_primitiveRoots (NeZero.pos n)).mp hξ)).trans
        (norm_sub_rev ξ 1)

/-- In prime order, the `(p - 1)`st power of the distance from a primitive root to one
is the norm of `p`. This includes order two and requires no completeness hypothesis. -/
theorem norm_sub_one_pow_prime_sub_one {p : ℕ} [Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ p) : ‖ζ - 1‖ ^ (p - 1) = ‖(p : K)‖ := by
  simpa [Nat.totient_prime (Fact.out : p.Prime), Polynomial.eval_one_cyclotomic_prime]
    using hζ.norm_sub_one_pow_totient

end IsPrimitiveRoot
