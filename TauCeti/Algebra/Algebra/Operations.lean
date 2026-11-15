/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Operations
import Mathlib.Tactic.Ring

/-!
# Powers of submodules of an algebra

Three facts about the powers of a submodule of an algebra.

Once the powers of a submodule `M` repeat once, `M ^ (n + 1) = M ^ n`, they are constant from `n`
on. This is `TauCeti.pow_eq_pow_of_pow_succ_eq_pow` for submodules, which Mathlib makes a monoid
only over a commutative base (`Submodule.idemSemiring`). Only the recursion
`M ^ (k + 1) = M ^ k * M` is used, so it holds without that assumption, in particular for left
ideals (`Ideal R`) of a noncommutative ring.

To bound `span R s ^ (t + 1)` by the span of a set `W t` of words (for instance the words left
irreducible by a rewriting system), it suffices that `s ⊆ span R (W 0)` and that each product
`b * c` of a word `b ∈ W t` with a generator `c ∈ s` lies in `span R (W (t + 1))`; the induction on
`t` is `Submodule.span_pow_succ_le_span_of_forall_mul_mem`.

For submodules `X` and `Y` of a commutative algebra, write `V = X ⊔ Y`. A product of `i + j + 1`
elements of `V` is a sum of products with at least `i + 1` factors from `X` or at least `j + 1`
factors from `Y`, so

  `V ^ (i + j + 1) ≤ X ^ (i + 1) * V ^ j ⊔ Y ^ (j + 1) * V ^ i`.

For `X = R ∙ x₀` and `Y = R ∙ x₁` this says that a form of degree `i + j + 1` in two variables is
`x₀ ^ (i + 1) * a + x₁ ^ (j + 1) * b` with `a` and `b` forms of degrees `j` and `i`, the input to
the computation of the cohomology of the twisting sheaves on the projective line. Mathlib's
`Ideal.sup_pow_add_le_pow_sup_pow` is the analogous bound for ideals, where the cofactors
`V ^ j` and `V ^ i` are absorbed.

## Main results

* `Submodule.pow_eq_pow_of_pow_succ_eq_pow`: `M ^ (n + 1) = M ^ n` propagates to all `k ≥ n`.
* `Submodule.span_pow_succ_le_span_of_forall_mul_mem`: `span R s ^ (t + 1) ≤ span R (W t)` if
  `s ⊆ span R (W 0)` and right multiplication by `s` maps each `W t` into `span R (W (t + 1))`.
* `Submodule.sup_pow_add_add_one_le`: `(X ⊔ Y) ^ (i + j + 1)` is contained in
  `X ^ (i + 1) * (X ⊔ Y) ^ j ⊔ Y ^ (j + 1) * (X ⊔ Y) ^ i`.
-/

public section

namespace Submodule

section Semiring

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A] [IsScalarTower R A A]

/-- Once the powers of a submodule repeat once, they are constant from that point on.

Over a commutative base this is `TauCeti.pow_eq_pow_of_pow_succ_eq_pow`; here neither `R` nor
`A` need be commutative. -/
theorem pow_eq_pow_of_pow_succ_eq_pow {M : Submodule R A} {n : ℕ} (h : M ^ (n + 1) = M ^ n)
    {k : ℕ} (hk : n ≤ k) : M ^ k = M ^ n := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [Submodule.pow_succ, ih, ← Submodule.pow_succ, h]

end Semiring

section Algebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- **Bounding powers of a span by words.** Let `W t` be sets of words with
`s ⊆ span R (W 0)`, such that each product of a word in `W t` with an element of `s` is an
`R`-linear combination of words in `W (t + 1)`. Then every product of `t + 1` elements of
`span R s` is an `R`-linear combination of words in `W t`. -/
theorem span_pow_succ_le_span_of_forall_mul_mem {s : Set A} {W : ℕ → Set A}
    (h₀ : s ⊆ span R (W 0)) (hS : ∀ t, ∀ b ∈ W t, ∀ c ∈ s, b * c ∈ span R (W (t + 1)))
    (t : ℕ) : span R s ^ (t + 1) ≤ span R (W t) := by
  induction t with
  | zero => rwa [pow_one, span_le]
  | succ t ih =>
    rw [pow_succ]
    refine (mul_le_mul' ih le_rfl).trans ?_
    rw [span_mul_span, span_le]
    rintro _ ⟨b, hb, c, hc, rfl⟩
    exact hS t b hb c hc

end Algebra

section CommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The case `i = 0` of `Submodule.sup_pow_add_add_one_le`. -/
private theorem sup_pow_succ_le_mul_sup_pow_mul_sup (X Y : Submodule R A) (j : ℕ) :
    (X ⊔ Y) ^ (j + 1) ≤ X * (X ⊔ Y) ^ j ⊔ Y ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', sup_mul]
    refine sup_le le_sup_left ?_
    calc Y * (X ⊔ Y) ^ (j + 1) ≤ Y * (X * (X ⊔ Y) ^ j ⊔ Y ^ (j + 1)) := by gcongr
      _ = X * (Y * (X ⊔ Y) ^ j) ⊔ Y ^ (j + 1 + 1) := by
        simp only [← add_eq_sup]; ring
      _ ≤ X * (X ⊔ Y) ^ (j + 1) ⊔ Y ^ (j + 1 + 1) := by
        rw [pow_succ' _ j]; gcongr; exact le_sup_right

/-- **Powers of a sum of two submodules.** A product of `i + j + 1` elements of `X ⊔ Y` has at
least `i + 1` factors from `X` or at least `j + 1` factors from `Y`:
`(X ⊔ Y) ^ (i + j + 1) ≤ X ^ (i + 1) * (X ⊔ Y) ^ j ⊔ Y ^ (j + 1) * (X ⊔ Y) ^ i`. -/
theorem sup_pow_add_add_one_le (X Y : Submodule R A) (i j : ℕ) :
    (X ⊔ Y) ^ (i + j + 1) ≤ X ^ (i + 1) * (X ⊔ Y) ^ j ⊔ Y ^ (j + 1) * (X ⊔ Y) ^ i := by
  induction i generalizing j with
  | zero => simpa using sup_pow_succ_le_mul_sup_pow_mul_sup X Y j
  | succ i ih =>
    induction j with
    | zero =>
      simpa [sup_comm, add_comm] using sup_pow_succ_le_mul_sup_pow_mul_sup Y X (i + 1)
    | succ j ihj =>
      -- split off one factor of `X ⊔ Y`: its `X`-part uses the bound for `(i, j + 1)`, its
      -- `Y`-part the bound for `(i + 1, j)`
      rw [show i + 1 + (j + 1) + 1 = (i + (j + 1) + 1) + 1 by omega, pow_succ', sup_mul]
      apply sup_le
      · calc X * (X ⊔ Y) ^ (i + (j + 1) + 1)
            ≤ X * (X ^ (i + 1) * (X ⊔ Y) ^ (j + 1) ⊔ Y ^ (j + 1 + 1) * (X ⊔ Y) ^ i) := by
              gcongr; exact ih (j + 1)
          _ = X ^ (i + 1 + 1) * (X ⊔ Y) ^ (j + 1) ⊔ Y ^ (j + 1 + 1) * (X * (X ⊔ Y) ^ i) := by
              simp only [← add_eq_sup]; ring
          _ ≤ X ^ (i + 1 + 1) * (X ⊔ Y) ^ (j + 1) ⊔ Y ^ (j + 1 + 1) * (X ⊔ Y) ^ (i + 1) := by
              rw [pow_succ' _ i]; gcongr; exact le_sup_left
      · calc Y * (X ⊔ Y) ^ (i + (j + 1) + 1)
            = Y * (X ⊔ Y) ^ (i + 1 + j + 1) := by rw [show i + (j + 1) = i + 1 + j by omega]
          _ ≤ Y * (X ^ (i + 1 + 1) * (X ⊔ Y) ^ j ⊔ Y ^ (j + 1) * (X ⊔ Y) ^ (i + 1)) := by
              gcongr
          _ = X ^ (i + 1 + 1) * (Y * (X ⊔ Y) ^ j) ⊔ Y ^ (j + 1 + 1) * (X ⊔ Y) ^ (i + 1) := by
              simp only [← add_eq_sup]; ring
          _ ≤ X ^ (i + 1 + 1) * (X ⊔ Y) ^ (j + 1) ⊔ Y ^ (j + 1 + 1) * (X ⊔ Y) ^ (i + 1) := by
              rw [pow_succ' _ j]; gcongr; exact le_sup_right

end CommSemiring

end Submodule
