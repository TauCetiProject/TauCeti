/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.Module.Basic

/-!
# Varying and permuting the factors of a list product in a ring

In an `R`-algebra `A`, the product of a list is affine in each factor. In particular, shifting one
factor `a` by the scalar `algebraMap R A c` changes the product by `c` times the product of the
list with that factor deleted. This is the step that centres one letter of a word at a time.

A map `δ` of a possibly noncommutative, nonassociative semiring with cancellative addition
obeying the Leibniz rule `δ (a * b) = δ a * b + a * δ b` sends an ordered product
`f 0 * ⋯ * f (n - 1)`, bracketed to the right, to the sum, over the positions `k`, of the same
product with the factor `f k` replaced by `δ (f k)`. The rule covers both a derivation of a
commutative ring and the inner derivation `⁅a, -⁆` of an associative ring, which is how the
commutator with a Lie generator acts on a word in a universal enveloping algebra.

A ring homomorphism sending each scalar `c i • 1` to `d i • 1` carries the ordered product
`(M₀ - c₀ • 1) ⋯ (M_{m-1} - c_{m-1} • 1)` to the ordered product of the images, as for a change
of coefficients of matrices.

If the factors of an ordered product `x 0 * ⋯ * x (n - 1)` pairwise anticommute, permuting them
multiplies the product by the sign of the permutation. The factors need not square to zero, so this
covers graded-commutative rings such as Milnor K-theory, where a product with a repeated factor can
be nonzero.

## Main results

* `List.prod_append_sub_algebraMap_cons`:
  `(l₁ ++ (a - algebraMap R A c) :: l₂).prod = (l₁ ++ a :: l₂).prod - c • (l₁ ++ l₂).prod`.
* `TauCeti.map_prod_ofFn_of_leibniz`: the Leibniz rule for an ordered product of `n` factors.
* `TauCeti.map_list_prod_ofFn_sub_smul_one`: a ring homomorphism sending each `c i • 1` to
  `d i • 1` maps `∏ (M i - c i • 1)` to `∏ (φ (M i) - d i • 1)`, in order.
* `List.prod_ofFn_comp_swap_castSucc_succ`: interchanging two neighbouring anticommuting factors
  negates the product.
* `List.prod_ofFn_comp_perm`: for pairwise anticommuting factors,
  `(ofFn (x ∘ σ)).prod = sign σ • (ofFn x).prod`.
-/

public section

namespace List

section Algebra

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Shifting the factor `a` of the product of `l₁ ++ a :: l₂` by the scalar `algebraMap R A c`
subtracts `c` times the product of `l₁ ++ l₂`. -/
theorem prod_append_sub_algebraMap_cons (l₁ l₂ : List A) (a : A) (c : R) :
    (l₁ ++ (a - algebraMap R A c) :: l₂).prod = (l₁ ++ a :: l₂).prod - c • (l₁ ++ l₂).prod := by
  simp only [prod_append, prod_cons, sub_mul, mul_sub, Algebra.smul_def, Algebra.left_comm _ c]

end Algebra

section Anticommute

variable {A : Type*} [Ring A]

/-- Interchanging two neighbouring factors that anticommute negates the ordered product of a
tuple in a ring. -/
theorem prod_ofFn_comp_swap_castSucc_succ {n : ℕ} (x : Fin (n + 1) → A) (i : Fin n)
    (hx : x i.castSucc * x i.succ = -(x i.succ * x i.castSucc)) :
    (ofFn (x ∘ Equiv.swap i.castSucc i.succ)).prod = -(ofFn x).prod := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      have hk (k : Fin n) : Equiv.swap (0 : Fin (n + 2)) (Fin.succ 0) k.succ.succ = k.succ.succ :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) ((Fin.succ_injective _).ne
          (Fin.succ_ne_zero _))
      simp only [Fin.castSucc_zero, ofFn_succ, prod_cons, Function.comp_apply, hk,
        Equiv.swap_apply_left, Equiv.swap_apply_right, ← mul_assoc] at hx ⊢
      rw [hx, neg_mul, neg_neg]
    | succ j =>
      rw [← Fin.succ_castSucc] at hx ⊢
      rw [ofFn_succ, ofFn_succ (f := x), prod_cons, prod_cons, ← mul_neg,
        ← ih (fun k ↦ x k.succ) j hx]
      simp only [Function.comp_def,
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm,
        (Fin.succ_injective _).swap_apply]

/-- **Permuting anticommuting factors.** If the members of a tuple `x` in a ring pairwise
anticommute, then permuting the factors of the ordered product `x 0 * ⋯ * x (n - 1)` multiplies it
by the sign of the permutation. Equal members are not required to square to zero: the hypothesis
`x i * x j = -(x j * x i)` is only imposed for distinct indices `i ≠ j`. -/
theorem prod_ofFn_comp_perm {n : ℕ} {x : Fin n → A}
    (hx : ∀ i j, i ≠ j → x i * x j = -(x j * x i)) (σ : Equiv.Perm (Fin n)) :
    (ofFn (x ∘ σ)).prod = Equiv.Perm.sign σ • (ofFn x).prod := by
  cases n with
  | zero => simp [Subsingleton.elim σ 1]
  | succ n =>
    have hσ := (Equiv.Perm.mclosure_swap_castSucc_succ n).ge (Submonoid.mem_top σ)
    induction hσ using Submonoid.closure_induction generalizing x with
    | mem _ h =>
      obtain ⟨i, rfl⟩ := h
      rw [prod_ofFn_comp_swap_castSucc_succ x i (hx _ _ (Fin.castSucc_lt_succ (i := i)).ne),
        Equiv.Perm.sign_swap (Fin.castSucc_lt_succ (i := i)).ne, Units.neg_smul, one_smul]
    | one => simp
    | mul σ τ _ _ hσ hτ =>
      have hxσ : ∀ i j, i ≠ j → (x ∘ σ) i * (x ∘ σ) j = -((x ∘ σ) j * (x ∘ σ) i) :=
        fun i j hij ↦ hx _ _ (σ.injective.ne hij)
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hτ hxσ, hσ hx, Equiv.Perm.sign_mul,
        mul_comm, mul_smul]

end Anticommute

end List

namespace TauCeti

variable {A : Type*} [NonAssocSemiring A] [IsLeftCancelAdd A]

/-- **The Leibniz rule for an ordered product.** On a semiring `A` with cancellative addition, a
map `δ` with `δ (a * b) = δ a * b + a * δ b` sends the product `f 0 * (f 1 * ⋯ * f (n - 1))`,
bracketed to the right as `List.prod` does, to the sum over `k` of the same product with its
`k`-th factor replaced by `δ (f k)`. For `n = 0` this says `δ 1 = 0`. The semiring need be neither
commutative nor associative, and `δ` need not be additive. -/
theorem map_prod_ofFn_of_leibniz (δ : A → A) (hδ : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    {n : ℕ} (f : Fin n → A) :
    δ (List.ofFn f).prod = ∑ k, (List.ofFn (Function.update f k (δ (f k)))).prod := by
  induction n with
  | zero => simpa using hδ 1 1
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, hδ, ih, Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · simp only [List.ofFn_succ, List.prod_cons, Function.update_self,
        Function.update_of_ne (Fin.succ_ne_zero _)]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [List.ofFn_succ, List.prod_cons, Function.update_of_ne (Fin.succ_ne_zero k).symm]
      congr 3
      funext i
      simp only [Function.update_apply, Fin.succ_inj]

/-- A ring homomorphism `φ` sending each `c i • 1` to `d i • 1` sends the ordered product
`(M₀ - c₀ • 1) * ⋯ * (M_{m-1} - c_{m-1} • 1)` to
`(φ M₀ - d₀ • 1) * ⋯ * (φ M_{m-1} - d_{m-1} • 1)`. -/
theorem map_list_prod_ofFn_sub_smul_one {R S B C Φ : Type*} [Ring R] [Ring S] [SMul B R]
    [SMul C S] [FunLike Φ R S] [RingHomClass Φ R S] (φ : Φ) {m : ℕ} (M : Fin m → R)
    {c : Fin m → B} {d : Fin m → C} (hφ : ∀ i, φ (c i • 1) = d i • 1) :
    φ (List.ofFn fun i ↦ M i - c i • 1).prod = (List.ofFn fun i ↦ φ (M i) - d i • 1).prod := by
  simp only [map_list_prod, List.map_ofFn, Function.comp_def, map_sub, hφ]

end TauCeti
