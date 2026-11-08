/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.StarPolynomial
public import TauCeti.Analysis.StarAlgebra.CauchySchwarz

/-!
# Exponential word bounds for star distributions

Let `φ` be a positive functional on the noncommutative star polynomials `StarPolynomial ℂ ι`,
`0 ≤ φ (star p * p)`, for instance the star distribution of a family in a star algebra with
respect to a positive functional. Positivity alone does not make the generators act boundedly on
the GNS space of `φ`. This file shows that an exponential bound on the word moments does: if

`‖φ (w)‖ ≤ C * R ^ length w`

for some constant `C` and every word `w` in the generators `Xᵢ` and their adjoints `Xᵢ*`, then for
every star polynomial `p` and every `i`,

`φ (p* Xᵢ* Xᵢ p) ≤ R ^ 2 * φ (p* p)` and `φ (p* Xᵢ Xᵢ* p) ≤ R ^ 2 * φ (p* p)`.

These are the inequalities which say that left multiplication by `Xᵢ` and by `Xᵢ*` has norm at
most `R` on the GNS space of `φ`, so that the GNS representation extends to bounded operators.

The proof expands `p` in words: the moments `φ (p* (Xᵢ* Xᵢ) ^ m p)` are finite sums of word moments
of lengths `2 * m` plus a constant, so they grow at most like `D * (R ^ 2) ^ m` for a constant
`D`. The iterated Cauchy–Schwarz inequality `LinearMap.map_star_mul_star_mul_mul_le_of_forall_pow`
then removes the constant `D`.

## Main results

* `TauCeti.map_star_mul_star_X_mul_X_mul_le` — `φ (p* Xᵢ* Xᵢ p) ≤ R ^ 2 * φ (p* p)`.
* `TauCeti.map_star_mul_X_mul_star_X_mul_le` — `φ (p* Xᵢ Xᵢ* p) ≤ R ^ 2 * φ (p* p)`.

## References

* K. Schmüdgen, *An Invitation to Unbounded Representations of ∗-Algebras on Hilbert Space*,
  Graduate Texts in Mathematics 285, Springer, 2020, Chapter 4.
-/

public section

namespace TauCeti

open StarPolynomial ComplexOrder

variable {ι : Type*} {φ : StarPolynomial ℂ ι →ₗ[ℂ] ℂ} {C R : ℝ}

/-- For the square `star g * g` of a letter `g`, the moment of `u * (star g * g) ^ m * v` for
words `u` and `v` is the moment of a word of length `length u + 2 * m + length v`. -/
private theorem norm_map_list_prod_mul_pow_mul_list_prod_le
    (hR : ∀ w : List (ι × Bool), ‖φ (w.map (withStar X)).prod‖ ≤ C * R ^ w.length)
    (x : ι × Bool)
    (m : ℕ) (u v : List (ι × Bool)) :
    ‖φ ((u.map (withStar X)).prod * (star (withStar X x) * withStar X x) ^ m *
      (v.map (withStar X)).prod)‖ ≤ C * R ^ (u.length + v.length) * (R ^ 2) ^ m := by
  have hx : star (withStar (X (R := ℂ)) x) * withStar X x =
      ([(x.1, !x.2), x].map (withStar X)).prod := by
    obtain ⟨i, _ | _⟩ := x <;> simp
  rw [hx]
  induction m generalizing u with
  | zero => simpa using hR (u ++ v)
  | succ m ih =>
    rw [pow_succ', ← mul_assoc ((u.map (withStar X)).prod), ← List.prod_append,
      ← List.map_append]
    refine (ih _).trans_eq ?_
    simp only [List.length_append, List.length_cons, List.length_nil]
    ring

/-- The moments `φ (u * (star g * g) ^ m * v)` grow at most like `D * (R ^ 2) ^ m`. -/
private theorem exists_norm_map_mul_pow_mul_le
    (hR : ∀ w : List (ι × Bool), ‖φ (w.map (withStar X)).prod‖ ≤ C * R ^ w.length)
    (x : ι × Bool)
    (u v : StarPolynomial ℂ ι) :
    ∃ D, ∀ m, ‖φ (u * (star (withStar X x) * withStar X x) ^ m * v)‖ ≤ D * (R ^ 2) ^ m := by
  have hs := span_range_list_prod_withStar (R := ℂ) (ι := ι)
  induction (hs ▸ Submodule.mem_top : u ∈ _), (hs ▸ Submodule.mem_top : v ∈ _)
    using Submodule.span_induction₂ with
  | mem_mem u v hu hv =>
    obtain ⟨u, rfl⟩ := hu
    obtain ⟨v, rfl⟩ := hv
    exact ⟨_, fun m ↦ norm_map_list_prod_mul_pow_mul_list_prod_le hR x m u v⟩
  | zero_left v _ => exact ⟨0, by simp⟩
  | zero_right u _ => exact ⟨0, by simp⟩
  | add_left u₁ u₂ v _ _ _ h₁ h₂ =>
    obtain ⟨D₁, h₁⟩ := h₁
    obtain ⟨D₂, h₂⟩ := h₂
    refine ⟨D₁ + D₂, fun m ↦ ?_⟩
    rw [add_mul, add_mul, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ m) (h₂ m))
  | add_right u v₁ v₂ _ _ _ h₁ h₂ =>
    obtain ⟨D₁, h₁⟩ := h₁
    obtain ⟨D₂, h₂⟩ := h₂
    refine ⟨D₁ + D₂, fun m ↦ ?_⟩
    rw [mul_add, map_add, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (h₁ m) (h₂ m))
  | smul_left r u v _ _ h =>
    obtain ⟨D, h⟩ := h
    refine ⟨‖r‖ * D, fun m ↦ ?_⟩
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul, norm_mul, mul_assoc ‖r‖]
    exact mul_le_mul_of_nonneg_left (h m) (norm_nonneg r)
  | smul_right r u v _ _ h =>
    obtain ⟨D, h⟩ := h
    refine ⟨‖r‖ * D, fun m ↦ ?_⟩
    rw [mul_smul_comm, map_smul, smul_eq_mul, norm_mul, mul_assoc ‖r‖]
    exact mul_le_mul_of_nonneg_left (h m) (norm_nonneg r)

/-- The bound `φ (p* g* g p) ≤ R ^ 2 * φ (p* p)` for a letter `g`, a generator or the adjoint of
a generator. -/
private theorem map_star_mul_star_withStar_mul_withStar_mul_le
    (hφ : ∀ p, 0 ≤ φ (star p * p))
    (hR : ∀ w : List (ι × Bool), ‖φ (w.map (withStar X)).prod‖ ≤ C * R ^ w.length)
    (x : ι × Bool)
    (p : StarPolynomial ℂ ι) :
    φ (star p * star (withStar X x) * withStar X x * p) ≤ (R : ℂ) ^ 2 * φ (star p * p) := by
  obtain ⟨D, hD⟩ := exists_norm_map_mul_pow_mul_le hR x (star p) p
  exact_mod_cast φ.map_star_mul_star_mul_mul_le_of_forall_pow hφ _ p (sq_nonneg R) hD

/-- If a positive functional on the star polynomials satisfies `‖φ (w)‖ ≤ C * R ^ length w` on
every word `w` in the generators and their adjoints, then `φ (p* Xᵢ* Xᵢ p) ≤ R ^ 2 * φ (p* p)` for
every star polynomial `p`: left multiplication by `Xᵢ` has norm at most `R` on the GNS space. -/
theorem map_star_mul_star_X_mul_X_mul_le (hφ : ∀ p, 0 ≤ φ (star p * p))
    (hR : ∀ w : List (ι × Bool), ‖φ (w.map (withStar X)).prod‖ ≤ C * R ^ w.length)
    (i : ι) (p : StarPolynomial ℂ ι) :
    φ (star p * star (X i) * X i * p) ≤ (R : ℂ) ^ 2 * φ (star p * p) := by
  simpa using map_star_mul_star_withStar_mul_withStar_mul_le hφ hR (i, false) p

/-- If a positive functional on the star polynomials satisfies `‖φ (w)‖ ≤ C * R ^ length w` on
every word `w` in the generators and their adjoints, then `φ (p* Xᵢ Xᵢ* p) ≤ R ^ 2 * φ (p* p)` for
every star polynomial `p`: left multiplication by `Xᵢ*` has norm at most `R` on the GNS space. -/
theorem map_star_mul_X_mul_star_X_mul_le (hφ : ∀ p, 0 ≤ φ (star p * p))
    (hR : ∀ w : List (ι × Bool), ‖φ (w.map (withStar X)).prod‖ ≤ C * R ^ w.length)
    (i : ι) (p : StarPolynomial ℂ ι) :
    φ (star p * X i * star (X i) * p) ≤ (R : ℂ) ^ 2 * φ (star p * p) := by
  simpa using map_star_mul_star_withStar_mul_withStar_mul_le hφ hR (i, true) p

end TauCeti
