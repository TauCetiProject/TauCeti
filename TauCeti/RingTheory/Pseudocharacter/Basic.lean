/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Pseudocharacters

For a commutative ring `A`, a ring `R` that is an `A`-module (in practice an `A`-algebra) and
`d ∈ ℕ`, a `d`-dimensional `A`-valued pseudocharacter on `R` is an `A`-linear map `T : R → A`
with `T(xy) = T(yx)`, `T(1) = d` and

`∑_{σ ∈ S_{d+1}} sgn(σ) T^σ(x₁, …, x_{d+1}) = 0`

for all `xᵢ ∈ R`, where `T^σ(x) = ∏ T(x_{j₁} ⋯ x_{jₛ})` over the cycles `(j₁ … jₛ)` of `σ`, fixed
points included. Each cycle is read starting at its least element `i`, in the order
`i, σ i, σ² i, …`. No hypothesis on `d!` is made here.

## Main declarations

* `TauCeti.cycleProduct σ x i`: the product `x_i x_{σ i} ⋯ x_{σ^(k-1) i}` along the cycle of `i`,
  where `k` is the minimal period of `i`.
* `TauCeti.cycleTerm T σ x`: the product of `T (cycleProduct σ x i)` over the least elements `i`
  of the cycles of `σ`.
* `TauCeti.IsPseudocharacter T d`: the predicate.
* `TauCeti.isPseudocharacter_one_iff`: the `1`-dimensional pseudocharacters are the linear maps
  that preserve `1` and products.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.10 and §1.26](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

open Equiv Function

namespace TauCeti

section Monoid

variable {R : Type*} [Monoid R] {n : ℕ}

/-- The product `x_i x_{σ i} ⋯ x_{σ^(k-1) i}` of the entries of `x` along the cycle of `σ`
through `i`, read starting at `i`, where `k` is the minimal period of `i` under `σ`. -/
def cycleProduct (σ : Perm (Fin n)) (x : Fin n → R) (i : Fin n) : R :=
  (List.ofFn fun k : Fin (minimalPeriod σ i) ↦ x ((σ ^ (k : ℕ)) i)).prod

theorem cycleProduct_def (σ : Perm (Fin n)) (x : Fin n → R) (i : Fin n) :
    cycleProduct σ x i =
      (List.ofFn fun k : Fin (minimalPeriod σ i) ↦ x ((σ ^ (k : ℕ)) i)).prod :=
  (rfl)

/-- At a fixed point `i` of `σ` the cycle product is the entry `x i`. -/
theorem cycleProduct_of_isFixedPt {σ : Perm (Fin n)} (x : Fin n → R) {i : Fin n}
    (hi : IsFixedPt σ i) : cycleProduct σ x i = x i := by
  have h : minimalPeriod σ i = 1 := minimalPeriod_eq_one_iff_isFixedPt.mpr hi
  rw [cycleProduct_def, List.ofFn_congr h]
  simp

/-- For the identity permutation the cycle product at `i` is `x i`. -/
@[simp]
theorem cycleProduct_one (x : Fin n → R) (i : Fin n) : cycleProduct 1 x i = x i :=
  cycleProduct_of_isFixedPt x (by simp [IsFixedPt])

/-- For the transposition of `i ≠ j`, the cycle product starting at `i` is `x i * x j`. -/
theorem cycleProduct_swap (x : Fin n → R) {i j : Fin n} (hij : i ≠ j) :
    cycleProduct (swap i j) x i = x i * x j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : minimalPeriod (swap i j) i = 2 :=
    minimalPeriod_eq_prime (p := 2) (by simp [IsPeriodicPt, IsFixedPt])
      (by simpa [IsFixedPt, swap_apply_left] using hij.symm)
  rw [cycleProduct_def, List.ofFn_congr h]
  simp [List.ofFn_succ, pow_succ]

end Monoid

section CommRing

variable {A : Type*} [CommRing A] {R : Type*} [Ring R] [Module A R] {n : ℕ}

/-- The cycle term `T^σ(x) = ∏ T(x_{j₁} ⋯ x_{jₛ})` over the cycles `(j₁ … jₛ)` of `σ`, fixed
points included, each cycle read from its least element (`cycleProduct`). -/
def cycleTerm (T : R →ₗ[A] A) (σ : Perm (Fin n)) (x : Fin n → R) : A :=
  ∏ i ∈ Finset.univ.filter (fun i ↦ ∀ j, σ.SameCycle i j → i ≤ j), T (cycleProduct σ x i)

theorem cycleTerm_def (T : R →ₗ[A] A) (σ : Perm (Fin n)) (x : Fin n → R) :
    cycleTerm T σ x =
      ∏ i ∈ Finset.univ.filter (fun i ↦ ∀ j, σ.SameCycle i j → i ≤ j),
        T (cycleProduct σ x i) :=
  (rfl)

/-- The cycle term of the empty tuple is `1`. -/
@[simp]
theorem cycleTerm_fin_zero (T : R →ₗ[A] A) (σ : Perm (Fin 0)) (x : Fin 0 → R) :
    cycleTerm T σ x = 1 := by
  simp [cycleTerm_def]

/-- The cycle term of the identity is `∏ᵢ T(xᵢ)`: every point is its own cycle. -/
@[simp]
theorem cycleTerm_one (T : R →ₗ[A] A) (x : Fin n → R) :
    cycleTerm T 1 x = ∏ i, T (x i) := by
  rw [cycleTerm_def, Finset.filter_true_of_mem fun i _ j hij ↦ by
    rw [Perm.sameCycle_one] at hij
    exact hij.le]
  simp

/-- The cycle term of the transposition of two entries is `T(x₀x₁)`: one cycle factor. -/
theorem cycleTerm_swap_fin_two (T : R →ₗ[A] A) (x : Fin 2 → R) :
    cycleTerm T (swap 0 1) x = T (x 0 * x 1) := by
  have h : Finset.univ.filter (fun i : Fin 2 ↦ ∀ j, (swap 0 1 : Perm (Fin 2)).SameCycle i j →
      i ≤ j) = {0} := by
    ext i
    fin_cases i
    · simp
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      refine iff_of_false (fun h ↦ ?_) (by decide)
      exact absurd (h 0 ⟨1, by simp⟩) (by decide)
  rw [cycleTerm_def, h, Finset.prod_singleton, cycleProduct_swap x (by decide)]

/-- The alternating sum `∑_{σ ∈ S_n} sgn(σ) T^σ(x)` of the cycle terms. -/
def cycleSum (T : R →ₗ[A] A) (x : Fin n → R) : A :=
  ∑ σ : Perm (Fin n), (Perm.sign σ : ℤ) • cycleTerm T σ x

theorem cycleSum_def (T : R →ₗ[A] A) (x : Fin n → R) :
    cycleSum T x = ∑ σ : Perm (Fin n), (Perm.sign σ : ℤ) • cycleTerm T σ x :=
  (rfl)

/-- The alternating sum over `S₂` is `T(x₀)T(x₁) − T(x₀x₁)`. -/
theorem cycleSum_fin_two (T : R →ₗ[A] A) (x : Fin 2 → R) :
    cycleSum T x = T (x 0) * T (x 1) - T (x 0 * x 1) := by
  have h : (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} := by decide
  rw [cycleSum_def, h, Finset.sum_pair (by decide), cycleTerm_one, cycleTerm_swap_fin_two,
    Perm.sign_one, Perm.sign_swap (by decide)]
  simp [Fin.prod_univ_two, sub_eq_add_neg]

/-- A `d`-dimensional `A`-valued pseudocharacter on `R`: an `A`-linear map `T : R → A` with
`T(xy) = T(yx)`, `T(1) = d` and `∑_{σ ∈ S_{d+1}} sgn(σ) T^σ(x) = 0` for all `x ∈ R^(d+1)`. No
hypothesis on `d!` is made. -/
structure IsPseudocharacter (T : R →ₗ[A] A) (d : ℕ) : Prop where
  /-- `T` is central: `T(xy) = T(yx)`. -/
  map_mul_comm : ∀ x y, T (x * y) = T (y * x)
  /-- `T(1) = d`. -/
  map_one : T 1 = d
  /-- The pseudocharacter identity in `d + 1` variables. -/
  cycleSum_eq_zero : ∀ x : Fin (d + 1) → R, cycleSum T x = 0

/-- The `1`-dimensional pseudocharacters are the linear maps preserving `1` and products. -/
theorem isPseudocharacter_one_iff (T : R →ₗ[A] A) :
    IsPseudocharacter T 1 ↔ T 1 = 1 ∧ ∀ x y, T (x * y) = T x * T y := by
  refine ⟨fun h ↦ ⟨by simpa using h.map_one, fun x y ↦ ?_⟩, fun ⟨h1, hmul⟩ ↦ ⟨?_, ?_, ?_⟩⟩
  · have := h.cycleSum_eq_zero ![x, y]
    rw [cycleSum_fin_two, sub_eq_zero] at this
    simpa using this.symm
  · intro x y
    rw [hmul, hmul, mul_comm]
  · simpa using h1
  · intro x
    rw [cycleSum_fin_two, hmul, sub_self]

end CommRing

end TauCeti
