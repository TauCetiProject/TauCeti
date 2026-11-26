/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import TauCeti.GroupTheory.Perm.Cycle.Product
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Pseudocharacters

For a commutative ring `A`, a semiring `R` that is an `A`-module (in practice an `A`-algebra) and
`d ∈ ℕ`, a `d`-dimensional `A`-valued pseudocharacter on `R` is an `A`-linear map `T : R → A`
with `T(xy) = T(yx)`, `T(1) = d` and

`∑_{σ ∈ S_{d+1}} sgn(σ) T^σ(x₁, …, x_{d+1}) = 0`

for all `xᵢ ∈ R`, where `T^σ(x) = ∏ T(x_{j₁} ⋯ x_{jₛ})` over the cycles `(j₁ … jₛ)` of `σ`, fixed
points included, is the cycle term `TauCeti.cycleTerm` of
`TauCeti.GroupTheory.Perm.Cycle.Product`. No hypothesis on `d!` is made here.

## Main declarations

* `TauCeti.cycleSum T x`: the alternating sum `∑_σ sgn(σ) T^σ(x)` of the cycle terms.
* `TauCeti.IsPseudocharacter T d`: the predicate.
* `TauCeti.isPseudocharacter_one_iff`: the `1`-dimensional pseudocharacters are the linear maps
  that preserve `1` and products.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.10 and §1.26](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

open Equiv

namespace TauCeti

section CommRing

variable {A : Type*} [CommRing A] {R : Type*} {n : ℕ}

/-- The alternating sum `∑_{σ ∈ S_n} sgn(σ) T^σ(x)` of the cycle terms. -/
def cycleSum [Monoid R] (T : R → A) (x : Fin n → R) : A :=
  ∑ σ : Perm (Fin n), (Perm.sign σ : ℤ) • cycleTerm T σ x

theorem cycleSum_def [Monoid R] (T : R → A) (x : Fin n → R) :
    cycleSum T x = ∑ σ : Perm (Fin n), (Perm.sign σ : ℤ) • cycleTerm T σ x :=
  (rfl)

/-- The alternating sum over `S₂` is `T(x₀)T(x₁) − T(x₀x₁)`. -/
theorem cycleSum_fin_two [Monoid R] (T : R → A) (x : Fin 2 → R) :
    cycleSum T x = T (x 0) * T (x 1) - T (x 0 * x 1) := by
  have h : (Finset.univ : Finset (Perm (Fin 2))) = {1, swap 0 1} := by decide
  rw [cycleSum_def, h, Finset.sum_pair (by decide), cycleTerm_one, cycleTerm_swap_fin_two,
    Perm.sign_one, Perm.sign_swap (by decide)]
  simp [Fin.prod_univ_two, sub_eq_add_neg]

variable [Semiring R] [Module A R]

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
