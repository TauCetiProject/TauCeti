/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

/-!
# The six Legendre parameters of an ordered split cubic

A cubic `(x - e₀) (x - e₁) (x - e₂)` with pairwise distinct roots in a field `K` is moved by the
translation `x ↦ x + e₀` to `x (x - d) (x - d λ)` with `d = e₁ - e₀` and
`λ = (e₂ - e₀) / (e₁ - e₀)`, the parameter of the Legendre equation `y² = x (x - 1) (x - λ)`.
The parameter depends on the order in which the three roots are listed. Listing them in the order
`(e_a, e_b, e_c)` gives `(e_c - e_a) / (e_b - e_a)`, which is the cross-ratio of
`(∞, e_a; e_b, e_c)` (in Tau Ceti, `OnePoint.crossRatioSphere ∞ e_a e_b e_c`). For the six orders
`(012), (021), (102), (120), (210), (201)` these are, respectively,

  `λ, 1 / λ, 1 - λ, 1 / (1 - λ), λ / (λ - 1), (λ - 1) / λ`.

This file packages the six values as a `Fin 6`-indexed tuple, `TauCeti.legendreParameters`, and
the six orders as permutations of `Fin 3`, `TauCeti.legendreRootOrder`, and proves that the
parameter of the `i`-th order is the `i`-th entry of the tuple. The labels are kept even when
values coincide: at `λ = -1` the tuple is `(-1, -1, 2, 1/2, 1/2, 2)`. The tuple is a total
expression in `λ`, so it is defined for every `λ`, but its entries are admissible Legendre
parameters, different from `0` and `1`, only when `λ` is.

## Main definitions

* `TauCeti.legendreParameters`: the tuple `(λ, λ⁻¹, 1 - λ, (1 - λ)⁻¹, λ / (λ - 1), (λ - 1) / λ)`.
* `TauCeti.legendreRootOrder`: the six orders `(012), (021), (102), (120), (210), (201)` of three
  roots, as permutations of `Fin 3`.

## Main results

* `TauCeti.legendreParameters_ne_zero`, `TauCeti.legendreParameters_ne_one`: for `λ ≠ 0, 1`, no
  entry is `0` or `1`.
* `TauCeti.legendreParameters_mul_eq_one`: for `λ ≠ 0, 1`, the labels `(0, 1)`, `(2, 3)` and
  `(4, 5)` are reciprocal pairs.
* `TauCeti.map_legendreParameters`: ring homomorphisms commute with the tuple.
* `TauCeti.legendreRootOrder_bijective`: the six labels enumerate the orders of three roots.
* `TauCeti.sub_div_sub_eq_legendreParameters`: the parameter of the `i`-th order of the roots
  `e` is the `i`-th entry of the tuple at `λ = (e 2 - e 0) / (e 1 - e 0)`.
* `TauCeti.range_sub_div_sub_eq_range_legendreParameters`: the parameters of all six orders are
  exactly the entries of the tuple.
* `TauCeti.sub_div_sub_ne_zero`, `TauCeti.sub_div_sub_ne_one`: for pairwise distinct roots, the
  parameter of every order is different from `0` and `1`.
* `TauCeti.sub_legendreRootOrder`: the scale `e (σ 1) - e (σ 0)` of the translated roots for the
  `i`-th order `σ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.7.
* M. A. Bennett and S. Siksek, *A conjecture of Erdős, supersingular primes and short character
  sums*, Ann. of Math. 191 (2020), 355–392, §6, proof of Lemma 6.2.
-/

public section

namespace TauCeti

/-! ### The labelled tuple of Legendre parameters -/

section DivisionRing

variable {K : Type*} [DivisionRing K] {l : K}

/-- The six Legendre parameters attached to `l`, in the labelled order
`(l, l⁻¹, 1 - l, (1 - l)⁻¹, l / (l - 1), (l - 1) / l)`. Labels are kept when values coincide.
The tuple is total in `l`; its entries are admissible parameters only when `l ≠ 0, 1`
(`TauCeti.legendreParameters_ne_zero`, `TauCeti.legendreParameters_ne_one`). -/
def legendreParameters (l : K) : Fin 6 → K :=
  ![l, l⁻¹, 1 - l, (1 - l)⁻¹, l / (l - 1), (l - 1) / l]

/-- The defining formula of `TauCeti.legendreParameters`. -/
theorem legendreParameters_def (l : K) :
    legendreParameters l = ![l, l⁻¹, 1 - l, (1 - l)⁻¹, l / (l - 1), (l - 1) / l] :=
  (rfl)

@[simp]
theorem legendreParameters_apply_zero (l : K) : legendreParameters l 0 = l :=
  (rfl)

@[simp]
theorem legendreParameters_apply_one (l : K) : legendreParameters l 1 = l⁻¹ :=
  (rfl)

@[simp]
theorem legendreParameters_apply_two (l : K) : legendreParameters l 2 = 1 - l :=
  (rfl)

@[simp]
theorem legendreParameters_apply_three (l : K) : legendreParameters l 3 = (1 - l)⁻¹ :=
  (rfl)

@[simp]
theorem legendreParameters_apply_four (l : K) : legendreParameters l 4 = l / (l - 1) :=
  (rfl)

@[simp]
theorem legendreParameters_apply_five (l : K) : legendreParameters l 5 = (l - 1) / l :=
  (rfl)

/-- For `l ≠ 0, 1`, no Legendre parameter attached to `l` is `0`. -/
theorem legendreParameters_ne_zero (h₀ : l ≠ 0) (h₁ : l ≠ 1) (i : Fin 6) :
    legendreParameters l i ≠ 0 := by
  have h₁' : l - 1 ≠ 0 := sub_ne_zero.mpr h₁
  have h₁'' : 1 - l ≠ 0 := sub_ne_zero.mpr h₁.symm
  fin_cases i <;> simp [h₀, h₁', h₁'']

/-- For `l ≠ 0, 1`, no Legendre parameter attached to `l` is `1`. -/
theorem legendreParameters_ne_one (h₀ : l ≠ 0) (h₁ : l ≠ 1) (i : Fin 6) :
    legendreParameters l i ≠ 1 := by
  have h₁' : l - 1 ≠ 0 := sub_ne_zero.mpr h₁
  fin_cases i
  · exact h₁
  · simpa using h₁
  · simpa [sub_eq_self] using h₀
  · simpa [sub_eq_self] using h₀
  · simp only [Fin.reduceFinMk, legendreParameters_apply_four, Ne, div_eq_one_iff_eq h₁']
    exact fun h ↦ one_ne_zero (sub_eq_self.mp h.symm)
  · simp [div_eq_one_iff_eq h₀]

/-- For `l ≠ 0, 1`, the Legendre parameters with labels `(0, 1)`, `(2, 3)` and `(4, 5)` are
reciprocal pairs. -/
theorem legendreParameters_mul_eq_one (h₀ : l ≠ 0) (h₁ : l ≠ 1) :
    legendreParameters l 0 * legendreParameters l 1 = 1 ∧
      legendreParameters l 2 * legendreParameters l 3 = 1 ∧
      legendreParameters l 4 * legendreParameters l 5 = 1 := by
  refine ⟨by simp [h₀], by simp [sub_ne_zero.mpr h₁.symm], ?_⟩
  rw [legendreParameters_apply_four, legendreParameters_apply_five, ← inv_div l (l - 1)]
  exact mul_inv_cancel₀ (div_ne_zero h₀ (sub_ne_zero.mpr h₁))

/-- Ring homomorphisms between division rings commute with the Legendre parameters. -/
@[simp]
theorem map_legendreParameters {L F : Type*} [DivisionRing L] [FunLike F K L]
    [RingHomClass F K L] (f : F) (l : K) (i : Fin 6) :
    f (legendreParameters l i) = legendreParameters (f l) i := by
  fin_cases i <;> simp

end DivisionRing

/-! ### The six orders of three roots -/

/-- The six orders `(012), (021), (102), (120), (210), (201)` of three roots, as permutations `σ`
of `Fin 3`: the `i`-th order lists the roots `e` as `(e (σ 0), e (σ 1), e (σ 2))`. Its Legendre
parameter is the `i`-th entry of `TauCeti.legendreParameters`
(`TauCeti.sub_div_sub_eq_legendreParameters`). -/
def legendreRootOrder (i : Fin 6) : Equiv.Perm (Fin 3) where
  toFun := ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0], ![2, 0, 1]] i
  invFun := ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0], ![1, 2, 0]] i
  left_inv := by revert i; decide
  right_inv := by revert i; decide

@[simp]
theorem legendreRootOrder_apply (i : Fin 6) (j : Fin 3) :
    legendreRootOrder i j =
      ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 1, 0], ![2, 0, 1]] i j :=
  (rfl)

/-- The six labels enumerate the orders of three roots, each exactly once. -/
theorem legendreRootOrder_bijective : Function.Bijective legendreRootOrder := by
  have hinj : Function.Injective legendreRootOrder := by
    intro i j h
    have h' : ∀ k, legendreRootOrder i k = legendreRootOrder j k := fun k ↦ by rw [h]
    revert i j
    decide
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  simp [Fintype.card_perm, Nat.factorial]

/-! ### Legendre parameters of the orders of three roots -/

section Field

variable {K : Type*} [Field K] {e : Fin 3 → K}

/-- **The six Legendre parameters of ordered roots.** For the `i`-th order `σ` of the roots `e`,
the Legendre parameter `(e (σ 2) - e (σ 0)) / (e (σ 1) - e (σ 0))` is the `i`-th entry of the
tuple of Legendre parameters at `λ = (e 2 - e 0) / (e 1 - e 0)`. Only `e 0 ≠ e 1` is assumed:
coincidences of `e 2` with `e 0` or `e 1` are matched by the junk value of division by zero. -/
theorem sub_div_sub_eq_legendreParameters (h : e 0 ≠ e 1) (i : Fin 6) :
    (e (legendreRootOrder i 2) - e (legendreRootOrder i 0)) /
        (e (legendreRootOrder i 1) - e (legendreRootOrder i 0)) =
      legendreParameters ((e 2 - e 0) / (e 1 - e 0)) i := by
  have h₁₀ : e 1 - e 0 ≠ 0 := sub_ne_zero.mpr h.symm
  fin_cases i <;> simp [one_sub_div h₁₀, div_sub_one h₁₀, div_div_div_cancel_right₀ h₁₀, inv_div]
  -- the remaining four orders are `a / b = -a / -b`
  all_goals grind

/-- For roots with `e 0 ≠ e 1`, the Legendre parameters of the six orders of the roots are exactly
the entries of the tuple of Legendre parameters at `λ = (e 2 - e 0) / (e 1 - e 0)`. -/
theorem range_sub_div_sub_eq_range_legendreParameters (h : e 0 ≠ e 1) :
    Set.range (fun σ : Equiv.Perm (Fin 3) ↦ (e (σ 2) - e (σ 0)) / (e (σ 1) - e (σ 0))) =
      Set.range (legendreParameters ((e 2 - e 0) / (e 1 - e 0))) := by
  rw [← legendreRootOrder_bijective.surjective.range_comp]
  exact congrArg Set.range (funext (sub_div_sub_eq_legendreParameters h))

end Field

section DivisionRing

variable {K : Type*} [DivisionRing K] {e : Fin 3 → K}

/-- For pairwise distinct roots `e`, the Legendre parameter of every order `σ` of the roots is
different from `0`. -/
theorem sub_div_sub_ne_zero (he : Function.Injective e) (σ : Equiv.Perm (Fin 3)) :
    (e (σ 2) - e (σ 0)) / (e (σ 1) - e (σ 0)) ≠ 0 :=
  div_ne_zero (sub_ne_zero.mpr ((he.comp σ.injective).ne (by decide)))
    (sub_ne_zero.mpr ((he.comp σ.injective).ne (by decide)))

/-- For pairwise distinct roots `e`, the Legendre parameter of every order `σ` of the roots is
different from `1`. -/
theorem sub_div_sub_ne_one (he : Function.Injective e) (σ : Equiv.Perm (Fin 3)) :
    (e (σ 2) - e (σ 0)) / (e (σ 1) - e (σ 0)) ≠ 1 := by
  have h₁₀ : e (σ 1) ≠ e (σ 0) := (he.comp σ.injective).ne (by decide)
  have h₂₁ : e (σ 2) ≠ e (σ 1) := (he.comp σ.injective).ne (by decide)
  rwa [Ne, div_eq_one_iff_eq (sub_ne_zero.mpr h₁₀), sub_left_inj]

end DivisionRing

section Ring

variable {R : Type*} [Ring R] {e : Fin 3 → R}

/-- **The scale of each order.** If `e 2 - e 0 = d * l` with `d = e 1 - e 0`, the scale
`e (σ 1) - e (σ 0)` of the `i`-th order `σ`, the second root after translating by the first, is the
`i`-th entry of `(d, d l, -d, d (l - 1), d (1 - l), -d l)`. For `d ≠ 0` and
`l = (e 2 - e 0) / d`, the translated roots of the `i`-th order are therefore `(0, d', d' l')`
with this scale `d'` and the `i`-th Legendre parameter `l'` at `l`
(`TauCeti.sub_div_sub_eq_legendreParameters`). -/
theorem sub_legendreRootOrder {l : R} (hl : e 2 - e 0 = (e 1 - e 0) * l) (i : Fin 6) :
    e (legendreRootOrder i 1) - e (legendreRootOrder i 0) =
      (e 1 - e 0) * ![1, l, -1, l - 1, 1 - l, -l] i := by
  fin_cases i <;> simp [mul_sub, ← hl]

end Ring

end TauCeti
