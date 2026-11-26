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
public import TauCeti.GroupTheory.Perm.ComputedCycleType
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation

/-!
# Pseudocharacters

For a commutative ring `A`, a semiring `R` that is an `A`-module (in practice an `A`-algebra) and
`d ∈ ℕ`, a `d`-dimensional `A`-valued pseudocharacter on `R` is an `A`-linear map `T : R → A`
with `T(xy) = T(yx)`, `T(1) = d` and

`∑_{σ ∈ S_{d+1}} sgn(σ) T^σ(x₁, …, x_{d+1}) = 0`

for all `xᵢ ∈ R`, where `T^σ(x) = ∏ T(x_{j₁} ⋯ x_{jₛ})` over the cycles `(j₁ … jₛ)` of `σ`, fixed
points included. Each cycle is read starting at its least element `i`, in the order
`i, σ i, σ² i, …`. No hypothesis on `d!` is made here.

The cycle products and cycle terms only need `T` to be a function from a monoid `R` to a
commutative monoid `A`; when `T(ab) = T(ba)`, the cycle term does not depend on where each cycle
is read from, so it is unchanged by relabelling the entries.

## Main declarations

* `Equiv.Perm.cycleProduct σ x i`: the product `x_i x_{σ i} ⋯ x_{σ^(k-1) i}` along the cycle of
  `i`, where `k` is the minimal period of `i`.
* `TauCeti.cycleTerm T σ x`: the product of `T (σ.cycleProduct x i)` over the least elements `i`
  of the cycles of `σ`.
* `TauCeti.cycleTerm_conj`: for `T(ab) = T(ba)`, relabelling the entries does not change the
  cycle term.
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

namespace Equiv.Perm

variable {R : Type*} [Monoid R] {n : ℕ}

/-- The product `x_i x_{σ i} ⋯ x_{σ^(k-1) i}` of the entries of `x` along the cycle of `σ`
through `i`, read starting at `i`, where `k` is the minimal period of `i` under `σ`. -/
def cycleProduct (σ : Perm (Fin n)) (x : Fin n → R) (i : Fin n) : R :=
  (List.ofFn fun k : Fin (minimalPeriod σ i) ↦ x ((σ ^ (k : ℕ)) i)).prod

theorem cycleProduct_def (σ : Perm (Fin n)) (x : Fin n → R) (i : Fin n) :
    σ.cycleProduct x i =
      (List.ofFn fun k : Fin (minimalPeriod σ i) ↦ x ((σ ^ (k : ℕ)) i)).prod :=
  (rfl)

/-- At a fixed point `i` of `σ` the cycle product is the entry `x i`. -/
theorem cycleProduct_of_isFixedPt {σ : Perm (Fin n)} (x : Fin n → R) {i : Fin n}
    (hi : IsFixedPt σ i) : σ.cycleProduct x i = x i := by
  have h : minimalPeriod σ i = 1 := minimalPeriod_eq_one_iff_isFixedPt.mpr hi
  rw [cycleProduct_def, List.ofFn_congr h]
  simp

/-- For the identity permutation the cycle product at `i` is `x i`. -/
@[simp]
theorem cycleProduct_one (x : Fin n → R) (i : Fin n) : (1 : Perm (Fin n)).cycleProduct x i = x i :=
  cycleProduct_of_isFixedPt x (by simp [IsFixedPt])

/-- For the transposition of `i ≠ j`, the cycle product starting at `i` is `x i * x j`. -/
theorem cycleProduct_swap_left (x : Fin n → R) {i j : Fin n} (hij : i ≠ j) :
    (swap i j).cycleProduct x i = x i * x j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : minimalPeriod (swap i j) i = 2 :=
    minimalPeriod_eq_prime (p := 2) (by simp [IsPeriodicPt, IsFixedPt])
      (by simpa [IsFixedPt, swap_apply_left] using hij.symm)
  rw [cycleProduct_def, List.ofFn_congr h]
  simp [List.ofFn_succ, pow_succ]

/-- For the transposition of `i ≠ j`, the cycle product starting at `j` is `x j * x i`. -/
theorem cycleProduct_swap_right (x : Fin n → R) {i j : Fin n} (hij : i ≠ j) :
    (swap i j).cycleProduct x j = x j * x i := by
  rw [swap_comm, cycleProduct_swap_left x hij.symm]

/-- Relabelling the entries along `τ` relabels the cycle products. -/
theorem cycleProduct_conj (σ τ : Perm (Fin n)) (x : Fin n → R) (i : Fin n) :
    (τ * σ * τ⁻¹).cycleProduct (x ∘ ⇑τ⁻¹) (τ i) = σ.cycleProduct x i := by
  have h : minimalPeriod (τ * σ * τ⁻¹) (τ i) = minimalPeriod σ i :=
    minimalPeriod_eq_minimalPeriod_iff.mpr fun k ↦ by
      simp only [IsPeriodicPt, IsFixedPt, iterate_eq_pow, conj_pow, mul_apply, coe_inv,
        symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
  rw [cycleProduct_def, cycleProduct_def, List.ofFn_congr h]
  simp only [conj_pow, mul_apply, coe_inv, symm_apply_apply, comp_apply]
  rfl

/-- If `T(ab) = T(ba)`, then `T` of the cycle product does not depend on the starting point:
reading the cycle from `σ i` instead of `i` rotates the product. -/
theorem map_cycleProduct_apply {β : Type*} {T : R → β} (hT : ∀ a b, T (a * b) = T (b * a))
    (σ : Perm (Fin n)) (x : Fin n → R) (i : Fin n) :
    T (σ.cycleProduct x (σ i)) = T (σ.cycleProduct x i) := by
  have hi : i ∈ periodicPts σ := σ.injective.mem_periodicPts i
  obtain ⟨m, hm⟩ :=
    Nat.exists_eq_add_one_of_ne_zero (minimalPeriod_pos_of_mem_periodicPts hi).ne'
  have hm' : minimalPeriod σ (σ i) = m + 1 := (minimalPeriod_apply hi).trans hm
  have hper : (σ ^ (m + 1)) i = i := by
    rw [← hm, ← iterate_eq_pow]
    exact isPeriodicPt_minimalPeriod σ i
  rw [cycleProduct_def, cycleProduct_def, List.ofFn_congr hm', List.ofFn_congr hm,
    List.ofFn_succ', List.ofFn_succ, List.prod_concat, List.prod_cons, hT]
  simp [← mul_apply, ← pow_succ, hper]

/-- If `T(ab) = T(ba)`, then `T` of the cycle product is the same at all points of a cycle. -/
theorem map_cycleProduct_eq_of_sameCycle {β : Type*} {T : R → β}
    (hT : ∀ a b, T (a * b) = T (b * a)) {σ : Perm (Fin n)} (x : Fin n → R) {i j : Fin n}
    (hij : σ.SameCycle i j) : T (σ.cycleProduct x i) = T (σ.cycleProduct x j) := by
  obtain ⟨k, -, rfl⟩ := hij.exists_pow_eq'
  clear hij
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply, map_cycleProduct_apply hT, ih]

end Equiv.Perm

namespace TauCeti

section Monoid

variable {R : Type*} [Monoid R] {A : Type*} [CommMonoid A] {n : ℕ}

/-- The cycle term `T^σ(x) = ∏ T(x_{j₁} ⋯ x_{jₛ})` over the cycles `(j₁ … jₛ)` of `σ`, fixed
points included, each cycle read from its least element (`Equiv.Perm.cycleProduct`). -/
def cycleTerm (T : R → A) (σ : Perm (Fin n)) (x : Fin n → R) : A :=
  ∏ i ∈ Finset.univ.filter σ.IsCycleMin, T (σ.cycleProduct x i)

theorem cycleTerm_def (T : R → A) (σ : Perm (Fin n)) (x : Fin n → R) :
    cycleTerm T σ x = ∏ i ∈ Finset.univ.filter σ.IsCycleMin, T (σ.cycleProduct x i) :=
  (rfl)

/-- The cycle term of the empty tuple is `1`. -/
@[simp]
theorem cycleTerm_fin_zero (T : R → A) (σ : Perm (Fin 0)) (x : Fin 0 → R) :
    cycleTerm T σ x = 1 := by
  simp [cycleTerm_def]

/-- The cycle term of the identity is `∏ᵢ T(xᵢ)`: every point is its own cycle. -/
@[simp]
theorem cycleTerm_one (T : R → A) (x : Fin n → R) :
    cycleTerm T 1 x = ∏ i, T (x i) := by
  rw [cycleTerm_def, Finset.filter_true_of_mem fun i _ j hij ↦ by
    rw [Perm.sameCycle_one] at hij
    exact hij.le]
  simp

/-- The cycle term of the transposition of two entries is `T(x₀x₁)`: one cycle factor. -/
theorem cycleTerm_swap_fin_two (T : R → A) (x : Fin 2 → R) :
    cycleTerm T (swap 0 1) x = T (x 0 * x 1) := by
  have h : Finset.univ.filter (swap 0 1 : Perm (Fin 2)).IsCycleMin = {0} := by
    ext i
    fin_cases i
    · simp [Perm.IsCycleMin]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      refine iff_of_false (fun h ↦ ?_) (by decide)
      exact absurd (h 0 ⟨1, by simp⟩) (by decide)
  rw [cycleTerm_def, h, Finset.prod_singleton, Perm.cycleProduct_swap_left x (by decide)]

/-- If `T(ab) = T(ba)`, relabelling the entries along `τ` does not change the cycle term. -/
theorem cycleTerm_conj {T : R → A} (hT : ∀ a b, T (a * b) = T (b * a))
    (σ τ : Perm (Fin n)) (x : Fin n → R) :
    cycleTerm T (τ * σ * τ⁻¹) (x ∘ ⇑τ⁻¹) = cycleTerm T σ x := by
  rw [cycleTerm_def, cycleTerm_def]
  refine Finset.prod_nbij' (fun i ↦ σ.cycleMin (τ⁻¹ i)) (fun i ↦ (τ * σ * τ⁻¹).cycleMin (τ i))
    (by simp) (by simp) (fun i hi ↦ ?_) (fun i hi ↦ ?_) (fun i _ ↦ ?_)
  · rw [Finset.mem_filter] at hi
    refine (Perm.cycleMin_eq_cycleMin_iff.mpr ?_).trans (Perm.cycleMin_eq_self_iff.mpr hi.2)
    rw [Perm.sameCycle_conj]
    simpa only [Perm.coe_inv, symm_apply_apply] using (σ.sameCycle_cycleMin (τ⁻¹ i)).symm
  · rw [Finset.mem_filter] at hi
    refine (Perm.cycleMin_eq_cycleMin_iff.mpr ?_).trans (Perm.cycleMin_eq_self_iff.mpr hi.2)
    have h := ((τ * σ * τ⁻¹).sameCycle_cycleMin (τ i)).symm
    rw [Perm.sameCycle_conj] at h
    simpa only [Perm.coe_inv, symm_apply_apply] using h
  · obtain ⟨j, rfl⟩ := τ.surjective i
    have hj : τ⁻¹ (τ j) = j := by simp
    rw [Perm.cycleProduct_conj, hj]
    exact Perm.map_cycleProduct_eq_of_sameCycle hT x (σ.sameCycle_cycleMin j)

end Monoid

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
