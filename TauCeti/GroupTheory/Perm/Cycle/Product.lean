/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.GroupTheory.Perm.Cycle.Factors
public import TauCeti.GroupTheory.Perm.ComputedCycleType
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Products along the cycles of a permutation

For a permutation `σ` of `Fin n` and a tuple `x : Fin n → R` in a monoid, the cycle product
`σ.cycleProduct x i` is the product `x_i x_{σ i} ⋯` along the cycle of `σ` through `i`, read
starting at `i`. For a function `T : R → A` to a commutative monoid, the cycle term
`T^σ(x) = ∏ T(x_{j₁} ⋯ x_{jₛ})` is the product over the cycles `(j₁ … jₛ)` of `σ`, fixed points
included, each cycle read from its least element `i` in the order `i, σ i, σ² i, …`.

When `T(ab) = T(ba)`, `T` of a cycle product does not depend on where the cycle is read from, so
the cycle term is unchanged by relabelling the entries.

## Main declarations

* `Equiv.Perm.cycleProduct σ x i`: the product `x_i x_{σ i} ⋯ x_{σ^(k-1) i}` along the cycle of
  `i`, where `k` is the minimal period of `i`.
* `Equiv.Perm.map_cycleProduct_eq_of_sameCycle`: for `T(ab) = T(ba)`, `T` of the cycle product
  is the same at all points of a cycle.
* `TauCeti.cycleTerm T σ x`: the product of `T (σ.cycleProduct x i)` over the least elements `i`
  of the cycles of `σ`.
* `TauCeti.cycleTerm_conj`: for `T(ab) = T(ba)`, relabelling the entries does not change the
  cycle term.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, §1.10](https://arxiv.org/abs/0809.0415)
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
  simp only [conj_pow, mul_apply, coe_inv, symm_apply_apply, comp_apply, Fin.val_cast]

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
  · refine Perm.cycleMin_eq_of_sameCycle_of_isCycleMin ?_ (Finset.mem_filter.mp hi).2
    rw [Perm.sameCycle_conj]
    simpa only [Perm.coe_inv, symm_apply_apply] using (σ.sameCycle_cycleMin (τ⁻¹ i)).symm
  · refine Perm.cycleMin_eq_of_sameCycle_of_isCycleMin ?_ (Finset.mem_filter.mp hi).2
    have h := ((τ * σ * τ⁻¹).sameCycle_cycleMin (τ i)).symm
    rw [Perm.sameCycle_conj] at h
    simpa only [Perm.coe_inv, symm_apply_apply] using h
  · obtain ⟨j, rfl⟩ := τ.surjective i
    have hj : τ⁻¹ (τ j) = j := by simp
    rw [Perm.cycleProduct_conj, hj]
    exact Perm.map_cycleProduct_eq_of_sameCycle hT x (σ.sameCycle_cycleMin j)

end TauCeti
