/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Set.Function
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Markoff surface and its Vieta moves

For a commutative ring `R`, the *Markoff surface* is the set `X(R)` of triples
`x = (x₀, x₁, x₂) ∈ R³` with `x₀² + x₁² + x₂² = 3 x₀ x₁ x₂`. Triples are functions `Fin 3 → R`,
so that coordinate permutations are precompositions. The equation is quadratic in each
coordinate, and replacing one coordinate by the other root of that quadratic is the *Vieta move*
`R_i x`, which replaces `x_i` by `3 x_{i+1} x_{i+2} - x_i`. The positive Markoff triples `M` are
the points of `X(ℤ)` with positive coordinates; the moves preserve them, and the Markoff graph
joins two positive triples related by a move.

## Main definitions

* `TauCeti.markoffForm`: the polynomial `Φ(x) = x₀² + x₁² + x₂² - 3 x₀ x₁ x₂`.
* `TauCeti.markoffSet R`: the Markoff surface `X(R)`, the zero set of `Φ`.
* `TauCeti.markoffSetNonzero R`: its nonzero locus `X*(R) = X(R) ∖ {0}`.
* `TauCeti.markoffVieta i`: the Vieta move `R_i`, defined on all of `R³`.
* `TauCeti.positiveMarkoffTriples`: the ordered positive Markoff triples `M ⊆ ℤ³`.
* `TauCeti.markoffGraph`: the simple graph on `M` whose edges are the Vieta moves.

## Main results

* `TauCeti.markoffForm_markoffVieta`: the moves preserve `Φ`, over every commutative ring.
* `TauCeti.markoffVieta_involutive`: each move is an involution of `R³`.
* `TauCeti.bijOn_markoffVieta_markoffSetNonzero`: each move permutes `X*(R)`.
* `TauCeti.markoffVieta_comp_perm`: coordinate permutations normalise the moves.
* `TauCeti.markoffVieta_apply_self_mul_self`: the two roots in the moved coordinate multiply to
  `x_{i+1}² + x_{i+2}²`.
* `TauCeti.markoffVieta_mem_positiveMarkoffTriples_iff`: the moves preserve `M`, in both
  directions.

## References

* J. Bourgain, A. Gamburd and P. Sarnak, *Markoff surfaces and strong approximation: 1*,
  arXiv:1607.01530, §1.
* D. E. Martin, *A new proof of Chen's theorem for Markoff graphs*, §1, equations (1.1)–(1.2).
* Y. Zhang, *Congruence and uniqueness of certain Markoff numbers*, Acta Arith. 128 (2007), §1.
-/

public section

namespace TauCeti

open Finset

variable {R S : Type*} [CommRing R] [CommRing S]

/-! ### The Markoff form and the Markoff surface -/

/-- The Markoff form `Φ(x) = x₀² + x₁² + x₂² - 3 x₀ x₁ x₂` of a triple `x : Fin 3 → R`, written
symmetrically as `∑ i, x i ^ 2 - 3 * ∏ i, x i`. -/
def markoffForm (x : Fin 3 → R) : R :=
  ∑ i, x i ^ 2 - 3 * ∏ i, x i

/-- The Markoff form in coordinates. -/
theorem markoffForm_eq (x : Fin 3 → R) :
    markoffForm x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 3 * x 0 * x 1 * x 2 := by
  simp only [markoffForm, Fin.sum_univ_three, Fin.prod_univ_three]
  ring

/-- The Markoff form is symmetric. -/
@[simp]
theorem markoffForm_comp_perm (x : Fin 3 → R) (σ : Equiv.Perm (Fin 3)) :
    markoffForm (x ∘ σ) = markoffForm x := by
  simp only [markoffForm, Function.comp_apply, Equiv.sum_comp σ fun i => x i ^ 2,
    Equiv.prod_comp σ x]

/-- The Markoff form commutes with ring homomorphisms. -/
theorem markoffForm_comp_ringHom (x : Fin 3 → R) (f : R →+* S) :
    markoffForm (f ∘ x) = f (markoffForm x) := by
  simp [markoffForm, map_sum, map_prod, map_ofNat]

/-- The Markoff surface `X(R)`: the triples `x : Fin 3 → R` with
`x₀² + x₁² + x₂² = 3 x₀ x₁ x₂`. -/
def markoffSet (R : Type*) [CommRing R] : Set (Fin 3 → R) :=
  {x | markoffForm x = 0}

/-- A triple lies on the Markoff surface exactly when the Markoff form vanishes at it. -/
theorem mem_markoffSet_iff_markoffForm_eq_zero {x : Fin 3 → R} :
    x ∈ markoffSet R ↔ markoffForm x = 0 :=
  Iff.rfl

/-- A triple lies on the Markoff surface exactly when `x₀² + x₁² + x₂² = 3 x₀ x₁ x₂`. -/
theorem mem_markoffSet {x : Fin 3 → R} :
    x ∈ markoffSet R ↔ x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 3 * x 0 * x 1 * x 2 := by
  rw [mem_markoffSet_iff_markoffForm_eq_zero, markoffForm_eq, sub_eq_zero]

/-- The origin lies on the Markoff surface. -/
@[simp]
theorem zero_mem_markoffSet : (0 : Fin 3 → R) ∈ markoffSet R := by
  simp [mem_markoffSet]

/-- The triple `(1, 1, 1)` lies on the Markoff surface over every commutative ring. -/
@[simp]
theorem one_mem_markoffSet : (1 : Fin 3 → R) ∈ markoffSet R := by
  rw [mem_markoffSet]
  simp only [Pi.one_apply]
  ring

/-- Ring homomorphisms map the Markoff surface `X(R)` into `X(S)`. -/
theorem comp_mem_markoffSet {x : Fin 3 → R} (hx : x ∈ markoffSet R) (f : R →+* S) :
    f ∘ x ∈ markoffSet S := by
  rw [mem_markoffSet_iff_markoffForm_eq_zero, markoffForm_comp_ringHom,
    mem_markoffSet_iff_markoffForm_eq_zero.mp hx, map_zero]

/-- The Markoff surface is stable under coordinate permutations. -/
@[simp]
theorem comp_perm_mem_markoffSet_iff {x : Fin 3 → R} {σ : Equiv.Perm (Fin 3)} :
    x ∘ σ ∈ markoffSet R ↔ x ∈ markoffSet R := by
  simp only [mem_markoffSet_iff_markoffForm_eq_zero, markoffForm_comp_perm]

/-- The nonzero locus `X*(R) = X(R) ∖ {0}` of the Markoff surface. Nonzero refers to the whole
triple: individual coordinates of a point of `X*(R)` may vanish. -/
def markoffSetNonzero (R : Type*) [CommRing R] : Set (Fin 3 → R) :=
  markoffSet R \ {0}

/-- The points of `X*(R)` are the nonzero points of `X(R)`. -/
theorem mem_markoffSetNonzero {x : Fin 3 → R} :
    x ∈ markoffSetNonzero R ↔ x ∈ markoffSet R ∧ x ≠ 0 :=
  Set.mem_sdiff_singleton

/-- The nonzero locus is contained in the Markoff surface. -/
theorem markoffSetNonzero_subset_markoffSet : markoffSetNonzero R ⊆ markoffSet R :=
  Set.sdiff_subset

/-- The nonzero locus is stable under coordinate permutations. -/
@[simp]
theorem comp_perm_mem_markoffSetNonzero_iff {x : Fin 3 → R} {σ : Equiv.Perm (Fin 3)} :
    x ∘ σ ∈ markoffSetNonzero R ↔ x ∈ markoffSetNonzero R := by
  simp only [mem_markoffSetNonzero, comp_perm_mem_markoffSet_iff, ne_eq]
  refine and_congr_right fun _ => not_congr ⟨fun h => ?_, fun h => by rw [h]; rfl⟩
  ext i
  simpa using congrFun h (σ.symm i)

/-! ### The Vieta moves -/

/-- The Vieta move `R_i`: replace the `i`-th coordinate `x_i` of a triple by
`3 x_{i+1} x_{i+2} - x_i`, the other root of the Markoff equation viewed as a quadratic in that
coordinate, and keep the other two coordinates. It is defined on all of `R³`. -/
def markoffVieta (i : Fin 3) (x : Fin 3 → R) : Fin 3 → R :=
  Function.update x i (3 * x (i + 1) * x (i + 2) - x i)

/-- The Vieta move `R_i` replaces `x_i` by `3 x_{i+1} x_{i+2} - x_i`. -/
@[simp]
theorem markoffVieta_apply_self (i : Fin 3) (x : Fin 3 → R) :
    markoffVieta i x i = 3 * x (i + 1) * x (i + 2) - x i := by
  simp [markoffVieta]

/-- The Vieta move `R_i` keeps every coordinate other than the `i`-th. -/
@[simp]
theorem markoffVieta_apply_of_ne {i j : Fin 3} (h : j ≠ i) (x : Fin 3 → R) :
    markoffVieta i x j = x j := by
  simp [markoffVieta, h]

/-- The old and the new `i`-th coordinate are the two roots of a quadratic, so they sum to
`3 x_{i+1} x_{i+2}`. -/
theorem markoffVieta_apply_self_add_self (i : Fin 3) (x : Fin 3 → R) :
    markoffVieta i x i + x i = 3 * x (i + 1) * x (i + 2) := by
  simp

/-- A Vieta move changes the sum of the coordinates by the change in the moved coordinate. -/
theorem sum_markoffVieta (i : Fin 3) (x : Fin 3 → R) :
    ∑ j, markoffVieta i x j = ∑ j, x j + (markoffVieta i x i - x i) := by
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

/-- The Vieta moves fix the origin. -/
@[simp]
theorem markoffVieta_zero (i : Fin 3) : markoffVieta i (0 : Fin 3 → R) = 0 := by
  ext j
  rcases eq_or_ne j i with rfl | h <;> simp [*]

/-- The Vieta moves commute with ring homomorphisms. -/
theorem comp_markoffVieta (f : R →+* S) (i : Fin 3) (x : Fin 3 → R) :
    f ∘ markoffVieta i x = markoffVieta i (f ∘ x) := by
  ext j
  rcases eq_or_ne j i with rfl | h <;> simp [*, map_ofNat]

/-- Applying the same Vieta move twice gives back the original triple. -/
@[simp]
theorem markoffVieta_markoffVieta (i : Fin 3) (x : Fin 3 → R) :
    markoffVieta i (markoffVieta i x) = x := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · have h1 : j + 1 ≠ j := by fin_cases j <;> decide
    have h2 : j + 2 ≠ j := by fin_cases j <;> decide
    simp [h1, h2]
  · simp [h]

/-- Each Vieta move is an involution of `R³`, with no hypothesis on the ring or the triple. -/
theorem markoffVieta_involutive (i : Fin 3) : Function.Involutive (markoffVieta (R := R) i) :=
  markoffVieta_markoffVieta i

/-- Each Vieta move is injective. -/
@[simp]
theorem markoffVieta_inj {i : Fin 3} {x y : Fin 3 → R} :
    markoffVieta i x = markoffVieta i y ↔ x = y :=
  (markoffVieta_involutive i).injective.eq_iff

/-- A Vieta move sends a triple to the origin only if the triple is the origin. -/
@[simp]
theorem markoffVieta_eq_zero_iff {i : Fin 3} {x : Fin 3 → R} : markoffVieta i x = 0 ↔ x = 0 := by
  conv_lhs => rw [← markoffVieta_zero i]
  exact markoffVieta_inj

/-- The Vieta moves preserve the Markoff form. This is a polynomial identity, valid before
imposing the Markoff equation. -/
@[simp]
theorem markoffForm_markoffVieta (i : Fin 3) (x : Fin 3 → R) :
    markoffForm (markoffVieta i x) = markoffForm x := by
  fin_cases i <;> simp [markoffForm_eq, markoffVieta] <;> ring

/-- The Vieta moves preserve the Markoff surface, in both directions. -/
@[simp]
theorem markoffVieta_mem_markoffSet_iff {i : Fin 3} {x : Fin 3 → R} :
    markoffVieta i x ∈ markoffSet R ↔ x ∈ markoffSet R := by
  simp only [mem_markoffSet_iff_markoffForm_eq_zero, markoffForm_markoffVieta]

/-- The Vieta moves preserve the nonzero locus `X*(R)`, in both directions. -/
@[simp]
theorem markoffVieta_mem_markoffSetNonzero_iff {i : Fin 3} {x : Fin 3 → R} :
    markoffVieta i x ∈ markoffSetNonzero R ↔ x ∈ markoffSetNonzero R := by
  simp only [mem_markoffSetNonzero, markoffVieta_mem_markoffSet_iff, ne_eq,
    markoffVieta_eq_zero_iff]

/-- Each Vieta move restricts to a bijection of the nonzero locus `X*(R)`, which is its own
inverse by `markoffVieta_involutive`. -/
theorem bijOn_markoffVieta_markoffSetNonzero (i : Fin 3) :
    Set.BijOn (markoffVieta i) (markoffSetNonzero R) (markoffSetNonzero R) :=
  Set.InvOn.bijOn
    ⟨fun x _ => markoffVieta_markoffVieta i x, fun x _ => markoffVieta_markoffVieta i x⟩
    (fun _ hx => markoffVieta_mem_markoffSetNonzero_iff.mpr hx)
    (fun _ hx => markoffVieta_mem_markoffSetNonzero_iff.mpr hx)

/-- Coordinate permutations normalise the Vieta moves: with `P_σ x = x ∘ σ⁻¹`, so that
`(P_σ x) (σ i) = x i`, one has `P_σ ∘ R_i = R_{σ i} ∘ P_σ`. -/
theorem markoffVieta_comp_perm (σ : Equiv.Perm (Fin 3)) (i : Fin 3) (x : Fin 3 → R) :
    markoffVieta (σ i) (x ∘ σ.symm) = markoffVieta i x ∘ σ.symm := by
  ext j
  rcases eq_or_ne j (σ i) with rfl | h
  · -- The two coordinates other than `σ i` are pulled back to the two coordinates other than `i`.
    have key : ∀ (τ : Equiv.Perm (Fin 3)) (k : Fin 3),
        (τ.symm (τ k + 1) = k + 1 ∧ τ.symm (τ k + 2) = k + 2) ∨
          (τ.symm (τ k + 1) = k + 2 ∧ τ.symm (τ k + 2) = k + 1) := by
      decide
    rcases key σ i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2, mul_right_comm]
  · have h' : σ.symm j ≠ i := fun hj => h (by rw [← hj, Equiv.apply_symm_apply])
    simp [h, h']

/-- If `x` lies on the Markoff surface, the two roots in the `i`-th coordinate multiply to
`x_{i+1}² + x_{i+2}²` (Vieta's formula for the constant term). -/
theorem markoffVieta_apply_self_mul_self {x : Fin 3 → R} (hx : x ∈ markoffSet R) (i : Fin 3) :
    markoffVieta i x i * x i = x (i + 1) ^ 2 + x (i + 2) ^ 2 := by
  rw [mem_markoffSet] at hx
  fin_cases i <;> simp <;> linear_combination -hx

/-! ### Positive Markoff triples and the Markoff graph -/

/-- The positive Markoff triples `M`: the integer points of the Markoff surface all of whose
coordinates are positive, kept as ordered triples. -/
def positiveMarkoffTriples : Set (Fin 3 → ℤ) :=
  {x | x ∈ markoffSet ℤ ∧ ∀ i, 0 < x i}

/-- A positive Markoff triple is a point of `X(ℤ)` with positive coordinates. -/
theorem mem_positiveMarkoffTriples {x : Fin 3 → ℤ} :
    x ∈ positiveMarkoffTriples ↔ x ∈ markoffSet ℤ ∧ ∀ i, 0 < x i :=
  Iff.rfl

/-- Positive Markoff triples lie on the Markoff surface. -/
theorem positiveMarkoffTriples_subset_markoffSet : positiveMarkoffTriples ⊆ markoffSet ℤ :=
  fun _ hx => hx.1

/-- Positive Markoff triples lie in the nonzero locus `X*(ℤ)`. -/
theorem positiveMarkoffTriples_subset_markoffSetNonzero :
    positiveMarkoffTriples ⊆ markoffSetNonzero ℤ := fun x hx =>
  mem_markoffSetNonzero.mpr ⟨hx.1, fun h => (hx.2 0).ne' (by simp [h])⟩

/-- The positive Markoff triple `(1, 1, 1)`. -/
@[simp]
theorem one_mem_positiveMarkoffTriples : (1 : Fin 3 → ℤ) ∈ positiveMarkoffTriples :=
  ⟨one_mem_markoffSet, fun _ => one_pos⟩

/-- The positive Markoff triples are stable under coordinate permutations. -/
@[simp]
theorem comp_perm_mem_positiveMarkoffTriples_iff {x : Fin 3 → ℤ} {σ : Equiv.Perm (Fin 3)} :
    x ∘ σ ∈ positiveMarkoffTriples ↔ x ∈ positiveMarkoffTriples := by
  simp only [mem_positiveMarkoffTriples, comp_perm_mem_markoffSet_iff, Function.comp_apply]
  exact and_congr_right fun _ => σ.forall_congr_right (q := fun i => 0 < x i)

/-- Positive Markoff triples are the triples of positive natural numbers `(a, b, c)` with
`a² + b² + c² = 3abc`; the equation has no subtraction, so it can be read in `ℕ`. -/
theorem mem_positiveMarkoffTriples_iff_nat {x : Fin 3 → ℤ} :
    x ∈ positiveMarkoffTriples ↔ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c ∧ x = ![(a : ℤ), b, c] := by
  constructor
  · rintro ⟨hx, hpos⟩
    rw [mem_markoffSet] at hx
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (hpos 0).le
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (hpos 1).le
    obtain ⟨c, hc⟩ := Int.eq_ofNat_of_zero_le (hpos 2).le
    rw [ha, hb, hc] at hx
    refine ⟨a, b, c, by simpa [ha] using hpos 0, by simpa [hb] using hpos 1,
      by simpa [hc] using hpos 2, by exact_mod_cast hx, ?_⟩
    ext i
    fin_cases i <;> simp [ha, hb, hc]
  · rintro ⟨a, b, c, ha, hb, hc, h, rfl⟩
    refine ⟨mem_markoffSet.mpr (by simpa using congrArg (Nat.cast : ℕ → ℤ) h), fun i => ?_⟩
    fin_cases i <;> simpa

/-- The Vieta moves preserve the positive Markoff triples: the new coordinate
`3 x_{i+1} x_{i+2} - x_i` is positive, because its product with `x_i > 0` is
`x_{i+1}² + x_{i+2}² > 0`. -/
theorem markoffVieta_mem_positiveMarkoffTriples {x : Fin 3 → ℤ}
    (hx : x ∈ positiveMarkoffTriples) (i : Fin 3) :
    markoffVieta i x ∈ positiveMarkoffTriples := by
  refine ⟨markoffVieta_mem_markoffSet_iff.mpr hx.1, fun j => ?_⟩
  rcases eq_or_ne j i with rfl | h
  · have hmul := markoffVieta_apply_self_mul_self hx.1 j
    have hsq : 0 < x (j + 1) ^ 2 + x (j + 2) ^ 2 := by
      have := hx.2 (j + 1)
      positivity
    exact pos_of_mul_pos_left (hmul ▸ hsq) (hx.2 j).le
  · rw [markoffVieta_apply_of_ne h]
    exact hx.2 j

/-- The Vieta moves preserve the positive Markoff triples, in both directions. -/
@[simp]
theorem markoffVieta_mem_positiveMarkoffTriples_iff {i : Fin 3} {x : Fin 3 → ℤ} :
    markoffVieta i x ∈ positiveMarkoffTriples ↔ x ∈ positiveMarkoffTriples :=
  ⟨fun h => markoffVieta_markoffVieta i x ▸ markoffVieta_mem_positiveMarkoffTriples h i,
    fun h => markoffVieta_mem_positiveMarkoffTriples h i⟩

/-- The integer Markoff graph: the simple graph on the positive Markoff triples in which `x` and
`y` are adjacent when they are distinct and `y` is obtained from `x` by a Vieta move. -/
def markoffGraph : SimpleGraph positiveMarkoffTriples :=
  SimpleGraph.fromRel fun x y => ∃ i, markoffVieta i x.1 = y.1

/-- Two positive Markoff triples are adjacent in the Markoff graph exactly when they are distinct
and related by a Vieta move. Adjacency is symmetric because the moves are involutions. -/
theorem markoffGraph_adj {x y : positiveMarkoffTriples} :
    markoffGraph.Adj x y ↔ x ≠ y ∧ ∃ i, markoffVieta i x.1 = y.1 := by
  rw [markoffGraph, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => or_iff_left_of_imp ?_
  rintro ⟨i, hi⟩
  exact ⟨i, by rw [← hi, markoffVieta_markoffVieta]⟩

end TauCeti
