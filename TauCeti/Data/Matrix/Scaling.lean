/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Instances.Matrix

/-!
# The entropy minimiser with prescribed marginals

Let `K` be a matrix with no zero entry, and let `a` and `b` be strictly positive vectors indexed by
the rows and by the columns of `K`. This file proves that among the nonnegative matrices with row
sums `a` and column sums `b` the relative entropy against `K` is minimised, and that every such
minimiser has strictly positive entries.

`Matrix.IsDiagonalScaling K u v P` records the shape of the minimiser described by the later steps
of this development: `P i j = u i * K i j * v j` for row factors `u` and column factors `v`, that is
a diagonal scaling of `K`.

The marginals here are arbitrary vectors of equal total mass, not probability distributions, and
the matrices are real: this is the setting of a diagonal scaling of a kernel, where the scaled
matrix has total mass `∑ i, a i` and is compared against the real kernel `K`. A probability-valued
plan with `PMF` marginals is `TauCeti.TransportMatrix`.

## Main definitions

* `Matrix.IsDiagonalScaling K u v P`: `P i j = u i * K i j * v j` for all `i` and `j`.
* `Matrix.HasMarginals a b P`: the row sums of `P` are `a` and its column sums are `b`.
* `Matrix.relEntropy P K`: the sum over `i`, `j` of `P i j * (log (P i j) - log (K i j))`.

## Main results

* `Matrix.exists_relEntropy_minOn`: a minimiser of `Matrix.relEntropy` against `K` among the
  matrices with row sums `a` and column sums `b` exists.
* `Matrix.pos_of_relEntropy_minOn`: every such minimiser has strictly positive entries.
-/
public section

open scoped BigOperators

namespace Matrix

variable {n m : ℕ}

/-! ### Marginals and diagonal scalings -/

/-- `P` is a nonnegative matrix whose row sums are `a` and whose column sums are `b`. -/
def HasMarginals (a : Fin n → ℝ) (b : Fin m → ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j)

/-- `P` is the diagonal scaling of `K` by the row factors `u` and the column factors `v`. -/
def IsDiagonalScaling (K : Matrix (Fin n) (Fin m) ℝ) (u : Fin n → ℝ) (v : Fin m → ℝ)
    (P : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ i j, P i j = u i * K i j * v j

theorem isDiagonalScaling_apply {K : Matrix (Fin n) (Fin m) ℝ} {u : Fin n → ℝ}
    {v : Fin m → ℝ} {P : Matrix (Fin n) (Fin m) ℝ} (h : IsDiagonalScaling K u v P) (i : Fin n)
    (j : Fin m) : P i j = u i * K i j * v j :=
  h i j

theorem IsDiagonalScaling.hasMarginals {K : Matrix (Fin n) (Fin m) ℝ} {u : Fin n → ℝ}
    {v : Fin m → ℝ} {P : Matrix (Fin n) (Fin m) ℝ} (h : IsDiagonalScaling K u v P)
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, (∑ j, u i * K i j * v j) = a i) (hb : ∀ j, (∑ i, u i * K i j * v j) = b j) :
    HasMarginals a b P := by
  have hP : P = fun i j => u i * K i j * v j := funext fun i => funext fun j => h i j
  constructor
  · intro i
    rw [hP]
    exact ha i
  · intro j
    rw [hP]
    exact hb j

theorem IsDiagonalScaling.smul {K : Matrix (Fin n) (Fin m) ℝ} {u : Fin n → ℝ} {v : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (h : IsDiagonalScaling K u v P) {r : ℝ} (hr : r ≠ 0) :
    IsDiagonalScaling K (fun i => r * u i) (fun j => r⁻¹ * v j) P := by
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  intro i j
  simp only []
  calc P i j = u i * K i j * v j := h i j
    _ = (u i * K i j * v j) * (r * r⁻¹) := by rw [hrr]; ring
    _ = r * u i * K i j * (r⁻¹ * v j) := by ring

/-! ### The relative entropy of a matrix against a kernel -/

/-- `Matrix.relEntropy P K` is the relative entropy of the nonnegative matrix `P` against the
strictly positive matrix `K`, that is the sum over `i`, `j` of
`P i j * (log (P i j) - log (K i j))` with the convention `0 * log 0 = 0`.

Writing `A = ∑ i j, P i j` and `B = ∑ i j, K i j`, it is `A` times the relative entropy of the
probability distributions `P i j / A` and `K i j / B`, up to the additive constant
`A * (log A - log B)`. Two matrices of equal total mass that differ by that constant are compared
the same way by an optimisation against `K`. -/
noncomputable def relEntropy (P K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, (P i j * Real.log (P i j) - P i j * Real.log (K i j))

private lemma continuous_relEntropy (K : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (relEntropy · K) := by
  unfold relEntropy
  fun_prop

/-! ### A minimiser of the relative entropy -/

theorem exists_relEntropy_minOn [NeZero n] (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ)
    (b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) (hmass : (∑ i, a i) = ∑ j, b j) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals a b P ∧
      ∀ Q : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals a b Q →
        relEntropy P K ≤ relEntropy Q K := by
  have hApos : 0 < ∑ i, a i := Finset.sum_pos (fun i _ => ha i) ⟨0, Finset.mem_univ _⟩
  set A := ∑ i, a i with hA
  have hA0 : A ≠ 0 := ne_of_gt hApos
  have hP₀ : (∀ i j, 0 ≤ (fun i j => a i * (b j * A⁻¹)) i j) ∧
      HasMarginals a b (fun i j => a i * (b j * A⁻¹)) := by
    constructor
    · intro i j
      change 0 ≤ a i * (b j * A⁻¹)
      exact mul_nonneg (le_of_lt (ha i)) (mul_nonneg (le_of_lt (hb j)) (inv_nonneg.mpr hApos.le))
    · constructor
      · intro i
        calc ∑ j, a i * (b j * A⁻¹) = a i * ∑ j, (b j * A⁻¹) := by rw [Finset.mul_sum]
          _ = a i * ((∑ j, b j) * A⁻¹) := by rw [← Finset.sum_mul]
          _ = a i * (A * A⁻¹) := by rw [← hmass]
          _ = a i := by rw [mul_inv_cancel₀ hA0, mul_one]
      · intro j
        calc ∑ i, a i * (b j * A⁻¹) = (∑ i, a i) * (b j * A⁻¹) := by rw [Finset.sum_mul]
          _ = A * (b j * A⁻¹) := by rw [hA]
          _ = b j * (A * A⁻¹) := by ring
          _ = b j := by rw [mul_inv_cancel₀ hA0, mul_one]
  have hnonneg : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i j, 0 ≤ P i j} := by
    have key : {P : Matrix (Fin n) (Fin m) ℝ | ∀ i j, 0 ≤ P i j}
        = ⋂ i : Fin n, ⋂ j : Fin m, {P : Matrix (Fin n) (Fin m) ℝ | 0 ≤ P i j} := by
      ext P
      simp only [Set.mem_iInter, Set.mem_ofPred]
    rw [key]
    exact isClosed_iInter fun i : Fin n => isClosed_iInter fun j : Fin m =>
      isClosed_le (f := fun _ => (0 : ℝ)) (g := fun P : Matrix (Fin n) (Fin m) ℝ => P i j)
        continuous_const (by fun_prop)
  have hrows : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i : Fin n, (∑ j, P i j) = a i} := by
    have key : {P : Matrix (Fin n) (Fin m) ℝ | ∀ i : Fin n, (∑ j, P i j) = a i}
        = ⋂ i : Fin n, {P : Matrix (Fin n) (Fin m) ℝ | (∑ j, P i j) = a i} := by
      ext P
      simp only [Set.mem_iInter, Set.mem_ofPred]
    rw [key]
    exact isClosed_iInter fun i : Fin n =>
      isClosed_eq (f := fun P : Matrix (Fin n) (Fin m) ℝ => ∑ j, P i j) (g := fun _ => a i)
        (by fun_prop) continuous_const
  have hcols : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ j : Fin m, (∑ i, P i j) = b j} := by
    have key : {P : Matrix (Fin n) (Fin m) ℝ | ∀ j : Fin m, (∑ i, P i j) = b j}
        = ⋂ j : Fin m, {P : Matrix (Fin n) (Fin m) ℝ | (∑ i, P i j) = b j} := by
      ext P
      simp only [Set.mem_iInter, Set.mem_ofPred]
    rw [key]
    exact isClosed_iInter fun j : Fin m =>
      isClosed_eq (f := fun P : Matrix (Fin n) (Fin m) ℝ => ∑ i, P i j) (g := fun _ => b j)
        (by fun_prop) continuous_const
  set S : Set (Matrix (Fin n) (Fin m) ℝ) :=
    {P | (∀ i j, 0 ≤ P i j) ∧ HasMarginals a b P} with hS
  have hclosed : IsClosed S := by
    rw [hS]
    exact hnonneg.inter (hrows.inter hcols)
  have hbound : ∀ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) → HasMarginals a b P →
      ∀ i j, P i j ≤ A := by
    intro P hP0 hPa i j
    exact (Finset.single_le_sum (fun k _ => hP0 i k) (Finset.mem_univ j)).trans
      ((hPa.1 i).le.trans (Finset.single_le_sum (fun k _ => (ha k).le) (Finset.mem_univ i)))
  have hbox : IsCompact {P : Matrix (Fin n) (Fin m) ℝ | ∀ i j, P i j ∈ Set.Icc 0 A} :=
    IsCompact.matrix (isCompact_Icc (α := ℝ))
  have hcompact : IsCompact S :=
    IsCompact.of_isClosed_subset hbox hclosed
      fun P hP => fun i j => ⟨hP.1 i j, hbound P hP.1 hP.2 i j⟩
  obtain ⟨P, hPmem, hPmin⟩ := hcompact.exists_isMinOn (f := fun P => relEntropy P K)
    ⟨fun i j => a i * (b j * A⁻¹), hP₀⟩ (continuous_relEntropy K).continuousOn
  rw [hS, Set.mem_ofPred] at hPmem
  have hPmin' : ∀ Q : Matrix (Fin n) (Fin m) ℝ, Q ∈ S → relEntropy P K ≤ relEntropy Q K := hPmin
  exact ⟨P, hPmem.1, hPmem.2, fun Q hQ hQ' => hPmin' Q ⟨hQ, hQ'⟩⟩

/-- The supporting-line inequality for the convex function `u ↦ u * Real.log u` on the nonnegative
reals: the tangent line at the positive point `a` lies below the graph at every nonnegative `u`. -/
private lemma mul_log_sub_mul_log_ge (a u : ℝ) (ha : 0 < a) (hu : 0 ≤ u) :
    u * Real.log u - a * Real.log a ≥ (u - a) * (Real.log a + 1) := by
  rcases lt_or_eq_of_le hu with hu' | hu0
  · have key : u * Real.log u - a * Real.log a - (u - a) * (Real.log a + 1)
        = a * ((u / a) * Real.log (u / a) - (u / a - 1)) := by
      rw [Real.log_div (x := u) (y := a) hu'.ne' ha.ne']
      field_simp
      ring
    have h1 : 0 ≤ (u / a) * Real.log (u / a) - (u / a - 1) :=
      sub_nonneg.mpr (Real.self_sub_one_le_mul_log (le_of_lt (div_pos hu' ha)))
    have h2 := mul_nonneg (le_of_lt ha) h1
    linarith
  · subst hu0
    simp only [Real.log_zero, zero_mul]
    linarith

/-- The sum of the difference of the indicator matrices of `i` and `i'` against a function of the
row index is the difference of the values of the function at `i` and `i'`. -/
private lemma sum_sub_indicator_mul (i i' : Fin n) (g : Fin n → ℝ) :
    ∑ x, ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) * g x = g i - g i' := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, one_mul, Fintype.sum_ite_eq']

/-- The sum of the difference of the indicator matrices of `j` and `j'` against a function is
the difference of the values of the function at `j` and `j'`. -/
private lemma sum_sub_indicator_mul' (j j' : Fin m) (g : Fin m → ℝ) :
    ∑ y, ((if y = j then 1 else 0) - (if y = j' then 1 else 0)) * g y = g j - g j' := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, one_mul, Fintype.sum_ite_eq']

private lemma sum_sub_eq_sum_sub (f g : Fin n → Fin m → ℝ) :
    (∑ x, ∑ y, f x y) - ∑ x, ∑ y, g x y = ∑ x, ∑ y, (f x y - g x y) := by
  calc (∑ x, ∑ y, f x y) - ∑ x, ∑ y, g x y
      = ∑ x, (∑ y, f x y - ∑ y, g x y) := by rw [← Finset.sum_sub_distrib]
    _ = ∑ x, ∑ y, (f x y - g x y) := by
      refine Fintype.sum_congr _ _ fun x => ?_
      rw [← Finset.sum_sub_distrib]

/-- The double sum of the product of the two indicator differences against a function of both
indices is the alternating sum of the values at the four cells of the two rectangles. -/
private lemma sum_sub_indicator_prod (g : Fin n → Fin m → ℝ) (i i' : Fin n) (j j' : Fin m) :
    ∑ x, ∑ y, ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) *
      ((if y = j then 1 else 0) - (if y = j' then 1 else 0)) * g x y
      = g i j - g i j' - g i' j + g i' j' := by
  have h1 : ∀ x : Fin n, ∑ y, ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) *
      ((if y = j then 1 else 0) - (if y = j' then 1 else 0)) * g x y
      = ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) * (g x j - g x j') := by
    intro x
    have hrw : (fun y => ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) *
        ((if y = j then 1 else 0) - (if y = j' then 1 else 0)) * g x y)
        = fun y => ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) *
          (((if y = j then 1 else 0) - (if y = j' then 1 else 0)) * g x y) := by
      funext y; ring
    rw [hrw, ← Finset.mul_sum, sum_sub_indicator_mul']
  calc ∑ x, ∑ y, _ = ∑ x, ((if x = i then 1 else 0) - (if x = i' then 1 else 0))
      * (g x j - g x j') := Finset.sum_congr rfl fun x _ => h1 x
    _ = g i j - g i j' - g i' j + g i' j' := by
        simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, one_mul, Fintype.sum_ite_eq']
        ring

/-- The double sum of the indicator matrix of a single cell against a function of both indices is
the value of the function at that cell. -/
private lemma sum_ite_and (g : Fin n → Fin m → ℝ) (i : Fin n) (j : Fin m) :
    (∑ x, ∑ y, ((if x = i ∧ y = j then 1 else 0 : ℝ)) * g x y) = g i j := by
  calc (∑ x, ∑ y, ((if x = i ∧ y = j then 1 else 0 : ℝ)) * g x y)
      = ∑ x, ∑ y, (if x = i ∧ y = j then g x y else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Finset.sum_congr rfl fun y _ => ?_
        split_ifs <;> simp
    _ = ∑ x, (if x = i then g x j else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        by_cases h : x = i <;> simp [h]
    _ = g i j := Fintype.sum_ite_eq' i fun x => g x j

/-- A function that vanishes outside the four cells of a rectangle has total sum equal to the
sum of its values at those four cells. -/
private lemma sum_four_ite (g : Fin n → Fin m → ℝ) (i i' : Fin n) (j j' : Fin m)
    (hi'ne : i ≠ i') (hj'ne : j ≠ j')
    (h0 : ∀ x y, (x ≠ i ∨ y ≠ j) → (x ≠ i ∨ y ≠ j') → (x ≠ i' ∨ y ≠ j)
      → (x ≠ i' ∨ y ≠ j') → g x y = 0) :
    (∑ x, ∑ y, g x y) = g i j + g i j' + g i' j + g i' j' := by
  have e1 : (∑ x, ∑ y, ((if x = i ∧ y = j then 1 else 0 : ℝ)) * g x y) = g i j := sum_ite_and g i j
  have e2 : (∑ x, ∑ y, ((if x = i ∧ y = j' then 1 else 0 : ℝ)) * g x y) = g i j' :=
    sum_ite_and g i j'
  have e3 : (∑ x, ∑ y, ((if x = i' ∧ y = j then 1 else 0 : ℝ)) * g x y) = g i' j :=
    sum_ite_and g i' j
  have e4 : (∑ x, ∑ y, ((if x = i' ∧ y = j' then 1 else 0 : ℝ)) * g x y) = g i' j' :=
    sum_ite_and g i' j'
  calc (∑ x, ∑ y, g x y)
      = ∑ x, ∑ y, ((if x = i ∧ y = j then 1 else 0) + (if x = i ∧ y = j' then 1 else 0)
        + (if x = i' ∧ y = j then 1 else 0) + (if x = i' ∧ y = j' then 1 else 0)) * g x y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h1 : x = i <;> by_cases h2 : y = j <;> by_cases h3 : x = i'
          <;> by_cases h4 : y = j' <;> simp_all
    _ = g i j + g i j' + g i' j + g i' j' := by
        have split : (∑ x, ∑ y, ((if x = i ∧ y = j then 1 else 0)
              + (if x = i ∧ y = j' then 1 else 0) + (if x = i' ∧ y = j then 1 else 0)
              + (if x = i' ∧ y = j' then 1 else 0)) * g x y)
            = (∑ x, ∑ y, ((if x = i ∧ y = j then 1 else 0 : ℝ)) * g x y)
              + (∑ x, ∑ y, ((if x = i ∧ y = j' then 1 else 0 : ℝ)) * g x y)
              + (∑ x, ∑ y, ((if x = i' ∧ y = j then 1 else 0 : ℝ)) * g x y)
              + (∑ x, ∑ y, ((if x = i' ∧ y = j' then 1 else 0 : ℝ)) * g x y) := by
          simp only [add_mul, Finset.sum_add_distrib]
        rw [split, e1, e2, e3, e4]

/-- A minimiser of `relEntropy` against a matrix with no zero entry has no zero entry: moving a
sufficiently small positive amount of mass into a zero entry, taken from one entry of the same row
and one entry of the same column, preserves the marginals and decreases the relative entropy. -/
theorem pos_of_relEntropy_minOn (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) {P : Matrix (Fin n) (Fin m) ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPa : HasMarginals a b P)
    (hmin : ∀ Q : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals a b Q →
      relEntropy P K ≤ relEntropy Q K) :
    ∀ i j, 0 < P i j := by
  by_contra hzero
  push Not at hzero
  obtain ⟨i, j, hij⟩ := hzero
  have hij0 : P i j = 0 := le_antisymm hij (hP i j)
  obtain ⟨j', hj'pos, hj'ne⟩ : ∃ j' : Fin m, 0 < P i j' ∧ j' ≠ j := by
    have key : ∃ y, 0 < P i y := by
      by_contra hcon
      push Not at hcon
      have h1 : (∑ y, P i y) ≤ 0 := Finset.sum_nonpos fun y _ => hcon y
      rw [hPa.1 i] at h1
      exact absurd h1 (not_le_of_gt (ha i))
    obtain ⟨j'', hj''⟩ := key
    have hj''ne : j'' ≠ j := by
      intro h
      rw [h] at hj''
      rw [hij0] at hj''
      exact absurd hj'' (lt_irrefl _)
    exact ⟨j'', hj'', hj''ne⟩
  obtain ⟨i', hi'pos, hi'ne⟩ : ∃ i' : Fin n, 0 < P i' j ∧ i' ≠ i := by
    have key : ∃ x, 0 < P x j := by
      by_contra hcon
      push Not at hcon
      have h1 : (∑ x, P x j) ≤ 0 := Finset.sum_nonpos fun x _ => hcon x
      rw [hPa.2 j] at h1
      exact absurd h1 (not_le_of_gt (hb j))
    obtain ⟨i'', hi''⟩ := key
    have hi''ne : i'' ≠ i := by
      intro h
      rw [h] at hi''
      rw [hij0] at hi''
      exact absurd hi'' (lt_irrefl _)
    exact ⟨i'', hi'', hi''ne⟩
  have hi'ne' : i ≠ i' := fun h => hi'ne h.symm
  have hj'ne' : j ≠ j' := fun h => hj'ne h.symm
  set y : ℝ := P i j' with hy
  set z : ℝ := P i' j with hz
  set q : ℝ := P i' j' with hq
  have hy0 : 0 < y := by rw [hy]; exact hj'pos
  have hz0 : 0 < z := by rw [hz]; exact hi'pos
  have hq0 : 0 ≤ q := by rw [hq]; exact hP i' j'
  set r : Fin n → ℝ := fun x => (if x = i then 1 else 0) - (if x = i' then 1 else 0) with hr
  set c : Fin m → ℝ := fun y => (if y = j then 1 else 0) - (if y = j' then 1 else 0) with hc
  set D : Fin n → Fin m → ℝ := fun x y => r x * c y with hD
  have hDrw : ∀ x y, r x * c y = D x y := by
    intro x y
    rfl
  have hri : r i = 1 := by rw [hr]; simp [hi'ne']
  have hri' : r i' = -1 := by rw [hr]; simp [hi'ne]
  have hcj : c j = 1 := by rw [hc]; simp [hj'ne']
  have hcj' : c j' = -1 := by rw [hc]; simp [hj'ne]
  have hDzero : ∀ x y, (x ≠ i ∨ y ≠ j) → (x ≠ i ∨ y ≠ j') → (x ≠ i' ∨ y ≠ j) → (x ≠ i' ∨ y ≠ j') →
      D x y = 0 := by
    intro x y h1 h2 h3 h4
    by_cases hx : x = i <;> by_cases hx' : x = i' <;> by_cases hy : y = j
      <;> by_cases hy' : y = j' <;> simp_all
  have hDrow : ∀ x, ∑ y, D x y = 0 := by
    intro x
    calc (∑ y, D x y) = r x * ∑ y, c y := by rw [hD, Finset.mul_sum]
      _ = 0 := by
        rw [Fintype.sum_congr _ _ (fun y => (mul_one (c y)).symm), hc,
          sum_sub_indicator_mul' j j' (fun _ => (1 : ℝ)), sub_self, mul_zero]
  have hDcol : ∀ y, ∑ x, D x y = 0 := by
    intro y
    have hrw : ∀ x, D x y = c y * r x := by
      intro x
      rw [hD]
      ring
    calc (∑ x, D x y) = ∑ x, c y * r x := Fintype.sum_congr _ _ hrw
      _ = c y * ∑ x, r x := by rw [Finset.mul_sum]
      _ = 0 := by
        rw [Fintype.sum_congr _ _ (fun x => (mul_one (r x)).symm), hr,
          sum_sub_indicator_mul i i' (fun _ => (1 : ℝ)), sub_self, mul_zero]
  set Q : ℝ → Matrix (Fin n) (Fin m) ℝ := fun t x y => P x y + t * D x y with hQ
  have hQcell : ∀ t x y, Q t x y = P x y + t * (r x * c y) := by
    intro t x y
    rw [hQ, hD]
  have hrAt : ∀ x, x = i → r x = 1 := by
    intro x h
    rw [hr]
    simp [h, hi'ne']
  have hrAt' : ∀ x, x = i' → r x = -1 := by
    intro x h
    rw [hr]
    simp [h, hi'ne]
  have hrOff : ∀ x, x ≠ i → x ≠ i' → r x = 0 := by
    intro x h h'
    rw [hr]
    simp [h, h']
  have hcAt : ∀ y, y = j → c y = 1 := by
    intro y h
    rw [hc]
    simp [h, hj'ne']
  have hcAt' : ∀ y, y = j' → c y = -1 := by
    intro y h
    rw [hc]
    simp [h, hj'ne]
  have hcOff : ∀ y, y ≠ j → y ≠ j' → c y = 0 := by
    intro y h h'
    rw [hc]
    simp [h, h']
  have hQnonneg : ∀ t, 0 ≤ t → t ≤ min y z → ∀ (u : Fin n) (v : Fin m), 0 ≤ Q t u v := by
    intro t ht0 ht u v
    have ht' : t ≤ y := le_trans ht (min_le_left _ _)
    have ht'' : t ≤ z := le_trans ht (min_le_right _ _)
    by_cases h1 : u = i
    · by_cases h2 : v = j
      · rw [hQcell, hrAt u h1, hcAt v h2, h1, h2, hij0]
        linarith
      · by_cases h3 : v = j'
        · rw [hQcell, hrAt u h1, hcAt' v h3, h1, h3]
          have key := hP i j'
          linarith
        · rw [hQcell, hrAt u h1, hcOff v h2 h3, h1]
          have key := hP i v
          linarith
    · by_cases h3 : u = i'
      · by_cases h2 : v = j
        · rw [hQcell, hrAt' u h3, hcAt v h2, h3, h2]
          have key := hP i' j
          linarith
        · by_cases h4 : v = j'
          · rw [hQcell, hrAt' u h3, hcAt' v h4, h3, h4]
            have key := hP i' j'
            linarith
          · rw [hQcell, hrAt' u h3, hcOff v h2 h4, h3]
            have key := hP i' v
            linarith
      · by_cases h2 : v = j
        · rw [hQcell, hrOff u h1 h3, hcAt v h2]
          have key := hP u v
          linarith
        · by_cases h4 : v = j'
          · rw [hQcell, hrOff u h1 h3, hcAt' v h4]
            have key := hP u v
            linarith
          · rw [hQcell, hrOff u h1 h3, hcOff v h2 h4]
            have key := hP u v
            linarith
  have hQmarg : ∀ t, HasMarginals a b (Q t) := by
    intro t
    constructor
    · intro x
      have h1 : (∑ y, Q t x y) = ∑ y, P x y := by
        rw [hQ, Finset.sum_add_distrib, ← Finset.mul_sum, hDrow x]
        simp
      rw [h1]
      exact hPa.1 x
    · intro y
      have h1 : (∑ x, Q t x y) = ∑ x, P x y := by
        rw [hQ, Finset.sum_add_distrib, ← Finset.mul_sum, hDcol y]
        simp
      rw [h1]
      exact hPa.2 y
  have hrelDiff (t : ℝ) :
      relEntropy (Q t) K - relEntropy P K
        = ((P i j + t) * Real.log (P i j + t) - P i j * Real.log (P i j)
          + (P i j' - t) * Real.log (P i j' - t) - P i j' * Real.log (P i j')
          + (P i' j - t) * Real.log (P i' j - t) - P i' j * Real.log (P i' j)
          + (P i' j' + t) * Real.log (P i' j' + t) - P i' j' * Real.log (P i' j'))
        - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
    have hQ1 : Q t i j = P i j + t := by rw [hQcell, hri, hcj]; ring
    have hQ2 : Q t i j' = P i j' - t := by rw [hQcell, hri, hcj']; ring
    have hQ3 : Q t i' j = P i' j - t := by rw [hQcell, hri', hcj]; ring
    have hQ4 : Q t i' j' = P i' j' + t := by rw [hQcell, hri', hcj']; ring
    unfold relEntropy
    set φ : Fin n → Fin m → ℝ := fun x y =>
      Q t x y * Real.log (Q t x y) - P x y * Real.log (P x y) with hφ
    have hφ0 : ∀ x y, (x ≠ i ∨ y ≠ j) → (x ≠ i ∨ y ≠ j') → (x ≠ i' ∨ y ≠ j) →
        (x ≠ i' ∨ y ≠ j') → φ x y = 0 := by
      intro x y h1 h2 h3 h4
      have hD0 : D x y = 0 := hDzero x y h1 h2 h3 h4
      rw [hφ]
      dsimp only
      rw [hQcell, hDrw, hD0, mul_zero, add_zero]
      ring_nf
    have hφsum : (∑ x, ∑ y, φ x y) = φ i j + φ i j' + φ i' j + φ i' j' :=
      sum_four_ite φ i i' j j' hi'ne' hj'ne' hφ0
    have hd'' : ∀ x y, D x y = ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) *
        ((if y = j then 1 else 0) - (if y = j' then 1 else 0)) := by
      intro x y
      rfl
    have hKsum : (∑ x, ∑ y, ((Q t x y - P x y) * Real.log (K x y)))
        = (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j) + Real.log (K i' j')) * t := by
      calc (∑ x, ∑ y, ((Q t x y - P x y) * Real.log (K x y)))
          = ∑ x, ∑ y, (D x y) * (t * Real.log (K x y)) := by
            refine Fintype.sum_congr _ _ fun x => Fintype.sum_congr _ _ fun y => ?_
            rw [hQcell]
            ring
        _ = ∑ x, ∑ y, ((if x = i then 1 else 0) - (if x = i' then 1 else 0)) *
            ((if y = j then 1 else 0) - (if y = j' then 1 else 0)) * (t * Real.log (K x y)) := by
          refine Fintype.sum_congr _ _ fun x => ?_
          refine Fintype.sum_congr _ _ fun y => ?_
          rw [hd'' x y]
        _ = (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
            + Real.log (K i' j')) * t := by
          rw [sum_sub_indicator_prod (fun x y => t * Real.log (K x y)) i i' j j']
          ring
    calc relEntropy (Q t) K - relEntropy P K
        = (∑ x, ∑ y, φ x y) - ∑ x, ∑ y, ((Q t x y - P x y) * Real.log (K x y)) := by
          have key : ∀ x y, (Q t x y * Real.log (Q t x y) - Q t x y * Real.log (K x y))
              - (P x y * Real.log (P x y) - P x y * Real.log (K x y))
              = φ x y - (Q t x y - P x y) * Real.log (K x y) := by
            intro x y
            rw [hφ]
            dsimp only
            ring
          unfold relEntropy
          calc (∑ x, ∑ y, (Q t x y * Real.log (Q t x y) - Q t x y * Real.log (K x y)))
              - ∑ x, ∑ y, (P x y * Real.log (P x y) - P x y * Real.log (K x y))
              = ∑ x, ∑ y, ((Q t x y * Real.log (Q t x y) - Q t x y * Real.log (K x y))
                - (P x y * Real.log (P x y) - P x y * Real.log (K x y))) := sum_sub_eq_sum_sub _ _
            _ = (∑ x, ∑ y, φ x y)
                - ∑ x, ∑ y, ((Q t x y - P x y) * Real.log (K x y)) := by
              have h1 : (∑ x, ∑ y, ((Q t x y * Real.log (Q t x y) - Q t x y * Real.log (K x y))
                  - (P x y * Real.log (P x y) - P x y * Real.log (K x y))))
                  = ∑ x, ∑ y, (φ x y - (Q t x y - P x y) * Real.log (K x y)) := by
                refine Fintype.sum_congr _ _ fun x => ?_
                refine Fintype.sum_congr _ _ fun y => ?_
                exact key x y
              exact h1.trans (sum_sub_eq_sum_sub _ _).symm
      _ = φ i j + φ i j' + φ i' j + φ i' j'
          - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
            + Real.log (K i' j')) * t := by
        rw [hφsum, hKsum]
      _ = _ := by
        rw [hφ]
        dsimp only
        rw [hQ1, hQ2, hQ3, hQ4]
        ring
  set L : ℝ := Real.log (K i j) - Real.log (K i j') - Real.log (K i' j) + Real.log (K i' j')
    with hL
  set C : ℝ := -Real.log y - Real.log z + Real.log (q + 1) + 2 * Real.log 2 - 1 - L with hC
  set t : ℝ := min (min (min y z) 1) (Real.exp (-(C + 1))) / 2 with ht
  have hminA : min (min (min y z) 1) (Real.exp (-(C + 1))) ≤ min (min y z) 1 := min_le_left _ _
  have hminy : min y z ≤ y := min_le_left _ _
  have hminz : min y z ≤ z := min_le_right _ _
  have hminE : min (min (min y z) 1) (Real.exp (-(C + 1))) ≤ Real.exp (-(C + 1)) :=
    min_le_right _ _
  have hX0 : 0 < min (min (min y z) 1) (Real.exp (-(C + 1))) := by
    exact lt_min (lt_min (lt_min hy0 hz0) (by norm_num)) (by positivity)
  have ht0 : 0 < t := by
    rw [ht]
    exact div_pos hX0 (by norm_num : (0 : ℝ) < 2)
  have hty : t ≤ y / 2 := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ (min (min y z) 1) / 2 := div_le_div_of_nonneg_right hminA (by norm_num)
      _ ≤ (min y z) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ ≤ y / 2 := div_le_div_of_nonneg_right hminy (by norm_num)
  have htz : t ≤ z / 2 := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ (min (min y z) 1) / 2 := div_le_div_of_nonneg_right hminA (by norm_num)
      _ ≤ (min y z) / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ ≤ z / 2 := div_le_div_of_nonneg_right hminz (by norm_num)
  have ht1 : t ≤ 1 / 2 := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ (min (min y z) 1) / 2 := div_le_div_of_nonneg_right hminA (by norm_num)
      _ ≤ 1 / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have htE : t ≤ Real.exp (-(C + 1)) := by
    rw [ht]
    calc (min (min (min y z) 1) (Real.exp (-(C + 1)))) / 2
        ≤ Real.exp (-(C + 1)) / 2 := div_le_div_of_nonneg_right hminE (by norm_num)
      _ ≤ Real.exp (-(C + 1)) := div_le_self (by positivity) (by norm_num)
  have hty0 : 0 < y - t := by linarith
  have htz0 : 0 < z - t := by linarith
  have hqt0 : 0 < q + t := by linarith
  have hqt1 : 0 < q + 1 := by linarith
  have htmin : t ≤ min y z := le_min
    (le_trans hty (div_le_self hy0.le (by norm_num)))
    (le_trans htz (div_le_self hz0.le (by norm_num)))
  have hlogt : Real.log t ≤ -(C + 1) := by
    have h1 : Real.log t ≤ Real.log (Real.exp (-(C + 1))) := by
      exact Real.strictMonoOn_log.monotoneOn ht0 (Real.exp_pos _) htE
    rwa [Real.log_exp] at h1
  have hhalfy : y / 2 ≤ y - t := by
    calc y / 2 = y - y / 2 := by ring
      _ ≤ y - t := sub_le_sub_left hty y
  have hhalfz : z / 2 ≤ z - t := by
    calc z / 2 = z - z / 2 := by ring
      _ ≤ z - t := sub_le_sub_left htz z
  have hby : (y - t) * Real.log (y - t) - y * Real.log y
      ≤ -t * (Real.log y - Real.log 2 + 1) := by
    have h1 : y * Real.log y - (y - t) * Real.log (y - t)
        ≥ t * (Real.log (y - t) + 1) := by
      have hle := mul_log_sub_mul_log_ge (y - t) y hty0 (le_of_lt hy0)
      linarith
    have h2 : Real.log y - Real.log 2 ≤ Real.log (y - t) := by
      rw [← Real.log_div (x := y) (y := 2) (ne_of_gt hy0) (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.strictMonoOn_log.monotoneOn (a := y / 2) (b := y - t)
        (div_pos hy0 (by norm_num : (0 : ℝ) < 2)) hty0 hhalfy
    have h3 := mul_le_mul_of_nonneg_left h2 ht0.le
    linarith
  have hbz : (z - t) * Real.log (z - t) - z * Real.log z
      ≤ -t * (Real.log z - Real.log 2 + 1) := by
    have h1 : z * Real.log z - (z - t) * Real.log (z - t)
        ≥ t * (Real.log (z - t) + 1) := by
      have hle := mul_log_sub_mul_log_ge (z - t) z htz0 (le_of_lt hz0)
      linarith
    have h2 : Real.log z - Real.log 2 ≤ Real.log (z - t) := by
      rw [← Real.log_div (x := z) (y := 2) (ne_of_gt hz0) (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.strictMonoOn_log.monotoneOn (a := z / 2) (b := z - t)
        (div_pos hz0 (by norm_num : (0 : ℝ) < 2)) htz0 hhalfz
    have h3 := mul_le_mul_of_nonneg_left h2 ht0.le
    linarith
  have hbq : (q + t) * Real.log (q + t) - q * Real.log q ≤ t * (Real.log (q + 1) + 1) := by
    have hle := mul_log_sub_mul_log_ge (q + t) q hqt0 hq0
    have h2 : Real.log (q + t) ≤ Real.log (q + 1) :=
      Real.strictMonoOn_log.monotoneOn hqt0 hqt1 (by linarith [ht1])
    have h3 := mul_le_mul_of_nonneg_left h2 ht0.le
    linarith
  have hnonpos : relEntropy P K ≤ relEntropy (Q t) K := hmin _ (hQnonneg t ht0.le htmin) (hQmarg t)
  have hneg : relEntropy (Q t) K - relEntropy P K < 0 := by
    rw [hrelDiff t, hij0, ← hy, ← hz, ← hq]
    simp only [Real.log_zero, zero_mul, zero_add, sub_zero]
    have key1 : Real.log t + C < 0 := by
      linarith [hlogt, hC]
    have key2 : (Real.log t + C) * t < 0 := mul_neg_of_neg_of_pos key1 ht0
    linarith [hby, hbz, hbq, hL]
  linarith

end Matrix
