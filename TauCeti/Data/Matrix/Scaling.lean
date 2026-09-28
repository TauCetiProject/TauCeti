/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Topology.Instances.Matrix
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# The entropy minimiser with prescribed marginals

Let `a` and `b` be real vectors indexed by the rows and by the columns of a real matrix `K` of shape
`n × m`, and let `S` be the set of the nonnegative matrices whose row sums are `a` and whose column
sums are `b`. When `S` is nonempty, the relative entropy of a matrix against `K` attains a minimum
on `S`, and for strictly positive marginals of equal total mass every minimiser has strictly
positive entries.

`K` itself is unrestricted. The relative entropy `Matrix.relEntropy P K` below is the formula
`∑ i, ∑ j, (P i j * log (P i j) - P i j * log (K i j))`; for a nonnegative `P` and a strictly
positive `K` it is the relative entropy of `P` against `K`, and the minimiser is positive for every
`K`. Strict positivity of `K` is needed only in the later steps, which identify the minimiser with a
diagonal scaling of `K`.

`Matrix.IsDiagonalScaling P K u v` records the shape of the minimiser described by the later steps
of this development: `P i j = u i * K i j * v j` for row factors `u` and column factors `v`, that
is a diagonal scaling of `K`.

The marginals here are arbitrary vectors of equal total mass, not probability distributions, and
the matrices are real: this is the setting of a diagonal scaling of a kernel, where the scaled
matrix has total mass `∑ i, a i` and is compared against the real kernel `K`. A probability-valued
plan with `PMF` marginals is `TauCeti.TransportMatrix`.

## Main definitions

* `Matrix.HasMarginals P a b`: the row sums of `P` are `a` and its column sums are `b`.
* `Matrix.IsDiagonalScaling P K u v`: `P i j = u i * K i j * v j` for all `i` and `j`.
* `Matrix.relEntropy P K`: the sum over `i`, `j` of `P i j * (log (P i j) - log (K i j))`.

## Main results

* `Matrix.exists_relEntropy_minOn`: a minimiser of `Matrix.relEntropy` against `K` among the
  nonnegative matrices with row sums `a` and column sums `b` exists, as soon as there is one such
  matrix.
* `Matrix.exists_relEntropy_minOn_of_pos`: the same, for strictly positive marginals `a` and `b` of
  equal total mass.
* `Matrix.pos_of_relEntropy_minOn`: every such minimiser has strictly positive entries.
-/
public section

open scoped BigOperators

namespace Matrix

variable {n m : ℕ}

/-! ### Marginals and diagonal scalings -/

/-- `P` has row sums `a` and column sums `b`, that is `(∑ j, P i j) = a i` and
`(∑ i, P i j) = b j` for all `i` and `j`.

This is the two sum equalities only. The nonnegativity of a matrix with these marginals is a
separate hypothesis, as it is in the results below. -/
def HasMarginals (P : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) : Prop :=
  (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j)

@[simp] theorem hasMarginals_def (P : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ) :
    HasMarginals P a b ↔ (∀ i, (∑ j, P i j) = a i) ∧ (∀ j, (∑ i, P i j) = b j) := Iff.rfl

/-- `P` is the diagonal scaling of `K` by the row factors `u` and the column factors `v`, that is
`P i j = u i * K i j * v j` for all `i` and `j`. -/
def IsDiagonalScaling (P : Matrix (Fin n) (Fin m) ℝ) (K : Matrix (Fin n) (Fin m) ℝ)
    (u : Fin n → ℝ) (v : Fin m → ℝ) : Prop :=
  ∀ i j, P i j = u i * K i j * v j

@[simp] theorem isDiagonalScaling_def (P K : Matrix (Fin n) (Fin m) ℝ) (u : Fin n → ℝ)
    (v : Fin m → ℝ) : IsDiagonalScaling P K u v ↔ ∀ i j, P i j = u i * K i j * v j := Iff.rfl

/-- The row and column sums of a diagonal scaling are the row and column sums of its factors, so
the stated sums of `u i * K i j * v j` over the columns and over the rows transfer through
`IsDiagonalScaling` to `HasMarginals P a b`. -/
theorem IsDiagonalScaling.hasMarginals {P K : Matrix (Fin n) (Fin m) ℝ} {u : Fin n → ℝ}
    {v : Fin m → ℝ} (h : IsDiagonalScaling P K u v) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, (∑ j, u i * K i j * v j) = a i) (hb : ∀ j, (∑ i, u i * K i j * v j) = b j) :
    HasMarginals P a b := by
  have hP : P = fun i j => u i * K i j * v j := funext fun i => funext fun j => h i j
  constructor
  · intro i
    rw [hP]
    exact ha i
  · intro j
    rw [hP]
    exact hb j

/-- A diagonal scaling is not unique: rescaling the row factors by `r` and the column factors by
`r ⁻¹`, for a nonzero `r`, leaves the scaled matrix `P` unchanged. -/
theorem IsDiagonalScaling.rescale_factors {P K : Matrix (Fin n) (Fin m) ℝ} {u : Fin n → ℝ}
    {v : Fin m → ℝ} (h : IsDiagonalScaling P K u v) {r : ℝ} (hr : r ≠ 0) :
    IsDiagonalScaling P K (fun i => r * u i) (fun j => r⁻¹ * v j) := by
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr
  intro i j
  calc P i j = u i * K i j * v j := h i j
    _ = (u i * K i j * v j) * (r * r⁻¹) := by rw [hrr]; ring
    _ = r * u i * K i j * (r⁻¹ * v j) := by ring

/-! ### The relative entropy of a matrix against a kernel -/

/-- `Matrix.relEntropy P K` is the real number
`∑ i, ∑ j, (P i j * Real.log (P i j) - P i j * Real.log (K i j))`, with the convention
`0 * log 0 = 0`.

The formula is defined for arbitrary real matrices `P` and `K`. For a nonnegative `P` and a strictly
positive `K` it is the relative entropy of `P` against `K`; the nonnegativity of `P` and the
strict positivity of `K` are hypotheses of the results that use this interpretation, not part of
the definition.

Writing `A = ∑ i j, P i j` and `B = ∑ i j, K i j`, for a nonnegative `P` of positive total mass
and a strictly positive `K` it is `A` times the relative entropy of the probability distributions
`P i j / A` and `K i j / B`, up to the additive constant `A * (log A - log B)`. Two matrices of
equal total mass that differ by that constant are compared the same way by an optimisation against
`K`. -/
noncomputable def relEntropy (P K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, (P i j * Real.log (P i j) - P i j * Real.log (K i j))

@[simp] theorem relEntropy_def (P K : Matrix (Fin n) (Fin m) ℝ) :
    relEntropy P K = ∑ i, ∑ j, (P i j * Real.log (P i j) - P i j * Real.log (K i j)) :=
  -- `(rfl)` rather than `rfl`: a bare `rfl` proof would demand that `relEntropy` be `@[expose]`,
  -- and this lemma is the supported unfolding interface instead.
  (rfl)

/-- The relative entropy against a fixed matrix is continuous in the matrix it is applied to. -/
theorem continuous_relEntropy (K : Matrix (Fin n) (Fin m) ℝ) : Continuous (relEntropy · K) := by
  unfold relEntropy
  fun_prop

/-! ### A minimiser of the relative entropy -/

/-- The relative entropy against `K` attains a minimum on the nonnegative matrices with row sums `a`
and column sums `b`, as soon as there is one such matrix.

The set of these matrices is closed, every entry of such a matrix is at most `∑ i, a i`, and the
relative entropy is continuous, so the minimum is attained on a closed subset of a compact box. -/
theorem exists_relEntropy_minOn (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (hfeas : ∃ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      ∀ Q : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        relEntropy P K ≤ relEntropy Q K := by
  obtain ⟨Pfeas, hPfeas0, hPfeasa⟩ := hfeas
  set A : ℝ := ∑ i, a i with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    calc (0 : ℝ) ≤ ∑ i, ∑ j, Pfeas i j :=
          Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hPfeas0 i j
      _ = ∑ i, a i := Finset.sum_congr rfl fun i _ => hPfeasa.1 i
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
    {P | (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b} with hS
  have hclosed : IsClosed S := by
    rw [hS]
    exact hnonneg.inter (hrows.inter hcols)
  have hbound : ∀ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) → HasMarginals P a b →
      ∀ i j, P i j ≤ A := by
    intro P hP0 hPa i j
    calc P i j ≤ ∑ k, P i k := Finset.single_le_sum (fun k _ => hP0 i k) (Finset.mem_univ j)
      _ = a i := hPa.1 i
      _ ≤ ∑ k, a k := Finset.single_le_sum
          (fun k _ => by rw [← hPa.1 k]; exact Finset.sum_nonneg fun l _ => hP0 k l)
          (Finset.mem_univ i)
      _ = A := hA.symm
  have hbox : IsCompact {P : Matrix (Fin n) (Fin m) ℝ | ∀ i j, P i j ∈ Set.Icc 0 A} :=
    IsCompact.matrix (isCompact_Icc (α := ℝ))
  have hcompact : IsCompact S :=
    IsCompact.of_isClosed_subset hbox hclosed
      fun P hP => fun i j => ⟨hP.1 i j, hbound P hP.1 hP.2 i j⟩
  obtain ⟨P, hPmem, hPmin⟩ := hcompact.exists_isMinOn (f := fun P => relEntropy P K)
    ⟨Pfeas, hPfeas0, hPfeasa⟩ (continuous_relEntropy K).continuousOn
  rw [hS, Set.mem_ofPred] at hPmem
  exact ⟨P, hPmem.1, hPmem.2, fun Q hQ0 hQa => (isMinOn_iff.mp hPmin) Q ⟨hQ0, hQa⟩⟩

/-- The relative entropy against `K` attains a minimum on the nonnegative matrices with row sums
`a` and column sums `b` whenever `a` and `b` are nonnegative and of equal total mass.

Such a matrix is always available: the product coupling `P i j = a i * b j / ∑ k, a k` has the
prescribed marginals when the total mass is positive, and when the total mass is zero both marginals
vanish identically, so the zero matrix has them. -/
theorem exists_relEntropy_minOn_of_nonneg (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ)
    (b : Fin m → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hmass : (∑ i, a i) = ∑ j, b j) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      ∀ Q : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        relEntropy P K ≤ relEntropy Q K := by
  have hfeas : ∃ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b := by
    by_cases hApos : 0 < ∑ i, a i
    · -- The product coupling of the two marginals.
      set A : ℝ := ∑ i, a i with hA
      have hA0 : A ≠ 0 := ne_of_gt hApos
      have hP₀ : (∀ i j, 0 ≤ (fun i j => a i * (b j * A⁻¹)) i j) ∧
          HasMarginals (fun i j => a i * (b j * A⁻¹)) a b := by
        constructor
        · intro i j
          exact mul_nonneg (ha i) (mul_nonneg (hb j) (inv_nonneg.mpr hApos.le))
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
      exact ⟨fun i j => a i * (b j * A⁻¹), hP₀.1, hP₀.2⟩
    · -- A total mass of zero forces both marginals to vanish.
      have hA0 : (∑ i, a i) = 0 :=
        le_antisymm (not_lt.mp hApos) (Finset.sum_nonneg fun i _ => ha i)
      have hb0 : (∑ j, b j) = 0 := by rw [← hmass, hA0]
      have hzero : HasMarginals (0 : Matrix (Fin n) (Fin m) ℝ) a b := by
        constructor
        · intro i
          have hle : a i ≤ ∑ k, a k := Finset.single_le_sum (fun k _ => ha k) (Finset.mem_univ i)
          rw [hA0] at hle
          simp only [Matrix.zero_apply, Finset.sum_const_zero]
          exact (le_antisymm hle (ha i)).symm
        · intro j
          have hle : b j ≤ ∑ k, b k := Finset.single_le_sum (fun k _ => hb k) (Finset.mem_univ j)
          rw [hb0] at hle
          simp only [Matrix.zero_apply, Finset.sum_const_zero]
          exact (le_antisymm hle (hb j)).symm
      exact ⟨0, fun _ _ => by simp, hzero⟩
  obtain ⟨P, hP, hPa⟩ := hfeas
  exact exists_relEntropy_minOn K a b ⟨P, hP, hPa⟩

/-- For strictly positive marginals `a` and `b` of equal total mass, the relative entropy against
`K` attains a minimum on the nonnegative matrices with row sums `a` and column sums `b`.

This is the case of nonnegative marginals of `exists_relEntropy_minOn_of_nonneg`; it is stated
separately because strictly positive marginals are the setting of the later steps of this
development, which identify the minimiser with a diagonal scaling of `K`. -/
theorem exists_relEntropy_minOn_of_pos (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ)
    (b : Fin m → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j)
    (hmass : (∑ i, a i) = ∑ j, b j) :
    ∃ P : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ P i j) ∧ HasMarginals P a b ∧
      ∀ Q : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
        relEntropy P K ≤ relEntropy Q K :=
  exists_relEntropy_minOn_of_nonneg K a b (fun i => (ha i).le) (fun j => (hb j).le) hmass

/-! ### Rectangle perturbations -/

/-- `subIndicator i i' x` is `1` at `i`, `-1` at `i'` and `0` elsewhere. It is the difference of
the two sparse vectors `Pi.single i 1` and `Pi.single i' 1`, and it is the weight of a perturbation
of the rows, or of the columns, of a matrix. -/
private def subIndicator {ι : Type*} [DecidableEq ι] (i i' : ι) : ι → ℝ :=
  Pi.single i 1 - Pi.single i' 1

/-- The value of the sparse vector `subIndicator i i' x` is the difference of the indicators of `i`
and `i'` at `x`. -/
private theorem subIndicator_apply {ι : Type*} [DecidableEq ι] (i i' x : ι) :
    subIndicator i i' x = (if x = i then (1 : ℝ) else 0) - if x = i' then 1 else 0 := by
  simp [subIndicator, Pi.single_apply]

/-- The sparse vector `subIndicator i i' x` is `1` at `i`, provided `i` and `i'` are distinct. -/
private theorem subIndicator_eq_one {ι : Type*} [DecidableEq ι] {i i' : ι} (h : i ≠ i') :
    subIndicator i i' i = 1 := by
  rw [subIndicator_apply, ite_eq_left rfl, ite_eq_right h, sub_zero]

/-- The sparse vector `subIndicator i i' x` is `-1` at `i'`, provided `i` and `i'` are distinct. -/
private theorem subIndicator_eq_neg_one {ι : Type*} [DecidableEq ι] {i i' : ι} (h : i ≠ i') :
    subIndicator i i' i' = -1 := by
  rw [subIndicator_apply, ite_eq_right (Ne.symm h), ite_eq_left rfl, zero_sub]

/-- The sum of the sparse vector `Pi.single a 1` against a function `g` is the value of `g` at
`a`. -/
private lemma sum_pi_single_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) (g : ι → ℝ) :
    ∑ x, (Pi.single a (1 : ℝ) : ι → ℝ) x * g x = g a := by
  simp [Pi.single_apply]

/-- The sum of the sparse vector `subIndicator i i' x` against a function `g` of `x` is the
difference of the values of `g` at `i` and `i'`. -/
private lemma sum_subIndicator_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (i i' : ι) (g : ι → ℝ) :
    ∑ x, subIndicator i i' x * g x = g i - g i' := by
  calc (∑ x, subIndicator i i' x * g x)
      = ∑ x, (Pi.single i (1 : ℝ) : ι → ℝ) x * g x
        - ∑ x, (Pi.single i' (1 : ℝ) : ι → ℝ) x * g x := by
          simp only [subIndicator, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    _ = g i - g i' := by rw [sum_pi_single_mul i g, sum_pi_single_mul i' g]

/-- The sum of the sparse vector `subIndicator i i' x` over `x` is `0`. -/
private lemma sum_subIndicator {ι : Type*} [Fintype ι] [DecidableEq ι] (i i' : ι) :
    ∑ x, subIndicator i i' x = 0 := by
  simpa using (sum_subIndicator_mul i i' fun _ => (1 : ℝ))

/-- The double sum of `subIndicator i i' x * (subIndicator j j' y * g x y)` over `x` and `y` is the
alternating sum of the values of `g` at the four cells of the rectangle `i`, `i'` by `j`, `j'`. -/
private lemma sum_subIndicator_prod (g : Fin n → Fin m → ℝ) (i i' : Fin n) (j j' : Fin m) :
    (∑ x, ∑ y, subIndicator i i' x * (subIndicator j j' y * g x y))
      = g i j - g i j' - g i' j + g i' j' := by
  have key : ∀ x : Fin n, (∑ y, subIndicator j j' y * g x y) = g x j - g x j' :=
    fun _ => sum_subIndicator_mul j j' (g _)
  calc (∑ x, ∑ y, subIndicator i i' x * (subIndicator j j' y * g x y))
      = ∑ x, subIndicator i i' x * (∑ y, subIndicator j j' y * g x y) := by
        apply Fintype.sum_congr
        intro x
        rw [Finset.mul_sum]
    _ = ∑ x, subIndicator i i' x * (g x j - g x j') := by
        apply Fintype.sum_congr
        intro x
        rw [key x]
    _ = g i j - g i j' - g i' j + g i' j' := by
        rw [sum_subIndicator_mul i i' (fun x => g x j - g x j')]
        ring

/-- The outer product of two differences of sparse vectors vanishes outside the four cells of the
rectangle `i`, `i'` by `j`, `j'`: a row or a column outside the rectangle carries the weight `0`. -/
private lemma subIndicator_mul_eq_zero (i i' : Fin n) (j j' : Fin m) (x : Fin n) (y : Fin m)
    (h1 : ¬(x = i ∧ y = j)) (h2 : ¬(x = i ∧ y = j')) (h3 : ¬(x = i' ∧ y = j))
    (h4 : ¬(x = i' ∧ y = j')) : subIndicator i i' x * subIndicator j j' y = 0 := by
  by_cases hx : x = i
  · have hy1 : y ≠ j := fun e => h1 ⟨hx, e⟩
    have hy2 : y ≠ j' := fun e => h2 ⟨hx, e⟩
    have h0 : subIndicator j j' y = 0 := by
      rw [subIndicator_apply, ite_eq_right hy1, ite_eq_right hy2, sub_zero]
    rw [h0, mul_zero]
  by_cases hx' : x = i'
  · have hy1 : y ≠ j := fun e => h3 ⟨hx', e⟩
    have hy2 : y ≠ j' := fun e => h4 ⟨hx', e⟩
    have h0 : subIndicator j j' y = 0 := by
      rw [subIndicator_apply, ite_eq_right hy1, ite_eq_right hy2, sub_zero]
    rw [h0, mul_zero]
  · have h0 : subIndicator i i' x = 0 := by
      rw [subIndicator_apply, ite_eq_right hx, ite_eq_right hx', sub_zero]
    rw [h0, zero_mul]

/-- A function of the two indices of a matrix that vanishes outside the four cells of the
rectangle `i`, `i'` by `j`, `j'` is the sum of the four single-cell matrices `Matrix.single _ _ _`
of its values there, so its double sum is the sum of those four values. -/
private lemma sum_eq_four (g : Fin n → Fin m → ℝ) (i i' : Fin n) (j j' : Fin m)
    (hi'ne : i ≠ i') (hj'ne : j ≠ j')
    (h0 : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j) → ¬(x = i' ∧ y = j') →
      g x y = 0) :
    (∑ x, ∑ y, g x y) = g i j + g i j' + g i' j + g i' j' := by
  have key : ∀ x y, g x y = (Matrix.single i j (g i j) + Matrix.single i j' (g i j')
      + Matrix.single i' j (g i' j) + Matrix.single i' j' (g i' j')) x y := by
    intro x y
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.add_apply]
    by_cases h1 : x = i ∧ y = j
    · rw [h1.1, h1.2, Matrix.single_apply_same,
        Matrix.single_apply_of_ne i j' (g i j') i j (fun h => hj'ne h.2.symm),
        Matrix.single_apply_of_ne i' j (g i' j) i j (fun h => hi'ne h.1.symm),
        Matrix.single_apply_of_ne i' j' (g i' j') i j (fun h => hi'ne h.1.symm)]
      simp only [add_zero]
    by_cases h2 : x = i ∧ y = j'
    · rw [h2.1, h2.2, Matrix.single_apply_of_ne i j (g i j) i j' (fun h => hj'ne h.2),
        Matrix.single_apply_same,
        Matrix.single_apply_of_ne i' j (g i' j) i j' (fun h => hi'ne h.1.symm),
        Matrix.single_apply_of_ne i' j' (g i' j') i j' (fun h => hi'ne h.1.symm)]
      simp
    by_cases h3 : x = i' ∧ y = j
    · rw [h3.1, h3.2, Matrix.single_apply_of_ne i j (g i j) i' j (fun h => hi'ne h.1),
        Matrix.single_apply_of_ne i j' (g i j') i' j (fun h => hi'ne h.1),
        Matrix.single_apply_same,
        Matrix.single_apply_of_ne i' j' (g i' j') i' j (fun h => hj'ne h.2.symm)]
      simp
    by_cases h4 : x = i' ∧ y = j'
    · rw [h4.1, h4.2, Matrix.single_apply_of_ne i j (g i j) i' j' (fun h => hi'ne h.1),
        Matrix.single_apply_of_ne i j' (g i j') i' j' (fun h => hi'ne h.1),
        Matrix.single_apply_of_ne i' j (g i' j) i' j' (fun h => hj'ne h.2),
        Matrix.single_apply_same]
      simp
    · rw [Matrix.single_apply_of_ne i j (g i j) x y (fun h => h1 ⟨h.1.symm, h.2.symm⟩),
        Matrix.single_apply_of_ne i j' (g i j') x y (fun h => h2 ⟨h.1.symm, h.2.symm⟩),
        Matrix.single_apply_of_ne i' j (g i' j) x y (fun h => h3 ⟨h.1.symm, h.2.symm⟩),
        Matrix.single_apply_of_ne i' j' (g i' j') x y (fun h => h4 ⟨h.1.symm, h.2.symm⟩)]
      simp only [add_zero]
      exact h0 x y h1 h2 h3 h4
  -- The double sum of the single-cell matrix of a value is that value.
  have single : ∀ (c : ℝ) (x : Fin n) (y : Fin m), (∑ p, ∑ q, Matrix.single x y c p q) = c := by
    intro c x y
    have key : ∀ p : Fin n, (∑ q, Matrix.single x y c p q) = if p = x then c else 0 := by
      intro p
      by_cases hp : p = x
      · rw [ite_eq_left hp]
        calc (∑ q, Matrix.single x y c p q)
            = ∑ q, (if q = y then c else 0) := by
                apply Fintype.sum_congr
                intro q
                rw [Matrix.single_apply, hp]
                by_cases hq : y = q
                · rw [ite_eq_left ⟨rfl, hq⟩, ite_eq_left (Eq.symm hq)]
                · rw [ite_eq_right (fun h => hq h.2), ite_eq_right (fun h => hq h.symm)]
          _ = c := Fintype.sum_ite_eq' y (fun _ => c)
      · rw [ite_eq_right hp]
        calc (∑ q, Matrix.single x y c p q)
            = ∑ _q, (0 : ℝ) := by
                apply Fintype.sum_congr
                intro q
                rw [Matrix.single_apply, ite_eq_right (fun h => hp h.1.symm)]
          _ = 0 := Finset.sum_const_zero
    calc (∑ p, ∑ q, Matrix.single x y c p q)
        = ∑ p, (if p = x then c else 0) := Fintype.sum_congr _ _ key
      _ = c := Fintype.sum_ite_eq' x (fun _ => c)
  calc (∑ x, ∑ y, g x y)
      = ∑ x, ∑ y, ((Matrix.single i j (g i j) + Matrix.single i j' (g i j')
        + Matrix.single i' j (g i' j) + Matrix.single i' j' (g i' j')) x y) := by
          apply Fintype.sum_congr
          intro x
          apply Fintype.sum_congr
          intro y
          rw [key x y]
    _ = g i j + g i j' + g i' j + g i' j' := by
        simp only [Matrix.add_apply, Finset.sum_add_distrib]
        rw [single (g i j) i j, single (g i j') i j', single (g i' j) i' j,
          single (g i' j') i' j']

/-- The double sums of two functions are subtracted termwise. -/
private lemma sum_sub_eq_sum_sub (f g : Fin n → Fin m → ℝ) :
    (∑ x, ∑ y, f x y) - ∑ x, ∑ y, g x y = ∑ x, ∑ y, (f x y - g x y) := by
  calc (∑ x, ∑ y, f x y) - ∑ x, ∑ y, g x y
      = ∑ x, (∑ y, f x y - ∑ y, g x y) := by rw [← Finset.sum_sub_distrib]
    _ = ∑ x, ∑ y, (f x y - g x y) := by
      apply Fintype.sum_congr
      intro x
      rw [← Finset.sum_sub_distrib]

/-- Adding the outer product `Matrix.vecMulVec r c` of a row weight `r` and a column weight `c`,
both of total sum `0`, preserves the row sums and the column sums. -/
private lemma hasMarginals_add_outer (a : Fin n → ℝ) (b : Fin m → ℝ) (P : Matrix (Fin n) (Fin m) ℝ)
    (hP : HasMarginals P a b) (r : Fin n → ℝ) (c : Fin m → ℝ) (hr : ∑ x, r x = 0)
    (hc : ∑ y, c y = 0) (t : ℝ) : HasMarginals (P + Matrix.vecMulVec (fun x => t * r x) c) a b := by
  constructor
  · intro x
    have key : (∑ y, (Matrix.vecMulVec (fun x => t * r x) c) x y) = 0 := by
      calc (∑ y, (Matrix.vecMulVec (fun x => t * r x) c) x y)
          = ∑ y, t * r x * c y := by simp only [Matrix.vecMulVec_apply]
      _ = ∑ y, t * (r x * c y) := by
          apply Fintype.sum_congr
          intro y
          ring
      _ = t * (r x * ∑ z, c z) := by rw [Finset.mul_sum, Finset.mul_sum]
      _ = 0 := by rw [hc, mul_zero, mul_zero]
    calc (∑ y, (P + Matrix.vecMulVec (fun x => t * r x) c) x y)
        = (∑ y, P x y) + ∑ y, (Matrix.vecMulVec (fun x => t * r x) c) x y := by
          simp only [Matrix.add_apply]
          rw [Finset.sum_add_distrib]
      _ = a x := by rw [key, add_zero, hP.1 x]
  · intro y
    have key : (∑ x, (Matrix.vecMulVec (fun x => t * r x) c) x y) = 0 := by
      calc (∑ x, (Matrix.vecMulVec (fun x => t * r x) c) x y)
          = ∑ x, (t * r x) * c y := by simp only [Matrix.vecMulVec_apply]
      _ = ∑ x, t * (r x * c y) := by
          apply Fintype.sum_congr
          intro x
          ring
      _ = t * ((∑ z, r z) * c y) := by rw [Finset.sum_mul, Finset.mul_sum]
      _ = 0 := by rw [hr, zero_mul, mul_zero]
    calc (∑ x, (P + Matrix.vecMulVec (fun x => t * r x) c) x y)
        = (∑ x, P x y) + ∑ x, (Matrix.vecMulVec (fun x => t * r x) c) x y := by
          simp only [Matrix.add_apply]
          rw [Finset.sum_add_distrib]
      _ = b y := by rw [key, add_zero, hP.2 y]

/-- A nonnegative matrix `P` perturbed by the outer product of `t * subIndicator i i'` and
`subIndicator j j'`, which moves `t` into the cell `(i, j)`, takes it from the cells `(i, j')` and
`(i', j)` and adds it at `(i', j')`, stays nonnegative as soon as `0 ≤ t ≤ P i j'` and
`0 ≤ t ≤ P i' j`, that is as soon as the two cells that give up mass keep a nonnegative value. -/
private lemma nonneg_add_subIndicator (P : Matrix (Fin n) (Fin m) ℝ) (i i' : Fin n) (j j' : Fin m)
    (hi'ne : i ≠ i') (hj'ne : j ≠ j') (t : ℝ) (ht0 : 0 ≤ t) (hty : t ≤ P i j')
    (htz : t ≤ P i' j) (hP : ∀ i j, 0 ≤ P i j) (u : Fin n) (v : Fin m) :
    0 ≤ P u v + t * (subIndicator i i' u * subIndicator j j' v) := by
  by_cases h1 : u = i ∧ v = j
  · rw [h1.1, h1.2, subIndicator_eq_one hi'ne, subIndicator_eq_one hj'ne, one_mul]
    linarith [hP i j]
  by_cases h2 : u = i ∧ v = j'
  · rw [h2.1, h2.2, subIndicator_eq_one hi'ne, subIndicator_eq_neg_one hj'ne, one_mul, mul_neg,
      mul_one]
    linarith [hP i j', hty]
  by_cases h3 : u = i' ∧ v = j
  · rw [h3.1, h3.2, subIndicator_eq_neg_one hi'ne, subIndicator_eq_one hj'ne, neg_one_mul,
      mul_neg, mul_one]
    linarith [hP i' j, htz]
  by_cases h4 : u = i' ∧ v = j'
  · rw [h4.1, h4.2, subIndicator_eq_neg_one hi'ne, subIndicator_eq_neg_one hj'ne, neg_one_mul,
      neg_neg, mul_one]
    linarith [hP i' j']
  have h0 : subIndicator i i' u * subIndicator j j' v = 0 :=
    subIndicator_mul_eq_zero i i' j j' u v h1 h2 h3 h4
  rw [h0, mul_zero, add_zero]
  exact hP u v

/-- Moving `t` into the cell `(i, j)` of `P`, taking it from the cells `(i, j')` and `(i', j)`, and
adding it to the cell `(i', j')`, changes the relative entropy against `K` by the corresponding
change of `u * log u` at those four cells, minus `t` times the alternating sum of `Real.log (K _ _)`
over them. -/
private lemma relEntropy_add_subIndicator (K P : Matrix (Fin n) (Fin m) ℝ) (i i' : Fin n)
    (j j' : Fin m) (hi'ne : i ≠ i') (hj'ne : j ≠ j') (t : ℝ) :
    relEntropy (P + Matrix.vecMulVec (fun x => t * subIndicator i i' x) (subIndicator j j')) K
        - relEntropy P K
      = ((P i j + t) * Real.log (P i j + t) - P i j * Real.log (P i j)
        + (P i j' - t) * Real.log (P i j' - t) - P i j' * Real.log (P i j')
        + (P i' j - t) * Real.log (P i' j - t) - P i' j * Real.log (P i' j)
        + (P i' j' + t) * Real.log (P i' j' + t) - P i' j' * Real.log (P i' j'))
      - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
        + Real.log (K i' j')) * t := by
  set Q : Matrix (Fin n) (Fin m) ℝ :=
    P + Matrix.vecMulVec (fun x => t * subIndicator i i' x) (subIndicator j j') with hQ
  have hQapply : ∀ x y,
      Q x y = P x y + (t * subIndicator i i' x) * subIndicator j j' y := by
    intro x y
    simp only [hQ, Matrix.add_apply, Matrix.vecMulVec_apply]
  -- The values at the four cells of the rectangle.
  have hQ1 : Q i j = P i j + t := by
    rw [hQapply, subIndicator_eq_one hi'ne, subIndicator_eq_one hj'ne]
    ring
  have hQ2 : Q i j' = P i j' - t := by
    rw [hQapply, subIndicator_eq_one hi'ne, subIndicator_eq_neg_one hj'ne]
    ring
  have hQ3 : Q i' j = P i' j - t := by
    rw [hQapply, subIndicator_eq_neg_one hi'ne, subIndicator_eq_one hj'ne]
    ring
  have hQ4 : Q i' j' = P i' j' + t := by
    rw [hQapply, subIndicator_eq_neg_one hi'ne, subIndicator_eq_neg_one hj'ne]
    ring
  -- Outside the four cells the perturbation vanishes, so the matrix `Q` agrees there with `P`.
  have hD : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j)
      → ¬(x = i' ∧ y = j') → subIndicator i i' x * subIndicator j j' y = 0 :=
    fun _ _ h1 h2 h3 h4 => subIndicator_mul_eq_zero i i' j j' _ _ h1 h2 h3 h4
  have hQ0 : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j)
      → ¬(x = i' ∧ y = j') → Q x y = P x y := by
    intro x y h1 h2 h3 h4
    have h0 : (t * subIndicator i i' x) * subIndicator j j' y = 0 := by
      calc (t * subIndicator i i' x) * subIndicator j j' y
          = t * (subIndicator i i' x * subIndicator j j' y) := by ring
        _ = 0 := by rw [hD x y h1 h2 h3 h4, mul_zero]
    rw [hQapply, h0, add_zero]
  -- The change of the two sums of `u * log u`, supported on the four cells.
  set φ : Fin n → Fin m → ℝ := fun x y => Q x y * Real.log (Q x y) - P x y * Real.log (P x y)
    with hφ
  have hφ0 : ∀ x y, ¬(x = i ∧ y = j) → ¬(x = i ∧ y = j') → ¬(x = i' ∧ y = j)
      → ¬(x = i' ∧ y = j') → φ x y = 0 := by
    intro x y h1 h2 h3 h4
    have h0 : Q x y = P x y := hQ0 x y h1 h2 h3 h4
    simp only [hφ, h0]
    ring
  have hφsum : (∑ x, ∑ y, φ x y) = φ i j + φ i j' + φ i' j + φ i' j' :=
    sum_eq_four φ i i' j j' hi'ne hj'ne hφ0
  -- The change of the two sums of `u * log (K u v)`, supported on the four cells as well.
  have hKsum : (∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)))
      = (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
        + Real.log (K i' j')) * t := by
    calc (∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)))
        = ∑ x, ∑ y, (t * (subIndicator i i' x * subIndicator j j' y)) * Real.log (K x y) := by
          apply Fintype.sum_congr
          intro x
          apply Fintype.sum_congr
          intro y
          rw [hQapply]
          ring
      _ = ∑ x, ∑ y, subIndicator i i' x * (subIndicator j j' y * (t * Real.log (K x y))) := by
          apply Fintype.sum_congr
          intro x
          apply Fintype.sum_congr
          intro y
          ring
      _ = (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
          rw [sum_subIndicator_prod (fun x y => t * Real.log (K x y)) i i' j j']
          ring
  calc relEntropy Q K - relEntropy P K
      = (∑ x, ∑ y, φ x y) - ∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)) := by
        have key : ∀ x y, (Q x y * Real.log (Q x y) - Q x y * Real.log (K x y))
              - (P x y * Real.log (P x y) - P x y * Real.log (K x y))
            = φ x y - (Q x y - P x y) * Real.log (K x y) := by
          intro x y
          simp only [hφ]
          ring
        unfold relEntropy
        calc (∑ x, ∑ y, (Q x y * Real.log (Q x y) - Q x y * Real.log (K x y)))
              - ∑ x, ∑ y, (P x y * Real.log (P x y) - P x y * Real.log (K x y))
            = ∑ x, ∑ y, ((Q x y * Real.log (Q x y) - Q x y * Real.log (K x y))
                - (P x y * Real.log (P x y) - P x y * Real.log (K x y))) := sum_sub_eq_sum_sub _ _
          _ = ∑ x, ∑ y, (φ x y - (Q x y - P x y) * Real.log (K x y)) := by
              apply Fintype.sum_congr
              intro x
              apply Fintype.sum_congr
              intro y
              exact key x y
          _ = (∑ x, ∑ y, φ x y) - ∑ x, ∑ y, ((Q x y - P x y) * Real.log (K x y)) :=
              (sum_sub_eq_sum_sub _ _).symm
      _ = φ i j + φ i j' + φ i' j + φ i' j'
        - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
        rw [hφsum, hKsum]
      _ = ((P i j + t) * Real.log (P i j + t) - P i j * Real.log (P i j)
        + (P i j' - t) * Real.log (P i j' - t) - P i j' * Real.log (P i j')
        + (P i' j - t) * Real.log (P i' j - t) - P i' j * Real.log (P i' j)
        + (P i' j' + t) * Real.log (P i' j' + t) - P i' j' * Real.log (P i' j'))
        - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
        simp only [hφ]
        rw [hQ1, hQ2, hQ3, hQ4]
        ring

/-- The loss of the function `u ↦ u * log u` at a cell of value `x` that gives up an amount `t`,
where `0 < t` and `t ≤ x / 2`, is at most `- t * (log x - log 2 + 1)`: the supporting line of
`TauCeti.Real.mul_log_sub_mul_log_ge` bounds the loss by `- t * (log (x - t) + 1)`, and
`x - t ≥ x / 2` bounds `log (x - t)` from below by `log x - log 2`. -/
private lemma sub_mul_log_le {x t : ℝ} (hx0 : 0 < x) (ht0 : 0 < t) (htx : t ≤ x / 2) :
    (x - t) * Real.log (x - t) - x * Real.log x ≤ -t * (Real.log x - Real.log 2 + 1) := by
  have hxt0 : 0 < x - t := by linarith
  have h1 : x * Real.log x - (x - t) * Real.log (x - t) ≥ t * (Real.log (x - t) + 1) := by
    have hle := TauCeti.Real.mul_log_sub_mul_log_ge (x - t) x hxt0 (le_of_lt hx0)
    linarith
  have hhalf : x / 2 ≤ x - t := by
    calc x / 2 = x - x / 2 := by ring
      _ ≤ x - t := sub_le_sub_left htx x
  have h2 : Real.log x - Real.log 2 ≤ Real.log (x - t) := by
    rw [← Real.log_div (x := x) (y := 2) (ne_of_gt hx0) (by norm_num : (2 : ℝ) ≠ 0)]
    exact Real.strictMonoOn_log.monotoneOn (a := x / 2) (b := x - t)
      (div_pos hx0 (by norm_num : (0 : ℝ) < 2)) hxt0 hhalf
  have h3 := mul_le_mul_of_nonneg_left h2 ht0.le
  linarith

/-- A minimiser of the relative entropy against `K` has no zero entry, for every matrix `K`: moving
a sufficiently small positive amount of mass into a zero entry, taken from one entry of the same
row and one entry of the same column, preserves the marginals and decreases the relative entropy.

There is no hypothesis on `K`: the argument below bounds the kernel contribution `t * L`, with
`L = log (K i j) - log (K i j') - log (K i' j) + log (K i' j')`, by an arbitrary constant. -/
theorem pos_of_relEntropy_minOn (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ j, 0 < b j) {P : Matrix (Fin n) (Fin m) ℝ} (hP : ∀ i j, 0 ≤ P i j)
    (hPa : HasMarginals P a b)
    (hmin : ∀ Q : Matrix (Fin n) (Fin m) ℝ, (∀ i j, 0 ≤ Q i j) → HasMarginals Q a b →
      relEntropy P K ≤ relEntropy Q K) :
    ∀ i j, 0 < P i j := by
  by_contra hzero
  push Not at hzero
  obtain ⟨i, j, hij⟩ := hzero
  have hij0 : P i j = 0 := le_antisymm hij (hP i j)
  -- The row of `i` and the column of `j` each contain a positive entry, because `a` and `b` are
  -- strictly positive.
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
  -- `y` and `z` are the two cells that give up mass, `q` is the cell that receives it.
  set y : ℝ := P i j' with hy
  set z : ℝ := P i' j with hz
  set q : ℝ := P i' j' with hq
  have hy0 : 0 < y := by rw [hy]; exact hj'pos
  have hz0 : 0 < z := by rw [hz]; exact hi'pos
  have hq0 : 0 ≤ q := by rw [hq]; exact hP i' j'
  -- For `0 < t` the perturbation `Q t = P + t * (subIndicator i i' ⊗ subIndicator j j')` moves `t`
  -- into the cell `(i, j)`, takes it from `(i, j')` and `(i', j)`, and adds it at `(i', j')`.
  set Q : ℝ → Matrix (Fin n) (Fin m) ℝ :=
    fun t => P + Matrix.vecMulVec (fun x => t * subIndicator i i' x) (subIndicator j j') with hQ
  have hQnonneg : ∀ t, 0 ≤ t → t ≤ min y z → ∀ u v, 0 ≤ Q t u v := by
    intro t ht htmin u v
    rw [hQ]
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
    have hre : (t * subIndicator i i' u) * subIndicator j j' v
        = t * (subIndicator i i' u * subIndicator j j' v) := by ring
    rw [hre]
    exact nonneg_add_subIndicator P i i' j j' hi'ne' hj'ne' t ht
      (le_trans htmin (min_le_left _ _)) (le_trans htmin (min_le_right _ _)) hP u v
  have hQmarg : ∀ t, HasMarginals (Q t) a b := by
    intro t
    rw [hQ]
    exact hasMarginals_add_outer a b P hPa (subIndicator i i') (subIndicator j j')
      (sum_subIndicator i i') (sum_subIndicator j j') t
  have hrelDiff (t : ℝ) :
      relEntropy (Q t) K - relEntropy P K
        = ((P i j + t) * Real.log (P i j + t) - P i j * Real.log (P i j)
          + (P i j' - t) * Real.log (P i j' - t) - P i j' * Real.log (P i j')
          + (P i' j - t) * Real.log (P i' j - t) - P i' j * Real.log (P i' j)
          + (P i' j' + t) * Real.log (P i' j' + t) - P i' j' * Real.log (P i' j'))
        - (Real.log (K i j) - Real.log (K i j') - Real.log (K i' j)
          + Real.log (K i' j')) * t := by
    rw [hQ]
    exact relEntropy_add_subIndicator K P i i' j j' hi'ne' hj'ne' t
  -- The step `t` is chosen so small that the gain at the receiving cell, `t * log t`, dominates the
  -- losses at the two donor cells, the gain at the fourth cell and the kernel term `t * L`.
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
  -- The supporting-line inequality bounds the loss at each of the two donor cells and the gain at
  -- the receiving cell.
  have hby : (y - t) * Real.log (y - t) - y * Real.log y
      ≤ -t * (Real.log y - Real.log 2 + 1) := sub_mul_log_le hy0 ht0 hty
  have hbz : (z - t) * Real.log (z - t) - z * Real.log z
      ≤ -t * (Real.log z - Real.log 2 + 1) := sub_mul_log_le hz0 ht0 htz
  have hbq : (q + t) * Real.log (q + t) - q * Real.log q ≤ t * (Real.log (q + 1) + 1) := by
    have hle := TauCeti.Real.mul_log_sub_mul_log_ge (q + t) q hqt0 hq0
    have h2 : Real.log (q + t) ≤ Real.log (q + 1) :=
      Real.strictMonoOn_log.monotoneOn hqt0 hqt1 (by linarith [ht1])
    have h3 := mul_le_mul_of_nonneg_left h2 ht0.le
    linarith
  -- The perturbed matrix is a competitor of `P`, and its relative entropy is strictly smaller.
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
