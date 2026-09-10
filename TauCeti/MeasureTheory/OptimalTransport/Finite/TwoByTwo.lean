/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix

/-!
# Two-by-two finite transport problems

A transport matrix between probability laws on two-point spaces has one degree of freedom. Its
upper-left entry ranges over the closed interval
`[max 0 (μ₀ + ν₀ - 1), min μ₀ ν₀]`, and the other three entries follow from the marginal sums.

This file gives the resulting equivalence between transport matrices and that interval. It also
writes every real-valued transport cost as an affine function of the interval parameter. The sign
of the cost cross-difference therefore selects an endpoint that minimizes the cost.
-/

public section

noncomputable section

open scoped BigOperators ENNReal

namespace TauCeti

/-- The lower endpoint for the upper-left entry of a two-by-two transport matrix. -/
def twoByTwoLower (μ ν : PMF (Fin 2)) : ℝ :=
  max 0 ((μ 0).toReal + (ν 0).toReal - 1)

/-- The upper endpoint for the upper-left entry of a two-by-two transport matrix. -/
def twoByTwoUpper (μ ν : PMF (Fin 2)) : ℝ :=
  min (μ 0).toReal (ν 0).toReal

/-- The feasible interval for the upper-left entry of a two-by-two transport matrix. -/
def TwoByTwoParameter (μ ν : PMF (Fin 2)) :=
  Set.Icc (twoByTwoLower μ ν) (twoByTwoUpper μ ν)

namespace TwoByTwoParameter

/-- A feasible two-by-two parameter is at least the lower endpoint. -/
theorem lower_le {μ ν : PMF (Fin 2)} (x : TwoByTwoParameter μ ν) :
    twoByTwoLower μ ν ≤ x.1 :=
  x.2.1

/-- A feasible two-by-two parameter is at most the upper endpoint. -/
theorem le_upper {μ ν : PMF (Fin 2)} (x : TwoByTwoParameter μ ν) :
    x.1 ≤ twoByTwoUpper μ ν :=
  x.2.2

/-- Feasible two-by-two parameters are equal when their real values are equal. -/
@[ext]
theorem ext {μ ν : PMF (Fin 2)} {x y : TwoByTwoParameter μ ν} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

end TwoByTwoParameter

namespace TransportMatrix

variable {μ ν : PMF (Fin 2)}

private theorem pmf_sum_two (μ : PMF (Fin 2)) :
    (μ 0).toReal + (μ 1).toReal = 1 := by
  simpa only [Fin.sum_univ_two] using PMF.sum_toReal_eq_one μ

/-- The upper-left entry of a two-by-two transport matrix, as a point of its feasible interval. -/
def twoByTwoParameter (A : TransportMatrix μ ν) : TwoByTwoParameter μ ν := by
  refine ⟨(A 0 0).toReal, ?_, ?_⟩
  · apply max_le ENNReal.toReal_nonneg
    have hrow := A.sum_toRealFun_row 0
    have hrow1 := A.sum_toRealFun_row 1
    have hcol := A.sum_toRealFun_col 0
    have h11 := A.toRealFun_nonneg (1, 1)
    have hμ := pmf_sum_two μ
    have hν := pmf_sum_two ν
    simp only [Fin.sum_univ_two, toRealFun_apply] at hrow hrow1 hcol h11
    linarith
  · apply le_min
    · exact (ENNReal.toReal_le_toReal (A.apply_ne_top 0 0) (μ.apply_ne_top 0)).2
        (A.apply_le_row 0 0)
    · exact (ENNReal.toReal_le_toReal (A.apply_ne_top 0 0) (ν.apply_ne_top 0)).2
        (A.apply_le_col 0 0)

/-- The real value of the parameter associated to a two-by-two transport matrix is its
upper-left entry. -/
@[simp]
theorem twoByTwoParameter_val (A : TransportMatrix μ ν) :
    (twoByTwoParameter A).1 = (A 0 0).toReal :=
  (rfl)

/-- Construct a two-by-two transport matrix from a point of its feasible interval. -/
def ofTwoByTwoParameter (x : TwoByTwoParameter μ ν) : TransportMatrix μ ν where
  matrix := !![ENNReal.ofReal x.1, ENNReal.ofReal ((μ 0).toReal - x.1);
    ENNReal.ofReal ((ν 0).toReal - x.1),
      ENNReal.ofReal (1 - (μ 0).toReal - (ν 0).toReal + x.1)]
  row_sum i := by
    have hx0 : 0 ≤ x.1 := (le_max_left 0 _).trans x.2.1
    have hxμ : x.1 ≤ (μ 0).toReal := x.2.2.trans (min_le_left _ _)
    have hxν : x.1 ≤ (ν 0).toReal := x.2.2.trans (min_le_right _ _)
    have hx11 : 0 ≤ 1 - (μ 0).toReal - (ν 0).toReal + x.1 := by
      have := (le_max_right 0 _).trans x.2.1
      linarith
    fin_cases i
    · rw [Fin.sum_univ_two]
      norm_num
      rw [← ENNReal.ofReal_add hx0 (sub_nonneg.2 hxμ), add_sub_cancel,
        ENNReal.ofReal_toReal (μ.apply_ne_top 0)]
    · rw [Fin.sum_univ_two]
      norm_num
      rw [← ENNReal.ofReal_add (sub_nonneg.2 hxν) hx11,
        ← ENNReal.ofReal_toReal (μ.apply_ne_top 1)]
      congr 1
      have hμ := pmf_sum_two μ
      linarith
  col_sum j := by
    have hx0 : 0 ≤ x.1 := (le_max_left 0 _).trans x.2.1
    have hxμ : x.1 ≤ (μ 0).toReal := x.2.2.trans (min_le_left _ _)
    have hxν : x.1 ≤ (ν 0).toReal := x.2.2.trans (min_le_right _ _)
    have hx11 : 0 ≤ 1 - (μ 0).toReal - (ν 0).toReal + x.1 := by
      have := (le_max_right 0 _).trans x.2.1
      linarith
    fin_cases j
    · rw [Fin.sum_univ_two]
      norm_num
      rw [← ENNReal.ofReal_add hx0 (sub_nonneg.2 hxν), add_sub_cancel,
        ENNReal.ofReal_toReal (ν.apply_ne_top 0)]
    · rw [Fin.sum_univ_two]
      norm_num
      rw [← ENNReal.ofReal_add (sub_nonneg.2 hxμ) hx11,
        ← ENNReal.ofReal_toReal (ν.apply_ne_top 1)]
      congr 1
      have hν := pmf_sum_two ν
      linarith

/-- The upper-left entry of the transport matrix constructed from a parameter is that parameter. -/
@[simp]
theorem ofTwoByTwoParameter_apply_zero_zero (x : TwoByTwoParameter μ ν) :
    (ofTwoByTwoParameter x 0 0).toReal = x.1 := by
  simp [ofTwoByTwoParameter, ENNReal.toReal_ofReal, (le_max_left 0 _).trans x.2.1]

/-- The real entries of the transport matrix constructed from a parameter. -/
theorem ofTwoByTwoParameter_toReal_apply (x : TwoByTwoParameter μ ν) (i j : Fin 2) :
    (ofTwoByTwoParameter x i j).toReal =
      !![x.1, (μ 0).toReal - x.1; (ν 0).toReal - x.1,
        1 - (μ 0).toReal - (ν 0).toReal + x.1] i j := by
  have hx0 : 0 ≤ x.1 := (le_max_left 0 _).trans x.2.1
  have hxμ : x.1 ≤ (μ 0).toReal := x.2.2.trans (min_le_left _ _)
  have hxν : x.1 ≤ (ν 0).toReal := x.2.2.trans (min_le_right _ _)
  have hx11 : 0 ≤ 1 - (μ 0).toReal - (ν 0).toReal + x.1 := by
    have := (le_max_right 0 _).trans x.2.1
    linarith
  fin_cases i <;> fin_cases j <;>
    simp [ofTwoByTwoParameter, ENNReal.toReal_ofReal, hx0, sub_nonneg.2 hxμ,
      sub_nonneg.2 hxν, hx11]

/-- Every real entry of a two-by-two transport matrix is determined by its upper-left entry. -/
theorem toReal_apply_eq_of_fin_two (A : TransportMatrix μ ν) (i j : Fin 2) :
    (A i j).toReal =
      !![(A 0 0).toReal, (μ 0).toReal - (A 0 0).toReal;
        (ν 0).toReal - (A 0 0).toReal,
          1 - (μ 0).toReal - (ν 0).toReal + (A 0 0).toReal] i j := by
  have hrow0 := A.sum_toRealFun_row 0
  have hrow1 := A.sum_toRealFun_row 1
  have hcol0 := A.sum_toRealFun_col 0
  have hμ := pmf_sum_two μ
  simp only [Fin.sum_univ_two, toRealFun_apply] at hrow0 hrow1 hcol0
  fin_cases i <;> fin_cases j <;> norm_num <;> linarith

/-- Two-by-two transport matrices are equivalent to their exact feasible parameter interval. -/
def twoByTwoEquiv (μ ν : PMF (Fin 2)) :
    TransportMatrix μ ν ≃ TwoByTwoParameter μ ν where
  toFun := twoByTwoParameter
  invFun := ofTwoByTwoParameter
  left_inv A := by
    ext i j
    apply (ENNReal.toReal_eq_toReal_iff'
      ((ofTwoByTwoParameter (twoByTwoParameter A)).apply_ne_top i j)
      (A.apply_ne_top i j)).1
    rw [ofTwoByTwoParameter_toReal_apply, toReal_apply_eq_of_fin_two]
    rfl
  right_inv x := by
    apply Subtype.ext
    exact ofTwoByTwoParameter_apply_zero_zero x

/-- Finite couplings of two two-point laws are equivalent to the feasible interval for their
upper-left mass. -/
def twoByTwoCouplingEquiv (μ ν : PMF (Fin 2)) :
    {π : PMF (Fin 2 × Fin 2) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν} ≃
      TwoByTwoParameter μ ν :=
  (transportMatrixEquiv μ ν).trans (twoByTwoEquiv μ ν)

/-- The cross-difference controlling which endpoint minimizes a two-by-two transport cost. -/
def twoByTwoCrossDiff (c : Fin 2 × Fin 2 → ℝ) : ℝ :=
  c (0, 0) - c (0, 1) - c (1, 0) + c (1, 1)

/-- The cost of a two-by-two transport matrix is affine in its upper-left entry. -/
theorem cost_eq_const_add_crossDiff_mul (c : Fin 2 × Fin 2 → ℝ)
    (A : TransportMatrix μ ν) :
    A.cost c = c (0, 1) * (μ 0).toReal + c (1, 0) * (ν 0).toReal +
      c (1, 1) * (1 - (μ 0).toReal - (ν 0).toReal) +
        twoByTwoCrossDiff c * (A 0 0).toReal := by
  rw [cost_def, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, toRealFun_apply]
  rw [toReal_apply_eq_of_fin_two A 0 1, toReal_apply_eq_of_fin_two A 1 0,
    toReal_apply_eq_of_fin_two A 1 1]
  norm_num
  simp only [twoByTwoCrossDiff]
  ring

private theorem twoByTwoLower_le_upper (μ ν : PMF (Fin 2)) :
    twoByTwoLower μ ν ≤ twoByTwoUpper μ ν :=
  (twoByTwoParameter (independent μ ν)).2.1.trans
    (twoByTwoParameter (independent μ ν)).2.2

/-- The endpoint of the feasible interval that minimizes the given two-by-two cost. -/
noncomputable def optimalTwoByTwoParameter (c : Fin 2 × Fin 2 → ℝ) (μ ν : PMF (Fin 2)) :
    TwoByTwoParameter μ ν :=
  if 0 ≤ twoByTwoCrossDiff c then
    ⟨twoByTwoLower μ ν, le_rfl, twoByTwoLower_le_upper μ ν⟩
  else
    ⟨twoByTwoUpper μ ν, twoByTwoLower_le_upper μ ν, le_rfl⟩

/-- A cost-minimizing two-by-two transport matrix. -/
noncomputable def optimalTwoByTwo (c : Fin 2 × Fin 2 → ℝ) (μ ν : PMF (Fin 2)) :
    TransportMatrix μ ν :=
  ofTwoByTwoParameter (optimalTwoByTwoParameter c μ ν)

/-- The exact cost of the chosen minimizing endpoint of the two-by-two feasible interval. -/
theorem optimalTwoByTwo_cost_eq (c : Fin 2 × Fin 2 → ℝ) (μ ν : PMF (Fin 2)) :
    (optimalTwoByTwo c μ ν).cost c =
      c (0, 1) * (μ 0).toReal + c (1, 0) * (ν 0).toReal +
        c (1, 1) * (1 - (μ 0).toReal - (ν 0).toReal) +
          twoByTwoCrossDiff c *
            if 0 ≤ twoByTwoCrossDiff c then twoByTwoLower μ ν else twoByTwoUpper μ ν := by
  rw [cost_eq_const_add_crossDiff_mul]
  by_cases h : 0 ≤ twoByTwoCrossDiff c
  · have hopt : (optimalTwoByTwo c μ ν 0 0).toReal = twoByTwoLower μ ν := by
      change (ofTwoByTwoParameter (optimalTwoByTwoParameter c μ ν) 0 0).toReal = _
      rw [ofTwoByTwoParameter_apply_zero_zero]
      simp [optimalTwoByTwoParameter, h]
    rw [hopt]
    simp [h]
  · have hopt : (optimalTwoByTwo c μ ν 0 0).toReal = twoByTwoUpper μ ν := by
      change (ofTwoByTwoParameter (optimalTwoByTwoParameter c μ ν) 0 0).toReal = _
      rw [ofTwoByTwoParameter_apply_zero_zero]
      simp [optimalTwoByTwoParameter, h]
    rw [hopt]
    simp [h]

/-- The chosen two-by-two transport matrix has cost no larger than any feasible matrix. -/
theorem optimalTwoByTwo_cost_le (c : Fin 2 × Fin 2 → ℝ) (A : TransportMatrix μ ν) :
    (optimalTwoByTwo c μ ν).cost c ≤ A.cost c := by
  rw [cost_eq_const_add_crossDiff_mul, cost_eq_const_add_crossDiff_mul]
  by_cases h : 0 ≤ twoByTwoCrossDiff c
  · have hA := (twoByTwoParameter A).2.1
    change twoByTwoLower μ ν ≤ (A 0 0).toReal at hA
    have hopt : (optimalTwoByTwo c μ ν 0 0).toReal = twoByTwoLower μ ν := by
      change (ofTwoByTwoParameter (optimalTwoByTwoParameter c μ ν) 0 0).toReal = _
      rw [ofTwoByTwoParameter_apply_zero_zero]
      simp [optimalTwoByTwoParameter, h]
    rw [hopt]
    nlinarith
  · have hA := (twoByTwoParameter A).2.2
    change (A 0 0).toReal ≤ twoByTwoUpper μ ν at hA
    have hcross : twoByTwoCrossDiff c ≤ 0 := le_of_not_ge h
    have hopt : (optimalTwoByTwo c μ ν 0 0).toReal = twoByTwoUpper μ ν := by
      change (ofTwoByTwoParameter (optimalTwoByTwoParameter c μ ν) 0 0).toReal = _
      rw [ofTwoByTwoParameter_apply_zero_zero]
      simp [optimalTwoByTwoParameter, h]
    rw [hopt]
    nlinarith

end TransportMatrix

end TauCeti
