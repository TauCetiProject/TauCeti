/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix

/-!
# The two by two transportation problem

A transportation matrix on two source and two target points has one free entry. The row and
column constraints determine the other three. Consequently the difference of the costs of two
plans is the difference of their upper-left entries multiplied by the cross difference of the
cost. The sign of this cross difference determines whether optimal plans maximize or minimize
that entry; if it vanishes, all plans cost the same. A strict inequality gives a unique optimizer.

This calculation explains why the Monge inequality favors uncrossing in ordered finite transport
problems.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti

namespace TransportMatrix

variable {μ ν : PMF (Fin 2)} (A B : TransportMatrix μ ν)

/-- The four real entries of a two by two transportation matrix are determined by its upper-left
entry and the marginals. -/
theorem toRealFun_entries_of_zero_zero_eq
    (h : A.toRealFun (0, 0) = B.toRealFun (0, 0)) :
    ∀ i j : Fin 2, A.toRealFun (i, j) = B.toRealFun (i, j) := by
  have hArow := A.sum_toRealFun_row 0
  have hBrow := B.sum_toRealFun_row 0
  have hAcol := A.sum_toRealFun_col 0
  have hBcol := B.sum_toRealFun_col 0
  have hArow1 := A.sum_toRealFun_row 1
  have hBrow1 := B.sum_toRealFun_row 1
  simp only [Fin.sum_univ_two] at hArow hBrow hAcol hBcol hArow1 hBrow1
  have h01 : A.toRealFun (0, 1) = B.toRealFun (0, 1) := by linarith
  have h10 : A.toRealFun (1, 0) = B.toRealFun (1, 0) := by linarith
  have h11 : A.toRealFun (1, 1) = B.toRealFun (1, 1) := by linarith
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

/-- Two transportation matrices with two rows and two columns agree if their upper-left entries
agree. -/
@[ext]
theorem ext_zero_zero (h : A 0 0 = B 0 0) : A = B := by
  apply ext
  intro i j
  apply (ENNReal.toReal_eq_toReal_iff' (A.apply_ne_top i j) (B.apply_ne_top i j)).mp
  simpa only [toRealFun_apply] using
    A.toRealFun_entries_of_zero_zero_eq B
      (by simpa only [toRealFun_apply] using congrArg ENNReal.toReal h) i j

/-- The upper-left entry of a two by two plan lies in the coupling interval determined by the
two marginals. -/
theorem zero_zero_bounds :
    0 ≤ A.toRealFun (0, 0) ∧
      A.toRealFun (0, 0) ≤ (μ 0).toReal ∧
      A.toRealFun (0, 0) ≤ (ν 0).toReal ∧
      (μ 0).toReal + (ν 0).toReal - 1 ≤ A.toRealFun (0, 0) := by
  have hrow0 := A.sum_toRealFun_row 0
  have hcol0 := A.sum_toRealFun_col 0
  have htotal := A.sum_toRealFun
  simp only [Fin.sum_univ_two] at hrow0 hcol0
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two] at htotal
  have hnonneg (i j : Fin 2) : 0 ≤ A.toRealFun (i, j) := A.toRealFun_nonneg (i, j)
  constructor
  · exact hnonneg 0 0
  constructor
  · simpa only [toRealFun_apply] using
      ENNReal.toReal_mono (μ.apply_ne_top 0) (A.apply_le_row 0 0)
  constructor
  · simpa only [toRealFun_apply] using
      ENNReal.toReal_mono (ν.apply_ne_top 0) (A.apply_le_col 0 0)
  · linarith [hnonneg 1 1]

/-- Construct the two by two transportation matrix with prescribed upper-left real mass `t`.
The four inequalities are exactly the coupling interval constraints. -/
def ofZeroZeroReal (μ ν : PMF (Fin 2)) (t : ℝ)
    (ht0 : 0 ≤ t) (htμ : t ≤ (μ 0).toReal) (htν : t ≤ (ν 0).toReal)
    (htlower : (μ 0).toReal + (ν 0).toReal - 1 ≤ t) : TransportMatrix μ ν := by
  let f : Fin 2 × Fin 2 → ℝ := fun q ↦
    if q.1 = 0 then
      if q.2 = 0 then t else (μ 0).toReal - t
    else if q.2 = 0 then (ν 0).toReal - t
    else 1 - (μ 0).toReal - (ν 0).toReal + t
  have hf : f ∈ RealPlans μ ν := by
    have hμsum : (μ 0).toReal + (μ 1).toReal = 1 := by
      simpa only [Fin.sum_univ_two] using PMF.sum_toReal_eq_one μ
    have hνsum : (ν 0).toReal + (ν 1).toReal = 1 := by
      simpa only [Fin.sum_univ_two] using PMF.sum_toReal_eq_one ν
    refine ⟨?_, ?_, ?_⟩
    · intro q
      rcases q with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp [f] <;> linarith
    · intro i
      fin_cases i <;> simp [f, Fin.sum_univ_two]
      all_goals linarith
    · intro j
      fin_cases j <;> simp [f, Fin.sum_univ_two]
      all_goals linarith
  exact ofRealFun hf

/-- The entries of the two by two matrix constructed from a point of the coupling interval. -/
@[simp]
theorem ofZeroZeroReal_apply (μ ν : PMF (Fin 2)) (t : ℝ)
    (ht0 : 0 ≤ t) (htμ : t ≤ (μ 0).toReal) (htν : t ≤ (ν 0).toReal)
    (htlower : (μ 0).toReal + (ν 0).toReal - 1 ≤ t) (i j : Fin 2) :
    ofZeroZeroReal μ ν t ht0 htμ htν htlower i j =
      if i = 0 then
        if j = 0 then ENNReal.ofReal t else ENNReal.ofReal ((μ 0).toReal - t)
      else if j = 0 then ENNReal.ofReal ((ν 0).toReal - t)
      else ENNReal.ofReal (1 - (μ 0).toReal - (ν 0).toReal + t) :=
  by simp [ofZeroZeroReal, ofRealFun_apply]; split_ifs <;> rfl

/-- The upper-left real entry of `ofZeroZeroReal` is its parameter. -/
theorem ofZeroZeroReal_zero_zero (μ ν : PMF (Fin 2)) (t : ℝ)
    (ht0 : 0 ≤ t) (htμ : t ≤ (μ 0).toReal) (htν : t ≤ (ν 0).toReal)
    (htlower : (μ 0).toReal + (ν 0).toReal - 1 ≤ t) :
    (ofZeroZeroReal μ ν t ht0 htμ htν htlower).toRealFun (0, 0) = t := by
  simp [ht0]

/-- The coupling interval is exactly the set of possible upper-left real entries of two by two
transportation matrices. -/
theorem exists_zero_zero_iff (μ ν : PMF (Fin 2)) (t : ℝ) :
    (0 ≤ t ∧ t ≤ (μ 0).toReal ∧ t ≤ (ν 0).toReal ∧
      (μ 0).toReal + (ν 0).toReal - 1 ≤ t) ↔
      ∃ A : TransportMatrix μ ν, A.toRealFun (0, 0) = t := by
  constructor
  · rintro ⟨ht0, htμ, htν, htlower⟩
    exact ⟨ofZeroZeroReal μ ν t ht0 htμ htν htlower,
      ofZeroZeroReal_zero_zero μ ν t ht0 htμ htν htlower⟩
  · rintro ⟨A, hA⟩
    simpa only [hA] using A.zero_zero_bounds

/-- The cost difference of two plans on two points in each marginal is their difference in
upper-left mass times the cross difference of the cost. -/
theorem cost_sub_cost_eq (c : Fin 2 × Fin 2 → ℝ) :
    A.cost c - B.cost c =
      (A.toRealFun (0, 0) - B.toRealFun (0, 0)) *
        (c (0, 0) + c (1, 1) - c (0, 1) - c (1, 0)) := by
  have hArow := A.sum_toRealFun_row 0
  have hBrow := B.sum_toRealFun_row 0
  have hAcol := A.sum_toRealFun_col 0
  have hBcol := B.sum_toRealFun_col 0
  have hArow1 := A.sum_toRealFun_row 1
  have hBrow1 := B.sum_toRealFun_row 1
  simp only [Fin.sum_univ_two] at hArow hBrow hAcol hBcol hArow1 hBrow1
  rw [A.cost_def, B.cost_def]
  simp only [Fin.sum_univ_two, Fintype.sum_prod_type]
  have h01 : A.toRealFun (0, 1) - B.toRealFun (0, 1) =
      -(A.toRealFun (0, 0) - B.toRealFun (0, 0)) := by linarith
  have h10 : A.toRealFun (1, 0) - B.toRealFun (1, 0) =
      -(A.toRealFun (0, 0) - B.toRealFun (0, 0)) := by linarith
  have h11 : A.toRealFun (1, 1) - B.toRealFun (1, 1) =
      A.toRealFun (0, 0) - B.toRealFun (0, 0) := by linarith
  calc
    _ = c (0, 0) * (A.toRealFun (0, 0) - B.toRealFun (0, 0)) +
        c (0, 1) * (A.toRealFun (0, 1) - B.toRealFun (0, 1)) +
        c (1, 0) * (A.toRealFun (1, 0) - B.toRealFun (1, 0)) +
        c (1, 1) * (A.toRealFun (1, 1) - B.toRealFun (1, 1)) := by ring
    _ = _ := by rw [h01, h10, h11]; ring

/-- Under the two by two Monge inequality, a plan with maximum upper-left mass minimizes
transport cost among all plans with the same marginals. -/
theorem cost_le_of_monge_of_le_zero_zero (c : Fin 2 × Fin 2 → ℝ)
    (hc : c (0, 0) + c (1, 1) ≤ c (0, 1) + c (1, 0))
    (hAB : B.toRealFun (0, 0) ≤ A.toRealFun (0, 0)) :
    A.cost c ≤ B.cost c := by
  rw [← sub_nonpos]
  rw [A.cost_sub_cost_eq B c]
  exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hAB) (by linarith)

/-- Under a strict Monge inequality, `A` costs no more than `B` exactly when `A` has at least
as much upper-left mass as `B`. -/
theorem cost_le_iff_le_zero_zero_of_strict_monge (c : Fin 2 × Fin 2 → ℝ)
    (hc : c (0, 0) + c (1, 1) < c (0, 1) + c (1, 0)) :
    A.cost c ≤ B.cost c ↔ B.toRealFun (0, 0) ≤ A.toRealFun (0, 0) := by
  rw [← sub_nonpos, A.cost_sub_cost_eq B c]
  have hcross : c (0, 0) + c (1, 1) - c (0, 1) - c (1, 0) < 0 := by linarith
  constructor
  · intro h
    exact sub_nonneg.mp ((mul_nonpos_iff_pos_imp_nonpos.mp h).2 hcross)
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h) hcross.le

/-- Under the reverse strict Monge inequality, cost increases with upper-left mass. -/
theorem cost_le_iff_le_zero_zero_of_reverse_strict_monge (c : Fin 2 × Fin 2 → ℝ)
    (hc : c (0, 1) + c (1, 0) < c (0, 0) + c (1, 1)) :
    A.cost c ≤ B.cost c ↔ A.toRealFun (0, 0) ≤ B.toRealFun (0, 0) := by
  rw [← sub_nonpos, A.cost_sub_cost_eq B c]
  have hcross : 0 < c (0, 0) + c (1, 1) - c (0, 1) - c (1, 0) := by linarith
  constructor
  · intro h
    exact sub_nonpos.mp ((mul_nonpos_iff_neg_imp_nonneg.mp h).2 hcross)
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hcross.le

/-- Under the reverse Monge inequality, a plan with minimum upper-left mass minimizes cost. -/
theorem cost_le_of_reverse_monge_of_zero_zero_le (c : Fin 2 × Fin 2 → ℝ)
    (hc : c (0, 1) + c (1, 0) ≤ c (0, 0) + c (1, 1))
    (hAB : A.toRealFun (0, 0) ≤ B.toRealFun (0, 0)) :
    A.cost c ≤ B.cost c := by
  rw [← sub_nonpos, A.cost_sub_cost_eq B c]
  exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hAB) (by linarith)

/-- When the two assignments have equal cost, every transportation matrix has the same cost. -/
theorem cost_eq_of_cross_eq (c : Fin 2 × Fin 2 → ℝ)
    (hc : c (0, 0) + c (1, 1) = c (0, 1) + c (1, 0)) :
    A.cost c = B.cost c := by
  have h := A.cost_sub_cost_eq B c
  have hcross : c (0, 0) + c (1, 1) - c (0, 1) - c (1, 0) = 0 := by linarith
  rw [hcross, mul_zero, sub_eq_zero] at h
  exact h

/-- The upper-left mass has a maximum among the transportation matrices with prescribed
marginals. -/
theorem exists_max_zero_zero (μ ν : PMF (Fin 2)) :
    ∃ A : TransportMatrix μ ν, ∀ B : TransportMatrix μ ν,
      B.toRealFun (0, 0) ≤ A.toRealFun (0, 0) := by
  have hμle : (μ 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (μ.coe_le_one 0)
  have hνle : (ν 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (ν.coe_le_one 0)
  let t := min (μ 0).toReal (ν 0).toReal
  have ht0 : 0 ≤ t := le_min (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)
  have htμ : t ≤ (μ 0).toReal := min_le_left _ _
  have htν : t ≤ (ν 0).toReal := min_le_right _ _
  have htlower : (μ 0).toReal + (ν 0).toReal - 1 ≤ t := by
    apply le_min <;> linarith
  refine ⟨ofZeroZeroReal μ ν t ht0 htμ htν htlower, fun B ↦ ?_⟩
  rw [ofZeroZeroReal_zero_zero]
  exact le_min B.zero_zero_bounds.2.1 B.zero_zero_bounds.2.2.1

/-- The upper-left mass also has a minimum among the transportation matrices with prescribed
marginals. -/
theorem exists_min_zero_zero (μ ν : PMF (Fin 2)) :
    ∃ A : TransportMatrix μ ν, ∀ B : TransportMatrix μ ν,
      A.toRealFun (0, 0) ≤ B.toRealFun (0, 0) := by
  have hμle : (μ 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (μ.coe_le_one 0)
  have hνle : (ν 0).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (ν.coe_le_one 0)
  let t := max 0 ((μ 0).toReal + (ν 0).toReal - 1)
  have ht0 : 0 ≤ t := le_max_left _ _
  have htμ : t ≤ (μ 0).toReal := max_le (ENNReal.toReal_nonneg) (by linarith)
  have htν : t ≤ (ν 0).toReal := max_le (ENNReal.toReal_nonneg) (by linarith)
  have htlower : (μ 0).toReal + (ν 0).toReal - 1 ≤ t := le_max_right _ _
  refine ⟨ofZeroZeroReal μ ν t ht0 htμ htν htlower, fun B ↦ ?_⟩
  rw [ofZeroZeroReal_zero_zero]
  exact max_le B.zero_zero_bounds.1 B.zero_zero_bounds.2.2.2

/-- Under a strict Monge inequality, the optimal matrices are exactly those with maximum
upper-left mass. -/
theorem isOptimal_iff_max_zero_zero (c : Fin 2 × Fin 2 → ℝ)
    (hc : c (0, 0) + c (1, 1) < c (0, 1) + c (1, 0)) :
    (∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ↔
      ∀ B : TransportMatrix μ ν, B.toRealFun (0, 0) ≤ A.toRealFun (0, 0) := by
  constructor
  · intro h B
    exact (A.cost_le_iff_le_zero_zero_of_strict_monge B c hc).mp (h B)
  · intro h B
    exact (A.cost_le_iff_le_zero_zero_of_strict_monge B c hc).mpr (h B)

/-- Under a reverse strict Monge inequality, optimal matrices have minimum upper-left mass. -/
theorem isOptimal_iff_min_zero_zero (c : Fin 2 × Fin 2 → ℝ)
    (hc : c (0, 1) + c (1, 0) < c (0, 0) + c (1, 1)) :
    (∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c) ↔
      ∀ B : TransportMatrix μ ν, A.toRealFun (0, 0) ≤ B.toRealFun (0, 0) := by
  constructor
  · intro h B
    exact (A.cost_le_iff_le_zero_zero_of_reverse_strict_monge B c hc).mp (h B)
  · intro h B
    exact (A.cost_le_iff_le_zero_zero_of_reverse_strict_monge B c hc).mpr (h B)

/-- A strict two by two Monge cost has a unique optimal transportation matrix. -/
theorem existsUnique_optimal_of_strict_monge (c : Fin 2 × Fin 2 → ℝ)
    (μ ν : PMF (Fin 2))
    (hc : c (0, 0) + c (1, 1) < c (0, 1) + c (1, 0)) :
    ∃! A : TransportMatrix μ ν, ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c := by
  obtain ⟨A, hA⟩ := exists_max_zero_zero μ ν
  refine ⟨A, (A.isOptimal_iff_max_zero_zero c hc).2 hA, ?_⟩
  intro B hB
  apply ext_zero_zero
  apply (ENNReal.toReal_eq_toReal_iff' (B.apply_ne_top 0 0) (A.apply_ne_top 0 0)).mp
  simpa only [toRealFun_apply] using
    le_antisymm (hA B) ((B.isOptimal_iff_max_zero_zero c hc).1 hB A)

/-- A reverse strict two by two Monge cost has a unique optimal transportation matrix. -/
theorem existsUnique_optimal_of_reverse_strict_monge (c : Fin 2 × Fin 2 → ℝ)
    (μ ν : PMF (Fin 2))
    (hc : c (0, 1) + c (1, 0) < c (0, 0) + c (1, 1)) :
    ∃! A : TransportMatrix μ ν, ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c := by
  obtain ⟨A, hA⟩ := exists_min_zero_zero μ ν
  refine ⟨A, (A.isOptimal_iff_min_zero_zero c hc).2 hA, ?_⟩
  intro B hB
  apply ext_zero_zero
  apply (ENNReal.toReal_eq_toReal_iff' (B.apply_ne_top 0 0) (A.apply_ne_top 0 0)).mp
  simpa only [toRealFun_apply] using
    le_antisymm ((B.isOptimal_iff_min_zero_zero c hc).1 hB A) (hA B)

end TransportMatrix

end TauCeti
