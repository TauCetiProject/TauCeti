/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Duality
public import TauCeti.MeasureTheory.OptimalTransport.Finite.Uncrossing.Basic

/-!
# Monotone finite transportation matrices

A transportation matrix on two finite linear orders is monotone when its positive entries do
not cross. For any real cost satisfying the Monge four-point inequality there is a monotone
cost-minimizing matrix. Its lower-rectangle masses are the minima of the marginal prefix
masses, so the monotone matrix is unique and minimizes every Monge cost. Negative costs and
zero marginal masses are allowed.

* `IsMonotone.sum_le_le_eq_min` gives the cumulative rectangle formula.
* `existsUnique_isMonotone` gives the unique monotone plan with prescribed marginals.
* `exists_isMonotone_forall_cost_le` produces a monotone Monge-cost minimizer.
* `IsMonotone.forall_cost_le` shows that every monotone plan minimizes every Monge cost.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti
namespace TransportMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [LinearOrder ι] [LinearOrder κ]
  {μ : PMF ι} {ν : PMF κ}

/-- A transportation matrix is monotone when two nonzero entries in increasing rows occur in
weakly increasing columns. Equivalently, its support contains no crossing pair. -/
def IsMonotone (A : TransportMatrix μ ν) : Prop :=
  ∀ ⦃i₁ i₂ : ι⦄ ⦃j₁ j₂ : κ⦄, i₁ < i₂ → A i₁ j₁ ≠ 0 → A i₂ j₂ ≠ 0 → j₁ ≤ j₂

/-- The defining no-crossing property of a monotone transportation matrix. -/
theorem isMonotone_iff (A : TransportMatrix μ ν) :
    A.IsMonotone ↔ ∀ ⦃i₁ i₂ : ι⦄ ⦃j₁ j₂ : κ⦄,
      i₁ < i₂ → A i₁ j₁ ≠ 0 → A i₂ j₂ ≠ 0 → j₁ ≤ j₂ := (Iff.rfl)

/-- The mass of a lower rectangle in a monotone plan is the smaller of the two marginal
prefix masses. This characterizes the joint distribution entirely in terms of the marginals. -/
@[simp]
theorem IsMonotone.sum_le_le_eq_min {A : TransportMatrix μ ν} (hA : A.IsMonotone)
    (i : ι) (j : κ) :
    (∑ i' with i' ≤ i, ∑ j' with j' ≤ j, (A.matrix i' j').toReal) =
      min (∑ i' with i' ≤ i, (μ i').toReal) (∑ j' with j' ≤ j, (ν j').toReal) := by
  classical
  have hsum_real : (∑ i' with i' ≤ i, ∑ j' with j' ≤ j, (A.matrix i' j').toReal) =
      (∑ i' with i' ≤ i, ∑ j' with j' ≤ j, A.toRealFun (i', j')) := by
    simp only [toRealFun_apply]
  rw [hsum_real]
  let H := ∑ i' with i' ≤ i, ∑ j' with j' ≤ j, A.toRealFun (i', j')
  let X := ∑ i' with i' ≤ i, ∑ j' with ¬j' ≤ j, A.toRealFun (i', j')
  let Y := ∑ j' with j' ≤ j, ∑ i' with ¬i' ≤ i, A.toRealFun (i', j')
  have hX : 0 ≤ X := Finset.sum_nonneg fun i' _ ↦
    Finset.sum_nonneg fun j' _ ↦ A.toRealFun_nonneg (i', j')
  have hY : 0 ≤ Y := Finset.sum_nonneg fun j' _ ↦
    Finset.sum_nonneg fun i' _ ↦ A.toRealFun_nonneg (i', j')
  have hrow : H + X = ∑ i' with i' ≤ i, (μ i').toReal := by
    dsimp [H, X]
    rw [← Finset.sum_add_distrib]
    simp only [Finset.sum_filter_add_sum_filter_not, A.sum_toRealFun_row]
  have hcol : H + Y = ∑ j' with j' ≤ j, (ν j').toReal := by
    dsimp [H, Y]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    simp only [Finset.sum_filter_add_sum_filter_not, A.sum_toRealFun_col]
  -- The opposite off-diagonal rectangles cannot both contain positive mass.
  have hzero : X = 0 ∨ Y = 0 := by
    by_cases hex : ∃ i' j', i' ≤ i ∧ ¬j' ≤ j ∧ A i' j' ≠ 0
    · right
      obtain ⟨i₀, j₀, hi₀, hj₀, h₀⟩ := hex
      apply Finset.sum_eq_zero
      intro j' hj'
      apply Finset.sum_eq_zero
      intro i' hi'
      have hi' : i < i' := lt_of_not_ge (Finset.mem_filter.mp hi').2
      have hj' : j' ≤ j := (Finset.mem_filter.mp hj').2
      have hz : A i' j' = 0 := by
        by_contra hn
        have := hA (hi₀.trans_lt hi') h₀ hn
        exact (not_le_of_gt (hj'.trans_lt (lt_of_not_ge hj₀))) this
      simp only [toRealFun_apply, hz, ENNReal.toReal_zero]
    · left
      apply Finset.sum_eq_zero
      intro i' hi'
      apply Finset.sum_eq_zero
      intro j' hj'
      have hz : A i' j' = 0 := by
        by_contra hn
        exact hex ⟨i', j', (Finset.mem_filter.mp hi').2,
          (Finset.mem_filter.mp hj').2, hn⟩
      simp only [toRealFun_apply, hz, ENNReal.toReal_zero]
  rw [← hrow, ← hcol]
  rcases hzero with h | h
  · rw [h, add_zero, min_eq_left (le_add_of_nonneg_right hY)]
  · rw [h, add_zero, min_eq_right (le_add_of_nonneg_right hX)]

/-- Two monotone transportation matrices with the same marginals are equal. -/
theorem IsMonotone.eq {A B : TransportMatrix μ ν} (hA : A.IsMonotone)
    (hB : B.IsMonotone) : A = B := by
  classical
  have hprefix (i : ι) (j : κ) :
      (∑ i' with i' ≤ i, ∑ j' with j' ≤ j, A.toRealFun (i', j')) =
      (∑ i' with i' ≤ i, ∑ j' with j' ≤ j, B.toRealFun (i', j')) := by
    simpa only [toRealFun_apply] using
      (hA.sum_le_le_eq_min i j).trans (hB.sum_le_le_eq_min i j).symm
  -- Induction recovers each entry from its rectangle mass and the earlier entries.
  have hreal : ∀ i j, A.toRealFun (i, j) = B.toRealFun (i, j) := by
    intro i
    apply wellFounded_lt.induction i
    intro i hi j
    apply wellFounded_lt.induction j
    intro j hj
    have hsum : (∑ i' with i' ≤ i, ∑ j' with j' ≤ j,
        (A.toRealFun (i', j') - B.toRealFun (i', j'))) = 0 := by
      simp_rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (hprefix i j)
    rw [Finset.sum_eq_single_of_mem i (by simp) ?_,
      Finset.sum_eq_single_of_mem j (by simp) ?_] at hsum
    · exact sub_eq_zero.mp hsum
    · intro j' hj' hj'ne
      exact sub_eq_zero.mpr (hj j' (lt_of_le_of_ne
        (Finset.mem_filter.mp hj').2 hj'ne))
    · intro i' hi' hi'ne
      apply Finset.sum_eq_zero
      intro j' _
      exact sub_eq_zero.mpr (hi i' (lt_of_le_of_ne
        (Finset.mem_filter.mp hi').2 hi'ne) j')
  apply ext
  intro i j
  have h := congrArg ENNReal.ofReal (hreal i j)
  simpa only [toRealFun_apply, ENNReal.ofReal_toReal (A.apply_ne_top i j),
    ENNReal.ofReal_toReal (B.apply_ne_top i j)] using h

/-- A finite Monge transport problem has a monotone minimizer. The cost may be any real-valued
array satisfying the four-point inequality on increasing rows and columns. -/
theorem exists_isMonotone_forall_cost_le (c : ι × κ → ℝ) (μ : PMF ι) (ν : PMF κ)
    (hc : ∀ ⦃i₁ i₂ : ι⦄ ⦃j₁ j₂ : κ⦄, i₁ < i₂ → j₁ < j₂ →
      c (i₁, j₁) + c (i₂, j₂) ≤ c (i₁, j₂) + c (i₂, j₁)) :
    ∃ A : TransportMatrix μ ν, A.IsMonotone ∧
      ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c := by
  classical
  obtain ⟨r⟩ := nonempty_orderEmbedding_of_finite_infinite ι ℝ
  obtain ⟨s⟩ := nonempty_orderEmbedding_of_finite_infinite κ ℝ
  let t : ι × κ → ℝ := fun q ↦ -(r q.1 * s q.2)
  let C : (ι × κ → ℝ) → ℝ := fun f ↦ ∑ q, c q * f q
  let T : (ι × κ → ℝ) → ℝ := fun f ↦ ∑ q, t q * f q
  have hC : Continuous C :=
    continuous_finsetSum _ fun q _ ↦ continuous_const.mul (continuous_apply q)
  have hT : Continuous T :=
    continuous_finsetSum _ fun q _ ↦ continuous_const.mul (continuous_apply q)
  -- First minimize transport cost, then select the auxiliary minimizer on that compact face.
  obtain ⟨A₀, hA₀⟩ := exists_forall_cost_le c μ ν
  let K : Set (ι × κ → ℝ) := RealPlans μ ν ∩ {f | C f = A₀.cost c}
  have hK : IsCompact K := isCompact_realPlans.inter_right
    (isClosed_eq hC continuous_const)
  have hKne : K.Nonempty :=
    ⟨A₀.toRealFun, A₀.toRealFun_mem_realPlans, (A₀.cost_def c).symm⟩
  obtain ⟨f, hf, hmin⟩ := hK.exists_isMinOn hKne hT.continuousOn
  let A := ofRealFun hf.1
  have hAc : A.cost c = A₀.cost c := (cost_ofRealFun c hf.1).trans hf.2
  have hA : ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c := fun B ↦
    hAc.trans_le (hA₀ B)
  refine ⟨A, ?_, hA⟩
  unfold IsMonotone
  intro i₁ i₂ j₂ j₁ hi h₁ h₂
  by_contra hj
  have hj : j₁ < j₂ := lt_of_not_ge hj
  -- Uncrossing preserves the optimal cost but strictly decreases the negative product score.
  obtain ⟨B, δ, hδ0, hδ, hB, hcost, hle, -⟩ :=
    A.exists_uncross_cost_le c hi.ne hj.ne (hc hi hj)
  have hδpos : 0 < δ := by
    rw [hδ]
    apply lt_min
    · rw [toRealFun_apply]
      exact ENNReal.toReal_pos h₁ (A.apply_ne_top i₁ j₂)
    · rw [toRealFun_apply]
      exact ENNReal.toReal_pos h₂ (A.apply_ne_top i₂ j₁)
  have hBc : B.cost c = A₀.cost c := (le_antisymm hle (hA B)).trans hAc
  have hBt : A.cost t ≤ B.cost t := by
    have hmem : B.toRealFun ∈ K :=
      ⟨B.toRealFun_mem_realPlans, (B.cost_def c).symm.trans hBc⟩
    have := isMinOn_iff.1 hmin _ hmem
    simpa only [A, cost_ofRealFun, cost_def, toRealFun_ofRealFun, T] using this
  have hupdate := A.cost_eq_of_uncross_update B t δ i₁ i₂ j₁ j₂ hB
  have hprod : 0 < (r i₂ - r i₁) * (s j₂ - s j₁) :=
    mul_pos (sub_pos.mpr (r.strictMono hi)) (sub_pos.mpr (s.strictMono hj))
  have hcross : t (i₁, j₁) + t (i₂, j₂) - t (i₁, j₂) - t (i₂, j₁) =
      -((r i₂ - r i₁) * (s j₂ - s j₁)) := by
    dsimp [t]
    ring
  rw [hcross] at hupdate
  linarith [mul_pos hδpos hprod]

/-- Any two probability mass functions on finite linear orders have exactly one monotone
transportation matrix. -/
theorem existsUnique_isMonotone (μ : PMF ι) (ν : PMF κ) :
    ∃! A : TransportMatrix μ ν, A.IsMonotone := by
  obtain ⟨A, hA, -⟩ := exists_isMonotone_forall_cost_le (fun _ ↦ 0) μ ν (by simp)
  exact ⟨A, hA, fun B hB ↦ hB.eq hA⟩

/-- Every monotone transportation matrix minimizes every real Monge cost. The same monotone
plan works for all such costs, since monotonicity and the marginals determine it uniquely. -/
theorem IsMonotone.forall_cost_le {A : TransportMatrix μ ν} (hA : A.IsMonotone)
    (c : ι × κ → ℝ)
    (hc : ∀ ⦃i₁ i₂ : ι⦄ ⦃j₁ j₂ : κ⦄, i₁ < i₂ → j₁ < j₂ →
      c (i₁, j₁) + c (i₂, j₂) ≤ c (i₁, j₂) + c (i₂, j₁)) :
    ∀ B : TransportMatrix μ ν, A.cost c ≤ B.cost c := by
  obtain ⟨M, hM, hmin⟩ := exists_isMonotone_forall_cost_le c μ ν hc
  rw [hA.eq hM]
  exact hmin

end TransportMatrix
end TauCeti
