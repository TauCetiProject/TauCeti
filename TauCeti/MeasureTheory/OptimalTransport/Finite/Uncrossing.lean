/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix

/-!
# Uncrossing a finite transport plan

If a transport plan puts positive mass on two crossing cells, transfer the smaller of those
masses to the two uncrossed cells. The row and column marginals stay fixed. Under the Monge
four-point inequality the transfer cannot increase transport cost, and it empties at least one
crossing cell. This is the elementary move used to obtain an optimal monotone coupling on
ordered finite supports.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti
namespace TransportMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {μ : PMF ι} {ν : PMF κ}

private abbrev corner (a : ι) (b : κ) (q : ι × κ) : ℝ :=
  Set.indicator {(a, b)} (fun _ ↦ (1 : ℝ)) q

omit [Fintype ι] in
private theorem sum_corner_row (a : ι) (b : κ) (i : ι) :
    ∑ j, corner a b (i, j) = (open scoped Classical in if i = a then 1 else 0) := by
  classical
  by_cases h : i = a
  · subst i
    simp [corner, Set.indicator, Prod.mk.injEq]
  · simp [corner, Set.indicator, h]

omit [Fintype κ] in
private theorem sum_corner_col (a : ι) (b : κ) (j : κ) :
    ∑ i, corner a b (i, j) = (open scoped Classical in if j = b then 1 else 0) := by
  classical
  by_cases h : j = b
  · subst j
    simp [corner, Set.indicator, Prod.mk.injEq]
  · simp [corner, Set.indicator, h]

private theorem sum_cost_corner (c : ι × κ → ℝ) (a : ι) (b : κ) :
    ∑ q, c q * corner a b q = c (a, b) := by
  classical
  simp [corner, Set.indicator]

/-- Transfer the smaller crossing mass to the two uncrossed cells. The resulting plan has the
same marginals, and the formula specifies every entry of the four-cell update. -/
theorem exists_uncross (A : TransportMatrix μ ν) {i₁ i₂ : ι} {j₁ j₂ : κ}
    (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    ∃ B : TransportMatrix μ ν, ∃ δ : ℝ,
      0 ≤ δ ∧ δ = min (A.toRealFun (i₁, j₂)) (A.toRealFun (i₂, j₁)) ∧
      (∀ q, B.toRealFun q = A.toRealFun q +
        δ * (Set.indicator {(i₁, j₁)} (fun _ ↦ (1 : ℝ)) q +
          Set.indicator {(i₂, j₂)} (fun _ ↦ (1 : ℝ)) q -
          Set.indicator {(i₁, j₂)} (fun _ ↦ (1 : ℝ)) q -
          Set.indicator {(i₂, j₁)} (fun _ ↦ (1 : ℝ)) q)) := by
  classical
  let f := A.toRealFun
  let δ := min (f (i₁, j₂)) (f (i₂, j₁))
  let g : ι × κ → ℝ := fun q ↦ f q +
    δ * (corner i₁ j₁ q + corner i₂ j₂ q - corner i₁ j₂ q - corner i₂ j₁ q)
  have hδ0 : 0 ≤ δ := le_min (A.toRealFun_nonneg _) (A.toRealFun_nonneg _)
  have hδ₁ : δ ≤ f (i₁, j₂) := min_le_left _ _
  have hδ₂ : δ ≤ f (i₂, j₁) := min_le_right _ _
  have hfnonneg : ∀ q, 0 ≤ f q := A.toRealFun_nonneg
  have hg : g ∈ RealPlans μ ν := by
    refine ⟨?_, ?_, ?_⟩
    · intro ⟨i, j⟩
      have hfi := hfnonneg (i, j)
      by_cases h₁ : i = i₁ <;> by_cases h₂ : i = i₂ <;>
        by_cases h₃ : j = j₁ <;> by_cases h₄ : j = j₂
      all_goals simp_all [g, corner, Prod.mk.injEq] <;>
        linarith [hfnonneg i j, hfnonneg i₁ j₁, hfnonneg i₁ j₂,
          hfnonneg i₂ j₁, hfnonneg i₂ j₂]
    · intro i
      calc
        ∑ j, g (i, j) = ∑ j, f (i, j) + δ *
            ((if i = i₁ then 1 else 0) + (if i = i₂ then 1 else 0) -
              (if i = i₁ then 1 else 0) - (if i = i₂ then 1 else 0)) := by
                simp only [g, Finset.sum_add_distrib, ← Finset.mul_sum,
                  Finset.sum_sub_distrib, sum_corner_row]
        _ = ∑ j, f (i, j) := by ring
        _ = (μ i).toReal := A.sum_toRealFun_row i
    · intro j
      calc
        ∑ i, g (i, j) = ∑ i, f (i, j) + δ *
            ((if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0) -
              (if j = j₂ then 1 else 0) - (if j = j₁ then 1 else 0)) := by
                simp only [g, Finset.sum_add_distrib, ← Finset.mul_sum,
                  Finset.sum_sub_distrib, sum_corner_col]
        _ = ∑ i, f (i, j) := by ring
        _ = (ν j).toReal := A.sum_toRealFun_col j
  refine ⟨ofRealFun hg, δ, hδ0, rfl, ?_⟩
  intro q
  rw [toRealFun_ofRealFun]

/-- A four-cell uncrossing empties one crossing cell and does not increase cost whenever
the uncrossed assignment satisfies the local Monge inequality. -/
theorem exists_uncross_cost_le (A : TransportMatrix μ ν) (c : ι × κ → ℝ)
    {i₁ i₂ : ι} {j₁ j₂ : κ} (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hc : c (i₁, j₁) + c (i₂, j₂) ≤ c (i₁, j₂) + c (i₂, j₁)) :
    ∃ B : TransportMatrix μ ν, B.cost c ≤ A.cost c ∧
      (B.toRealFun (i₁, j₂) = 0 ∨ B.toRealFun (i₂, j₁) = 0) ∧
      (∀ q, q ≠ (i₁, j₁) → q ≠ (i₂, j₂) → q ≠ (i₁, j₂) → q ≠ (i₂, j₁) →
        B.toRealFun q = A.toRealFun q) := by
  classical
  obtain ⟨B, δ, hδ0, hδ, hB⟩ := A.exists_uncross hi hj
  have hcost : B.cost c = A.cost c +
      δ * (c (i₁, j₁) + c (i₂, j₂) - c (i₁, j₂) - c (i₂, j₁)) := by
    rw [B.cost_def, A.cost_def]
    simp_rw [hB, mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    calc
      ∑ q, c q * (δ * (corner i₁ j₁ q + corner i₂ j₂ q -
        corner i₁ j₂ q - corner i₂ j₁ q)) =
          δ * ∑ q, c q * (corner i₁ j₁ q + corner i₂ j₂ q -
            corner i₁ j₂ q - corner i₂ j₁ q) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q _
              ring
      _ = _ := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, sum_cost_corner]
  have hcost_le : B.cost c ≤ A.cost c := by
    rw [hcost]
    have hcross : c (i₁, j₁) + c (i₂, j₂) - c (i₁, j₂) - c (i₂, j₁) ≤ 0 := by
      linarith
    linarith [mul_nonpos_of_nonneg_of_nonpos hδ0 hcross]
  refine ⟨B, hcost_le, ?_, ?_⟩
  · rcases le_total (A.toRealFun (i₁, j₂)) (A.toRealFun (i₂, j₁)) with h | h
    · left
      rw [hB, hδ, min_eq_left h]
      simp [hi, hj.symm]
    · right
      rw [hB, hδ, min_eq_right h]
      simp [hi.symm, hj]
  · intro q h₁₁ h₂₂ h₁₂ h₂₁
    rw [hB]
    simp [h₁₁, h₂₂, h₁₂, h₂₁]

end TransportMatrix
end TauCeti
