/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Relation
public import TauCeti.MeasureTheory.OptimalTransport.Finite.TransportMatrix

/-!
# Uncrossing a finite transport plan

If a transport plan puts positive mass on two crossing cells, transfer the smaller of those
masses to the two uncrossed cells. The row and column marginals stay fixed. Under the Monge
four-point inequality the transfer cannot increase transport cost, and it empties at least one
crossing cell. This is the elementary move used to obtain an optimal monotone coupling on
ordered finite supports.

The update uses four `Pi.single` terms on the product, giving an entrywise formula that also
cancels when the chosen rows or columns coincide. The relation `TransportMatrix.UncrossStep`
records one positive crossing transfer; `TransportMatrix.UncrossStep.cost_le` and
`TransportMatrix.cost_le_of_uncrossSteps` give the Monge cost comparisons for one step and
for a finite sequence.
-/

public section

noncomputable section

open scoped BigOperators

namespace TauCeti
namespace TransportMatrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {μ : PMF ι} {ν : PMF κ}

/-- Transfer the smaller crossing mass to the two uncrossed cells. The resulting plan has the
same marginals, and the formula specifies every entry of the four-cell update. This also applies
when the chosen rows or columns coincide; in that case the update cancels. -/
theorem exists_uncross (A : TransportMatrix μ ν) {i₁ i₂ : ι} {j₁ j₂ : κ} :
    (open Classical in ∃ B : TransportMatrix μ ν, ∃ δ : ℝ,
      0 ≤ δ ∧ δ = min (A.toRealFun (i₁, j₂)) (A.toRealFun (i₂, j₁)) ∧
      (∀ q, B.toRealFun q = A.toRealFun q +
        δ * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q))) := by
  classical
  let f := A.toRealFun
  let δ := min (f (i₁, j₂)) (f (i₂, j₁))
  let g : ι × κ → ℝ := fun q ↦ f q +
    δ * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
      Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
      Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
      Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q)
  have hδ0 : 0 ≤ δ := le_min (A.toRealFun_nonneg _) (A.toRealFun_nonneg _)
  have hδ₁ : δ ≤ f (i₁, j₂) := min_le_left _ _
  have hδ₂ : δ ≤ f (i₂, j₁) := min_le_right _ _
  have hfnonneg : ∀ q, 0 ≤ f q := A.toRealFun_nonneg
  have hg : g ∈ RealPlans μ ν := by
    refine ⟨?_, ?_, ?_⟩
    -- Check entries directly so the proof also covers coincident rows or columns.
    · intro ⟨i, j⟩
      have hfi := hfnonneg (i, j)
      by_cases h₁ : i = i₁ <;> by_cases h₂ : i = i₂ <;>
        by_cases h₃ : j = j₁ <;> by_cases h₄ : j = j₂
      all_goals simp_all [g, Pi.single_apply, Prod.mk.injEq] <;>
        linarith [hfnonneg i j, hfnonneg i₁ j₁, hfnonneg i₁ j₂,
          hfnonneg i₂ j₁, hfnonneg i₂ j₂]
    · intro i
      calc
        ∑ j, g (i, j) = ∑ j, f (i, j) + δ *
            ((if i = i₁ then 1 else 0) + (if i = i₂ then 1 else 0) -
              (if i = i₁ then 1 else 0) - (if i = i₂ then 1 else 0)) := by
                simp [g, Finset.sum_add_distrib, ← Finset.mul_sum,
                  Finset.sum_sub_distrib, Pi.single_apply, Prod.mk.injEq, ite_and]
        _ = ∑ j, f (i, j) := by ring
        _ = (μ i).toReal := A.sum_toRealFun_row i
    · intro j
      calc
        ∑ i, g (i, j) = ∑ i, f (i, j) + δ *
            ((if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0) -
              (if j = j₂ then 1 else 0) - (if j = j₁ then 1 else 0)) := by
                simp [g, Finset.sum_add_distrib, ← Finset.mul_sum,
                  Finset.sum_sub_distrib, Pi.single_apply, Prod.mk.injEq, ite_and]
        _ = ∑ i, f (i, j) := by ring
        _ = (ν j).toReal := A.sum_toRealFun_col j
  refine ⟨ofRealFun hg, δ, hδ0, rfl, ?_⟩
  intro q
  rw [toRealFun_ofRealFun]

/-- The cost change determined by a four-cell update, for any real cost. No sign or
ordering assumptions are needed for this exact formula. -/
theorem cost_eq_of_uncross_update (A B : TransportMatrix μ ν) (c : ι × κ → ℝ)
    (δ : ℝ) (i₁ i₂ : ι) (j₁ j₂ : κ)
    (hB : (open Classical in ∀ q, B.toRealFun q = A.toRealFun q +
      δ * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q))) :
    B.cost c = A.cost c +
      δ * (c (i₁, j₁) + c (i₂, j₂) - c (i₁, j₂) - c (i₂, j₁)) := by
  classical
  rw [B.cost_def, A.cost_def]
  simp_rw [hB, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  calc
    ∑ q, c q * (δ * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
      Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
      Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
      Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q)) =
        δ * ∑ q, c q * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q _
            ring
    _ = _ := by
      simp [mul_add, mul_sub, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, Pi.single_apply]

/-- A four-cell uncrossing empties one crossing cell and does not increase cost whenever
the uncrossed assignment satisfies the local Monge inequality. The same witness and transfer
amount satisfy the exact four-cell update and cost formulas. -/
theorem exists_uncross_cost_le (A : TransportMatrix μ ν) (c : ι × κ → ℝ)
    {i₁ i₂ : ι} {j₁ j₂ : κ} (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hc : c (i₁, j₁) + c (i₂, j₂) ≤ c (i₁, j₂) + c (i₂, j₁)) :
    (open Classical in ∃ B : TransportMatrix μ ν, ∃ δ : ℝ,
      0 ≤ δ ∧ δ = min (A.toRealFun (i₁, j₂)) (A.toRealFun (i₂, j₁)) ∧
      (∀ q, B.toRealFun q = A.toRealFun q +
        δ * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
          Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q)) ∧
      B.cost c = A.cost c +
        δ * (c (i₁, j₁) + c (i₂, j₂) - c (i₁, j₂) - c (i₂, j₁)) ∧
      B.cost c ≤ A.cost c ∧
      (B.toRealFun (i₁, j₂) = 0 ∨ B.toRealFun (i₂, j₁) = 0) ∧
      (∀ q, q ≠ (i₁, j₁) → q ≠ (i₂, j₂) → q ≠ (i₁, j₂) → q ≠ (i₂, j₁) →
        B.toRealFun q = A.toRealFun q)) := by
  classical
  obtain ⟨B, δ, hδ0, hδ, hB⟩ := A.exists_uncross
  have hcost := A.cost_eq_of_uncross_update B c δ i₁ i₂ j₁ j₂ hB
  have hcost_le : B.cost c ≤ A.cost c := by
    rw [hcost]
    have hcross : c (i₁, j₁) + c (i₂, j₂) - c (i₁, j₂) - c (i₂, j₁) ≤ 0 := by
      linarith
    linarith [mul_nonpos_of_nonneg_of_nonpos hδ0 hcross]
  refine ⟨B, δ, hδ0, hδ, hB, hcost, hcost_le, ?_, ?_⟩
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

section Step

variable [LT ι] [LT κ]

/-- One uncrossing step transfers the smaller of two strictly positive crossing masses to
the two uncrossed cells. -/
def UncrossStep (A B : TransportMatrix μ ν) : Prop :=
  (open Classical in ∃ (i₁ i₂ : ι) (j₁ j₂ : κ) (δ : ℝ), i₁ < i₂ ∧ j₁ < j₂ ∧ 0 < δ ∧
    δ = min (A.toRealFun (i₁, j₂)) (A.toRealFun (i₂, j₁)) ∧
    (open Classical in ∀ q, B.toRealFun q = A.toRealFun q +
      δ * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q)))

/-- The crossing witnesses and exact four-cell formula characterizing an uncrossing step. -/
theorem uncrossStep_iff (A B : TransportMatrix μ ν) :
    A.UncrossStep B ↔ (open Classical in
      ∃ (i₁ i₂ : ι) (j₁ j₂ : κ) (δ : ℝ), i₁ < i₂ ∧ j₁ < j₂ ∧ 0 < δ ∧
    δ = min (A.toRealFun (i₁, j₂)) (A.toRealFun (i₂, j₁)) ∧
    (open Classical in ∀ q, B.toRealFun q = A.toRealFun q +
      δ * (Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₁) (1 : ℝ) q +
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₂) (1 : ℝ) q -
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₁, j₂) (1 : ℝ) q -
        Pi.single (M := fun _ : ι × κ ↦ ℝ) (i₂, j₁) (1 : ℝ) q))) := (Iff.rfl)

/-- Each uncrossing step weakly decreases every Monge cost. -/
theorem UncrossStep.cost_le {A B : TransportMatrix μ ν} (h : A.UncrossStep B)
    (c : ι × κ → ℝ)
    (hc : ∀ ⦃i₁ i₂ : ι⦄ ⦃j₁ j₂ : κ⦄, i₁ < i₂ → j₁ < j₂ →
      c (i₁, j₁) + c (i₂, j₂) ≤ c (i₁, j₂) + c (i₂, j₁)) :
    B.cost c ≤ A.cost c := by
  classical
  obtain ⟨i₁, i₂, j₁, j₂, δ, hi, hj, hδ, -, hB⟩ := h
  rw [A.cost_eq_of_uncross_update B c δ i₁ i₂ j₁ j₂ hB]
  have hcross : c (i₁, j₁) + c (i₂, j₂) - c (i₁, j₂) - c (i₂, j₁) ≤ 0 := by
    linarith [hc hi hj]
  linarith [mul_nonpos_of_nonneg_of_nonpos hδ.le hcross]

/-- A finite sequence of uncrossing steps weakly decreases every Monge cost. -/
theorem cost_le_of_uncrossSteps {A B : TransportMatrix μ ν}
    (h : Relation.ReflTransGen UncrossStep A B) (c : ι × κ → ℝ)
    (hc : ∀ ⦃i₁ i₂ : ι⦄ ⦃j₁ j₂ : κ⦄, i₁ < i₂ → j₁ < j₂ →
      c (i₁, j₁) + c (i₂, j₂) ≤ c (i₁, j₂) + c (i₂, j₁)) :
    B.cost c ≤ A.cost c := by
  exact Relation.reflTransGen_le_of_le
    (r := Function.onFun (· ≥ ·) (fun A : TransportMatrix μ ν ↦ A.cost c))
    (fun _ _ hstep ↦ hstep.cost_le c hc) A B h

end Step

end TransportMatrix
end TauCeti
