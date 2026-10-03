/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.BoundedBelow
public import TauCeti.MeasureTheory.OptimalTransport.Duality.LowerSemicontinuous

/-!
# Kantorovich duality for costs bounded below

For an extended-real cost bounded below by integrable marginal terms, subtracting those terms
reduces both the primal and dual problems to the nonnegative cost regime. This file proves weak
duality on arbitrary measurable spaces and strong duality on Polish spaces when the nonnegative
residual is lower semicontinuous. In particular, this holds for lower semicontinuous costs with
upper semicontinuous split lower bounds.

The supremum of the dual values is taken in `EReal`, without truncation at zero: the common value
can be negative or infinite. Feasible potentials are real and integrable, and their constraint is
stated directly as `φ x + ψ y ≤ c (x, y)`. No dual attainment is asserted.

## Main results

* `TauCeti.dualFeasible_residual_iff`: normalization of the signed dual constraint.
* `TauCeti.kantorovichDualValue_le_transportCostBddBelow`: weak duality for signed costs.
* `TauCeti.isLUB_kantorovichDualValue_of_lowerSemicontinuous_residual_bddBelow`: Polish strong
  duality for a lower semicontinuous residual.
* `TauCeti.isLUB_kantorovichDualValue_of_lowerSemicontinuous_bddBelow`: Polish strong duality.
* `TauCeti.transportCostBddBelow_eq_sSup_kantorovichDualValue`: its supremum formula.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Theorem 5.10.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

universe u v

variable {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → EReal} {μ : Measure X} {ν : Measure Y}
  {φ : X → ℝ} {ψ : Y → ℝ}

/-- Subtracting a split lower bound from each potential identifies the signed dual constraint
with dual feasibility for the nonnegative residual cost. -/
-- Normalize before simplification rewrites subtraction inside the potential functions.
@[simp↓]
theorem dualFeasible_residual_iff (h : IntegrableSplitLowerBound c μ ν) :
    DualFeasible (fun z ↦ (h.residual z : EReal))
      (fun x ↦ φ x - h.fst x) (fun y ↦ ψ y - h.snd y) ↔ DualFeasible c φ ψ := by
  rw [dualFeasible_iff, dualFeasible_iff]
  apply forall_congr' fun x ↦ forall_congr' fun y ↦ ?_
  rw [← h.coe_residual_add (x, y)]
  have heq : ((φ x - h.fst x : ℝ) : EReal) + ((ψ y - h.snd y : ℝ) : EReal) +
      ((h.fst x + h.snd y : ℝ) : EReal) = (φ x : EReal) + (ψ y : EReal) := by
    simp only [← EReal.coe_add]
    congr 1
    ring
  rw [← EReal.coe_add (h.fst x) (h.snd y), ← heq]
  exact (EReal.addLECancellable_coe (h.fst x + h.snd y)).add_le_add_iff_right.symm

/-- Weak duality against a fixed coupling for an extended-real cost bounded below by
integrable marginal terms. -/
theorem kantorovichDualValue_le_planCostBddBelow (h : IntegrableSplitLowerBound c μ ν)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hf : DualFeasible c φ ψ)
    {π : Measure (X × Y)} (hπ : IsCoupling π μ ν) :
    (kantorovichDualValue μ ν φ ψ : EReal) ≤ planCostBddBelow π hπ h := by
  have hr := (dualFeasible_residual_iff h).2 hf
  have hv := hr.kantorovichDualValue_le_lintegral
    (hφ.sub h.integrable_fst) (hψ.sub h.integrable_snd) hπ
  rw [kantorovichDualValue_sub hφ hψ h.integrable_fst h.integrable_snd,
    EReal.coe_sub] at hv
  have hv' := (EReal.sub_le_iff_le_add
    (.inl (EReal.coe_ne_bot (kantorovichDualValue μ ν h.fst h.snd)))
    (.inl (EReal.coe_ne_top (kantorovichDualValue μ ν h.fst h.snd)))).1 hv
  simpa only [planCostBddBelow_def, kantorovichDualValue_def, EReal.coe_add, add_assoc] using hv'

/-- Weak duality for the signed primal infimum. No topological, probability, or finite-cost
hypothesis is needed. -/
theorem kantorovichDualValue_le_transportCostBddBelow (h : IntegrableSplitLowerBound c μ ν)
    (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hf : DualFeasible c φ ψ) :
    (kantorovichDualValue μ ν φ ψ : EReal) ≤ transportCostBddBelow c μ ν h :=
  le_transportCostBddBelow h fun _ hπ ↦
    kantorovichDualValue_le_planCostBddBelow h hφ hψ hf hπ

section Polish

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Polish Kantorovich duality for costs bounded below.** If the nonnegative residual of an
integrable split lower bound is lower semicontinuous, the signed primal value is the least upper
bound of the values of all integrable feasible real potentials. The value may be negative or
`∞`; no integrable split upper envelope or dual attainment is assumed. -/
theorem isLUB_kantorovichDualValue_of_lowerSemicontinuous_residual_bddBelow
    (h : IntegrableSplitLowerBound c μ ν) (hres : LowerSemicontinuous h.residual) :
    IsLUB {r : EReal | ∃ (φ : X → ℝ) (ψ : Y → ℝ), Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible c φ ψ ∧
      (kantorovichDualValue μ ν φ ψ : EReal) = r} (transportCostBddBelow c μ ν h) := by
  have hlu := isLUB_ofReal_kantorovichDualValue_integrable_of_lowerSemicontinuous
    (μ := μ) (ν := ν) hres
  constructor
  · rintro r ⟨φ, ψ, hφ, hψ, hf, rfl⟩
    exact kantorovichDualValue_le_transportCostBddBelow h hφ hψ hf
  · intro b hbound
    let k := kantorovichDualValue μ ν h.fst h.snd
    have hk : (k : EReal) ≤ b := hbound
      ⟨h.fst, h.snd, h.integrable_fst, h.integrable_snd,
        dualFeasible_iff.2 (fun x y ↦ by
          simpa only [← EReal.coe_add] using h.le_cost x y), rfl⟩
    have hnonneg : 0 ≤ b - (k : EReal) :=
      (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot k))
        (.inl (EReal.coe_ne_top k))).2 (by simpa using hk)
    have hr : transportCost h.residual μ ν ≤ (b - (k : EReal)).toENNReal := by
      apply hlu.2
      rintro r ⟨φ, ψ, hφ, hψ, hf, rfl⟩
      have hf' : DualFeasible c (fun x ↦ φ x + h.fst x)
          (fun y ↦ ψ y + h.snd y) := by
        apply (dualFeasible_residual_iff h).1
        simpa only [add_sub_cancel_right] using hf
      have hval := hbound ⟨fun x ↦ φ x + h.fst x, fun y ↦ ψ y + h.snd y,
        hφ.add h.integrable_fst, hψ.add h.integrable_snd, hf', rfl⟩
      rw [kantorovichDualValue_add hφ hψ h.integrable_fst h.integrable_snd,
        EReal.coe_add] at hval
      have hs := (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot k))
        (.inl (EReal.coe_ne_top k))).2 hval
      simpa only [EReal.real_coe_toENNReal] using EReal.toENNReal_le_toENNReal hs
    have hr' := EReal.coe_ennreal_le_coe_ennreal_iff.2 hr
    rw [EReal.coe_toENNReal hnonneg] at hr'
    have hfinal := (EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot k))
      (.inl (EReal.coe_ne_top k))).1 hr'
    rw [transportCostBddBelow_eq_transportCost_residual_add_integral_add_integral]
    simpa only [k, kantorovichDualValue_def] using hfinal

/-- The signed transport value is the supremum in `EReal` of all integrable feasible dual
values on Polish spaces when the residual of an integrable split lower bound is lower
semicontinuous. -/
theorem transportCostBddBelow_eq_sSup_kantorovichDualValue_of_lowerSemicontinuous_residual
    (h : IntegrableSplitLowerBound c μ ν) (hres : LowerSemicontinuous h.residual) :
    transportCostBddBelow c μ ν h = sSup {r : EReal | ∃ (φ : X → ℝ) (ψ : Y → ℝ),
      Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible c φ ψ ∧
      (kantorovichDualValue μ ν φ ψ : EReal) = r} :=
  (isLUB_kantorovichDualValue_of_lowerSemicontinuous_residual_bddBelow h hres).sSup_eq.symm

/-- For a lower semicontinuous extended-real cost with an integrable upper semicontinuous split
lower bound on Polish spaces, the signed primal value is the least upper bound of the values of
all integrable feasible real potentials. -/
theorem isLUB_kantorovichDualValue_of_lowerSemicontinuous_bddBelow
    (h : IntegrableSplitLowerBound c μ ν) (hc : LowerSemicontinuous c)
    (ha : UpperSemicontinuous h.fst) (hb : UpperSemicontinuous h.snd) :
    IsLUB {r : EReal | ∃ (φ : X → ℝ) (ψ : Y → ℝ), Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible c φ ψ ∧
      (kantorovichDualValue μ ν φ ψ : EReal) = r} (transportCostBddBelow c μ ν h) := by
  apply isLUB_kantorovichDualValue_of_lowerSemicontinuous_residual_bddBelow h
  rw [funext h.residual_def]
  exact lowerSemicontinuous_residual h.fst h.snd hc ha hb

/-- The signed transport value is the supremum in `EReal` of all integrable feasible dual
values, for lower semicontinuous costs on Polish spaces with an integrable upper semicontinuous
split lower bound. -/
theorem transportCostBddBelow_eq_sSup_kantorovichDualValue
    (h : IntegrableSplitLowerBound c μ ν) (hc : LowerSemicontinuous c)
    (ha : UpperSemicontinuous h.fst) (hb : UpperSemicontinuous h.snd) :
    transportCostBddBelow c μ ν h = sSup {r : EReal | ∃ (φ : X → ℝ) (ψ : Y → ℝ),
      Integrable φ μ ∧ Integrable ψ ν ∧
      DualFeasible c φ ψ ∧
      (kantorovichDualValue μ ν φ ψ : EReal) = r} :=
  (isLUB_kantorovichDualValue_of_lowerSemicontinuous_bddBelow h hc ha hb).sSup_eq.symm

end Polish

end TauCeti
