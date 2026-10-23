/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Duality.BoundedAbove
public import TauCeti.MeasureTheory.OptimalTransport.Cost.BoundedBelow
import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic

/-!
# Dual attainment for signed transport costs

An integrable split lower bound defines the signed transport value without truncating negative
values. An integrable split upper bound makes the normalized problem finite. If the residual
`c - (h.fst + h.snd)` of the split lower bound is lower semicontinuous on a product of Polish
spaces, this file proves attainment for probability marginals by integrable real potentials,
and concentration of every residual-optimal plan on their signed contact relation.

Feasibility holds on a product of full-measure sets. Requiring it at every point would exclude
valid optimizers when the marginals do not have full support. Weak duality is therefore provided
for this same class, on arbitrary measurable spaces. All value equalities take place in `EReal`;
in particular, a negative optimum retains its sign.

The normalization uses `IntegrableSplitLowerBound.residual` and the nonnegative attainment
theorem `IsOptimalCoupling.exists_ae_mem_dualContactSet_of_le_add`. Adding the lower-bound
terms back to the potentials preserves both contact and optimality.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Theorem 5.10 (iii).
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {c : X × Y → EReal} {μ : Measure X} {ν : Measure Y}
  {φ : X → ℝ} {ψ : Y → ℝ}

/-- Weak duality for signed costs and integrable potentials feasible on a product of
full-measure sets. No topological or normalization hypothesis is needed. -/
theorem kantorovichDualValue_le_transportCostBddBelow_of_null_compl
    (h : IntegrableSplitLowerBound c μ ν) {A : Set X} {B : Set Y}
    (hA : μ Aᶜ = 0) (hB : ν Bᶜ = 0) (hφ : Integrable φ μ) (hψ : Integrable ψ ν)
    (hfeas : ∀ x ∈ A, ∀ y ∈ B, ((φ x + ψ y : ℝ) : EReal) ≤ c (x, y)) :
    (kantorovichDualValue μ ν φ ψ : EReal) ≤ transportCostBddBelow c μ ν h := by
  have hr : ∀ x ∈ A, ∀ y ∈ B,
      ENNReal.ofReal ((φ x - h.fst x) + (ψ y - h.snd y)) ≤ h.residual (x, y) := by
    intro x hx y hy
    simpa only [sub_add_sub_comm] using h.ofReal_le_residual_of_le (hfeas x hx y hy)
  have hv := ofReal_kantorovichDualValue_le_transportCost_of_null_compl hA hB
    (hφ.sub h.integrable_fst) (hψ.sub h.integrable_snd) hr
  have hv' := EReal.coe_le_coe_ennreal_of_ofReal_le hv
  simp only [Pi.sub_def] at hv'
  rw [kantorovichDualValue_sub hφ hψ h.integrable_fst h.integrable_snd,
    EReal.coe_sub] at hv'
  have hv'' := (EReal.sub_le_iff_le_add
    (.inl (EReal.coe_ne_bot (kantorovichDualValue μ ν h.fst h.snd)))
    (.inl (EReal.coe_ne_top (kantorovichDualValue μ ν h.fst h.snd)))).1 hv'
  simpa only [transportCostBddBelow_eq_transportCost_residual_add_integral_add_integral,
    kantorovichDualValue_def, EReal.coe_add, add_assoc] using hv''

section Polish

variable [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Every residual-optimal plan admits integrable signed dual optimizers when the residual is
lower semicontinuous and the cost has an integrable split upper bound. The potentials are
feasible on a product of full-measure sets and equal the cost along the given plan. Their value
is the signed primal value for every split lower bound, without any semicontinuity assumption
on the alternative normalization. -/
theorem IsOptimalCoupling.exists_kantorovichDualValue_eq_transportCostBddBelow
    {h : IntegrableSplitLowerBound c μ ν} {π : Measure (X × Y)}
    (hπ : IsOptimalCoupling h.residual π μ ν) (hres : LowerSemicontinuous h.residual)
    {a : X → ℝ} {b : Y → ℝ} (ha : Integrable a μ) (hb : Integrable b ν)
    (hle : ∀ x y, c (x, y) ≤ ((a x + b y : ℝ) : EReal)) :
    ∃ (φ : X → ℝ) (ψ : Y → ℝ) (A : Set X) (B : Set Y),
      MeasurableSet A ∧ MeasurableSet B ∧ μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
      Integrable φ μ ∧ Integrable ψ ν ∧
      (∀ x ∈ A, ∀ y ∈ B, ((φ x + ψ y : ℝ) : EReal) ≤ c (x, y)) ∧
      (∀ᵐ z ∂π, ((φ z.1 + ψ z.2 : ℝ) : EReal) = c z) ∧
      ∀ k : IntegrableSplitLowerBound c μ ν,
        planCostBddBelow π hπ.toIsCoupling k = (kantorovichDualValue μ ν φ ψ : EReal) ∧
        (kantorovichDualValue μ ν φ ψ : EReal) = transportCostBddBelow c μ ν k := by
  -- Subtract the lower-bound terms from the upper envelope as well as the cost.
  have hupper x y : h.residual (x, y) ≤
      ENNReal.ofReal ((a x - h.fst x) + (b y - h.snd y)) := by
    simpa only [sub_add_sub_comm] using h.residual_le_ofReal_of_le (hle x y)
  -- Solve the nonnegative residual problem, then restore the split lower bound.
  obtain ⟨f, g, A, B, hA, hB, hμA, hνB, hf, hg, hfeas, hcontact⟩ :=
    hπ.exists_ae_mem_dualContactSet_of_le_add hres
      (ha.sub h.integrable_fst) (hb.sub h.integrable_snd) hupper
  have hshift (x : X) (y : Y) :
      (((f x + h.fst x) + (g y + h.snd y) : ℝ) : EReal) =
        ((f x + g y : ℝ) : EReal) + ((h.fst x : EReal) + (h.snd y : EReal)) := by
    simp only [← EReal.coe_add]
    congr 1
    ring
  -- Contact identifies the signed plan cost with the shifted dual value.
  have hvalue : planCostBddBelow π hπ.toIsCoupling h =
      (kantorovichDualValue μ ν (fun x ↦ f x + h.fst x)
        (fun y ↦ g y + h.snd y) : EReal) := by
    rw [planCostBddBelow_def,
      lintegral_eq_ofReal_kantorovichDualValue hπ.toIsCoupling hf hg hcontact,
      kantorovichDualValue_add hf hg h.integrable_fst h.integrable_snd,
      EReal.coe_ennreal_ofReal,
      max_eq_left
        (kantorovichDualValue_nonneg_of_ae_mem_dualContactSet hπ.toIsCoupling hf hg hcontact)]
    simp only [kantorovichDualValue_def, EReal.coe_add, add_assoc]
  have hopt : planCostBddBelow π hπ.toIsCoupling h = transportCostBddBelow c μ ν h := by
    rw [planCostBddBelow_def,
      transportCostBddBelow_eq_transportCost_residual_add_integral_add_integral,
      hπ.lintegral_eq, EReal.coe_add, add_assoc]
  refine ⟨fun x ↦ f x + h.fst x, fun y ↦ g y + h.snd y,
    A, B, hA, hB, hμA, hνB, hf.add h.integrable_fst, hg.add h.integrable_snd,
    ?_, ?_, fun k ↦ ?_⟩
  · intro x hx y hy
    rw [hshift, ← h.coe_residual_add (x, y)]
    exact add_le_add (EReal.coe_le_coe_ennreal_of_ofReal_le (hfeas x hx y hy)) le_rfl
  · filter_upwards [hcontact] with z hz
    rw [hshift, mem_dualContactSet_iff.1 hz, h.coe_residual_add]
  · rw [← planCostBddBelow_congr_lowerBound h k hπ.toIsCoupling,
      ← transportCostBddBelow_congr_lowerBound h k]
    exact ⟨hvalue, hvalue.symm.trans hopt⟩

/-- Signed primal and dual attainment for a lower semicontinuous residual and integrable split
bounds. The coupling and potentials satisfy complementary slackness, and their values agree
for every choice of split lower bound. -/
theorem
    exists_isCoupling_kantorovichDualValue_eq_transportCostBddBelow_of_lowerSemicontinuous_residual
    (h : IntegrableSplitLowerBound c μ ν) (hres : LowerSemicontinuous h.residual)
    {a : X → ℝ} {b : Y → ℝ} (ha : Integrable a μ) (hb : Integrable b ν)
    (hle : ∀ x y, c (x, y) ≤ ((a x + b y : ℝ) : EReal)) :
    ∃ (π : Measure (X × Y)) (hπ : IsCoupling π μ ν)
      (φ : X → ℝ) (ψ : Y → ℝ) (A : Set X) (B : Set Y),
      MeasurableSet A ∧ MeasurableSet B ∧ μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
      Integrable φ μ ∧ Integrable ψ ν ∧
      (∀ x ∈ A, ∀ y ∈ B, ((φ x + ψ y : ℝ) : EReal) ≤ c (x, y)) ∧
      (∀ᵐ z ∂π, ((φ z.1 + ψ z.2 : ℝ) : EReal) = c z) ∧
      ∀ k : IntegrableSplitLowerBound c μ ν,
        planCostBddBelow π hπ k = (kantorovichDualValue μ ν φ ψ : EReal) ∧
        (kantorovichDualValue μ ν φ ψ : EReal) = transportCostBddBelow c μ ν k := by
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling μ ν hres
  exact ⟨π, hπ.toIsCoupling,
    hπ.exists_kantorovichDualValue_eq_transportCostBddBelow hres ha hb hle⟩

/-- Signed primal and dual attainment for a lower semicontinuous cost with an upper
semicontinuous integrable split lower bound and an integrable split upper bound. The coupling
and potentials satisfy complementary slackness, with value independent of the lower bound. -/
theorem exists_isCoupling_kantorovichDualValue_eq_transportCostBddBelow
    (h : IntegrableSplitLowerBound c μ ν) (hc : LowerSemicontinuous c)
    (hf : UpperSemicontinuous h.fst) (hg : UpperSemicontinuous h.snd)
    {a : X → ℝ} {b : Y → ℝ} (ha : Integrable a μ) (hb : Integrable b ν)
    (hle : ∀ x y, c (x, y) ≤ ((a x + b y : ℝ) : EReal)) :
    ∃ (π : Measure (X × Y)) (hπ : IsCoupling π μ ν)
      (φ : X → ℝ) (ψ : Y → ℝ) (A : Set X) (B : Set Y),
      MeasurableSet A ∧ MeasurableSet B ∧ μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
      Integrable φ μ ∧ Integrable ψ ν ∧
      (∀ x ∈ A, ∀ y ∈ B, ((φ x + ψ y : ℝ) : EReal) ≤ c (x, y)) ∧
      (∀ᵐ z ∂π, ((φ z.1 + ψ z.2 : ℝ) : EReal) = c z) ∧
      ∀ k : IntegrableSplitLowerBound c μ ν,
        planCostBddBelow π hπ k = (kantorovichDualValue μ ν φ ψ : EReal) ∧
        (kantorovichDualValue μ ν φ ψ : EReal) = transportCostBddBelow c μ ν k := by
  apply
    exists_isCoupling_kantorovichDualValue_eq_transportCostBddBelow_of_lowerSemicontinuous_residual
      h ?_ ha hb hle
  rw [funext h.residual_def]
  exact lowerSemicontinuous_residual h.fst h.snd hc hf hg

end Polish

end TauCeti
