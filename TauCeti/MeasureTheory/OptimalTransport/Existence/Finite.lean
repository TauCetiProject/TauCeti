/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Existence.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Mixture
public import TauCeti.MeasureTheory.OptimalTransport.Cost.BoundedBelow

/-!
# Primal attainment for finite measures and signed costs

A lower-semicontinuous nonnegative cost on Polish spaces admits an optimal coupling of
finite measures exactly when the two measures have equal mass. This extends probability
attainment by normalization; zero mass is treated by the zero plan, without normalization.
The optimal value is allowed to be infinite.

For an extended-real cost bounded below by integrable marginal terms, attainment follows
by minimizing the nonnegative residual whenever it is lower semicontinuous. Lower
semicontinuity of the cost and upper semicontinuity of the two lower-bound terms suffice
for this hypothesis. The resulting plan minimizes
the signed cost for every choice of integrable split lower bound, not just the one used
in the existence argument.

## References

* C. Villani, *Optimal Transport: Old and New*, Springer, 2009, Theorem 4.1 and Chapter 5.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ]

/-- A lower-semicontinuous cost admits an optimal coupling of finite measures if and only if
their masses agree. Only the first measure needs an explicit finiteness hypothesis:
equal mass makes the second finite as well. Infinite optimal values are permitted. -/
theorem exists_isOptimalCoupling_iff {c : X × Y → ℝ≥0∞} (hc : LowerSemicontinuous c) :
    (∃ π, IsOptimalCoupling c π μ ν) ↔ μ univ = ν univ := by
  refine ⟨fun ⟨_, hπ⟩ ↦ hπ.toIsCoupling.measure_univ_eq, fun hmass ↦ ?_⟩
  have hνfin : IsFiniteMeasure ν := ⟨hmass ▸ measure_lt_top μ univ⟩
  rcases eq_or_ne μ 0 with rfl | hμ
  · have hν : ν = 0 := Measure.measure_univ_eq_zero.mp (by simpa using hmass.symm)
    subst ν
    exact ⟨0, isOptimalCoupling_iff.2 ⟨isCoupling_zero, by simp⟩⟩
  have hμ0 : μ univ ≠ 0 := fun h ↦ hμ (Measure.measure_univ_eq_zero.mp h)
  have hν : ν ≠ 0 := by
    intro h
    exact hμ0 (by simpa [h] using hmass)
  let : NeZero μ := ⟨hμ⟩
  let : NeZero ν := ⟨hν⟩
  obtain ⟨π, hπ⟩ := exists_isOptimalCoupling ((μ univ)⁻¹ • μ) ((ν univ)⁻¹ • ν) hc
  have hscaled := hπ.smul (measure_ne_top μ univ)
  refine ⟨μ univ • π, ?_⟩
  simpa only [← hmass, smul_smul, ENNReal.mul_inv_cancel hμ0 (measure_ne_top μ univ),
    one_smul] using hscaled

/-- An extended-real cost with an integrable split lower bound whose residual is lower
semicontinuous attains its signed transport value between finite equal-mass measures.
The same plan attains the value for every other integrable split lower bound, without any
semicontinuity assumption on that alternative normalization. -/
theorem exists_isCoupling_planCostBddBelow_eq_transportCostBddBelow_of_lowerSemicontinuous_residual
    {c : X × Y → EReal}
    (hmass : μ univ = ν univ) (h : IntegrableSplitLowerBound c μ ν)
    (hres : LowerSemicontinuous h.residual) :
    ∃ (π : Measure (X × Y)) (hπ : IsCoupling π μ ν),
      ∀ k : IntegrableSplitLowerBound c μ ν,
        planCostBddBelow π hπ k = transportCostBddBelow c μ ν k := by
  obtain ⟨π, hπ⟩ := (exists_isOptimalCoupling_iff hres).2 hmass
  have heq : planCostBddBelow π hπ.toIsCoupling h = transportCostBddBelow c μ ν h := by
    rw [planCostBddBelow_def,
      transportCostBddBelow_eq_transportCost_residual_add_integral_add_integral,
      hπ.lintegral_eq, EReal.coe_add, add_assoc]
  refine ⟨π, hπ.toIsCoupling, fun k ↦ ?_⟩
  rw [← planCostBddBelow_congr_lowerBound h k hπ.toIsCoupling,
    ← transportCostBddBelow_congr_lowerBound h k]
  exact heq

/-- A lower-semicontinuous extended-real cost with upper-semicontinuous integrable split
lower bound attains its signed transport value between finite equal-mass measures.
The same plan attains the value for every other integrable split lower bound, without any
semicontinuity assumption on that alternative normalization. -/
theorem exists_isCoupling_planCostBddBelow_eq_transportCostBddBelow {c : X × Y → EReal}
    (hmass : μ univ = ν univ) (h : IntegrableSplitLowerBound c μ ν)
    (hc : LowerSemicontinuous c) (ha : UpperSemicontinuous h.fst)
    (hb : UpperSemicontinuous h.snd) :
    ∃ (π : Measure (X × Y)) (hπ : IsCoupling π μ ν),
      ∀ k : IntegrableSplitLowerBound c μ ν,
        planCostBddBelow π hπ k = transportCostBddBelow c μ ν k := by
  apply exists_isCoupling_planCostBddBelow_eq_transportCostBddBelow_of_lowerSemicontinuous_residual
    hmass h
  rw [funext h.residual_def]
  exact lowerSemicontinuous_residual h.fst h.snd hc ha hb

end TauCeti
