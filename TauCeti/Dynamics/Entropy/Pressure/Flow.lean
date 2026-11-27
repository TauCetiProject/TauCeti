/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import TauCeti.Dynamics.Entropy.Pressure
public import TauCeti.Dynamics.TopologicalEntropy.Flow
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# Topological pressure of continuous flows

For a continuous real flow `ϕ` on a uniform space and a continuous potential `F : C(X, ℝ)`, the
topological pressure of the flow is the pressure of its time-`1` map for the potential
`F₁ x = ∫ s in 0..1, F (ϕ s x)`, the integral of `F` along the unit flow segment from `x`:

```text
flowTopologicalPressure ϕ F = topologicalPressure (ϕ 1) F₁.
```

The Birkhoff sums of `F₁` under the time-`1` map are the integrals of `F` along flow segments of
integer length: `birkhoffSum (ϕ 1) F₁ n x = ∫ s in 0..n, F (ϕ s x)`. For the zero potential the
flow pressure is the topological entropy of the time-`1` map.

## Main definitions

* `TauCeti.flowTimeOnePotential ϕ F`: the potential `F₁ x = ∫ s in 0..1, F (ϕ s x)`.
* `TauCeti.flowTopologicalPressure ϕ F`: the pressure `topologicalPressure (ϕ 1) F₁`.

## Main results

* `TauCeti.continuous_flowTimeOnePotential`: `F₁` is continuous.
* `TauCeti.birkhoffSum_flowTimeOnePotential`: `birkhoffSum (ϕ 1) F₁ n x = ∫ s in 0..n, F (ϕ s x)`.
* `TauCeti.flowTopologicalPressure_zero`: `flowTopologicalPressure ϕ 0 = coverEntropy (ϕ 1) univ`.
* `TauCeti.flowTopologicalPressure_mono`, `TauCeti.flowTopologicalPressure_add_const`:
  monotonicity in the potential and `P(ϕ, F + c) = P(ϕ, F) + c`.
* `TauCeti.flowTopologicalPressure_id`: for the trivial flow, `F₁ = F` and the flow pressure is the
  pressure of the identity map.

This is the definition and item 3 of §5.5 of the ClassicalErgodicTheory roadmap.
-/

public section

namespace TauCeti

open Dynamics Set intervalIntegral

section Potential

variable {X : Type*} [TopologicalSpace X] (ϕ : Flow ℝ X) (F : C(X, ℝ))

/-- The integral of a potential `F` along the unit flow segment starting at `x`:
`F₁ x = ∫ s in 0..1, F (ϕ s x)`. -/
noncomputable def flowTimeOnePotential (x : X) : ℝ :=
  ∫ s in (0 : ℝ)..1, F (ϕ s x)

theorem flowTimeOnePotential_def (x : X) :
    flowTimeOnePotential ϕ F x = ∫ s in (0 : ℝ)..1, F (ϕ s x) :=
  (rfl)

/-- The potential along a flow line is continuous in time. -/
theorem continuous_potential_flow (x : X) : Continuous fun s : ℝ ↦ F (ϕ s x) :=
  F.continuous.comp (ϕ.continuous continuous_id continuous_const)

/-- The time-`1` potential `F₁` of a continuous potential is continuous. -/
theorem continuous_flowTimeOnePotential : Continuous (flowTimeOnePotential ϕ F) :=
  continuous_parametric_intervalIntegral_of_continuous' (f := fun x s ↦ F (ϕ s x))
    (F.continuous.comp (ϕ.continuous continuous_snd continuous_fst)) 0 1

/-- The Birkhoff sums of `F₁` under the time-`1` map are the integrals of `F` along flow segments
of integer length. -/
theorem birkhoffSum_flowTimeOnePotential (n : ℕ) (x : X) :
    birkhoffSum (ϕ 1) (flowTimeOnePotential ϕ F) n x = ∫ s in (0 : ℝ)..n, F (ϕ s x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hit : (ϕ 1)^[n] x = ϕ n x := by rw [flow_iterate, mul_one]
    have hseg : flowTimeOnePotential ϕ F ((ϕ 1)^[n] x) = ∫ s in (n : ℝ)..(n + 1), F (ϕ s x) := by
      rw [flowTimeOnePotential_def, hit]
      simp_rw [← ϕ.map_add]
      rw [intervalIntegral.integral_comp_add_right (fun s ↦ F (ϕ s x)), zero_add, add_comm]
    rw [birkhoffSum_succ_apply, ih, hseg, Nat.cast_succ,
      integral_add_adjacent_intervals ((continuous_potential_flow ϕ F x).intervalIntegrable _ _)
        ((continuous_potential_flow ϕ F x).intervalIntegrable _ _)]

end Potential

section Pressure

variable {X : Type*} [UniformSpace X] (ϕ : Flow ℝ X) (F : C(X, ℝ))

/-- The topological pressure of a continuous real flow `ϕ` for a continuous potential `F`: the
pressure of the time-`1` map for the potential `F₁ x = ∫ s in 0..1, F (ϕ s x)`. -/
noncomputable def flowTopologicalPressure : EReal :=
  topologicalPressure (ϕ 1) (flowTimeOnePotential ϕ F)

theorem flowTopologicalPressure_def :
    flowTopologicalPressure ϕ F = topologicalPressure (ϕ 1) (flowTimeOnePotential ϕ F) :=
  (rfl)

/-- The pressure of a flow for the zero potential is the topological entropy of its time-`1`
map. -/
@[simp]
theorem flowTopologicalPressure_zero : flowTopologicalPressure ϕ 0 = coverEntropy (ϕ 1) univ := by
  have : flowTimeOnePotential ϕ 0 = 0 := by
    funext x
    simp [flowTimeOnePotential_def]
  rw [flowTopologicalPressure_def, this, topologicalPressure_zero]

variable {F} in
/-- The pressure of a flow is monotone in the potential. -/
theorem flowTopologicalPressure_mono {G : C(X, ℝ)} (h : ∀ x, F x ≤ G x) :
    flowTopologicalPressure ϕ F ≤ flowTopologicalPressure ϕ G :=
  topologicalPressure_mono fun x ↦ integral_mono_on zero_le_one
    ((continuous_potential_flow ϕ F x).intervalIntegrable _ _)
    ((continuous_potential_flow ϕ G x).intervalIntegrable _ _) fun _ _ ↦ h _

/-- Adding a constant `c` to the potential adds `c` to the pressure of a flow. -/
theorem flowTopologicalPressure_add_const (c : ℝ) :
    flowTopologicalPressure ϕ (F + ContinuousMap.const X c) = flowTopologicalPressure ϕ F + c := by
  have : flowTimeOnePotential ϕ (F + ContinuousMap.const X c) =
      fun x ↦ flowTimeOnePotential ϕ F x + c := by
    funext x
    simp only [flowTimeOnePotential_def, ContinuousMap.add_apply, ContinuousMap.const_apply]
    rw [integral_add ((continuous_potential_flow ϕ F x).intervalIntegrable _ _)
      intervalIntegrable_const]
    simp
  rw [flowTopologicalPressure_def, this, topologicalPressure_add_const, flowTopologicalPressure_def]

/-- For the trivial flow the time-`1` potential is `F` itself. -/
@[simp]
theorem flowTimeOnePotential_id : flowTimeOnePotential (Flow.id ℝ X) F = F := by
  funext x
  simp [flowTimeOnePotential_def]

/-- For the trivial flow the flow pressure is the pressure of the identity map. -/
@[simp]
theorem flowTopologicalPressure_id :
    flowTopologicalPressure (Flow.id ℝ X) F = topologicalPressure id F := by
  rw [flowTopologicalPressure_def, flowTimeOnePotential_id, Flow.id_apply]

end Pressure

end TauCeti
