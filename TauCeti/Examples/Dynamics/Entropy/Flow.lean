/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Dynamics.Entropy.Pressure.Flow
public import TauCeti.Dynamics.Flow.Basic
public import TauCeti.Dynamics.TopologicalEntropy.Flow
public import TauCeti.Topology.Instances.AddCircle.Flow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Dynamics.Entropy.Equicontinuous
import Mathlib.MeasureTheory.Group.Integral

/-!
# Worked examples: entropy and pressure of continuous flows

* **Time change.** For `c > 0` the time change `t ↦ ϕ (c * t)` of a flow on a compact space is a
  flow whose time-`1` map has `c` times the entropy of the time-`1` map of `ϕ`: flow entropy
  depends on the time scale.
* **Unit-speed circle flow.** Every time-`t` map of the translation flow of `AddCircle p` is a
  rotation, of entropy `0`; so is the flow's pressure for the zero potential. On `UnitAddCircle`
  the time-`1` map is the identity and the time-`1` potential `F₁ x = ∫ s in 0..1, F (x + s)` is
  the constant `∫ F d volume`, so the flow pressure of every continuous potential `F` is
  `∫ F d volume`.
* **Trivial flow.** For the trivial flow the time-`1` potential is `F` itself, and on a nonempty
  finite space the flow pressure is `max F`, the pressure of the identity map.
-/

public section

open Set Dynamics TauCeti

namespace TauCeti.FlowEntropyExamples

variable {X : Type*} [UniformSpace X] [CompactSpace X]

/-- A time change by `c > 0` multiplies the entropy of the time-`1` map by `c`. -/
example (ϕ : Flow ℝ X) {c : ℝ} (hc : 0 < c) :
    coverEntropy (ϕ.timeChange c 1) univ = c * coverEntropy (ϕ 1) univ := by
  rw [Flow.timeChange_apply, mul_one, coverEntropy_flow_of_pos ϕ hc]

/-- Every time-`t` map of the unit-speed flow on the circle has entropy `0`. -/
example {p : ℝ} [Fact (0 < p)] (t : ℝ) :
    coverEntropy (AddCircle.translationFlow p t) univ = 0 := by
  have h : AddCircle.translationFlow p t = (· + (t : AddCircle p)) := by
    funext x
    simp
  rw [h, coverEntropy_addCircle_add_right_eq_zero]

/-- The unit-speed flow on the circle has pressure `0` for the zero potential. -/
example {p : ℝ} [Fact (0 < p)] :
    flowTopologicalPressure (AddCircle.translationFlow p) 0 = 0 := by
  have h : AddCircle.translationFlow p 1 = (· + ((1 : ℝ) : AddCircle p)) := by
    funext x
    simp
  rw [flowTopologicalPressure_zero, h, coverEntropy_addCircle_add_right_eq_zero]

/-- The entropy of the time-`t` maps of the unit-speed circle flow agrees with
`coverEntropy_flow_univ`: `0 = |t| * 0`. -/
example {p : ℝ} [Fact (0 < p)] (t : ℝ) :
    coverEntropy (AddCircle.translationFlow p t) univ =
      |t| * coverEntropy (AddCircle.translationFlow p 1) univ :=
  coverEntropy_flow_univ _ t

/-- For the trivial flow on a nonempty finite space, the flow pressure is the maximum of the
potential. -/
example {Y : Type*} [UniformSpace Y] [Fintype Y] [Nonempty Y] (F : C(Y, ℝ)) :
    flowTopologicalPressure (Flow.id ℝ Y) F =
      (Finset.univ.sup' Finset.univ_nonempty F : ℝ) := by
  rw [flowTopologicalPressure_id, topologicalPressure_id]

/-- On `UnitAddCircle`, the time-`1` potential of the unit-speed flow is the constant
`∫ F d volume`. -/
theorem flowTimeOnePotential_translationFlow_one (F : C(UnitAddCircle, ℝ)) (x : UnitAddCircle) :
    flowTimeOnePotential (AddCircle.translationFlow 1) F x = ∫ y, F y := by
  rw [flowTimeOnePotential_def]
  simp only [AddCircle.translationFlow_apply]
  have h := UnitAddCircle.intervalIntegral_preimage 0 fun b ↦ F (x + b)
  rw [zero_add] at h
  rw [h]
  exact MeasureTheory.integral_add_left_eq_self (fun y ↦ F y) x

/-- **Check.** The unit-speed flow on `UnitAddCircle` has pressure `∫ F d volume` for every
continuous potential `F`. -/
theorem flowTopologicalPressure_translationFlow_one (F : C(UnitAddCircle, ℝ)) :
    flowTopologicalPressure (AddCircle.translationFlow 1) F = ((∫ y, F y : ℝ) : EReal) := by
  have hid : AddCircle.translationFlow 1 1 = id :=
    (AddCircle.translationFlow_eq_id_iff 1).2 (AddSubgroup.mem_zmultiples 1)
  have hF₁ : flowTimeOnePotential (AddCircle.translationFlow 1) F = fun _ ↦ ∫ y, F y :=
    funext (flowTimeOnePotential_translationFlow_one F)
  rw [flowTopologicalPressure_def, hid, hF₁, topologicalPressure_const,
    coverEntropy_id_eq_zero isCompact_univ.totallyBounded univ_nonempty, zero_add]

end TauCeti.FlowEntropyExamples
