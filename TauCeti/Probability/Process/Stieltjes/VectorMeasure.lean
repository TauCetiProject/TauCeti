/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon
public import Mathlib.Probability.Process.Adapted

/-!
# Finite-horizon vector measures of adapted processes

For strongly adapted processes valued in a complete normed group with BV paths on a finite
horizon, fixed-set evaluations of the derivative vector measure are strongly measurable at the
horizon. This supplies finite-variation integrators without assuming that the original path is
increasing or globally BV. The open initial endpoint excludes an initial atom.

For continuous real paths, the predictable variation parts from
`MeasureTheory.StronglyAdapted.exists_stieltjesFunction_sub_stieltjesFunction` identify it with
the difference of the parts' restricted Stieltjes measures via
`BoundedVariationOn.vectorMeasureIcc_eq_toSignedMeasure_sub`.
-/

public section

open MeasureTheory Set

namespace MeasureTheory.StronglyAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω}
  {R : Type*} [LinearOrder R] [TopologicalSpace R] [OrderTopology R]
  [CompactIccSpace R] [MeasurableSpace R] [BorelSpace R]
  [SecondCountableTopology R] [DenselyOrdered R]
  {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
  {ℱ : Filtration R m} {X : R → Ω → E} {a b : R}

/-- Every fixed-set evaluation of the finite-horizon Stieltjes vector measure of a strongly
adapted process with BV paths on that horizon is strongly measurable at the horizon.
No moments or path regularity outside the horizon are required. -/
theorem stronglyMeasurable_vectorMeasureIcc_apply (hX : StronglyAdapted ℱ X)
    (hab : a ≤ b)
    (hv : ∀ ω, BoundedVariationOn (fun t => X t ω) (Icc a b)) (s : Set R) :
    StronglyMeasurable[ℱ b] (fun ω => (hv ω).vectorMeasureIcc hab s) := by
  let : MeasurableSpace Ω := ℱ b
  exact BoundedVariationOn.stronglyMeasurable_vectorMeasureIcc_apply hab
    (fun _ ht => hX.stronglyMeasurable_le ht.2) hv s

/-- Every fixed-set evaluation of the finite-horizon Stieltjes vector measure of an
adapted process in a second-countable Borel space with BV paths on that horizon is measurable
at the horizon. No moments or path regularity outside the horizon are required. -/
theorem _root_.MeasureTheory.Adapted.measurable_vectorMeasureIcc_apply
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (hX : Adapted ℱ X) (hab : a ≤ b)
    (hv : ∀ ω, BoundedVariationOn (fun t => X t ω) (Icc a b)) (s : Set R) :
    Measurable[ℱ b] (fun ω => (hv ω).vectorMeasureIcc hab s) := by
  let : MeasurableSpace Ω := ℱ b
  exact BoundedVariationOn.measurable_vectorMeasureIcc_apply hab
    (fun _ ht => hX.measurable_le ht.2) hv s

end MeasureTheory.StronglyAdapted
