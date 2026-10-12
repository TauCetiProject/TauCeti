/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurability of the continuous functional calculus

For a fixed continuous scalar function `f`, the map `a ↦ cfc f a` is measurable whenever
its defining predicate is measurable. On the predicate, Mathlib's
`ContinuousOn.cfc_of_mem_nhdsSet` supplies continuity; elsewhere the calculus is zero.
The resulting map need not be continuous on the whole algebra.

The theorem `measurable_cfc` generalizes Gaëtan Serré's `CFC.measurable_sqrt`
in `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable`.

This lets continuous spectral functions be applied to random Hermitian matrices without
choosing measurable eigenvectors. It also applies to random self-adjoint elements of
complete normed algebras carrying an isometric continuous functional calculus.

## Main results

* `TauCeti.measurable_cfc`: measurability on the whole algebra, including the zero value
  outside the defining predicate.
* `TauCeti.measurable_cfc_of_predicate`: measurability along a random element satisfying
  the defining predicate, without a measurability assumption on the predicate itself.
-/

public section

open scoped Topology

namespace TauCeti

variable {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A] [StarRing A]
  [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p] [ContinuousStar A]
  [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A]

/-- Applying a fixed continuous scalar function by functional calculus is measurable on
the whole algebra if the defining predicate is measurable. Outside the predicate the
calculus takes the value zero. -/
@[fun_prop]
theorem measurable_cfc {f : 𝕜 → 𝕜} (hf : Continuous f)
    (hp : MeasurableSet {a : A | p a}) : Measurable (cfc f : A → A) := by
  classical
  have hc : ContinuousOn (cfc f : A → A) {a | p a} :=
    continuousOn_id.cfc_of_mem_nhdsSet f (s := Set.univ) Filter.univ_mem
      (fun _ ha ↦ ha) hf.continuousOn
  convert hc.measurable_piecewise (continuousOn_const (c := (0 : A))) hp using 1
  ext a
  by_cases ha : p a
  · simp [Set.piecewise, ha]
  · simp [Set.piecewise, ha, cfc_apply_of_not_predicate a ha]

/-- Continuous functional calculus preserves measurability along a random element
satisfying its defining predicate. The predicate itself need not be measurable. -/
@[fun_prop]
theorem measurable_cfc_of_predicate {X : Type*} [MeasurableSpace X]
    {a : X → A} (ha : Measurable a) (hpa : ∀ x, p (a x))
    {f : 𝕜 → 𝕜} (hf : Continuous f) : Measurable (fun x ↦ cfc f (a x)) := by
  have hc : Continuous (fun b : {b : A | p b} ↦ cfc f (b : A)) :=
    continuous_subtype_val.cfc_of_mem_nhdsSet f (s := Set.univ) Filter.univ_mem
      (fun b ↦ b.property) hf.continuousOn
  exact hc.measurable.comp (ha.subtype_mk (h := hpa))

end TauCeti
