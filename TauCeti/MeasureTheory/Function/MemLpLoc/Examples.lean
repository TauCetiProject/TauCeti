/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import TauCeti.MeasureTheory.Function.MemLpLoc.Basic
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Examples of local Lebesgue classes on finite-dimensional spaces

On a nontrivial finite-dimensional real normed space `E` with an additive Haar measure:

* `TauCeti.memLpLoc_norm_inv_iff_lt_finrank`: the singular kernel `x ↦ ‖x‖⁻¹` is locally `Lᵖ` on
  a neighbourhood of the origin exactly when `p < dim E`; in `ℝ³`, exactly when `p < 3`;
* the identity of `E` is locally `Lᵖ` on `E` for every `p` but belongs to no global `Lᵖ` with
  `p ≠ 0` (`TauCeti.not_memLp_id`), so the class is local;
* `StrongDual.memLpLoc_indicator_pos`: the indicator of an open half-space is locally `Lᵖ` for
  every `p`.

The checks at the end test the independence of the Haar measure on the measure `2 • volume`, and
the transport along the coordinate identification of `ℝ × ℝ`, whose norm `max (|y₁|, |y₂|)` is not
an inner product norm, with `EuclideanSpace ℝ (Fin 2)`.

## References

* The inverse-norm and identity checks follow mo271's
  [TauCeti#41136](https://github.com/TauCetiProject/TauCeti/pull/41136).
-/

public section

open MeasureTheory Metric Set
open scoped ENNReal Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] {p : ℝ≥0∞}

/-- On a nontrivial finite-dimensional real normed space, `x ↦ ‖x‖⁻¹` is locally `Lᵖ` on a
neighbourhood `U` of the origin if and only if `p < Module.finrank ℝ E`. -/
theorem memLpLoc_norm_inv_iff_lt_finrank [Nontrivial E] {U : Set E} (hU : U ∈ 𝓝 (0 : E)) :
    MemLpLoc p U (fun x : E => ‖x‖⁻¹) ↔ p < Module.finrank ℝ E := by
  refine ⟨fun h => ?_, fun h => memLpLoc_iff.2 fun K _ hK => hK.memLp_norm_inv_restrict h⟩
  by_contra! hp
  obtain ⟨ε, hε, hεU⟩ := nhds_basis_closedBall.mem_iff.1 hU
  exact not_memLp_norm_inv_closedBall hε hp (memLpLoc_iff.1 h _ hεU (isCompact_closedBall 0 ε))

/-- In `ℝ³`, `x ↦ |x|⁻¹` is locally `Lᵖ` exactly for `p < 3`. -/
example : MemLpLoc p univ (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) ↔ p < 3 := by
  simpa using memLpLoc_norm_inv_iff_lt_finrank (E := EuclideanSpace ℝ (Fin 3)) (p := p)
    Filter.univ_mem

/-- The identity of a nontrivial `E` is locally `Lᵖ` on `E` for every `p`, and not in `Lᵖ(E)`
for any `p ≠ 0`: the class is local. -/
example [Nontrivial E] (hp : p ≠ 0) :
    MemLpLoc p univ (id : E → E) ∧ ¬ MemLp (id : E → E) p volume :=
  ⟨continuous_id.memLpLoc, not_memLp_id hp⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] in
/-- The indicator of an open half-space `{x | 0 < ℓ x}` is locally `Lᵖ` on every set, for every
exponent. -/
theorem _root_.StrongDual.memLpLoc_indicator_pos [OpensMeasurableSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)] (ℓ : StrongDual ℝ E) (U : Set E) :
    MemLpLoc p U ({x : E | 0 < ℓ x}.indicator fun _ => (1 : ℝ)) := memLpLoc_iff.2 fun K _ hK =>
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  memLp_indicator_const p
    (isOpen_lt continuous_const ℓ.continuous).measurableSet.nullMeasurableSet 1
    (Or.inr (measure_ne_top _ _))

/-- Replacing `volume` by `2 • volume` does not change the local `Lᵖ` class. -/
example {F : Type*} [NormedAddCommGroup F] {U : Set E} {f : E → F} :
    MemLpLoc p U f ↔
      ∀ K : Set E, K ⊆ U → IsCompact K → MemLp f p (((2 : ℝ≥0∞) • volume).restrict K) :=
  have : ((2 : ℝ≥0∞) • (volume : Measure E)).IsAddHaarMeasure :=
    .smul _ two_ne_zero ENNReal.ofNat_ne_top
  Measure.memLpLoc_iff_of_isAddHaarMeasure _

/-- `ℝ × ℝ`, with the norm `max (|y₁|, |y₂|)` and product Lebesgue measure, has the local `Lᵖ`
classes of `EuclideanSpace ℝ (Fin 2)` through the identification of coordinates. -/
example {F : Type*} [NormedAddCommGroup F] {V : Set (EuclideanSpace ℝ (Fin 2))}
    {u : EuclideanSpace ℝ (Fin 2) → F} :
    let e : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      ((LinearEquiv.finTwoArrow ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearEquiv).toContinuousLinearEquiv
    MemLpLoc p (e ⁻¹' V) (u ∘ e) ↔ MemLpLoc p V u :=
  have : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  ContinuousLinearEquiv.memLpLoc_comp_iff _

end TauCeti
