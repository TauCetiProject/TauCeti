/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.Restricted.PolydiscReduction

/-!
# Residue reduction of polydisc evaluation

Over a complete ultrametric normed field `K`, evaluating a unit-bounded restricted power series
`f ∈ K°⟨T₁, …, Tₙ⟩` at a power-bounded tuple `a ∈ (K°)ⁿ` lands in `K°` and commutes with
coefficientwise residue reduction `TauCeti.Huber.polydiscReduction n K`.

This file specializes the `weightedEvalHom` reduction results of
`TauCeti.RingTheory.Huber.Restricted.PolydiscReduction` to `TauCeti.ValuationSpectrum.evalAtHom`.

## Main results

* `TauCeti.ValuationSpectrum.evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring`: evaluation
  of a unit-bounded series at a power-bounded tuple is power-bounded.
* `TauCeti.ValuationSpectrum.residue_evalAtHom_eq_eval_polydiscReduction`: residue reduction
  commutes with `evalAtHom`.
* `TauCeti.ValuationSpectrum.norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero`: `‖f(a)‖ = 1`
  iff `polydiscReduction n K f` does not vanish at `ā`.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber
open scoped NormedField Valued

variable {n : ℕ} {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Evaluating a unit-bounded series at a power-bounded tuple yields a power-bounded element. -/
theorem evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring
    (a : Fin n → K) (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    evalAtHom a ha f.val ∈ powerBoundedSubring K := by
  rw [evalAtHom_def]
  exact weightedEvalHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha _ f

/-- **Reduction commutes with evaluation at power-bounded tuples.** For `f ∈ K°⟨T₁, …, Tₙ⟩` and
`a ∈ (K°)ⁿ`, the residue of `f(a)` in `𝓀[K]` equals the value of `polydiscReduction n K f` at
the residue tuple `ā`. -/
theorem residue_evalAtHom_eq_eval_polydiscReduction (a : Fin n → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    IsLocalRing.residue 𝒪[K]
        ⟨evalAtHom a ha f.val,
          (powerBoundedSubring_eq_integer (K := K)).le
            (evalAtHom_mem_powerBoundedSubring_of_mem_weightedSubring a ha f)⟩ =
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue 𝒪[K]
          ⟨a i, (powerBoundedSubring_eq_integer (K := K)).le
            (mem_powerBoundedSubring.mpr (ha i))⟩)
        (polydiscReduction n K f) := by
  simpa only [evalAtHom_def] using
    residue_weightedEvalHom_eq_eval_polydiscReduction a ha
      ((isWeightBounded_one_weight_iff_forall_isPowerBounded (RingHom.id K) a).2 ha) f

/-- A unit-bounded series `f ∈ K°⟨T₁, …, Tₙ⟩` evaluates to an element of norm `1` at `a ∈ (K°)ⁿ`
if and only if its reduction does not vanish at the residue tuple `ā`. -/
theorem norm_evalAtHom_eq_one_iff_eval_polydiscReduction_ne_zero (a : Fin n → K)
    (ha : ∀ i, IsPowerBounded (a i))
    (f : weightedSubring (fun _ : Fin n ↦ ({1} : Set K)) isWeightFamily_one_weight
      (powerBoundedSubring K)) :
    ‖evalAtHom a ha f.val‖ = 1 ↔
      MvPolynomial.eval
        (fun i ↦ IsLocalRing.residue 𝒪[K]
          ⟨a i, (powerBoundedSubring_eq_integer (K := K)).le
            (mem_powerBoundedSubring.mpr (ha i))⟩)
        (polydiscReduction n K f) ≠ 0 := by
  simpa only [evalAtHom_def] using
    norm_weightedEvalHom_eq_one_iff_eval_polydiscReduction_ne_zero a ha
      ((isWeightBounded_one_weight_iff_forall_isPowerBounded (RingHom.id K) a).2 ha) f

end TauCeti.ValuationSpectrum
