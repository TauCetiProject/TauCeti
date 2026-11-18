/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

import TauCeti.InformationTheory.KullbackLeibler.ChainRule

/-!
# Relative entropy of finite product measures

Relative entropy tensorizes over finite products of probability measures:
`klDiv (Measure.pi P) (Measure.pi Q) = ∑ i, klDiv (P i) (Q i)`. In particular the relative
entropy between the laws of `n` independent observations from `P` and from `Q` is
`n * klDiv P Q`, the form used in minimax lower bounds for samples of size `n`.

The proof is by induction on the number of factors. `MeasurableEquiv.piFinSuccAbove` splits off
the first coordinate and carries `Measure.pi P` to a binary product; measurable equivalences
preserve relative entropy, since the Radon–Nikodym derivative is transported along them; and the
binary case is `TauCeti.klDiv_prod_prod`.

## Main statements

* `TauCeti.klDiv_map_measurableEquiv`: relative entropy between σ-finite measures is invariant
  under a measurable equivalence.
* `TauCeti.klDiv_pi`: tensorization over `Fin n`.
* `TauCeti.klDiv_pi_const`: `klDiv (P^n) (Q^n) = n * klDiv P Q`.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Section 2.4,
  property (iii) of the Kullback divergence, p. 85.
-/

public section

open MeasureTheory InformationTheory
open scoped ENNReal

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Relative entropy between σ-finite measures is invariant under a measurable equivalence:
the Radon–Nikodym derivative is transported along the equivalence. -/
theorem klDiv_map_measurableEquiv (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    (e : X ≃ᵐ Y) : klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  by_cases hac : μ ≪ ν
  swap
  · refine (klDiv_of_not_ac hac).symm ▸ klDiv_of_not_ac fun h ↦ hac ?_
    simpa [Measure.map_map e.symm.measurable e.measurable] using h.map e.symm.measurable
  have hllr : (fun x ↦ llr (μ.map e) (ν.map e) (e x)) =ᵐ[μ] llr μ ν :=
    hac.ae_le <| by
      filter_upwards [e.measurableEmbedding.rnDeriv_map μ ν] with x hx
      simp [llr, hx]
  have hint : Integrable (llr (μ.map e) (ν.map e)) (μ.map e) ↔ Integrable (llr μ ν) μ := by
    rw [integrable_map_equiv]
    exact integrable_congr hllr
  by_cases hi : Integrable (llr μ ν) μ
  · rw [klDiv_of_ac_of_integrable (hac.map e.measurable) (hint.2 hi),
      klDiv_of_ac_of_integrable hac hi, integral_map_equiv, integral_congr_ae hllr]
    simp [measureReal_def, e.map_apply]
  · rw [klDiv_of_not_integrable hi, klDiv_of_not_integrable (mt hint.1 hi)]

/-- **Tensorization** of relative entropy over finite products of probability measures. -/
theorem klDiv_pi {n : ℕ} (P Q : Fin n → Measure X)
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)] :
    klDiv (Measure.pi P) (Measure.pi Q) = ∑ i, klDiv (P i) (Q i) := by
  induction n with
  | zero => rw [Measure.pi_of_empty P, Measure.pi_of_empty Q]; simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ X) 0
    rw [← klDiv_map_measurableEquiv _ _ e, (measurePreserving_piFinSuccAbove P 0).map_eq,
      (measurePreserving_piFinSuccAbove Q 0).map_eq, klDiv_prod_prod, Fin.sum_univ_succ]
    exact congrArg _ (ih _ _)

/-- Relative entropy between the laws of `n` independent observations from `P` and from `Q`:
`klDiv (P^n) (Q^n) = n * klDiv P Q`. -/
theorem klDiv_pi_const {n : ℕ} (P Q : Measure X) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] :
    klDiv (Measure.pi fun _ : Fin n ↦ P) (Measure.pi fun _ : Fin n ↦ Q) = n * klDiv P Q := by
  simp [klDiv_pi]

end TauCeti
