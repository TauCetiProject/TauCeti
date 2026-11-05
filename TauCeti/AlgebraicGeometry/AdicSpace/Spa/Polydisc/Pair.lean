/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc

import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Completion.Homeomorph
import TauCeti.RingTheory.Huber.Restricted.GaussNorm
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.GaussValuation

/-!
# Adic spectrum of the relative closed unit polydisc over a nonarchimedean field

Over a nontrivially normed ultrametric field `K`, the relative closed unit polydisc
`(Pair.powerBounded K).polydisc n` from
`TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Pair.Polydisc` has plus ring equal to the
completion of `K°⟨T₁, …, Tₙ⟩` (`TauCeti.Huber.Pair.weighted_plus_one_weight`), which coincides with
the power-bounded subring `(K⟨T₁, …, Tₙ⟩)°` of the uncompleted restricted power-series ring by the
Gauss-norm unit-ball comparison (`TauCeti.Huber.weightedSubring_powerBoundedSubring_eq`). Combining
this identification with Wedhorn's Proposition 7.48
(`TauCeti.ValuationSpectrum.spaCompletionHomeomorph`) identifies
`spa ((Pair.powerBounded K).polydiscPlus n)` homeomorphically with
`TauCeti.ValuationSpectrum.closedPolydisc n K` without requiring `K` to be complete; when `K` is
complete, the inverse homeomorphism acts on underlying points of `Spv` by pullback along
`TauCeti.Huber.restrictedMvPowerSeriesCompletionEquiv`.

## Main definitions

* `TauCeti.Huber.Pair.polydisc.closedPolydiscHomeomorph`: homeomorphism between
  `spa ((Pair.powerBounded K).polydiscPlus n)` and `closedPolydisc n K` over a nontrivially normed
  ultrametric field `K`.

## Main results

* `TauCeti.Huber.Pair.polydisc.coe_closedPolydiscHomeomorph_apply` and
  `TauCeti.Huber.Pair.polydisc.coe_closedPolydiscHomeomorph_symm_apply`: pointwise descriptions of
  `closedPolydiscHomeomorph` and (when `K` is complete) its inverse on `Spv`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic], Proposition 7.48, Example 7.57, and Remark and
  Definition 8.41.
-/

public section

namespace TauCeti.Huber

open TauCeti.ValuationSpectrum UniformSpace

section NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- **Over a nontrivially normed ultrametric field `K`, the adic spectrum of
`(Pair.powerBounded K).polydisc n` is homeomorphic to `closedPolydisc n K`.** -/
noncomputable def Pair.polydisc.closedPolydiscHomeomorph (n : ℕ) :
    spa ((Pair.powerBounded K).polydiscPlus n) ≃ₜ closedPolydisc n K :=
  (Homeomorph.setCongr (congrArg spa (by
      rw [Pair.polydiscPlus, Pair.polydisc, Pair.completion_plus, Pair.weighted_plus_one_weight,
        Pair.powerBounded_plus, weightedSubring_powerBoundedSubring_eq]))).trans
    ((spaCompletionHomeomorph _).trans (Homeomorph.setCongr (closedPolydisc_def n K).symm))

/-- `closedPolydiscHomeomorph` acts on underlying points of `Spv` by pullback along
`Completion.coeRingHom`. -/
@[simp]
theorem Pair.polydisc.coe_closedPolydiscHomeomorph_apply (n : ℕ)
    (v : spa ((Pair.powerBounded K).polydiscPlus n)) :
    (Pair.polydisc.closedPolydiscHomeomorph n v :
        Spv (weightedRestrictedSubring (fun _ : Fin n ↦ ({1} : Set K))
          isWeightFamily_one_weight)) =
      ValuationSpectrum.comap Completion.coeRingHom v.1 := by
  simp [closedPolydiscHomeomorph, Homeomorph.setCongr]

/-- Over a complete nontrivially normed ultrametric field `K`, the inverse of
`closedPolydiscHomeomorph` acts on underlying points of `Spv` by pullback along
`restrictedMvPowerSeriesCompletionEquiv`. -/
@[simp]
theorem Pair.polydisc.coe_closedPolydiscHomeomorph_symm_apply [CompleteSpace K] (n : ℕ)
    (w : closedPolydisc n K) :
    ((Pair.polydisc.closedPolydiscHomeomorph n).symm w :
        Spv (restrictedMvPowerSeriesCompletion n K)) =
      ValuationSpectrum.comap (restrictedMvPowerSeriesCompletionEquiv n K).toRingHom w.1 := by
  let e := restrictedMvPowerSeriesCompletionEquiv n K
  have hid : Completion.coeRingHom.comp e.toRingHom = RingHom.id _ := by
    ext x
    rw [RingHom.comp_apply, RingHom.id_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact (restrictedMvPowerSeriesCompletionEquiv_symm_apply (e x)).symm.trans
      (e.symm_apply_apply x)
  conv_rhs => rw [← (Pair.polydisc.closedPolydiscHomeomorph n).apply_symm_apply w]
  rw [Pair.polydisc.coe_closedPolydiscHomeomorph_apply,
    ← Function.comp_apply (f := ValuationSpectrum.comap _),
    ← ValuationSpectrum.comap_comp, hid, ValuationSpectrum.comap_id, id]

end NormedField

end TauCeti.Huber
