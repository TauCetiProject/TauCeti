/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Switching between two maps with the same image law

Let `f` and `g` be almost-everywhere measurable maps, and let `t` be a measurable set that `f` and
`g` enter on the same points almost everywhere. If the image laws of `f` and `g` agree off `t`
(in particular, if `μ.map f = μ.map g`), then following `f` on the preimage of `t` and `g` off it
gives a map with the same image law as `f`.

The typical use is with randomized codings: if two codings `q ↦ (q.1, f q)` and `q ↦ (q.1, g q)`
of the same joint law keep the first coordinate, one may switch between them along any measurable
event of the first coordinate.

## Main results

* `TauCeti.MeasureTheory.Measure.map_ite_mem_eq` — switching between two maps whose image laws
  agree off a measurable set, along an almost-everywhere common preimage of that set, does not
  change the image law.
-/

public section

open Set

namespace TauCeti.MeasureTheory.Measure

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Switching between two maps with the same image law off a set.** If `f` and `g` are
`μ`-a.e. measurable, enter the measurable set `t` on the same points `μ`-almost everywhere, and have
the same image law off `t` (for instance because `μ.map f = μ.map g`), then the map that follows
`f` when the image lies in `t` and `g` otherwise has the same image law as `f`. -/
theorem map_ite_mem_eq {μ : Measure α} {f g : α → β} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {t : Set β} [DecidablePred (· ∈ t)] (ht : MeasurableSet t)
    (hfgt : ∀ᵐ a ∂μ, f a ∈ t ↔ g a ∈ t)
    (hfg : (μ.map f).restrict tᶜ = (μ.map g).restrict tᶜ) :
    μ.map (fun a => if f a ∈ t then f a else g a) = μ.map f := by
  set h := fun a => if f a ∈ t then f a else g a
  have hh : AEMeasurable h μ :=
    (Measurable.ite (ht.preimage measurable_fst) measurable_fst measurable_snd).comp_aemeasurable
      (hf.prodMk hg)
  -- Split both laws into their parts on `t` and on `tᶜ`. Up to null sets the switched map enters
  -- `t` exactly on `f ⁻¹' t`, where it follows `f`; off it, it follows `g`, whose law agrees with
  -- that of `f` off `t`.
  have hpre : h ⁻¹' t =ᵐ[μ] f ⁻¹' t := by
    filter_upwards [hfgt] with a ha
    by_cases hfa : f a ∈ t <;> simp [h, hfa, ← ha]
  have hpre' : f ⁻¹' t =ᵐ[μ] g ⁻¹' t := Filter.eventuallyEqSet_iff.2 hfgt
  have hon : (μ.map h).restrict t = (μ.map f).restrict t := by
    rw [restrict_map_of_aemeasurable hh ht, restrict_map_of_aemeasurable hf ht,
      restrict_congr_set hpre]
    refine map_congr ?_
    filter_upwards [ae_restrict_mem₀ (hf.nullMeasurableSet_preimage ht)] with a (ha : f a ∈ t)
    simp [h, ha]
  have hoff : (μ.map h).restrict tᶜ = (μ.map f).restrict tᶜ := by
    rw [hfg, restrict_map_of_aemeasurable hh ht.compl, restrict_map_of_aemeasurable hg ht.compl,
      preimage_compl, preimage_compl,
      restrict_congr_set (hpre.trans hpre').compl]
    refine map_congr ?_
    filter_upwards [ae_restrict_mem₀ (hg.nullMeasurableSet_preimage ht).compl,
      ae_restrict_of_ae hfgt] with a (ha : g a ∉ t) hfa
    simp [h, hfa.not.2 ha]
  rw [← restrict_add_restrict_compl (μ := μ.map h) ht, hon, hoff, restrict_add_restrict_compl ht]

end TauCeti.MeasureTheory.Measure
