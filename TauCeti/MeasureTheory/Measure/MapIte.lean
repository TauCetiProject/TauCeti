/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Switching between two maps with the same image law

Let `f` and `g` be measurable maps with the same image law, `μ.map f = μ.map g`, and let `t` be a
measurable set that `f` and `g` enter on the same points almost everywhere. Following `f` on
the preimage of that set and `g` off it gives a map with the same image law again.

The typical use is with randomized codings: if two codings `q ↦ (q.1, f q)` and `q ↦ (q.1, g q)`
of the same joint law keep the first coordinate, one may switch between them along any measurable
event of the first coordinate.

## Main results

* `TauCeti.MeasureTheory.Measure.map_ite_mem_eq` — switching between two maps with the same image
  law along an almost-everywhere common measurable preimage does not change the image law.
-/

public section

open Set

namespace TauCeti.MeasureTheory.Measure

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Switching between two maps with the same image law.** If `f` and `g` are measurable with
`μ.map f = μ.map g`, and they enter the measurable set `t` on the same points `μ`-almost everywhere,
then the map that follows `f` when the image lies in `t` and `g` otherwise has the same image
law. -/
theorem map_ite_mem_eq {μ : Measure α} {f g : α → β} (hf : Measurable f) (hg : Measurable g)
    {t : Set β} [DecidablePred (· ∈ t)] (ht : MeasurableSet t)
    (hfgt : ∀ᵐ a ∂μ, f a ∈ t ↔ g a ∈ t)
    (hfg : μ.map f = μ.map g) :
    μ.map (fun a => if f a ∈ t then f a else g a) = μ.map f := by
  have hmeas : Measurable fun a => if f a ∈ t then f a else g a :=
    Measurable.ite (hf ht) hf hg
  ext B hB
  -- Partition using `f`'s preimage, so the two branches are disjoint even on the exceptional set.
  have hsplit : (fun a => if f a ∈ t then f a else g a) ⁻¹' B =
      f ⁻¹' (t ∩ B) ∪ ((f ⁻¹' t)ᶜ ∩ g ⁻¹' B) := by
    ext a
    by_cases ha : f a ∈ t <;> simp [ha]
  have hdisj : Disjoint (f ⁻¹' (t ∩ B)) ((f ⁻¹' t)ᶜ ∩ g ⁻¹' B) := by
    simp only [preimage_inter]
    exact disjoint_compl_right.mono inter_subset_left inter_subset_left
  have hbranch : μ ((f ⁻¹' t)ᶜ ∩ g ⁻¹' B) = μ (g ⁻¹' (tᶜ ∩ B)) := by
    apply measure_congr
    filter_upwards [hfgt] with a ha
    simp only [mem_inter_iff, mem_compl_iff, mem_preimage]
    rw [ha]
  have hcompl : μ (g ⁻¹' (tᶜ ∩ B)) = μ (f ⁻¹' (tᶜ ∩ B)) := by
    rw [← map_apply hg (ht.compl.inter hB), ← hfg, map_apply hf (ht.compl.inter hB)]
  have hpartition : f ⁻¹' (t ∩ B) ∪ f ⁻¹' (tᶜ ∩ B) = f ⁻¹' B := by
    ext a
    by_cases ha : f a ∈ t <;> simp [ha]
  calc
    μ.map (fun a => if f a ∈ t then f a else g a) B =
        μ (f ⁻¹' (t ∩ B) ∪ ((f ⁻¹' t)ᶜ ∩ g ⁻¹' B)) := by
      rw [map_apply hmeas hB, hsplit]
    _ = μ (f ⁻¹' (t ∩ B)) + μ ((f ⁻¹' t)ᶜ ∩ g ⁻¹' B) :=
      measure_union hdisj ((hf ht).compl.inter (hg hB))
    _ = μ (f ⁻¹' (t ∩ B)) + μ (f ⁻¹' (tᶜ ∩ B)) := by rw [hbranch, hcompl]
    _ = μ (f ⁻¹' (t ∩ B) ∪ f ⁻¹' (tᶜ ∩ B)) :=
      (measure_union (Disjoint.preimage f (disjoint_compl_right.mono inter_subset_left
        inter_subset_left)) (hf (ht.compl.inter hB))).symm
    _ = μ (f ⁻¹' B) := congrArg μ hpartition
    _ = μ.map f B := (map_apply hf hB).symm

end TauCeti.MeasureTheory.Measure
