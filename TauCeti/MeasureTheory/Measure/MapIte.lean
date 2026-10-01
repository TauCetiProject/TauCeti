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
measurable set that `f` and `g` enter on the same points, `f ⁻¹' t = g ⁻¹' t`. Following `f` on
that common preimage and `g` off it gives a map with the same image law again.

The typical use is with randomized codings: if two codings `q ↦ (q.1, f q)` and `q ↦ (q.1, g q)`
of the same joint law keep the first coordinate, one may switch between them along any measurable
event of the first coordinate.

## Main results

* `TauCeti.MeasureTheory.Measure.map_ite_mem_eq` — switching between two maps with the same image
  law along a common measurable preimage does not change the image law.
-/

public section

open Set

namespace TauCeti.MeasureTheory.Measure

open _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Switching between two maps with the same image law.** If `f` and `g` are measurable with
`μ.map f = μ.map g`, and they enter the measurable set `t` on the same points, then the map that
follows `f` when the image lies in `t` and `g` otherwise has the same image law. -/
theorem map_ite_mem_eq {μ : Measure α} {f g : α → β} (hf : Measurable f) (hg : Measurable g)
    {t : Set β} [DecidablePred (· ∈ t)] (ht : MeasurableSet t) (hfgt : f ⁻¹' t = g ⁻¹' t)
    (hfg : μ.map f = μ.map g) :
    μ.map (fun a => if f a ∈ t then f a else g a) = μ.map f := by
  have hmeas : Measurable fun a => if f a ∈ t then f a else g a :=
    Measurable.ite (hf ht) hf hg
  ext B hB
  -- The preimage of `B` splits along the common preimage of `t`; on its complement, `g` may be
  -- replaced by `f` because they have the same image law.
  have hsplit : (fun a => if f a ∈ t then f a else g a) ⁻¹' B = f ⁻¹' (t ∩ B) ∪ g ⁻¹' (tᶜ ∩ B) := by
    ext a
    by_cases ha : f a ∈ t
    · have hga : g a ∈ t := show a ∈ g ⁻¹' t by rw [← hfgt]; exact ha
      simp [ha, hga]
    · have hga : g a ∉ t := fun h => ha (show a ∈ f ⁻¹' t by rw [hfgt]; exact h)
      simp [ha, hga]
  have hdisj : Disjoint (f ⁻¹' (t ∩ B)) (g ⁻¹' (tᶜ ∩ B)) :=
    disjoint_left.2 fun a ha hga => hga.1 (show a ∈ g ⁻¹' t by rw [← hfgt]; exact ha.1)
  have hcompl : μ (g ⁻¹' (tᶜ ∩ B)) = μ (f ⁻¹' (tᶜ ∩ B)) := by
    rw [← map_apply hg (ht.compl.inter hB), ← hfg, map_apply hf (ht.compl.inter hB)]
  rw [map_apply hmeas hB, map_apply hf hB, hsplit,
    measure_union hdisj (hg (ht.compl.inter hB)), hcompl,
    ← measure_union (Disjoint.preimage f (disjoint_compl_right.mono inter_subset_left
      inter_subset_left)) (hf (ht.compl.inter hB)), ← preimage_union, ← union_inter_distrib_right,
    union_compl_self, univ_inter]

end TauCeti.MeasureTheory.Measure
