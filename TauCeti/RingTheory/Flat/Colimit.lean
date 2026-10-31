/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Filtered colimits of flat modules

A small filtered colimit of flat modules is flat (Stacks, Lemma 10.39.3 (05UU)). The proof uses
the equational criterion for flatness: a relation `∑ fᵢ xᵢ = 0` in the colimit comes from a
relation at some stage, because finitely many elements and the vanishing of one element are
witnessed at a common stage of a filtered diagram. Flatness of that stage makes the relation
trivial there, and the trivialization maps to the colimit.

## Main results

* `Module.Flat.of_isColimit`: the point of a colimit cocone of a small filtered diagram of flat
  modules is flat.

## References

* [Stacks Project, Tag 05UU](https://stacks.math.columbia.edu/tag/05UU)
-/

public section

open CategoryTheory Limits

universe u

namespace Module.Flat

variable {R : Type u} [CommRing R]

/-- A small filtered colimit of flat modules is flat. -/
@[stacks 05UU]
theorem of_isColimit {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ ModuleCat.{u} R}
    [∀ j, Module.Flat R (F.obj j)] {c : Cocone F} (hc : IsColimit c) : Module.Flat R c.pt := by
  classical
  refine of_forall_isTrivialRelation fun {l f x} hfx => ?_
  -- The finitely many elements `x i` come from a common stage `k`.
  choose j y hy using fun i => Concrete.isColimit_exists_rep F hc (x i)
  let O : Finset J := Finset.univ.image j
  have hO (i : Fin l) : j i ∈ O := Finset.mem_image_of_mem j (Finset.mem_univ i)
  let k := IsFiltered.sup O ∅
  let y' (i : Fin l) : F.obj k := F.map (IsFiltered.toSup O ∅ (hO i)) (y i)
  have hy' (i : Fin l) : c.ι.app k (y' i) = x i := by
    rw [← hy i, ← c.w (IsFiltered.toSup O ∅ (hO i)), ConcreteCategory.comp_apply]
  -- The relation holds at stage `k` up to an element dying in the colimit, so it holds at a
  -- later stage `m`.
  have h0 : c.ι.app k (∑ i, f i • y' i) = c.ι.app k 0 := by
    simp only [map_sum, map_smul, map_zero, hy', hfx]
  obtain ⟨m, g, g', hg⟩ := Concrete.isColimit_exists_of_rep_eq F hc _ _ h0
  have hrel : ∑ i, f i • F.map g (y' i) = 0 := by
    simpa only [map_sum, map_smul, map_zero] using hg
  -- Flatness of the stage `m` trivializes the relation, and the trivialization maps to the
  -- colimit.
  obtain ⟨n, a, z, hz, ha⟩ := isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨n, a, fun t => c.ι.app m (z t), fun i => ?_, ha⟩
  have hi := congrArg (c.ι.app m) (hz i)
  simp only [map_sum, map_smul] at hi
  rw [← hi, ← hy' i, ← c.w g, ConcreteCategory.comp_apply]

end Module.Flat
