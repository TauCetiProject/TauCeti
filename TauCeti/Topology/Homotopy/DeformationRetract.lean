/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Composing strong deformation retractions

Two successive strong deformation retractions compose: first deform onto the intermediate
space, then run its deformation after the first retraction. The resulting homotopy fixes
the image of the final inclusion throughout. Inclusions are expressed as continuous maps,
so the result also applies to subspaces represented by different but homeomorphic types.
-/

public section

open Set Function

namespace ContinuousMap.HomotopicRel

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Compose the relative homotopies of two strong deformation retractions. The first
retraction must be a left inverse of its inclusion; no separation or closedness is needed. -/
theorem comp_retractions {i : C(Y, X)} {j : C(Z, Y)} {r : C(X, Y)} {s : C(Y, Z)}
    (hX : (ContinuousMap.id X).HomotopicRel (i.comp r) (range i))
    (hY : (ContinuousMap.id Y).HomotopicRel (j.comp s) (range j))
    (hr : LeftInverse r i) :
    (ContinuousMap.id X).HomotopicRel ((i.comp j).comp (s.comp r)) (range (i.comp j)) := by
  obtain ⟨H⟩ := hX
  obtain ⟨G⟩ := hY
  let H' : (ContinuousMap.id X).HomotopyRel (i.comp r) (range (i.comp j)) :=
    { H with prop' := fun t x hx => H.eq_fst t (by
        obtain ⟨z, rfl⟩ := hx
        exact mem_range_self (j z)) }
  let G' : (i.comp r).HomotopyRel ((i.comp j).comp (s.comp r))
      (range (i.comp j)) :=
    { toFun := fun p => i (G (p.1, r p.2))
      continuous_toFun := i.continuous.comp
        (G.continuous.comp (continuous_fst.prodMk (r.continuous.comp continuous_snd)))
      map_zero_left := fun x => by simp
      map_one_left := fun x => by simp
      prop' := by
        rintro t x ⟨z, rfl⟩
        simpa only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, hr (j z),
          ContinuousMap.id_apply] using congrArg i (G.eq_fst t (mem_range_self z)) }
  exact ⟨H'.trans G'⟩

end ContinuousMap.HomotopicRel
