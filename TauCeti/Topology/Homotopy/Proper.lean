/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper homotopy equivalences

A continuous map `f : X → Y` is a *proper homotopy equivalence*
(`ContinuousMap.HasProperHomotopyInverse`) if it is proper and has a proper homotopy inverse
`g : Y → X` for which both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` are proper as maps
`I × X → X` and `I × Y → Y`. These are the equivalences of the proper homotopy category, in which
invariants at infinity such as simple connectivity at infinity live.

Every homeomorphism is a proper homotopy equivalence (`Homeomorph.hasProperHomotopyInverse`).

## References

* F. T. Farrell, L. R. Taylor, J. B. Wagoner, *The Whitehead theorem in the proper category*,
  Compositio Math. 27 (1973), 1–23.
-/

public section

open scoped unitInterval

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map `f : X → Y` is a **proper homotopy equivalence** if it is proper and has a
proper homotopy inverse `g`, with both homotopies `g ∘ f ≃ id` and `f ∘ g ≃ id` proper as maps
`I × X → X` and `I × Y → Y`. -/
def HasProperHomotopyInverse (f : C(X, Y)) : Prop :=
  IsProperMap f ∧ ∃ g : C(Y, X), IsProperMap g ∧
    ∃ H : Homotopy (g.comp f) (ContinuousMap.id X), ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y),
      IsProperMap H ∧ IsProperMap H'

namespace HasProperHomotopyInverse

/-- A proper map with a proper inverse `g` up to proper homotopies `g ∘ f ≃ id` and
`f ∘ g ≃ id` is a proper homotopy equivalence. -/
theorem intro {f : C(X, Y)} (hf : IsProperMap f) (g : C(Y, X)) (hg : IsProperMap g)
    (H : Homotopy (g.comp f) (ContinuousMap.id X)) (H' : Homotopy (f.comp g) (ContinuousMap.id Y))
    (hH : IsProperMap H) (hH' : IsProperMap H') : f.HasProperHomotopyInverse :=
  ⟨hf, g, hg, H, H', hH, hH'⟩

/-- A proper homotopy equivalence is a proper map. -/
theorem isProperMap {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) : IsProperMap f :=
  hf.1

/-- A proper homotopy equivalence has a proper homotopy inverse `g`, with proper homotopies
`g ∘ f ≃ id` and `f ∘ g ≃ id`. -/
theorem exists_inverse {f : C(X, Y)} (hf : f.HasProperHomotopyInverse) :
    ∃ g : C(Y, X), IsProperMap g ∧
      ∃ H : Homotopy (g.comp f) (ContinuousMap.id X),
        ∃ H' : Homotopy (f.comp g) (ContinuousMap.id Y), IsProperMap H ∧ IsProperMap H' :=
  hf.2

end HasProperHomotopyInverse

end ContinuousMap

/-- A homeomorphism is a proper homotopy equivalence, with constant homotopies: these are the
projections `I × X → X` and `I × Y → Y`, which are proper as `I` is compact. -/
theorem Homeomorph.hasProperHomotopyInverse {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) : (e : C(X, Y)).HasProperHomotopyInverse := by
  refine .intro e.isProperMap e.symm e.symm.isProperMap
    ((ContinuousMap.Homotopy.refl _).cast rfl e.symm_comp_toContinuousMap)
    ((ContinuousMap.Homotopy.refl _).cast rfl e.toContinuousMap_comp_symm) ?_ ?_ <;>
  · convert isProperMap_snd_of_compactSpace (X := I) using 1
    ext x
    simp
