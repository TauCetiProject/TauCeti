/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.DPMorphism

/-!
# Lemmas on divided power morphisms

This file supplements `Mathlib.RingTheory.DividedPowers.DPMorphism` with list-product
compatibility for divided power morphisms.

## Main results

* `DividedPowers.IsDPMorphism.map_list_prod_dpow`: a divided power morphism maps a finite product
  of divided powers of elements of `I` to the corresponding product of divided powers of their
  images.
-/

public section

namespace DividedPowers

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {I : Ideal R} {J : Ideal S}
  {hI : DividedPowers I} {hJ : DividedPowers J}

/-- A divided power morphism maps a finite product of divided powers of elements of `I` to the
corresponding product of divided powers of their images. -/
theorem IsDPMorphism.map_list_prod_dpow {f : R →+* S} (hf : IsDPMorphism hI hJ f)
    {l : List (ℕ × R)} (hl : ∀ p ∈ l, p.2 ∈ I) :
    f (l.map fun p ↦ hI.dpow p.1 p.2).prod =
      ((l.map fun p ↦ (p.1, f p.2)).map fun q ↦ hJ.dpow q.1 q.2).prod := by
  rw [map_list_prod]
  simp only [List.map_map]
  congr 1
  exact List.map_congr_left fun p hp ↦ hf.map_dpow (hl p hp)

end DividedPowers
