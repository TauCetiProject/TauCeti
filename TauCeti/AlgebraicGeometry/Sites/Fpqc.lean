/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fppf covers are jointly surjective

Every point of a scheme lies in the image of some member of any fppf covering sieve, since the
sieve contains a jointly surjective fppf covering family.

## Main results

* `AlgebraicGeometry.Scheme.exists_mem_range_of_mem_fppfTopology`: fppf covering sieves of a
  scheme are jointly surjective.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- **Fppf covers are jointly surjective.** Every point of a scheme lies in the image of some
member of any fppf covering sieve. -/
theorem exists_mem_range_of_mem_fppfTopology {T : Scheme.{u}} {S : Sieve T}
    (hS : S ∈ fppfTopology T) (t : T) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ T), S g ∧ t ∈ Set.range g := by
  have : fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS
  obtain ⟨R, ⟨hsurj, -⟩, hRS⟩ := hS
  obtain ⟨_, _, hg, ht⟩ := hsurj t
  cases hg with
  | @of Y g hg => exact ⟨Y, g, hRS Y g hg, ht⟩

end AlgebraicGeometry.Scheme
