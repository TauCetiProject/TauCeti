/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Covering sieves of the fppf topology

Every point of a scheme lies in the image of some member of any fppf covering sieve, since the
sieve contains a jointly surjective fppf covering family. On the big fppf site of a scheme `S`,
the base change `T ×_S S' ⟶ T` of a surjective flat morphism `p : S' ⟶ S`, locally of finite
presentation, generates a covering sieve of `T`.

## Main results

* `AlgebraicGeometry.Scheme.exists_mem_range_of_mem_fppfTopology`: fppf covering sieves of a
  scheme are jointly surjective.
* `AlgebraicGeometry.Scheme.Hom.generate_singleton_counit_mem_fppfTopology_over`: the base change
  `T ×_S S' ⟶ T` of an fppf morphism generates a covering sieve of the big fppf site.
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

namespace AlgebraicGeometry.Scheme.Hom

open Limits

universe u

variable {S S' : Scheme.{u}} (p : S' ⟶ S)

/-- The base change `T ×_S S' ⟶ T` of a surjective flat morphism `p : S' ⟶ S`, locally of finite
presentation, generates a covering sieve of `T` on the big fppf site of `S`. -/
theorem generate_singleton_counit_mem_fppfTopology_over [Surjective p] [Flat p]
    [LocallyOfFinitePresentation p] (T : Over S) :
    Sieve.generate (.singleton ((Over.mapPullbackAdj p).counit.app T)) ∈
      (fppfTopology.over S) T := by
  rw [← Presieve.ofArrows_pUnit.{0}, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Presieve.ofArrows_pUnit, Over.mapPullbackAdj_counit_app]
  exact (pullback.fst T.hom p).singleton_mem_fppfPrecoverage

end AlgebraicGeometry.Scheme.Hom
