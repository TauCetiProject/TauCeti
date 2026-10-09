/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Algebra.Homology.Split

/-!
# Complexes of semisimple modules split

Let `K` be a homological complex of modules over a ring `R`, of any shape, whose terms are
semisimple modules; for instance any complex of vector spaces over a division ring, or of modules
over a semisimple ring.  Every submodule of a semisimple module is a direct summand, and every
submodule and quotient of a semisimple module is semisimple.  So in every degree the inclusion of
the cycles is a split monomorphism and the projection of the cycles onto the homology is a split
epimorphism.

By `HomologicalComplex.exists_homotopyEquiv_d_eq_zero`, `K` is therefore chain homotopy equivalent
to a complex with zero differentials, whose terms are the homology of `K`: over a division ring
every complex is homotopy equivalent to its homology.  This reduces statements about the homology
of complexes of vector spaces, such as the Künneth theorem over a field, to complexes with zero
differential.

## Main results

* `HomologicalComplex.isSplitMono_iCycles_of_isSemisimpleModule`: the cycles of a semisimple term
  split off.
* `HomologicalComplex.isSplitEpi_homologyπ_of_isSemisimpleModule`: the homology in a degree with
  semisimple term splits off the cycles.
-/

public section

open CategoryTheory

universe v u

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι) [IsSemisimpleModule R (K.X i)]

/-- The inclusion of the cycles into a semisimple term of a complex of modules is a split
monomorphism. -/
instance isSplitMono_iCycles_of_isSemisimpleModule : IsSplitMono (K.iCycles i) := by
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property (K.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) LinearMap.id
  exact .mk' ⟨ModuleCat.ofHom r, ModuleCat.hom_ext hr⟩

/-- In a degree whose term is semisimple, the projection of the cycles of a complex of modules onto
its homology is a split epimorphism: the cycles are a submodule of a semisimple module, hence
semisimple. -/
instance isSplitEpi_homologyπ_of_isSemisimpleModule : IsSplitEpi (K.homologyπ i) := by
  have := IsSemisimpleModule.of_injective (K.iCycles i).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
  obtain ⟨s, hs⟩ := IsSemisimpleModule.lifting_property (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) LinearMap.id
  exact .mk' ⟨ModuleCat.ofHom s, ModuleCat.hom_ext hs⟩

end HomologicalComplex
