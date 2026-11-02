/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RepresentationTheory.Continuous.TopRep

/-!
# Complexes of topological representations

A chain map of complexes of monoid representations preserves differential kernels on invariant
vectors. This fact applies to arbitrary complex shapes, independently of any chosen resolution or
cohomology theory.
-/

public section

open CategoryTheory

namespace TopRep

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G]
  {ι : Type*} {s : ComplexShape ι} {J J' : HomologicalComplex (TopRep.{w} k G) s}

/-- A chain map carries an invariant element killed by a differential to an invariant element
killed by the corresponding differential. -/
theorem d_mapInvariants_f_apply (f : J ⟶ J') {i j : ι} (z : (J.X i).ρ.invariants)
    (hz : (J.d i j).hom (z : (J.X i).V) = 0) :
    (J'.d i j).hom ((f.f i).hom.mapInvariants z : (J'.X i).V) = 0 := by
  rw [ContIntertwiningMap.mapInvariants_apply, ← ConcreteCategory.comp_apply, f.comm,
    ConcreteCategory.comp_apply, hz, map_zero]

end TopRep
