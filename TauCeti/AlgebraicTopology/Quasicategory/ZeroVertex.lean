/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.InitialVertex

/-!
# Zero vertices

A *zero vertex* of a simplicial set `C` (`SSet.IsZeroVertex`) is a vertex which is both initial and
terminal. In a quasicategory this is a zero object, and a quasicategory with a zero vertex is
*pointed*.

## References

* J. Lurie, *Higher Algebra*, Definition 1.1.1.1 (pointed `∞`-categories).
-/

public section

universe u

open CategoryTheory Simplicial

namespace SSet

variable {C : SSet.{u}}

/-- A vertex of a simplicial set is a *zero vertex* if it is both initial and terminal. In a
quasicategory this is a zero object. -/
def IsZeroVertex (x : C _⦋0⦌) : Prop :=
  C.IsInitialVertex x ∧ C.IsTerminalVertex x

lemma isZeroVertex_iff (x : C _⦋0⦌) :
    C.IsZeroVertex x ↔ C.IsInitialVertex x ∧ C.IsTerminalVertex x :=
  Iff.rfl

namespace IsZeroVertex

variable {x : C _⦋0⦌}

/-- A zero vertex is initial. -/
lemma isInitialVertex (hx : C.IsZeroVertex x) : C.IsInitialVertex x :=
  hx.1

/-- A zero vertex is terminal. -/
lemma isTerminalVertex (hx : C.IsZeroVertex x) : C.IsTerminalVertex x :=
  hx.2

/-- Zero vertices are preserved by isomorphisms of simplicial sets. -/
lemma map_iso {D : SSet.{u}} (hx : C.IsZeroVertex x) (e : C ≅ D) :
    D.IsZeroVertex (e.hom.app _ x) :=
  ⟨hx.1.map_iso e, hx.2.map_iso e⟩

end IsZeroVertex

/-- Zero vertices correspond under isomorphisms of simplicial sets. -/
lemma isZeroVertex_iff_of_iso {D : SSet.{u}} (e : C ≅ D) (x : C _⦋0⦌) :
    D.IsZeroVertex (e.hom.app _ x) ↔ C.IsZeroVertex x :=
  and_congr (isInitialVertex_iff_of_iso e x) (isTerminalVertex_iff_of_iso e x)

end SSet
