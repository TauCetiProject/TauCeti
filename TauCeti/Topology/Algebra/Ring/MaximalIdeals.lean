/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Ideals of a topological ring with open unit group

Openness of the unit group makes the closure of a proper ideal proper again: the units are open, so
their complement is a closed set containing the ideal, hence containing its closure. For a maximal
ideal `𝔪` that closure is an ideal squeezed between `𝔪` and the unit ideal, so it is `𝔪` itself and
`𝔪` is closed.

Openness of the unit group is the only topological input, and it stays a hypothesis so that any
route to it can consume this lemma. `TauCeti.RingTheory.Huber.UnitGroup` supplies one for complete
Huber rings and reads Wedhorn's Proposition 7.51 off it, but nothing here mentions completeness, a
nonarchimedean topology, or commutativity: `Ideal A` is the lattice of left ideals of a ring `A`,
and a proper left ideal already avoids the units.

Contrast `TauCeti.Topology.Algebra.Nonarchimedean.MaximalIdeals`, which proves maximal ideals
*open*. That argument needs a linear topology and is vacuous for a Tate ring, where no proper ideal
is open; closedness is the form that survives.

## Main results

* `Ideal.closure_ne_top_of_isOpen_isUnit` : the closure of a proper ideal of a topological ring is
  again proper once the unit group is open.
* `Ideal.isClosed_of_isMaximal_of_isOpen_isUnit` : a maximal ideal of a topological ring is closed
  once the unit group is open.

## Provenance

Adapted from AINTLIB (see References), section `MaximalIdealClosed` of the source file, where the
statement is `isClosed_of_isMaximal_of_isOpen_units`. The argument is that file's; the
commutativity hypothesis is dropped, and the properness step, which uses nothing about maximality,
is separated out as `Ideal.closure_ne_top_of_isOpen_isUnit`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.51.
* [C. Birkbeck, *AINTLIB*](https://github.com/CBirkbeck/AINTLIB), branch `dev/adic-spaces`,
  commit `37bbdaeb`, `projects/AdicSpaces/Adic spaces/AdicSpectrum.lean`.
-/

public section

/-- **The closure of a proper ideal of a topological ring is proper once the unit group is
open.** -/
theorem Ideal.closure_ne_top_of_isOpen_isUnit {A : Type*} [Ring A] [TopologicalSpace A]
    [IsTopologicalRing A] (hU : IsOpen {a : A | IsUnit a}) {J : Ideal A} (hJ : J ≠ ⊤) :
    J.closure ≠ ⊤ := by
  rw [Ideal.ne_top_iff_one]
  exact fun h1 ↦ (closure_minimal (fun x hx ↦ mt (Ideal.eq_top_of_isUnit_mem J hx) hJ)
    hU.isClosed_compl h1) isUnit_one

/-- **A maximal ideal of a topological ring is closed once the unit group is open.** -/
theorem Ideal.isClosed_of_isMaximal_of_isOpen_isUnit {A : Type*} [Ring A] [TopologicalSpace A]
    [IsTopologicalRing A] (hU : IsOpen {a : A | IsUnit a}) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    IsClosed (𝔪 : Set A) := by
  rw [← closure_eq_iff_isClosed, ← Ideal.coe_closure]
  congr 1
  exact (Ideal.IsMaximal.eq_of_le ‹_›
    (Ideal.closure_ne_top_of_isOpen_isUnit hU (Ideal.IsMaximal.ne_top ‹_›))
    fun x hx ↦ subset_closure hx).symm

end
