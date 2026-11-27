/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Limit.Basic
public import TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.ConeComposition
public import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.TrivialFibration

/-!
# The mapping-space criterion for limits and colimits

For a quasicategory `C`, a cone is a limit exactly when composition with it induces a weak
homotopy equivalence on each vertex fibre. Dually a cocone is a colimit exactly when
precomposition with it induces these equivalences.
The composition maps and their section factorizations are defined in
`TauCeti.AlgebraicTopology.Quasicategory.MappingSpace.ConeComposition`.

## References

* J. Lurie, *Higher Topos Theory*, Lemma 4.2.4.3.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), §4.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Opposite Simplicial SimplexCategory

namespace SSet

variable {K C : SSet.{u}} {p : K ⟶ C} [Quasicategory C]

namespace slice

variable (y : C _⦋0⦌) (c : (slice p) _⦋0⦌)

/-- `SSet.slice.postcomp y c` is a weak homotopy equivalence exactly when the projection
`Hom^R_C(y, c) ⟶ (C_{/p})_y` is a trivial fibration, since the section of `src` it is built from is
a weak homotopy equivalence. -/
private lemma isWeakHomotopyEquivalence_postcomp_iff :
    IsWeakHomotopyEquivalence (postcomp y c) ↔
      (monomorphisms SSet.{u}).rlp (postcompSpace.tgt y c) := by
  obtain ⟨s, hs, he⟩ := exists_section_postcomp y c
  rw [← he]
  exact isWeakHomotopyEquivalence_section_comp_iff (postcompSpace.rlp_src y c) _ s hs

variable {y c}

variable (c) in
/-- **The mapping-space criterion for limits** (HTT Lemma 4.2.4.3). For a quasicategory `C`, a cone
`c` over a diagram `p : K ⟶ C` is a limit cone exactly when, for every vertex `y` of `C`,
postcomposition with `c` is a weak homotopy equivalence from the right mapping space
`Hom^R_C(y, x)` into the cone point `x` of `c` to the fibre over `y` of the projection
`C_{/p} ⟶ C`. -/
theorem isLimit_iff_forall_isWeakHomotopyEquivalence_postcomp :
    IsLimit p c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (postcomp y c) := by
  simp only [isWeakHomotopyEquivalence_postcomp_iff,
    RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber,
    postcompSpace.isWeaklyContractible_fiber_tgt_iff]
  rw [isLimit_iff, isTerminalVertex_iff_rlp_monomorphisms_π,
    RightFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
  exact ⟨fun h _ d ↦ h d.val, fun h d ↦ by
    simpa only [fiber.coe_basePoint] using h _ (fiber.basePoint (π p) (x := d) rfl)⟩


end slice

namespace coslice

variable (c : (coslice p) _⦋0⦌) (y : C _⦋0⦌)

/-- `SSet.coslice.precomp c y` is a weak homotopy equivalence exactly when the projection
`Hom^L_C(c, y) ⟶ (C_{p/})_y` is a trivial fibration, since the section of `src` it is built from
is a weak homotopy equivalence. -/
private lemma isWeakHomotopyEquivalence_precomp_iff :
    IsWeakHomotopyEquivalence (precomp c y) ↔
      (monomorphisms SSet.{u}).rlp (precompSpace.tgt c y) := by
  obtain ⟨s, hs, he⟩ := exists_section_precomp c y
  rw [← he]
  exact isWeakHomotopyEquivalence_section_comp_iff (precompSpace.rlp_src c y) _ s hs

variable {c y}

variable (c) in
/-- **The mapping-space criterion for colimits**, dually to HTT Lemma 4.2.4.3. For a quasicategory
`C`, a cocone `c` under a diagram `p : K ⟶ C` is a colimit cocone exactly when, for every vertex
`y` of `C`, precomposition with `c` is a weak homotopy equivalence from the left mapping space
`Hom^L_C(x, y)` out of the cocone point `x` of `c` to the fibre over `y` of the projection
`C_{p/} ⟶ C`. -/
theorem isColimit_iff_forall_isWeakHomotopyEquivalence_precomp :
    IsColimit p c ↔ ∀ y : C _⦋0⦌, IsWeakHomotopyEquivalence (precomp c y) := by
  simp only [isWeakHomotopyEquivalence_precomp_iff,
    LeftFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber,
    precompSpace.isWeaklyContractible_fiber_tgt_iff]
  rw [isColimit_iff, isInitialVertex_iff_rlp_monomorphisms_π,
    LeftFibration.rlp_monomorphisms_iff_isWeaklyContractible_fiber]
  exact ⟨fun h _ d ↦ h d.val, fun h d ↦ by
    simpa only [fiber.coe_basePoint] using h _ (fiber.basePoint (π p) (x := d) rfl)⟩


end coslice

end SSet
