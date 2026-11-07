/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.RamificationLocus
import TauCeti.Topology.Sober

/-!
# Lifting minimal branch points to minimal ramification points

For a morphism locally of finite type, a branch point with no proper generization in the
branch locus has a ramified preimage with no proper generization in the ramification locus.
The preimage can be chosen to generize any prescribed ramified point in its fibre.

This is the topological step transferring purity of the ramification locus to purity of
the branch locus: once the chosen source point has local dimension one, equality of source
and target local dimensions gives the same conclusion at the branch point. No finiteness,
Noetherianity, normality or purity assumption is needed for the lifting step itself.

The argument chooses the generic point of an irreducible component of the closed
ramification locus through the prescribed point. Its image generizes the original branch
point, so minimality of that branch point forces equality of their images.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]

/-- A branch point without proper generizations in the branch locus lifts to a ramified
point without proper generizations in the ramification locus. The lift may be chosen to
generize any prescribed ramified point above the branch point. -/
theorem exists_maximal_ramificationLocus_over_of_maximal_branchLocus
    {y : Y} (hy : ∀ y' ∈ f.branchLocus, y' ⤳ y → y' = y)
    {x : X} (hx : x ∈ f.ramificationLocus) (hxy : f x = y) :
    ∃ z ∈ f.ramificationLocus, z ⤳ x ∧ f z = y ∧
      ∀ z' ∈ f.ramificationLocus, z' ⤳ z → z' = z := by
  let : QuasiSober f.ramificationLocus :=
    (f.isClosed_ramificationLocus).isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨z, hz, hzx⟩ := (f.isClosed_ramificationLocus).exists_genericPoint_specializes hx
  refine ⟨z, z.2, hzx, hy _ ?_ (hxy ▸ hzx.map f.continuous), ?_⟩
  · exact mem_branchLocus_iff.mpr ⟨z, z.2, rfl⟩
  · intro z' hz' hzz'
    exact congrArg Subtype.val ((TauCeti.mem_genericPoints_iff.mp hz) ⟨z', hz'⟩
      ((subtype_specializes_iff _ _).mpr hzz'))

end AlgebraicGeometry.Scheme.Hom
