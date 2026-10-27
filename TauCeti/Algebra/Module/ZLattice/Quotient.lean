/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Quotients by full lattices: compactness and circle coordinates

Let `L : Submodule ℤ E` be a full lattice, `IsZLattice ℝ L`, in a finite-dimensional real normed
space `E`. The orbit space `AddAction.orbitRel.Quotient L E` of translation by `L`, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is the image of a
compact fundamental parallelepiped of the lattice, so it is compact. For a complex vector space
`E` this is the compactness of the complex torus `E / L`.

A lattice basis also supplies circle coordinates on the quotient: reduce its real coordinates
modulo one. The resulting `Module.Basis.quotientLatticeEquiv` is an isomorphism of topological
additive groups onto a product of additive circles.

## Main results

* `Submodule.instCompactSpaceOrbitRelQuotient`: the translation orbit space is compact.
* `QuotientAddGroup.instCompactSpaceOfIsZLattice`: the additive quotient is compact.
* `Module.Basis.latticeCircleCoordinates`: the continuous homomorphism of circle coordinates.
* `Module.Basis.quotientLatticeEquiv`: the quotient is a product of additive circles.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 1, Section 1.1.
-/

public section

/-- The quotient of a finite-dimensional real normed space by a full lattice is compact: it is the
image of a compact fundamental parallelepiped of the lattice. -/
instance Submodule.instCompactSpaceOrbitRelQuotient {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] : CompactSpace (AddAction.orbitRel.Quotient L E) := by
  refine isCompact_univ_iff.1 ?_
  rw [← Set.range_eq_univ.2 _root_.Quotient.mk_surjective]
  refine IsZLattice.isCompact_range_of_periodic L _ continuous_quotient_mk' fun z w hw ↦ ?_
  rw [Submodule.orbitRelQuotient_mk_add, (L.orbitRelQuotient_mk_eq_zero_iff).2 hw, add_zero]

/-- The additive quotient of a finite-dimensional real normed space by a full lattice is compact. -/
instance QuotientAddGroup.instCompactSpaceOfIsZLattice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : AddSubgroup E) [DiscreteTopology L]
    [IsZLattice ℝ L.toIntSubmodule] : CompactSpace (E ⧸ L) := by
  -- Reuse the compact orbit space above. The quotient by L.toIntSubmodule is the quotient
  -- by L: toIntSubmodule retains L as its underlying additive subgroup.
  let e := L.toIntSubmodule.orbitRelQuotientAddEquiv
  apply e.surjective.compactSpace
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  -- The quotient-map criterion uses Quotient.mk', while the evaluation lemma for e uses
  -- Quotient.mk with an explicit relation; expose that constructor to apply the lemma.
  change Continuous (fun x : E => e (_root_.Quotient.mk _ x))
  simpa only [e, Submodule.orbitRelQuotientAddEquiv_mk] using
    (show Continuous (Submodule.Quotient.mk : E → E ⧸ L.toIntSubmodule) from
      continuous_quotient_mk')

noncomputable section

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : AddSubgroup E} [DiscreteTopology L] [IsZLattice ℝ L.toIntSubmodule]
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ L.toIntSubmodule)

/-- Real coordinates in a lattice basis, reduced modulo one. -/
def latticeCircleCoordinates : E →ₜ+ UnitAddTorus ι where
  toFun x i := ((b.ofZLatticeBasis ℝ L.toIntSubmodule).repr x i : UnitAddCircle)
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp (continuous_equivFun_basis (b.ofZLatticeBasis ℝ L.toIntSubmodule)))

@[simp]
theorem latticeCircleCoordinates_apply (x : E) (i : ι) :
    b.latticeCircleCoordinates x i =
      ((b.ofZLatticeBasis ℝ L.toIntSubmodule).repr x i : UnitAddCircle) :=
  (rfl)

/-- The vectors with integral lattice coordinates are exactly the lattice. -/
@[simp]
theorem ker_latticeCircleCoordinates :
    (b.latticeCircleCoordinates : E →+ UnitAddTorus ι).ker = L := by
  ext x
  have hmem := (b.ofZLatticeBasis ℝ L.toIntSubmodule).mem_span_iff_repr_mem ℤ x
  rw [b.ofZLatticeBasis_span ℝ, ← Submodule.mem_toAddSubgroup,
    AddSubgroup.toIntSubmodule_toAddSubgroup] at hmem
  rw [AddMonoidHom.mem_ker, funext_iff]
  simpa [latticeCircleCoordinates_apply, AddCircle.coe_eq_zero_iff, AddSubgroup.mem_zmultiples_iff,
    Set.mem_range] using hmem.symm

/-- Every tuple of circle coordinates is realized by a vector. -/
theorem latticeCircleCoordinates_surjective : Function.Surjective b.latticeCircleCoordinates := by
  intro y
  choose x hx using fun i => QuotientAddGroup.mk_surjective (y i)
  refine ⟨(b.ofZLatticeBasis ℝ L.toIntSubmodule).equivFun.symm x, ?_⟩
  ext i
  rw [latticeCircleCoordinates_apply, ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  exact hx i

/-- A lattice basis identifies the quotient by the lattice with a product of additive circles.
The `i`-th coordinate of a vector is its `i`-th real basis coordinate modulo one. -/
def quotientLatticeEquiv : (E ⧸ L) ≃ₜ+ UnitAddTorus ι :=
  let e := QuotientAddGroup.liftEquiv L
    b.latticeCircleCoordinates_surjective b.ker_latticeCircleCoordinates.symm
  let hc : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr
    simpa only [e, Function.comp_def, QuotientAddGroup.liftEquiv_mk,
      ContinuousAddMonoidHom.coe_toAddMonoidHom, AddMonoidHom.coe_ofClass] using
      map_continuous b.latticeCircleCoordinates
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

@[simp]
theorem quotientLatticeEquiv_apply_mk (x : E) (i : ι) :
    b.quotientLatticeEquiv (QuotientAddGroup.mk x) i =
      ((b.ofZLatticeBasis ℝ L.toIntSubmodule).repr x i : UnitAddCircle) := by
  -- The continuous equivalence extends liftEquiv with continuity proofs. Expose its
  -- underlying lift so liftEquiv_mk can rewrite through the structure extension.
  change QuotientAddGroup.liftEquiv L b.latticeCircleCoordinates_surjective
    b.ker_latticeCircleCoordinates.symm (QuotientAddGroup.mk x) i = _
  rw [QuotientAddGroup.liftEquiv_mk, ContinuousAddMonoidHom.coe_toAddMonoidHom,
    AddMonoidHom.coe_ofClass, latticeCircleCoordinates_apply]

/-- The inverse circle-coordinate map sends reduced real coordinates to their linear combination
in the lattice basis, modulo the lattice. -/
@[simp]
theorem quotientLatticeEquiv_symm_apply (x : ι → ℝ) :
    b.quotientLatticeEquiv.symm (fun i => (x i : UnitAddCircle)) =
      QuotientAddGroup.mk ((b.ofZLatticeBasis ℝ L.toIntSubmodule).equivFun.symm x) := by
  apply b.quotientLatticeEquiv.injective
  ext i
  simp only [ContinuousAddEquiv.apply_symm_apply, quotientLatticeEquiv_apply_mk,
    ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end Module.Basis
