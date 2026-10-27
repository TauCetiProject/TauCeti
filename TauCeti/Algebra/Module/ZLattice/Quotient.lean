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
# The quotient by a full lattice is compact

Let `L : Submodule ℤ E` be a full lattice, `IsZLattice ℝ L`, in a finite-dimensional real normed
space `E`. The orbit space `AddAction.orbitRel.Quotient L E` of translation by `L`, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is the image of a
compact fundamental parallelepiped of the lattice, so it is compact. For a complex vector space
`E` this is the compactness of the complex torus `E / L`.

A lattice basis also supplies circle coordinates on the quotient: reduce its real coordinates
modulo one. The resulting `Module.Basis.quotientLatticeEquiv` is an isomorphism of topological
additive groups onto a product of additive circles. It uses Mathlib's `Basis.ofZLatticeBasis`
and `QuotientAddGroup.liftEquiv`.

## Main results

* `Submodule.instCompactSpaceOrbitRelQuotient`: the quotient by a full lattice is compact.

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

noncomputable section

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : AddSubgroup E} [DiscreteTopology L] [IsZLattice ℝ L.toIntSubmodule]
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ L.toIntSubmodule)

/-- Real coordinates in a lattice basis, reduced modulo one. -/
def latticeCircleCoordinates : E →+ (ι → AddCircle (1 : ℝ)) where
  toFun x i := ((b.ofZLatticeBasis ℝ L.toIntSubmodule).equivFun x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

@[simp]
theorem latticeCircleCoordinates_apply (x : E) (i : ι) :
    b.latticeCircleCoordinates x i =
      ((b.ofZLatticeBasis ℝ L.toIntSubmodule).repr x i : AddCircle (1 : ℝ)) := by
  simp [latticeCircleCoordinates, Basis.equivFun_apply]

/-- Circle coordinates are continuous. -/
@[fun_prop]
theorem continuous_latticeCircleCoordinates : Continuous b.latticeCircleCoordinates := by
  refine continuous_pi fun i => ?_
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp (continuous_equivFun_basis (b.ofZLatticeBasis ℝ L.toIntSubmodule)))

/-- The vectors with integral lattice coordinates are exactly the lattice. -/
@[simp]
theorem ker_latticeCircleCoordinates : b.latticeCircleCoordinates.ker = L := by
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
def quotientLatticeEquiv : (E ⧸ L) ≃ₜ+ (ι → AddCircle (1 : ℝ)) := by
  let e := QuotientAddGroup.liftEquiv L
    b.latticeCircleCoordinates_surjective b.ker_latticeCircleCoordinates.symm
  have hc : Continuous e := by
    apply (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr
    simpa only [e, Function.comp_def, QuotientAddGroup.liftEquiv_mk] using
      b.continuous_latticeCircleCoordinates
  have hcompact : CompactSpace (E ⧸ L) := by
    have h := IsZLattice.isCompact_range_of_periodic L.toIntSubmodule
      (QuotientAddGroup.mk : E → E ⧸ L) QuotientAddGroup.continuous_mk
      (fun x z hz => by
        rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff z).mpr hz, add_zero])
    rw [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at h
    exact isCompact_univ_iff.mp h
  exact ContinuousAddEquiv.mk e hc
    (e.toEquiv.toHomeomorphOfContinuousClosed hc hc.isClosedMap).symm.continuous

@[simp]
theorem quotientLatticeEquiv_apply_mk (x : E) (i : ι) :
    b.quotientLatticeEquiv (QuotientAddGroup.mk x) i =
      ((b.ofZLatticeBasis ℝ L.toIntSubmodule).repr x i : AddCircle (1 : ℝ)) := by
  unfold quotientLatticeEquiv
  exact b.latticeCircleCoordinates_apply x i

/-- The inverse circle-coordinate map sends reduced real coordinates to their linear combination
in the lattice basis, modulo the lattice. -/
@[simp]
theorem quotientLatticeEquiv_symm_apply (x : ι → ℝ) :
    b.quotientLatticeEquiv.symm (fun i => (x i : AddCircle (1 : ℝ))) =
      QuotientAddGroup.mk ((b.ofZLatticeBasis ℝ L.toIntSubmodule).equivFun.symm x) := by
  apply b.quotientLatticeEquiv.injective
  ext i
  simp only [ContinuousAddEquiv.apply_symm_apply, quotientLatticeEquiv_apply_mk,
    ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end Module.Basis
