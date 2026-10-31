/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.GroupTheory.IndexNSmul
public import TauCeti.Algebra.Module.Submodule.OrbitRelQuotient
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.Module.ZLattice.Basic
public import TauCeti.Topology.Algebra.Group.DiscontinuousSubgroup
public import TauCeti.Topology.Algebra.Module.Quotient
public import TauCeti.Topology.Algebra.Module.Submodule

/-!
# Quotients by full lattices: compactness, circle coordinates and `L / cL`

Let `L : Submodule ℤ E` be a full lattice, `IsZLattice ℝ L`, in a finite-dimensional real normed
space `E`. The orbit space `AddAction.orbitRel.Quotient L E` of translation by `L`, with the
additive group structure of `E ⧸ L` (`Submodule.orbitRelQuotientAddEquiv`), is the image of a
compact fundamental parallelepiped of the lattice, so it is compact. For a complex vector space
`E` this is the compactness of the complex torus `E / L`.

A lattice basis also supplies circle coordinates on the quotient: reduce its real coordinates
modulo one. The resulting `Module.Basis.quotientLatticeEquiv` is an isomorphism of topological
additive groups onto a product of additive circles.

If `L ∩ V` is a full lattice in a subspace `V`, the map `V / (L ∩ V) → E / L` induced by the
inclusion is a closed embedding, so the compact torus `V / (L ∩ V)` is identified with a closed
subgroup of `E / L`.

For `c : ℕ`, the lattice `cL` is `(c : ℝ) • L`, read in `L` through `Submodule.submoduleOf`. The
quotient `L / cL` has `c ^ n` elements when `L` has rank `n`, so it is finite for `c ≠ 0`.

## Main results

* `Submodule.instCompactSpaceOrbitRelQuotient`: the translation orbit space is compact.
* `QuotientAddGroup.instCompactSpaceOfIsZLattice`: the additive quotient is compact.
* `Module.Basis.latticeCircleCoordinates`: the continuous homomorphism of circle coordinates.
* `Module.Basis.quotientLatticeEquiv`: the quotient is a product of additive circles.
* `Module.Basis.orbitRelQuotientLatticeEquiv`: the same circle coordinates on the orbit space.
* `Submodule.isClosedEmbedding_orbitRelQuotientMap_subtype`: if `L ∩ V` is a full lattice in `V`,
  then `V / (L ∩ V) → E / L` is a closed embedding.
* `ZLattice.card_quotient_smul_submoduleOf`: `L / cL` has `c ^ n` elements for a full lattice
  `L` of rank `n`; it is finite for `c ≠ 0`.

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
    [IsZLattice ℝ L.toIntSubmodule] : CompactSpace (E ⧸ L) :=
  -- Reuse the compact orbit space above. The quotient by L.toIntSubmodule is the quotient
  -- by L: toIntSubmodule retains L as its underlying additive subgroup.
  L.toIntSubmodule.orbitRelQuotientContinuousAddEquiv.surjective.compactSpace
    (map_continuous L.toIntSubmodule.orbitRelQuotientContinuousAddEquiv)

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

namespace Module.Basis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
  (b : Basis ι ℤ L)

/-- A lattice basis identifies the orbit space `E / L` of translation by the lattice with a product
of additive circles: `Module.Basis.quotientLatticeEquiv`, read on the orbit space through
`Submodule.orbitRelQuotientContinuousAddEquiv`. -/
def orbitRelQuotientLatticeEquiv : AddAction.orbitRel.Quotient L E ≃ₜ+ UnitAddTorus ι :=
  -- `quotientLatticeEquiv` is stated for an additive subgroup `L'` through `L'.toIntSubmodule`.
  -- For `L' = L.toAddSubgroup` this submodule is `L` itself, by `AddSubgroup.toIntSubmodule` and
  -- `Submodule.toAddSubgroup` being structure projections, so the instance, the basis `b` and the
  -- quotient `E ⧸ L` are those of `L`.
  haveI : IsZLattice ℝ L.toAddSubgroup.toIntSubmodule := ‹IsZLattice ℝ L›
  L.orbitRelQuotientContinuousAddEquiv.trans (quotientLatticeEquiv (L := L.toAddSubgroup) b)

/-- The `i`-th circle coordinate of the orbit of `x` is the `i`-th real basis coordinate of `x`
modulo one. -/
@[simp]
theorem orbitRelQuotientLatticeEquiv_apply_mk (x : E) (i : ι) :
    b.orbitRelQuotientLatticeEquiv (_root_.Quotient.mk (AddAction.orbitRel L E) x) i =
      ((b.ofZLatticeBasis ℝ L).repr x i : UnitAddCircle) :=
  -- As in `orbitRelQuotientLatticeEquiv`, `L.toAddSubgroup.toIntSubmodule` is `L` by structure
  -- projections. The instance term of the definition is not syntactically `‹IsZLattice ℝ L›`, so
  -- `simp` and `rw` cannot see through it; compose the two evaluation lemmas directly.
  haveI : IsZLattice ℝ L.toAddSubgroup.toIntSubmodule := ‹IsZLattice ℝ L›
  (congrArg (fun y ↦ quotientLatticeEquiv (L := L.toAddSubgroup) b y i)
    (L.orbitRelQuotientContinuousAddEquiv_mk x)).trans
    (quotientLatticeEquiv_apply_mk (L := L.toAddSubgroup) b x i)

/-- The inverse circle coordinates send reduced real coordinates to the orbit of their linear
combination in the lattice basis. -/
@[simp]
theorem orbitRelQuotientLatticeEquiv_symm_apply (x : ι → ℝ) :
    b.orbitRelQuotientLatticeEquiv.symm (fun i => (x i : UnitAddCircle)) =
      _root_.Quotient.mk (AddAction.orbitRel L E) ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by
  apply b.orbitRelQuotientLatticeEquiv.injective
  ext i
  simp only [ContinuousAddEquiv.apply_symm_apply, orbitRelQuotientLatticeEquiv_apply_mk,
    ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

end Module.Basis

/-! ### Subtori -/

section Subtorus

open Topology

variable {K : Type*} [NormedField K] [NormedSpace ℝ K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace K E] [IsScalarTower ℝ K E]
  [FiniteDimensional ℝ E] (L : Submodule ℤ E)

/-- If `L ∩ V` is a full lattice in a subspace `V`, then the map of quotients
`V / (L ∩ V) → E / L` induced by the inclusion of `V` is a closed embedding: the compact torus
`V / (L ∩ V)` is identified with its image, a closed subgroup of `E / L`. -/
theorem Submodule.isClosedEmbedding_orbitRelQuotientMap_subtype [DiscreteTopology L]
    (V : Submodule K E) [IsZLattice ℝ (ZLattice.comap K L V.subtype)] :
    IsClosedEmbedding ((ZLattice.comap K L V.subtype).orbitRelQuotientMap L
      (V.subtype.restrictScalars ℤ) le_rfl) := by
  have : FiniteDimensional ℝ V := .of_injective (V.subtype.restrictScalars ℝ) V.injective_subtype
  refine Continuous.isClosedEmbedding ?_ ?_
  · exact Submodule.continuous_orbitRelQuotientMap _ _ _ continuous_subtype_val
  · exact (Submodule.orbitRelQuotientMap_injective_iff _ _ _ _).2 le_rfl

end Subtorus

/-! ### The quotient `L / cL` -/

open Module Submodule
open scoped Pointwise

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E}

/-- A vector of `L` lies in `cL = (c : ℝ) • L` exactly when it is `c` times a vector of `L`. -/
theorem mem_smul_submoduleOf_iff {c : ℕ} {v : L} :
    v ∈ ((c : ℝ) • L).submoduleOf L ↔ ∃ w : L, c • w = v := by
  rw [submoduleOf, Submodule.mem_comap, subtype_apply, mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, h⟩
    exact ⟨⟨w, hw⟩, Subtype.ext (by rw [← h, Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul])⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, w.2, by rw [Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]⟩

variable (L) [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The quotient `L / cL` of a full lattice of rank `n` has `c ^ n` elements. For `c = 0` this
reads `Nat.card L = 0 ^ n`: the lattice is infinite unless `n = 0`. -/
theorem card_quotient_smul_submoduleOf (c : ℕ) :
    Nat.card (L ⧸ ((c : ℝ) • L).submoduleOf L) = c ^ finrank ℝ E := by
  have h : (((c : ℝ) • L).submoduleOf L).toAddSubgroup = (nsmulAddMonoidHom (α := L) c).range := by
    ext v
    simp [mem_smul_submoduleOf_iff]
  rw [← ZLattice.rank ℝ L, ← AddSubgroup.index_range_nsmul L c, ← h]
  -- The quotient by a submodule is by definition the quotient by its additive subgroup, whose
  -- order is the index.
  rfl

instance (c : ℕ) [NeZero c] : Finite (L ⧸ ((c : ℝ) • L).submoduleOf L) :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_quotient_smul_submoduleOf]
    exact pow_ne_zero _ (NeZero.ne c)

/-- The finite quotient `L / cL` as a `Fintype`, so that finite sums over it, such as the Gauss
sums of a lattice, elaborate for a full lattice and `c ≠ 0`. -/
noncomputable instance instFintypeQuotientSmulSubmoduleOf (c : ℕ) [NeZero c] :
    Fintype (L ⧸ ((c : ℝ) • L).submoduleOf L) :=
  Fintype.ofFinite _

end ZLattice
