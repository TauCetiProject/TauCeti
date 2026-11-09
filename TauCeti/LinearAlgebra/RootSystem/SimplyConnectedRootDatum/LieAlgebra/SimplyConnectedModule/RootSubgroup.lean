/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Primitive
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.SimplyConnectedModule.Lattice
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Injective
import TauCeti.Algebra.Lie.DirectSum

/-!
# Injective simple-root parameters on the full-weight lattice

Every positive and negative numbered simple-root map on the full-weight lattice is
injective over every commutative ring, including nonreduced rings. The fundamental
summand at node `i` detects the `i`-th root parameter: its highest vector and its first
lowering form a primitive two-dimensional root string. Consequently the polynomial
Kostant action cannot lose the parameter after scalar extension.

The maps here are the existing `kostantRootSubgroupParam` on `scLattice`; no new
ambient group is introduced. The argument uses the integral normalization of the
fundamental highest vector, rather than nonvanishing of a rational root operator.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
-/

public section

namespace TauCeti.DynkinType

open _root_.DirectSum _root_.TauCeti.UniversalEnvelopingAlgebra

noncomputable section

-- Match the tensor module used by the integral point action.
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

local notation "ρ" => representation ℚ (t.lieAlgebra ht) (t.scModule ht)
local notation "M" => Submodule.toAddSubgroup (t.scLattice ht)
local notation "e" => LieAlgebra.Basis.rootGenerator (t.lieBasis ht)
local notation "h" => LieAlgebra.Basis.h (t.lieBasis ht)
local notation "rootOp" => kostantRootOperator e h ρ M (t.kostantForm_apply_mem_scLattice ht)

private def highest (i : Fin t.rank) : M :=
  ⟨lof ℚ _ (t.fundamentalModule ht) i (t.fundamentalModuleGenerator ht i),
    lof_mem_scLattice_iff.mpr (t.fundamentalModuleGenerator_mem_fundamentalLattice ht i)⟩

private def lowered (i : Fin t.rank) : M := rootOp (.inr i) (highest t ht i)

private theorem primitive_highest (i : Fin t.rank) : IsPrimitive (highest t ht i) := by
  -- Direct-sum operations are pointwise, and subtype operations are inherited,
  -- so the two linearity equations below hold definitionally.
  let p : M →ₗ[ℤ] t.fundamentalLattice ht i :=
    { toFun x := ⟨(x : t.scModule ht) i, mem_scLattice_iff.mp x.2 i⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hp : p (highest t ht i) = ⟨t.fundamentalModuleGenerator ht i,
      t.fundamentalModuleGenerator_mem_fundamentalLattice ht i⟩ := by
    apply Subtype.ext
    exact lof_apply ℚ i (t.fundamentalModuleGenerator ht i)
  exact IsPrimitive.of_map (g := p) (hp.symm ▸ t.isPrimitive_fundamentalModuleGenerator ht i)

private theorem e_highest (i : Fin t.rank) : rootOp (.inl i) (highest t ht i) = 0 := by
  apply Subtype.ext
  simp only [coe_kostantRootOperator_apply, LieAlgebra.Basis.rootGenerator_inl,
    representation_ι_apply, highest, ← lof_lie,
    lie_lieBasis_e_fundamentalModuleGenerator, map_zero, ZeroMemClass.coe_zero]

private theorem f_lowered (i : Fin t.rank) : rootOp (.inr i) (lowered t ht i) = 0 := by
  apply Subtype.ext
  simp only [lowered, coe_kostantRootOperator_apply, LieAlgebra.Basis.rootGenerator_inr,
    representation_ι_apply, highest, ← lof_lie,
    lie_lieBasis_f_lie_lieBasis_f_fundamentalModuleGenerator, map_zero, ZeroMemClass.coe_zero]

private theorem e_lowered (i : Fin t.rank) : rootOp (.inl i) (lowered t ht i) = highest t ht i := by
  apply Subtype.ext
  simp only [lowered, coe_kostantRootOperator_apply, LieAlgebra.Basis.rootGenerator_inl,
    LieAlgebra.Basis.rootGenerator_inr, representation_ι_apply, highest, ← lof_lie,
    lie_lieBasis_e_lie_lieBasis_f_fundamentalModuleGenerator]

private theorem primitive_lowered (i : Fin t.rank) : IsPrimitive (lowered t ht i) := by
  apply IsPrimitive.of_map (g := rootOp (.inl i))
  rw [e_lowered]
  exact primitive_highest t ht i

/-- Every signed simple-root operator on the full-weight lattice admits a vector whose image
is primitive and whose second image vanishes. This detects the integral root parameter without
requiring either vector to belong to the chosen weight basis. -/
theorem exists_isPrimitive_scLattice_rootOperator (i : Fin t.rank ⊕ Fin t.rank) :
    ∃ v : M, rootOp i (rootOp i v) = 0 ∧ IsPrimitive (rootOp i v) := by
  cases i with
  | inl j =>
    refine ⟨lowered t ht j, ?_, ?_⟩
    · exact (congrArg (rootOp (.inl j)) (e_lowered t ht j)).trans (e_highest t ht j)
    · exact (congrArg IsPrimitive (e_lowered t ht j)).mpr (primitive_highest t ht j)
  | inr j =>
    exact ⟨highest t ht j, f_lowered t ht j, primitive_lowered t ht j⟩

/-- Every numbered positive or negative simple-root subgroup on the full-weight lattice
has injective parameter map over every commutative ring. -/
theorem kostantRootSubgroupParam_scLattice_injective (A : Type*) [CommRing A]
    (i : Fin t.rank ⊕ Fin t.rank) :
    Function.Injective (kostantRootSubgroupParam e h ρ M
      (t.kostantForm_apply_mem_scLattice ht) i
      (t.isNilpotent_representation_scModule_rootGenerator ht i) (CommAlgCat.of ℤ A)) := by
  -- Term elimination avoids reverting the large represented-module signature during cases.
  exact (t.exists_isPrimitive_scLattice_rootOperator ht i).elim fun v hv =>
    kostantRootSubgroupParam_injective_of_isPrimitive
      (L := t.lieAlgebra ht) (V := t.scModule ht)
      (I := Fin t.rank ⊕ Fin t.rank) (κ := Fin t.rank) e h ρ M
      (t.kostantForm_apply_mem_scLattice ht) i
      (t.isNilpotent_representation_scModule_rootGenerator ht i) v (rootOp i v)
      (coe_kostantRootOperator_apply e h ρ M
        (t.kostantForm_apply_mem_scLattice ht) i v).symm
      ((coe_kostantRootOperator_apply e h ρ M
        (t.kostantForm_apply_mem_scLattice ht) i (rootOp i v)).symm.trans
          (congrArg Subtype.val hv.1)) hv.2 A

end

end TauCeti.DynkinType
