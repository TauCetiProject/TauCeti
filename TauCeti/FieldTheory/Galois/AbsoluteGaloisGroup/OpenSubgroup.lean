/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic

/-!
# Finite separable subextensions and open fixing subgroups

In a normal extension `Ω/K`, a separable intermediate field has an open fixing subgroup
exactly when it is finite over `K`, and its degree is the index of that subgroup. Hence the
finite intermediate fields of a separable `L/K` inside `Ω` correspond, reversing inclusion,
to the open subgroups of `Gal(Ω/K)` containing `L.fixingSubgroup`.

The inverse takes the separable part of the fixed field. This is essential over an imperfect
base: the full fixed field in an algebraic closure can contain purely inseparable elements.
The correspondence therefore applies in particular to Mathlib's algebraic-closure model of
the absolute Galois group, without assuming that `K` is perfect or that `L/K` is finite.

This refines `TauCeti.intermediateFieldEquivClosedSubgroup`, using its fixed-field identities
and restriction to the separable closure, as in the fundamental theorem of infinite Galois theory.
-/

public section

noncomputable section

namespace IntermediateField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [Normal K Ω]

/-- The degree of a separable intermediate field in a normal extension equals the index of
its fixing subgroup. Neither the intermediate field nor the ambient extension need be finite. -/
theorem finrank_eq_fixingSubgroup_index_of_le_separableClosure
    (M : IntermediateField K Ω) (hM : M ≤ separableClosure K Ω) :
    Module.finrank K M = M.fixingSubgroup.index := by
  have hdegree := (restrictAlgEquiv hM).toLinearEquiv.finrank_eq
  have hindex := (restrict hM).map_fixingSubgroup_index (E' := Ω)
  have hmap : (restrict hM).map (IsScalarTower.toAlgHom K (separableClosure K Ω) Ω) = M :=
    lift_restrict hM
  rw [hmap] at hindex
  exact hdegree.trans
    ((finrank_eq_fixingSubgroup_index (separableClosure K Ω) (restrict hM)).trans hindex.symm)

/-- A separable intermediate field of a normal extension has an open fixing subgroup exactly
when it is finite over the base field. -/
theorem isOpen_fixingSubgroup_iff_of_le_separableClosure
    (M : IntermediateField K Ω) (hM : M ≤ separableClosure K Ω) :
    IsOpen (M.fixingSubgroup : Set Gal(Ω/K)) ↔ FiniteDimensional K M := by
  refine ⟨fun hopen ↦ ?_, fun _ ↦ M.fixingSubgroup_isOpen⟩
  have := Subgroup.quotient_finite_of_isOpen M.fixingSubgroup hopen
  have : M.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  apply Module.finite_of_finrank_pos
  rw [finrank_eq_fixingSubgroup_index_of_le_separableClosure M hM]
  exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero (H := M.fixingSubgroup))

/-- The separable part of the fixed field of an open subgroup of a normal extension is finite
over the base field. The full fixed field need not be finite over an imperfect base. -/
theorem finiteDimensional_fixedField_inf_separableClosure_of_isOpen
    {H : Subgroup Gal(Ω/K)} (hH : IsOpen (H : Set Gal(Ω/K))) :
    FiniteDimensional K ↥(fixedField H ⊓ separableClosure K Ω) := by
  apply (isOpen_fixingSubgroup_iff_of_le_separableClosure _ inf_le_right).mp
  rw [fixingSubgroup_inf_separableClosure,
    TauCeti.fixingSubgroup_fixedField (Subgroup.isClosed_of_isOpen H hH)]
  exact hH

variable (L : IntermediateField K Ω) [Algebra.IsSeparable K L]

/-- Finite intermediate fields contained in a separable `L/K` correspond, reversing inclusion,
to the open subgroups of `Gal(Ω/K)` containing `L.fixingSubgroup`. This uses only normality of
`Ω/K`; in particular it applies to an algebraic closure in every characteristic. -/
def finiteSubextensionEquivOpenSubgroup :
    {M : IntermediateField K Ω // M ≤ L ∧ FiniteDimensional K M} ≃o
      {U : OpenSubgroup Gal(Ω/K) // L.fixingSubgroup ≤ U.toSubgroup}ᵒᵈ where
  toFun M := ⟨⟨M.val.fixingSubgroup, by
    have := M.property.2
    exact M.val.fixingSubgroup_isOpen⟩, fixingSubgroup_antitone M.property.1⟩
  invFun U := ⟨fixedField U.val.toSubgroup ⊓ separableClosure K Ω, by
    constructor
    · calc
        fixedField U.val.toSubgroup ⊓ separableClosure K Ω ≤
            fixedField L.fixingSubgroup ⊓ separableClosure K Ω :=
          inf_le_inf_right _ (fixedField_le U.property)
        _ = L := fixedField_fixingSubgroup_inf_separableClosure (le_separableClosure K Ω L)
    · exact finiteDimensional_fixedField_inf_separableClosure_of_isOpen U.val.isOpen⟩
  left_inv M := Subtype.ext <|
    fixedField_fixingSubgroup_inf_separableClosure
      (M.property.1.trans (le_separableClosure K Ω L))
  right_inv U := by
    apply Subtype.ext
    apply OpenSubgroup.toSubgroup_injective
    exact (fixingSubgroup_inf_separableClosure _).trans
      (TauCeti.fixingSubgroup_fixedField U.val.isClosed)
  map_rel_iff' {M N} :=
    fixingSubgroup_le_iff_of_le_separableClosure
      (M.property.1.trans (le_separableClosure K Ω L))

/-- The finite-subextension correspondence sends a field to its pointwise fixing subgroup. -/
@[simp]
theorem finiteSubextensionEquivOpenSubgroup_apply
    (M : {M : IntermediateField K Ω // M ≤ L ∧ FiniteDimensional K M}) :
    (OrderDual.ofDual (L.finiteSubextensionEquivOpenSubgroup M)).val.toSubgroup =
      M.val.fixingSubgroup :=
  (rfl)

/-- The inverse correspondence takes the separable part of the fixed field. -/
@[simp]
theorem finiteSubextensionEquivOpenSubgroup_symm_apply
    (U : {U : OpenSubgroup Gal(Ω/K) // L.fixingSubgroup ≤ U.toSubgroup}) :
    (L.finiteSubextensionEquivOpenSubgroup.symm (OrderDual.toDual U)).val =
      fixedField U.val.toSubgroup ⊓ separableClosure K Ω :=
  (rfl)

end IntermediateField
