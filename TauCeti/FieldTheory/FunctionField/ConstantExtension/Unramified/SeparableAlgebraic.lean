/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified

import TauCeti.FieldTheory.FunctionField.ConstantExtension.FiniteDescent
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower

/-!
# Unramifiedness in algebraic extensions of constants

For a separable algebraic extension of constants, each residue element comes from a finite
constant subextension. The finite local criterion
`Place.ramificationIdx_eq_one_and_isSeparable_iff_isUnramifiedAt` and
`Place.isUnramifiedAt_of_constantCompositum_eq_top` give separability there.

* `Place.isSeparable_residueField_of_constantCompositum_eq_top` proves residue separability
  for arbitrary separable algebraic extensions of constants.
* `Place.isUnramified_restrict_of_constantCompositum_eq_top` combines residue separability with
  `Place.ramificationIdx_eq_one_of_constantCompositum_eq_top`. For function fields, every place
  below is covered by `Place.restrict_surjective`.

This extends Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Theorem 3.6.3(a),
to algebraic separable extensions over arbitrary constant fields.
-/

public section

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F'] [Algebra.IsSeparable k k']

/-- In a separable algebraic constant extension, the residue field at each place upstairs is
separable over the residue field at the restricted place. -/
theorem isSeparable_residueField_of_constantCompositum_eq_top (P' : Place k' F')
    (h : constantCompositum F k' F' = ⊤) :
    Algebra.IsSeparable
      (@restrict k k' F F' _ _ _ _ _ _ _ _ _ _ _ P'
        ⟨(isSeparable_of_constantCompositum_eq_top (k := k) h).isIntegral⟩).ResidueField
      P'.ResidueField := by
  let _ : Algebra.IsSeparable F F' := isSeparable_of_constantCompositum_eq_top (k := k) h
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  -- Descend a lift of the residue to a finite constant subextension.
  have ha : (a : F') ∈ constantCompositum F k' F' := h.symm ▸ IntermediateField.mem_top
  obtain ⟨L, hL, haL⟩ :=
    exists_finiteDimensional_constantSubfield_of_mem_constantCompositum (k := k) ha
  let _ : FiniteDimensional k L := hL
  let E := constantCompositum F L F'
  let _ : Algebra L E := constantCompositumAlgebra F L F'
  have := isScalarTower_constantCompositum F L F'
  have := isScalarTower_base_constantCompositum k F L F'
  have hE : constantCompositum F L E = ⊤ := (constantCompositum_eq_top_iff F L F' E).mpr rfl
  let _ : FiniteDimensional F E := finiteDimensional_of_constantCompositum_eq_top (k := k) hE
  let _ : Algebra.IsSeparable F E := isSeparable_of_constantCompositum_eq_top (k := k) hE
  let Q := P'.restrict L E
  have hsep : Algebra.IsSeparable (Q.restrict k F).ResidueField Q.ResidueField :=
    ((ramificationIdx_eq_one_and_isSeparable_iff_isUnramifiedAt k F Q).mpr
      (isUnramifiedAt_of_constantCompositum_eq_top (k := k) hE Q)).2
  let b : Q.integers :=
    ⟨⟨a, haL⟩, (mem_integers_restrict_iff L E P' ⟨a, haL⟩).mpr a.property⟩
  have hb : algebraMap Q.ResidueField P'.ResidueField (IsLocalRing.residue Q.integers b) =
      IsLocalRing.residue P'.integers a := by
    rw [IsLocalRing.ResidueField.algebraMap_residue]
    exact congrArg _ (Subtype.ext (coe_algebraMap_integers L E P' b))
  rw [← hb]
  exact P'.isSeparable_algebraMap_residueField_restrict
    (k₀ := k) (F₀ := F) (k₁ := L) (F₁ := E)
    (hsep.isSeparable _ (IsLocalRing.residue Q.integers b))

/-- The restriction of a place in a separable algebraic constant extension is unramified in that
extension. The given place witnesses the existence of a place above its restriction. -/
theorem isUnramified_restrict_of_constantCompositum_eq_top (P' : Place k' F')
    (h : constantCompositum F k' F' = ⊤) :
    @IsUnramified k k' F F' _ _ _ _ _ _ _ _ _ _ _
      ⟨(isSeparable_of_constantCompositum_eq_top (k := k) h).isIntegral⟩
      (@restrict k k' F F' _ _ _ _ _ _ _ _ _ _ _ P'
        ⟨(isSeparable_of_constantCompositum_eq_top (k := k) h).isIntegral⟩) := by
  let _ : Algebra.IsSeparable F F' := isSeparable_of_constantCompositum_eq_top (k := k) h
  refine (isUnramified_iff (P'.restrict k F)).2 ⟨⟨P', rfl⟩, fun Q _ ↦ ?_⟩
  exact ⟨ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h Q,
    Q.isSeparable_residueField_of_constantCompositum_eq_top h⟩

end TauCeti.Place
