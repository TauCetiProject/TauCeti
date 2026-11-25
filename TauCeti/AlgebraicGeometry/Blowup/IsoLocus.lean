/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.Blowup.BaseChange
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine

/-!
# Where a blowup is an isomorphism

The blowup `Bl_I X ⟶ X` along an ideal sheaf `I` is an isomorphism exactly when `V(I)` is an
effective Cartier divisor (`Scheme.IdealSheafData.isIso_blowupToBase_iff`). This file localizes
that statement: over an affine open `U`, the blowup is an isomorphism over `U` exactly when the
pullback of `I` to `Spec Γ(X, U)` is an effective Cartier divisor
(`Scheme.IdealSheafData.isIso_blowupToBase_restrict_iff`). Hence a point lies off the centre of
the blowup exactly when it has an affine neighbourhood on which `I` is an effective Cartier divisor
(`Scheme.IdealSheafData.mem_isoLocus_blowupToBase_iff`): the centre is the locus where `I` is not
locally invertible.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The blowup is an isomorphism over an affine open exactly where `I` is invertible.** Over an
affine open `U`, the blowup `Bl_I X ⟶ X` is an isomorphism over `U` iff the pullback of `I` to
`Spec Γ(X, U)` is an effective Cartier divisor. -/
theorem isIso_blowupToBase_restrict_iff {U : X.Opens} (hU : IsAffineOpen U) :
    IsIso (I.blowupToBase ∣_ U) ↔ (I.comap hU.fromSpec).IsEffectiveCartier := by
  -- Both `blowupToBase ∣_ U` and the affine chart are pullbacks of the blowup along `U ⟶ X`.
  let e := (isPullback_morphismRestrict I.blowupToBase U).isoIsPullback _ _
    (I.isPullback_blowupChart hU)
  have he : e.hom ≫ (Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨U, hU⟩)) ≫ hU.isoSpec.inv) =
      I.blowupToBase ∣_ U :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  rw [← he, comap_fromSpec_eq_ofIdealTop, ← isIso_toSpecZero_reesAlgebra_iff,
    ← toSpecCoeff_reesAlgebra]
  constructor
  · intro h
    have : IsIso (Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨U, hU⟩)) ≫ hU.isoSpec.inv) :=
      IsIso.of_isIso_comp_left e.hom _
    exact IsIso.of_isIso_comp_right _ hU.isoSpec.inv
  · intro h
    infer_instance

/-- **The iso locus of a blowup.** A point `x` lies off the centre of `Bl_I X ⟶ X` exactly when it
has an affine open neighbourhood `U` such that the pullback of `I` to `Spec Γ(X, U)` is an
effective Cartier divisor. -/
theorem mem_isoLocus_blowupToBase_iff {x : X} :
    x ∈ I.blowupToBase.isoLocus ↔
      ∃ (U : X.Opens) (hU : IsAffineOpen U), x ∈ U ∧ (I.comap hU.fromSpec).IsEffectiveCartier := by
  refine ⟨fun hx ↦ ?_, fun ⟨U, hU, hxU, hI⟩ ↦ ?_⟩
  · obtain ⟨U, hU, hxU, hle⟩ := exists_isAffineOpen_mem_and_subset hx
    exact ⟨U, hU, hxU, (I.isIso_blowupToBase_restrict_iff hU).mp
      ((I.blowupToBase.le_isoLocus_iff).mp hle)⟩
  · exact (I.blowupToBase.le_isoLocus_iff.mpr ((I.isIso_blowupToBase_restrict_iff hU).mpr hI)) hxU

end AlgebraicGeometry.Scheme.IdealSheafData
