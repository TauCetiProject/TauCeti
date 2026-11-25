/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import TauCeti.AlgebraicGeometry.Morphisms.IsoLocus

/-!
# Where a blowup is an isomorphism

The blowup `Bl_I X ⟶ X` along an ideal sheaf `I` is an isomorphism exactly when `V(I)` is an
effective Cartier divisor (`Scheme.IdealSheafData.isIso_blowupToBase_iff`). This file localizes
that statement: over an open `U`, the blowup is an isomorphism over `U` exactly when the
restriction of `I` to `U` is an effective Cartier divisor
(`Scheme.IdealSheafData.isIso_blowupToBase_restrict_iff`). Hence a point lies off the centre of
the blowup exactly when it has an open neighbourhood on which `I` is an effective Cartier divisor
(`Scheme.IdealSheafData.mem_isoLocus_blowupToBase_iff`): the centre is the locus where `I` is not
locally invertible.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The blowup is an isomorphism over an open exactly where `I` is invertible.** Over an open
`U`, the blowup `Bl_I X ⟶ X` is an isomorphism over `U` iff the restriction of `I` to `U` is an
effective Cartier divisor. -/
theorem isIso_blowupToBase_restrict_iff (U : X.Opens) :
    IsIso (I.blowupToBase ∣_ U) ↔ (I.comap U.ι).IsEffectiveCartier := by
  -- Both `blowupToBase ∣_ U` and the blowup of `I.comap U.ι` are pullbacks of the blowup
  -- along `U ⟶ X`.
  rw [← IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict I.blowupToBase U)
    (I.isPullback_blowupMap_of_flat U.ι), isIso_comp_left_iff, isIso_blowupToBase_iff]

/-- **The iso locus of a blowup.** A point `x` lies off the centre of `Bl_I X ⟶ X` exactly when it
has an open neighbourhood `U` such that the restriction of `I` to `U` is an effective Cartier
divisor. -/
theorem mem_isoLocus_blowupToBase_iff {x : X} :
    x ∈ I.blowupToBase.isoLocus ↔ ∃ U : X.Opens, x ∈ U ∧ (I.comap U.ι).IsEffectiveCartier :=
  I.blowupToBase.mem_isoLocus_iff.trans <|
    exists_congr fun U ↦ and_congr_right fun _ ↦ I.isIso_blowupToBase_restrict_iff U

end AlgebraicGeometry.Scheme.IdealSheafData
