/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.Pullback
public import Mathlib.AlgebraicGeometry.Noetherian
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.IdealSheaf.Extension

/-!
# Extending blowups from open subschemes

Let `j : X ⟶ Y` be any open immersion into a locally Noetherian scheme. The schematic
closure in `Y` of a centre on `X` defines a blowup whose base change to `X` is the original
blowup, including its full scheme structure. If the original centre avoids the inverse image
of an open `U ⊆ Y`, the extended blowup is an isomorphism over `U`.

On a locally Noetherian scheme the extended centre is of finite type, so the extended
blowup is proper. Thus an admissible blowup on an open subscheme extends to a proper
admissible blowup of the ambient scheme. This is the extension step used to enlarge
and glue partial compactifications.

## References

* The Stacks Project, Section 38.33, *Nagata compactification* (tag 0F41).
* The Stacks Project, Section 31.33, *Blowing up* (tag 01OF).

The construction uses schematic closure of the centre, as formalized by
`Scheme.IdealSheafData.comap_map_of_isOpenImmersion`, and the flat base-change property
`Scheme.IdealSheafData.isPullback_blowupMap_of_flat`.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (j : X ⟶ Y) [IsOpenImmersion j]

/-- A blowup on any open subscheme of a locally Noetherian scheme extends to a proper
blowup of the ambient scheme. If its centre avoids the inverse image of `U`, the extended
centre avoids `U` and the extension is an isomorphism over `U`. The cartesian square identifies
its restriction with the given
blowup, and the equality of ideals identifies its restricted centre scheme-theoretically. -/
theorem exists_blowup_extension [IsLocallyNoetherian Y] (U : Y.Opens)
    (hU : Disjoint (j ⁻¹' (U : Set Y)) (I.support : Set X)) :
    ∃ (J : Y.IdealSheafData) (b : I.blowup ⟶ J.blowup),
      J.comap j = I ∧ Disjoint (U : Set Y) (J.support : Set Y) ∧ IsProper J.blowupToBase ∧
        IsPullback I.blowupToBase b j J.blowupToBase ∧ IsIso (J.blowupToBase ∣_ U) := by
  let J := I.map j
  have hJI : J.comap j = I := I.comap_map_of_isOpenImmersion j
  have hJ := (I.disjoint_support_map_iff j U).mpr hU
  obtain ⟨b, hb⟩ : ∃ b : I.blowup ⟶ J.blowup,
      IsPullback I.blowupToBase b j J.blowupToBase := by
    rw [← hJI]
    exact ⟨J.blowupMap j, J.isPullback_blowupMap_of_flat j⟩
  exact ⟨J, b, hJI, hJ, inferInstance, hb,
    J.isIso_blowupToBase_restrict_of_disjoint_support hJ⟩

end AlgebraicGeometry.Scheme.IdealSheafData
