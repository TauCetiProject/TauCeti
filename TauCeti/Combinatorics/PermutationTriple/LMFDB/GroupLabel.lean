/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.LMFDB.PassportRecord.Examples
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.String
-- The concrete record checks reduce decimal rendering in the kernel.
import all Init.Data.ToString.Basic
import all Init.Data.Repr

/-!
# Recognizing the group component of a passport record

A passport record stores a degree and a one-based transitive-group number.
`PassportRecord.groupString` reconstructs their literal `nTj` component. For a valid record,
recognizing this string returns an index whose reference subgroup is conjugate to the monodromy
group of the reference triple.
The recognition theorem therefore supplies the group certificate, not just a numerical match.

The nonabelian degree-three and Euclidean degree-four records exercise both the index shift and
the conjugacy certificate. This file does not interpret the partitions or trailing orbit letter
of a full passport or map label.

## References

* LMFDB, *Belyi map labels* and *Transitive group labels*.
-/

public section

namespace TauCeti.PermutationTriple.LMFDB.PassportRecord

variable {n : ℕ}

/-- The literal transitive-group component reconstructed from the stored degree and one-based
group number. This does not assert that the record's full `plabel` contains that component. -/
def groupString (r : PassportRecord n) : String :=
  toString r.deg ++ "T" ++ toString r.group

/-- The group component is formed from the stored fields, even for an invalid record. -/
theorem groupString_def (r : PassportRecord n) :
    r.groupString = toString r.deg ++ "T" ++ toString r.group := (rfl)

namespace IsValidAt

variable {r : PassportRecord n} {t : ConnectedTriple n}

/-- The group component of a valid passport record is recognized, and the resulting index
labels the monodromy group of its reference triple. -/
theorem exists_parse_groupString (h : r.IsValidAt t) :
    ∃ j, parseTransitiveGroupLabel n r.groupString = some j ∧
      TransitiveGroupLabel j t.1.monodromyGroup := by
  obtain ⟨j, hj, hlabel⟩ := h.exists_transitiveGroupLabel
  refine ⟨j, parseTransitiveGroupLabel_eq_some_iff.mpr ?_, hlabel⟩
  simp only [groupString_def, h.deg_eq, ← hj, transitiveGroupLabelString_def]

/-- For a valid record, the recognized index is exactly the zero-based form of the stored
group number. -/
theorem parse_groupString_eq_some_iff (h : r.IsValidAt t) (j : TransitiveGroupIndex n) :
    parseTransitiveGroupLabel n r.groupString = some j ↔ j.val + 1 = r.group := by
  obtain ⟨l, hl, _⟩ := h.exists_transitiveGroupLabel
  have hparse : parseTransitiveGroupLabel n r.groupString = some l := by
    apply parseTransitiveGroupLabel_eq_some_iff.mpr
    simp only [groupString_def, h.deg_eq, ← hl, transitiveGroupLabelString_def]
  rw [hparse, Option.some.injEq, Fin.ext_iff]
  omega

/-- Recognizing the group component of a valid record certifies conjugacy of its monodromy
group with the returned reference subgroup. -/
theorem transitiveGroupLabel_of_parse_groupString (h : r.IsValidAt t)
    {j : TransitiveGroupIndex n} (hj : parseTransitiveGroupLabel n r.groupString = some j) :
    TransitiveGroupLabel j t.1.monodromyGroup := by
  obtain ⟨k, hk, hlabel⟩ := h.exists_parse_groupString
  have hkj : k = j := Option.some.inj (hk.symm.trans hj)
  exact hkj ▸ hlabel

end IsValidAt

/-- The nonabelian degree-three example is displayed as `3T2`, not `3T1`. -/
@[simp] theorem groupString_s3PassportRecord : s3PassportRecord.groupString = "3T2" := by
  decide +kernel

/-- The torus example is displayed as `4T1`, despite its positive genus. -/
@[simp] theorem groupString_torusPassportRecord : torusPassportRecord.groupString = "4T1" := by
  decide +kernel

-- These clients use the parser output as a certificate of the actual monodromy group.
example : TransitiveGroupLabel (⟨1, by simp⟩ : TransitiveGroupIndex 3)
    s3Triple.monodromyGroup :=
  isValidAt_s3PassportRecord.transitiveGroupLabel_of_parse_groupString (by
    rw [parseTransitiveGroupLabel_eq_some_iff, groupString_s3PassportRecord,
      transitiveGroupLabelString_def]
    decide)

example : TransitiveGroupLabel (⟨0, by simp⟩ : TransitiveGroupIndex 4)
    torusTriple.monodromyGroup :=
  isValidAt_torusPassportRecord.transitiveGroupLabel_of_parse_groupString (by
    rw [parseTransitiveGroupLabel_eq_some_iff, groupString_torusPassportRecord,
      transitiveGroupLabelString_def]
    decide)

end TauCeti.PermutationTriple.LMFDB.PassportRecord
