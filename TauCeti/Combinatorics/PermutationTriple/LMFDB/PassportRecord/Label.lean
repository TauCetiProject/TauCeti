/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.LMFDB.Label
public import TauCeti.Combinatorics.PermutationTriple.LMFDB.PassportRecord.Basic

/-!
# Certifying the full label of a passport record

The validity predicate for a passport record intentionally leaves its stored label string
unconstrained. `PassportRecord.HasValidLabel` is the additional finite certificate: the full
string parses, and its group number and ordered partitions agree with the stored fields.
Together with validity of the record, this certifies that the parsed group is conjugate to
the monodromy group and that the parsed partitions are the full cycle partitions. Through
`PassportSpec.hasLabel_iff_exists_conjugate_eq_toPassportSpec` it also identifies the canonical
reference passport up to conjugation.

## References

* LMFDB, *Belyi map labels*, https://www.lmfdb.org/knowledge/show/belyi.label.
-/

public section

namespace TauCeti.PermutationTriple.LMFDB.PassportRecord

variable {n : ℕ} {r : PassportRecord n}

/-- The full stored passport label parses and agrees with the record's group and partition
fields. This is separate from `IsValidAt`, which does not constrain the label string. -/
def HasValidLabel (r : PassportRecord n) : Prop :=
  ∃ L : PassportLabel n, parsePassportLabel n r.plabel = some L ∧
    L.groupNumber = r.group ∧ (L.lam0, L.lam1, L.laminf) = r.lambdas

/-- A full-label certificate supplies a successful parse whose group and partitions agree
with the stored fields. -/
theorem hasValidLabel_iff :
    r.HasValidLabel ↔ ∃ L : PassportLabel n, parsePassportLabel n r.plabel = some L ∧
      L.groupNumber = r.group ∧ (L.lam0, L.lam1, L.laminf) = r.lambdas := (Iff.rfl)

/-- The full-label certificate is decidable by parsing and comparing finite data. -/
instance : Decidable r.HasValidLabel :=
  match h : parsePassportLabel n r.plabel with
  | none => isFalse (by simp [HasValidLabel, h])
  | some L => decidable_of_iff
      (L.groupNumber = r.group ∧ (L.lam0, L.lam1, L.laminf) = r.lambdas)
      (by simp [HasValidLabel, h])

/-- After a successful parse, certifying the label means precisely checking its two stored
data components; in particular the parsed output is not an additional choice. -/
theorem hasValidLabel_iff_of_parse {L : PassportLabel n}
    (hL : parsePassportLabel n r.plabel = some L) :
    r.HasValidLabel ↔
      L.groupNumber = r.group ∧ (L.lam0, L.lam1, L.laminf) = r.lambdas := by
  simp [HasValidLabel, hL]

namespace IsValidAt

variable {t : ConnectedTriple n}

/-- A certified full label of a valid record is a mathematical label of every passport
containing the reference triple, not just a matching string. -/
theorem hasLabel_of_hasValidLabel (h : r.IsValidAt t) (hr : r.HasValidLabel)
    {L : PassportLabel n} (hL : parsePassportLabel n r.plabel = some L)
    {P : PassportSpec n} (htP : PassportSpec.HasPassport t P) : P.HasLabel L := by
  obtain ⟨hgroup, hparts⟩ := (hasValidLabel_iff_of_parse hL).mp hr
  obtain ⟨K, hKgroup, hKparts, hK⟩ := h.exists_hasLabel htP
  have hg : L.group = K.group := by
    apply Fin.val_injective
    have := hgroup.trans hKgroup.symm
    simpa only [PassportLabel.groupNumber_def, Nat.add_right_cancel_iff] using this
  have hparts' := hparts.trans hKparts.symm
  have hLK : L = K := by
    apply PassportLabel.ext hg
    · exact congrArg Prod.fst hparts'
    · exact congrArg (fun d => d.2.1) hparts'
    · exact congrArg (fun d => d.2.2) hparts'
  exact hLK ▸ hK

end IsValidAt

end TauCeti.PermutationTriple.LMFDB.PassportRecord
