/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.OfTriple
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Basic

/-!
# Stable label data for permutation-triple passports

The stable mathematical part of a passport label consists of its degree, a transitive-group
label, and the three ordered full cycle partitions at `0`, `1`, and `∞`. The degree is the
index of `TauCeti.PassportLabel`; the group index is zero-based internally, so an index `j` is
displayed externally as `nT(j + 1)`.

`TauCeti.PassportSpec.HasLabel` interprets this data on a passport specification. It uses
`TauCeti.TransitiveGroupLabel`, so it compares the reference monodromy subgroup only up to
conjugacy in the ambient symmetric group. Consequently the interpretation is unchanged when the
reference subgroup of a passport is replaced by a conjugate.

This deliberately does not include a trailing orbit letter: such a letter enumerates Galois
orbits inside a passport and is not an intrinsic invariant of the passport.

## Main definitions

* `TauCeti.PassportLabel`: the stable degree, group, and ordered partition data of a label.
* `TauCeti.PassportLabel.groupNumber`: the one-based group number displayed after `T`.
* `TauCeti.PassportLabel.toPassportSpec`: the canonical passport using the reference subgroup.
* `TauCeti.PassportSpec.HasLabel`: interpretation of label data on a passport specification.

## Main results

* `TauCeti.PassportSpec.hasLabel_iff_exists_conjugate_eq_toPassportSpec`: a passport has a
  label exactly when a conjugate of it is the canonical reference passport for that label.
* `TauCeti.PassportSpec.hasLabel_conjugate_iff`: label semantics is independent of the chosen
  representative of the reference monodromy subgroup.
* `TauCeti.PassportSpec.hasLabel_iff_of_hasPassport`: a passport containing a connected triple
  has the label read directly from that triple's monodromy and cycle data.

## References

* LMFDB, *Belyi map search labels*.
* G. Butler and J. McKay, *The transitive groups of degree up to eleven*.
-/

open Equiv

public section

namespace TauCeti

/-- The stable mathematical data in a passport label of degree `n`.

The transitive-group index is zero-based. Thus `group = j` represents the externally displayed
group label `nT(j + 1)`. The three partitions remain ordered by the branch points `0`, `1`, and
`∞`. -/
@[ext]
structure PassportLabel (n : ℕ) where
  /-- The zero-based index of the reference transitive group. -/
  group : TransitiveGroupIndex n
  /-- The full cycle partition at `0`. -/
  lam0 : Multiset ℕ
  /-- The full cycle partition at `1`. -/
  lam1 : Multiset ℕ
  /-- The full cycle partition at `∞`. -/
  laminf : Multiset ℕ
  deriving DecidableEq

namespace PassportLabel

variable {n : ℕ}

/-- The one-based transitive-group number displayed after `T` in an `nTj` label. -/
def groupNumber (L : PassportLabel n) : ℕ :=
  L.group + 1

/-- The displayed group number is one more than the internal zero-based index. -/
theorem groupNumber_def (L : PassportLabel n) : L.groupNumber = L.group + 1 :=
  (rfl)

/-- The displayed transitive-group number is positive. -/
theorem groupNumber_pos (L : PassportLabel n) : 0 < L.groupNumber := by
  simp [groupNumber]

/-- The displayed transitive-group number does not exceed the number of supported reference
groups in its degree. -/
theorem groupNumber_le (L : PassportLabel n) : L.groupNumber ≤ numTransitiveGroups n := by
  exact L.group.isLt

/-- The canonical passport specification represented by a label, using the supplier's reference
subgroup for its group component. -/
def toPassportSpec (L : PassportLabel n) : PassportSpec n where
  G := referenceSubgroup n L.group
  lam0 := L.lam0
  lam1 := L.lam1
  laminf := L.laminf

@[simp]
theorem toPassportSpec_G (L : PassportLabel n) : L.toPassportSpec.G = referenceSubgroup n L.group :=
  (rfl)

@[simp]
theorem toPassportSpec_lam0 (L : PassportLabel n) : L.toPassportSpec.lam0 = L.lam0 :=
  (rfl)

@[simp]
theorem toPassportSpec_lam1 (L : PassportLabel n) : L.toPassportSpec.lam1 = L.lam1 :=
  (rfl)

@[simp]
theorem toPassportSpec_laminf (L : PassportLabel n) : L.toPassportSpec.laminf = L.laminf :=
  (rfl)

end PassportLabel

namespace PassportSpec

variable {n : ℕ}

/-- A passport specification has label `L` when its reference subgroup has `L`'s transitive-group
label and its three ordered full cycle partitions are those recorded by `L`.

This predicate interprets the stable mathematical fields of a passport label. It does not assert
that the passport is admissible and does not interpret any external orbit letter. -/
def HasLabel (P : PassportSpec n) (L : PassportLabel n) : Prop :=
  TransitiveGroupLabel L.group P.G ∧
    P.lam0 = L.lam0 ∧ P.lam1 = L.lam1 ∧ P.laminf = L.laminf

/-- The defining characterization of passport label semantics. -/
theorem hasLabel_iff (P : PassportSpec n) (L : PassportLabel n) :
    P.HasLabel L ↔
      TransitiveGroupLabel L.group P.G ∧
        P.lam0 = L.lam0 ∧ P.lam1 = L.lam1 ∧ P.laminf = L.laminf :=
  Iff.rfl

end PassportSpec

namespace PassportLabel

variable {n : ℕ}

/-- The canonical reference passport of a label has that label. -/
@[simp]
theorem hasLabel_toPassportSpec (L : PassportLabel n) : L.toPassportSpec.HasLabel L :=
  ⟨transitiveGroupLabel_referenceSubgroup n L.group, rfl, rfl, rfl⟩

end PassportLabel

namespace PassportSpec

variable {n : ℕ}

/-- A passport has a label exactly when conjugating its reference subgroup can turn it into the
canonical reference passport carrying that label data. -/
theorem hasLabel_iff_exists_conjugate_eq_toPassportSpec (P : PassportSpec n)
    (L : PassportLabel n) :
    P.HasLabel L ↔ ∃ τ : Perm (Fin n), P.conjugate τ = L.toPassportSpec := by
  rw [hasLabel_iff, transitiveGroupLabel_iff]
  constructor
  · rintro ⟨⟨τ, hG⟩, h0, h1, hinf⟩
    refine ⟨τ, PassportSpec.ext ?_ ?_ ?_ ?_⟩
    · simpa using hG
    · simpa using h0
    · simpa using h1
    · simpa using hinf
  · rintro ⟨τ, hτ⟩
    have hG := congrArg PassportSpec.G hτ
    have h0 := congrArg PassportSpec.lam0 hτ
    have h1 := congrArg PassportSpec.lam1 hτ
    have hinf := congrArg PassportSpec.laminf hτ
    exact ⟨⟨τ, by simpa using hG⟩, by simpa using h0, by simpa using h1,
      by simpa using hinf⟩

/-- Replacing a passport's reference monodromy subgroup by a conjugate does not change its label. -/
@[simp]
theorem hasLabel_conjugate_iff (P : PassportSpec n) (L : PassportLabel n)
    (τ : Perm (Fin n)) : (P.conjugate τ).HasLabel L ↔ P.HasLabel L := by
  simp [HasLabel]

/-- Read a label from any connected triple belonging to the passport: its group component is the
transitive-group label of the monodromy group, and its partition components are the triple's
ordered full cycle data. -/
theorem hasLabel_iff_of_hasPassport {t : ConnectedTriple n} {P : PassportSpec n}
    (htP : HasPassport t P) (L : PassportLabel n) :
    P.HasLabel L ↔
      TransitiveGroupLabel L.group t.1.monodromyGroup ∧
        t.1.cycleData.1 = L.lam0 ∧
        t.1.cycleData.2.1 = L.lam1 ∧ t.1.cycleData.2.2 = L.laminf := by
  rw [hasPassport_iff] at htP
  rcases htP with ⟨⟨τ, hG⟩, h0, h1, hinf⟩
  have hlabel :
      TransitiveGroupLabel L.group
          (t.1.monodromyGroup.map (MulAut.conj τ).toMonoidHom) ↔
        TransitiveGroupLabel L.group t.1.monodromyGroup := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using
      transitiveGroupLabel_map_conj_iff t.1.monodromyGroup τ (j := L.group)
  rw [hasLabel_iff, ← hG, hlabel, ← h0, ← h1, ← hinf]

end PassportSpec

namespace ConnectedTriple

variable {n : ℕ}

/-- The label of an attached passport is read directly from the connected triple's monodromy
group and ordered full cycle data. -/
@[simp]
theorem passportOf_hasLabel_iff (t : ConnectedTriple n) (L : PassportLabel n) :
    t.passportOf.HasLabel L ↔
      TransitiveGroupLabel L.group t.1.monodromyGroup ∧
        t.1.cycleData.1 = L.lam0 ∧
        t.1.cycleData.2.1 = L.lam1 ∧ t.1.cycleData.2.2 = L.laminf :=
  PassportSpec.hasLabel_iff_of_hasPassport t.hasPassport_passportOf L

end ConnectedTriple

end TauCeti
