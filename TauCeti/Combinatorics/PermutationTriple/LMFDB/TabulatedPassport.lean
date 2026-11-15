/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.LMFDB.PassportRecord.Basic
public import TauCeti.Combinatorics.PermutationTriple.Passport.BranchPoints
import TauCeti.Combinatorics.PermutationTriple.Passport.Examples

/-!
# Tabulated representatives of branch-point orbits of passports

The LMFDB does not store one row per ordered passport. Reordering the three branch points
`0`, `1`, `∞` acts on ordered passports, and of each orbit of this action the database tabulates a
single ordered passport, keeping every isomorphism class of connected triples in that chosen
ordered passport. A `TauCeti.PermutationTriple.LMFDB.TabulatedPassport` records the stored ordered
passport together with its admissibility. The assertion it supports about a given ordered
passport `P` is `TauCeti.PermutationTriple.LMFDB.TabulatedPassport.IsRepresentativeOf`: the stored
ordered passport lies in the branch-point orbit of `P`, and nothing stronger.

The stored classes are the classes of the stored ordered passport, not of its orbit. The other
ordered passports of the orbit have classes of their own: reordering the branch points maps the
classes of one ordered passport of the orbit bijectively onto those of another
(`TauCeti.PassportSpec.classSetEquivReindexBranchPoints`), so a count such as the passport size
transports across the orbit, but distinct ordered passports of one orbit share no class
(`TauCeti.OrderedPassport.disjoint_classSet_of_mem_orbit`).

The database chooses its representative by an ordering of labels that has no stable mathematical
description. The choice is therefore carrier-only data, like the trailing letter of a map label,
and nothing here derives it: no canonical representative of an orbit is defined, and the torus
passport gives two different tabulated passports, each with classes, representing the same orbit
(`TauCeti.PermutationTriple.LMFDB.TabulatedPassport.exists_isRepresentativeOf_ne`).

The tabulated passport of a passport row is the passport of its reference triple
(`TauCeti.PermutationTriple.LMFDB.TabulatedPassport.ofTriple`): the stored triples of a valid row
are classes of exactly that ordered passport of its orbit, and the stored passport size is the size
of every ordered passport of the orbit.

## Main definitions

* `TauCeti.PermutationTriple.LMFDB.TabulatedPassport`: a stored admissible ordered passport.
* `TauCeti.PermutationTriple.LMFDB.TabulatedPassport.IsRepresentativeOf`: the stored ordered
  passport lies in the branch-point orbit of a given ordered passport.

## Main results

* `TauCeti.PermutationTriple.LMFDB.TabulatedPassport.isRepresentativeOf_iff_of_mem_orbit`: the
  assertion depends only on the orbit of the given ordered passport.
* `TauCeti.PermutationTriple.LMFDB.TabulatedPassport.IsRepresentativeOf.passportSize_eq`: the
  stored ordered passport has the size of the given one.
* `TauCeti.PermutationTriple.LMFDB.TabulatedPassport.IsRepresentativeOf.disjoint_classSet`:
  different representatives of one orbit share no class.
* `TauCeti.PermutationTriple.LMFDB.TabulatedPassport.exists_isRepresentativeOf_ne`: an orbit can
  have several representatives with classes.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt.mk_mem_classSet_iff_eq`: a stored
  triple of a valid row is a class of an ordered passport of the orbit only when that ordered
  passport is the stored one.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Proceedings of the
  Thirteenth Algorithmic Number Theory Symposium, Open Book Series 2, 2019, Algorithm 2.3.1.
-/

open Equiv MulAction

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-- A tabulated passport in degree `n`: the ordered passport a database stores as the
representative of its orbit under reordering the branch points, with a proof that it is
admissible.

It is a structure of its own rather than an `TauCeti.OrderedPassport`, so that the branch-point
action on ordered passports does not act on it: the stored representative is fixed data, and a
tabulated passport asserts nothing about the other ordered passports of its orbit. -/
@[ext]
structure TabulatedPassport (n : ℕ) where
  /-- The stored ordered passport. -/
  stored : PassportSpec n
  /-- The stored ordered passport is admissible. -/
  isAdmissible : stored.IsAdmissible

namespace TabulatedPassport

variable {n : ℕ}

/-- The stored ordered passport of a tabulated passport, as an ordered passport. -/
def toOrderedPassport (T : TabulatedPassport n) : OrderedPassport n :=
  ⟨T.stored, T.isAdmissible⟩

@[simp] theorem coe_toOrderedPassport (T : TabulatedPassport n) :
    T.toOrderedPassport.1 = T.stored :=
  (rfl)

/-- A tabulated passport is determined by its stored ordered passport. -/
theorem toOrderedPassport_injective :
    Function.Injective (toOrderedPassport : TabulatedPassport n → OrderedPassport n) :=
  fun _ _ h ↦ TabulatedPassport.ext (congrArg Subtype.val h)

/-- The tabulated passport `T` represents the ordered passport `P`: the stored ordered passport
lies in the orbit of `P` under reordering the branch points.

This is the only assertion a tabulated passport supports about `P`. It does not say which ordered
passport of the orbit is stored. -/
def IsRepresentativeOf (T : TabulatedPassport n) (P : OrderedPassport n) : Prop :=
  T.toOrderedPassport ∈ orbit (Perm (Fin 3))ᵐᵒᵖ P

/-- A tabulated passport represents `P` exactly when its stored ordered passport is obtained from
`P` by reordering the branch points. -/
theorem isRepresentativeOf_iff {T : TabulatedPassport n} {P : OrderedPassport n} :
    T.IsRepresentativeOf P ↔ ∃ ρ : Perm (Fin 3), P.1.reindexBranchPoints ρ = T.stored := by
  rw [IsRepresentativeOf, mem_orbit_iff]
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ.unop, congrArg Subtype.val hρ⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨MulOpposite.op ρ, Subtype.ext hρ⟩

/-- A tabulated passport represents its own stored ordered passport. -/
@[simp] theorem isRepresentativeOf_toOrderedPassport (T : TabulatedPassport n) :
    T.IsRepresentativeOf T.toOrderedPassport :=
  mem_orbit_self _

/-- Whether a tabulated passport represents an ordered passport depends only on the branch-point
orbit of that ordered passport. -/
theorem isRepresentativeOf_iff_of_mem_orbit {T : TabulatedPassport n} {P Q : OrderedPassport n}
    (hQ : Q ∈ orbit (Perm (Fin 3))ᵐᵒᵖ P) : T.IsRepresentativeOf Q ↔ T.IsRepresentativeOf P := by
  rw [IsRepresentativeOf, IsRepresentativeOf, orbit_eq_iff.mpr hQ]

/-- Reordering the branch points of the represented ordered passport does not change whether a
tabulated passport represents it. -/
@[simp] theorem isRepresentativeOf_smul_iff {T : TabulatedPassport n} {P : OrderedPassport n}
    (ρ : (Perm (Fin 3))ᵐᵒᵖ) : T.IsRepresentativeOf (ρ • P) ↔ T.IsRepresentativeOf P :=
  isRepresentativeOf_iff_of_mem_orbit (mem_orbit P ρ)

namespace IsRepresentativeOf

variable {T T' : TabulatedPassport n} {P : OrderedPassport n}

/-- The stored ordered passport of a representative has the size of the represented ordered
passport. -/
theorem passportSize_eq (h : T.IsRepresentativeOf P) : T.stored.passportSize = P.1.passportSize :=
  OrderedPassport.passportSize_eq_of_mem_orbit h

/-- Reordering the branch points along some permutation maps the classes of the represented
ordered passport onto the classes of the stored one. -/
theorem exists_op_smul_mem_classSet_iff (h : T.IsRepresentativeOf P) :
    ∃ ρ : Perm (Fin 3), ∀ c : ConnectedIsoClass n,
      MulOpposite.op ρ • c ∈ T.stored.classSet ↔ c ∈ P.1.classSet := by
  obtain ⟨ρ, hρ⟩ := isRepresentativeOf_iff.mp h
  exact ⟨ρ, fun c ↦ hρ ▸ PassportSpec.op_smul_mem_classSet_reindexBranchPoints_iff ρ c P.1⟩

/-- Two representatives of one orbit sharing an isomorphism class are equal. -/
theorem eq_of_mem_classSet (hT : T.IsRepresentativeOf P) (hT' : T'.IsRepresentativeOf P)
    {c : ConnectedIsoClass n} (hc : c ∈ T.stored.classSet) (hc' : c ∈ T'.stored.classSet) :
    T = T' :=
  toOrderedPassport_injective (OrderedPassport.eq_of_mem_orbit_of_mem_classSet
    (by rwa [IsRepresentativeOf, ← orbit_eq_iff.mpr hT'] at hT) hc hc')

/-- Different representatives of one orbit have disjoint sets of classes. -/
theorem disjoint_classSet (hT : T.IsRepresentativeOf P) (hT' : T'.IsRepresentativeOf P)
    (hne : T ≠ T') : Disjoint T.stored.classSet T'.stored.classSet :=
  Finset.disjoint_left.mpr fun _ hc hc' ↦ hne (hT.eq_of_mem_classSet hT' hc hc')

end IsRepresentativeOf

/-- The tabulated passport of a connected triple: its stored ordered passport is the passport of
the triple. This is the tabulated passport of a passport row with reference triple `t`. -/
noncomputable def ofTriple (t : ConnectedTriple n) : TabulatedPassport n :=
  ⟨t.passportOf, t.isAdmissible_passportOf⟩

@[simp] theorem stored_ofTriple (t : ConnectedTriple n) : (ofTriple t).stored = t.passportOf :=
  (rfl)

@[simp] theorem toOrderedPassport_ofTriple (t : ConnectedTriple n) :
    (ofTriple t).toOrderedPassport = t.orderedPassportOf :=
  Subtype.ext t.coe_orderedPassportOf.symm

/-- The choice of representative is not determined by the orbit: the passport of the torus triple
and its reordering by the exchange of `1` and `∞` are different tabulated passports, each with
classes, representing the same orbit. -/
theorem exists_isRepresentativeOf_ne :
    ∃ (P : OrderedPassport 4) (T T' : TabulatedPassport 4),
      T.IsRepresentativeOf P ∧ T'.IsRepresentativeOf P ∧ T ≠ T' ∧
        T.stored.classSet.Nonempty ∧ T'.stored.classSet.Nonempty := by
  let t : ConnectedTriple 4 := ⟨torusTriple, isConnected_torusTriple⟩
  obtain ⟨Q, hQ, hne⟩ := exists_ne_mem_orbit_orderedPassportOf_torusTriple
  obtain ⟨ρ, rfl⟩ := hQ
  induction ρ using MulOpposite.rec' with | h ρ => ?_
  have hmem : ConnectedIsoClass.mk t ∈ (ofTriple t).stored.classSet :=
    t.mk_mem_classSet_passportOf
  have hsmul : MulOpposite.op ρ • ConnectedIsoClass.mk t ∈
      (MulOpposite.op ρ • t.orderedPassportOf).1.classSet := by
    rw [OrderedPassport.coe_smul, ConnectedTriple.coe_orderedPassportOf,
      PassportSpec.smul_eq_reindexBranchPoints, MulOpposite.unop_op,
      PassportSpec.op_smul_mem_classSet_reindexBranchPoints_iff]
    exact hmem
  let Q := MulOpposite.op ρ • t.orderedPassportOf
  refine ⟨t.orderedPassportOf, ofTriple t, ⟨Q.1, Q.2⟩, ?_, mem_orbit _ _, fun h ↦ hne ?_,
    ⟨_, hmem⟩, ⟨_, hsmul⟩⟩
  · rw [← toOrderedPassport_ofTriple]
    exact isRepresentativeOf_toOrderedPassport _
  · exact (congrArg toOrderedPassport h).symm.trans (toOrderedPassport_ofTriple t)

end TabulatedPassport

namespace PassportRecord.IsValidAt

variable {r : PassportRecord n} {t : ConnectedTriple n}

open TabulatedPassport

/-- The stored triples of a valid passport row are classes of the stored ordered passport. -/
theorem mk_mem_classSet_ofTriple (h : r.IsValidAt t) {s : PermutationTriple n}
    (hs : s ∈ r.triples) (hconn : s.IsConnected) :
    ConnectedIsoClass.mk ⟨s, hconn⟩ ∈ (ofTriple t).stored.classSet := by
  obtain ⟨_, hpass⟩ := h.hasPassport_of_mem_triples s hs
  rw [stored_ofTriple, PassportSpec.mem_classSet, ConnectedIsoClass.hasPassport_mk]
  exact hpass

/-- A stored triple of a valid passport row is a class of an ordered passport of the orbit only when
that ordered passport is the stored one: the stored classes belong to the stored ordered passport,
not to its orbit. -/
theorem mk_mem_classSet_iff_eq (h : r.IsValidAt t) {P : OrderedPassport n}
    (hP : (ofTriple t).IsRepresentativeOf P) {s : PermutationTriple n} (hs : s ∈ r.triples)
    (hconn : s.IsConnected) :
    ConnectedIsoClass.mk ⟨s, hconn⟩ ∈ P.1.classSet ↔ P = t.orderedPassportOf := by
  have hstored := h.mk_mem_classSet_ofTriple hs hconn
  rw [stored_ofTriple, ← ConnectedTriple.coe_orderedPassportOf] at hstored
  constructor
  · intro hmem
    have hP' : P ∈ orbit (Perm (Fin 3))ᵐᵒᵖ t.orderedPassportOf :=
      mem_orbit_symm.mp (toOrderedPassport_ofTriple t ▸ hP)
    exact OrderedPassport.eq_of_mem_orbit_of_mem_classSet hP' hmem hstored
  · rintro rfl
    exact hstored

/-- The stored passport size of a valid passport row is the size of every ordered passport of the
orbit of the stored one. -/
theorem passSize_eq_of_isRepresentativeOf (h : r.IsValidAt t) {P : OrderedPassport n}
    (hP : (ofTriple t).IsRepresentativeOf P) : r.passSize = P.1.passportSize :=
  h.passSize_eq.trans hP.passportSize_eq

end PassportRecord.IsValidAt

end LMFDB
end PermutationTriple
end TauCeti
