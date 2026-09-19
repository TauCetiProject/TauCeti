/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
public import TauCeti.Combinatorics.PermutationTriple.GeometryType
public import TauCeti.Combinatorics.PermutationTriple.Passport.Basic

/-!
# Classes in a passport

A passport class is an isomorphism class of connected permutation triples with fixed monodromy
subgroup up to conjugacy and fixed ordered cycle partitions.  This file collects those classes in
a finite set and defines the passport size to be its cardinality.

The ordered cycle partitions determine the Euler characteristic, genus, order triple, and geometry
type.  The comparison theorems below state this without choosing representatives of isomorphism
classes.  In particular, a passport is a coarser invariant than an isomorphism class; no uniqueness
of a class inside a passport is asserted.

## Main declarations

* `TauCeti.PassportSpec.classSet`: the finite set of connected isomorphism classes in a passport.
* `TauCeti.PassportSpec.passportSize`: the number of those classes.
* `TauCeti.PassportSpec.cycleData_eq_of_hasPassport`: two triples in one passport have the same
  ordered cycle data.
* `TauCeti.PassportSpec.genus_eq_of_hasPassport`: a passport determines the genus.
* `TauCeti.PassportSpec.orderTriple_eq_of_hasPassport`: a passport determines the order triple.
* `TauCeti.PassportSpec.geometryType_eq_of_hasPassport`: a passport determines the geometry type.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

open Equiv MulAction

public section

namespace TauCeti

namespace PassportSpec

variable {n : ℕ}

/-! ## The finite passport class set -/

/-- The finite set of isomorphism classes of connected triples having passport `P`.

The elements are quotient classes themselves, rather than arbitrarily chosen representatives. -/
noncomputable def classSet (P : PassportSpec n) : Finset (ConnectedIsoClass n) := by
  classical
  exact Finset.univ.filter fun c ↦ c.HasPassport P

/-- Membership in the class set is precisely passport membership. -/
@[simp]
theorem mem_classSet {P : PassportSpec n} {c : ConnectedIsoClass n} :
    c ∈ P.classSet ↔ c.HasPassport P := by
  classical
  simp [classSet]

/-- The size of a passport is the number of isomorphism classes of connected triples in it. -/
noncomputable def passportSize (P : PassportSpec n) : ℕ := P.classSet.card

/-- The passport size is the cardinality of the passport class set. -/
theorem passportSize_def (P : PassportSpec n) : P.passportSize = P.classSet.card :=
  (rfl)

/-- A passport has positive size exactly when some connected triple has that passport. -/
theorem passportSize_pos_iff (P : PassportSpec n) :
    0 < P.passportSize ↔ ∃ t : ConnectedTriple n, HasPassport t P := by
  classical
  rw [passportSize_def, Finset.card_pos]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨t, rfl⟩ := ConnectedIsoClass.mk_surjective c
    exact ⟨t, (ConnectedIsoClass.hasPassport_mk t P).mp (mem_classSet.mp hc)⟩
  · rintro ⟨t, ht⟩
    exact ⟨ConnectedIsoClass.mk t,
      mem_classSet.mpr ((ConnectedIsoClass.hasPassport_mk t P).mpr ht)⟩

/-- A passport has size zero exactly when no connected triple has that passport. -/
theorem passportSize_eq_zero_iff (P : PassportSpec n) :
    P.passportSize = 0 ↔ ∀ t : ConnectedTriple n, ¬ HasPassport t P := by
  constructor
  · intro h t ht
    have hpos := (passportSize_pos_iff P).2 ⟨t, ht⟩
    omega
  · intro h
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨t, ht⟩ := (passportSize_pos_iff P).1 hpos
    exact h t ht

/-- A nonempty passport class set supplies admissible passport data. -/
theorem isAdmissible_of_classSet_nonempty {P : PassportSpec n} (hP : P.classSet.Nonempty) :
    P.IsAdmissible := by
  obtain ⟨c, hc⟩ := hP
  exact ConnectedIsoClass.isAdmissible_of_hasPassport (mem_classSet.mp hc)

/-- An inadmissible passport has no isomorphism classes. -/
theorem classSet_eq_empty_of_not_isAdmissible {P : PassportSpec n} (hP : ¬ P.IsAdmissible) :
    P.classSet = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  exact hP (ConnectedIsoClass.isAdmissible_of_hasPassport (mem_classSet.mp hc))

/-- An inadmissible passport has size zero. -/
theorem passportSize_eq_zero_of_not_isAdmissible {P : PassportSpec n}
    (hP : ¬ P.IsAdmissible) : P.passportSize = 0 := by
  rw [passportSize_def, classSet_eq_empty_of_not_isAdmissible hP, Finset.card_empty]

/-- Conjugating the reference monodromy subgroup does not change the passport class set. -/
@[simp]
theorem classSet_conjugate (P : PassportSpec n) (tau : Perm (Fin n)) :
    (P.conjugate tau).classSet = P.classSet := by
  classical
  ext c
  simp

/-- Conjugating the reference monodromy subgroup does not change the passport size. -/
@[simp]
theorem passportSize_conjugate (P : PassportSpec n) (tau : Perm (Fin n)) :
    (P.conjugate tau).passportSize = P.passportSize := by
  rw [passportSize_def, passportSize_def, classSet_conjugate]

/-! ## Invariants determined by a passport -/

/-- Two connected triples in the same passport have identical ordered full cycle partitions. -/
theorem cycleData_eq_of_hasPassport {P : PassportSpec n} {t t' : ConnectedTriple n}
    (ht : HasPassport t P) (ht' : HasPassport t' P) : t.1.cycleData = t'.1.cycleData := by
  rcases (hasPassport_iff t P).mp ht with ⟨_, ht0, ht1, htinf⟩
  rcases (hasPassport_iff t' P).mp ht' with ⟨_, ht0', ht1', htinf'⟩
  ext <;> simp_all

/-- Two connected triples in the same passport have equal Euler characteristic. -/
theorem eulerChar_eq_of_hasPassport {P : PassportSpec n} {t t' : ConnectedTriple n}
    (ht : HasPassport t P) (ht' : HasPassport t' P) : t.1.eulerChar = t'.1.eulerChar := by
  simp only [PermutationTriple.eulerChar_eq_cycleCounts,
    PermutationTriple.cycleCounts_eq_card_cycleData, cycleData_eq_of_hasPassport ht ht']

/-- Two connected triples in the same passport have equal genus. -/
theorem genus_eq_of_hasPassport {P : PassportSpec n} {t t' : ConnectedTriple n}
    (ht : HasPassport t P) (ht' : HasPassport t' P) : t.1.genus = t'.1.genus := by
  rw [PermutationTriple.genus_def, PermutationTriple.genus_def,
    eulerChar_eq_of_hasPassport ht ht']

/-- Two connected triples in the same passport have equal ordered triples of permutation orders. -/
theorem orderTriple_eq_of_hasPassport {P : PassportSpec n} {t t' : ConnectedTriple n}
    (ht : HasPassport t P) (ht' : HasPassport t' P) : t.1.orderTriple = t'.1.orderTriple := by
  rw [PermutationTriple.orderTriple_eq_lcm_cycleData,
    PermutationTriple.orderTriple_eq_lcm_cycleData, cycleData_eq_of_hasPassport ht ht']

/-- Two connected triples in the same passport have the same spherical, Euclidean, or hyperbolic
geometry type. -/
theorem geometryType_eq_of_hasPassport {P : PassportSpec n} {t t' : ConnectedTriple n}
    (ht : HasPassport t P) (ht' : HasPassport t' P) : t.1.geometryType = t'.1.geometryType := by
  apply PermutationTriple.geometryType_eq_of_sum_eq
  rw [orderTriple_eq_of_hasPassport ht ht']

end PassportSpec

end TauCeti
