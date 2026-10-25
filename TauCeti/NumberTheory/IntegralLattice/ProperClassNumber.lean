/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Proper
public import TauCeti.NumberTheory.IntegralLattice.ClassNumber

/-!
# Proper classes in a genus and the proper class number

The proper classes in the genus of `L` are the proper classes `cls⁺ M` of the lattices `M` of the
genus, in the ambient space `V` of `L`; they form the subset `L.genusProperClasses` of
`ProperIsometryQuotient V`. The proper class number `h⁺(L)` is its cardinality.

Each class of the genus consists of one or two proper classes, according to whether its lattices
have an improper self-isometry, so `h(L) ≤ h⁺(L) ≤ 2 h(L)`, and the two class sets are finite
together. More precisely, writing `a` for the number of classes in the genus whose lattices have
an improper self-isometry, `h⁺(L) + a = 2 h(L)` in positive rank. Proper classes are what the
proper mass `m⁺` sums over, and the classes with and without an improper self-isometry are the
two cases in the comparison of `m⁺` with the mass `m`.

Like the class number, the proper class number depends only on the genus and not on the ambient
space used to count it, it is finite for definite lattices, and it is `1` in rank at most one.

## Main definitions

* `TauCeti.IntegralLattice.genusProperClasses`: the proper classes in the genus of `L`.
* `TauCeti.IntegralLattice.properClassNumber`: the proper class number `h⁺(L)`.

## Main results

* `TauCeti.IntegralLattice.properIsometryClass_mem_genusProperClasses_iff`: the proper class of
  `M` lies in the genus of `L` exactly when `M` has the same genus as `L`.
* `TauCeti.IntegralLattice.SameGenus.properClassNumber_eq`: lattices of the same genus, in
  possibly different ambient spaces, have the same proper class number.
* `TauCeti.IntegralLattice.finite_genusProperClasses_iff`: a genus has finitely many proper
  classes exactly when it has finitely many classes; in particular
  `TauCeti.IntegralLattice.IsPosDef.finite_genusProperClasses` and
  `TauCeti.IntegralLattice.IsNegDef.finite_genusProperClasses`.
* `TauCeti.IntegralLattice.classNumber_le_properClassNumber` and
  `TauCeti.IntegralLattice.properClassNumber_le_two_mul_classNumber`: `h ≤ h⁺ ≤ 2h`.
* `TauCeti.IntegralLattice.properClassNumber_add_card_eq_two_mul_classNumber`: `h⁺ + a = 2h`
  in positive rank, where `a` counts the classes with an improper self-isometry.
* `TauCeti.IntegralLattice.properClassNumber_eq_one_of_finrank_le_one`: in rank at most one the
  genus is a single proper class.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A, for proper classes and the proper
  class number.
* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, §2, for the
  proper and full classes of a genus.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

open ProperIsometryQuotient

section GenusProperClasses

/-- The proper classes in the genus of `L`: the proper classes of the lattices in the ambient
space of `L` which have the same genus as `L`, that is, the proper classes contained in a class
of the genus. -/
def genusProperClasses (L : IntegralLattice V) : Set (ProperIsometryQuotient V) :=
  toIsometryQuotient ⁻¹' L.genusClasses

/-- A proper class lies in the genus of `L` exactly when the class containing it does. -/
theorem mem_genusProperClasses_iff {L : IntegralLattice V} {c : ProperIsometryQuotient V} :
    c ∈ L.genusProperClasses ↔ c.toIsometryQuotient ∈ L.genusClasses :=
  Iff.rfl

/-- The proper class of `M` lies in the genus of `L` exactly when `M` has the same genus as
`L`. -/
@[simp]
theorem properIsometryClass_mem_genusProperClasses_iff {L M : IntegralLattice V} :
    M.properIsometryClass ∈ L.genusProperClasses ↔ L.SameGenus M := by
  rw [mem_genusProperClasses_iff, toIsometryQuotient_properIsometryClass,
    isometryClass_mem_genusClasses_iff]

/-- The genus of `L` contains the proper class of `L`. -/
theorem properIsometryClass_mem_genusProperClasses (L : IntegralLattice V) :
    L.properIsometryClass ∈ L.genusProperClasses :=
  properIsometryClass_mem_genusProperClasses_iff.mpr (SameGenus.refl L)

/-- Every class in the genus of `L` contains a proper class of the genus. -/
@[simp]
theorem image_toIsometryQuotient_genusProperClasses (L : IntegralLattice V) :
    toIsometryQuotient '' L.genusProperClasses = L.genusClasses :=
  Set.image_preimage_eq _ toIsometryQuotient_surjective

/-- Two lattices in `V` have the same proper classes in their genus exactly when they have the
same genus. -/
theorem genusProperClasses_eq_genusProperClasses_iff {L M : IntegralLattice V} :
    L.genusProperClasses = M.genusProperClasses ↔ L.SameGenus M := by
  rw [← genusClasses_eq_genusClasses_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [genusProperClasses, h, genusProperClasses]⟩
  rw [← image_toIsometryQuotient_genusProperClasses, h, image_toIsometryQuotient_genusProperClasses]

/-- Lattices of the same genus have the same proper classes in their genus. -/
theorem SameGenus.genusProperClasses_eq {L M : IntegralLattice V} (h : L.SameGenus M) :
    L.genusProperClasses = M.genusProperClasses :=
  genusProperClasses_eq_genusProperClasses_iff.mpr h

/-- Transport along `f : V ≃ W` carries the proper classes in the genus of `L` onto the proper
classes in the genus of any lattice in `W` with the same genus as `L`. -/
theorem properIsometryQuotientEquiv_mem_genusProperClasses_iff (f : V ≃ₗ[ℚ] W)
    {L : IntegralLattice V} {L' : IntegralLattice W} (h : L.SameGenus L')
    (c : ProperIsometryQuotient V) :
    properIsometryQuotientEquiv f c ∈ L'.genusProperClasses ↔ c ∈ L.genusProperClasses := by
  rw [mem_genusProperClasses_iff, mem_genusProperClasses_iff,
    toIsometryQuotient_properIsometryQuotientEquiv,
    isometryQuotientEquiv_mem_genusClasses_iff f h]

/-- **A genus has finitely many proper classes exactly when it has finitely many classes**, each
class consisting of at most two proper classes. -/
theorem finite_genusProperClasses_iff {L : IntegralLattice V} :
    L.genusProperClasses.Finite ↔ L.genusClasses.Finite := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.preimage' fun c _ ↦ finite_preimage_toIsometryQuotient c⟩
  rw [← image_toIsometryQuotient_genusProperClasses]
  exact h.image _

/-- A positive definite genus contains finitely many proper classes. -/
theorem IsPosDef.finite_genusProperClasses {L : IntegralLattice V} (hL : L.IsPosDef) :
    L.genusProperClasses.Finite :=
  finite_genusProperClasses_iff.mpr hL.finite_genusClasses

/-- A negative definite genus contains finitely many proper classes. -/
theorem IsNegDef.finite_genusProperClasses {L : IntegralLattice V} (hL : L.IsNegDef) :
    L.genusProperClasses.Finite :=
  finite_genusProperClasses_iff.mpr hL.finite_genusClasses

end GenusProperClasses

section ProperClassNumber

/-- The proper class number `h⁺(L)`: the number of proper classes in the genus of `L`. It is `0`
when the genus contains infinitely many proper classes. -/
noncomputable def properClassNumber (L : IntegralLattice V) : ℕ :=
  Nat.card L.genusProperClasses

/-- The proper class number is the cardinality of the set of proper classes in the genus. -/
theorem properClassNumber_def (L : IntegralLattice V) :
    L.properClassNumber = Nat.card L.genusProperClasses :=
  (rfl)

/-- The proper class number is positive exactly when the genus contains finitely many classes. -/
theorem properClassNumber_pos_iff {L : IntegralLattice V} :
    0 < L.properClassNumber ↔ L.genusClasses.Finite := by
  rw [properClassNumber_def, Nat.card_pos_iff, Set.finite_coe_iff, finite_genusProperClasses_iff]
  exact and_iff_right ⟨⟨_, L.properIsometryClass_mem_genusProperClasses⟩⟩

/-- **The proper class number is an invariant of the genus.** Lattices of the same genus have the
same proper class number, even when they live in different ambient spaces. -/
theorem SameGenus.properClassNumber_eq {L : IntegralLattice V} {M : IntegralLattice W}
    (h : L.SameGenus M) : L.properClassNumber = M.properClassNumber := by
  obtain ⟨f⟩ := h.nonempty_linearEquiv
  exact Nat.card_congr <| (properIsometryQuotientEquiv f).subtypeEquiv fun c ↦
    (properIsometryQuotientEquiv_mem_genusProperClasses_iff f h c).symm

/-- Isometric lattices have the same proper class number. -/
theorem Isometry.properClassNumber_eq {L : IntegralLattice V} {M : IntegralLattice W}
    (e : Isometry L M) : L.properClassNumber = M.properClassNumber :=
  e.sameGenus.properClassNumber_eq

/-- A positive definite lattice has positive proper class number. -/
theorem IsPosDef.properClassNumber_pos {L : IntegralLattice V} (hL : L.IsPosDef) :
    0 < L.properClassNumber :=
  properClassNumber_pos_iff.mpr hL.finite_genusClasses

/-- A negative definite lattice has positive proper class number. -/
theorem IsNegDef.properClassNumber_pos {L : IntegralLattice V} (hL : L.IsNegDef) :
    0 < L.properClassNumber :=
  properClassNumber_pos_iff.mpr hL.finite_genusClasses

/-- The proper class number counts, class by class, the proper classes in the genus. -/
theorem properClassNumber_eq_sum {L : IntegralLattice V} (hL : L.genusClasses.Finite) :
    L.properClassNumber =
      ∑ c ∈ hL.toFinset,
        Nat.card (toIsometryQuotient ⁻¹' {c} : Set (ProperIsometryQuotient V)) := by
  classical
  have hP := finite_genusProperClasses_iff.mpr hL
  rw [properClassNumber_def, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hP,
    Finset.card_eq_sum_card_fiberwise (f := toIsometryQuotient) (t := hL.toFinset)
      (fun c hc ↦ by simpa [genusProperClasses] using hc)]
  refine Finset.sum_congr rfl fun c hc ↦ ?_
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ (finite_preimage_toIsometryQuotient c)]
  congr 1
  ext d
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff,
    genusProperClasses]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨by rw [h]; simpa using hc, h⟩⟩

/-- **`h⁺ + a = 2h`.** In positive rank, the proper class number plus the number `a` of classes in
the genus whose lattices have an improper self-isometry is twice the class number: a class with
an improper self-isometry is one proper class, and any other class is two. -/
theorem properClassNumber_add_card_eq_two_mul_classNumber {L : IntegralLattice V}
    (hV : 0 < finrank ℚ V) (hL : L.genusClasses.Finite) :
    L.properClassNumber +
        (hL.toFinset.filter fun c ↦ (specialOrthogonalGroup c.out).index = 2).card =
      2 * L.classNumber := by
  rw [properClassNumber_eq_sum hL, Finset.card_filter, ← Finset.sum_add_distrib, classNumber_def,
    Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hL, mul_comm, ← smul_eq_mul,
    ← Finset.sum_const]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  have h := natCard_preimage_toIsometryQuotient_mul_index c.out hV
  rw [isometryClass_out] at h
  rcases index_specialOrthogonalGroup_eq_one_or_two c.out with hi | hi
  · rw [hi, mul_one] at h
    simp [hi, h]
  · rw [hi, mul_eq_right₀ two_ne_zero] at h
    simp [hi, h]

/-- Each class in the genus contains a proper class in the genus, so `h ≤ h⁺`. -/
theorem classNumber_le_properClassNumber (L : IntegralLattice V) :
    L.classNumber ≤ L.properClassNumber := by
  by_cases hL : L.genusClasses.Finite
  · rw [classNumber_def, properClassNumber_def, ← image_toIsometryQuotient_genusProperClasses]
    exact Nat.card_image_le (finite_genusProperClasses_iff.mpr hL)
  · rw [classNumber_def, Set.Infinite.card_eq_zero hL]
    exact Nat.zero_le _

/-- Each class in the genus contains at most two proper classes, so `h⁺ ≤ 2h`. -/
theorem properClassNumber_le_two_mul_classNumber (L : IntegralLattice V) :
    L.properClassNumber ≤ 2 * L.classNumber := by
  by_cases hL : L.genusClasses.Finite
  · rw [properClassNumber_eq_sum hL, classNumber_def, Nat.card_coe_set_eq,
      Set.ncard_eq_toFinset_card _ hL, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun c _ ↦ natCard_preimage_toIsometryQuotient_le_two c
  · rw [properClassNumber_def, Set.Infinite.card_eq_zero (mt finite_genusProperClasses_iff.mp hL)]
    exact Nat.zero_le _

end ProperClassNumber

section RankLeOne

/-- In rank at most one the genus of `L` is the single proper class of `L`: in rank zero every
isometry is proper, and in rank one negation is an improper self-isometry. -/
theorem genusProperClasses_eq_singleton_of_finrank_le_one {L : IntegralLattice V}
    (hle : finrank ℤ L ≤ 1) : L.genusProperClasses = {L.properIsometryClass} := by
  rw [genusProperClasses, genusClasses_eq_singleton_of_finrank_le_one hle]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
  · exact preimage_toIsometryQuotient_eq_singleton_of_finrank_eq_zero L (L.finrank_carrier ▸ h)
  · refine preimage_toIsometryQuotient_eq_singleton_of_index_eq_two
      ((index_specialOrthogonalGroup_eq_two_iff L).mpr ⟨Isometry.neg L, ?_⟩)
    rw [Isometry.det_neg, h, pow_one]

/-- In rank at most one the proper class number is `1`. -/
theorem properClassNumber_eq_one_of_finrank_le_one {L : IntegralLattice V}
    (hle : finrank ℤ L ≤ 1) : L.properClassNumber = 1 := by
  rw [properClassNumber_def, genusProperClasses_eq_singleton_of_finrank_le_one hle,
    Nat.card_unique]

end RankLeOne

end TauCeti.IntegralLattice
