/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.GaloisGroups.Orbits
public import TauCeti.GroupTheory.Perm.Partition

/-!
# Intrinsic cycle types of a polynomial Galois group

`Polynomial.Gal.cycleTypes p` is the set of full cycle types exhibited by the Galois action on
the distinct roots of `p`. Fixed roots contribute parts equal to one. The set can be computed
in any splitting extension and with any numbering of the roots, so comparisons with factor
degrees or reference permutation groups do not require a preferred splitting field.

Every member has sum equal to the number of distinct roots and least common multiple dividing
the order of `p.Gal`. For separable polynomials the sum is `p.natDegree`. No separability or
irreducibility is required to define the invariant: for an inseparable polynomial it describes
the action on its distinct roots.

The construction uses `Polynomial.Gal.galActionHom`, its equivariant comparison
`Polynomial.Gal.galActionHom_eq_permCongr`, and `Equiv.Perm.fullCycleType_permCongr`.
-/

public section

namespace TauCeti

open Polynomial

universe u v w

variable {F : Type u} [Field F]

open scoped Classical in
/-- The full cycle types of the Galois action on the distinct roots of `p`, including one part
for every fixed root. This is an intrinsic invariant of the polynomial. -/
noncomputable def _root_.Polynomial.Gal.cycleTypes (p : F[X]) : Set (Multiset ℕ) :=
  letI : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  Set.range fun g : p.Gal ↦ (Gal.galActionHom p p.SplittingField g).fullCycleType

variable (p : F[X]) (E : Type v) [Field E] [Algebra F E]
  [Fact ((p.map (algebraMap F E)).Splits)]

open scoped Classical in
/-- The intrinsic set of cycle types is the range of the full cycle type of the root action
in any splitting extension. -/
theorem _root_.Polynomial.Gal.cycleTypes_eq :
    Gal.cycleTypes p = Set.range fun g : p.Gal ↦ (Gal.galActionHom p E g).fullCycleType := by
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  have h : (fun g : p.Gal ↦ (Gal.galActionHom p p.SplittingField g).fullCycleType) =
      (fun g : p.Gal ↦ (Gal.galActionHom p E g).fullCycleType) := by
    funext g
    rw [Gal.galActionHom_eq_permCongr p p.SplittingField E,
      Equiv.Perm.fullCycleType_permCongr]
  exact congrArg Set.range h

open scoped Classical in
/-- A multiset is a Galois cycle type exactly when some Galois automorphism realizes it in
the chosen splitting extension. -/
theorem _root_.Polynomial.Gal.mem_cycleTypes_iff {t : Multiset ℕ} :
    t ∈ Gal.cycleTypes p ↔ ∃ g : p.Gal, (Gal.galActionHom p E g).fullCycleType = t := by
  rw [Gal.cycleTypes_eq p E, Set.mem_range]

open scoped Classical in
/-- The same membership characterization, expressed directly in the permutation image. -/
theorem _root_.Polynomial.Gal.mem_cycleTypes_iff_exists_mem_range {t : Multiset ℕ} :
    t ∈ Gal.cycleTypes p ↔ ∃ σ ∈ (Gal.galActionHom p E).range, σ.fullCycleType = t := by
  rw [Gal.mem_cycleTypes_iff p E]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨_, ⟨g, rfl⟩, hg⟩,
    fun ⟨_, ⟨g, rfl⟩, hg⟩ ↦ ⟨g, hg⟩⟩

open scoped Classical in
/-- Numbering the roots by any finite type leaves the set of Galois cycle types unchanged. -/
theorem _root_.Polynomial.Gal.cycleTypes_eq_range_permCongr {α : Type w} [Fintype α]
    (e : p.rootSet E ≃ α) :
    Gal.cycleTypes p = Set.range fun g : p.Gal ↦
      (e.permCongr (Gal.galActionHom p E g)).fullCycleType := by
  simp only [Equiv.Perm.fullCycleType_permCongr, ← Gal.cycleTypes_eq p E]

open scoped Classical in
/-- Every root permutation induced by a Galois automorphism exhibits a Galois cycle type. -/
@[simp]
theorem _root_.Polynomial.Gal.fullCycleType_mem_cycleTypes (g : p.Gal) :
    (Gal.galActionHom p E g).fullCycleType ∈ Gal.cycleTypes p :=
  (Gal.mem_cycleTypes_iff p E).mpr ⟨g, rfl⟩

open scoped Classical in
/-- The identity exhibits the type consisting of one part for each distinct root. -/
theorem _root_.Polynomial.Gal.replicate_mem_cycleTypes :
    Multiset.replicate (Fintype.card (p.rootSet E)) 1 ∈ Gal.cycleTypes p := by
  simpa using Gal.fullCycleType_mem_cycleTypes p E 1

omit E [Field E] [Algebra F E] [Fact ((p.map (algebraMap F E)).Splits)] in
/-- A polynomial Galois group exhibits only finitely many cycle types. -/
theorem _root_.Polynomial.Gal.finite_cycleTypes : (Gal.cycleTypes p).Finite := by
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  rw [Gal.cycleTypes_eq p p.SplittingField]
  exact Set.finite_range _

open scoped Classical in
/-- The sum of any Galois cycle type is the number of distinct roots in a splitting extension. -/
theorem _root_.Polynomial.Gal.sum_eq_card_rootSet_of_mem_cycleTypes {t : Multiset ℕ}
    (ht : t ∈ Gal.cycleTypes p) : t.sum = Fintype.card (p.rootSet E) := by
  obtain ⟨g, rfl⟩ := (Gal.mem_cycleTypes_iff p E).mp ht
  exact Equiv.Perm.sum_fullCycleType _

omit E [Field E] [Algebra F E] [Fact ((p.map (algebraMap F E)).Splits)] in
/-- For a separable polynomial, every Galois cycle type is a partition of its degree. -/
theorem _root_.Polynomial.Gal.sum_eq_natDegree_of_mem_cycleTypes (hsep : p.Separable)
    {t : Multiset ℕ} (ht : t ∈ Gal.cycleTypes p) : t.sum = p.natDegree := by
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  rw [Gal.sum_eq_card_rootSet_of_mem_cycleTypes p p.SplittingField ht,
    card_rootSet_eq_natDegree hsep (IsSplittingField.splits p.SplittingField p)]

open scoped Classical in
/-- The least common multiple of an exhibited cycle type divides the Galois-group order. -/
theorem _root_.Polynomial.Gal.lcm_dvd_natCard_of_mem_cycleTypes {t : Multiset ℕ}
    (ht : t ∈ Gal.cycleTypes p) : t.lcm ∣ Nat.card p.Gal := by
  let : Fact ((p.map (algebraMap F p.SplittingField)).Splits) :=
    ⟨IsSplittingField.splits p.SplittingField p⟩
  obtain ⟨g, rfl⟩ := (Gal.mem_cycleTypes_iff p p.SplittingField).mp ht
  rw [Equiv.Perm.fullCycleType_def, Equiv.Perm.lcm_parts_partition,
    orderOf_injective _ (Gal.galActionHom_injective p p.SplittingField)]
  exact orderOf_dvd_natCard g

end TauCeti
