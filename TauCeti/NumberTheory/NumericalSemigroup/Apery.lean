/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumericalSemigroup.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Order.Interval.Set.Nat

/-!
# Apéry sets of numerical semigroups

For an additive submonoid `S` of `ℕ` and `n : ℕ`, the Apéry set `S.aperySet n` consists of the
elements `s ∈ S` such that `s - n` (computed in `ℤ`) does not lie in `S`. When `n ∈ S` its
elements are exactly the least elements of `S` in their residue classes modulo `n`, and when
moreover `S` is a numerical semigroup there is exactly one such element in each residue class.

Apéry sets are the basic tool for computing the invariants of a numerical semigroup: every
element of `S` is uniquely a multiple of `n` plus an element of the Apéry set, and Selmer's
formula reads off the Frobenius number as the largest element of the Apéry set minus `n`.

## Main definitions

* `AddSubmonoid.aperySet S n`: the Apéry set of `S` with respect to `n`.

## Main results

* `AddSubmonoid.mem_aperySet_iff_forall_modEq_le`: for `0 < n ∈ S`, the Apéry set consists of
  the least elements of `S` in their residue classes modulo `n`.
* `AddSubmonoid.IsNumericalSemigroup.bijOn_mod_aperySet`: reduction modulo `n ∈ S` is a
  bijection from the Apéry set of a numerical semigroup onto `{0, …, n - 1}`.
* `AddSubmonoid.IsNumericalSemigroup.ncard_aperySet`: the Apéry set has exactly `n` elements.
* `AddSubmonoid.existsUnique_mem_aperySet_mul_add_eq`: for `0 < n ∈ S`, every `s ∈ S` is
  uniquely `k * n + w` with `w` in the Apéry set.
* `AddSubmonoid.closure_insert_aperySet`: `n` and the Apéry set generate `S`.
* `AddSubmonoid.IsNumericalSemigroup.numericalFrobenius_eq_sSup_aperySet_sub`: Selmer's formula
  `F(S) = max Ap(S, n) - n`. It holds for every positive `n`, not only for `n ∈ S`.
* `AddSubmonoid.mem_aperySet_of_add_mem_aperySet_left`: the Apéry set is closed under summands
  taken in `S`.

## References

* A. Assi and P. A. García-Sánchez, *Numerical semigroups and applications* (2014),
  §1, Lemma 4, Proposition 6, Corollary 7 and Proposition 12(i); §2, Lemma 46.
-/

public section

namespace AddSubmonoid

variable {S : AddSubmonoid ℕ} {n s w : ℕ}

/-- The **Apéry set** of `S` with respect to `n`: the elements `s ∈ S` that are not `n` more than
an element of `S`, i.e. those for which `s - n`, computed in `ℤ`, does not belong to `S`. -/
def aperySet (S : AddSubmonoid ℕ) (n : ℕ) : Set ℕ :=
  {s | s ∈ S ∧ ∀ t ∈ S, t + n ≠ s}

/-- Membership in the Apéry set, unfolded. -/
@[simp]
theorem mem_aperySet : s ∈ S.aperySet n ↔ s ∈ S ∧ ∀ t ∈ S, t + n ≠ s := Iff.rfl

/-- Membership in the Apéry set, with the difference `s - n` taken in `ℕ`. -/
theorem mem_aperySet_iff_sub_notMem : s ∈ S.aperySet n ↔ s ∈ S ∧ (n ≤ s → s - n ∉ S) := by
  refine and_congr_right fun _ ↦ ⟨fun h hle hmem ↦ h _ hmem (Nat.sub_add_cancel hle), ?_⟩
  rintro h t ht rfl
  exact h (Nat.le_add_left n t) (by simpa using ht)

/-- Membership in the Apéry set, with the difference `s - n` taken in `ℤ`. -/
theorem mem_aperySet_iff_intCast : s ∈ S.aperySet n ↔ s ∈ S ∧ ∀ t ∈ S, (t : ℤ) ≠ s - n := by
  refine and_congr_right fun _ ↦ forall₂_congr fun t _ ↦ ?_
  constructor <;> intro h <;> omega

/-- The Apéry set of `S` is contained in `S`. -/
theorem aperySet_subset : S.aperySet n ⊆ S := fun _ hs ↦ hs.1

/-- For `n ≠ 0`, the Apéry set contains `0`. -/
theorem zero_mem_aperySet (hn : n ≠ 0) : 0 ∈ S.aperySet n :=
  ⟨S.zero_mem, fun _ _ h ↦ hn (by omega)⟩

/-- Every element of `S` below `n` lies in the Apéry set. -/
theorem mem_aperySet_of_lt (hs : s ∈ S) (h : s < n) : s ∈ S.aperySet n :=
  ⟨hs, fun _ _ _ ↦ by omega⟩

/-- The Apéry set with respect to `0` is empty. -/
@[simp]
theorem aperySet_zero : S.aperySet 0 = ∅ :=
  Set.eq_empty_of_forall_notMem fun s hs ↦ hs.2 s hs.1 (Nat.add_zero s)

/-- The Apéry set of `ℕ` with respect to `n` is `{0, …, n - 1}`. -/
@[simp]
theorem aperySet_top : (⊤ : AddSubmonoid ℕ).aperySet n = Set.Iio n := by
  ext s
  simp only [mem_aperySet, mem_top, true_and, forall_const, Set.mem_Iio]
  refine ⟨fun h ↦ ?_, fun h t ht ↦ by omega⟩
  by_contra! hle
  exact h (s - n) (Nat.sub_add_cancel hle)

/-- A natural number above an element `w ∈ S` and congruent to it modulo `n ∈ S` lies in `S`. -/
theorem mem_of_le_of_modEq {m : ℕ} (hn : n ∈ S) (hw : w ∈ S) (hle : w ≤ m)
    (h : w ≡ m [MOD n]) : m ∈ S := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp h
  rw [← Nat.add_sub_cancel' hle, hk, Nat.mul_comm, ← smul_eq_mul]
  exact S.add_mem hw (S.nsmul_mem hn k)

/-- For `n ∈ S`, an element of the Apéry set is at most every element of `S` congruent to it
modulo `n`. -/
theorem le_of_mem_aperySet_of_modEq (hn : n ∈ S) (hw : w ∈ S.aperySet n) (hs : s ∈ S)
    (h : s ≡ w [MOD n]) : w ≤ s := by
  by_contra! hlt
  have hdvd : n ∣ w - s := (Nat.modEq_iff_dvd' hlt.le).mp h
  have hle : n ≤ w - s := Nat.le_of_dvd (by omega) hdvd
  refine hw.2 (w - n) (mem_of_le_of_modEq hn hs (by omega) ?_) (by omega)
  refine (Nat.modEq_iff_dvd' (by omega)).mpr ?_
  rw [show w - n - s = w - s - n by omega]
  exact Nat.dvd_sub hdvd dvd_rfl

/-- For `0 < n ∈ S`, the Apéry set consists of the least elements of `S` in their residue
classes modulo `n`. -/
theorem mem_aperySet_iff_forall_modEq_le (hn : n ∈ S) (hpos : n ≠ 0) :
    w ∈ S.aperySet n ↔ w ∈ S ∧ ∀ s ∈ S, s ≡ w [MOD n] → w ≤ s := by
  refine ⟨fun hw ↦ ⟨hw.1, fun s hs h ↦ le_of_mem_aperySet_of_modEq hn hw hs h⟩, ?_⟩
  rintro ⟨hw, hmin⟩
  refine ⟨hw, fun t ht hsum ↦ ?_⟩
  have := hmin t ht (hsum ▸ (Nat.add_modulus_modEq_iff.mpr rfl).symm)
  omega

/-- For `n ∈ S`, two elements of the Apéry set congruent modulo `n` are equal. -/
theorem eq_of_mem_aperySet_of_modEq {v : ℕ} (hn : n ∈ S) (hv : v ∈ S.aperySet n)
    (hw : w ∈ S.aperySet n) (h : v ≡ w [MOD n]) : v = w :=
  le_antisymm (le_of_mem_aperySet_of_modEq hn hv hw.1 h.symm)
    (le_of_mem_aperySet_of_modEq hn hw hv.1 h)

/-- For `n ∈ S`, reduction modulo `n` is injective on the Apéry set. -/
theorem injOn_mod_aperySet (hn : n ∈ S) : Set.InjOn (· % n) (S.aperySet n) :=
  fun _ hv _ hw h ↦ eq_of_mem_aperySet_of_modEq hn hv hw h

/-- For `n ∈ S`, the Apéry set is finite. -/
theorem finite_aperySet (hn : n ∈ S) : (S.aperySet n).Finite := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  exact (Set.finite_Iio n).of_injOn (fun w _ ↦ Nat.mod_lt w hpos) (injOn_mod_aperySet hn)

/-- For `n ≠ 0`, below every `s ∈ S` there is an element of the Apéry set congruent to `s`
modulo `n`: the least element of `S` in the residue class of `s`. -/
theorem exists_mem_aperySet_modEq_le (hpos : n ≠ 0) (hs : s ∈ S) :
    ∃ w ∈ S.aperySet n, w ≡ s [MOD n] ∧ w ≤ s := by
  classical
  have hP : ∃ w, w ∈ S ∧ w ≡ s [MOD n] := ⟨s, hs, Nat.ModEq.refl s⟩
  obtain ⟨hmem, hmod⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, ⟨hmem, fun t ht hsum ↦ ?_⟩, hmod,
    Nat.find_min' hP ⟨hs, Nat.ModEq.refl s⟩⟩
  refine Nat.find_min hP (m := t) (by omega) ⟨ht, ?_⟩
  exact (Nat.add_modulus_modEq_iff.mpr rfl).symm.trans (hsum ▸ hmod)

/-- In a numerical semigroup, every residue class modulo `n ≠ 0` contains an element of the
Apéry set. -/
theorem IsNumericalSemigroup.exists_mem_aperySet_modEq (h : S.IsNumericalSemigroup)
    (hpos : n ≠ 0) (i : ℕ) : ∃ w ∈ S.aperySet n, w ≡ i [MOD n] := by
  have hs : n * S.numericalConductor + i ∈ S :=
    mem_of_numericalConductor_le h (by nlinarith [Nat.one_le_iff_ne_zero.mpr hpos])
  obtain ⟨w, hw, hmod, -⟩ := exists_mem_aperySet_modEq_le hpos hs
  exact ⟨w, hw, hmod.trans (Nat.mul_add_mod _ _ _)⟩

/-- **Apéry's lemma.** For a numerical semigroup `S` and `n ∈ S`, reduction modulo `n` is a
bijection from the Apéry set onto `{0, …, n - 1}`. -/
theorem IsNumericalSemigroup.bijOn_mod_aperySet (h : S.IsNumericalSemigroup) (hn : n ∈ S) :
    Set.BijOn (· % n) (S.aperySet n) (Set.Iio n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  refine ⟨fun w _ ↦ Nat.mod_lt w hpos, injOn_mod_aperySet hn, fun i hi ↦ ?_⟩
  obtain ⟨w, hw, hmod⟩ := h.exists_mem_aperySet_modEq hpos.ne' i
  exact ⟨w, hw, Eq.trans hmod (Nat.mod_eq_of_lt hi)⟩

/-- For a numerical semigroup `S` and `n ∈ S`, the Apéry set has exactly `n` elements. -/
theorem IsNumericalSemigroup.ncard_aperySet (h : S.IsNumericalSemigroup) (hn : n ∈ S) :
    (S.aperySet n).ncard = n := by
  rw [(h.bijOn_mod_aperySet hn).ncard_eq, Set.ncard_Iio_nat]

/-- For `0 < n ∈ S`, every element of `S` is uniquely of the form `k * n + w` with `w` in the
Apéry set. -/
theorem existsUnique_mem_aperySet_mul_add_eq (hn : n ∈ S) (hpos : n ≠ 0) (hs : s ∈ S) :
    ∃! p : ℕ × ℕ, p.2 ∈ S.aperySet n ∧ p.1 * n + p.2 = s := by
  obtain ⟨w, hw, hmod, hle⟩ := exists_mem_aperySet_modEq_le hpos hs
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
  refine ⟨(k, w), ⟨hw, ?_⟩, ?_⟩
  · rw [Nat.mul_comm] at hk
    dsimp only
    omega
  rintro ⟨k', w'⟩ ⟨hw', hsum⟩
  dsimp only at hw' hsum
  subst hsum
  have hw'w : w' = w :=
    eq_of_mem_aperySet_of_modEq hn hw' hw ((Nat.mul_add_mod' k' n w').symm.trans hmod.symm)
  subst hw'w
  have hkk : k' * n = k * n := by rw [Nat.mul_comm k]; omega
  rw [Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hpos) hkk]

/-- For `0 < n ∈ S`, the submonoid `S` is generated by `n` together with its Apéry set. Since
`0` lies in every submonoid, the element `0` of the Apéry set may be discarded. -/
theorem closure_insert_aperySet (hn : n ∈ S) (hpos : n ≠ 0) :
    closure (insert n (S.aperySet n)) = S := by
  refine le_antisymm (closure_le.mpr (Set.insert_subset hn aperySet_subset)) fun s hs ↦ ?_
  obtain ⟨⟨k, w⟩, ⟨hw, rfl⟩, -⟩ := existsUnique_mem_aperySet_mul_add_eq hn hpos hs
  rw [← smul_eq_mul]
  exact add_mem (nsmul_mem (subset_closure (Set.mem_insert n _)) k)
    (subset_closure (Set.mem_insert_of_mem n hw))

/-- For a numerical semigroup `S` and `n ≠ 0`, the largest element of the Apéry set is
`C(S) + n - 1`, where `C(S)` is the conductor. -/
theorem IsNumericalSemigroup.isGreatest_aperySet (h : S.IsNumericalSemigroup) (hpos : n ≠ 0) :
    IsGreatest (S.aperySet n) (S.numericalConductor + n - 1) := by
  refine ⟨⟨mem_of_numericalConductor_le h (by omega), fun t ht hsum ↦ ?_⟩, fun s hs ↦ ?_⟩
  · have hc : S.numericalConductor ≤ t := (numericalConductor_le_iff h).mpr fun m hm ↦ by
      rcases hm.eq_or_lt with rfl | hlt
      · exact ht
      · exact mem_of_numericalConductor_le h (by omega)
    omega
  · by_contra! hlt
    exact hs.2 (s - n) (mem_of_numericalConductor_le h (by omega)) (by omega)

/-- **Selmer's formula** for the Frobenius number: for a numerical semigroup `S` and `n ≠ 0`,
`F(S) = max Ap(S, n) - n`. The usual hypothesis `n ∈ S` is not needed. -/
theorem IsNumericalSemigroup.numericalFrobenius_eq_sSup_aperySet_sub
    (h : S.IsNumericalSemigroup) (hpos : n ≠ 0) :
    S.numericalFrobenius = (sSup (S.aperySet n) : ℕ) - n := by
  rw [(h.isGreatest_aperySet hpos).csSup_eq]
  have := S.numericalFrobenius_add_one
  omega

/-- If a sum of two elements of `S` lies in the Apéry set, so does the first summand. -/
theorem mem_aperySet_of_add_mem_aperySet_left {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (h : x + y ∈ S.aperySet n) : x ∈ S.aperySet n :=
  ⟨hx, fun t ht hsum ↦ h.2 (t + y) (S.add_mem ht hy) (by omega)⟩

/-- If a sum of two elements of `S` lies in the Apéry set, so does the second summand. -/
theorem mem_aperySet_of_add_mem_aperySet_right {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S)
    (h : x + y ∈ S.aperySet n) : y ∈ S.aperySet n :=
  mem_aperySet_of_add_mem_aperySet_left hy hx (Nat.add_comm x y ▸ h)

/-- The Apéry set of the semigroup generated by `3` and `5` with respect to `3`. -/
example : (closure ({3, 5} : Set ℕ)).aperySet 3 = {0, 5, 10} := by
  have h : (closure ({3, 5} : Set ℕ)).IsNumericalSemigroup :=
    (isNumericalSemigroup_closure_pair_iff 3 5).mpr (by decide)
  have h3 : 3 ∈ closure ({3, 5} : Set ℕ) := subset_closure (by simp)
  refine (Set.eq_of_subset_of_ncard_le ?_ ?_ (finite_aperySet h3)).symm
  · simp only [Set.insert_subset_iff, Set.singleton_subset_iff, mem_aperySet_iff_sub_notMem,
      mem_closure_pair, smul_eq_mul]
    refine ⟨⟨⟨0, 0, rfl⟩, by omega⟩, ⟨⟨0, 1, rfl⟩, ?_⟩, ⟨⟨0, 2, rfl⟩, ?_⟩⟩ <;>
      rintro - ⟨a, b, hab⟩ <;> omega
  · rw [h.ncard_aperySet h3, Set.ncard_eq_three.mpr ⟨0, 5, 10, by decide, by decide, by decide,
      rfl⟩]

/-- The Apéry set of `ℕ` with respect to `1`. -/
example : (⊤ : AddSubmonoid ℕ).aperySet 1 = {0} := by
  ext
  simp

end AddSubmonoid
