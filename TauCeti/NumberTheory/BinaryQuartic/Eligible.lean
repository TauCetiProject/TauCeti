/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuartic.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-!
# Eligible invariant pairs of integral binary quartic forms

A pair `(I, J)` of integers is *eligible* (`TauCeti.BinaryQuartic.IsEligible`) when it is the
pair of invariants of some integral binary quartic form, irreducible or not. Bhargava and
Shankar's Theorem 1.7 classifies these pairs by congruences modulo `9` and `27`
(`TauCeti.BinaryQuartic.isEligible_iff`): `(I, J)` is eligible exactly when

* `I ≡ 0 (mod 3)` and `J ≡ 0 (mod 27)`, or
* `I ≡ 1 (mod 9)` and `J ≡ ±2 (mod 27)`, or
* `I ≡ 4 (mod 9)` and `J ≡ ±16 (mod 27)`, or
* `I ≡ 7 (mod 9)` and `J ≡ ±7 (mod 27)`.

No condition at a prime other than `3` is needed. Necessity uses only the coefficient formulas:
modulo `9` and `27` the invariants depend only on `c` modulo `9` and on `ae` and `bd` modulo `3`.
Sufficiency is witnessed by forms `x³ y + r x² y² + s x y³ + t y⁴` with `r ∈ {-1, 0, 1}`, which
have a rational root at `[1 : 0]`. Hence eligibility depends only on `(I mod 9, J mod 27)`, and
the eligible pairs are the nine translates of `9ℤ × 27ℤ` listed in
`TauCeti.BinaryQuartic.eligibleResidues` (`isEligible_iff_mem_eligibleResidues`).

## References

* M. Bhargava, A. Shankar, *Binary quartic forms having bounded invariants, and the
  boundedness of the average rank of elliptic curves*, Ann. of Math. 181 (2015), Theorem 1.7,
  Lemma 2.9 and §2.8.
-/

public section

namespace TauCeti

namespace BinaryQuartic

/-- A pair of integers is eligible when it is the pair of invariants `(I(f), J(f))` of an
integral binary quartic form `f`, with no irreducibility or nondegeneracy condition on `f`. -/
def IsEligible (I J : ℤ) : Prop :=
  ∃ f : BinaryQuartic ℤ, invI f = I ∧ invJ f = J

/-- The congruence conditions of Bhargava–Shankar, Theorem 1.7, on a pair `(I, J)` of
integers. -/
def EligibilityCongruence (I J : ℤ) : Prop :=
  (I ≡ 0 [ZMOD 3] ∧ J ≡ 0 [ZMOD 27]) ∨
  (I ≡ 1 [ZMOD 9] ∧ (J ≡ 2 [ZMOD 27] ∨ J ≡ -2 [ZMOD 27])) ∨
  (I ≡ 4 [ZMOD 9] ∧ (J ≡ 16 [ZMOD 27] ∨ J ≡ -16 [ZMOD 27])) ∨
  (I ≡ 7 [ZMOD 9] ∧ (J ≡ 7 [ZMOD 27] ∨ J ≡ -7 [ZMOD 27]))

/-- Unfolding `IsEligible`: an explicit integral form realizing the pair. -/
theorem isEligible_iff_exists {I J : ℤ} :
    IsEligible I J ↔ ∃ f : BinaryQuartic ℤ, invI f = I ∧ invJ f = J := Iff.rfl

/-- Unfolding `EligibilityCongruence` into its four cases. -/
theorem eligibilityCongruence_iff {I J : ℤ} :
    EligibilityCongruence I J ↔
      (I ≡ 0 [ZMOD 3] ∧ J ≡ 0 [ZMOD 27]) ∨
      (I ≡ 1 [ZMOD 9] ∧ (J ≡ 2 [ZMOD 27] ∨ J ≡ -2 [ZMOD 27])) ∨
      (I ≡ 4 [ZMOD 9] ∧ (J ≡ 16 [ZMOD 27] ∨ J ≡ -16 [ZMOD 27])) ∨
      (I ≡ 7 [ZMOD 9] ∧ (J ≡ 7 [ZMOD 27] ∨ J ≡ -7 [ZMOD 27])) := Iff.rfl

/-- The invariant pair of every integral binary quartic form is eligible. -/
theorem isEligible_invI_invJ (f : BinaryQuartic ℤ) : IsEligible (invI f) (invJ f) :=
  ⟨f, rfl, rfl⟩

/-- Eligibility is preserved by the weighted scaling `(I, J) ↦ (r² I, r³ J)`, the effect on the
invariants of scaling a form by `r`. -/
theorem IsEligible.sq_mul_pow_three_mul {I J : ℤ} (h : IsEligible I J) (r : ℤ) :
    IsEligible (r ^ 2 * I) (r ^ 3 * J) := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨r • f, invI_smul r f, invJ_smul r f⟩

/-- The eligibility congruences depend only on `I` modulo `9` and `J` modulo `27`. -/
theorem eligibilityCongruence_congr {I I' J J' : ℤ} (hI : I ≡ I' [ZMOD 9])
    (hJ : J ≡ J' [ZMOD 27]) : EligibilityCongruence I J ↔ EligibilityCongruence I' J' := by
  have hI3 : I ≡ I' [ZMOD 3] := Int.ModEq.of_mul_left 3 hI
  unfold EligibilityCongruence Int.ModEq at *
  rw [hI, hJ, hI3]

/-- The eligibility congruences are decidable, as conditions on residues. -/
instance : DecidableRel EligibilityCongruence := fun _ _ ↦
  decidable_of_iff _ eligibilityCongruence_iff.symm

/-- The finite check behind necessity: modulo `9` and `27`, the invariants of a form are the
displayed polynomials in `c` and in `u = ae`, `v = bd`, and these satisfy the congruences. -/
private theorem eligibilityCongruence_aux (u v c t : ℤ) :
    EligibilityCongruence (c ^ 2 + 12 * u - 3 * v)
      (-2 * c ^ 3 + 9 * c * (8 * u + v) - 27 * t) := by
  obtain ⟨c₀, q, hc₀, hc₀', rfl⟩ : ∃ c₀ q, 0 ≤ c₀ ∧ c₀ < 9 ∧ c = c₀ + 9 * q :=
    ⟨c % 9, c / 9, by omega, by omega, by omega⟩
  obtain ⟨u₀, s, hu₀, hu₀', rfl⟩ : ∃ u₀ s, 0 ≤ u₀ ∧ u₀ < 3 ∧ u = u₀ + 3 * s :=
    ⟨u % 3, u / 3, by omega, by omega, by omega⟩
  obtain ⟨v₀, w, hv₀, hv₀', rfl⟩ : ∃ v₀ w, 0 ≤ v₀ ∧ v₀ < 3 ∧ v = v₀ + 3 * w :=
    ⟨v % 3, v / 3, by omega, by omega, by omega⟩
  rw [eligibilityCongruence_congr (I' := c₀ ^ 2 + 12 * u₀ - 3 * v₀)
    (J' := -2 * c₀ ^ 3 + 9 * c₀ * (8 * u₀ + v₀))]
  · interval_cases c₀ <;> interval_cases u₀ <;> interval_cases v₀ <;>
      decide
  · exact Int.modEq_iff_dvd.2 ⟨-(2 * c₀ * q + 9 * q ^ 2 + 4 * s - w), by ring⟩
  · exact Int.modEq_iff_dvd.2 ⟨-(-2 * c₀ ^ 2 * q - 18 * c₀ * q ^ 2 - 54 * q ^ 3 +
      c₀ * (8 * s + w) + 3 * q * (8 * u₀ + v₀) + 9 * q * (8 * s + w) - t), by ring⟩

/-- The invariant pair of every integral binary quartic form satisfies the eligibility
congruences: the necessity half of
Bhargava–Shankar, Theorem 1.7. -/
theorem eligibilityCongruence_invI_invJ (f : BinaryQuartic ℤ) :
    EligibilityCongruence (invI f) (invJ f) := by
  have h := eligibilityCongruence_aux (f 0 * f 4) (f 1 * f 3) (f 2)
    (f 0 * f 3 ^ 2 + f 1 ^ 2 * f 4)
  rw [invI_def, invJ_def]
  convert h using 1 <;> ring

/-- Every pair satisfying the eligibility congruences is the invariant pair of an integral
binary quartic form: the sufficiency half of Bhargava–Shankar, Theorem 1.7. -/
theorem EligibilityCongruence.isEligible {I J : ℤ} (h : EligibilityCongruence I J) :
    IsEligible I J := by
  have key : ∀ r s t : ℤ, IsEligible (r ^ 2 - 3 * s) (-2 * r ^ 3 + 9 * r * s - 27 * t) :=
    fun r s t ↦ ⟨![0, 1, r, s, t], by simp [invI_def]; ring, by simp [invJ_def]; ring⟩
  unfold EligibilityCongruence Int.ModEq at h
  rcases h with ⟨hI, hJ⟩ | ⟨hI, hJ | hJ⟩ | ⟨hI, hJ | hJ⟩ | ⟨hI, hJ | hJ⟩
  · convert key 0 (-(I / 3)) (-(J / 27)) using 1 <;> omega
  -- In cases (b)–(d), `s = (1 - I) / 3`; the sign `r = ±1` is the one making `t` integral.
  all_goals
    first
    | convert key (-1) ((1 - I) / 3) ((2 - 9 * ((1 - I) / 3) - J) / 27) using 1 <;> omega
    | convert key 1 ((1 - I) / 3) ((-2 + 9 * ((1 - I) / 3) - J) / 27) using 1 <;> omega

/-- **Bhargava–Shankar, Theorem 1.7.** A pair of integers is the pair of invariants of an
integral binary quartic form if and only if it satisfies the eligibility congruences. -/
theorem isEligible_iff (I J : ℤ) : IsEligible I J ↔ EligibilityCongruence I J := by
  refine ⟨?_, EligibilityCongruence.isEligible⟩
  rintro ⟨f, rfl, rfl⟩
  exact eligibilityCongruence_invI_invJ f

/-- The nine residue pairs `(I mod 9, J mod 27)` of eligible invariant pairs. The body is exposed
so that membership, and with it eligibility, can be decided by computation. -/
@[expose] def eligibleResidues : Finset (ZMod 9 × ZMod 27) :=
  {(0, 0), (3, 0), (6, 0), (1, 2), (1, -2), (4, 16), (4, -16), (7, 7), (7, -7)}

/-- There are exactly nine eligible residue pairs modulo `(9, 27)`. -/
theorem card_eligibleResidues : eligibleResidues.card = 9 := by
  rfl

private theorem mem_eligibleResidues_iff_val (x : ZMod 9 × ZMod 27) :
    x ∈ eligibleResidues ↔ EligibilityCongruence x.1.val x.2.val := by
  revert x
  decide +kernel

/-- **Bhargava–Shankar, Lemma 2.9.** A pair of integers is eligible if and only if its residues
modulo `9` and `27` form one of the nine pairs of `eligibleResidues`. Hence the eligible pairs
are the union of nine translates of the lattice `9ℤ × 27ℤ`. -/
theorem isEligible_iff_mem_eligibleResidues (I J : ℤ) :
    IsEligible I J ↔ ((I : ZMod 9), (J : ZMod 27)) ∈ eligibleResidues := by
  rw [isEligible_iff, mem_eligibleResidues_iff_val, ZMod.val_intCast, ZMod.val_intCast]
  exact eligibilityCongruence_congr (Int.mod_modEq I 9).symm (Int.mod_modEq J 27).symm

/-- Eligibility of an integer pair is decided by its residues modulo `9` and `27`. -/
instance : DecidableRel IsEligible := fun I J ↦
  decidable_of_iff _ (isEligible_iff_mem_eligibleResidues I J).symm

end BinaryQuartic

end TauCeti
