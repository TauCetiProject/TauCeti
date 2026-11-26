/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Divisors

/-!
# Square-divisor tails and their multiplicities

Let `Δ : A → ℤ` be an integer-valued invariant, such as a discriminant, on a family `A`.
Sieving the elements with `Δ` squarefree up to a modulus cutoff `M` leaves the *tail*
`TauCeti.squareDivisorTail Δ M`: the `a` with `Δ a ≠ 0` for which some squarefree `m > M`
has `m ^ 2 ∣ Δ a`. Intersecting with a height sublevel set gives the tail counted by sieves
over a height box.

Bounding the size of the tail is usually not enough to sum the sieve errors over the moduli.
What is summed is the *multiplicity* `TauCeti.squareDivisorMultiplicity Δ M a`, the number of
squarefree `m > M` with `m ^ 2 ∣ Δ a`. It is the finite count of such `m` among the divisors of
`|Δ a|`, so it is zero when `Δ a = 0`, although every square divides `0`: this agrees with
removing the singular locus `Δ = 0` before sieving. An element lies in the tail exactly when its
multiplicity is positive (`TauCeti.squareDivisorMultiplicity_pos_iff`), so on a finite set the
tail has at most the summed multiplicity many elements
(`TauCeti.ncard_inter_squareDivisorTail_le_sum`). Both decrease as the cutoff `M` grows.

The summed multiplicity is the left side of the summed tail estimates of Bhargava, Shankar and
Wang, *Squarefree values of polynomial discriminants I*, Invent. Math. 228 (2022), Theorem 4.4
and (39).
-/

public section

open Finset

namespace TauCeti

variable {A : Type*} (Δ : A → ℤ)

/-- The elements `a` with `Δ a ≠ 0` such that `m ^ 2 ∣ Δ a` for some squarefree `m > M`. -/
def squareDivisorTail (M : ℕ) : Set A :=
  {a | Δ a ≠ 0 ∧ ∃ m : ℕ, M < m ∧ Squarefree m ∧ (m : ℤ) ^ 2 ∣ Δ a}

/-- The number of squarefree `m > M` with `m ^ 2 ∣ Δ a`, counted among the divisors of `|Δ a|`;
it is zero when `Δ a = 0`. -/
noncomputable def squareDivisorMultiplicity (M : ℕ) (a : A) : ℕ := by
  classical
  exact #{m ∈ (Δ a).natAbs.divisors | M < m ∧ Squarefree m ∧ (m : ℤ) ^ 2 ∣ Δ a}

variable {Δ} {M M' : ℕ} {a : A}

/-- Membership in the tail, unfolded. -/
@[simp]
theorem mem_squareDivisorTail :
    a ∈ squareDivisorTail Δ M ↔
      Δ a ≠ 0 ∧ ∃ m : ℕ, M < m ∧ Squarefree m ∧ (m : ℤ) ^ 2 ∣ Δ a :=
  Iff.rfl

/-- The multiplicity is the number of squarefree divisors `m > M` of `|Δ a|` whose square divides
`Δ a`, for any decision procedure for squarefreeness. -/
theorem squareDivisorMultiplicity_eq_card [DecidablePred fun m : ℕ ↦ Squarefree m] :
    squareDivisorMultiplicity Δ M a =
      #{m ∈ (Δ a).natAbs.divisors | M < m ∧ Squarefree m ∧ (m : ℤ) ^ 2 ∣ Δ a} := by
  rw [squareDivisorMultiplicity]
  congr

/-- The multiplicity only depends on the value of the invariant. -/
theorem squareDivisorMultiplicity_congr {B : Type*} {Δ' : B → ℤ} {b : B} (h : Δ a = Δ' b) :
    squareDivisorMultiplicity Δ M a = squareDivisorMultiplicity Δ' M b := by
  classical
  simp only [squareDivisorMultiplicity_eq_card, h]

/-- The multiplicity vanishes on the singular locus `Δ = 0`. -/
@[simp]
theorem squareDivisorMultiplicity_of_eq_zero (h : Δ a = 0) :
    squareDivisorMultiplicity Δ M a = 0 := by
  classical
  simp [squareDivisorMultiplicity_eq_card, h]

/-- An element has positive multiplicity exactly when it lies in the tail. -/
@[simp, grind =]
theorem squareDivisorMultiplicity_pos_iff :
    0 < squareDivisorMultiplicity Δ M a ↔ a ∈ squareDivisorTail Δ M := by
  classical
  rw [squareDivisorMultiplicity_eq_card, Finset.card_pos, Finset.filter_nonempty_iff,
    mem_squareDivisorTail]
  constructor
  · rintro ⟨m, hm, hM, hsq, hdvd⟩
    exact ⟨fun h ↦ by simp [h] at hm, m, hM, hsq, hdvd⟩
  · rintro ⟨h0, m, hM, hsq, hdvd⟩
    refine ⟨m, Nat.mem_divisors.mpr ⟨?_, Int.natAbs_ne_zero.mpr h0⟩, hM, hsq, hdvd⟩
    exact Int.natCast_dvd.mp ((dvd_pow_self (m : ℤ) two_ne_zero).trans hdvd)

/-- An element outside the tail has multiplicity zero. -/
@[simp]
theorem squareDivisorMultiplicity_eq_zero_iff :
    squareDivisorMultiplicity Δ M a = 0 ↔ a ∉ squareDivisorTail Δ M := by
  rw [← squareDivisorMultiplicity_pos_iff, Nat.pos_iff_ne_zero, not_not]

/-- The tail shrinks as the modulus cutoff grows. -/
theorem squareDivisorTail_antitone : Antitone (squareDivisorTail Δ) := by
  intro M M' hMM' a ha
  rw [mem_squareDivisorTail] at ha ⊢
  obtain ⟨h0, m, hM, hm⟩ := ha
  exact ⟨h0, m, hMM'.trans_lt hM, hm⟩

/-- The multiplicity decreases as the modulus cutoff grows. -/
theorem squareDivisorMultiplicity_antitone (Δ : A → ℤ) (a : A) :
    Antitone fun M ↦ squareDivisorMultiplicity Δ M a := by
  classical
  intro M M' hMM'
  simp only [squareDivisorMultiplicity_eq_card]
  refine Finset.card_le_card fun m hm ↦ ?_
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, hMM'.trans_lt hm.2.1, hm.2.2⟩

/-- If `|Δ a| ≤ N ^ 2`, every modulus counted by the multiplicity lies in `(M, N]`. -/
theorem squareDivisorMultiplicity_le_card_Ioc {N : ℕ} (hN : (Δ a).natAbs ≤ N ^ 2) :
    squareDivisorMultiplicity Δ M a ≤ #{m ∈ Ioc M N | ((m : ℕ) : ℤ) ^ 2 ∣ Δ a} := by
  classical
  rw [squareDivisorMultiplicity_eq_card]
  refine Finset.card_le_card_of_injOn id (fun m hm ↦ ?_) (Set.injOn_id _)
  simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisors] at hm
  obtain ⟨⟨-, h0⟩, hM, -, hdvd⟩ := hm
  have hle : m ^ 2 ≤ N ^ 2 := by
    refine (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) ?_).trans hN
    rwa [← Int.natCast_dvd, Nat.cast_pow]
  simp only [id, Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq]
  exact ⟨⟨hM, (Nat.pow_le_pow_iff_left two_ne_zero).mp hle⟩, hdvd⟩

/-- On a finite set `s`, the tail has at most as many elements as the summed multiplicity. -/
theorem ncard_inter_squareDivisorTail_le_sum (s : Finset A) (Δ : A → ℤ) (M : ℕ) :
    ((s : Set A) ∩ squareDivisorTail Δ M).ncard ≤ ∑ a ∈ s, squareDivisorMultiplicity Δ M a := by
  classical
  calc ((s : Set A) ∩ squareDivisorTail Δ M).ncard
      = #{a ∈ s | a ∈ squareDivisorTail Δ M} := by
        rw [← Set.ncard_coe_finset, Finset.coe_filter, Set.inter_def]
        simp only [Finset.mem_coe]
    _ = ∑ a ∈ s, if a ∈ squareDivisorTail Δ M then 1 else 0 := Finset.card_filter _ _
    _ ≤ ∑ a ∈ s, squareDivisorMultiplicity Δ M a := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        split_ifs with h
        · exact squareDivisorMultiplicity_pos_iff.mpr h
        · exact Nat.zero_le _

end TauCeti
