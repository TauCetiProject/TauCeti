/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.ProperPower
import TauCeti.Data.List.Commutation
import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced
import TauCeti.GroupTheory.FreeGroup.ProperPower.Basic

/-!
# Periods and stable occurrences of powers in free groups

A *period* of the free group `F(α)` is a cyclically reduced element that is not a proper power
(in particular `A ≠ 1`, since `1 = 1 ^ 2`). A power `A ^ q`, `q ≥ 1`, has a *stable occurrence* in
an element `W` when the reduced word of `W` contains the word of `A` repeated `q + 2` times: the
occurrence of `A ^ q` is flanked by a copy of `A` on each side. Two stable occurrences of powers
of a period whose blocks share at least `|A|` letters overlap correctly: they start at positions
congruent modulo `|A|` ([IFT], Lemma 57, for powers of the same sign), since the reduced word of an
element that is not a proper power is fixed by no nontrivial rotation. In [IFT] this is what makes
the maximal stable occurrences of powers of `A` in `W` pairwise disjoint, so that they cut `W` into
its canonical `A`-decomposition `W = B₁ ∘ A ^ q₁ ∘ B₂ ∘ ⋯ ∘ A ^ q_k ∘ B_{k+1}`; the upper bound,
the size and the rank defined here are read off the stable occurrences.

For a list `𝒜 = (A₁, …, A_L)` of periods, the `N`-large rank of `W` is the largest `j` such that
`A_j ^ q` or `A_j⁻¹ ^ q` has a stable occurrence in `W` for some `q ≥ N`; for `N = 1` this is the
rank of `W`. These notions organise the words obtained from the variables by the products `φ_{L,p}`
of powers of the basic automorphisms of a quadratic equation, and the cut equations labelled by
them, in the proof of the implicit function theorem over free groups.

## Main definitions

* `FreeGroup.IsPeriod`: cyclically reduced and not a proper power.
* `FreeGroup.IsStableOccurrence`: a stable occurrence of a power of `A` in `W` at a position.
* `FreeGroup.IsMaxStableOccurrence`: a stable occurrence not contained in another one.
* `FreeGroup.maxExp`: the largest exponent of a stable occurrence of a power of `A` or of `A⁻¹`
  (the upper `A`-bound).
* `FreeGroup.HasLargeSize`: the canonical `N`-large decomposition has size `(N, r)`.
* `FreeGroup.largeRank`: the `N`-large rank of an element with respect to a list of periods.

## Main results

* `FreeGroup.modEq_of_isStableOccurrence`: two stable occurrences of powers of a period that
  overlap in at least the length of the period, in particular two whose powers share a letter,
  overlap correctly.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.4, p. 40 (periods) and §7.1, pp. 92–94: Lemma 57, Definitions 33–35.
-/

public section

namespace FreeGroup

variable {α : Type*} [DecidableEq α]

/-! ### Periods -/

/-- A period ([IFT], §5.4, p. 40): a cyclically reduced element that is not a proper power. A
period is nontrivial, since `1 = 1 ^ 2` is a proper power. (In §7.1, p. 92, the source also excludes
the elements of the coefficient group; there is no coefficient group here.) -/
def IsPeriod (A : FreeGroup α) : Prop :=
  IsCyclicallyReduced A.toWord ∧ ¬Group.IsProperPower A

/-- An element is a period exactly when it is cyclically reduced and not a proper power. -/
theorem isPeriod_iff {A : FreeGroup α} :
    A.IsPeriod ↔ IsCyclicallyReduced A.toWord ∧ ¬Group.IsProperPower A :=
  Iff.rfl

/-- A period is cyclically reduced. -/
theorem IsPeriod.isCyclicallyReduced {A : FreeGroup α} (hA : A.IsPeriod) :
    IsCyclicallyReduced A.toWord :=
  hA.1

/-- A period is not a proper power. -/
theorem IsPeriod.not_isProperPower {A : FreeGroup α} (hA : A.IsPeriod) : ¬Group.IsProperPower A :=
  hA.2

/-- A period is nontrivial. -/
theorem IsPeriod.ne_one {A : FreeGroup α} (hA : A.IsPeriod) : A ≠ 1 :=
  Group.ne_one_of_not_isProperPower hA.2

/-- Every generator is a period. -/
@[simp]
theorem isPeriod_of (a : α) : (of a).IsPeriod :=
  ⟨by simp [toWord_of], not_isProperPower_of a⟩

/-! ### Stable occurrences -/

/-- The power `A ^ q`, `q ≥ 1`, has a stable occurrence in `W` at position `i` ([IFT], §7.1,
p. 92): the reduced word of `W` contains, starting at position `i`, the word of `A` repeated
`q + 2` times, so that the occurrence of `A ^ q` at position `i + |A|` is flanked by a copy of `A`
on each side. As a junk case, `1 ^ q` has a stable occurrence at every position `i ≤ |W|` for
every `q ≥ 1`. -/
def IsStableOccurrence (W A : FreeGroup α) (i q : ℕ) : Prop :=
  1 ≤ q ∧ ∃ u v : List (α × Bool),
    W.toWord = u ++ (List.replicate (q + 2) A.toWord).flatten ++ v ∧ u.length = i

/-- The power `A ^ q` has a stable occurrence in `W` at position `i` exactly when `q ≥ 1` and the
reduced word of `W` splits as `u ++ A ^ (q + 2) ++ v` with `u` of length `i`. -/
theorem isStableOccurrence_iff {W A : FreeGroup α} {i q : ℕ} :
    W.IsStableOccurrence A i q ↔ 1 ≤ q ∧ ∃ u v : List (α × Bool),
      W.toWord = u ++ (List.replicate (q + 2) A.toWord).flatten ++ v ∧ u.length = i :=
  Iff.rfl

/-- The exponent of a stable occurrence is positive. -/
theorem IsStableOccurrence.one_le {W A : FreeGroup α} {i q : ℕ} (h : W.IsStableOccurrence A i q) :
    1 ≤ q :=
  h.1

/-- A stable occurrence fits in the reduced word: its block `A ^ (q + 2)` ends by the end of `W`. -/
theorem IsStableOccurrence.add_mul_le_length {W A : FreeGroup α} {i q : ℕ}
    (h : W.IsStableOccurrence A i q) : i + (q + 2) * A.toWord.length ≤ W.toWord.length := by
  obtain ⟨-, u, v, hW, rfl⟩ := h
  simp [hW, List.length_flatten]

/-- If a power of `A` has a stable occurrence in `W`, then `A` is cyclically reduced ([IFT],
p. 92): the reduced word of `W` contains two consecutive copies of the word of `A`. -/
theorem IsStableOccurrence.isCyclicallyReduced {W A : FreeGroup α} {i q : ℕ}
    (h : W.IsStableOccurrence A i q) : IsCyclicallyReduced A.toWord := by
  obtain ⟨-, u, v, hW, -⟩ := h
  have hred : IsReduced (A.toWord ++ A.toWord) := (isReduced_toWord (x := W)).infix
    ⟨u, (List.replicate q A.toWord).flatten ++ v, by simp [hW, List.replicate_succ]⟩
  exact ⟨hred.infix (List.prefix_append _ _).isInfix, (List.isChain_append.1 hred).2.2⟩

/-- If a power of `A` has a stable occurrence in `W`, then `A` is a period exactly when it is not
a proper power. -/
theorem IsStableOccurrence.isPeriod_iff {W A : FreeGroup α} {i q : ℕ}
    (h : W.IsStableOccurrence A i q) : A.IsPeriod ↔ ¬Group.IsProperPower A :=
  ⟨IsPeriod.not_isProperPower, fun hA => ⟨h.isCyclicallyReduced, hA⟩⟩

/-- For a cyclically reduced `A`, the power `A ^ q` has a stable occurrence at the start of
`A ^ (q + 2)`. -/
theorem isStableOccurrence_pow {A : FreeGroup α} (hA : IsCyclicallyReduced A.toWord) {q : ℕ}
    (hq : 1 ≤ q) : (A ^ (q + 2)).IsStableOccurrence A 0 q :=
  ⟨hq, [], [], by rw [toWord_pow, (hA.flatten_replicate _).isReduced.reduce_eq]; simp, rfl⟩

/-- **Correct overlapping** ([IFT], Lemma 57). Let `A` be an element that is not a proper power
(a period: stability forces `A` to be cyclically reduced). Two stable occurrences of powers of
`A` in `W` whose blocks `A ^ (q + 2)` and `A ^ (r + 2)` share at least `|A|` letters start at
positions congruent modulo `|A|`. This applies in particular when the powers `A ^ q` and `A ^ r`
themselves share a letter, which is the form of the source. Only powers of the same sign are
compared here: the source's remark that occurrences of `A ^ q` and of `A⁻¹ ^ p` are disjoint is
not part of this statement. -/
theorem modEq_of_isStableOccurrence {W A : FreeGroup α} (hA : ¬Group.IsProperPower A) {i q j r : ℕ}
    (h₁ : W.IsStableOccurrence A i q) (h₂ : W.IsStableOccurrence A j r)
    (hij : i ≤ j + (r + 1) * A.toWord.length) (hji : j ≤ i + (q + 1) * A.toWord.length) :
    i ≡ j [MOD A.toWord.length] := by
  wlog hle : i ≤ j generalizing i q j r
  · exact (this h₂ h₁ hji hij (by lia)).symm
  obtain ⟨-, u, v, hW, rfl⟩ := h₁
  obtain ⟨-, u', v', hW', rfl⟩ := h₂
  -- each block is a prefix of the word of `W` from the position where it starts
  have hblock {s t : List (α × Bool)} {k : ℕ}
      (h : W.toWord = s ++ (List.replicate k A.toWord).flatten ++ t) :
      (List.replicate k A.toWord).flatten <+: W.toWord.drop s.length :=
    ⟨t, by rw [h, List.append_assoc, List.drop_left]⟩
  -- the word of `A` begins the second block, at position `|u'|` of `W`, and it lies in the first
  -- block at offset `|u'| - |u|`, as the first block reaches at least `|A|` letters past `|u'|`
  have hA₂ : A.toWord <+: W.toWord.drop u'.length :=
    List.IsPrefix.trans (by simp [List.replicate_succ]) (hblock hW')
  have hA₁ : A.toWord <+: ((List.replicate (q + 2) A.toWord).flatten).drop
      (u'.length - u.length) := by
    refine List.prefix_of_prefix_length_le hA₂ ?_ ?_
    · have hdrop : W.toWord.drop u'.length =
          (W.toWord.drop u.length).drop (u'.length - u.length) := by
        rw [List.drop_drop, Nat.add_sub_cancel' hle]
      exact hdrop ▸ (hblock hW).drop _
    · simp only [List.length_drop, List.length_flatten, List.map_replicate, List.sum_replicate_nat,
        add_mul, one_mul] at hji ⊢
      lia
  refine (Nat.modEq_iff_dvd' hle).2 (Nat.modEq_zero_iff_dvd.1
    (List.modEq_of_prefix_drop_flatten_replicate
      (not_exists_eq_flatten_replicate_of_not_isProperPower (by rwa [mk_toWord])) le_rfl hA₁
      (m' := r + 2) (by simp [List.replicate_succ])))

/-- A maximal stable occurrence of a power of `A` in `W` ([IFT], §7.1, p. 92): a stable occurrence
whose power `A ^ q` is not contained in the power of another stable occurrence. -/
def IsMaxStableOccurrence (W A : FreeGroup α) (i q : ℕ) : Prop :=
  W.IsStableOccurrence A i q ∧ ∀ j r, W.IsStableOccurrence A j r → j ≤ i →
    i + q * A.toWord.length ≤ j + r * A.toWord.length → j = i ∧ r = q

/-- A stable occurrence `(i, q)` of a power of `A` is maximal exactly when every stable occurrence
`(j, r)` whose power `A ^ r` contains the power `A ^ q` is `(i, q)` itself. -/
theorem isMaxStableOccurrence_iff {W A : FreeGroup α} {i q : ℕ} :
    W.IsMaxStableOccurrence A i q ↔ W.IsStableOccurrence A i q ∧ ∀ j r,
      W.IsStableOccurrence A j r → j ≤ i →
        i + q * A.toWord.length ≤ j + r * A.toWord.length → j = i ∧ r = q :=
  Iff.rfl

/-- A maximal stable occurrence is a stable occurrence. -/
theorem IsMaxStableOccurrence.isStableOccurrence {W A : FreeGroup α} {i q : ℕ}
    (h : W.IsMaxStableOccurrence A i q) : W.IsStableOccurrence A i q :=
  h.1

/-! ### Bounds, sizes and ranks -/

/-- The upper `A`-bound `max_A(W)` ([IFT], Definition 33): the largest exponent `q` of a stable
occurrence of `A ^ q` or of `A⁻¹ ^ q` in `W`, and `0` if there is none (and, as a junk value,
for `A = 1`, whose stable occurrences have unbounded exponents). The source's exponents carry a
sign, `A⁻¹ ^ q` counting as `A ^ (-q)`; they are counted here by absolute value. -/
noncomputable def maxExp (W A : FreeGroup α) : ℕ :=
  sSup {q | ∃ i, W.IsStableOccurrence A i q ∨ W.IsStableOccurrence A⁻¹ i q}

/-- The upper bound counts the powers of `A` and of `A⁻¹` alike. -/
@[simp]
theorem maxExp_inv (W A : FreeGroup α) : maxExp W A⁻¹ = maxExp W A := by
  simp only [maxExp, inv_inv, or_comm]

/-- The exponent of a stable occurrence of a power of `A ≠ 1` is at most the upper `A`-bound. -/
theorem IsStableOccurrence.le_maxExp {W A : FreeGroup α} (hA : A ≠ 1) {i q : ℕ}
    (h : W.IsStableOccurrence A i q) : q ≤ maxExp W A := by
  -- the exponents of stable occurrences of `A` and `A⁻¹` are bounded by the length of `W`
  have hbdd (B : FreeGroup α) (i q : ℕ) (hB : B ≠ 1) (h : W.IsStableOccurrence B i q) :
      q ≤ W.toWord.length := by
    have := h.add_mul_le_length
    have : 1 ≤ B.toWord.length := List.length_pos_iff.2 (toWord_eq_nil_iff.not.2 hB)
    nlinarith
  refine le_csSup ⟨W.toWord.length, ?_⟩ ⟨i, .inl h⟩
  rintro q' ⟨i', h' | h'⟩
  exacts [hbdd _ _ _ hA h', hbdd _ _ _ (inv_ne_one.2 hA) h']

/-- The upper `A`-bound is at most any bound on the exponents of the stable occurrences of the
powers of `A` and of `A⁻¹`. -/
theorem maxExp_le {W A : FreeGroup α} {r : ℕ}
    (h : ∀ i q, W.IsStableOccurrence A i q ∨ W.IsStableOccurrence A⁻¹ i q → q ≤ r) :
    maxExp W A ≤ r :=
  csSup_le' fun q ⟨i, hq⟩ => h i q hq

/-- A positive upper `A`-bound is attained: it is the exponent of a stable occurrence of a power
of `A` or of `A⁻¹` in `W`. -/
theorem exists_isStableOccurrence_maxExp {W A : FreeGroup α} (h : maxExp W A ≠ 0) :
    ∃ i, W.IsStableOccurrence A i (maxExp W A) ∨ W.IsStableOccurrence A⁻¹ i (maxExp W A) :=
  Nat.sSup_mem (Set.ne_empty_iff_nonempty.1 fun he => h (by simp [maxExp, he]))
    (by_contra fun hb => h (Nat.sSup_of_not_bddAbove hb))

/-- The canonical `N`-large `A`-decomposition of `W` has size `(N, r)` ([IFT], Definition 34, in
the form used in Definition 38): every maximal stable occurrence of a power of `A` or of `A⁻¹` in
`W` has exponent at least `N` or at most `r`, so that the words between the `N`-large powers have
upper `A`-bound at most `r`. The lower bound of Definition 34 is taken to be `N`, the last piece
of the decomposition is included, and exponents are counted by absolute value. If `A` is not
cyclically reduced, no power of `A` has a stable occurrence and the condition holds trivially. -/
def HasLargeSize (W A : FreeGroup α) (N r : ℕ) : Prop :=
  ∀ B ∈ ({A, A⁻¹} : Set (FreeGroup α)), ∀ i q, W.IsMaxStableOccurrence B i q → N ≤ q ∨ q ≤ r

/-- The canonical `N`-large `A`-decomposition of `W` has size `(N, r)` exactly when every maximal
stable occurrence of a power of `A` or of `A⁻¹` in `W` has exponent at least `N` or at most `r`. -/
theorem hasLargeSize_iff {W A : FreeGroup α} {N r : ℕ} :
    W.HasLargeSize A N r ↔ ∀ i q,
      W.IsMaxStableOccurrence A i q ∨ W.IsMaxStableOccurrence A⁻¹ i q → N ≤ q ∨ q ≤ r := by
  simp only [HasLargeSize, Set.forall_mem_insert, Set.mem_singleton_iff, forall_eq, or_imp,
    forall_and]

/-- The size condition treats the powers of `A` and of `A⁻¹` alike. -/
@[simp]
theorem hasLargeSize_inv {W A : FreeGroup α} {N r : ℕ} :
    W.HasLargeSize A⁻¹ N r ↔ W.HasLargeSize A N r := by
  simp only [hasLargeSize_iff, inv_inv, or_comm]

/-- If no stable occurrence of a power of `A` or of `A⁻¹` in `W` has exponent above `r`, then the
canonical `N`-large decomposition has size `(N, r)` for every `N`. -/
theorem hasLargeSize_of_maxExp_le {W A : FreeGroup α} {N r : ℕ} (h : maxExp W A ≤ r) :
    W.HasLargeSize A N r := by
  intro B hB i q hmax
  right
  rcases eq_or_ne A 1 with rfl | hA
  · -- no stable occurrence of a power of `1` is maximal: it extends to a larger exponent
    obtain rfl : B = 1 := by simpa using hB
    obtain ⟨⟨-, u, v, hW, hu⟩, hmax⟩ := hmax
    have := hmax i (q + 1) ⟨Nat.le_add_left 1 q, u, v, by simpa using hW, hu⟩ le_rfl (by simp)
    lia
  · rcases hB with rfl | rfl
    · exact (hmax.1.le_maxExp hA).trans h
    · exact (hmax.1.le_maxExp (inv_ne_one.2 hA)).trans ((maxExp_inv W A).trans_le h)

/-- The `N`-large rank of `W` with respect to a list of periods `𝒜 = (A₁, …, A_L)` ([IFT],
Definitions 34 and 35): the largest index `j ∈ [1, L]` such that `A_j ^ q` or `A_j⁻¹ ^ q` has a
stable occurrence in `W` for some `q ≥ N`, and `0` if there is none. For `N = 1` this is the
`𝒜`-rank of `W`. Powers of `A_j⁻¹` count as in the `𝒜`-rank of Definition 34 (Definition 35
literally mentions only `A_j ^ q`), and an entry `A_j = 1` counts for every `W` as a junk case. -/
noncomputable def largeRank (𝒜 : List (FreeGroup α)) (N : ℕ) (W : FreeGroup α) : ℕ :=
  sSup {j | ∃ (hj : 1 ≤ j ∧ j ≤ 𝒜.length) (i q : ℕ), N ≤ q ∧
    (W.IsStableOccurrence (𝒜[j - 1]'(by omega)) i q ∨
      W.IsStableOccurrence (𝒜[j - 1]'(by omega))⁻¹ i q)}

/-- If `𝒜[j] ^ q` or `𝒜[j]⁻¹ ^ q` has a stable occurrence in `W` for some `q ≥ N`, then the
`N`-large rank of `W` is at least `j + 1`. -/
theorem le_largeRank {𝒜 : List (FreeGroup α)} {N : ℕ} {W : FreeGroup α} {j i q : ℕ}
    (hj : j < 𝒜.length) (hq : N ≤ q)
    (h : W.IsStableOccurrence 𝒜[j] i q ∨ W.IsStableOccurrence 𝒜[j]⁻¹ i q) :
    j + 1 ≤ largeRank 𝒜 N W :=
  le_csSup ⟨𝒜.length, fun _ ⟨hj', _⟩ => hj'.2⟩ ⟨⟨by lia, by lia⟩, i, q, hq, h⟩

/-- The `N`-large rank of `W` is at most `s` if every `j` such that `𝒜[j] ^ q` or `𝒜[j]⁻¹ ^ q`
has a stable occurrence in `W` for some `q ≥ N` satisfies `j + 1 ≤ s`. -/
theorem largeRank_le {𝒜 : List (FreeGroup α)} {N : ℕ} {W : FreeGroup α} {s : ℕ}
    (h : ∀ (j : ℕ) (hj : j < 𝒜.length) (i q : ℕ), N ≤ q →
      (W.IsStableOccurrence 𝒜[j] i q ∨ W.IsStableOccurrence 𝒜[j]⁻¹ i q) → j + 1 ≤ s) :
    largeRank 𝒜 N W ≤ s :=
  csSup_le' fun j ⟨hj, i, q, hq, hs⟩ => by
    have := h (j - 1) (by lia) i q hq hs
    lia

/-- The `N`-large rank is at most the length of the list of periods. -/
theorem largeRank_le_length (𝒜 : List (FreeGroup α)) (N : ℕ) (W : FreeGroup α) :
    largeRank 𝒜 N W ≤ 𝒜.length :=
  largeRank_le fun _ hj _ _ _ _ => hj

/-- A positive `N`-large rank is attained: if it is `j + 1`, then `𝒜[j] ^ q` or `𝒜[j]⁻¹ ^ q` has a
stable occurrence in `W` for some `q ≥ N`. -/
theorem exists_isStableOccurrence_of_largeRank_eq_add_one {𝒜 : List (FreeGroup α)} {N : ℕ}
    {W : FreeGroup α} {j : ℕ} (h : largeRank 𝒜 N W = j + 1) :
    ∃ (hj : j < 𝒜.length) (i q : ℕ), N ≤ q ∧
      (W.IsStableOccurrence 𝒜[j] i q ∨ W.IsStableOccurrence 𝒜[j]⁻¹ i q) := by
  by_contra hne
  -- otherwise every index `k` with an `N`-large stable occurrence satisfies `k < j`
  have : largeRank 𝒜 N W ≤ j := largeRank_le fun k hk i q hq hs => by
    have := le_largeRank hk hq hs
    rcases eq_or_ne k j with rfl | hkj
    · exact absurd ⟨hk, i, q, hq, hs⟩ hne
    · lia
  lia

/-! ### Examples -/

section Examples

variable (a : α)

/- No power of `a⁻¹` has a stable occurrence in a power of `a`. -/
private theorem not_isStableOccurrence_of_pow_inv (n i q : ℕ) :
    ¬(of a ^ n).IsStableOccurrence (of a)⁻¹ i q := by
  rintro ⟨-, u, v, hW, -⟩
  have : (a, false) ∈ (of a ^ n).toWord := by simp [hW, toWord_inv, invRev, toWord_of]
  simp [toWord_of_pow] at this

/- The stable occurrences of powers of `a` in `a⁷` end by position `7`. -/
private theorem add_le_of_isStableOccurrence_of_pow {i q : ℕ}
    (h : (of a ^ 7).IsStableOccurrence (of a) i q) : i + q + 2 ≤ 7 := by
  have := h.add_mul_le_length
  simp only [toWord_of_pow, toWord_of, List.length_replicate, List.length_singleton,
    mul_one] at this
  lia

private theorem isStableOccurrence_of_pow_seven : (of a ^ 7).IsStableOccurrence (of a) 0 5 :=
  isStableOccurrence_pow (by simp [toWord_of]) (by norm_num)

/- In `a⁷`, the occurrence of `a⁵` at position `1`, flanked by `a` on each side, is a maximal
stable occurrence. -/
private theorem isMaxStableOccurrence_of_pow_seven :
    (of a ^ 7).IsMaxStableOccurrence (of a) 0 5 := by
  refine ⟨isStableOccurrence_of_pow_seven a, fun j r h hj _ => ?_⟩
  have := add_le_of_isStableOccurrence_of_pow a h
  simp only [toWord_of, List.length_singleton, mul_one] at *
  lia

/-- The upper `a`-bound of `a⁷` is `5`. -/
example : maxExp (of a ^ 7) (of a) = 5 := by
  refine le_antisymm (maxExp_le fun i q h => ?_)
    ((isStableOccurrence_of_pow_seven a).le_maxExp (of_ne_one a))
  rcases h with h | h
  · have := add_le_of_isStableOccurrence_of_pow a h
    lia
  · exact absurd h (not_isStableOccurrence_of_pow_inv a 7 i q)

/-- The canonical `5`-large `a`-decomposition of `a⁷` has size `(5, 2)`. -/
example : (of a ^ 7).HasLargeSize (of a) 5 2 := by
  rintro B (rfl | rfl) i q hmax
  · have := add_le_of_isStableOccurrence_of_pow a hmax.1
    have := hmax.2 0 5 (isStableOccurrence_of_pow_seven a) (Nat.zero_le i)
      (by simp only [toWord_of, List.length_singleton, mul_one]; lia)
    lia
  · exact absurd hmax.1 (not_isStableOccurrence_of_pow_inv a 7 i q)

/-- The canonical `6`-large `a`-decomposition of `a⁷` does not have size `(6, 2)`: the maximal
stable occurrence `a⁵` is neither `6`-large nor of exponent at most `2`. -/
example : ¬(of a ^ 7).HasLargeSize (of a) 6 2 := fun h => by
  have := h (of a) (by simp) 0 5 (isMaxStableOccurrence_of_pow_seven a)
  lia

/-- With respect to the single period `a`, the element `a⁷` has `5`-large rank `1` and
`6`-large rank `0`. -/
example : largeRank [of a] 5 (of a ^ 7) = 1 ∧ largeRank [of a] 6 (of a ^ 7) = 0 := by
  refine ⟨le_antisymm (largeRank_le_length _ _ _)
    (le_largeRank (j := 0) (by simp) le_rfl (.inl (isStableOccurrence_of_pow_seven a))),
    Nat.le_zero.1 (largeRank_le fun j hj i q hq h => ?_)⟩
  obtain rfl : j = 0 := by simpa using hj
  rcases h with h | h
  · have := add_le_of_isStableOccurrence_of_pow a h
    lia
  · exact absurd h (not_isStableOccurrence_of_pow_inv a 7 i q)

end Examples

/- The element `aba` of the free group on two generators is not a proper power: it has
exponent sum `1` in `b`. -/
private theorem not_isProperPower_aba : ¬Group.IsProperPower (of (0 : Fin 2) * of 1 * of 0) :=
  Group.not_isProperPower_of_map_eq_ofAdd_one
    (FreeGroup.lift fun c => if c = 1 then Multiplicative.ofAdd (1 : ℤ) else 1) (by simp)

/-- Lemma 57 needs `A` not to be a proper power: `A = (ab)²` has stable occurrences at `0` and
`2` in `(ab)⁷`, whose blocks share `10 ≥ |A|` letters, at positions not congruent modulo
`|A| = 4`. -/
example : Group.IsProperPower ((of (0 : Fin 2) * of 1) ^ 2) ∧
    ((of (0 : Fin 2) * of 1) ^ 7).IsStableOccurrence ((of 0 * of 1) ^ 2) 0 1 ∧
    ((of (0 : Fin 2) * of 1) ^ 7).IsStableOccurrence ((of 0 * of 1) ^ 2) 2 1 ∧
    0 ≤ 2 + (1 + 1) * ((of (0 : Fin 2) * of 1) ^ 2).toWord.length ∧
    2 ≤ 0 + (1 + 1) * ((of (0 : Fin 2) * of 1) ^ 2).toWord.length ∧
    ¬0 ≡ 2 [MOD ((of (0 : Fin 2) * of 1) ^ 2).toWord.length] :=
  ⟨Group.isProperPower_pow _ le_rfl, ⟨le_rfl, [], [(0, true), (1, true)], by decide, rfl⟩,
    ⟨le_rfl, [(0, true), (1, true)], [], by decide, rfl⟩, by decide, by decide, by decide⟩

/-- Lemma 57 needs stability: the period `A = aba` occurs (without flanks) at positions `0` and
`2` of `ababa`, which are not congruent modulo `|A| = 3`. -/
example : ¬Group.IsProperPower (of (0 : Fin 2) * of 1 * of 0) ∧
    ((of (0 : Fin 2) * of 1) ^ 2 * of 0).toWord =
      [] ++ (of (0 : Fin 2) * of 1 * of 0).toWord ++ [(1, true), (0, true)] ∧
    ((of (0 : Fin 2) * of 1) ^ 2 * of 0).toWord =
      [(0, true), (1, true)] ++ (of (0 : Fin 2) * of 1 * of 0).toWord ++ [] ∧
    ¬0 ≡ 2 [MOD (of (0 : Fin 2) * of 1 * of 0).toWord.length] :=
  ⟨not_isProperPower_aba, by decide, by decide, by decide⟩

/-- Lemma 57 needs the blocks to overlap in at least `|A|` letters: the period `A = aba` has
stable occurrences `(0, 1)` and `(8, 1)` in `W = (aba)³ ba (aba)²`, whose blocks share one
letter, at positions not congruent modulo `|A| = 3`. -/
example : ¬Group.IsProperPower (of (0 : Fin 2) * of 1 * of 0) ∧
    ((of (0 : Fin 2) * of 1 * of 0) ^ 3 * (of 1 * of 0) *
      (of 0 * of 1 * of 0) ^ 2).IsStableOccurrence (of 0 * of 1 * of 0) 0 1 ∧
    ((of (0 : Fin 2) * of 1 * of 0) ^ 3 * (of 1 * of 0) *
      (of 0 * of 1 * of 0) ^ 2).IsStableOccurrence (of 0 * of 1 * of 0) 8 1 ∧
    ¬8 ≤ 0 + (1 + 1) * (of (0 : Fin 2) * of 1 * of 0).toWord.length ∧
    ¬0 ≡ 8 [MOD (of (0 : Fin 2) * of 1 * of 0).toWord.length] :=
  ⟨not_isProperPower_aba,
    ⟨le_rfl, [], [(1, true), (0, true), (0, true), (1, true), (0, true), (0, true), (1, true),
      (0, true)], by decide, rfl⟩,
    ⟨le_rfl, [(0, true), (1, true), (0, true), (0, true), (1, true), (0, true), (0, true),
      (1, true)], [], by decide, rfl⟩, by decide, by decide⟩

end FreeGroup
