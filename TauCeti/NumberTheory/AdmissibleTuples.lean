/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Group.Nat
import TauCeti.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum.Prime

/-!
# Admissible tuples and the prime `k`-tuples conjecture

A finite set `H` of natural numbers is *admissible* if for every prime `p` some residue class
modulo `p` contains no element of `H`. This is the obvious necessary condition for the translates
`n + h`, `h ∈ H`, to be simultaneously prime for infinitely many `n`: if `H` meets every class
modulo `p`, then for each `n` one of the numbers `n + h` is divisible by `p`, so they can all be
prime only if one of them equals `p`. The *prime `k`-tuples conjecture* asserts that this
condition is also sufficient. It is stated here as a proposition; it is not proved and is not
assumed anywhere. Its case `H = {0, 2}` is the twin prime conjecture.

Only the primes `p ≤ #H` can obstruct admissibility, since `#H` elements meet at most `#H` residue
classes. This gives a finite criterion, and makes admissibility decidable.

## Main definitions

* `TauCeti.SieveMaynard.IsAdmissible H`: for every prime `p`, some residue class modulo `p`
  contains no element of `H`.
* `TauCeti.SieveMaynard.primeTranslates H`: the set of `n` such that `n + h` is prime for every
  `h ∈ H`.
* `TauCeti.SieveMaynard.PrimeTuplesConjecture`: for every admissible `H`, the set
  `primeTranslates H` is infinite.

## Main results

* `TauCeti.SieveMaynard.isAdmissible_iff_card_image_mod_lt`: `H` is admissible exactly when, for
  every prime `p ≤ #H`, the residues of `H` modulo `p` number fewer than `p`.
* `TauCeti.SieveMaynard.IsAdmissible.mono`, `TauCeti.SieveMaynard.isAdmissible_image_add_right_iff`:
  subsets and translates of admissible sets are admissible.
* `TauCeti.SieveMaynard.isAdmissible_of_forall_not_dvd`: if no element of `H` is divisible by a
  prime `p ≤ #H`, then `H` is admissible.
* `TauCeti.SieveMaynard.isAdmissible_of_infinite_primeTranslates`: admissibility is necessary for
  `primeTranslates H` to be infinite.
* `TauCeti.SieveMaynard.PrimeTuplesConjecture.infinite_setOf_twin_prime`: the conjecture implies
  that there are infinitely many twin primes.

## References

* J. Maynard, *Small gaps between primes*, Ann. of Math. 181 (2015), 383–413, §1.
-/

public section

open Finset

namespace TauCeti.SieveMaynard

variable {G H : Finset ℕ}

/-! ### Admissible sets -/

/-- A finite set `H` of natural numbers is admissible if for every prime `p` there is a residue
class `a` modulo `p` that contains no element of `H`. -/
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ a : ℕ, ∀ h ∈ H, ¬h ≡ a [MOD p]

/-- The defining property of an admissible set. -/
theorem isAdmissible_def (H : Finset ℕ) :
    IsAdmissible H ↔ ∀ p : ℕ, p.Prime → ∃ a : ℕ, ∀ h ∈ H, ¬h ≡ a [MOD p] :=
  Iff.rfl

/-- The empty set is admissible. -/
@[simp]
theorem isAdmissible_empty : IsAdmissible ∅ :=
  fun _ _ ↦ ⟨0, fun _ h ↦ absurd h (notMem_empty _)⟩

/-- A subset of an admissible set is admissible. -/
theorem IsAdmissible.mono (hH : IsAdmissible H) (hGH : G ⊆ H) : IsAdmissible G :=
  fun p hp ↦ (hH p hp).imp fun _ ha h hh ↦ ha h (hGH hh)

/-- **Finite criterion for admissibility.** A finite set `H` is admissible exactly when, for
every prime `p ≤ #H`, the residues of `H` modulo `p` number fewer than `p`. The primes `p > #H`
impose no condition, since `#H` elements have at most `#H` residues. -/
theorem isAdmissible_iff_card_image_mod_lt :
    IsAdmissible H ↔ ∀ p : ℕ, p.Prime → p ≤ #H → #(H.image (· % p)) < p := by
  constructor
  · intro hH p hp _
    exact (Nat.exists_forall_not_modEq_iff_card_image_mod_lt hp.pos H).1 (hH p hp)
  · intro h p hp
    refine (Nat.exists_forall_not_modEq_iff_card_image_mod_lt hp.pos H).2 ?_
    rcases le_or_gt p #H with hle | hlt
    · exact h p hp hle
    · exact card_image_le.trans_lt hlt

/-- The finite criterion for admissibility as a statement bounded over `range (#H + 1)`, the form
used to decide it. -/
theorem isAdmissible_iff_forall_mem_range :
    IsAdmissible H ↔ ∀ p ∈ range (#H + 1), p.Prime → #(H.image (· % p)) < p := by
  rw [isAdmissible_iff_card_image_mod_lt]
  exact ⟨fun h p hmem hp ↦ h p hp (Nat.lt_add_one_iff.1 (mem_range.1 hmem)),
    fun h p hp hle ↦ h p (mem_range.2 (Nat.lt_add_one_iff.2 hle)) hp⟩

/-- Admissibility is decidable, by the finite criterion `isAdmissible_iff_forall_mem_range`. -/
instance decidableIsAdmissible (H : Finset ℕ) : Decidable (IsAdmissible H) :=
  decidable_of_iff (∀ p ∈ range (#H + 1), p.Prime → #(H.image (· % p)) < p)
    isAdmissible_iff_forall_mem_range.symm

/-- If no element of `H` is divisible by a prime `p ≤ #H`, then `H` is admissible: it misses the
class of `0` modulo those primes. -/
theorem isAdmissible_of_forall_not_dvd
    (h : ∀ p : ℕ, p.Prime → p ≤ #H → ∀ n ∈ H, ¬p ∣ n) : IsAdmissible H := by
  intro p hp
  rcases le_or_gt p #H with hle | hlt
  · exact ⟨0, fun n hn hmod ↦ h p hp hle n hn (Nat.modEq_zero_iff_dvd.1 hmod)⟩
  · exact (Nat.exists_forall_not_modEq_iff_card_image_mod_lt hp.pos H).2
      (card_image_le.trans_lt hlt)

/-- A translate of an admissible set is admissible. -/
theorem IsAdmissible.image_add_right (hH : IsAdmissible H) (c : ℕ) :
    IsAdmissible (H.image (· + c)) := by
  intro p hp
  obtain ⟨a, ha⟩ := hH p hp
  refine ⟨a + c, fun h hh hmod ↦ ?_⟩
  obtain ⟨h', hh', rfl⟩ := mem_image.1 hh
  exact ha h' hh' (Nat.ModEq.add_right_cancel' c hmod)

/-- Admissibility is invariant under translation. -/
@[simp]
theorem isAdmissible_image_add_right_iff (c : ℕ) :
    IsAdmissible (H.image (· + c)) ↔ IsAdmissible H := by
  refine ⟨fun hH p hp ↦ ?_, fun hH ↦ hH.image_add_right c⟩
  obtain ⟨a, ha⟩ := hH p hp
  refine ⟨a + (p - 1) * c, fun h hh hmod ↦ ha (h + c) (mem_image_of_mem _ hh) ?_⟩
  have hpc : a + (p - 1) * c + c = a + p * c := by
    rw [add_assoc, ← Nat.add_one_mul, Nat.sub_add_cancel hp.one_le]
  exact (hpc ▸ hmod.add_right c).trans (Nat.add_mul_mod_self_left a p c)

/-! ### Prime translates and the prime `k`-tuples conjecture -/

/-- The set of natural numbers `n` such that `n + h` is prime for every `h ∈ H`. -/
def primeTranslates (H : Finset ℕ) : Set ℕ :=
  {n | ∀ h ∈ H, (n + h).Prime}

/-- Membership in `primeTranslates H`. -/
@[simp]
theorem mem_primeTranslates {n : ℕ} : n ∈ primeTranslates H ↔ ∀ h ∈ H, (n + h).Prime :=
  Iff.rfl

/-- Every natural number is a prime translate of the empty set. -/
@[simp]
theorem primeTranslates_empty : primeTranslates ∅ = Set.univ := by
  ext n
  simp

/-- The prime translates of `{0}` are the primes. -/
@[simp]
theorem primeTranslates_singleton_zero : primeTranslates {0} = {n : ℕ | n.Prime} := by
  ext n
  simp

/-- Enlarging `H` shrinks its set of prime translates. -/
theorem primeTranslates_anti (hGH : G ⊆ H) : primeTranslates H ⊆ primeTranslates G :=
  fun _ hn h hh ↦ hn h (hGH hh)

/-- **Admissibility is necessary.** If `n + h` is prime for every `h ∈ H` for infinitely many
`n`, then `H` is admissible: if `H` met every residue class modulo a prime `p`, then for each such
`n` some `n + h` would be divisible by `p`, hence equal to `p`, forcing `n ≤ p`. -/
theorem isAdmissible_of_infinite_primeTranslates (hH : (primeTranslates H).Infinite) :
    IsAdmissible H := by
  by_contra hna
  rw [isAdmissible_def] at hna
  push Not at hna
  obtain ⟨p, hp, hcover⟩ := hna
  refine hH ((Set.finite_le_nat p).subset fun n hn ↦ ?_)
  obtain ⟨h, hh, hmod⟩ := hcover ((p - 1) * n)
  have hpn : n + (p - 1) * n = p * n := by
    rw [add_comm, ← Nat.add_one_mul, Nat.sub_add_cancel hp.one_le]
  have hdvd : p ∣ n + h :=
    Nat.modEq_zero_iff_dvd.1 ((hpn ▸ hmod.add_left n).trans
      (Nat.modEq_zero_iff_dvd.2 (dvd_mul_right p n)))
  have heq : p = n + h := (Nat.prime_dvd_prime_iff_eq hp (hn h hh)).1 hdvd
  rw [Set.mem_ofPred_eq]
  omega

/-- The **prime `k`-tuples conjecture**: for every admissible finite set `H`, there are
infinitely many `n` such that `n + h` is prime for every `h ∈ H`. This is the statement of the
conjecture, not a theorem. -/
def PrimeTuplesConjecture : Prop :=
  ∀ H : Finset ℕ, IsAdmissible H → (primeTranslates H).Infinite

/-- The statement of the prime `k`-tuples conjecture. -/
theorem primeTuplesConjecture_def :
    PrimeTuplesConjecture ↔ ∀ H : Finset ℕ, IsAdmissible H → (primeTranslates H).Infinite :=
  Iff.rfl

/-- The prime `k`-tuples conjecture implies that there are infinitely many twin primes. -/
theorem PrimeTuplesConjecture.infinite_setOf_twin_prime (h : PrimeTuplesConjecture) :
    {n : ℕ | n.Prime ∧ (n + 2).Prime}.Infinite := by
  refine (h {0, 2} (by decide +kernel)).mono fun n hn ↦ ?_
  simpa using hn

/-! ### Examples -/

example : IsAdmissible {0, 2} := by decide +kernel

/-- `{0, 2, 4}` meets all three classes modulo `3`. -/
example : ¬IsAdmissible {0, 2, 4} := by decide +kernel

example : IsAdmissible {0, 2, 6, 8, 12} := by decide +kernel

/-- `{0, 1}` covers both classes modulo `2`. -/
example : ¬IsAdmissible {0, 1} := by decide +kernel

/-- The primes are infinite: the conjecture holds for `H = {0}`. -/
example : (primeTranslates {0}).Infinite := by
  rw [primeTranslates_singleton_zero]
  exact Nat.infinite_setOfPred_prime

/-- `n` and `n + 1` are both prime only for `n = 2`: the set is nonempty but finite, so
`Infinite` cannot be weakened to `Nonempty` in the conjecture. -/
example : primeTranslates {0, 1} = {2} := by
  ext n
  simp only [mem_primeTranslates, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
    add_zero, Set.mem_singleton_iff]
  refine ⟨fun ⟨hn, hn1⟩ ↦ ?_, fun hn ↦ by rw [hn]; norm_num⟩
  by_contra hne
  have hodd : ¬Even n := fun he ↦ hne (hn.even_iff.1 he)
  have h1 : n + 1 = 2 := hn1.even_iff.1 (Nat.even_add_one.2 hodd)
  exact Nat.not_prime_one (by rwa [show n = 1 by omega] at hn)

/-- One of `n`, `n + 2`, `n + 4` is divisible by `3`, so all three are prime only for `n = 3`. -/
example : primeTranslates {0, 2, 4} = {3} := by
  ext n
  simp only [mem_primeTranslates, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq,
    add_zero, Set.mem_singleton_iff]
  refine ⟨fun ⟨h0, h2, h4⟩ ↦ ?_, fun hn ↦ by rw [hn]; norm_num⟩
  have hdvd : 3 ∣ n ∨ 3 ∣ n + 2 ∨ 3 ∣ n + 4 := by omega
  rcases hdvd with h | h | h
  · exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h0).1 h).symm
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h2).1 h
    exact absurd h0 (by rw [show n = 1 by omega]; exact Nat.not_prime_one)
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three h4).1 h
    omega

end TauCeti.SieveMaynard
