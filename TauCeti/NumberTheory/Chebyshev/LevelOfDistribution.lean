/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import TauCeti.NumberTheory.Chebyshev.ResidueClass

/-!
# The level of distribution of the primes

For a modulus `q` and a real cutoff `x`, the *discrepancy*
`discrepancy q x = max_{(a, q) = 1} |π(x; q, a) - π(x) / φ(q)|` is the largest deviation of the
number `π(x; q, a) = Chebyshev.primeCountAP q a x` of primes `p ≤ x` in a reduced residue class
from the proportion `1 / φ(q)` of all primes `p ≤ x`. The maximum runs over the reduced residues
`0 ≤ a < q` (none for `q = 0`, where the maximum is `0`), and the comparison term `π(x) / φ(q)`
counts every prime `p ≤ x`, including the primes dividing `q`, as in Maynard's normalization.

Following Maynard (1.3), the primes have *level of distribution* `θ` (`PrimesHaveLevel θ`) if for
every `A > 0`

```text
∑_{1 ≤ q ≤ x^θ} max_{(a, q) = 1} |π(x; q, a) - π(x) / φ(q)| = O_A(x / (log x)^A)   (x → ∞).
```

No sign is imposed on `θ`: every `θ ≤ 0` is a level, since then only `q = 1` occurs. The
Bombieri–Vinogradov theorem gives every `θ < 1/2`; the Elliott–Halberstam conjecture
(`ElliottHalberstam`) asserts every `θ < 1`. It is a named hypothesis, and nothing here asserts it.

Maynard's sieve uses the level through the error terms `E(N, q)` of (5.16), here `windowError q N`:
one plus the largest deviation, over the reduced classes, of the number of primes in the window
`[N, 2N)` from `1 / φ(q)` of all primes in the window. Since the window `[N, 2N)` is the
difference of the ranges `p ≤ 2N - 1` and `p ≤ N - 1`, `E(N, q)` is at most
`1 + discrepancy q (2N - 1) + discrepancy q (N - 1)`, and moving the cutoff `N - 1` to `N` costs
at most `1`. Hence a level `θ < 1` gives `∑_{1 ≤ q ≤ N^θ} E(N, q) = O_A(N / (log N)^A)` for every
`A`, and by monotonicity the same over `q ≤ N^θ'` for every `θ' ≤ θ`: the form used in
Maynard (5.20).

## Main definitions

* `TauCeti.SieveDistribution.discrepancy q x`: `max_{(a, q) = 1} |π(x; q, a) - π(x) / φ(q)|`.
* `TauCeti.SieveDistribution.PrimesHaveLevel θ`: the primes have level of distribution `θ`.
* `TauCeti.SieveDistribution.ElliottHalberstam`: every `θ < 1` is a level of distribution.
* `TauCeti.SieveDistribution.windowError q N`: Maynard's `E(N, q)`.

## Main results

* `TauCeti.SieveDistribution.abs_primeCountAP_sub_le_discrepancy` and
  `TauCeti.SieveDistribution.discrepancy_le`: the discrepancy bounds, and is bounded by any bound
  for, every reduced class.
* `TauCeti.SieveDistribution.discrepancy_one`: the trivial modulus has discrepancy `0`.
* `TauCeti.SieveDistribution.PrimesHaveLevel.isBigO`: a level gives the bound for every real `A`.
* `TauCeti.SieveDistribution.PrimesHaveLevel.mono`: a level `θ` is a level for every `θ' ≤ θ`.
* `TauCeti.SieveDistribution.primesHaveLevel_of_nonpos`: every `θ ≤ 0` is a level.
* `TauCeti.SieveDistribution.discrepancy_natCast_sub_one_le`: moving the cutoff from `N` to `N - 1`
  changes the discrepancy by at most `1`.
* `TauCeti.SieveDistribution.windowError_le`:
  `E(N, q) ≤ 1 + discrepancy q (2N - 1) + discrepancy q (N - 1)`.
* `TauCeti.SieveDistribution.PrimesHaveLevel.isBigO_sum_windowError`: for a level `θ < 1`,
  `∑_{1 ≤ q ≤ N^θ} E(N, q) = O_A(N / (log N)^A)` for every `A`.

## References

* J. Maynard, *Small gaps between primes*, Ann. of Math. (2) 181 (2015), 383–413, definition
  (1.3), equations (5.16) and (5.20).
-/

public section

open Finset Filter Asymptotics
open Chebyshev (primeCountAP)
open scoped Nat.Prime

namespace TauCeti.SieveDistribution

/-- The largest deviation `max_{(a, q) = 1} |π(x; q, a) - π(x) / φ(q)|` of the number of primes
`p ≤ x` in a reduced residue class modulo `q` from the proportion `1 / φ(q)` of all primes `p ≤ x`.
The maximum runs over the reduced residues `0 ≤ a < q`; for `q = 0` there are none and it is `0`.
The comparison term `π(x) / φ(q)` counts every prime `p ≤ x`, including those dividing `q`. -/
noncomputable def discrepancy (q : ℕ) (x : ℝ) : ℝ :=
  ⨆ a : {a : Fin q // (a : ℕ).Coprime q},
    |(primeCountAP q ((a.val : ℕ) : ZMod q) x : ℝ) - π ⌊x⌋₊ / q.totient|

/-- The primes have level of distribution `θ`, in the sense of Maynard (1.3): for every `A > 0`,
`∑_{1 ≤ q ≤ x^θ} max_{(a, q) = 1} |π(x; q, a) - π(x) / φ(q)| = O_A(x / (log x)^A)` as `x → ∞`.
No sign condition is imposed on `θ`. -/
def PrimesHaveLevel (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A →
    (fun x : ℝ ↦ ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, discrepancy q x) =O[atTop] fun x ↦ x / Real.log x ^ A

/-- The Elliott–Halberstam conjecture: the primes have level of distribution `θ` for every
`θ < 1`. It is a named hypothesis; nothing here asserts it. -/
def ElliottHalberstam : Prop :=
  ∀ θ : ℝ, θ < 1 → PrimesHaveLevel θ

/-- Maynard's `E(N, q)` of (5.16): one plus the largest deviation, over the reduced residues
`0 ≤ a < q`, of the number of primes in the window `[N, 2N)` congruent to `a` modulo `q` from the
proportion `1 / φ(q)` of all primes in the window. -/
noncomputable def windowError (q N : ℕ) : ℝ :=
  1 + ⨆ a : {a : Fin q // (a : ℕ).Coprime q},
    |(#{p ∈ Ico N (2 * N) | p.Prime ∧ ((p : ℕ) : ZMod q) = ((a.val : ℕ) : ZMod q)} : ℝ) -
      #{p ∈ Ico N (2 * N) | p.Prime} / q.totient|

variable {q : ℕ} {x θ θ' : ℝ}

/-! ### The discrepancy -/

/-- The discrepancy is a maximum of absolute values, hence nonnegative. -/
theorem discrepancy_nonneg (q : ℕ) (x : ℝ) : 0 ≤ discrepancy q x :=
  Real.iSup_nonneg fun _ ↦ abs_nonneg _

/-- There are no reduced residues `0 ≤ a < 0`, so the maximum defining `discrepancy 0 x` is
empty. -/
@[simp]
theorem discrepancy_zero (x : ℝ) : discrepancy 0 x = 0 :=
  Real.iSup_of_isEmpty _

/-- Every reduced residue class modulo `q` deviates from the mean by at most `discrepancy q x`. -/
theorem abs_primeCountAP_sub_le_discrepancy {a : ZMod q} (ha : IsUnit a) (x : ℝ) :
    |(primeCountAP q a x : ℝ) - π ⌊x⌋₊ / q.totient| ≤ discrepancy q x := by
  rcases eq_or_ne q 0 with rfl | hq
  · -- Modulo `0` the congruence is equality, and no prime is a unit of `ℤ`.
    have h : primeCountAP 0 a x = 0 := by
      rw [Chebyshev.primeCountAP_def]
      refine card_eq_zero.2 <| filter_eq_empty_iff.2 fun p hp hpa ↦ ?_
      have hu : (p : ℕ).Coprime 0 := (ZMod.isUnit_iff_coprime p 0).1 (hpa ▸ ha)
      exact (Nat.prime_of_mem_primesLE hp).ne_one ((Nat.coprime_zero_right p).1 hu)
    simp [h]
  · have : NeZero q := ⟨hq⟩
    have hcop : a.val.Coprime q :=
      (ZMod.isUnit_iff_coprime a.val q).1 (by rwa [ZMod.natCast_zmod_val])
    refine le_of_eq_of_le ?_ (le_ciSup (Finite.bddAbove_range _) ⟨⟨a.val, a.val_lt⟩, hcop⟩)
    simp only [ZMod.natCast_zmod_val]

/-- A common bound for the reduced residue classes modulo `q` bounds `discrepancy q x`. Such a
bound is nonnegative, since `1` is a unit. -/
theorem discrepancy_le {C : ℝ}
    (h : ∀ a : ZMod q, IsUnit a → |(primeCountAP q a x : ℝ) - π ⌊x⌋₊ / q.totient| ≤ C) :
    discrepancy q x ≤ C :=
  Real.iSup_le (fun a ↦ h _ ((ZMod.isUnit_iff_coprime _ q).2 a.property))
    ((abs_nonneg _).trans (h 1 isUnit_one))

/-- Modulo `1` every prime lies in the single class, so the discrepancy vanishes. -/
@[simp]
theorem discrepancy_one (x : ℝ) : discrepancy 1 x = 0 :=
  le_antisymm (discrepancy_le fun a _ ↦ by simp) (discrepancy_nonneg 1 x)

/-! ### Levels of distribution -/

/-- A larger power of the logarithm in the denominator gives a smaller function. -/
private theorem isBigO_div_log_rpow_of_le {A B : ℝ} (hAB : A ≤ B) :
    (fun x : ℝ ↦ x / Real.log x ^ B) =O[atTop] fun x ↦ x / Real.log x ^ A := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hlog : 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos 1) hx
  have hx0 : 0 ≤ x := (Real.exp_pos 1).le.trans hx
  have hA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos (by linarith) A
  rw [one_mul, Real.norm_of_nonneg (div_nonneg hx0 (Real.rpow_nonneg (by linarith) B)),
    Real.norm_of_nonneg (div_nonneg hx0 hA.le)]
  exact div_le_div_of_nonneg_left hx0 hA (Real.rpow_le_rpow_of_exponent_le hlog hAB)

/-- A level of distribution gives the bound for every real saving `A`, not only for `A > 0`. -/
theorem PrimesHaveLevel.isBigO (h : PrimesHaveLevel θ) (A : ℝ) :
    (fun x : ℝ ↦ ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, discrepancy q x) =O[atTop] fun x ↦ x / Real.log x ^ A :=
  (h (max A 1) (lt_max_of_lt_right one_pos)).trans (isBigO_div_log_rpow_of_le (le_max_left A 1))

/-- A level of distribution is a level for every smaller exponent. -/
theorem PrimesHaveLevel.mono (h : PrimesHaveLevel θ) (hθ : θ' ≤ θ) : PrimesHaveLevel θ' := by
  intro A hA
  refine IsBigO.trans (IsBigO.of_bound 1 ?_) (h A hA)
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [one_mul, Real.norm_of_nonneg (sum_nonneg fun q _ ↦ discrepancy_nonneg q x),
    Real.norm_of_nonneg (sum_nonneg fun q _ ↦ discrepancy_nonneg q x)]
  exact sum_le_sum_of_subset_of_nonneg
    (Icc_subset_Icc_right (Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx hθ)))
    fun q _ _ ↦ discrepancy_nonneg q x

/-- Every `θ ≤ 0` is a level of distribution: for `x ≥ 1` only the modulus `q = 1` occurs. -/
theorem primesHaveLevel_of_nonpos (hθ : θ ≤ 0) : PrimesHaveLevel θ := by
  intro A _
  refine (isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with x hx
  refine (sum_eq_zero fun q hq ↦ ?_).symm
  have hle : ⌊x ^ θ⌋₊ ≤ 1 := Nat.floor_le_one_of_le_one (Real.rpow_le_one_of_one_le_of_nonpos hx hθ)
  obtain rfl : q = 1 := by have := mem_Icc.1 hq; omega
  exact discrepancy_one x

/-! ### Maynard's window errors -/

/-- A window error is at least `1`. -/
theorem one_le_windowError (q N : ℕ) : 1 ≤ windowError q N :=
  le_add_of_nonneg_right <| Real.iSup_nonneg fun _ ↦ abs_nonneg _

/-- The window `[0, 0)` is empty. -/
@[simp]
theorem windowError_zero_right (q : ℕ) : windowError q 0 = 1 := by
  simp [windowError, Real.iSup_const_zero]

/-- Modulo `1` the single class holds every prime of the window. -/
@[simp]
theorem windowError_one_left (N : ℕ) : windowError 1 N = 1 := by
  simp [windowError, Subsingleton.eq_zero]

/-- The primes of the window `[N, 2N)` satisfying `P` are those with `p ≤ 2N - 1` minus those with
`p ≤ N - 1`. -/
private theorem card_filter_Ico_add_card_filter_primesLE (N : ℕ) (P : ℕ → Prop)
    [DecidablePred P] :
    #{p ∈ Ico N (2 * N) | p.Prime ∧ P p} + #{p ∈ (N - 1).primesLE | P p} =
      #{p ∈ (2 * N - 1).primesLE | P p} := by
  have hD : Disjoint {p ∈ Ico N (2 * N) | p.Prime ∧ P p} {p ∈ (N - 1).primesLE | P p} := by
    refine disjoint_left.2 fun p h₁ h₂ ↦ ?_
    simp only [mem_filter, mem_Ico, Nat.mem_primesLE] at h₁ h₂
    obtain ⟨⟨h₁, h₁'⟩, -⟩ := h₁
    obtain ⟨⟨h₂, -⟩, -⟩ := h₂
    omega
  rw [← card_union_of_disjoint hD]
  congr 1
  ext p
  simp only [mem_union, mem_filter, mem_Ico, Nat.mem_primesLE]
  constructor
  · rintro (⟨⟨h₁, h₂⟩, hp, hP⟩ | ⟨⟨h, hp⟩, hP⟩) <;> exact ⟨⟨by omega, hp⟩, hP⟩
  · rintro ⟨⟨h, hp⟩, hP⟩
    have := hp.two_le
    by_cases hN : N ≤ p
    · exact Or.inl ⟨⟨hN, by omega⟩, hp, hP⟩
    · exact Or.inr ⟨⟨by omega, hp⟩, hP⟩

/-- A window error is controlled by the discrepancies at the two ends of the window: since the
window `[N, 2N)` is the difference of the ranges `p ≤ 2N - 1` and `p ≤ N - 1`,
`E(N, q) ≤ 1 + discrepancy q (2N - 1) + discrepancy q (N - 1)`. -/
theorem windowError_le (q N : ℕ) :
    windowError q N ≤ 1 + discrepancy q ↑(2 * N - 1) + discrepancy q ↑(N - 1) := by
  rw [windowError, add_assoc]
  refine add_le_add le_rfl (Real.iSup_le (fun a ↦ ?_)
    (add_nonneg (discrepancy_nonneg _ _) (discrepancy_nonneg _ _)))
  have ha : IsUnit ((a.val : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime _ q).2 a.property
  have h₁ := abs_primeCountAP_sub_le_discrepancy ha ((2 * N - 1 : ℕ) : ℝ)
  have h₂ := abs_primeCountAP_sub_le_discrepancy ha ((N - 1 : ℕ) : ℝ)
  have hw := card_filter_Ico_add_card_filter_primesLE N
    (fun p ↦ ((p : ℕ) : ZMod q) = ((a.val : ℕ) : ZMod q))
  have ht := card_filter_Ico_add_card_filter_primesLE N (fun _ ↦ True)
  simp only [and_true, filter_true, Nat.primesLE_card_eq_primeCounting] at ht
  rw [Chebyshev.primeCountAP_def, Nat.floor_natCast] at h₁ h₂
  rw [← hw, ← ht] at h₁
  push_cast at h₁ h₂
  calc _ = |((#{p ∈ Ico N (2 * N) | p.Prime ∧ ((p : ℕ) : ZMod q) = ((a.val : ℕ) : ZMod q)} : ℝ) +
          #{p ∈ (N - 1).primesLE | ((p : ℕ) : ZMod q) = ((a.val : ℕ) : ZMod q)} -
          (#{p ∈ Ico N (2 * N) | p.Prime} + π (N - 1)) / q.totient) -
        (#{p ∈ (N - 1).primesLE | ((p : ℕ) : ZMod q) = ((a.val : ℕ) : ZMod q)} -
          π (N - 1) / q.totient)| := by
        congr 1
        ring
    _ ≤ _ := (abs_sub _ _).trans (add_le_add h₁ h₂)

/-- Moving the cutoff from `N` down to `N - 1` removes at most the prime `N` itself. -/
private theorem card_filter_primesLE_le_add_one (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    #{p ∈ N.primesLE | P p} ≤ #{p ∈ (N - 1).primesLE | P p} + 1 := by
  refine (card_le_card fun p hp ↦ ?_).trans (card_insert_le N _)
  simp only [mem_filter, Nat.mem_primesLE, mem_insert] at hp ⊢
  by_cases h : p = N
  · exact Or.inl h
  · exact Or.inr ⟨⟨by omega, hp.1.2⟩, hp.2⟩

/-- Moving the cutoff from `N` down to `N - 1` changes the discrepancy by at most one: a
residue class gains or loses at most the prime `N`, and the mean at most `1 / φ(q) ≤ 1`. -/
theorem discrepancy_natCast_sub_one_le (q N : ℕ) :
    discrepancy q ↑(N - 1) ≤ discrepancy q N + 1 := by
  refine discrepancy_le fun a ha ↦ ?_
  have h := abs_primeCountAP_sub_le_discrepancy ha (N : ℝ)
  rw [Chebyshev.primeCountAP_def, Nat.floor_natCast] at h ⊢
  have hmono : (N - 1).primesLE ⊆ N.primesLE := Nat.primesLE_mono (Nat.sub_le N 1)
  have hu₁ : (#{p ∈ N.primesLE | ((p : ℕ) : ZMod q) = a} : ℝ) ≤
      #{p ∈ (N - 1).primesLE | ((p : ℕ) : ZMod q) = a} + 1 := by
    exact_mod_cast card_filter_primesLE_le_add_one N _
  have hu₂ : (#{p ∈ (N - 1).primesLE | ((p : ℕ) : ZMod q) = a} : ℝ) ≤
      #{p ∈ N.primesLE | ((p : ℕ) : ZMod q) = a} := by
    exact_mod_cast card_le_card (filter_subset_filter _ hmono)
  have hv₁ := card_filter_primesLE_le_add_one N (fun _ ↦ True)
  have hv₂ := card_le_card hmono
  simp only [filter_true, Nat.primesLE_card_eq_primeCounting] at hv₁ hv₂
  have he₀ : (0 : ℝ) ≤ ((π N : ℝ) - π (N - 1)) / q.totient :=
    div_nonneg (sub_nonneg.2 (by exact_mod_cast hv₂)) (Nat.cast_nonneg _)
  have he₁ : ((π N : ℝ) - π (N - 1)) / q.totient ≤ 1 := by
    rcases Nat.eq_zero_or_pos q.totient with h0 | h0
    · simp [h0]
    · rw [div_le_one (by exact_mod_cast h0)]
      have : (π N : ℝ) ≤ π (N - 1) + 1 := by exact_mod_cast hv₁
      have : (1 : ℝ) ≤ q.totient := by exact_mod_cast h0
      linarith
  have hid : ((π (N - 1) : ℕ) : ℝ) / q.totient =
      (π N : ℝ) / q.totient - ((π N : ℝ) - π (N - 1)) / q.totient := by
    ring
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-! ### Window errors under a level of distribution -/

/-- `x ^ θ = O(x / (log x) ^ A)` for `θ < 1` and every real `A`. -/
private theorem isBigO_rpow_div_log_rpow (hθ : θ < 1) (A : ℝ) :
    (fun x : ℝ ↦ x ^ θ) =O[atTop] fun x ↦ x / Real.log x ^ A := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [(isLittleO_log_rpow_rpow_atTop A (sub_pos.2 hθ)).bound one_pos,
    eventually_gt_atTop 1] with x hlog hx
  have hx0 : 0 < x := by linarith
  have hlA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos (Real.log_pos hx) A
  rw [one_mul, Real.norm_of_nonneg hlA.le, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hlog
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _),
    Real.norm_of_nonneg (div_nonneg hx0.le hlA.le), le_div_iff₀ hlA]
  calc x ^ θ * Real.log x ^ A ≤ x ^ θ * x ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx0.le _)
    _ = x := by rw [← Real.rpow_add hx0, add_sub_cancel, Real.rpow_one]

/-- If `N ≤ g N ≤ 2 N` eventually, then `g N / (log (g N)) ^ A = O(N / (log N) ^ A)` for
`A ≥ 0`. -/
private theorem isBigO_comp_div_log_rpow {g : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ g N ∧ g N ≤ 2 * N) :
    (fun N ↦ g N / Real.log (g N) ^ A) =O[atTop] fun N : ℕ ↦ (N : ℝ) / Real.log N ^ A := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [hg, eventually_ge_atTop 2] with N ⟨hg₁, hg₂⟩ hN
  have hN1 : (1 : ℝ) < N := Nat.one_lt_cast.2 hN
  have hlN : 0 < Real.log N := Real.log_pos hN1
  have hpos : 0 < Real.log N ^ A := Real.rpow_pos_of_pos hlN A
  have hpow : Real.log N ^ A ≤ Real.log (g N) ^ A :=
    Real.rpow_le_rpow hlN.le (Real.log_le_log (by linarith) hg₁) hA
  rw [Real.norm_of_nonneg (div_nonneg (by linarith) (hpos.le.trans hpow)),
    Real.norm_of_nonneg (div_nonneg (by linarith) hpos.le), ← mul_div_assoc]
  exact div_le_div₀ (by positivity) hg₂ hpos hpow

/-- Pointwise form of the window bound: for `N ≥ 2` the window errors over `q ≤ N ^ θ` sum to at
most `2 N ^ θ` plus the discrepancy sums of the level `θ` at `2N - 1` and at `N`. -/
private theorem norm_sum_windowError_le {N : ℕ} (hN : 2 ≤ N) :
    ‖∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, windowError q N‖ ≤
      1 * ‖2 * (N : ℝ) ^ θ +
        (∑ q ∈ Icc 1 ⌊((2 * N - 1 : ℕ) : ℝ) ^ θ⌋₊, discrepancy q ↑(2 * N - 1)) +
        ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, discrepancy q N‖ := by
  have hpos : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg N) θ
  have hfl : ⌊(N : ℝ) ^ θ⌋₊ ≤ ⌊((2 * N - 1 : ℕ) : ℝ) ^ θ⌋₊ := by
    rcases lt_or_ge θ 0 with hθ | hθ
    · rw [Nat.floor_eq_zero.2 (Real.rpow_lt_one_of_one_lt_of_neg (Nat.one_lt_cast.2 hN) hθ)]
      exact Nat.zero_le _
    · exact Nat.floor_le_floor (Real.rpow_le_rpow (Nat.cast_nonneg N)
        (by exact_mod_cast (show N ≤ 2 * N - 1 by omega)) hθ)
  rw [one_mul, Real.norm_of_nonneg (sum_nonneg fun q _ ↦ zero_le_one.trans
      (one_le_windowError q N)),
    Real.norm_of_nonneg (add_nonneg (add_nonneg (by positivity) (sum_nonneg fun q _ ↦
      discrepancy_nonneg _ _)) (sum_nonneg fun q _ ↦ discrepancy_nonneg _ _))]
  calc ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, windowError q N
      ≤ ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, (2 + discrepancy q ↑(2 * N - 1) + discrepancy q N) :=
        sum_le_sum fun q _ ↦ by
          linarith [windowError_le q N, discrepancy_natCast_sub_one_le q N]
    _ = 2 * ⌊(N : ℝ) ^ θ⌋₊ + ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, discrepancy q ↑(2 * N - 1) +
          ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, discrepancy q N := by
        rw [sum_add_distrib, sum_add_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right,
          nsmul_eq_mul, mul_comm]
    _ ≤ _ := by
        gcongr 2 * ?_ + ?_ + _
        · exact Nat.floor_le hpos
        · exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hfl)
            fun q _ _ ↦ discrepancy_nonneg q _

/-- The window errors of Maynard (5.20): if the primes have level of distribution `θ < 1`, then
`∑_{1 ≤ q ≤ N^θ} E(N, q) = O_A(N / (log N) ^ A)` for every `A`. With
`PrimesHaveLevel.mono`, the same holds over `q ≤ N^θ'` for every `θ' ≤ θ`. -/
theorem PrimesHaveLevel.isBigO_sum_windowError (h : PrimesHaveLevel θ) (hθ : θ < 1) (A : ℝ) :
    (fun N : ℕ ↦ ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, windowError q N) =O[atTop]
      fun N ↦ (N : ℝ) / Real.log N ^ A := by
  set f : ℝ → ℝ := fun x ↦ ∑ q ∈ Icc 1 ⌊x ^ θ⌋₊, discrepancy q x
  have hb : ∀ᶠ N : ℕ in atTop, (N : ℝ) ≤ ((2 * N - 1 : ℕ) : ℝ) ∧
      ((2 * N - 1 : ℕ) : ℝ) ≤ 2 * N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Nat.cast_sub (by omega)]
    push_cast
    constructor <;> linarith [(show (1 : ℝ) ≤ N by exact_mod_cast hN)]
  have hg : Tendsto (fun N : ℕ ↦ ((2 * N - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_atTop_mono' _ (hb.mono fun _ h ↦ h.1) tendsto_natCast_atTop_atTop
  have hnat := fun {k : ℝ → ℝ} (hk : k =O[atTop] fun x ↦ x / Real.log x ^ max A 0) ↦
    hk.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsum : (fun N : ℕ ↦ ∑ q ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, windowError q N) =O[atTop]
      fun N : ℕ ↦ 2 * (N : ℝ) ^ θ + f ((2 * N - 1 : ℕ) : ℝ) + f N :=
    IsBigO.of_bound 1 <| (eventually_ge_atTop 2).mono fun N hN ↦ norm_sum_windowError_le hN
  refine (hsum.trans ((((hnat (isBigO_rpow_div_log_rpow hθ (max A 0))).const_mul_left 2).add
    (((h.isBigO (max A 0)).comp_tendsto hg).trans
      (isBigO_comp_div_log_rpow (le_max_right A 0) hb))).add
    (hnat (h.isBigO (max A 0))))).trans ?_
  exact (isBigO_div_log_rpow_of_le (le_max_left A 0)).comp_tendsto tendsto_natCast_atTop_atTop

/-! ### Examples

Modulo `3` the primes `p ≤ 5` are `2, 5` in the class of `2` and none in the class of `1`, against
the mean `π(5) / φ(3) = 3 / 2`, which also counts the prime `3` of the non-reduced class: the
discrepancy is `3 / 2`, whereas averaging only the primes of the reduced classes would give `1`.
The window `[2, 4)` holds the primes `2` and `3`; against the mean `1` its reduced classes hold
`0` and `1` primes, so `E(2, 3) = 2`. -/

example : discrepancy 3 5 = 3 / 2 := by
  have hπ : (π 5 : ℝ) / Nat.totient 3 = 3 / 2 := by
    rw [Nat.totient_prime Nat.prime_three, show π 5 = 3 by decide]
    norm_num
  have h₁ : primeCountAP 3 1 5 = 0 := by
    rw [Chebyshev.primeCountAP_def, Nat.floor_ofNat]; decide
  have h₂ : primeCountAP 3 2 5 = 2 := by
    rw [Chebyshev.primeCountAP_def, Nat.floor_ofNat]; decide
  refine le_antisymm (Real.iSup_le (fun a ↦ ?_) (by norm_num)) ?_
  · obtain ⟨a, ha⟩ := a
    fin_cases a
    · exact absurd ha (by decide)
    · norm_num [hπ, h₁, abs_of_pos]
    · norm_num [hπ, h₂, abs_of_pos]
  · have := abs_primeCountAP_sub_le_discrepancy (q := 3) (a := 1) isUnit_one 5
    rwa [Nat.floor_ofNat, hπ, h₁, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_pos (by norm_num)] at this

example : windowError 3 2 = 2 := by
  have hφ : (Nat.totient 3 : ℝ) = 2 := by rw [Nat.totient_prime Nat.prime_three]; norm_num
  have ht : #{p ∈ Ico 2 4 | p.Prime} = 2 := by decide
  have h₁ : #{p ∈ Ico 2 4 | p.Prime ∧ ((p : ℕ) : ZMod 3) = 1} = 0 := by decide
  have h₂ : #{p ∈ Ico 2 4 | p.Prime ∧ ((p : ℕ) : ZMod 3) = 2} = 1 := by decide
  rw [windowError, show (2 : ℝ) = 1 + 1 by norm_num]
  congr 1
  refine le_antisymm (Real.iSup_le (fun a ↦ ?_) zero_le_one) ?_
  · obtain ⟨a, ha⟩ := a
    fin_cases a
    · exact absurd ha (by decide)
    · simp [ht, hφ, h₁]
    · simp [ht, hφ, h₂]
  · refine le_of_eq_of_le ?_ (le_ciSup (Finite.bddAbove_range _) ⟨1, by decide⟩)
    simp [ht, hφ, h₁]

end TauCeti.SieveDistribution
