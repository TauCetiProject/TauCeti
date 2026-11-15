/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Additive, strongly additive, and completely additive arithmetic functions

An arithmetic function `f : ArithmeticFunction R` taking values in an additive structure with zero
is **additive** (`ArithmeticFunction.IsAdditive`) when `f 1 = 0` and `f (m * n) = f m + f n` for
all positive coprime `m` and `n`. Two strengthenings appear throughout probabilistic and analytic
number theory:

* **Strong additivity** (`ArithmeticFunction.IsStronglyAdditive`): `f` is additive and
  `f (p ^ k) = f p` for every prime `p` and exponent `k > 0`, modeled on `ω = cardDistinctFactors`.
* **Complete additivity** (`ArithmeticFunction.IsCompletelyAdditive`): `f 1 = 0` and
  `f (m * n) = f m + f n` for all positive `m` and `n` without coprimality, modeled on
  `Ω = cardFactors`.

As with Mathlib's `ArithmeticFunction.IsMultiplicative`, the carrier retains `f 0 = 0`, and the
explicit `f 1 = 0` clause is required in non-cancellative codomains such as `ℕ∞` (where the
indicator sending positive integers to `⊤` satisfies `f (m * n) = f m + f n` on positive inputs
without vanishing at `1`); when addition is left-cancellative, the coprime product law alone forces
`f 1 = 0` (`ArithmeticFunction.isAdditive_iff_of_isLeftCancelAdd`). Moreover, since `0.Coprime n`
holds only at `n = 1`, where both `f 0` and `f 1` vanish, coprime additivity automatically extends
to all coprime pairs in `ℕ` (`ArithmeticFunction.IsAdditive.map_mul_of_coprime`), and all three
prime-factorization expansions hold unconditionally for every `n : ℕ` (including `n = 0` and
`n = 1`).

## Main definitions

* `ArithmeticFunction.IsAdditive`: additive arithmetic functions (`f 1 = 0` and coprime additivity
  on positive inputs).
* `ArithmeticFunction.IsStronglyAdditive`: strongly additive arithmetic functions (`IsAdditive` and
  `f (p ^ k) = f p` for prime `p` and `0 < k`).
* `ArithmeticFunction.IsCompletelyAdditive`: completely additive arithmetic functions (`f 1 = 0`
  and `f (m * n) = f m + f n` on all positive inputs).

## Main results

* `ArithmeticFunction.IsAdditive.sum_primeFactors_pow_factorization`: for additive `f` and every
  `n : ℕ`, `f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p)`.
* `ArithmeticFunction.IsAdditive.eq_iff_eq_on_prime_powers`: two additive functions are equal if
  and only if they agree on all prime powers `p ^ k` with `k ≠ 0`.
* `ArithmeticFunction.IsAdditive.lcm_apply_add_gcd_apply`: `f (x.lcm y) + f (x.gcd y) = f x + f y`.
* `ArithmeticFunction.IsStronglyAdditive.sum_primeFactors`,
  `ArithmeticFunction.IsStronglyAdditive.eq_iff_eq_on_primes`: distinct-prime expansion
  `f n = ∑ p ∈ n.primeFactors, f p` and determination by prime values for strongly additive
  functions.
* `ArithmeticFunction.IsCompletelyAdditive.map_pow`,
  `ArithmeticFunction.IsCompletelyAdditive.sum_primeFactors`,
  `ArithmeticFunction.IsCompletelyAdditive.eq_iff_eq_on_primes`: power law `f (n ^ k) = k • f n`,
  multiplicity-weighted prime expansion `f n = ∑ p ∈ n.primeFactors, n.factorization p • f p`, and
  determination by prime values for completely additive functions.
* `ArithmeticFunction.isStronglyAdditive_cardDistinctFactors`,
  `ArithmeticFunction.isCompletelyAdditive_cardFactors`: strong additivity of `ω` and complete
  additivity of `Ω`.

## References

* C. Elsholtz and T. Tao, *Counting the number of solutions to the Erdős–Straus equation on unit
  fractions*, Appendix A, Lemmas A.2–A.3.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 1.
-/

public section

open Finset

namespace ArithmeticFunction

variable {R S : Type*}

/-! ### Additive arithmetic functions -/

/-- An arithmetic function `f` is **additive** if `f 1 = 0` and `f (m * n) = f m + f n` for all
positive coprime natural numbers `m` and `n`. -/
def IsAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 0 ∧ ∀ {m n : ℕ}, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m + f n

/-- Unfolding characterization of `ArithmeticFunction.IsAdditive`. -/
theorem isAdditive_def [AddZeroClass R] {f : ArithmeticFunction R} :
    f.IsAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m + f n :=
  Iff.rfl

/-- In a codomain with left-cancellative addition, the coprime product law on positive inputs
already forces `f 1 = 0` via `f 1 = f (1 * 1) = f 1 + f 1`. -/
theorem isAdditive_iff_of_isLeftCancelAdd [AddZeroClass R] [IsLeftCancelAdd R]
    {f : ArithmeticFunction R} :
    f.IsAdditive ↔ ∀ {m n : ℕ}, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ hf.2, fun h ↦ ⟨add_left_cancel ((h zero_lt_one zero_lt_one rfl).symm.trans
    (add_zero (f 1)).symm), h⟩⟩

namespace IsAdditive

section AddZeroClass

variable [AddZeroClass R] {f : ArithmeticFunction R}

/-- An additive arithmetic function vanishes at `1`. -/
@[simp, grind =]
theorem map_one (hf : f.IsAdditive) : f 1 = 0 :=
  hf.1

/-- Additivity on positive coprime factors. -/
theorem map_mul (hf : f.IsAdditive) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    f (m * n) = f m + f n :=
  hf.2 hm hn hmn

/-- Additivity extends to all coprime pairs in `ℕ`: if one factor is `0`, coprimality forces the
other to be `1`, and both `f 0` and `f 1` vanish. Stated with `m.gcd n = 1` (definitionally
`m.Coprime n`) to match `ArithmeticFunction.IsMultiplicative.map_mul_of_coprime` and `simp` normal
form. -/
@[simp, grind =]
theorem map_mul_of_coprime (hf : f.IsAdditive) {m n : ℕ} (hmn : m.gcd n = 1) :
    f (m * n) = f m + f n := by
  rcases eq_or_ne m 0 with rfl | hm
  · obtain rfl : n = 1 := Nat.coprime_zero_left n |>.mp hmn
    simp [hf.map_one]
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : m = 1 := Nat.coprime_zero_right m |>.mp hmn
    simp [hf.map_one]
  exact hf.2 (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn

/-- Characterization of `IsAdditive` using nonzero guards in place of positivity. -/
theorem iff_ne_zero :
    f.IsAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m + f n :=
  and_congr_right' <| forall₂_congr fun _ _ ↦
    ⟨fun h hm hn ↦ h (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn),
      fun h hm hn ↦ h hm.ne' hn.ne'⟩

/-- Characterization of `IsAdditive` using coprimality on all of `ℕ`, matching the shape of
`ArithmeticFunction.IsMultiplicative`. -/
theorem iff_coprime :
    f.IsAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ ⟨hf.map_one, fun hmn ↦ hf.map_mul_of_coprime hmn⟩,
    fun ⟨h1, h⟩ ↦ ⟨h1, fun _ _ hmn ↦ h hmn⟩⟩

/-- Post-composing an additive arithmetic function on nonzero inputs with an additive monoid
homomorphism preserves additivity. -/
theorem of_eq_addMonoidHom [AddZeroClass S] (hf : f.IsAdditive) (φ : R →+ S)
    {g : ArithmeticFunction S} (hg : ∀ n ≠ 0, g n = φ (f n)) : g.IsAdditive :=
  iff_ne_zero.mpr ⟨by rw [hg 1 one_ne_zero, hf.map_one, φ.map_zero], fun {m n} hm hn hmn ↦ by
    rw [hg (m * n) (mul_ne_zero hm hn), hg m hm, hg n hn, hf.map_mul_of_coprime hmn, map_add]⟩

/-- Pointwise scalar multiplication by a distributive action preserves additivity. -/
theorem smul [DistribSMul S R] (hf : f.IsAdditive) (c : S) : (c • f).IsAdditive :=
  ⟨by simp [hf.map_one], fun hm hn hmn ↦ by simp [hf.map_mul hm hn hmn, smul_add]⟩

end AddZeroClass

/-- Coercing an `ℕ`-valued additive arithmetic function into an `AddMonoidWithOne` preserves
additivity. -/
theorem natCast [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} (hf : f.IsAdditive) :
    (f : ArithmeticFunction R).IsAdditive :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ rfl

/-- Coercing a `ℤ`-valued additive arithmetic function into an `AddGroupWithOne` preserves
additivity. -/
theorem intCast [AddGroupWithOne R] {f : ArithmeticFunction ℤ} (hf : f.IsAdditive) :
    (f : ArithmeticFunction R).IsAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ rfl

section AddCommMonoid

variable [AddCommMonoid R] {f g : ArithmeticFunction R}

/-- The pointwise sum of two additive arithmetic functions is additive. -/
theorem add (hf : f.IsAdditive) (hg : g.IsAdditive) : (f + g).IsAdditive :=
  ⟨by simp [hf.map_one, hg.map_one], fun hm hn hmn ↦ by
    simp only [add_apply, hf.map_mul hm hn hmn, hg.map_mul hm hn hmn]
    exact add_add_add_comm _ _ _ _⟩

open scoped Function in
/-- An additive function converts the product of a pairwise coprime finite family into the sum of
its values. -/
theorem map_prod {ι : Type*} (g : ι → ℕ) (hf : f.IsAdditive) (s : Finset ι)
    (hs : (s : Set ι).Pairwise (Nat.Coprime on g)) :
    f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf.map_one]
  | insert a s has ih =>
    rw [coe_insert, Set.pairwise_insert_of_symm] at hs
    rw [prod_insert has, sum_insert has, hf.map_mul_of_coprime, ih hs.1]
    exact Nat.Coprime.prod_right fun i hi ↦ hs.2 i hi (ne_of_mem_of_not_mem hi has).symm

/-- An additive function converts a product of distinct primes into the sum of its values at those
primes. -/
theorem map_prod_of_prime (hf : f.IsAdditive) (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    f (∏ p ∈ t, p) = ∑ p ∈ t, f p :=
  hf.map_prod id t fun _ hx _ hy hxy ↦ (Nat.coprime_primes (ht _ hx) (ht _ hy)).mpr hxy

/-- An additive function converts a product over any subset of `n.primeFactors` into the sum of its
values. -/
theorem map_prod_of_subset_primeFactors (hf : f.IsAdditive) (n : ℕ) (t : Finset ℕ)
    (ht : t ⊆ n.primeFactors) : f (∏ p ∈ t, p) = ∑ p ∈ t, f p :=
  hf.map_prod_of_prime t fun _ hp ↦ Nat.prime_of_mem_primeFactors (ht hp)

/-- On a squarefree natural number `n`, an additive function sums over `n.primeFactors` (note that
`Squarefree 0` is false and `Squarefree 1` gives the empty sum `f 1 = 0`). -/
theorem sum_primeFactors_of_squarefree (hf : f.IsAdditive) {n : ℕ} (hn : Squarefree n) :
    f n = ∑ p ∈ n.primeFactors, f p := by
  rw [← hf.map_prod_of_subset_primeFactors n n.primeFactors Subset.rfl,
    Nat.prod_primeFactors_of_squarefree hn]

/-- **Prime-power representation of an additive arithmetic function.** For every `n : ℕ` (including
`0` and `1`), `f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p)`. -/
theorem sum_primeFactors_pow_factorization (hf : f.IsAdditive) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, f (p ^ n.factorization p) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmult := Nat.multiplicative_factorization (fun m ↦ Multiplicative.ofAdd (f m))
    (fun _ _ hmn ↦ by simp [hf.map_mul_of_coprime hmn]) (by simp [hf.map_one]) hn
  simpa [Finsupp.prod, Nat.support_factorization] using congrArg Multiplicative.toAdd hmult

/-- Two additive arithmetic functions are equal if and only if they agree at every prime power
`p ^ k` with `p` prime and `k ≠ 0`. -/
theorem eq_iff_eq_on_prime_powers (hf : f.IsAdditive) (hg : g.IsAdditive) :
    f = g ↔ ∀ p k : ℕ, p.Prime → k ≠ 0 → f (p ^ k) = g (p ^ k) := by
  refine ⟨fun h _ _ _ _ ↦ h ▸ rfl, fun h ↦ ext fun n ↦ ?_⟩
  rw [hf.sum_primeFactors_pow_factorization, hg.sum_primeFactors_pow_factorization]
  refine sum_congr rfl fun p hp ↦ h p (n.factorization p) (Nat.prime_of_mem_primeFactors hp) ?_
  exact Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp)

/-- Additive counterpart of `ArithmeticFunction.IsMultiplicative.lcm_apply_mul_gcd_apply`: for
every `x, y : ℕ`, `f (x.lcm y) + f (x.gcd y) = f x + f y`. -/
theorem lcm_apply_add_gcd_apply (hf : f.IsAdditive) (x y : ℕ) :
    f (x.lcm y) + f (x.gcd y) = f x + f y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hzero : ∀ p : ℕ, f (p ^ 0) = 0 := fun p ↦ by rw [pow_zero, hf.map_one]
  set s := x.primeFactors ∪ y.primeFactors
  have hexpand : ∀ {m : ℕ}, (∀ p ∈ m.primeFactors, p ∈ s) →
      f m = ∑ p ∈ s, f (p ^ m.factorization p) := fun {m} hsub ↦ by
    rw [hf.sum_primeFactors_pow_factorization]
    exact sum_subset hsub fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp (Nat.support_factorization m ▸ hp), hzero]
  rw [hexpand (by simp [s, Nat.factorization_lcm hx hy, ← Nat.support_factorization]),
    hexpand (fun p hp ↦ mem_union_left _
      (Nat.primeFactors_mono (Nat.gcd_dvd_left x y) hx hp)),
    hexpand (fun _ hp ↦ mem_union_left _ hp),
    hexpand (fun _ hp ↦ mem_union_right _ hp),
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun p _ ↦ ?_
  rcases le_total (x.factorization p) (y.factorization p) with h | h <;>
    simp [Nat.factorization_lcm hx hy, Nat.factorization_gcd hx hy, h, add_comm]

end AddCommMonoid

/-- Additive counterpart of `ArithmeticFunction.IsMultiplicative.map_div_of_coprime`: if `d ∣ m`
and `m / d` is coprime to `d`, then `f (m / d) = f m - f d`. -/
theorem map_div_of_coprime [AddGroup R] {f : ArithmeticFunction R} (hf : f.IsAdditive)
    {m d : ℕ} (hdm : d ∣ m) (hc : (m / d).Coprime d) : f (m / d) = f m - f d :=
  eq_sub_of_add_eq <| by rw [← hf.map_mul_of_coprime hc, Nat.div_mul_cancel hdm]

section SubtractionCommMonoid

variable [SubtractionCommMonoid R] {f g : ArithmeticFunction R}

/-- Pointwise negation preserves additivity. -/
theorem neg (hf : f.IsAdditive) : (-f).IsAdditive :=
  ⟨by simp [hf.map_one], fun hm hn hmn ↦ by
    simp only [neg_apply, hf.map_mul hm hn hmn, neg_add_rev, add_comm]⟩

/-- Pointwise subtraction preserves additivity. -/
theorem sub (hf : f.IsAdditive) (hg : g.IsAdditive) : (f - g).IsAdditive :=
  ⟨by simp [hf.map_one, hg.map_one], fun hm hn hmn ↦ by
    simp only [sub_apply, hf.map_mul hm hn hmn, hg.map_mul hm hn hmn]
    exact (sub_add_sub_comm _ _ _ _).symm⟩

end SubtractionCommMonoid

end IsAdditive

/-- The zero arithmetic function is additive. -/
@[simp]
theorem isAdditive_zero [AddZeroClass R] : (0 : ArithmeticFunction R).IsAdditive :=
  ⟨by simp, fun _ _ _ ↦ by simp⟩

/-- A finite pointwise sum of additive arithmetic functions is additive. -/
theorem isAdditive_sum [AddCommMonoid R] {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction R)
    (hf : ∀ i ∈ s, (f i).IsAdditive) : (∑ i ∈ s, f i).IsAdditive := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [sum_insert has]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi ↦ hf i (mem_insert_of_mem hi))

/-! ### Strongly additive arithmetic functions -/

/-- An arithmetic function `f` is **strongly additive** if it is additive and `f (p ^ k) = f p`
for every prime `p` and positive exponent `k`. -/
def IsStronglyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  f.IsAdditive ∧ ∀ {p k : ℕ}, p.Prime → 0 < k → f (p ^ k) = f p

/-- Unfolding characterization of `ArithmeticFunction.IsStronglyAdditive`. -/
theorem isStronglyAdditive_def [AddZeroClass R] {f : ArithmeticFunction R} :
    f.IsStronglyAdditive ↔ f.IsAdditive ∧ ∀ {p k : ℕ}, p.Prime → 0 < k → f (p ^ k) = f p :=
  Iff.rfl

namespace IsStronglyAdditive

section AddZeroClass

variable [AddZeroClass R] {f : ArithmeticFunction R}

/-- Every strongly additive arithmetic function is additive. -/
theorem isAdditive (hf : f.IsStronglyAdditive) : f.IsAdditive :=
  hf.1

/-- A strongly additive arithmetic function vanishes at `1`. -/
@[simp, grind =]
theorem map_one (hf : f.IsStronglyAdditive) : f 1 = 0 :=
  hf.isAdditive.map_one

/-- At every positive power of a prime `p`, a strongly additive function takes the value `f p`. -/
@[simp, grind =]
theorem map_prime_pow (hf : f.IsStronglyAdditive) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    f (p ^ k) = f p :=
  hf.2 hp (Nat.pos_of_ne_zero hk)

/-- Post-composing a strongly additive arithmetic function on nonzero inputs with an additive
monoid homomorphism preserves strong additivity. -/
theorem of_eq_addMonoidHom [AddZeroClass S] (hf : f.IsStronglyAdditive) (φ : R →+ S)
    {g : ArithmeticFunction S} (hg : ∀ n ≠ 0, g n = φ (f n)) : g.IsStronglyAdditive :=
  ⟨hf.isAdditive.of_eq_addMonoidHom φ hg, fun {p k} hp hk ↦ by
    rw [hg (p ^ k) (pow_ne_zero k hp.ne_zero), hg p hp.ne_zero, hf.map_prime_pow hp hk.ne']⟩

/-- Pointwise scalar multiplication by a distributive action preserves strong additivity. -/
theorem smul [DistribSMul S R] (hf : f.IsStronglyAdditive) (c : S) :
    (c • f).IsStronglyAdditive :=
  ⟨hf.isAdditive.smul c, fun hp hk ↦ by simp [hf.map_prime_pow hp hk.ne']⟩

end AddZeroClass

/-- Coercing an `ℕ`-valued strongly additive arithmetic function into an `AddMonoidWithOne`
preserves strong additivity. -/
theorem natCast [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} (hf : f.IsStronglyAdditive) :
    (f : ArithmeticFunction R).IsStronglyAdditive :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ rfl

/-- Coercing a `ℤ`-valued strongly additive arithmetic function into an `AddGroupWithOne`
preserves strong additivity. -/
theorem intCast [AddGroupWithOne R] {f : ArithmeticFunction ℤ} (hf : f.IsStronglyAdditive) :
    (f : ArithmeticFunction R).IsStronglyAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ rfl

section AddCommMonoid

variable [AddCommMonoid R] {f g : ArithmeticFunction R}

/-- The pointwise sum of two strongly additive arithmetic functions is strongly additive. -/
theorem add (hf : f.IsStronglyAdditive) (hg : g.IsStronglyAdditive) :
    (f + g).IsStronglyAdditive :=
  ⟨hf.isAdditive.add hg.isAdditive, fun hp hk ↦ by
    simp [hf.map_prime_pow hp hk.ne', hg.map_prime_pow hp hk.ne']⟩

/-- **Distinct-prime representation of a strongly additive function.** For every `n : ℕ`
(including `0` and `1`), `f n = ∑ p ∈ n.primeFactors, f p`. -/
theorem sum_primeFactors (hf : f.IsStronglyAdditive) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, f p := by
  rw [hf.isAdditive.sum_primeFactors_pow_factorization]
  refine sum_congr rfl fun p hp ↦ hf.map_prime_pow (Nat.prime_of_mem_primeFactors hp) ?_
  exact Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp)

/-- Two strongly additive arithmetic functions are equal if and only if they agree on all primes. -/
theorem eq_iff_eq_on_primes (hf : f.IsStronglyAdditive) (hg : g.IsStronglyAdditive) :
    f = g ↔ ∀ p : ℕ, p.Prime → f p = g p := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ ext fun n ↦ ?_⟩
  rw [hf.sum_primeFactors, hg.sum_primeFactors]
  exact sum_congr rfl fun p hp ↦ h p (Nat.prime_of_mem_primeFactors hp)

end AddCommMonoid

section SubtractionCommMonoid

variable [SubtractionCommMonoid R] {f g : ArithmeticFunction R}

/-- Pointwise negation preserves strong additivity. -/
theorem neg (hf : f.IsStronglyAdditive) : (-f).IsStronglyAdditive :=
  ⟨hf.isAdditive.neg, fun hp hk ↦ by simp [hf.map_prime_pow hp hk.ne']⟩

/-- Pointwise subtraction preserves strong additivity. -/
theorem sub (hf : f.IsStronglyAdditive) (hg : g.IsStronglyAdditive) :
    (f - g).IsStronglyAdditive :=
  ⟨hf.isAdditive.sub hg.isAdditive, fun hp hk ↦ by
    simp [hf.map_prime_pow hp hk.ne', hg.map_prime_pow hp hk.ne']⟩

end SubtractionCommMonoid

end IsStronglyAdditive

/-- The zero arithmetic function is strongly additive. -/
@[simp]
theorem isStronglyAdditive_zero [AddZeroClass R] :
    (0 : ArithmeticFunction R).IsStronglyAdditive :=
  ⟨isAdditive_zero, fun _ _ ↦ by simp⟩

/-- A finite pointwise sum of strongly additive arithmetic functions is strongly additive. -/
theorem isStronglyAdditive_sum [AddCommMonoid R] {ι : Type*} (s : Finset ι)
    (f : ι → ArithmeticFunction R) (hf : ∀ i ∈ s, (f i).IsStronglyAdditive) :
    (∑ i ∈ s, f i).IsStronglyAdditive := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [sum_insert has]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi ↦ hf i (mem_insert_of_mem hi))

/-- The distinct-prime-factor counting function `ω = cardDistinctFactors` is strongly additive. -/
@[simp]
theorem isStronglyAdditive_cardDistinctFactors : cardDistinctFactors.IsStronglyAdditive :=
  ⟨⟨cardDistinctFactors_one, fun _ _ hmn ↦ cardDistinctFactors_mul hmn⟩,
    fun hp hk ↦ (cardDistinctFactors_apply_prime_pow hp hk.ne').trans
      (cardDistinctFactors_apply_prime hp).symm⟩

/-- The distinct-prime-factor counting function `ω = cardDistinctFactors` is additive. -/
@[simp]
theorem isAdditive_cardDistinctFactors : cardDistinctFactors.IsAdditive :=
  isStronglyAdditive_cardDistinctFactors.isAdditive

/-! ### Completely additive arithmetic functions -/

/-- An arithmetic function `f` is **completely additive** if `f 1 = 0` and `f (m * n) = f m + f n`
for all positive natural numbers `m` and `n`. -/
def IsCompletelyAdditive [AddZeroClass R] (f : ArithmeticFunction R) : Prop :=
  f 1 = 0 ∧ ∀ {m n : ℕ}, 0 < m → 0 < n → f (m * n) = f m + f n

/-- Unfolding characterization of `ArithmeticFunction.IsCompletelyAdditive`. -/
theorem isCompletelyAdditive_def [AddZeroClass R] {f : ArithmeticFunction R} :
    f.IsCompletelyAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, 0 < m → 0 < n → f (m * n) = f m + f n :=
  Iff.rfl

/-- In a codomain with left-cancellative addition, `f (m * n) = f m + f n` on positive inputs
already forces `f 1 = 0`. -/
theorem isCompletelyAdditive_iff_of_isLeftCancelAdd [AddZeroClass R] [IsLeftCancelAdd R]
    {f : ArithmeticFunction R} :
    f.IsCompletelyAdditive ↔ ∀ {m n : ℕ}, 0 < m → 0 < n → f (m * n) = f m + f n :=
  ⟨fun hf ↦ hf.2, fun h ↦ ⟨add_left_cancel ((h zero_lt_one zero_lt_one).symm.trans
    (add_zero (f 1)).symm), h⟩⟩

namespace IsCompletelyAdditive

section AddZeroClass

variable [AddZeroClass R] {f : ArithmeticFunction R}

/-- Every completely additive arithmetic function is additive. -/
theorem isAdditive (hf : f.IsCompletelyAdditive) : f.IsAdditive :=
  ⟨hf.1, fun hm hn _ ↦ hf.2 hm hn⟩

/-- A completely additive arithmetic function vanishes at `1`. -/
@[simp, grind =]
theorem map_one (hf : f.IsCompletelyAdditive) : f 1 = 0 :=
  hf.1

/-- Complete additivity on positive factors. -/
theorem map_mul (hf : f.IsCompletelyAdditive) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    f (m * n) = f m + f n :=
  hf.2 hm hn

/-- Complete additivity on nonzero factors. -/
@[simp, grind =]
theorem map_mul_of_ne_zero (hf : f.IsCompletelyAdditive) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    f (m * n) = f m + f n :=
  hf.2 (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)

/-- Characterization of `IsCompletelyAdditive` using nonzero guards in place of positivity. -/
theorem iff_ne_zero :
    f.IsCompletelyAdditive ↔ f 1 = 0 ∧ ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → f (m * n) = f m + f n :=
  and_congr_right' <| forall₂_congr fun _ _ ↦
    ⟨fun h hm hn ↦ h (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn),
      fun h hm hn ↦ h hm.ne' hn.ne'⟩

/-- Post-composing a completely additive arithmetic function on nonzero inputs with an additive
monoid homomorphism preserves complete additivity. -/
theorem of_eq_addMonoidHom [AddZeroClass S] (hf : f.IsCompletelyAdditive) (φ : R →+ S)
    {g : ArithmeticFunction S} (hg : ∀ n ≠ 0, g n = φ (f n)) : g.IsCompletelyAdditive :=
  iff_ne_zero.mpr ⟨by rw [hg 1 one_ne_zero, hf.map_one, φ.map_zero], fun {m n} hm hn ↦ by
    rw [hg (m * n) (mul_ne_zero hm hn), hg m hm, hg n hn, hf.map_mul_of_ne_zero hm hn, map_add]⟩

/-- Pointwise scalar multiplication by a distributive action preserves complete additivity. -/
theorem smul [DistribSMul S R] (hf : f.IsCompletelyAdditive) (c : S) :
    (c • f).IsCompletelyAdditive :=
  ⟨by simp [hf.map_one], fun hm hn ↦ by simp [hf.map_mul hm hn, smul_add]⟩

end AddZeroClass

/-- Coercing an `ℕ`-valued completely additive arithmetic function into an `AddMonoidWithOne`
preserves complete additivity. -/
theorem natCast [AddMonoidWithOne R] {f : ArithmeticFunction ℕ} (hf : f.IsCompletelyAdditive) :
    (f : ArithmeticFunction R).IsCompletelyAdditive :=
  hf.of_eq_addMonoidHom (Nat.castAddMonoidHom R) fun _ _ ↦ rfl

/-- Coercing a `ℤ`-valued completely additive arithmetic function into an `AddGroupWithOne`
preserves complete additivity. -/
theorem intCast [AddGroupWithOne R] {f : ArithmeticFunction ℤ} (hf : f.IsCompletelyAdditive) :
    (f : ArithmeticFunction R).IsCompletelyAdditive :=
  hf.of_eq_addMonoidHom (Int.castAddHom R) fun _ _ ↦ rfl

/-- Power law for completely additive functions: `f (n ^ k) = k • f n` for every `n, k : ℕ`
(including `n = 0`, where both sides vanish for `k = 0` via `f 1 = 0` and for `k > 0` via
`f 0 = 0`). -/
@[simp, grind =]
theorem map_pow [AddMonoid R] {f : ArithmeticFunction R} (hf : f.IsCompletelyAdditive)
    (n k : ℕ) : f (n ^ k) = k • f n := by
  rcases eq_or_ne n 0 with rfl | hn
  · cases k <;> simp [hf.map_one]
  induction k with
  | zero => simp [hf.map_one]
  | succ k ih => rw [pow_succ, hf.map_mul_of_ne_zero (pow_ne_zero k hn) hn, ih, succ_nsmul]

section AddCommMonoid

variable [AddCommMonoid R] {f g : ArithmeticFunction R}

/-- The pointwise sum of two completely additive arithmetic functions is completely additive. -/
theorem add (hf : f.IsCompletelyAdditive) (hg : g.IsCompletelyAdditive) :
    (f + g).IsCompletelyAdditive :=
  ⟨by simp [hf.map_one, hg.map_one], fun hm hn ↦ by
    simp only [add_apply, hf.map_mul hm hn, hg.map_mul hm hn]
    exact add_add_add_comm _ _ _ _⟩

/-- A completely additive function converts any finite product of nonzero naturals into the sum of
its values. -/
theorem map_prod {ι : Type*} (g : ι → ℕ) (hf : f.IsCompletelyAdditive) (s : Finset ι)
    (hs : ∀ i ∈ s, g i ≠ 0) : f (∏ i ∈ s, g i) = ∑ i ∈ s, f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf.map_one]
  | insert a s has ih =>
    have ha : g a ≠ 0 := hs a (mem_insert_self a s)
    have hs' : ∀ i ∈ s, g i ≠ 0 := fun i hi ↦ hs i (mem_insert_of_mem hi)
    rw [prod_insert has, sum_insert has, hf.map_mul_of_ne_zero ha (prod_ne_zero_iff.mpr hs'),
      ih hs']

/-- **Factorization formula for a completely additive function.** For every `n : ℕ` (including `0`
and `1`), `f n = ∑ p ∈ n.primeFactors, n.factorization p • f p`. -/
theorem sum_primeFactors (hf : f.IsCompletelyAdditive) (n : ℕ) :
    f n = ∑ p ∈ n.primeFactors, n.factorization p • f p := by
  rw [hf.isAdditive.sum_primeFactors_pow_factorization]
  exact sum_congr rfl fun p _ ↦ hf.map_pow p (n.factorization p)

/-- Two completely additive arithmetic functions are equal if and only if they agree on all
primes. -/
theorem eq_iff_eq_on_primes (hf : f.IsCompletelyAdditive) (hg : g.IsCompletelyAdditive) :
    f = g ↔ ∀ p : ℕ, p.Prime → f p = g p := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ ext fun n ↦ ?_⟩
  rw [hf.sum_primeFactors, hg.sum_primeFactors]
  exact sum_congr rfl fun p hp ↦ by rw [h p (Nat.prime_of_mem_primeFactors hp)]

end AddCommMonoid

/-- For a completely additive function taking values in an additive group, `f (m / d) = f m - f d`
whenever `d ∣ m` and `m ≠ 0` (at `m = 0`, `f (0 / 2) = 0` whereas `f 0 - f 2 = -f 2`). -/
theorem map_div [AddGroup R] {f : ArithmeticFunction R} (hf : f.IsCompletelyAdditive)
    {m d : ℕ} (hdm : d ∣ m) (hm : m ≠ 0) : f (m / d) = f m - f d := by
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero hm hdm
  have hmd : m / d ≠ 0 := fun h ↦ hm (by rw [← Nat.div_mul_cancel hdm, h, zero_mul])
  exact eq_sub_of_add_eq <| by rw [← hf.map_mul_of_ne_zero hmd hd, Nat.div_mul_cancel hdm]

section SubtractionCommMonoid

variable [SubtractionCommMonoid R] {f g : ArithmeticFunction R}

/-- Pointwise negation preserves complete additivity. -/
theorem neg (hf : f.IsCompletelyAdditive) : (-f).IsCompletelyAdditive :=
  ⟨by simp [hf.map_one], fun hm hn ↦ by
    simp only [neg_apply, hf.map_mul hm hn, neg_add_rev, add_comm]⟩

/-- Pointwise subtraction preserves complete additivity. -/
theorem sub (hf : f.IsCompletelyAdditive) (hg : g.IsCompletelyAdditive) :
    (f - g).IsCompletelyAdditive :=
  ⟨by simp [hf.map_one, hg.map_one], fun hm hn ↦ by
    simp only [sub_apply, hf.map_mul hm hn, hg.map_mul hm hn]
    exact (sub_add_sub_comm _ _ _ _).symm⟩

end SubtractionCommMonoid

end IsCompletelyAdditive

/-- The zero arithmetic function is completely additive. -/
@[simp]
theorem isCompletelyAdditive_zero [AddZeroClass R] :
    (0 : ArithmeticFunction R).IsCompletelyAdditive :=
  ⟨by simp, fun _ _ ↦ by simp⟩

/-- A finite pointwise sum of completely additive arithmetic functions is completely additive. -/
theorem isCompletelyAdditive_sum [AddCommMonoid R] {ι : Type*} (s : Finset ι)
    (f : ι → ArithmeticFunction R) (hf : ∀ i ∈ s, (f i).IsCompletelyAdditive) :
    (∑ i ∈ s, f i).IsCompletelyAdditive := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [sum_insert has]
    exact (hf a (mem_insert_self a s)).add (ih fun i hi ↦ hf i (mem_insert_of_mem hi))

/-- The total-prime-factor counting function `Ω = cardFactors` is completely additive. -/
@[simp]
theorem isCompletelyAdditive_cardFactors : cardFactors.IsCompletelyAdditive :=
  ⟨cardFactors_one, fun hm hn ↦ cardFactors_mul hm.ne' hn.ne'⟩

/-- The total-prime-factor counting function `Ω = cardFactors` is additive. -/
@[simp]
theorem isAdditive_cardFactors : cardFactors.IsAdditive :=
  isCompletelyAdditive_cardFactors.isAdditive

end ArithmeticFunction
