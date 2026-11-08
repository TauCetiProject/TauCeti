/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.Data.PNat.Prime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Supernatural numbers

A supernatural number, also called a Steinitz number, is a formal product
`\prod_p p ^ n_p`, where `p` ranges over the rational primes and every exponent `n_p` is an
extended natural number.  This file realizes supernatural numbers as exponent functions and
equips them with the arithmetic used for orders and indices of profinite groups.

Multiplication adds exponents, divisibility is pointwise comparison, and gcd and lcm are the
lattice infimum and supremum.  Positive natural numbers embed by their prime factorizations.
The finite supernatural numbers are characterized as those with finite support and no infinite
exponent.

## Main definitions

* `Supernatural`: supernatural numbers as prime-indexed extended-natural exponent functions.
* `Supernatural.ofFun`: the supernatural number with prescribed exponent at each prime.
* `Supernatural.ofNat`: the supernatural number attached to a positive natural number.
* `Supernatural.primePower`: the supernatural prime power `p ^ n`, including `p ^ infinity`.
* `Supernatural.primaryPart`: the `p`-primary part of a supernatural number.
* `Supernatural.primeToPart`: the prime-to-`p` part of a supernatural number.
* `Supernatural.IsNatural`: the predicate that a supernatural number comes from `ofNat`.

## References

The definitions and terminology follow Ribes--Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

/-- A supernatural number is a formal product of rational primes with exponents in `\mathbb{N}_∞`.

This is a separate type, rather than an abbreviation for a function type, because multiplication
of supernatural numbers is pointwise addition of exponents, not the pointwise multiplication a
function type carries.  As for Mathlib's `Matrix`, the body of the synonym is exposed, since the
operations are pointwise operations of the underlying function type and can only be defined, and
their pointwise characterizations only stated, with the synonym transparent.  The operations and
instances themselves are opaque and are used through the pointwise lemmas below; `ofFun` is the
named constructor building a supernatural number from its exponents. -/
@[expose]
def Supernatural := Nat.Primes → ℕ∞

namespace Supernatural

instance : CoeFun Supernatural fun _ ↦ Nat.Primes → ℕ∞ := ⟨id⟩

/-- Two supernatural numbers are equal when all of their prime exponents are equal. -/
@[ext]
theorem ext {m n : Supernatural} (h : ∀ p, m p = n p) : m = n :=
  funext h

/-- The supernatural number with prescribed exponent at each prime.

This is the named constructor for downstream definitions such as `profiniteOrder`, playing the
role that `Matrix.of` plays for `Matrix`. -/
def ofFun (f : Nat.Primes → ℕ∞) : Supernatural :=
  f

@[simp]
theorem ofFun_apply (f : Nat.Primes → ℕ∞) (p : Nat.Primes) : ofFun f p = f p :=
  (rfl)

noncomputable instance : CompleteLattice Supernatural :=
  inferInstanceAs (CompleteLattice (Nat.Primes → ℕ∞))

instance : One Supernatural := ⟨fun _ ↦ 0⟩

instance : Mul Supernatural := ⟨fun m n p ↦ m p + n p⟩

instance : CommMonoid Supernatural where
  mul_assoc m n k := by ext p; exact add_assoc (m p) (n p) (k p)
  one_mul m := by ext p; exact zero_add (m p)
  mul_one m := by ext p; exact add_zero (m p)
  mul_comm m n := by ext p; exact add_comm (m p) (n p)

/-- Every exponent of the multiplicative unit is zero. -/
@[simp]
theorem one_apply (p : Nat.Primes) : (1 : Supernatural) p = 0 :=
  rfl

@[simp]
theorem mul_apply (m n : Supernatural) (p : Nat.Primes) : (m * n) p = m p + n p :=
  rfl

/-- Raising to a natural power multiplies every exponent by that power. -/
@[simp]
theorem pow_apply (m : Supernatural) (n : ℕ) (p : Nat.Primes) : (m ^ n) p = n • m p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_apply, ih, succ_nsmul]

@[simp]
theorem inf_apply (m n : Supernatural) (p : Nat.Primes) : (m ⊓ n) p = m p ⊓ n p :=
  rfl

@[simp]
theorem sup_apply (m n : Supernatural) (p : Nat.Primes) : (m ⊔ n) p = m p ⊔ n p :=
  rfl

/-- Every exponent of the greatest supernatural number is infinite. -/
@[simp]
theorem top_apply (p : Nat.Primes) : (⊤ : Supernatural) p = ⊤ :=
  rfl

/-- Every exponent of the least supernatural number is zero. -/
@[simp]
theorem bot_apply (p : Nat.Primes) : (⊥ : Supernatural) p = 0 :=
  rfl

/-- Suprema of supernatural numbers are computed exponentwise. -/
@[simp]
theorem iSup_apply {ι : Sort*} (m : ι → Supernatural) (p : Nat.Primes) :
    (⨆ i, m i) p = ⨆ i, m i p :=
  _root_.iSup_apply

/-- Infima of supernatural numbers are computed exponentwise. -/
@[simp]
theorem iInf_apply {ι : Sort*} (m : ι → Supernatural) (p : Nat.Primes) :
    (⨅ i, m i) p = ⨅ i, m i p :=
  _root_.iInf_apply

/-- The multiplicative unit is also the least supernatural number. -/
@[simp]
theorem one_eq_bot : (1 : Supernatural) = ⊥ :=
  rfl

/-- Divisibility of supernatural numbers is comparison of every prime exponent. -/
@[simp]
theorem dvd_iff_le {m n : Supernatural} : m ∣ n ↔ m ≤ n := by
  refine ⟨?_, fun h ↦ ⟨fun p ↦ n p - m p, ext fun p ↦ (add_tsub_cancel_of_le (h p)).symm⟩⟩
  rintro ⟨k, rfl⟩ p
  exact le_self_add

/-- One supernatural number is at most another exactly when each exponent is at most the
corresponding exponent of the other. -/
theorem le_iff {m n : Supernatural} : m ≤ n ↔ ∀ p, m p ≤ n p :=
  Pi.le_def

/-- A supernatural number divides another exactly when each exponent is at most the
corresponding exponent of the other. -/
theorem dvd_iff {m n : Supernatural} : m ∣ n ↔ ∀ p, m p ≤ n p :=
  dvd_iff_le.trans le_iff

/-- The exponent of a supernatural number at a given prime. -/
def exponent (p : Nat.Primes) : Supernatural →o ℕ∞ :=
  Pi.evalOrderHom p

@[simp]
theorem exponent_apply (p : Nat.Primes) (m : Supernatural) : exponent p m = m p :=
  (rfl)

/-- The supernatural prime power `p ^ n`; all exponents away from `p` are zero. -/
def primePower (p : Nat.Primes) (n : ℕ∞) : Supernatural :=
  Pi.single p n

@[simp]
theorem primePower_apply_self (p : Nat.Primes) (n : ℕ∞) : primePower p n p = n :=
  Pi.single_eq_same (M := fun _ : Nat.Primes ↦ ℕ∞) p n

@[simp]
theorem primePower_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : ℕ∞) :
    primePower p n q = 0 :=
  Pi.single_eq_of_ne (M := fun _ : Nat.Primes ↦ ℕ∞) h n

@[simp]
theorem primePower_zero (p : Nat.Primes) : primePower p 0 = 1 :=
  Pi.single_zero p

/-- A prime power determines its exponent: `p ^ m = p ^ n` forces `m = n`. -/
theorem primePower_injective (p : Nat.Primes) : Function.Injective (primePower p) :=
  Pi.single_injective (M := fun _ : Nat.Primes ↦ ℕ∞) p

/-- A prime power with a sum of exponents is the product of the two prime powers. -/
@[simp]
theorem primePower_add (p : Nat.Primes) (m n : ℕ∞) :
    primePower p (m + n) = primePower p m * primePower p n :=
  Pi.single_add (f := fun _ : Nat.Primes ↦ ℕ∞) p m n

/-- A prime power `p ^ m` is at most a supernatural number exactly when `m` is at most its
exponent at `p`. -/
theorem primePower_le_iff (p : Nat.Primes) (m : ℕ∞) (n : Supernatural) :
    primePower p m ≤ n ↔ m ≤ n p := by
  rw [le_iff]
  refine ⟨fun h ↦ by simpa using h p, fun h q ↦ ?_⟩
  by_cases hq : q = p
  · subst q
    simpa using h
  · simp [hq]

/-- Two prime powers at the same prime compare as their exponents do. -/
@[simp]
theorem primePower_le_primePower_iff (p : Nat.Primes) {m n : ℕ∞} :
    primePower p m ≤ primePower p n ↔ m ≤ n := by
  rw [primePower_le_iff, primePower_apply_self]

/-- Two prime powers at the same prime compare strictly as their exponents do. -/
@[simp]
theorem primePower_lt_primePower_iff (p : Nat.Primes) {m n : ℕ∞} :
    primePower p m < primePower p n ↔ m < n :=
  lt_iff_lt_of_le_iff_le' (primePower_le_primePower_iff p) (primePower_le_primePower_iff p)

/-- A rational prime, regarded as the supernatural number having exponent one at that prime. -/
instance : Coe Nat.Primes Supernatural :=
  ⟨fun p ↦ primePower p 1⟩

/-- A prime is at most a supernatural number exactly when its exponent there is nonzero.

This is the simp-normal form of `coe_prime_dvd_iff`, since `dvd_iff_le` rewrites divisibility
of supernatural numbers to comparison. -/
@[simp]
theorem coe_prime_le_iff (p : Nat.Primes) (n : Supernatural) :
    (p : Supernatural) ≤ n ↔ n p ≠ 0 :=
  (primePower_le_iff p 1 n).trans Order.one_le_iff_ne_zero

/-- A prime divides a supernatural number exactly when its exponent there is nonzero. -/
theorem coe_prime_dvd_iff (p : Nat.Primes) (n : Supernatural) :
    (p : Supernatural) ∣ n ↔ n p ≠ 0 :=
  dvd_iff_le.trans (coe_prime_le_iff p n)

/-- The `p`-primary part of a supernatural number. -/
def primaryPart (p : Nat.Primes) (n : Supernatural) : Supernatural :=
  primePower p (n p)

@[simp]
theorem primaryPart_apply_self (p : Nat.Primes) (n : Supernatural) : primaryPart p n p = n p :=
  primePower_apply_self _ _

@[simp]
theorem primaryPart_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : Supernatural) :
    primaryPart p n q = 0 :=
  primePower_apply_of_ne h _

/-- The `p`-primary part of a supernatural number is trivial (equal to `⊥ = 1`) exactly when `p`
does not divide it. -/
@[simp]
theorem primaryPart_eq_bot_iff {p : Nat.Primes} {n : Supernatural} :
    primaryPart p n = ⊥ ↔ n p = 0 := by
  rw [← one_eq_bot, primaryPart, ← primePower_zero p, (primePower_injective p).eq_iff]

/-- The prime-to-`p` part of a supernatural number, obtained by deleting its `p`-exponent. -/
def primeToPart (p : Nat.Primes) (n : Supernatural) : Supernatural :=
  Function.update n p 0

@[simp]
theorem primeToPart_apply_self (p : Nat.Primes) (n : Supernatural) : primeToPart p n p = 0 :=
  Function.update_self p 0 n

@[simp]
theorem primeToPart_apply_of_ne {p q : Nat.Primes} (h : q ≠ p) (n : Supernatural) :
    primeToPart p n q = n q :=
  Function.update_of_ne h 0 n

/-- A supernatural number is the product of its `p`-primary and prime-to-`p` parts. -/
theorem primaryPart_mul_primeToPart (p : Nat.Primes) (n : Supernatural) :
    primaryPart p n * primeToPart p n = n := by
  ext q
  by_cases h : q = p
  · subst q
    simp
  · simp [h]

/-- The embedding of positive natural numbers into supernatural numbers by prime
factorization. -/
def ofNat (n : ℕ+) : Supernatural :=
  fun p ↦ (padicValNat p n : ℕ∞)

@[simp]
theorem ofNat_apply (n : ℕ+) (p : Nat.Primes) : ofNat n p = (padicValNat p n : ℕ∞) :=
  (rfl)

/-- The exponent of `p` in `ofNat n` is the multiplicity of `p` in the prime factorization
of `n`. -/
theorem ofNat_apply_eq_factorization (n : ℕ+) (p : Nat.Primes) :
    ofNat n p = ((n : ℕ).factorization p : ℕ∞) := by
  rw [ofNat_apply, Nat.factorization_def _ p.prop, Nat.padicValNat_def]

@[simp]
theorem ofNat_one : ofNat 1 = 1 := by
  ext p
  simp [ofNat_apply_eq_factorization, -ofNat_apply]

/-- The prime factorization embedding turns multiplication of positive natural numbers into
multiplication of supernatural numbers, that is, into addition of exponents. -/
@[simp]
theorem ofNat_mul (m n : ℕ+) : ofNat (m * n) = ofNat m * ofNat n := by
  ext p
  simp [ofNat_apply_eq_factorization, -ofNat_apply, Nat.factorization_mul m.ne_zero n.ne_zero]

/-- Divisibility of positive natural numbers agrees with comparison of their supernatural
images.

This is the simp-normal form of `ofNat_dvd_ofNat_iff`, since `dvd_iff_le` rewrites divisibility
of supernatural numbers to comparison. -/
@[simp]
theorem ofNat_le_ofNat_iff {m n : ℕ+} : ofNat m ≤ ofNat n ↔ m ∣ n := by
  simp only [le_iff, ofNat_apply_eq_factorization, Nat.cast_le, PNat.dvd_iff,
    ← Nat.factorization_prime_le_iff_dvd m.ne_zero n.ne_zero]
  exact ⟨fun h p hp ↦ h ⟨p, hp⟩, fun h p ↦ h p p.prop⟩

/-- Divisibility of positive natural numbers agrees with divisibility of their supernatural
images. -/
theorem ofNat_dvd_ofNat_iff {m n : ℕ+} : ofNat m ∣ ofNat n ↔ m ∣ n :=
  dvd_iff_le.trans ofNat_le_ofNat_iff

/-- Prime factorization embeds positive natural numbers injectively into supernatural numbers. -/
theorem ofNat_injective : Function.Injective ofNat := fun _ _ h ↦
  PNat.dvd_antisymm (ofNat_le_ofNat_iff.mp h.le) (ofNat_le_ofNat_iff.mp h.ge)

/-- The embedding of positive natural numbers as a multiplicative homomorphism. -/
def ofNatMonoidHom : ℕ+ →* Supernatural where
  toFun := ofNat
  map_one' := ofNat_one
  map_mul' := ofNat_mul

@[simp]
theorem ofNatMonoidHom_apply (n : ℕ+) : ofNatMonoidHom n = ofNat n :=
  (rfl)

/-- The positive-natural embedding takes gcd to the supernatural gcd. -/
@[simp]
theorem ofNat_gcd (m n : ℕ+) : ofNat (PNat.gcd m n) = ofNat m ⊓ ofNat n := by
  ext p
  rw [inf_apply, ofNat_apply_eq_factorization, ofNat_apply_eq_factorization,
    ofNat_apply_eq_factorization, PNat.gcd_coe, Nat.factorization_gcd m.ne_zero n.ne_zero]
  exact Nat.mono_cast.map_min

/-- The positive-natural embedding takes lcm to the supernatural lcm. -/
@[simp]
theorem ofNat_lcm (m n : ℕ+) : ofNat (PNat.lcm m n) = ofNat m ⊔ ofNat n := by
  ext p
  rw [sup_apply, ofNat_apply_eq_factorization, ofNat_apply_eq_factorization,
    ofNat_apply_eq_factorization, PNat.lcm_coe, Nat.factorization_lcm m.ne_zero n.ne_zero]
  exact Nat.mono_cast.map_max

/-- A supernatural number is natural when it lies in the image of `ofNat`. -/
def IsNatural (n : Supernatural) : Prop :=
  ∃ m : ℕ+, ofNat m = n

/-- A supernatural number is natural exactly when it is the image under `ofNat` of a positive
natural number.  This is `IsNatural` by definition, and is the form downstream files use, since
the body of `IsNatural` is not exposed. -/
theorem isNatural_def {n : Supernatural} : IsNatural n ↔ ∃ m : ℕ+, ofNat m = n :=
  Iff.rfl

/-- Every positive natural number gives a natural supernatural number. -/
@[simp]
theorem isNatural_ofNat (n : ℕ+) : IsNatural (ofNat n) :=
  ⟨n, rfl⟩

/-- The support of a supernatural number is the set of primes having nonzero exponent. -/
def support (n : Supernatural) : Set Nat.Primes :=
  Function.support n

@[simp]
theorem mem_support {n : Supernatural} {p : Nat.Primes} : p ∈ support n ↔ n p ≠ 0 :=
  Iff.rfl

private theorem finite_support_ofNat (n : ℕ+) : (support (ofNat n)).Finite := by
  refine ((n : ℕ).primeFactors.finite_toSet.preimage Nat.Primes.coe_nat_injective.injOn).subset
    fun (p : Nat.Primes) (hp : p ∈ support (ofNat n)) ↦ ?_
  rw [mem_support, ofNat_apply_eq_factorization, Nat.cast_ne_zero,
    ← Finsupp.mem_support_iff, Nat.support_factorization] at hp
  exact hp

/-- A supernatural number comes from a positive natural number exactly when it has finite
support and every exponent is finite. -/
theorem isNatural_iff {n : Supernatural} :
    IsNatural n ↔ (support n).Finite ∧ ∀ p, n p ≠ ⊤ := by
  refine ⟨?_, fun ⟨hsupport, hfinite⟩ ↦ ?_⟩
  · rintro ⟨m, rfl⟩
    exact ⟨finite_support_ofNat m, fun p ↦ by simp⟩
  · -- Transport the finite exponents to a prime-supported `ℕ →₀ ℕ` and invert the
    -- factorization equivalence.
    let f : Nat.Primes →₀ ℕ := Finsupp.ofSupportFinite (fun p ↦ (n p).toNat)
      (hsupport.subset fun p hp ↦ by simp_all)
    let e : Nat.Primes ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
    have hprime : ∀ q ∈ (f.embDomain e).support, q.Prime := by
      intro q hq
      rw [Finsupp.support_embDomain] at hq
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hq
      exact p.prop
    refine ⟨Nat.factorizationEquiv.symm ⟨_, hprime⟩, ext fun p ↦ ?_⟩
    have hfactorization :
        ((Nat.factorizationEquiv.symm ⟨_, hprime⟩ : ℕ+) : ℕ).factorization = f.embDomain e :=
      congrArg Subtype.val (Nat.factorizationEquiv.apply_symm_apply ⟨_, hprime⟩)
    have he : e p = p := congrFun (Function.Embedding.coeFn_mk _ _) p
    have hf : f p = (n p).toNat := congrFun Finsupp.ofSupportFinite_coe p
    rw [ofNat_apply_eq_factorization, hfactorization, ← he, Finsupp.embDomain_apply_self, hf,
      ENat.natCast_toNat (hfinite p)]

/-- A prime power with infinite exponent is not a natural supernatural number. -/
@[simp]
theorem not_isNatural_primePower_top (p : Nat.Primes) : ¬IsNatural (primePower p ⊤) := by
  rw [isNatural_iff]
  push Not
  exact fun _ ↦ ⟨p, by simp⟩

end Supernatural

end TauCeti
