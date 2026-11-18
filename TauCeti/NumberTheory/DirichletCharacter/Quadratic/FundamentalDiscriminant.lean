/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LocalFactor
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
public import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminants
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.OddPrimePower.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# Quadratic Dirichlet characters and fundamental discriminants

A primitive quadratic Dirichlet character `χ` of level `N ≠ 0` is the character of a fundamental
discriminant: there is a fundamental discriminant `D` with `|D| = N` such that
`χ n = fundamentalDiscriminantCharCast R D n` at every integer `n`, the left side read modulo `N`
and the right side modulo `|D|`. When `2 ≠ 0` in the coefficient ring, `D` is `N` if `χ (-1) = 1`
and `-N` otherwise. The principal character is included: it is primitive only at level `1`, where
`D = 1`.

More generally, every quadratic Dirichlet character `χ` of any nonzero level `N` (primitive or not)
corresponds to a unique fundamental discriminant `D` with `|D| = χ.conductor` such that
`χ n = fundamentalDiscriminantCharCast R D n` at every integer `n` coprime to `N`, namely
`D = χ (-1) · χ.conductor` (`χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise). Passing
to `χ.primitiveCharacter` reduces existence to the primitive case when `2 ≠ 0`, while when `2 = 0`
every quadratic character is principal and `D = 1`. Uniqueness comes from `χ (-1) = D.sign` when
`2 ≠ 0` and from `D.natAbs = 1 ↔ D = 1` when `2 = 0`. Equivalently, `D = fundamentalDiscriminant d`
for a unique squarefree radicand `d` (`D` when `D ≡ 1 (mod 4)` and `D / 4` otherwise).

At every odd prime `p ∤ N`, the character value is `χ p = legendreSym p D = legendreSym p d` (cast
to `R`); when `2 ≠ 0` in `R`, `χ p = -1` holds exactly when `D` (equivalently `d`) is not a square
modulo `p`.

The proof of the primitive case is local. At a prime power `p ^ k`, `k ≠ 0`, a primitive quadratic
character is the Legendre character modulo `p` (so `k = 1`) when `p` is odd, and `χ₄`, `χ₈` or
`χ₈'` (so `k = 2` or `k = 3`) when `p = 2`; in each case it is the character of a prime
discriminant `p*`, `-4`, `8` or `-8` of absolute value `p ^ k`. The local factors of a primitive
character are primitive, and the character of a product of prime discriminants at distinct primes
is the product of their characters, so `D` is the product of the prime discriminants of the local
factors.

The results hold for characters with values in any commutative ring (requiring `2 ≠ 0` only where
`-1 ≠ 1` is needed to separate nonsquares from squares).

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of absolute
  value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a fundamental discriminant of absolute
  value `N`.
* `DirichletCharacter.IsPrimitive.isFundamentalDiscr_ite`,
  `DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite`: when `2 ≠ 0`,
  that fundamental discriminant is `χ (-1) N`.
* `DirichletCharacter.isFundamentalDiscr_ite_conductor`,
  `DirichletCharacter.apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime`,
  `DirichletCharacter.eq_ite_conductor_of_forall_isCoprime`: at any nonzero level `N` and over any
  commutative ring, the unique fundamental discriminant of a quadratic character `χ` is
  `χ (-1) · χ.conductor`.
* `DirichletCharacter.existsUnique_isFundamentalDiscr`: existence and uniqueness of the primitive
  fundamental discriminant of a quadratic character of any nonzero level `N`.
* `DirichletCharacter.existsUnique_squarefree_fundamentalDiscriminant`: the equivalent squarefree
  radicand form.
* `DirichletCharacter.apply_natCast_eq_legendreSym_of_forall_isCoprime`,
  `DirichletCharacter.apply_natCast_eq_legendreSym_ite_conductor`,
  `DirichletCharacter.apply_natCast_eq_neg_one_iff_not_isSquare`: odd-prime Legendre symbol values
  and the characterization of `χ p = -1` by `¬ IsSquare (D : ZMod p)`.

## References

H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
Cambridge University Press, 2007, §9.3, pp. 295–297 (Theorem 9.13).
-/

public section

open TauCeti.Multiquadratic

namespace DirichletCharacter

variable {R : Type*} [CommRing R]

/-- A character of level `p ^ k` that is primitive and the lift of an integer-valued character
`ψ₀` of level `d`, where `ψ₀` agrees with the character of a prime discriminant `P` of absolute
value `d`, is the character of `P`, and `d = p ^ k`. -/
private theorem exists_isPrimeDiscriminant_apply_eq_of_eq_changeLevel {p k d : ℕ}
    [NeZero (p ^ k)] {ψ : DirichletCharacter R (p ^ k)} (hψ : ψ.IsPrimitive) {hd : d ∣ p ^ k}
    {ψ₀ : DirichletCharacter ℤ d} (h : ψ = changeLevel hd (ψ₀.ringHomComp (Int.castRingHom R)))
    {P : ℤ} (hP : IsPrimeDiscriminant P) (hPd : P.natAbs = d)
    (hval : ∀ n : ℤ, fundamentalDiscriminantChar P hP.isFundamentalDiscr n = ψ₀ n) :
    ∃ (P : ℤ) (hP : IsPrimeDiscriminant P), P.natAbs = p ^ k ∧
      ∀ n : ℤ, ψ n = fundamentalDiscriminantCharCast R P hP.isFundamentalDiscr n := by
  subst h
  -- the level `p ^ k` is the conductor, which divides the level `d` of `ψ₀`
  have hdk : d = p ^ k := Nat.dvd_antisymm hd <| by
    rw [← (isPrimitive_def _).mp hψ, conductor_changeLevel]
    exact conductor_dvd_level _
  refine ⟨P, hP, hPd.trans hdk, apply_intCast_eq_of_forall_isCoprime (hPd.trans hdk).symm
    fun n hn ↦ ?_⟩
  rw [changeLevel_ringHomComp_intCast_apply hd ψ₀ hn, fundamentalDiscriminantCharCast_apply,
    hval]

/-- **The primitive quadratic characters of prime-power level.** A primitive quadratic character
of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant `P` with `|P| = p ^ k`: the
Legendre character, with `P = p*` and `k = 1`, when `p` is odd, and `χ₄`, `χ₈` or `χ₈'`, with
`P = -4`, `8` or `-8`, when `p = 2`. -/
theorem IsPrimitive.exists_isPrimeDiscriminant_apply_eq {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    {ψ : DirichletCharacter R (p ^ k)} (hψ : ψ.IsPrimitive) (hq : ψ.IsQuadratic) :
    ∃ (P : ℤ) (hP : IsPrimeDiscriminant P), P.natAbs = p ^ k ∧
      ∀ n : ℤ, ψ n = fundamentalDiscriminantCharCast R P hP.isFundamentalDiscr n := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  -- the principal character has conductor `1 ≠ p ^ k`
  have h1 : ψ ≠ 1 := by
    rintro rfl
    rw [isPrimitive_def, conductor_one, eq_comm, Nat.pow_eq_one] at hψ
    exact hψ.elim hp.one_lt.ne' hk
  rcases eq_or_ne p 2 with rfl | hp2
  · rcases (isQuadratic_iff_of_level_two_pow ψ).mp hq with h | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · exact absurd h h1
    · exact exists_isPrimeDiscriminant_apply_eq_of_eq_changeLevel hψ h isPrimeDiscriminant_neg_four
        rfl fundamentalDiscriminantChar_neg_four
    · exact exists_isPrimeDiscriminant_apply_eq_of_eq_changeLevel hψ h isPrimeDiscriminant_eight
        rfl fundamentalDiscriminantChar_eight
    · exact exists_isPrimeDiscriminant_apply_eq_of_eq_changeLevel hψ h
        isPrimeDiscriminant_neg_eight rfl fundamentalDiscriminantChar_neg_eight
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨_, h⟩ :=
      ((isQuadratic_iff_eq_one_or_eq_changeLevel_quadraticChar hp2 k ψ).mp hq).resolve_left h1
    exact exists_isPrimeDiscriminant_apply_eq_of_eq_changeLevel hψ h
      (isPrimeDiscriminant_oddPrimeDiscriminant hp (hp.odd_of_ne_two hp2))
      (oddPrimeDiscriminant_natAbs p) fun n ↦ by
        rw [fundamentalDiscriminantChar_oddPrimeDiscriminant (hp.odd_of_ne_two hp2), legendreSym]

/-- **Primitive quadratic characters are Kronecker characters.** A primitive quadratic character
`χ` of level `N ≠ 0` is the character of a fundamental discriminant `D` with `|D| = N`:
`χ n = fundamentalDiscriminantCharCast R D n` at every integer `n` (Montgomery–Vaughan,
Theorem 9.13). The discriminant `D` is the product of the prime discriminants of the local factors
of `χ`. -/
theorem IsPrimitive.exists_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D.natAbs = N ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  have hk {p : ℕ} (hp : p ∈ N.primeFactors) : N.factorization p ≠ 0 :=
    Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])
  -- the local factor at each prime `p ∣ N` is the character of a prime discriminant `P p`
  have hloc (p : ℕ) : ∃ P : ℤ, p ∈ N.primeFactors → ∃ hP : IsPrimeDiscriminant P,
      P.natAbs = ordProj[p] N ∧ ∀ n : ℤ,
        localFactor p χ n = fundamentalDiscriminantCharCast R P hP.isFundamentalDiscr n := by
    by_cases hp : p ∈ N.primeFactors
    · obtain ⟨P, hP⟩ := (isPrimitive_localFactor hχ p).exists_isPrimeDiscriminant_apply_eq
        (Nat.prime_of_mem_primeFactors hp) (hk hp) (hq.localFactor p)
      exact ⟨P, fun _ ↦ hP⟩
    · exact ⟨0, fun h ↦ absurd h hp⟩
  choose P hP using hloc
  have hPN {p : ℕ} (hp : p ∈ N.primeFactors) : (P p).natAbs = ordProj[p] N := (hP p hp).2.1
  -- the prime discriminants at distinct primes are coprime, hence distinct
  have hcop : ∀ p ∈ N.primeFactors, ∀ p' ∈ N.primeFactors, p ≠ p' → IsCoprime (P p) (P p') :=
    fun p hp p' hp' hne ↦ Int.isCoprime_iff_nat_coprime.mpr <| by
      rw [hPN hp, hPN hp']
      exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hp') hne
  have hinj : Set.InjOn P N.primeFactors := fun p hp p' hp' h ↦ by
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h' := congrArg Int.natAbs h
    rw [hPN hp, hPN hp'] at h'
    exact (Nat.prime_dvd_prime_iff_eq hpp (Nat.prime_of_mem_primeFactors hp')).mp
      (hpp.dvd_of_dvd_pow (h' ▸ dvd_pow_self p (hk hp)))
  have hD := isFundamentalDiscr_prod_of_pairwise_isCoprime (fun p hp ↦ (hP p hp).1) hcop
  have hDN : (∏ p ∈ N.primeFactors, P p).natAbs = N := by
    rw [Int.natAbs_prod, Finset.prod_congr rfl fun p hp ↦ hPN hp,
      ← Nat.prod_primeFactors_pow_factorization (NeZero.ne N)]
  refine ⟨_, hD, hDN, apply_intCast_eq_of_forall_isCoprime hDN.symm fun n hn ↦ ?_⟩
  -- at an integer prime to `N`, evaluate the product of the lifted local factors
  have hu : (n : ZMod N) = ZMod.unitOfIsCoprime n hn := (ZMod.coe_unitOfIsCoprime n hn).symm
  have hval (ψ : DirichletCharacter R N) (u : (ZMod N)ˣ) :
      ψ u = (MulChar.mulEquivToUnitHom ψ u : R) := by simp
  conv_lhs => rw [← prod_changeLevel_localFactor χ, hu, hval, map_prod,
    MonoidHom.finsetProd_apply, Units.coe_prod]
  rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_apply_int hD
    (s := N.primeFactors.image P) (Finset.forall_mem_image.mpr fun p hp ↦ (hP p hp).1)
    (Finset.prod_image hinj), genusCharFun_def, Finset.prod_image hinj, Int.cast_prod]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  rw [← hval, ← hu, changeLevel_eq_cast_of_dvd' _ _ hn, (hP p hp).2.2,
    fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_apply_primeDiscriminant (hP p hp).1]

section Sign

variable [DecidableEq R] [NeZero (2 : R)] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- When `2 ≠ 0`, the fundamental discriminant of a primitive quadratic character `χ` of level `N`
is `N` if `χ (-1) = 1` and `-N` otherwise, its sign being `χ (-1)`. -/
private theorem IsPrimitive.exists_eq_ite_apply_eq (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D = (if χ (-1) = 1 then (N : ℤ) else -N) ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  have hsign : χ (-1) = D.sign := by
    simpa [fundamentalDiscriminantChar_neg_one] using hval (-1)
  refine ⟨D, hD, ?_, hval⟩
  split_ifs with h1 <;> rw [hsign] at h1 <;> rcases hD.ne_zero.lt_or_gt with h | h
  · rw [Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero,
      one_add_one_eq_two] at h1
    exact absurd h1 two_ne_zero
  · omega
  · omega
  · rw [Int.sign_eq_one_of_pos h, Int.cast_one] at h1
    exact absurd rfl h1

/-- When `2 ≠ 0`, the integer `χ (-1) N`, that is `N` if `χ (-1) = 1` and `-N` otherwise, is a
fundamental discriminant for every primitive quadratic character `χ` of level `N`. -/
theorem IsPrimitive.isFundamentalDiscr_ite (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (N : ℤ) else -N) := by
  obtain ⟨D, hD, rfl, -⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hD

/-- **Primitive quadratic characters are Kronecker characters, with their discriminant.** When
`2 ≠ 0`, a primitive quadratic character `χ` of level `N` is the character of the fundamental
discriminant `D = χ (-1) N`: `χ n = fundamentalDiscriminantCharCast R D n` at every integer `n`.
For the principal character, primitive only at level `1`, this is `D = 1`. -/
theorem IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ n = fundamentalDiscriminantCharCast R _ (hχ.isFundamentalDiscr_ite hq) n := by
  obtain ⟨D, hD, rfl, hval⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hval n

end Sign

section ArbitraryLevel

/-- For a quadratic Dirichlet character `χ` of any nonzero level `N`, the integer
`χ (-1) · χ.conductor` — that is, `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise —
is a fundamental discriminant. This holds over any commutative ring, including rings with `2 = 0`
where every quadratic character is principal and the discriminant is `1`. -/
theorem isFundamentalDiscr_ite_conductor [DecidableEq R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hχ : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) := by
  by_cases h2 : (2 : R) = 0
  · obtain rfl : χ = 1 := hχ.eq_one_of_two_eq_zero h2
    simp [conductor_one, MulChar.one_apply isUnit_one.neg]
  · have : NeZero (2 : R) := ⟨h2⟩
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    simpa [primitiveCharacter_apply_neg_one] using
      χ.primitiveCharacter_isPrimitive.isFundamentalDiscr_ite hχ.primitiveCharacter

/-- **Quadratic characters are lifts of Kronecker characters.** At every integer `n` coprime to
the level `N ≠ 0`, a quadratic Dirichlet character `χ` agrees with the `R`-realization of the
character of the fundamental discriminant `D = χ (-1) · χ.conductor` (Montgomery–Vaughan,
Theorem 9.13). -/
theorem apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime [DecidableEq R]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (hχ : χ.IsQuadratic)
    {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ (χ.isFundamentalDiscr_ite_conductor hχ) n := by
  by_cases h2 : (2 : R) = 0
  · obtain rfl : χ = 1 := hχ.eq_one_of_two_eq_zero h2
    have hu : IsUnit (n : ZMod N) := by rwa [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm]
    rw [MulChar.one_apply hu, fundamentalDiscriminantCharCast_apply,
      fundamentalDiscriminantChar_intCast]
    simp [conductor_one, MulChar.one_apply isUnit_one.neg, TauCeti.kroneckerSym_one_left]
  · have : NeZero (2 : R) := ⟨h2⟩
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    rw [← primitiveCharacter_apply_of_isCoprime χ hn,
      χ.primitiveCharacter_isPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite
        hχ.primitiveCharacter n,
      fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantCharCast_apply,
      fundamentalDiscriminantChar_intCast, fundamentalDiscriminantChar_intCast,
      primitiveCharacter_apply_neg_one]

/-- Any fundamental discriminant `D` of absolute value `χ.conductor` whose character agrees with
`χ` at every integer coprime to `N` is necessarily `χ (-1) · χ.conductor`. -/
theorem eq_ite_conductor_of_forall_isCoprime [DecidableEq R] {N : ℕ}
    (χ : DirichletCharacter R N) {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (habs : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ) := by
  by_cases h2 : (2 : R) = 0
  · rcases eq_or_ne N 0 with rfl | hN
    · exact absurd (habs.trans (conductor_eq_zero_iff_level_eq_zero.mpr rfl))
        (Int.natAbs_ne_zero.mpr hD.ne_zero)
    · have : NeZero N := ⟨hN⟩
      have hχeq : χ = changeLevel (habs ▸ χ.conductor_dvd_level)
          (fundamentalDiscriminantCharCast R D hD) :=
        (eq_changeLevel_iff_forall_isCoprime _ χ _).mpr hval
      have hq : χ.IsQuadratic :=
        hχeq ▸ (fundamentalDiscriminantCharCast_isQuadratic hD).changeLevel _
      obtain rfl : χ = 1 := hq.eq_one_of_two_eq_zero h2
      rw [conductor_one] at habs ⊢
      simp [hD.natAbs_eq_one_iff.mp habs, MulChar.one_apply isUnit_one.neg]
  · have hsign : χ (-1) = D.sign := by
      simpa [fundamentalDiscriminantChar_neg_one] using
        hval (-1) (IsCoprime.neg_left isCoprime_one_left)
    rcases hD.ne_zero.lt_or_gt with h | h
    · have hneg : χ (-1) ≠ 1 := by
        rw [hsign, Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one]
        exact fun h1 ↦ h2 (by rw [← one_add_one_eq_two]; exact neg_eq_iff_add_eq_zero.mp h1)
      rw [ite_eq_right hneg]
      omega
    · rw [ite_eq_left (by rw [hsign, Int.sign_eq_one_of_pos h, Int.cast_one])]
      omega

/-- **The primitive discriminant of a quadratic character.** For a quadratic Dirichlet character
`χ` of any nonzero level `N` with values in any commutative ring `R`, there is a unique
fundamental discriminant `D` with `|D| = χ.conductor` such that `χ n` equals the `R`-realization
of the Kronecker character of `D` at every integer `n` coprime to `N` (Montgomery–Vaughan,
Theorem 9.13). The principal character corresponds to `D = 1`; explicitly,
`D = χ (-1) · χ.conductor`. -/
theorem existsUnique_isFundamentalDiscr {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  refine ⟨if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ),
    ⟨χ.isFundamentalDiscr_ite_conductor hχ, by simp [apply_ite Int.natAbs],
      fun n hn ↦ χ.apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime hχ hn⟩, ?_⟩
  rintro D ⟨hD, habs, hval⟩
  exact χ.eq_ite_conductor_of_forall_isCoprime hD habs hval

/-- **The squarefree radicand of a quadratic character.** Every quadratic Dirichlet character `χ`
of nonzero level `N` corresponds to a unique squarefree integer `d` such that
`D = fundamentalDiscriminant d` has `|D| = χ.conductor` and `χ` agrees with the character of `D`
at every integer coprime to `N`. -/
theorem existsUnique_squarefree_fundamentalDiscriminant {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hχ : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d, (fundamentalDiscriminant d).natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N →
        χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
          (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, habs, hval⟩, huniq⟩ := χ.existsUnique_isFundamentalDiscr hχ
  obtain ⟨d, ⟨hd, rfl⟩, -⟩ := hD.existsUnique_squarefree_fundamentalDiscriminant
  refine ⟨d, ⟨hd, habs, hval⟩, ?_⟩
  rintro d' ⟨hd', habs', hval'⟩
  exact fundamentalDiscriminant_injective
    (huniq _ ⟨isFundamentalDiscr_fundamentalDiscriminant hd', habs', hval'⟩)

/-- If `χ` agrees with the character of a fundamental discriminant `D` at all integers coprime to
`N`, then at every odd prime `p ∤ N`, `χ p` is the cast of `legendreSym p D`. -/
theorem apply_natCast_eq_legendreSym_of_forall_isCoprime {N : ℕ}
    (χ : DirichletCharacter R N) {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  have hcop : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)
  simpa [fundamentalDiscriminantCharCast_natCast_eq_legendreSym hD hp2] using hval p hcop

/-- At an odd prime `p ∤ N`, a quadratic Dirichlet character `χ` of nonzero level `N` evaluates to
the cast of the Legendre symbol of its primitive discriminant `χ (-1) · χ.conductor` modulo `p`. -/
theorem apply_natCast_eq_legendreSym_ite_conductor [DecidableEq R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hχ : χ.IsQuadratic)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) : R) :=
  χ.apply_natCast_eq_legendreSym_of_forall_isCoprime (χ.isFundamentalDiscr_ite_conductor hχ)
    (fun _ hn ↦ χ.apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime hχ hn) hp2 hpN

/-- When `2 ≠ 0` in `R`, if `χ` agrees with the character of a fundamental discriminant `D` at all
integers coprime to `N`, then at an odd prime `p ∤ N`, `χ p = -1` holds if and only if `D` is not
a square modulo `p`. Combined with `isSquare_fundamentalDiscriminant_iff`, this also gives the
nonsquare condition for the corresponding squarefree radicand `d`. -/
theorem apply_natCast_eq_neg_one_iff_not_isSquare [NeZero (2 : R)] {N : ℕ}
    (χ : DirichletCharacter R N) {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = -1 ↔ ¬ IsSquare (D : ZMod p) := by
  have hcop : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)
  have h := hval p hcop
  rw [Int.cast_natCast, Int.cast_natCast] at h
  rw [h, fundamentalDiscriminantCharCast_natCast_eq_neg_one_iff hD hp2]

end ArbitraryLevel

end DirichletCharacter

/-! ## Examples -/

section Examples

open DirichletCharacter

/-! Fundamental discriminants `1, -4, 8, -8, 5, -3, 12`, and `-12` as a non-fundamental
discriminant (`-12 = 4 · (-3)` with `-3 ≡ 1 (mod 4)`). -/

example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧ Int.IsFundamentalDiscr 8 ∧
    Int.IsFundamentalDiscr (-8) ∧ Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) := by
  have h5 : Int.IsFundamentalDiscr 5 :=
    Int.isFundamentalDiscr_iff_squarefree.mpr
      (Or.inl ⟨by norm_num, Int.squarefree_natAbs.mp Nat.prime_five.squarefree⟩)
  have h3 : Int.IsFundamentalDiscr (-3) :=
    Int.isFundamentalDiscr_iff_squarefree.mpr
      (Or.inl ⟨by norm_num, Int.squarefree_natAbs.mp Nat.prime_three.squarefree⟩)
  have h12 : Int.IsFundamentalDiscr 12 :=
    (Int.isFundamentalDiscr_four_mul (m := 3)).mpr
      ⟨Int.squarefree_natAbs.mp Nat.prime_three.squarefree, by norm_num⟩
  have hneg12 : ¬ Int.IsFundamentalDiscr (-12) := fun h ↦ by
    have := ((Int.isFundamentalDiscr_iff_squarefree.mp h).resolve_left (by omega)).2.2
    omega
  exact ⟨Int.isFundamentalDiscr_one, isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr, isPrimeDiscriminant_neg_eight.isFundamentalDiscr,
    h5, h3, h12, hneg12⟩

/-! For `χ₄` lifted to level `12`, the conductor is `4` and the unique fundamental discriminant is
`D = -4`; the lifted character vanishes at `3` while `χ_{-4}(3) = -1`, showing that agreement holds
only at integers coprime to `12`. -/

example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    χ.conductor = 4 ∧
      (∀ n : ℤ, IsCoprime n 12 →
        χ n = fundamentalDiscriminantCharCast ℂ (-4)
          isPrimeDiscriminant_neg_four.isFundamentalDiscr n) ∧
      χ 3 = 0 ∧
      fundamentalDiscriminantCharCast ℂ (-4)
        isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) = -1 := by
  intro χ
  refine ⟨by simp [χ, conductor_changeLevel, conductor_χ₄_ringHomComp], fun n hn ↦ ?_,
    MulChar.map_nonunit χ (by decide), ?_⟩
  · rw [changeLevel_ringHomComp_intCast_apply (by norm_num : 4 ∣ 12) ZMod.χ₄ hn,
      fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_four]
  · rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_four]
    simp

/-! For the principal character at level `6`, the conductor is `1` and the unique fundamental
discriminant is `D = 1`. -/

example :
    let χ : DirichletCharacter ℂ 6 := 1
    χ.conductor = 1 ∧
      (∀ n : ℤ, IsCoprime n 6 →
        χ n = fundamentalDiscriminantCharCast ℂ 1 Int.isFundamentalDiscr_one n) := by
  intro χ
  refine ⟨conductor_one, fun n hn ↦ ?_⟩
  have hu : IsUnit (n : ZMod 6) := by rwa [ZMod.isUnit_intCast_iff_isCoprime, isCoprime_comm]
  rw [MulChar.one_apply hu, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_intCast, TauCeti.kroneckerSym_one_left, Int.cast_one]

/-! At conductor `8`, `χ₈` and `χ₈'` have the same `|D| = 8` and are distinguished by their values
at `-1`, yielding `D = 8` and `D = -8`. -/

example :
    let ψ : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
    let ψ' : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)
    (if ψ (-1) = 1 then (ψ.conductor : ℤ) else -(ψ.conductor : ℤ)) = 8 ∧
      (if ψ' (-1) = 1 then (ψ'.conductor : ℤ) else -(ψ'.conductor : ℤ)) = -8 := by
  intro ψ ψ'
  have h8 : ZMod.χ₈ (-1 : ZMod 8) = 1 := by decide
  have h8' : ZMod.χ₈' (-1 : ZMod 8) = -1 := by decide
  have h1 : ψ (-1) = 1 := by simp [ψ, h8]
  have h2 : ψ' (-1) = -1 := by simp [ψ', h8']
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  simp [ψ, ψ', conductor_χ₈_ringHomComp, conductor_χ₈'_ringHomComp, h1, h2, hne]

/-! The conductor-`12` character `χ₄ · (Legendre mod 3)` has fundamental discriminant `D = 12`,
squarefree radicand `d = 3`, values `-1, -1, 1` at `5, 7, 11`, and lifting it to level `24`
preserves both its conductor and its discriminant `D = 12`. -/

example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) *
        changeLevel (by norm_num : 3 ∣ 12)
          ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ))
    let χ₂₄ : DirichletCharacter ℂ 24 := changeLevel (by norm_num : 12 ∣ 24) χ
    χ.conductor = 12 ∧ χ₂₄.conductor = 12 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = 12 ∧
      (if χ₂₄ (-1) = 1 then (χ₂₄.conductor : ℤ) else -(χ₂₄.conductor : ℤ)) = 12 ∧
      fundamentalDiscriminant 3 = 12 ∧
      χ 5 = -1 ∧ χ 7 = -1 ∧ χ 11 = 1 ∧
      (∀ n : ℤ, IsCoprime n 24 → χ₂₄ n = fundamentalDiscriminantCharCast ℂ 12
        ((Int.isFundamentalDiscr_four_mul (m := 3)).mpr
          ⟨Int.squarefree_natAbs.mp Nat.prime_three.squarefree, by norm_num⟩) n) ∧
      ¬ IsSquare (3 : ZMod 5) := by
  intro χ χ₂₄
  have h12 : Int.IsFundamentalDiscr 12 :=
    (Int.isFundamentalDiscr_four_mul (m := 3)).mpr
      ⟨Int.squarefree_natAbs.mp Nat.prime_three.squarefree, by norm_num⟩
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  have hcond : χ.conductor = 12 := by
    rw [conductor_mul_of_coprime] <;>
      simp only [conductor_changeLevel, conductor_χ₄_ringHomComp,
        conductor_changeLevel_quadraticChar hR (by norm_num : 3 ≠ 2)]
    norm_num
  have hneg : χ (-1) = 1 := by
    have h4 : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
    have h3 : quadraticChar (ZMod 3) (-1 : ZMod 3) = -1 := by decide
    simp [χ, h4, h3]
  have hval : ∀ n : ℤ, IsCoprime n 12 →
      χ n = fundamentalDiscriminantCharCast ℂ 12 h12 n := by
    intro n hn
    have hq : χ.IsQuadratic :=
      ((ZMod.isQuadratic_χ₄.comp _).changeLevel _).mul
        (((quadraticChar_isQuadratic _).comp _).changeLevel _)
    have hD : (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = 12 := by
      simp [hcond, hneg]
    rw [χ.apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime hq hn,
      fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantCharCast_apply,
      fundamentalDiscriminantChar_intCast, fundamentalDiscriminantChar_intCast, hD]
  have h5 : χ 5 = -1 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h := χ.apply_natCast_eq_legendreSym_of_forall_isCoprime (p := 5) h12 hval
      (by decide) (by decide)
    norm_num at h
    exact h
  have h7 : χ 7 = -1 := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have h := χ.apply_natCast_eq_legendreSym_of_forall_isCoprime (p := 7) h12 hval
      (by decide) (by decide)
    norm_num at h
    exact h
  have h11 : χ 11 = 1 := by
    have : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    have h := χ.apply_natCast_eq_legendreSym_of_forall_isCoprime (p := 11) h12 hval
      (by decide) (by decide)
    norm_num at h
    exact h
  have hfd3 : fundamentalDiscriminant 3 = 12 := by norm_num [fundamentalDiscriminant_def]
  have hns : ¬ IsSquare (3 : ZMod 5) := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hns12 : ¬ IsSquare ((12 : ℤ) : ZMod 5) :=
      (χ.apply_natCast_eq_neg_one_iff_not_isSquare (p := 5) h12 hval
        (by decide) (by decide)).mp h5
    rw [← hfd3] at hns12
    simpa using (isSquare_fundamentalDiscriminant_iff 3 (p := 5) (by decide)).not.mp hns12
  refine ⟨hcond, by rw [conductor_changeLevel, hcond], by simp [hcond, hneg],
    by simp [χ₂₄, conductor_changeLevel, hcond, hneg], hfd3,
    h5, h7, h11, (forall_isCoprime_changeLevel_apply_eq_iff (by norm_num : (12 : ℤ).natAbs ∣ 12)
      (by norm_num : 12 ∣ 24) χ (fundamentalDiscriminantCharCast ℂ 12 h12)).mpr hval, hns⟩

/-! Odd-prime dictionary checks: `D = 12` has radicand `d = 3`, with
`legendreSym 5 12 = legendreSym 5 3 = -1` and `legendreSym 3 12 = legendreSym 3 3 = 0`; `D = -4`
has radicand `d = -1`; and the prime `2` is excluded since `χ_5(2) = -1 ≠ 1 = legendreSym 2 5`. -/

example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h5 : Int.IsFundamentalDiscr 5 :=
      Int.isFundamentalDiscr_iff_squarefree.mpr
        (Or.inl ⟨by norm_num, Int.squarefree_natAbs.mp Nat.prime_five.squarefree⟩)
    legendreSym 5 12 = -1 ∧ legendreSym 5 3 = -1 ∧
      legendreSym 3 12 = 0 ∧ legendreSym 3 3 = 0 ∧
      fundamentalDiscriminant (-1) = -4 ∧
      fundamentalDiscriminantChar 5 h5 2 = -1 ∧ legendreSym 2 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  intro h5
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num [fundamentalDiscriminant_def], ?_, by norm_num⟩
  rw [fundamentalDiscriminantChar_two]
  decide

end Examples
