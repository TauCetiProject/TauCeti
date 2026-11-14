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
`χ n = fundamentalDiscriminantCharCast R D hD n` at every integer `n`, the left side read modulo `N`
and the right side modulo `|D|`. When `2 ≠ 0` in the coefficient ring, `D` is `N` if `χ (-1) = 1`
and `-N` otherwise; when `2 = 0`, every quadratic character is principal (`N = 1`, `D = 1`).

At an arbitrary level `N ≠ 0`, passing to `χ.primitiveCharacter` attaches to every quadratic
Dirichlet character `χ` a unique fundamental discriminant `D = χ.fundamentalDiscriminant` (namely
`χ.conductor` when `χ (-1) = 1` and `-χ.conductor` otherwise) with `|D| = χ.conductor` such that
`χ n = fundamentalDiscriminantCharCast R D hD n` at every integer `n` coprime to `N`. Lifting `χ` by
`changeLevel` to a nonzero multiple of `N` preserves both its conductor and its discriminant. At an
odd natural number `n` coprime to `N`, `χ n` is the cast of `jacobiSym D n`, which coincides with
the Jacobi symbol of the squarefree radicand `fundamentalDiscriminantRadicand D` (and with
`legendreSym p D = legendreSym p (fundamentalDiscriminantRadicand D)` when `n = p` is an odd prime
not dividing `N`); in particular, when `2 ≠ 0` in `R`, a value `χ n = -1` at an odd natural number
`n` certifies that both `D` and its radicand are nonsquares modulo `n`.

The primitive step is local. At a prime power `p ^ k`, `k ≠ 0`, a primitive quadratic character is
the Legendre character modulo `p` (so `k = 1`) when `p` is odd, and `χ₄`, `χ₈` or `χ₈'` (so `k = 2`
or `k = 3`) when `p = 2`; in each case it is the character of a prime discriminant `p*`, `-4`, `8`
or `-8` of absolute value `p ^ k`. The local factors of a primitive character are primitive, and
the character of a product of prime discriminants at distinct primes is the product of their
characters, so `D` is the product of the prime discriminants of the local factors.

The results hold for characters with values in any commutative ring.

## Main definitions and results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of absolute
  value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a fundamental discriminant of absolute
  value `N`.
* `DirichletCharacter.IsPrimitive.isFundamentalDiscr_ite`,
  `DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite`: when `2 ≠ 0`,
  that fundamental discriminant is `χ (-1) N`.
* `DirichletCharacter.fundamentalDiscriminant`: the signed conductor `±χ.conductor` determined by
  `χ (-1)`, invariant under `primitiveCharacter` and under `changeLevel` to nonzero multiples.
* `MulChar.IsQuadratic.isFundamentalDiscr_fundamentalDiscriminant`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_of_isCoprime`: for quadratic `χ` at
  level `N ≠ 0`, `χ.fundamentalDiscriminant` is a fundamental discriminant whose Kronecker character
  agrees with `χ` on integers coprime to `N`.
* `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`: existence and uniqueness of the
  fundamental discriminant of a quadratic Dirichlet character at any nonzero level.
* `MulChar.IsQuadratic.apply_natCast_eq_jacobiSym_fundamentalDiscriminant`,
  `MulChar.IsQuadratic.apply_natCast_eq_jacobiSym_radicand`,
  `MulChar.IsQuadratic.apply_natCast_prime_eq_legendreSym_fundamentalDiscriminant`,
  `MulChar.IsQuadratic.apply_natCast_prime_eq_legendreSym_radicand`,
  `MulChar.IsQuadratic.not_isSquare_fundamentalDiscriminant_of_apply_eq_neg_one`,
  `MulChar.IsQuadratic.not_isSquare_radicand_of_apply_eq_neg_one`: odd-modulus Jacobi and odd-prime
  Legendre values, together with nonsquare consequences for both the discriminant and its squarefree
  radicand.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*,
  Cambridge University Press, 2007, §9.3, pp. 295–297 (Theorem 9.13).
* B. Conrad, *Quadratic characters associated to quadratic fields*, Theorem 2.4 and Corollary 3.1.
-/

public section

open TauCeti.Multiquadratic hiding fundamentalDiscriminant

namespace DirichletCharacter

section Primitive

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

end Primitive

section Discriminant

variable {R : Type*} [CommMonoidWithZero R]

/-- **The fundamental discriminant of a quadratic Dirichlet character.** For a Dirichlet character
`χ` of level `N`, this is `χ.conductor` when `χ (-1) = 1` and `-χ.conductor` otherwise. When
`N ≠ 0` and `χ` is quadratic, it is a fundamental discriminant (`Int.IsFundamentalDiscr`) whose
Kronecker character agrees with `χ` at all integers coprime to `N`; on non-quadratic characters or
at level `0` it returns the signed conductor `±χ.conductor` (for instance `0` at level `0`, or `-5`
for a primitive quartic character modulo `5` with `χ (-1) = -1`). -/
noncomputable def fundamentalDiscriminant {N : ℕ} (χ : DirichletCharacter R N) : ℤ :=
  open Classical in if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)

/-- Defining `if` expression for `DirichletCharacter.fundamentalDiscriminant`. -/
theorem fundamentalDiscriminant_def {N : ℕ} (χ : DirichletCharacter R N) :
    χ.fundamentalDiscriminant =
      open Classical in if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ) :=
  (rfl)

/-- `DirichletCharacter.fundamentalDiscriminant` written with any `DecidableEq R` instance. -/
theorem fundamentalDiscriminant_eq_ite [DecidableEq R] {N : ℕ} (χ : DirichletCharacter R N) :
    χ.fundamentalDiscriminant =
      if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ) := by
  rw [fundamentalDiscriminant_def]
  congr

/-- When `χ (-1) = 1`, `χ.fundamentalDiscriminant` is `+χ.conductor`. -/
@[simp]
theorem fundamentalDiscriminant_of_apply_neg_one_eq_one {N : ℕ} {χ : DirichletCharacter R N}
    (h : χ (-1) = 1) : χ.fundamentalDiscriminant = χ.conductor := by
  simp [fundamentalDiscriminant_def, h]

/-- When `χ (-1) ≠ 1`, `χ.fundamentalDiscriminant` is `-χ.conductor`. -/
@[simp]
theorem fundamentalDiscriminant_of_apply_neg_one_ne_one {N : ℕ} {χ : DirichletCharacter R N}
    (h : χ (-1) ≠ 1) : χ.fundamentalDiscriminant = -χ.conductor := by
  simp [fundamentalDiscriminant_def, h]

/-- The absolute value of `χ.fundamentalDiscriminant` is the conductor of `χ`. -/
@[simp]
theorem natAbs_fundamentalDiscriminant {N : ℕ} (χ : DirichletCharacter R N) :
    χ.fundamentalDiscriminant.natAbs = χ.conductor := by
  rw [fundamentalDiscriminant_def]
  split_ifs <;> simp

/-- Passing to `primitiveCharacter` preserves `fundamentalDiscriminant`. -/
@[simp]
theorem fundamentalDiscriminant_primitiveCharacter {N : ℕ} (χ : DirichletCharacter R N) :
    χ.primitiveCharacter.fundamentalDiscriminant = χ.fundamentalDiscriminant := by
  have hcond : χ.primitiveCharacter.conductor = χ.conductor :=
    (isPrimitive_def _).mp χ.primitiveCharacter_isPrimitive
  have hneg : χ.primitiveCharacter (-1) = χ (-1) := by
    simpa using χ.primitiveCharacter_apply_of_isCoprime (a := -1)
      (IsCoprime.neg_left isCoprime_one_left)
  by_cases h : χ (-1) = 1
  · rw [fundamentalDiscriminant_of_apply_neg_one_eq_one h,
      fundamentalDiscriminant_of_apply_neg_one_eq_one (hneg.trans h), hcond]
  · rw [fundamentalDiscriminant_of_apply_neg_one_ne_one h,
      fundamentalDiscriminant_of_apply_neg_one_ne_one (hneg.symm ▸ h), hcond]

/-- Lifting a character to a nonzero multiple of its level preserves `fundamentalDiscriminant`. -/
@[simp]
theorem fundamentalDiscriminant_changeLevel {N M : ℕ} [NeZero M] (h : N ∣ M)
    (χ : DirichletCharacter R N) :
    (changeLevel h χ).fundamentalDiscriminant = χ.fundamentalDiscriminant := by
  have : NeZero N := ⟨fun hN ↦ NeZero.ne M (zero_dvd_iff.mp (hN ▸ h))⟩
  rw [fundamentalDiscriminant_def, fundamentalDiscriminant_def, conductor_changeLevel,
    changeLevel_apply_neg_one]

/-- The principal character at any nonzero level has fundamental discriminant `1`. -/
@[simp]
theorem fundamentalDiscriminant_one {N : ℕ} [NeZero N] :
    (1 : DirichletCharacter R N).fundamentalDiscriminant = 1 := by
  have hu : IsUnit (-1 : ZMod N) := isUnit_one.neg
  rw [fundamentalDiscriminant_of_apply_neg_one_eq_one (MulChar.one_apply hu), conductor_one,
    Nat.cast_one]

/-- At a nonzero level, `χ.fundamentalDiscriminant = 1` holds precisely for the principal
character. -/
@[simp]
theorem fundamentalDiscriminant_eq_one_iff {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) :
    χ.fundamentalDiscriminant = 1 ↔ χ = 1 := by
  refine ⟨fun h ↦ eq_one_iff_conductor_eq_one.mpr ?_, ?_⟩
  · simpa using congrArg Int.natAbs h
  · rintro rfl
    exact fundamentalDiscriminant_one

end Discriminant

section ArbitraryLevel

variable {R : Type*} [CommRing R]

/-- **The discriminant of a quadratic Dirichlet character is a fundamental discriminant.** -/
theorem _root_.MulChar.IsQuadratic.isFundamentalDiscr_fundamentalDiscriminant {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    Int.IsFundamentalDiscr χ.fundamentalDiscriminant := by
  by_cases h2 : (2 : R) = 0
  · rw [hχ.eq_one_of_two_eq_zero h2, fundamentalDiscriminant_one]
    exact Int.isFundamentalDiscr_iff_squarefree.mpr (.inl ⟨rfl, squarefree_one⟩)
  · classical
    have : NeZero (2 : R) := ⟨h2⟩
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    rw [← fundamentalDiscriminant_primitiveCharacter, fundamentalDiscriminant_eq_ite,
      (isPrimitive_def _).mp χ.primitiveCharacter_isPrimitive]
    exact χ.primitiveCharacter_isPrimitive.isFundamentalDiscr_ite hχ.primitiveCharacter

/-- **The primitive character of a quadratic Dirichlet character is the Kronecker character of its
fundamental discriminant.** -/
theorem _root_.MulChar.IsQuadratic.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) (n : ℤ) :
    χ.primitiveCharacter n =
      fundamentalDiscriminantCharCast R χ.fundamentalDiscriminant
        hχ.isFundamentalDiscr_fundamentalDiscriminant n := by
  by_cases h2 : (2 : R) = 0
  · have h1 : χ = 1 := hχ.eq_one_of_two_eq_zero h2
    subst h1
    have : Subsingleton (ZMod (1 : DirichletCharacter R N).conductor) := by
      rw [conductor_one]
      infer_instance
    have : Subsingleton (ZMod (1 : DirichletCharacter R N).fundamentalDiscriminant.natAbs) := by
      rw [fundamentalDiscriminant_one, Int.natAbs_one]
      infer_instance
    rw [primitiveCharacter_one, MulChar.one_apply (isUnit_of_subsingleton _),
      (fundamentalDiscriminantCharCast_isQuadratic
        MulChar.isQuadratic_one.isFundamentalDiscr_fundamentalDiscriminant).eq_one_of_two_eq_zero
          h2,
      MulChar.one_apply (isUnit_of_subsingleton _)]
  · classical
    have : NeZero (2 : R) := ⟨h2⟩
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have heq : χ.fundamentalDiscriminant =
        if χ.primitiveCharacter (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
      rw [← fundamentalDiscriminant_primitiveCharacter, fundamentalDiscriminant_eq_ite,
        (isPrimitive_def _).mp χ.primitiveCharacter_isPrimitive]
    rw [χ.primitiveCharacter_isPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite
        hχ.primitiveCharacter n,
      fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast,
      fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast, heq]

/-- **Value of a quadratic Dirichlet character at an integer coprime to its level.** At every
integer `n` coprime to `N`, a quadratic character `χ` of level `N ≠ 0` agrees with the Kronecker
character of `χ.fundamentalDiscriminant`. -/
theorem _root_.MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_of_isCoprime
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {n : ℤ}
    (hn : IsCoprime n N) :
    χ n =
      fundamentalDiscriminantCharCast R χ.fundamentalDiscriminant
        hχ.isFundamentalDiscr_fundamentalDiscriminant n := by
  rw [← χ.primitiveCharacter_apply_of_isCoprime hn,
    hχ.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast]

/-- The cast of the sign of `χ.fundamentalDiscriminant` is `χ (-1)`. -/
theorem _root_.MulChar.IsQuadratic.sign_fundamentalDiscriminant {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    (χ.fundamentalDiscriminant.sign : R) = χ (-1) := by
  simpa [fundamentalDiscriminantChar_neg_one] using
    (hχ.apply_eq_fundamentalDiscriminantCharCast_of_isCoprime
      (IsCoprime.neg_left isCoprime_one_left)).symm

/-- **Uniqueness of the fundamental discriminant.** Any fundamental discriminant `D` with
`|D| = χ.conductor` whose Kronecker character agrees with `χ` on integers coprime to `N` equals
`χ.fundamentalDiscriminant`. -/
theorem eq_fundamentalDiscriminant_of_natAbs_eq {N : ℕ} {χ : DirichletCharacter R N} {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) (habs : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = χ.fundamentalDiscriminant := by
  have hsign : χ (-1) = (D.sign : R) := by
    simpa [fundamentalDiscriminantChar_neg_one] using
      hval (-1) (IsCoprime.neg_left isCoprime_one_left)
  by_cases h2 : (2 : R) = 0
  · have : NeZero N :=
      ⟨fun hN ↦ Int.natAbs_ne_zero.mpr hD.ne_zero
        (habs.trans (conductor_eq_zero_iff_level_eq_zero.mpr hN))⟩
    have hq : χ.IsQuadratic := by
      intro a
      by_cases ha : IsUnit a
      · obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
        have hn : IsCoprime n N := (ZMod.isUnit_intCast_iff_isCoprime n N).mp ha |>.symm
        rw [hval n hn]
        exact fundamentalDiscriminantCharCast_isQuadratic hD n
      · exact Or.inl (MulChar.map_nonunit χ ha)
    have h1 : χ = 1 := hq.eq_one_of_two_eq_zero h2
    subst h1
    rw [conductor_one] at habs
    rw [fundamentalDiscriminant_one]
    have hmod := hD.emod_four_eq_zero_or_one
    omega
  · rw [fundamentalDiscriminant_def]
    split_ifs with h1
    · rw [hsign] at h1
      rcases hD.ne_zero.lt_or_gt with hneg | hpos
      · rw [Int.sign_eq_neg_one_of_neg hneg, Int.cast_neg, Int.cast_one,
          neg_eq_iff_add_eq_zero, one_add_one_eq_two] at h1
        exact absurd h1 h2
      · omega
    · rcases hD.ne_zero.lt_or_gt with hneg | hpos
      · omega
      · rw [Int.sign_eq_one_of_pos hpos, Int.cast_one] at hsign
        exact absurd hsign h1

/-- **The primitive discriminant of a quadratic character.** Every quadratic Dirichlet character `χ`
of nonzero level `N` agrees, at all integers coprime to `N`, with the scalar realization of the
character of a unique fundamental discriminant `D` with `|D| = χ.conductor`, namely
`D = χ.fundamentalDiscriminant`. -/
theorem existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D,
      D.natAbs = χ.conductor ∧ ∀ n : ℤ, IsCoprime n N →
        χ n = fundamentalDiscriminantCharCast R D hD n :=
  ⟨χ.fundamentalDiscriminant,
    ⟨hχ.isFundamentalDiscr_fundamentalDiscriminant, χ.natAbs_fundamentalDiscriminant,
      fun _ hn ↦ hχ.apply_eq_fundamentalDiscriminantCharCast_of_isCoprime hn⟩,
    fun _ ⟨hD, habs, hval⟩ ↦ eq_fundamentalDiscriminant_of_natAbs_eq hD habs hval⟩

end ArbitraryLevel

section OddModulus

variable {R : Type*} [CommRing R]

/-- **Odd-argument value of a quadratic character in terms of its discriminant.** At an odd natural
number `n` coprime to `N`, a quadratic Dirichlet character `χ` of level `N` takes the value
`jacobiSym χ.fundamentalDiscriminant n`. -/
theorem _root_.MulChar.IsQuadratic.apply_natCast_eq_jacobiSym_fundamentalDiscriminant
    {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {n : ℕ} (hn : _root_.Odd n)
    (hcop : n.Coprime N) :
    χ n = (jacobiSym χ.fundamentalDiscriminant n : R) := by
  obtain rfl | _ := eq_zero_or_neZero N
  · obtain rfl := (Nat.coprime_zero_right n).mp hcop
    simp
  · rw [← Int.cast_natCast n,
      hχ.apply_eq_fundamentalDiscriminantCharCast_of_isCoprime
        (Nat.isCoprime_iff_coprime.mpr hcop),
      fundamentalDiscriminantCharCast_apply,
      fundamentalDiscriminantChar_natCast_eq_jacobiSym
        hχ.isFundamentalDiscr_fundamentalDiscriminant hn]

/-- **Odd-argument value of a quadratic character in terms of the squarefree radicand.** At an odd
natural number `n` coprime to `N`, `χ n` equals the cast of
`jacobiSym (fundamentalDiscriminantRadicand χ.fundamentalDiscriminant) n`. -/
theorem _root_.MulChar.IsQuadratic.apply_natCast_eq_jacobiSym_radicand
    {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {n : ℕ} (hn : _root_.Odd n)
    (hcop : n.Coprime N) :
    χ n =
      (jacobiSym (fundamentalDiscriminantRadicand χ.fundamentalDiscriminant) n : R) := by
  obtain rfl | _ := eq_zero_or_neZero N
  · obtain rfl := (Nat.coprime_zero_right n).mp hcop
    simp
  · rw [hχ.apply_natCast_eq_jacobiSym_fundamentalDiscriminant hn hcop,
      jacobiSym_fundamentalDiscriminantRadicand hn
        hχ.isFundamentalDiscr_fundamentalDiscriminant.emod_four_eq_zero_or_one]

/-- **Odd-prime value of a quadratic character in terms of its discriminant.** At an odd prime
`p ∤ N`, a quadratic Dirichlet character `χ` of level `N` takes the value
`legendreSym p χ.fundamentalDiscriminant`. -/
theorem _root_.MulChar.IsQuadratic.apply_natCast_prime_eq_legendreSym_fundamentalDiscriminant
    {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p χ.fundamentalDiscriminant : R) := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact hχ.apply_natCast_eq_jacobiSym_fundamentalDiscriminant
    ((Fact.out : p.Prime).odd_of_ne_two hp2) ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)

/-- **Odd-prime value of a quadratic character in terms of the squarefree radicand.** At an odd
prime `p ∤ N`, `χ p` equals the cast of
`legendreSym p (fundamentalDiscriminantRadicand χ.fundamentalDiscriminant)`. -/
theorem _root_.MulChar.IsQuadratic.apply_natCast_prime_eq_legendreSym_radicand
    {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p (fundamentalDiscriminantRadicand χ.fundamentalDiscriminant) : R) := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact hχ.apply_natCast_eq_jacobiSym_radicand
    ((Fact.out : p.Prime).odd_of_ne_two hp2) ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)

/-- In a nontrivial coefficient ring, `χ n = -1` implies `n.Coprime N`, since nonunits map to
`0 ≠ -1`. -/
private theorem coprime_level_of_apply_eq_neg_one [Nontrivial R] {N n : ℕ}
    {χ : DirichletCharacter R N} (hn : χ n = -1) : n.Coprime N := by
  have hu : IsUnit (n : ZMod N) := by
    by_contra hnu
    exact neg_ne_zero.mpr one_ne_zero (hn.symm.trans (MulChar.map_nonunit χ hnu))
  exact (ZMod.isUnit_iff_coprime n N).mp hu

/-- When `2 ≠ 0` in `R` and `χ n = -1` at an odd natural number `n`, the Jacobi symbol of
`χ.fundamentalDiscriminant` modulo `n` is `-1` (and `n.Coprime N` holds automatically). -/
theorem _root_.MulChar.IsQuadratic.jacobiSym_fundamentalDiscriminant_eq_neg_one
    [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {n : ℕ}
    (hn : _root_.Odd n) (hval : χ n = -1) :
    jacobiSym χ.fundamentalDiscriminant n = -1 := by
  have : Nontrivial R := ⟨2, 0, two_ne_zero⟩
  have hjac : (jacobiSym χ.fundamentalDiscriminant n : R) = -1 :=
    (hχ.apply_natCast_eq_jacobiSym_fundamentalDiscriminant hn
      (coprime_level_of_apply_eq_neg_one hval)).symm.trans hval
  rcases jacobiSym.trichotomy χ.fundamentalDiscriminant n with h | h | h
  · rw [h, Int.cast_zero] at hjac
    exact absurd hjac.symm (neg_ne_zero.mpr one_ne_zero)
  · rw [h, Int.cast_one, eq_neg_iff_add_eq_zero, one_add_one_eq_two] at hjac
    exact absurd hjac two_ne_zero
  · exact h

/-- When `2 ≠ 0` in `R` and `χ n = -1` at an odd natural number `n`, the Jacobi symbol of
`fundamentalDiscriminantRadicand χ.fundamentalDiscriminant` modulo `n` is `-1`. -/
theorem _root_.MulChar.IsQuadratic.jacobiSym_radicand_eq_neg_one
    [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {n : ℕ}
    (hn : _root_.Odd n) (hval : χ n = -1) :
    jacobiSym (fundamentalDiscriminantRadicand χ.fundamentalDiscriminant) n = -1 := by
  have : Nontrivial R := ⟨2, 0, two_ne_zero⟩
  have hcop : n.Coprime N := coprime_level_of_apply_eq_neg_one hval
  have : NeZero N := ⟨fun hN ↦ by
    obtain rfl := (Nat.coprime_zero_right n).mp (hN ▸ hcop)
    rw [Nat.cast_one, map_one, eq_neg_iff_add_eq_zero, one_add_one_eq_two] at hval
    exact two_ne_zero hval⟩
  rw [jacobiSym_fundamentalDiscriminantRadicand hn
    hχ.isFundamentalDiscr_fundamentalDiscriminant.emod_four_eq_zero_or_one]
  exact hχ.jacobiSym_fundamentalDiscriminant_eq_neg_one hn hval

/-- When `2 ≠ 0` in `R` and `χ p = -1` at an odd prime `p`, the Legendre symbol of
`χ.fundamentalDiscriminant` modulo `p` is `-1` (and `p ∤ N` holds automatically). -/
theorem _root_.MulChar.IsQuadratic.legendreSym_fundamentalDiscriminant_eq_neg_one
    [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hp : χ p = -1) :
    legendreSym p χ.fundamentalDiscriminant = -1 := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact hχ.jacobiSym_fundamentalDiscriminant_eq_neg_one
    ((Fact.out : p.Prime).odd_of_ne_two hp2) hp

/-- When `2 ≠ 0` in `R` and `χ p = -1` at an odd prime `p`, the Legendre symbol of
`fundamentalDiscriminantRadicand χ.fundamentalDiscriminant` modulo `p` is `-1`. -/
theorem _root_.MulChar.IsQuadratic.legendreSym_radicand_eq_neg_one
    [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hp : χ p = -1) :
    legendreSym p (fundamentalDiscriminantRadicand χ.fundamentalDiscriminant) = -1 := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact hχ.jacobiSym_radicand_eq_neg_one ((Fact.out : p.Prime).odd_of_ne_two hp2) hp

/-- **Nonsquare criterion for the discriminant.** When `2 ≠ 0` in `R` and `χ n = -1` at an odd
natural number `n`, `χ.fundamentalDiscriminant` is not a square modulo `n`. -/
theorem _root_.MulChar.IsQuadratic.not_isSquare_fundamentalDiscriminant_of_apply_eq_neg_one
    [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {n : ℕ}
    (hn : _root_.Odd n) (hval : χ n = -1) :
    ¬ IsSquare (χ.fundamentalDiscriminant : ZMod n) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one
    (hχ.jacobiSym_fundamentalDiscriminant_eq_neg_one hn hval)

/-- **Nonsquare criterion for the squarefree radicand.** When `2 ≠ 0` in `R` and `χ n = -1` at an
odd natural number `n`, `fundamentalDiscriminantRadicand χ.fundamentalDiscriminant` is not a square
modulo `n`. -/
theorem _root_.MulChar.IsQuadratic.not_isSquare_radicand_of_apply_eq_neg_one
    [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {n : ℕ}
    (hn : _root_.Odd n) (hval : χ n = -1) :
    ¬ IsSquare (fundamentalDiscriminantRadicand χ.fundamentalDiscriminant : ZMod n) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one (hχ.jacobiSym_radicand_eq_neg_one hn hval)

end OddModulus

/-! ### Examples -/

section Examples

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

-- The principal character at level `6` has fundamental discriminant `1`.
example : (1 : DirichletCharacter ℂ 6).fundamentalDiscriminant = 1 :=
  fundamentalDiscriminant_one

-- At conductor `8`, `χ₈` and `χ₈'` have discriminants `8` and `-8`, separated by `χ (-1)`.
example :
    fundamentalDiscriminant ZMod.χ₈ = 8 ∧ fundamentalDiscriminant ZMod.χ₈' = -8 := by
  have h8 : conductor ZMod.χ₈ = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five ZMod.χ₈ (by decide)
  have h8' : conductor ZMod.χ₈' = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five ZMod.χ₈' (by decide)
  refine ⟨?_, ?_⟩
  · rw [fundamentalDiscriminant_of_apply_neg_one_eq_one (by decide), h8]; rfl
  · rw [fundamentalDiscriminant_of_apply_neg_one_ne_one (by decide), h8']; rfl

-- `χ₄` lifted to level `12` has discriminant `-4` and vanishes at `3`, whereas `χ_{-4}(3) = -1`.
example :
    (changeLevel (by decide : 4 ∣ 12) ZMod.χ₄).fundamentalDiscriminant = -4 ∧
      changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) =
        -1 := by
  have h4 : conductor ZMod.χ₄ = 4 :=
    conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
  refine ⟨?_, ?_, by rw [fundamentalDiscriminantChar_neg_four]; decide⟩
  · rw [fundamentalDiscriminant_changeLevel,
      fundamentalDiscriminant_of_apply_neg_one_ne_one (by decide), h4]
    rfl
  · exact MulChar.map_nonunit _ (by decide)

-- Running example: `χ₄ · (Legendre mod 3)` at level `lcm 4 3 = 12` has discriminant `12`,
-- radicand `3`, values `-1, -1, 1` at `5, 7, 11`, and unchanged discriminant at level `24`.
example :
    (mul ZMod.χ₄ (quadraticChar (ZMod 3))).IsQuadratic ∧
      (mul ZMod.χ₄ (quadraticChar (ZMod 3))).fundamentalDiscriminant = 12 ∧
      fundamentalDiscriminantRadicand
          (mul ZMod.χ₄ (quadraticChar (ZMod 3))).fundamentalDiscriminant = 3 ∧
      mul ZMod.χ₄ (quadraticChar (ZMod 3)) (5 : ℕ) = -1 ∧
      mul ZMod.χ₄ (quadraticChar (ZMod 3)) (7 : ℕ) = -1 ∧
      mul ZMod.χ₄ (quadraticChar (ZMod 3)) (11 : ℕ) = 1 ∧
      (changeLevel (by decide : Nat.lcm 4 3 ∣ 24)
          (mul ZMod.χ₄ (quadraticChar (ZMod 3)))).fundamentalDiscriminant = 12 := by
  have : NeZero (Nat.lcm 4 3) := ⟨by decide⟩
  have hq : (mul ZMod.χ₄ (quadraticChar (ZMod 3))).IsQuadratic :=
    isQuadratic_mul (by intro a; fin_cases a <;> decide) (quadraticChar_isQuadratic (ZMod 3))
  have hc4 : (changeLevel (Nat.dvd_lcm_left 4 3) ZMod.χ₄).conductor = 4 := by
    rw [conductor_changeLevel]
    exact conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
  have hc3 : (changeLevel (Nat.dvd_lcm_right 4 3) (quadraticChar (ZMod 3))).conductor = 3 := by
    rw [conductor_changeLevel]
    refine (Nat.prime_three.eq_one_or_self_of_dvd _ (conductor_dvd_level _)).resolve_left
      fun h1 ↦ ?_
    have hq2 : quadraticChar (ZMod 3) 2 = 1 := by
      rw [eq_one_iff_conductor_eq_one.mpr h1]
      exact MulChar.one_apply (by decide)
    rw [quadraticChar_neg_one_iff_not_isSquare.mpr (by decide)] at hq2
    omega
  have hcond : (mul ZMod.χ₄ (quadraticChar (ZMod 3))).conductor = 12 := by
    rw [DirichletCharacter.mul, conductor_mul_of_coprime (by rw [hc4, hc3]; decide), hc4, hc3]
  have hneg1 : mul ZMod.χ₄ (quadraticChar (ZMod 3)) (-1) = 1 := by
    rw [DirichletCharacter.mul, MulChar.mul_apply, changeLevel_apply_neg_one,
      changeLevel_apply_neg_one, quadraticChar_neg_one_iff_not_isSquare.mpr (by decide)]
    decide
  have hdisc : (mul ZMod.χ₄ (quadraticChar (ZMod 3))).fundamentalDiscriminant = 12 := by
    rw [fundamentalDiscriminant_of_apply_neg_one_eq_one hneg1, hcond]
    rfl
  have hrad :
      fundamentalDiscriminantRadicand
        (mul ZMod.χ₄ (quadraticChar (ZMod 3))).fundamentalDiscriminant = 3 := by
    rw [hdisc, fundamentalDiscriminantRadicand_of_mod_four_ne_one (by decide)]
    norm_num
  refine ⟨hq, hdisc, hrad, ?_, ?_, ?_, ?_⟩
  · have : Fact (Nat.Prime 5) := ⟨by decide⟩
    rw [hq.apply_natCast_prime_eq_legendreSym_radicand (by decide) (by decide), hrad]
    norm_num
  · have : Fact (Nat.Prime 7) := ⟨by decide⟩
    rw [hq.apply_natCast_prime_eq_legendreSym_radicand (by decide) (by decide), hrad]
    norm_num
  · have : Fact (Nat.Prime 11) := ⟨by decide⟩
    rw [hq.apply_natCast_prime_eq_legendreSym_radicand (by decide) (by decide), hrad]
    norm_num
  · rw [fundamentalDiscriminant_changeLevel, hdisc]

end Examples

end DirichletCharacter
