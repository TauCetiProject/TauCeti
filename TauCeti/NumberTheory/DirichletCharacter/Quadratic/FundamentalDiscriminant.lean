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
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# Quadratic Dirichlet characters and fundamental discriminants

Every primitive quadratic Dirichlet character `χ` of level `N ≠ 0` is the character of a
fundamental discriminant: there is a fundamental discriminant `D` with `|D| = N` such that
`χ n = fundamentalDiscriminantCharCast R D hD n` at every integer `n`, the left side read modulo
`N` and the right side modulo `|D|`. More generally, any quadratic Dirichlet character `χ` of
nonzero level `N` agrees, at every integer coprime to `N`, with the realization of the character
of a unique fundamental discriminant `D` satisfying `|D| = χ.conductor`, namely
`D = χ.conductor` if `χ (-1) = 1` and `D = -χ.conductor` otherwise. The principal character is
included and corresponds to `D = 1`.

The local proof identifies each prime-power local factor of a primitive quadratic character as
the Legendre character (with `P = p*` and `k = 1`) at an odd prime `p`, or one of `χ₄`, `χ₈`,
`χ₈'` (with `P = -4`, `8`, `-8`) at `p = 2`, and multiplies these prime discriminants together.
An arbitrary quadratic character `χ` reduces to its primitive character `χ.primitiveCharacter` of
level `χ.conductor`. Uniqueness holds in every commutative ring `R`, without excluding `2 = 0`:
when `2 = 0`, every quadratic character is principal, so `χ.conductor = 1` and `D = 1` is forced
because `-1` is not a fundamental discriminant; when `2 ≠ 0`, `χ (-1) = (D.sign : R)` fixes the
sign of `D`.

For complex Dirichlet characters (more generally, any `RCLike`-valued character on a monoid with
finitely many units), being real-valued is equivalent to being quadratic by
`MulChar.isQuadratic_iff_forall_im_eq_zero` in `TauCeti.NumberTheory.MulChar.Real`. Both the
integer-valued character `fundamentalDiscriminantChar` and its scalar realizations agree through
`Int.castRingHom` (`fundamentalDiscriminantCharCast_apply`, `fundamentalDiscriminantCharCast_int`).

Writing `D = fundamentalDiscriminant d` for the unique squarefree radicand `d` (`d = D` if
`D ≡ 1 (mod 4)` and `d = D / 4` otherwise) gives the odd-prime dictionary: at every odd prime
`p ∤ N`, `χ p = (legendreSym p D : R) = (legendreSym p d : R)`, while `χ.primitiveCharacter p`
equals this Legendre symbol at every odd prime `p`, including `0` at ramified primes. When
`2 ≠ 0`, `χ p = -1` holds if and only if `p ∤ N` and `D` (equivalently `d`) is not a square
modulo `p`.

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of absolute
  value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a fundamental discriminant of absolute
  value `N`.
* `DirichletCharacter.IsPrimitive.isFundamentalDiscr_ite`,
  `DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite`: that fundamental
  discriminant is `χ (-1) N`, in every commutative ring.
* `DirichletCharacter.eq_ite_conductor_of_isFundamentalDiscr`,
  `DirichletCharacter.isFundamentalDiscr_ite_conductor`,
  `DirichletCharacter.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor`,
  `DirichletCharacter.apply_eq_fundamentalDiscriminantCharCast_ite_conductor`: for any quadratic
  character `χ` of nonzero level `N`, `D = if χ (-1) = 1 then χ.conductor else -χ.conductor` is
  the unique fundamental discriminant of absolute value `χ.conductor` matching `χ` at `-1`, and
  its character agrees with `χ.primitiveCharacter` everywhere and with `χ` on integers coprime
  to `N`.
* `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`: existence and uniqueness of the
  fundamental discriminant of a quadratic Dirichlet character of any nonzero level.
* `DirichletCharacter.changeLevel_apply_eq_fundamentalDiscriminantCharCast_iff`: naturality of
  the primitive discriminant under lifting to a nonzero multiple level.
* `DirichletCharacter.existsUnique_squarefree_fundamentalDiscriminant_apply_eq`: the unique
  squarefree radicand `d` with `D = fundamentalDiscriminant d`.
* `DirichletCharacter.apply_natCast_eq_jacobiSym_of_forall_isCoprime`,
  `DirichletCharacter.apply_prime_eq_legendreSym_of_forall_isCoprime`,
  `DirichletCharacter.primitiveCharacter_apply_prime_eq_legendreSym_of_forall_isCoprime`: the
  odd-argument Jacobi and odd-prime Legendre formulas.
* `DirichletCharacter.apply_prime_eq_neg_one_iff_not_dvd_and_not_isSquare`: when `2 ≠ 0`,
  `χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (D : ZMod p)` for every odd prime `p`.

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

/-- If `D` is a fundamental discriminant with `|D| = χ.conductor` whose character agrees at `-1`
with a quadratic Dirichlet character `χ` of nonzero level `N`, then `D` is `χ.conductor` if
`χ (-1) = 1` and `-χ.conductor` otherwise. This holds in every commutative ring: when `2 = 0`,
`χ` is principal, so `χ.conductor = 1` and `D = 1` because `-1` is not a fundamental discriminant.
-/
theorem eq_ite_conductor_of_isFundamentalDiscr [DecidableEq R] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hDc : D.natAbs = χ.conductor)
    (hneg : χ (-1) = fundamentalDiscriminantCharCast R D hD (-1)) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  by_cases h2 : (2 : R) = 0
  · have h1 : χ = 1 := hq.eq_one_of_two_eq_zero h2
    have hD1 : D = 1 := hD.natAbs_eq_one_iff.mp (hDc.trans (by rw [h1, conductor_one]))
    simp [h1, hD1, conductor_one, MulChar.one_apply isUnit_one.neg]
  · have hsign : χ (-1) = D.sign := by
      simpa [fundamentalDiscriminantChar_neg_one] using hneg
    split_ifs with h1 <;> rw [hsign] at h1 <;> rcases hD.ne_zero.lt_or_gt with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero,
        one_add_one_eq_two] at h1
      exact absurd h1 h2
    · omega
    · omega
    · rw [Int.sign_eq_one_of_pos h, Int.cast_one] at h1
      exact absurd rfl h1

section Sign

variable [DecidableEq R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- The fundamental discriminant of a primitive quadratic character `χ` of level `N` is `N` if
`χ (-1) = 1` and `-N` otherwise. -/
private theorem IsPrimitive.exists_eq_ite_apply_eq (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D = (if χ (-1) = 1 then (N : ℤ) else -N) ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  have hcond : χ.conductor = N := (isPrimitive_def _).mp hχ
  have hDeq := eq_ite_conductor_of_isFundamentalDiscr hq hD (hDN.trans hcond.symm)
    (by simpa using hval (-1))
  exact ⟨D, hD, by rwa [hcond] at hDeq, hval⟩

/-- The integer `χ (-1) N`, that is `N` if `χ (-1) = 1` and `-N` otherwise, is a fundamental
discriminant for every primitive quadratic character `χ` of level `N`. -/
theorem IsPrimitive.isFundamentalDiscr_ite (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (N : ℤ) else -N) := by
  obtain ⟨D, hD, rfl, -⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hD

/-- **Primitive quadratic characters are Kronecker characters, with their discriminant.** A
primitive quadratic character `χ` of level `N` is the character of the fundamental discriminant
`D = χ (-1) N`: `χ n = fundamentalDiscriminantCharCast R D hD n` at every integer `n`. For the
principal character, primitive only at level `1`, this is `D = 1`. -/
theorem IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ n = fundamentalDiscriminantCharCast R _ (hχ.isFundamentalDiscr_ite hq) n := by
  obtain ⟨D, hD, rfl, hval⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hval n

end Sign

/-! ### Arbitrary-level quadratic characters -/

/-- The signed conductor `if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor` equals `1` if
and only if `χ` is principal. -/
@[simp]
theorem ite_conductor_eq_one_iff {R : Type*} [CommMonoidWithZero R] [DecidableEq R]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 ↔ χ = 1 := by
  split_ifs with h
  · rw [Nat.cast_eq_one, eq_one_iff_conductor_eq_one]
  · refine iff_of_false (by omega) ?_
    rintro rfl
    exact h (MulChar.one_apply isUnit_one.neg)

/-- For every quadratic Dirichlet character `χ` of nonzero level, the signed conductor
`if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor` is a fundamental discriminant. -/
theorem isFundamentalDiscr_ite_conductor [DecidableEq R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa [primitiveCharacter_apply_neg_one] using
    χ.primitiveCharacter_isPrimitive.isFundamentalDiscr_ite hq.primitiveCharacter

/-- The primitive character of a quadratic Dirichlet character `χ` of nonzero level agrees, at
every integer, with the realization of the fundamental-discriminant character of
`if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor`. -/
theorem primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor [DecidableEq R]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter R N) (hq : χ.IsQuadratic) (n : ℤ) :
    χ.primitiveCharacter n =
      fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_ite_conductor χ hq) n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, hDeq, hval⟩ :=
    χ.primitiveCharacter_isPrimitive.exists_eq_ite_apply_eq hq.primitiveCharacter
  rw [primitiveCharacter_apply_neg_one] at hDeq
  subst hDeq
  exact hval n

/-- Every quadratic Dirichlet character `χ` of nonzero level `N` agrees, at every integer coprime
to `N`, with the realization of the fundamental-discriminant character of
`if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor`. -/
theorem apply_eq_fundamentalDiscriminantCharCast_ite_conductor [DecidableEq R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hq : χ.IsQuadratic) {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_ite_conductor χ hq) n := by
  rw [← primitiveCharacter_apply_of_isCoprime χ hn]
  exact primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor χ hq n

/-- For a fundamental discriminant `D` with `|D| = χ.conductor`, `χ` agrees with
`fundamentalDiscriminantCharCast R D hD` on integers coprime to `N` if and only if
`χ.primitiveCharacter` agrees with it at every integer. -/
theorem primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_iff {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hDc : D.natAbs = χ.conductor) :
    (∀ n : ℤ, χ.primitiveCharacter n = fundamentalDiscriminantCharCast R D hD n) ↔
      (∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) := by
  refine ⟨fun h n hn ↦ by rw [← primitiveCharacter_apply_of_isCoprime χ hn, h n],
    fun hval ↦ ?_⟩
  have hq : χ.IsQuadratic :=
    isQuadratic_of_forall_isCoprime_apply_eq (fundamentalDiscriminantCharCast_isQuadratic hD) hval
  classical
  have hDeq := eq_ite_conductor_of_isFundamentalDiscr hq hD hDc
    (by simpa using hval (-1) (IsCoprime.neg_left isCoprime_one_left))
  subst hDeq
  exact primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor χ hq

/-- **The primitive discriminant of a quadratic character.** A quadratic Dirichlet character `χ`
of any nonzero level `N`, with values in any commutative ring `R`, agrees at every integer coprime
to `N` with the realization of the character of a unique fundamental discriminant `D` satisfying
`|D| = χ.conductor`. Explicitly, `D = χ.conductor` if `χ (-1) = 1` and `D = -χ.conductor`
otherwise; the principal character corresponds to `D = 1` (Montgomery–Vaughan, Theorem 9.13). -/
theorem existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D,
      D.natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  refine ⟨if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor,
    ⟨isFundamentalDiscr_ite_conductor χ hq,
      by split_ifs <;> simp,
      fun n hn ↦ apply_eq_fundamentalDiscriminantCharCast_ite_conductor χ hq hn⟩,
    fun D ⟨hD, hDc, hval⟩ ↦
      eq_ite_conductor_of_isFundamentalDiscr hq hD hDc
        (by simpa using hval (-1) (IsCoprime.neg_left isCoprime_one_left))⟩

/-- **Naturality of the primitive discriminant under level change.** Raising a character `χ` from
level `N` to a nonzero multiple `M` preserves its conductor (`conductor_changeLevel`), and for any
fundamental discriminant `D` with `|D| = χ.conductor`, `changeLevel h χ` agrees with
`fundamentalDiscriminantCharCast R D hD` on integers coprime to `M` if and only if `χ` agrees
with it on integers coprime to `N`. -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast_iff {N M : ℕ} [NeZero M]
    (h : N ∣ M) (χ : DirichletCharacter R N) {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hDc : D.natAbs = χ.conductor) :
    (∀ n : ℤ, IsCoprime n M →
      changeLevel h χ n = fundamentalDiscriminantCharCast R D hD n) ↔
    (∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) := by
  have : NeZero N := ⟨fun h0 ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (h0 ▸ h))⟩
  refine ⟨fun hval ↦ ?_, fun hval n hn ↦ ?_⟩
  · have hqM : (changeLevel h χ).IsQuadratic :=
      isQuadratic_of_forall_isCoprime_apply_eq (fundamentalDiscriminantCharCast_isQuadratic hD) hval
    have hq : χ.IsQuadratic := (isQuadratic_changeLevel_iff h).mp hqM
    classical
    have hDeq : D = if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
      simpa [changeLevel_apply_neg_one, conductor_changeLevel] using
        eq_ite_conductor_of_isFundamentalDiscr hqM hD (by rwa [conductor_changeLevel])
          (by simpa using hval (-1) (IsCoprime.neg_left isCoprime_one_left))
    subst hDeq
    exact fun n hn ↦ apply_eq_fundamentalDiscriminantCharCast_ite_conductor χ hq hn
  · rw [changeLevel_eq_cast_of_dvd' χ h hn]
    exact hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr h))

/-- **The squarefree radicand of a quadratic character.** Every quadratic Dirichlet character `χ`
of nonzero level `N` agrees, at every integer coprime to `N`, with the character of
`fundamentalDiscriminant d` for a unique squarefree integer `d` with
`|fundamentalDiscriminant d| = χ.conductor`. -/
theorem existsUnique_squarefree_fundamentalDiscriminant_apply_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (hq : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d,
      (fundamentalDiscriminant d).natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N →
          χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
            (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniq⟩ := existsUnique_isFundamentalDiscr_apply_eq χ hq
  obtain ⟨d, ⟨hd, rfl⟩, -⟩ := existsUnique_squarefree_fundamentalDiscriminant_eq hD
  exact ⟨d, ⟨hd, hDc, hval⟩, fun d' ⟨hd', hDc', hval'⟩ ↦
    fundamentalDiscriminant_injective
      (huniq _ ⟨isFundamentalDiscr_fundamentalDiscriminant hd', hDc', hval'⟩)⟩

/-! ### Odd-argument Jacobi, odd-prime Legendre, and nonsquare dictionary -/

/-- If `χ` agrees with the character of a fundamental discriminant `D` on integers coprime to `N`,
then at every odd natural number `n` coprime to `N`, `χ n` is the cast of the Jacobi symbol
`(D / n)`. When `D = fundamentalDiscriminant d`, `jacobiSym_fundamentalDiscriminant` rewrites the
right-hand side to `(jacobiSym d n : R)`. -/
theorem apply_natCast_eq_jacobiSym_of_forall_isCoprime {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℕ} (hn : _root_.Odd n) (hcop : n.Coprime N) :
    χ n = (jacobiSym D n : R) := by
  have h := hval (n : ℤ) (Nat.isCoprime_iff_coprime.mpr hcop)
  rw [Int.cast_natCast, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hn] at h
  exact h

/-- If `χ` agrees with the character of a fundamental discriminant `D` on integers coprime to `N`,
then at every odd prime `p ∤ N`, `χ p` is the cast of the Legendre symbol `(D / p)`. When
`D = fundamentalDiscriminant d`, `legendreSym_fundamentalDiscriminant` rewrites the right-hand
side to `(legendreSym p d : R)`. -/
theorem apply_prime_eq_legendreSym_of_forall_isCoprime {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  rw [apply_natCast_eq_jacobiSym_of_forall_isCoprime hD hval
    ((Fact.out : p.Prime).odd_of_ne_two hp2) ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN),
    ← jacobiSym.legendreSym.to_jacobiSym]

/-- If `χ` agrees with the character of a fundamental discriminant `D` of absolute value
`χ.conductor` on integers coprime to `N`, then its primitive character evaluates to the Legendre
symbol `(D / p)` at every odd prime `p`, including the ramified primes `p ∣ D` where both sides
vanish. -/
theorem primitiveCharacter_apply_prime_eq_legendreSym_of_forall_isCoprime {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hDc : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ.primitiveCharacter p = (legendreSym p D : R) := by
  have h := (primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_iff hD hDc).mpr hval p
  rw [Int.cast_natCast, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2] at h
  exact h

/-- **Nonsquare criterion from a character value `-1`.** When `2 ≠ 0` in the coefficient ring `R`,
if `χ` agrees with the character of a fundamental discriminant `D` on integers coprime to `N`, then
at any odd prime `p`, `χ p = -1` if and only if `p ∤ N` and `D` is not a square modulo `p`. When
`D = fundamentalDiscriminant d`, `isSquare_intCast_fundamentalDiscriminant_iff` gives the same
criterion for `d`. -/
theorem apply_prime_eq_neg_one_iff_not_dvd_and_not_isSquare [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (D : ZMod p) := by
  have h0neg : (0 : R) ≠ -1 := fun h ↦ NeZero.ne (2 : R) (by linear_combination 2 * h)
  have h1neg : (1 : R) ≠ -1 := fun h ↦ NeZero.ne (2 : R) (by linear_combination h)
  by_cases hpN : p ∣ N
  · have hnonunit : ¬ IsUnit (p : ZMod N) := by
      rw [ZMod.isUnit_iff_coprime, (Fact.out : p.Prime).coprime_iff_not_dvd]
      exact not_not.mpr hpN
    rw [MulChar.map_nonunit χ hnonunit]
    exact iff_of_false h0neg (fun h ↦ h.1 hpN)
  · rw [apply_prime_eq_legendreSym_of_forall_isCoprime hD hval hp2 hpN, and_iff_right hpN,
      ← legendreSym.eq_neg_one_iff]
    rcases quadraticChar_isQuadratic (ZMod p) (D : ZMod p) with h | h | h <;>
      simp [legendreSym, h, h0neg, h1neg]

end DirichletCharacter

/-! ## Examples -/

section Examples

open DirichletCharacter

/-! Fundamental discriminants `1`, `-4`, `8`, `-8`, `5`, `-3`, `12` and the non-fundamental
discriminant `-12 = 4 · (-3)` with `-3 ≡ 1 (mod 4)`. -/

example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧ Int.IsFundamentalDiscr 8 ∧
    Int.IsFundamentalDiscr (-8) ∧ Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) := by
  have h5 : Int.IsFundamentalDiscr 5 := by
    have h :=
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_five (by decide)).isFundamentalDiscr
    rwa [oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num)] at h
  have hneg3 : Int.IsFundamentalDiscr (-3) := by
    have h :=
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_three (by decide)).isFundamentalDiscr
    rwa [oddPrimeDiscriminant_of_mod_four_eq_three (by norm_num)] at h
  have h12 : Int.IsFundamentalDiscr 12 :=
    (Int.isFundamentalDiscr_four_mul (m := 3)).mpr
      ⟨((Int.prime_iff_natAbs_prime (k := 3)).mpr Nat.prime_three).squarefree,
        Or.inr (by norm_num)⟩
  refine ⟨Int.isFundamentalDiscr_one, isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr,
    isPrimeDiscriminant_neg_eight.isFundamentalDiscr, h5, hneg3, h12, fun h ↦ ?_⟩
  have h' : (4 * -3 : ℤ) = -12 := by norm_num
  rw [← h', Int.isFundamentalDiscr_four_mul] at h
  have := h.2
  omega

/-! At levels `4` and `8`, `χ₄`, `χ₈` and `χ₈'` correspond to the fundamental discriminants
`-4`, `8` and `-8`; the sign at `-1` distinguishes `8` from `-8` at conductor `8`. -/

example :
    let χ : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
    ∃ hD : Int.IsFundamentalDiscr (-4), (-4 : ℤ).natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n 4 → χ n = fundamentalDiscriminantCharCast ℂ (-4) hD n := by
  intro χ
  refine ⟨isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    by simp [χ, conductor_χ₄_ringHomComp], fun n _ ↦ ?_⟩
  rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_four,
    MulChar.ringHomComp_apply, eq_intCast]

example :
    let χ : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
    let ψ : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)
    χ.conductor = 8 ∧ ψ.conductor = 8 ∧ χ (-1) = 1 ∧ ψ (-1) = -1 ∧
      (∃ hD : Int.IsFundamentalDiscr 8,
        ∀ n : ℤ, IsCoprime n 8 → χ n = fundamentalDiscriminantCharCast ℂ 8 hD n) ∧
      (∃ hD : Int.IsFundamentalDiscr (-8),
        ∀ n : ℤ, IsCoprime n 8 → ψ n = fundamentalDiscriminantCharCast ℂ (-8) hD n) := by
  intro χ ψ
  have hχ_neg : ZMod.χ₈ (-1) = 1 := by decide
  have hψ_neg : ZMod.χ₈' (-1) = -1 := by decide
  refine ⟨by simp [χ, conductor_χ₈_ringHomComp], by simp [ψ, conductor_χ₈'_ringHomComp],
    by rw [MulChar.ringHomComp_apply, hχ_neg, map_one],
    by rw [MulChar.ringHomComp_apply, hψ_neg, map_neg, map_one],
    ⟨isPrimeDiscriminant_eight.isFundamentalDiscr, fun n _ ↦ by
      rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_eight,
        MulChar.ringHomComp_apply, eq_intCast]⟩,
    ⟨isPrimeDiscriminant_neg_eight.isFundamentalDiscr, fun n _ ↦ by
      rw [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_eight,
        MulChar.ringHomComp_apply, eq_intCast]⟩⟩

/-! Running example: `χ₄ · (Legendre mod 3)` at level `12` has conductor `12`, even parity
`χ (-1) = 1`, fundamental discriminant `D = 12` (not `-12`), squarefree radicand `d = 3`, values
`-1, -1, 1` at `5, 7, 11`, and lifting to level `24` preserves both its conductor and `D = 12`.
Moreover `χ 5 = -1` implies that neither `12` nor `3` is a square modulo `5`. -/

example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) *
        changeLevel (by norm_num : 3 ∣ 12)
          ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ))
    let χ24 : DirichletCharacter ℂ 24 := changeLevel (by norm_num : 12 ∣ 24) χ
    have h12 : Int.IsFundamentalDiscr 12 :=
      (Int.isFundamentalDiscr_four_mul (m := 3)).mpr
        ⟨((Int.prime_iff_natAbs_prime (k := 3)).mpr Nat.prime_three).squarefree,
          Or.inr (by norm_num)⟩
    χ.conductor = 12 ∧ χ (-1) = 1 ∧
      (∀ n : ℤ, IsCoprime n 12 → χ n = fundamentalDiscriminantCharCast ℂ 12 h12 n) ∧
      χ 5 = -1 ∧ χ 7 = -1 ∧ χ 11 = 1 ∧
      χ24.conductor = 12 ∧
      (∀ n : ℤ, IsCoprime n 24 → χ24 n = fundamentalDiscriminantCharCast ℂ 12 h12 n) ∧
      ¬ IsSquare (12 : ZMod 5) ∧ ¬ IsSquare (3 : ZMod 5) := by
  intro χ χ24 h12
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  have hcond : χ.conductor = 12 := by
    rw [conductor_mul_of_coprime] <;>
      simp only [conductor_changeLevel, conductor_χ₄_ringHomComp,
        conductor_changeLevel_quadraticChar hR (by norm_num : 3 ≠ 2)]
    norm_num
  have hneg : χ (-1) = 1 := by
    have hχ4_neg : ZMod.χ₄ (-1) = -1 := by decide
    have hq3_neg : quadraticChar (ZMod 3) (-1) = -1 := by
      simpa [legendreSym] using (by norm_num : legendreSym 3 (-1) = -1)
    rw [MulChar.mul_apply, changeLevel_apply_neg_one, changeLevel_apply_neg_one,
      MulChar.ringHomComp_apply, MulChar.ringHomComp_apply, hχ4_neg, hq3_neg]
    norm_num
  have hq : χ.IsQuadratic :=
    ((ZMod.isQuadratic_χ₄.comp _).changeLevel _).mul
      (((quadraticChar_isQuadratic (ZMod 3)).comp _).changeLevel _)
  have hval :
      ∀ n : ℤ, IsCoprime n 12 → χ n = fundamentalDiscriminantCharCast ℂ 12 h12 n := by
    classical
    obtain ⟨D, ⟨hD, hDc, hDval⟩, -⟩ := existsUnique_isFundamentalDiscr_apply_eq χ hq
    have hD12 : D = 12 := by
      have h := eq_ite_conductor_of_isFundamentalDiscr hq hD hDc
        (by simpa using hDval (-1) (IsCoprime.neg_left isCoprime_one_left))
      simpa [hcond, hneg] using h
    subst hD12
    exact hDval
  have h5 : χ 5 = -1 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h := apply_prime_eq_legendreSym_of_forall_isCoprime (p := 5) h12 hval
      (by decide) (by decide)
    norm_num at h ⊢
    exact h
  have h7 : χ 7 = -1 := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have h := apply_prime_eq_legendreSym_of_forall_isCoprime (p := 7) h12 hval
      (by decide) (by decide)
    norm_num at h ⊢
    exact h
  have h11 : χ 11 = 1 := by
    have : Fact (Nat.Prime 11) := ⟨Nat.prime_eleven⟩
    have h := apply_prime_eq_legendreSym_of_forall_isCoprime (p := 11) h12 hval
      (by decide) (by decide)
    norm_num at h ⊢
    exact h
  have h24val :
      ∀ n : ℤ, IsCoprime n 24 → χ24 n = fundamentalDiscriminantCharCast ℂ 12 h12 n :=
    (changeLevel_apply_eq_fundamentalDiscriminantCharCast_iff
      (by norm_num : 12 ∣ 24) χ h12 (by simp [hcond])).mpr hval
  have hnsq12 : ¬ IsSquare (12 : ZMod 5) := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have h := ((apply_prime_eq_neg_one_iff_not_dvd_and_not_isSquare (p := 5) h12 hval
      (by decide)).mp (by simpa using h5)).2
    simpa using h
  have hnsq3 : ¬ IsSquare (3 : ZMod 5) := by
    have h2 : IsUnit (2 : ZMod 5) := (ZMod.isUnit_iff_coprime 2 5).mpr (by decide)
    have hfd : fundamentalDiscriminant 3 = 12 := by norm_num [fundamentalDiscriminant_def]
    have h :=
      (isSquare_intCast_fundamentalDiscriminant_iff h2 3).not.mp (by simpa [hfd] using hnsq12)
    simpa using h
  exact ⟨hcond, hneg, hval, h5, h7, h11, by simp [χ24, conductor_changeLevel, hcond],
    h24val, hnsq12, hnsq3⟩

/-! Lifting `χ₄` to level `12` gives an imprimitive character of conductor `4` and discriminant
`D = -4`; it vanishes at `3`, whereas `χ_(-4)(3) = -1`, showing that agreement holds only at
integers coprime to `12`. -/

example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by norm_num : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    have hD : Int.IsFundamentalDiscr (-4) := isPrimeDiscriminant_neg_four.isFundamentalDiscr
    χ.conductor = 4 ∧
      (∀ n : ℤ, IsCoprime n 12 → χ n = fundamentalDiscriminantCharCast ℂ (-4) hD n) ∧
      χ 3 = 0 ∧ fundamentalDiscriminantCharCast ℂ (-4) hD 3 = -1 := by
  intro χ hD
  refine ⟨by simp [χ, conductor_changeLevel, conductor_χ₄_ringHomComp],
    fun n hn ↦ by
      rw [changeLevel_ringHomComp_intCast_apply (by norm_num : 4 ∣ 12) _ hn,
        fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_neg_four],
    MulChar.map_nonunit χ (by decide), ?_⟩
  rw [fundamentalDiscriminantCharCast_apply]
  have h := fundamentalDiscriminantChar_neg_four 3
  have h3 : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  rw [Int.cast_ofNat, h3] at h
  rw [h, Int.cast_neg, Int.cast_one]

/-! The principal character at level `6` has conductor `1` and fundamental discriminant `D = 1`;
it agrees with `χ_1` at `n = 5`, while `-3` fails `|D| = conductor`. -/

example :
    let χ : DirichletCharacter ℂ 6 := 1
    χ.conductor = 1 ∧
      (∀ n : ℤ, IsCoprime n 6 →
        χ n = fundamentalDiscriminantCharCast ℂ 1 Int.isFundamentalDiscr_one n) ∧
      χ 5 = 1 ∧ (-3 : ℤ).natAbs ≠ χ.conductor := by
  intro χ
  refine ⟨conductor_one, fun n hn ↦ ?_, MulChar.one_apply (by decide),
    by rw [conductor_one]; decide⟩
  have hu : IsUnit (n : ZMod 6) := (ZMod.isUnit_intCast_iff_isCoprime n 6).mpr hn.symm
  rw [MulChar.one_apply hu, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_intCast]
  simp

/-! Odd-prime dictionary and exclusion of `p = 2`: `D = 12` has radicand `d = 3`, `D = -4` has
radicand `d = -1`, at `p = 5` we have `legendreSym 5 12 = legendreSym 5 3 = -1`, at `p = 3` both
vanish, and at `p = 2` we have `χ_5(2) = -1 ≠ 1 = legendreSym 2 5`. -/

example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    fundamentalDiscriminant 3 = 12 ∧ fundamentalDiscriminant (-1) = -4 ∧
      (legendreSym 5 12 = -1 ∧ legendreSym 5 3 = -1) ∧
      (legendreSym 3 12 = 0 ∧ legendreSym 3 3 = 0) ∧
      (∃ h5 : Int.IsFundamentalDiscr 5,
        fundamentalDiscriminantChar 5 h5 2 = -1 ∧ legendreSym 2 5 = 1) := by
  intro _
  have h5 : Int.IsFundamentalDiscr 5 := by
    have h :=
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_five (by decide)).isFundamentalDiscr
    rwa [oddPrimeDiscriminant_of_mod_four_eq_one (by norm_num)] at h
  refine ⟨by norm_num [fundamentalDiscriminant_def], by norm_num [fundamentalDiscriminant_def],
    ⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩, ⟨h5, ?_, by norm_num⟩⟩
  rw [fundamentalDiscriminantChar_two]
  decide

end Examples
