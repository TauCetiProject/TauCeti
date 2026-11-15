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

Every quadratic Dirichlet character `χ` of nonzero level `N` with values in a commutative ring `R`
is governed by a unique fundamental discriminant `D` of absolute value `χ.conductor`: at every
integer `n` coprime to `N`, `χ n = fundamentalDiscriminantCharCast R D hD n`. Explicitly,
`D = χ.conductor` when `χ (-1) = 1` and `D = -χ.conductor` otherwise, including in characteristic
two (where every quadratic character is trivial of conductor `1`, with `D = 1`). When `χ` is
primitive, `χ.conductor = N` and the agreement holds at *all* integers `n`. The principal character
at any nonzero level corresponds to `D = 1`.

Locally, at a prime power `p ^ k` (`k ≠ 0`), a primitive quadratic character is the Legendre
character modulo `p` (with `k = 1`) when `p` is odd, and `χ₄`, `χ₈` or `χ₈'` (with `k = 2` or `3`)
when `p = 2`; in each case it is the character of a prime discriminant `p*`, `-4`, `8` or `-8` of
absolute value `p ^ k`. Globally, the discriminant of a primitive quadratic character is the product
of the prime discriminants of its local factors, and the primitive discriminant of any quadratic
character `χ` of level `N ≠ 0` is the discriminant of `χ.primitiveCharacter`.

Lifting `χ` along `N ∣ M` (`M ≠ 0`) preserves both `χ.conductor` and `χ (-1)`, hence preserves its
fundamental discriminant `D`. Through `fundamentalDiscriminant` and
`fundamentalDiscriminantRadicand`, `D` also corresponds to a unique squarefree radicand `d` with
`fundamentalDiscriminant d = D`. At any odd natural number `m` coprime to `N`,
`χ m = jacobiSym D m = jacobiSym d m`, and at any odd prime `p ∤ N`,
`χ p = legendreSym p D = legendreSym p d`. When `2 ≠ 0` in `R` and `p` is an odd prime,
`χ p = -1` holds if and only if `p ∤ N` and `D` (equivalently `d`) is not a square in `ZMod p`.

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of prime-power level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of
  absolute value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a unique fundamental discriminant of absolute
  value `N`.
* `DirichletCharacter.IsPrimitive.isFundamentalDiscr_ite`,
  `DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite`: that fundamental
  discriminant is `if χ (-1) = 1 then N else -N`.
* `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq`: every quadratic Dirichlet
  character `χ` of level `N ≠ 0` corresponds to a unique fundamental discriminant `D` with
  `|D| = χ.conductor` agreeing with `χ` on all integers coprime to `N`.
* `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_forall_isCoprime_apply_eq`,
  `DirichletCharacter.conductor_eq_natAbs_of_forall_isCoprime_apply_eq`: when `2 ≠ 0` in `R`,
  agreement on integers coprime to `N` automatically forces `χ.conductor = |D|`.
* `MulChar.IsQuadratic.isFundamentalDiscr_conductor_ite`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime`: explicit formula
  `if χ (-1) = 1 then χ.conductor else -χ.conductor` for the primitive discriminant of `χ`.
* `MulChar.IsQuadratic.natAbs_eq_conductor_and_forall_changeLevel_apply_eq_iff`: naturality of the
  primitive discriminant under `DirichletCharacter.changeLevel`.
* `MulChar.IsQuadratic.existsUnique_squarefree_apply_eq`: unique squarefree radicand formulation.
* `DirichletCharacter.apply_prime_eq_legendreSym_of_forall_isCoprime`,
  `DirichletCharacter.apply_prime_eq_legendreSym_radicand_of_forall_isCoprime`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare_radicand`: odd-prime Legendre values
  and the nonsquare criterion at primes where `χ p = -1`.

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

/-- Two nonzero integers whose casts of signs to a ring with `2 ≠ 0` agree and whose `natAbs`
agree are equal. -/
private theorem eq_of_cast_sign_eq_of_natAbs_eq {D₁ D₂ : ℤ} (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0)
    (h2 : (2 : R) ≠ 0) (hsign : (D₁.sign : R) = (D₂.sign : R))
    (habs : D₁.natAbs = D₂.natAbs) : D₁ = D₂ := by
  have hs : D₁.sign = D₂.sign := by
    rcases h₁.lt_or_gt with hn₁ | hp₁ <;> rcases h₂.lt_or_gt with hn₂ | hp₂
    · rw [Int.sign_eq_neg_one_of_neg hn₁, Int.sign_eq_neg_one_of_neg hn₂]
    · rw [Int.sign_eq_neg_one_of_neg hn₁, Int.sign_eq_one_of_pos hp₂, Int.cast_neg, Int.cast_one,
        neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hsign
      exact absurd hsign h2
    · rw [Int.sign_eq_one_of_pos hp₁, Int.sign_eq_neg_one_of_neg hn₂, Int.cast_neg, Int.cast_one,
        eq_comm, neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hsign
      exact absurd hsign h2
    · rw [Int.sign_eq_one_of_pos hp₁, Int.sign_eq_one_of_pos hp₂]
  rw [← Int.sign_mul_natAbs D₁, ← Int.sign_mul_natAbs D₂, hs, habs]

/-- **Uniqueness for primitive quadratic characters.** Every primitive quadratic character `χ` of
level `N ≠ 0` is the character of a *unique* fundamental discriminant `D` of absolute value `N`. -/
theorem IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = N ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  refine ⟨D, ⟨hD, hDN, hval⟩, fun D' ⟨hD', hD'N, hval'⟩ ↦ ?_⟩
  by_cases h2 : (2 : R) = 0
  · have hN1 : N = 1 := hχ.eq_one_iff.mp (hq.eq_one_of_two_eq_zero h2)
    rw [hD'.natAbs_eq_one_iff.mp (hD'N.trans hN1), hD.natAbs_eq_one_iff.mp (hDN.trans hN1)]
  · refine eq_of_cast_sign_eq_of_natAbs_eq hD'.ne_zero hD.ne_zero h2 ?_ (hD'N.trans hDN.symm)
    have h1 : χ (-1) = (D'.sign : R) := by
      simpa [fundamentalDiscriminantChar_neg_one] using hval' (-1)
    have h1' : χ (-1) = (D.sign : R) := by
      simpa [fundamentalDiscriminantChar_neg_one] using hval (-1)
    exact h1.symm.trans h1'

/-- Two equal fundamental discriminants give equal character values at every integer. -/
private theorem fundamentalDiscriminantCharCast_congr {D₁ D₂ : ℤ}
    (hD₁ : Int.IsFundamentalDiscr D₁) (hD₂ : Int.IsFundamentalDiscr D₂) (h : D₁ = D₂)
    (n : ℤ) :
    fundamentalDiscriminantCharCast R D₁ hD₁ n =
      fundamentalDiscriminantCharCast R D₂ hD₂ n := by
  subst h
  rfl

/-- The primitive character of `χ` takes the same value at `-1` as `χ`. -/
private theorem primitiveCharacter_apply_neg_one {N : ℕ} (χ : DirichletCharacter R N) :
    χ.primitiveCharacter (-1) = χ (-1) := by
  conv_rhs => rw [← χ.changeLevel_primitiveCharacter, changeLevel_apply_neg_one]

section Sign

variable [DecidableEq R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- The fundamental discriminant of a primitive quadratic character `χ` of level `N ≠ 0` is `N` if
`χ (-1) = 1` and `-N` otherwise, over any commutative ring `R`. -/
private theorem IsPrimitive.exists_eq_ite_apply_eq (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D = (if χ (-1) = 1 then (N : ℤ) else -N) ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  by_cases h2 : (2 : R) = 0
  · have hχ1 : χ = 1 := hq.eq_one_of_two_eq_zero h2
    have hN1 : N = 1 := hχ.eq_one_iff.mp hχ1
    subst hN1
    refine ⟨1, Int.isFundamentalDiscr_one, ?_, fun n ↦ ?_⟩
    · simp [hχ1, MulChar.one_apply isUnit_one.neg]
    · simp [hχ1]
  · obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
    have hsign : χ (-1) = D.sign := by
      simpa [fundamentalDiscriminantChar_neg_one] using hval (-1)
    refine ⟨D, hD, ?_, hval⟩
    split_ifs with h1 <;> rw [hsign] at h1 <;> rcases hD.ne_zero.lt_or_gt with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero,
        one_add_one_eq_two] at h1
      exact absurd h1 h2
    · omega
    · omega
    · rw [Int.sign_eq_one_of_pos h, Int.cast_one] at h1
      exact absurd rfl h1

/-- The integer `if χ (-1) = 1 then N else -N` is a fundamental discriminant for every primitive
quadratic character `χ` of level `N ≠ 0`. -/
theorem IsPrimitive.isFundamentalDiscr_ite (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (N : ℤ) else -N) := by
  obtain ⟨D, hD, rfl, -⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hD

/-- **Primitive quadratic characters are Kronecker characters, with their discriminant.** A
primitive quadratic character `χ` of level `N ≠ 0` is the character of the fundamental discriminant
`D = if χ (-1) = 1 then N else -N`: `χ n = fundamentalDiscriminantCharCast R D hD n` at every
integer `n`. For the principal character, primitive only at level `1`, this is `D = 1`. -/
theorem IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ n = fundamentalDiscriminantCharCast R _ (hχ.isFundamentalDiscr_ite hq) n := by
  obtain ⟨D, hD, rfl, hval⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hval n

end Sign

/-- Raising the level of `χ` preserves the signed conductor formula
`if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem conductor_ite_changeLevel [DecidableEq R] {N M : ℕ} [NeZero M] (hNM : N ∣ M)
    (χ : DirichletCharacter R N) :
    (if changeLevel hNM χ (-1) = 1 then ((changeLevel hNM χ).conductor : ℤ)
      else -(changeLevel hNM χ).conductor) =
      if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  rw [changeLevel_apply_neg_one, conductor_changeLevel]

/-! ### General-level consequences of agreement on coprime integers -/

/-- Lifting `χ` and `fundamentalDiscriminantCharCast R D hD` to `Nat.lcm N |D|` produces the same
character whenever `χ` agrees with `fundamentalDiscriminantCharCast R D hD` on all integers
coprime to `N`. -/
private theorem changeLevel_lcm_eq_of_forall_isCoprime {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    changeLevel (Nat.dvd_lcm_left N D.natAbs) χ =
      changeLevel (Nat.dvd_lcm_right N D.natAbs) (fundamentalDiscriminantCharCast R D hD) := by
  refine MulChar.ext' fun x ↦ ?_
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  refine apply_intCast_eq_of_forall_isCoprime rfl (fun m hm ↦ ?_) n
  have hmN : IsCoprime m N :=
    hm.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left N D.natAbs))
  rw [changeLevel_eq_cast_of_dvd' _ (Nat.dvd_lcm_left N D.natAbs) hm,
    changeLevel_eq_cast_of_dvd' _ (Nat.dvd_lcm_right N D.natAbs) hm, h m hmN]

/-- Any Dirichlet character of nonzero level `N` agreeing on integers coprime to `N` with the
character of a fundamental discriminant is quadratic. -/
theorem isQuadratic_of_forall_isCoprime_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    χ.IsQuadratic := by
  have : NeZero (N.lcm D.natAbs) := ⟨Nat.lcm_ne_zero (NeZero.ne N) hD.neZero_natAbs.ne⟩
  rw [← isQuadratic_changeLevel_iff (Nat.dvd_lcm_left N D.natAbs),
    changeLevel_lcm_eq_of_forall_isCoprime hD h]
  exact (fundamentalDiscriminantCharCast_isQuadratic hD).changeLevel _

/-- When `2 ≠ 0` in `R`, any Dirichlet character `χ` of nonzero level `N` agreeing on integers
coprime to `N` with `fundamentalDiscriminantCharCast R D hD` has conductor `|D|`. -/
theorem conductor_eq_natAbs_of_forall_isCoprime_apply_eq [NeZero (2 : R)] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    χ.conductor = D.natAbs := by
  have : NeZero (N.lcm D.natAbs) := ⟨Nat.lcm_ne_zero (NeZero.ne N) hD.neZero_natAbs.ne⟩
  have heq := congrArg conductor (changeLevel_lcm_eq_of_forall_isCoprime hD h)
  rwa [conductor_changeLevel, conductor_changeLevel,
    conductor_fundamentalDiscriminantCharCast] at heq

/-- **Naturality on coprime integers.** If `χ` agrees with `fundamentalDiscriminantCharCast R D hD`
on all integers coprime to `N`, then for `N ∣ M`, `changeLevel hNM χ` agrees with
`fundamentalDiscriminantCharCast R D hD` on all integers coprime to `M`. -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast_of_isCoprime {N M : ℕ}
    (hNM : N ∣ M) {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℤ} (hn : IsCoprime n M) :
    changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [changeLevel_eq_cast_of_dvd' χ hNM hn]
  exact h n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))

/-- At an odd natural number `m` coprime to `N`, a character agreeing with
`fundamentalDiscriminantCharCast R D hD` on integers coprime to `N` takes the cast of
`jacobiSym D m`. -/
theorem apply_natCast_eq_jacobiSym_of_forall_isCoprime {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {m : ℕ} (hm : _root_.Odd m) (hcop : m.Coprime N) :
    χ m = (jacobiSym D m : R) := by
  rw [← Int.cast_natCast m, h m (Nat.isCoprime_iff_coprime.mpr hcop),
    fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hm]

/-- At an odd natural number `m` coprime to `N`, a character agreeing with
`fundamentalDiscriminantCharCast R D hD` on integers coprime to `N` takes the cast of
`jacobiSym (fundamentalDiscriminantRadicand D) m`. -/
theorem apply_natCast_eq_jacobiSym_radicand_of_forall_isCoprime {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {m : ℕ} (hm : _root_.Odd m) (hcop : m.Coprime N) :
    χ m = (jacobiSym (fundamentalDiscriminantRadicand D) m : R) := by
  rw [apply_natCast_eq_jacobiSym_of_forall_isCoprime hD h hm hcop,
    jacobiSym_fundamentalDiscriminantRadicand hD hm]

/-- At an odd prime `p ∤ N`, a character agreeing with `fundamentalDiscriminantCharCast R D hD` on
integers coprime to `N` takes the cast of `legendreSym p D`. -/
theorem apply_prime_eq_legendreSym_of_forall_isCoprime {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  rw [apply_natCast_eq_jacobiSym_of_forall_isCoprime hD h
    ((Fact.out : p.Prime).odd_of_ne_two hp2) ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN),
    jacobiSym.legendreSym.to_jacobiSym]

/-- At an odd prime `p ∤ N`, a character agreeing with `fundamentalDiscriminantCharCast R D hD` on
integers coprime to `N` takes the cast of `legendreSym p (fundamentalDiscriminantRadicand D)`. -/
theorem apply_prime_eq_legendreSym_radicand_of_forall_isCoprime {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p (fundamentalDiscriminantRadicand D) : R) := by
  rw [apply_prime_eq_legendreSym_of_forall_isCoprime hD h hp2 hpN,
    legendreSym_fundamentalDiscriminantRadicand hD hp2]

/-- **Nonsquare criterion for the discriminant at an odd prime.** When `2 ≠ 0` in `R` and `p` is an
odd prime, a character `χ` agreeing on integers coprime to `N` with
`fundamentalDiscriminantCharCast R D hD` satisfies `χ p = -1` if and only if `p ∤ N` and `D` is not
a square in `ZMod p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (D : ZMod p) := by
  have hp : p.Prime := Fact.out
  have h01 : (-1 : R) ≠ 0 := fun h0 ↦ by
    have : Subsingleton R := subsingleton_of_zero_eq_one (neg_eq_zero.mp h0).symm
    exact NeZero.ne (2 : R) (Subsingleton.elim _ _)
  refine ⟨fun hχp ↦ ?_, fun ⟨hpN, hnsq⟩ ↦ ?_⟩
  · have hpN : ¬ p ∣ N := fun hdvd ↦ by
      have hnu : ¬ IsUnit (p : ZMod N) := by
        rw [ZMod.isUnit_iff_coprime, hp.coprime_iff_not_dvd]
        exact not_not.mpr hdvd
      exact h01 (hχp.symm.trans (χ.map_nonunit hnu))
    refine ⟨hpN, (legendreSym.eq_neg_one_iff p).mp ?_⟩
    rw [apply_prime_eq_legendreSym_of_forall_isCoprime hD h hp2 hpN] at hχp
    have htri : legendreSym p D = 0 ∨ legendreSym p D = 1 ∨ legendreSym p D = -1 := by
      rw [jacobiSym.legendreSym.to_jacobiSym]
      exact jacobiSym.trichotomy D p
    rcases htri with h0 | h1 | hm1
    · rw [h0, Int.cast_zero] at hχp
      exact absurd hχp.symm h01
    · rw [h1, Int.cast_one, eq_comm, neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hχp
      exact absurd hχp (NeZero.ne (2 : R))
    · exact hm1
  · rw [apply_prime_eq_legendreSym_of_forall_isCoprime hD h hp2 hpN,
      (legendreSym.eq_neg_one_iff p).mpr hnsq, Int.cast_neg, Int.cast_one]

/-- **Nonsquare criterion for the squarefree radicand at an odd prime.** When `2 ≠ 0` in `R` and
`p` is an odd prime, `χ p = -1` holds if and only if `p ∤ N` and
`fundamentalDiscriminantRadicand D` is not a square in `ZMod p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare_radicand [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (h : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare ((fundamentalDiscriminantRadicand D : ℤ) : ZMod p) := by
  rw [apply_prime_eq_neg_one_iff_not_isSquare hD h hp2,
    isSquare_fundamentalDiscriminantRadicand_zmod_iff hD ((Fact.out : p.Prime).odd_of_ne_two hp2)]

end DirichletCharacter

/-! ### The primitive discriminant of any quadratic Dirichlet character -/

namespace MulChar.IsQuadratic

open DirichletCharacter

variable {R : Type*} [CommRing R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- Two fundamental discriminants of absolute value `χ.conductor` that both agree with a quadratic
character `χ` on all integers coprime to `N` are equal. -/
theorem eq_of_isFundamentalDiscr_of_natAbs_eq_conductor (hχ : χ.IsQuadratic) {D₁ D₂ : ℤ}
    (hD₁ : Int.IsFundamentalDiscr D₁) (hD₂ : Int.IsFundamentalDiscr D₂)
    (hc₁ : D₁.natAbs = χ.conductor) (hc₂ : D₂.natAbs = χ.conductor)
    (h₁ : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D₁ hD₁ n)
    (h₂ : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D₂ hD₂ n) :
    D₁ = D₂ := by
  by_cases h2 : (2 : R) = 0
  · have hχ1 : χ = 1 := hχ.eq_one_of_two_eq_zero h2
    rw [hχ1, conductor_one] at hc₁ hc₂
    rw [hD₁.natAbs_eq_one_iff.mp hc₁, hD₂.natAbs_eq_one_iff.mp hc₂]
  · refine DirichletCharacter.eq_of_cast_sign_eq_of_natAbs_eq hD₁.ne_zero hD₂.ne_zero h2 ?_
      (hc₁.trans hc₂.symm)
    have hcop : IsCoprime (-1 : ℤ) N := IsCoprime.neg_left isCoprime_one_left
    have hs₁ : χ (-1) = (D₁.sign : R) := by
      simpa [fundamentalDiscriminantChar_neg_one] using h₁ (-1) hcop
    have hs₂ : χ (-1) = (D₂.sign : R) := by
      simpa [fundamentalDiscriminantChar_neg_one] using h₂ (-1) hcop
    exact hs₁.symm.trans hs₂

/-- **The primitive discriminant of a quadratic Dirichlet character.** Every quadratic Dirichlet
character `χ` of nonzero level `N` over a commutative ring `R` corresponds to a unique fundamental
discriminant `D` with `|D| = χ.conductor` such that `χ n = fundamentalDiscriminantCharCast R D hD n`
for every integer `n` coprime to `N` (Montgomery–Vaughan, Theorem 9.13). The principal character
corresponds to `D = 1`. -/
theorem existsUnique_isFundamentalDiscr_apply_eq (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, hDc, hval⟩ :=
    (primitiveCharacter_isPrimitive χ).exists_isFundamentalDiscr_apply_eq hχ.primitiveCharacter
  refine ⟨D, ⟨hD, hDc, fun n hn ↦ ?_⟩, fun D' ⟨hD', hD'c, hval'⟩ ↦
    hχ.eq_of_isFundamentalDiscr_of_natAbs_eq_conductor hD' hD hD'c hDc hval' fun n hn ↦ ?_⟩
  · rw [← χ.primitiveCharacter_apply_of_isCoprime hn, hval]
  · rw [← χ.primitiveCharacter_apply_of_isCoprime hn, hval]

/-- When `2 ≠ 0` in `R`, the conductor condition `|D| = χ.conductor` is automatic: there is a
unique fundamental discriminant `D` agreeing with `χ` on all integers coprime to `N`. -/
theorem existsUnique_isFundamentalDiscr_forall_isCoprime_apply_eq [NeZero (2 : R)]
    (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D,
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, ⟨hD, _, hval⟩, huniq⟩ := hχ.existsUnique_isFundamentalDiscr_apply_eq
  refine ⟨D, ⟨hD, hval⟩, fun D' ⟨hD', hval'⟩ ↦ huniq D' ⟨hD', ?_, hval'⟩⟩
  exact (conductor_eq_natAbs_of_forall_isCoprime_apply_eq hD' hval').symm

/-- **Naturality of the primitive discriminant under `changeLevel`.** For `N ∣ M` with `M ≠ 0`, a
fundamental discriminant `D` is the primitive discriminant of `DirichletCharacter.changeLevel hNM χ`
if and only if it is the primitive discriminant of `χ`. -/
theorem natAbs_eq_conductor_and_forall_changeLevel_apply_eq_iff (hχ : χ.IsQuadratic) {M : ℕ}
    [NeZero M] (hNM : N ∣ M) {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    (D.natAbs = (DirichletCharacter.changeLevel hNM χ).conductor ∧
      ∀ n : ℤ, IsCoprime n M →
        DirichletCharacter.changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n) ↔
      D.natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  refine ⟨fun ⟨hcM, hvalM⟩ ↦ ?_, fun ⟨hc, hval⟩ ↦
    ⟨by rw [conductor_changeLevel, hc], fun n hn ↦
      changeLevel_apply_eq_fundamentalDiscriminantCharCast_of_isCoprime hNM hD hval hn⟩⟩
  obtain ⟨D₀, ⟨hD₀, hc₀, hval₀⟩, -⟩ := hχ.existsUnique_isFundamentalDiscr_apply_eq
  have hDD₀ : D = D₀ :=
    (hχ.changeLevel hNM).eq_of_isFundamentalDiscr_of_natAbs_eq_conductor hD hD₀ hcM
      (by rw [conductor_changeLevel, hc₀]) hvalM fun n hn ↦
        changeLevel_apply_eq_fundamentalDiscriminantCharCast_of_isCoprime hNM hD₀ hval₀ hn
  subst hDD₀
  exact ⟨hc₀, hval₀⟩

/-- **Squarefree radicand form of the primitive discriminant.** Every quadratic Dirichlet character
`χ` of nonzero level `N` corresponds to a unique squarefree integer `d` with
`|fundamentalDiscriminant d| = χ.conductor` such that `χ` agrees with the character of
`fundamentalDiscriminant d` on all integers coprime to `N`. -/
theorem existsUnique_squarefree_apply_eq (hχ : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d, (fundamentalDiscriminant d).natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n =
        fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
          (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniq⟩ := hχ.existsUnique_isFundamentalDiscr_apply_eq
  refine ⟨fundamentalDiscriminantRadicand D,
    ⟨squarefree_fundamentalDiscriminantRadicand hD, ?_, fun n hn ↦ ?_⟩,
    fun d ⟨hd, hdc, hvald⟩ ↦ ?_⟩
  · rwa [fundamentalDiscriminant_fundamentalDiscriminantRadicand hD]
  · rw [hval n hn]
    exact DirichletCharacter.fundamentalDiscriminantCharCast_congr hD _
      (fundamentalDiscriminant_fundamentalDiscriminantRadicand hD).symm n
  · have hdD : fundamentalDiscriminant d = D :=
      huniq (fundamentalDiscriminant d)
        ⟨isFundamentalDiscr_fundamentalDiscriminant hd, hdc, hvald⟩
    rw [← hdD, fundamentalDiscriminantRadicand_fundamentalDiscriminant]

section Sign

variable [DecidableEq R]

/-- For every quadratic Dirichlet character `χ` of nonzero level `N`, the signed conductor
`if χ (-1) = 1 then χ.conductor else -χ.conductor` is a fundamental discriminant. -/
theorem isFundamentalDiscr_conductor_ite (hχ : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [DirichletCharacter.primitiveCharacter_apply_neg_one] using
    (primitiveCharacter_isPrimitive χ).isFundamentalDiscr_ite hχ.primitiveCharacter

/-- `χ.primitiveCharacter` is the character of the fundamental discriminant
`if χ (-1) = 1 then χ.conductor else -χ.conductor` at every integer `n`. -/
theorem primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite (hχ : χ.IsQuadratic)
    (n : ℤ) :
    χ.primitiveCharacter n =
      fundamentalDiscriminantCharCast R _ hχ.isFundamentalDiscr_conductor_ite n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [(primitiveCharacter_isPrimitive χ).apply_eq_fundamentalDiscriminantCharCast_ite
    hχ.primitiveCharacter n]
  exact DirichletCharacter.fundamentalDiscriminantCharCast_congr _ _
    (by rw [DirichletCharacter.primitiveCharacter_apply_neg_one]) n

/-- **Explicit primitive-discriminant formula at coprime integers.** For a quadratic Dirichlet
character `χ` of nonzero level `N` and any integer `n` coprime to `N`, `χ n` equals the character
of `D = if χ (-1) = 1 then χ.conductor else -χ.conductor` at `n`. -/
theorem apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime (hχ : χ.IsQuadratic)
    {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ hχ.isFundamentalDiscr_conductor_ite n := by
  rw [← χ.primitiveCharacter_apply_of_isCoprime hn,
    hχ.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite]

/-- The unique fundamental discriminant of `χ` equals
`if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem eq_ite_conductor_of_isFundamentalDiscr (hχ : χ.IsQuadratic) {D : ℤ}
    (hD : Int.IsFundamentalDiscr D) (hc : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor :=
  hχ.eq_of_isFundamentalDiscr_of_natAbs_eq_conductor hD hχ.isFundamentalDiscr_conductor_ite hc
    (by split_ifs <;> simp) hval fun _ hn ↦
      hχ.apply_eq_fundamentalDiscriminantCharCast_ite_of_isCoprime hn

end Sign

end MulChar.IsQuadratic

namespace DirichletCharacter

/-- A Dirichlet character `χ` of nonzero level `N` over a commutative ring `R` is quadratic if and
only if it agrees on all integers coprime to `N` with the character of a fundamental discriminant
of absolute value `χ.conductor`. -/
theorem isQuadratic_iff_exists_isFundamentalDiscr_apply_eq {R : Type*} [CommRing R] {N : ℕ}
    [NeZero N] (χ : DirichletCharacter R N) :
    χ.IsQuadratic ↔ ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n :=
  ⟨fun hχ ↦ hχ.existsUnique_isFundamentalDiscr_apply_eq.exists,
    fun ⟨_, hD, _, hval⟩ ↦ isQuadratic_of_forall_isCoprime_apply_eq hD hval⟩

end DirichletCharacter

/-! ### Concrete checks and examples -/

section Examples

open DirichletCharacter

private theorem isFundamentalDiscr_neg_three : Int.IsFundamentalDiscr (-3) := by
  simpa [oddPrimeDiscriminant_of_mod_four_eq_three (p := 3) (by decide)] using
    (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_three (by decide)).isFundamentalDiscr

private theorem isFundamentalDiscr_five : Int.IsFundamentalDiscr 5 := by
  simpa [oddPrimeDiscriminant_of_mod_four_eq_one (p := 5) (by decide)] using
    (isPrimeDiscriminant_oddPrimeDiscriminant (by decide : Nat.Prime 5)
      (by decide)).isFundamentalDiscr

private theorem isFundamentalDiscr_twelve : Int.IsFundamentalDiscr 12 := by
  have h := isPrimeDiscriminant_neg_four.isFundamentalDiscr.mul isFundamentalDiscr_neg_three
    (by decide)
  norm_num at h
  exact h

-- Small fundamental discriminants vs. `-12 = 4 * (-3)` with `-3 ≡ 1 (mod 4)`.
example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧
    Int.IsFundamentalDiscr 8 ∧ Int.IsFundamentalDiscr (-8) ∧
    Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) :=
  ⟨Int.isFundamentalDiscr_one, isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr, isPrimeDiscriminant_neg_eight.isFundamentalDiscr,
    isFundamentalDiscr_five, isFundamentalDiscr_neg_three, isFundamentalDiscr_twelve,
    fun h ↦ (h.2.1 (-3) (by norm_num)).2 (by norm_num)⟩

-- Running example of conductor `12`: `χ₄` times the Legendre character mod `3` has level `12`,
-- conductor `12`, fundamental discriminant `D = 12`, values `-1, -1, 1` at `5, 7, 11`, and the
-- same conductor and discriminant after lifting to level `24`.
example :
    let χ₁₂ : DirichletCharacter ℤ (Nat.lcm 4 3) :=
      DirichletCharacter.mul ZMod.χ₄ (quadraticChar (ZMod 3))
    χ₁₂.IsQuadratic ∧ χ₁₂.conductor = 12 ∧
      (if χ₁₂ (-1) = 1 then (χ₁₂.conductor : ℤ) else -χ₁₂.conductor) = 12 ∧
      χ₁₂ (5 : ℕ) = -1 ∧ χ₁₂ (7 : ℕ) = -1 ∧ χ₁₂ (11 : ℕ) = 1 ∧
      (changeLevel (by decide : Nat.lcm 4 3 ∣ 24) χ₁₂).conductor = 12 := by
  intro χ₁₂
  have : NeZero (Nat.lcm 4 3) := ⟨by decide⟩
  have hq : χ₁₂.IsQuadratic :=
    DirichletCharacter.isQuadratic_mul ZMod.isQuadratic_χ₄ (quadraticChar_isQuadratic (ZMod 3))
  have h12 : Int.IsFundamentalDiscr 12 := isFundamentalDiscr_twelve
  have hval : ∀ n : ℤ, IsCoprime n (Nat.lcm 4 3) →
      χ₁₂ n = fundamentalDiscriminantCharCast ℤ 12 h12 n := by
    intro n hn
    dsimp only [χ₁₂]
    rw [DirichletCharacter.mul, MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ hn,
      changeLevel_eq_cast_of_dvd' _ _ hn, fundamentalDiscriminantCharCast_apply]
    have hmul := fundamentalDiscriminantChar_mul isPrimeDiscriminant_neg_four.isFundamentalDiscr
      isFundamentalDiscr_neg_three (by decide : IsCoprime (-4 : ℤ) (-3)) n
    have hprod : (-4 : ℤ) * (-3) = 12 := by norm_num
    have h3 : quadraticChar (ZMod 3) (n : ZMod 3) = legendreSym 3 n := rfl
    rw [fundamentalDiscriminantChar_neg_four,
      fundamentalDiscriminantChar_neg_three isFundamentalDiscr_neg_three, ← h3] at hmul
    simpa [hprod] using hmul.symm
  have hcond : χ₁₂.conductor = 12 :=
    conductor_eq_natAbs_of_forall_isCoprime_apply_eq h12 hval
  have hD : 12 = if χ₁₂ (-1) = 1 then (χ₁₂.conductor : ℤ) else -χ₁₂.conductor :=
    hq.eq_ite_conductor_of_isFundamentalDiscr h12 (by omega) hval
  have h5 : χ₁₂ (5 : ℕ) = -1 := by
    have := apply_natCast_eq_jacobiSym_of_forall_isCoprime h12 hval (m := 5)
      (by decide) (by decide)
    norm_num at this
    exact this
  have h7 : χ₁₂ (7 : ℕ) = -1 := by
    have := apply_natCast_eq_jacobiSym_of_forall_isCoprime h12 hval (m := 7)
      (by decide) (by decide)
    norm_num at this
    exact this
  have h11 : χ₁₂ (11 : ℕ) = 1 := by
    have := apply_natCast_eq_jacobiSym_of_forall_isCoprime h12 hval (m := 11)
      (by decide) (by decide)
    norm_num at this
    exact this
  refine ⟨hq, hcond, hD.symm, h5, h7, h11, ?_⟩
  rw [conductor_changeLevel, hcond]

-- `χ₄` lifted to level `12` has conductor `4` and `D = -4`; at `3` (not coprime to `12`), the
-- lifted character vanishes while `χ_{-4}(3) = -1`.
example :
    let χ : DirichletCharacter ℤ 12 := changeLevel (by decide : 4 ∣ 12) ZMod.χ₄
    χ.conductor = 4 ∧ (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = -4 ∧
      χ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) =
        -1 := by
  intro χ
  have hc4 : DirichletCharacter.conductor ZMod.χ₄ = 4 :=
    conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
  have hc : χ.conductor = 4 := by rw [conductor_changeLevel, hc4]
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [conductor_ite_changeLevel, hc4]
    decide
  · exact χ.map_nonunit (by decide)
  · rw [fundamentalDiscriminantChar_neg_four]
    decide

-- The principal character at level `6` has conductor `1` and fundamental discriminant `D = 1`.
example :
    let χ : DirichletCharacter ℂ 6 := 1
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 := by
  simp [conductor_one, MulChar.one_apply isUnit_one.neg]

-- At conductor `8`, `D = 8` (`χ₈`) and `D = -8` (`χ₈'`) have the same `|D|` and opposite signs at
-- `-1`.
example :
    fundamentalDiscriminantChar 8 isPrimeDiscriminant_eight.isFundamentalDiscr (-1) = 1 ∧
      fundamentalDiscriminantChar (-8) isPrimeDiscriminant_neg_eight.isFundamentalDiscr (-1) =
        -1 := by
  rw [fundamentalDiscriminantChar_neg_one, fundamentalDiscriminantChar_neg_one]
  decide

-- Odd-prime dictionary (`D = 12`, radicand `d = 3`, at `p = 5` and ramified `p = 3`) vs. the
-- excluded prime `p = 2` (`χ_5(2) = -1` whereas `legendreSym 2 5 = 1`).
example :
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    fundamentalDiscriminantRadicand 12 = 3 ∧
      fundamentalDiscriminantRadicand (-4) = -1 ∧
      legendreSym 5 12 = -1 ∧ legendreSym 5 3 = -1 ∧
      legendreSym 3 12 = 0 ∧ legendreSym 3 3 = 0 ∧
      fundamentalDiscriminantChar 5 isFundamentalDiscr_five 2 = -1 ∧
      legendreSym 2 5 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨by norm_num [fundamentalDiscriminantRadicand_def],
    by norm_num [fundamentalDiscriminantRadicand_def],
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, by norm_num⟩
  rw [fundamentalDiscriminantChar_two]
  decide

end Examples
