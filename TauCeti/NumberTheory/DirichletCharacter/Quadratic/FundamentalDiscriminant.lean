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
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.OddPrimePower.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# Quadratic Dirichlet characters and fundamental discriminants

Every quadratic Dirichlet character `χ` of positive level `N` (with values in any commutative ring
`R`) is induced by the Kronecker character of a unique fundamental discriminant `D` with
`|D| = χ.conductor`: at every integer `n` coprime to `N`,
`χ n = fundamentalDiscriminantCharCast R D hD n`, so `χ` is the lift via `changeLevel` of
`fundamentalDiscriminantCharCast R D hD` from level `|D| ∣ N` to level `N`. Explicitly,
`D = χ.conductor` when `χ (-1) = 1` and `D = -χ.conductor` otherwise — this holds in every
commutative ring, including characteristic `2` (where every quadratic character is principal and
`D = 1`). When `2 ≠ 0` in `R`, agreement with `fundamentalDiscriminantCharCast R D hD` on integers
coprime to `N` alone forces `|D| = χ.conductor`, so `D` is unique even without fixing `|D|`.

For complex (or any `RCLike`-valued) characters, `MulChar.isQuadratic_iff_forall_im_eq_zero` (in
`TauCeti.NumberTheory.MulChar.Real`) and `DirichletCharacter.isQuadratic_of_forall_im_eq_zero`
identify real-valued characters with quadratic ones, so the classification applies directly to
every real Dirichlet character. The principal character is included at every positive level `N`,
with `χ.conductor = 1` and `D = 1`.

For primitive `χ`, the proof is local. At a prime power `p ^ k`, `k ≠ 0`, a primitive quadratic
character is the Legendre character modulo `p` (so `k = 1`) when `p` is odd, and `χ₄`, `χ₈` or
`χ₈'` (so `k = 2` or `k = 3`) when `p = 2`; in each case it is the character of a prime
discriminant `p*`, `-4`, `8` or `-8` of absolute value `p ^ k`. The local factors of a primitive
character are primitive, and the character of a product of prime discriminants at distinct primes
is the product of their characters, so `D` is the product of the prime discriminants of the local
factors. For a general character `χ`, passing to `χ.primitiveCharacter` reduces immediately to the
primitive case.

Via the bijection `fundamentalDiscriminantEquiv` between squarefree integers `d` and fundamental
discriminants `D = fundamentalDiscriminant d`, the classification also attaches a unique
squarefree radicand `d` to `χ`, with `d = 1 ↔ χ = 1`, `|d| ≤ χ.conductor`,
`χ n = (jacobiSym d n : R)` for every odd `n` coprime to `N`, and `χ p = (legendreSym p d : R)`
for every odd prime `p ∤ N`. Whenever `2 ≠ 0` in `R`, the value `χ p = -1` at an odd prime `p`
automatically implies `p ∤ N` and `¬ IsSquare (D : ZMod p)` (equivalently
`¬ IsSquare (d : ZMod p)`).

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of absolute
  value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a unique fundamental discriminant of absolute
  value `N`.
* `DirichletCharacter.eq_ite_conductor_of_isFundamentalDiscr`,
  `DirichletCharacter.natAbs_eq_conductor_of_apply_eq_fundamentalDiscriminantCharCast`: uniqueness
  of `D` as the signed conductor `χ (-1) · χ.conductor` (at any characteristic when
  `|D| = χ.conductor`, and without fixing `|D|` whenever `2 ≠ 0`).
* `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq_of_neZero_two`: arbitrary-level
  existence and uniqueness of the primitive fundamental discriminant of a quadratic character.
* `DirichletCharacter.natAbs_ite_conductor`,
  `DirichletCharacter.isFundamentalDiscr_ite_conductor`,
  `DirichletCharacter.apply_eq_fundamentalDiscriminantCharCast_ite_conductor`,
  `DirichletCharacter.eq_changeLevel_fundamentalDiscriminantCharCast_ite_conductor`,
  `DirichletCharacter.ite_conductor_eq_one_iff`: explicit signed-conductor form and lift identity.
* `DirichletCharacter.ite_conductor_changeLevel`,
  `DirichletCharacter.changeLevel_apply_eq_fundamentalDiscriminantCharCast`: naturality under
  `changeLevel`.
* `DirichletCharacter.existsUnique_squarefree_apply_eq_fundamentalDiscriminantCharCast`,
  `DirichletCharacter.exists_squarefree_apply_eq_legendreSym`: squarefree-radicand form and
  odd-prime Legendre / odd-integer Jacobi dictionary.
* `DirichletCharacter.not_isSquare_of_apply_natCast_eq_neg_one`,
  `DirichletCharacter.apply_natCast_eq_neg_one_iff_not_isSquare`,
  `DirichletCharacter.isSquare_of_apply_natCast_eq_one`,
  `DirichletCharacter.apply_natCast_eq_one_iff_isSquare`: nonsquare and square criteria at odd
  primes when `2 ≠ 0`.

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

/-! ### Arbitrary level, uniqueness, and the signed-conductor formula -/

/-- The signed conductor `if χ (-1) = 1 then χ.conductor else -χ.conductor` has absolute value
`χ.conductor`. -/
@[simp]
theorem natAbs_ite_conductor [DecidableEq R] {N : ℕ} (χ : DirichletCharacter R N) :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)).natAbs =
      χ.conductor := by
  split_ifs <;> simp

/-- **Uniqueness of the primitive discriminant.** If a fundamental discriminant `D` has
`|D| = χ.conductor` and its character agrees with `χ` at all integers coprime to `N`, then `D` is
`χ.conductor` when `χ (-1) = 1` and `-χ.conductor` otherwise. No hypothesis on the characteristic
of `R` is needed: when `2 = 0` in `R`, `χ` is quadratic hence principal, so `χ.conductor = 1` and
`D = 1`. -/
theorem eq_ite_conductor_of_isFundamentalDiscr [DecidableEq R] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hDc : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ) := by
  have : NeZero N := ⟨by
    rintro rfl
    rw [conductor_eq_zero_iff_level_eq_zero.mpr rfl] at hDc
    exact hD.ne_zero (Int.natAbs_eq_zero.mp hDc)⟩
  have hEq : χ = changeLevel (hDc.symm ▸ χ.conductor_dvd_level)
      (fundamentalDiscriminantCharCast R D hD) :=
    (eq_changeLevel_iff_forall_isCoprime _).mpr hval
  have hq : χ.IsQuadratic := by
    rw [hEq]
    exact (fundamentalDiscriminantCharCast_isQuadratic hD).changeLevel _
  by_cases h2 : (2 : R) = 0
  · have hχ1 : χ = 1 := hq.eq_one_of_two_eq_zero h2
    have hc1 : χ.conductor = 1 := by rw [hχ1, conductor_one]
    have hD1 : D = 1 := hD.natAbs_eq_one_iff.mp (hDc.trans hc1)
    have hneg1 : χ (-1) = 1 := by rw [hχ1]; exact MulChar.one_apply isUnit_one.neg
    simp [hD1, hc1, hneg1]
  · have hsign : χ (-1) = D.sign := by
      simpa [fundamentalDiscriminantChar_neg_one] using
        hval (-1) (IsCoprime.neg_left isCoprime_one_left)
    split_ifs with h1 <;> rw [hsign] at h1 <;> rcases hD.ne_zero.lt_or_gt with h | h
    · rw [Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero,
        one_add_one_eq_two] at h1
      exact absurd h1 h2
    · omega
    · omega
    · rw [Int.sign_eq_one_of_pos h, Int.cast_one] at h1
      exact absurd rfl h1

/-- When `2 ≠ 0` in `R`, any fundamental discriminant `D` whose character agrees with `χ` on
integers coprime to `N` automatically satisfies `|D| = χ.conductor` (and hence `|D| ∣ N`). -/
theorem natAbs_eq_conductor_of_apply_eq_fundamentalDiscriminantCharCast [NeZero (2 : R)]
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D.natAbs = χ.conductor := by
  have := hD.neZero_natAbs
  have : NeZero (Nat.lcm N D.natAbs) := ⟨Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne D.natAbs)⟩
  have hlcm :
      changeLevel (Nat.dvd_lcm_left N D.natAbs) χ =
        changeLevel (Nat.dvd_lcm_right N D.natAbs) (fundamentalDiscriminantCharCast R D hD) := by
    refine MulChar.ext fun u ↦ ?_
    obtain ⟨n, hn⟩ := ZMod.intCast_surjective (u : ZMod (Nat.lcm N D.natAbs))
    have hcop : IsCoprime n (Nat.lcm N D.natAbs : ℕ) := by
      rw [isCoprime_comm, ← ZMod.isUnit_intCast_iff_isCoprime, hn]
      exact u.isUnit
    have hcopN : IsCoprime n N :=
      hcop.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr (Nat.dvd_lcm_left N D.natAbs))
    rw [← hn, changeLevel_eq_cast_of_dvd' χ _ hcop,
      changeLevel_eq_cast_of_dvd' (fundamentalDiscriminantCharCast R D hD) _ hcop, hval n hcopN]
  have hcond := congrArg conductor hlcm
  rw [conductor_changeLevel, conductor_changeLevel, conductor_fundamentalDiscriminantCharCast hD]
    at hcond
  exact hcond.symm

/-- For every quadratic character `χ` of positive level `N`, the signed conductor
`if χ (-1) = 1 then χ.conductor else -χ.conductor` is a fundamental discriminant. -/
theorem isFundamentalDiscr_ite_conductor [DecidableEq R] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, hDc, hprim⟩ :=
    (primitiveCharacter_isPrimitive χ).exists_isFundamentalDiscr_apply_eq hq.primitiveCharacter
  have hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n :=
    fun n hn ↦ by rw [← primitiveCharacter_apply_of_isCoprime χ hn, hprim n]
  rwa [← eq_ite_conductor_of_isFundamentalDiscr hD hDc hval]

/-- Every quadratic character `χ` of positive level `N` agrees on integers coprime to `N` with the
character of the fundamental discriminant `if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem apply_eq_fundamentalDiscriminantCharCast_ite_conductor [DecidableEq R] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_ite_conductor hq) n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, hDc, hprim⟩ :=
    (primitiveCharacter_isPrimitive χ).exists_isFundamentalDiscr_apply_eq hq.primitiveCharacter
  have hval : ∀ m : ℤ, IsCoprime m N → χ m = fundamentalDiscriminantCharCast R D hD m :=
    fun m hm ↦ by rw [← primitiveCharacter_apply_of_isCoprime χ hm, hprim m]
  have hEq := eq_ite_conductor_of_isFundamentalDiscr hD hDc hval
  cases hEq
  exact hval n hn

/-- Every quadratic character `χ` of positive level `N` is the lift via `changeLevel` of the
primitive character attached to its signed conductor `χ (-1) · χ.conductor`. -/
theorem eq_changeLevel_fundamentalDiscriminantCharCast_ite_conductor [DecidableEq R]
    {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    χ = changeLevel ((natAbs_ite_conductor χ).symm ▸ χ.conductor_dvd_level)
      (fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_ite_conductor hq)) :=
  (eq_changeLevel_iff_forall_isCoprime _).mpr fun _ hn ↦
    apply_eq_fundamentalDiscriminantCharCast_ite_conductor hq hn

/-- The signed conductor of a Dirichlet character of positive level is `1` if and only if the
character is principal. -/
theorem ite_conductor_eq_one_iff [DecidableEq R] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = 1 ↔ χ = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · split_ifs at h with h1
    · exact eq_one_iff_conductor_eq_one.mpr (by omega)
    · omega
  · subst h
    have hneg1 : (1 : DirichletCharacter R N) (-1) = 1 := MulChar.one_apply isUnit_one.neg
    simp [hneg1, conductor_one]

/-- **The primitive discriminant of a quadratic character.** Every quadratic Dirichlet character
`χ` of positive level `N` determines a unique fundamental discriminant `D` with
`|D| = χ.conductor` such that `χ n = fundamentalDiscriminantCharCast R D hD n` at every integer
`n` coprime to `N` (Montgomery–Vaughan, Theorem 9.13). The principal character is included at
every positive level, with `D = 1`. -/
theorem existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  refine ⟨if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ),
    ⟨isFundamentalDiscr_ite_conductor hq, natAbs_ite_conductor χ,
      fun _ hn ↦ apply_eq_fundamentalDiscriminantCharCast_ite_conductor hq hn⟩, ?_⟩
  rintro D ⟨hD, hDc, hval⟩
  exact eq_ite_conductor_of_isFundamentalDiscr hD hDc hval

/-- When `2 ≠ 0` in `R`, a quadratic Dirichlet character `χ` of positive level `N` determines a
unique fundamental discriminant `D` whose character agrees with `χ` on integers coprime to `N`,
without fixing `|D| = χ.conductor` in advance (that equality holds automatically). -/
theorem existsUnique_isFundamentalDiscr_apply_eq_of_neZero_two [NeZero (2 : R)] {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D,
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, ⟨hD, -, hval⟩, huniq⟩ := existsUnique_isFundamentalDiscr_apply_eq hq
  refine ⟨D, ⟨hD, hval⟩, ?_⟩
  rintro D' ⟨hD', hval'⟩
  exact huniq D' ⟨hD',
    natAbs_eq_conductor_of_apply_eq_fundamentalDiscriminantCharCast hD' hval', hval'⟩

section PrimitiveSign

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- A primitive quadratic character `χ` of level `N ≠ 0` is the character of a unique fundamental
discriminant `D` with `|D| = N`. -/
theorem IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = N ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniq⟩ :=
    DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq hq
  have hDN : D.natAbs = N := hDc.trans ((isPrimitive_def χ).mp hχ)
  refine ⟨D, ⟨hD, hDN, apply_intCast_eq_of_forall_isCoprime hDN.symm hval⟩, ?_⟩
  rintro D' ⟨hD', hD'N, hval'⟩
  exact huniq D' ⟨hD', hD'N.trans ((isPrimitive_def χ).mp hχ).symm, fun n _ ↦ hval' n⟩

/-- The integer `χ (-1) N`, that is `N` if `χ (-1) = 1` and `-N` otherwise, is a fundamental
discriminant for every primitive quadratic character `χ` of level `N`. -/
theorem IsPrimitive.isFundamentalDiscr_ite [DecidableEq R] (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (N : ℤ) else -N) := by
  simpa [(isPrimitive_def χ).mp hχ] using isFundamentalDiscr_ite_conductor hq

/-- **Primitive quadratic characters are Kronecker characters, with their discriminant.** A
primitive quadratic character `χ` of level `N` is the character of the fundamental discriminant
`D = χ (-1) N`: `χ n = fundamentalDiscriminantCharCast R D n` at every integer `n`. For the
principal character, primitive only at level `1`, this is `D = 1`. -/
theorem IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite [DecidableEq R]
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (n : ℤ) :
    χ n = fundamentalDiscriminantCharCast R _ (hχ.isFundamentalDiscr_ite hq) n := by
  obtain ⟨D, hD, hDN, hprim⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  have hEq := eq_ite_conductor_of_isFundamentalDiscr hD
    (hDN.trans ((isPrimitive_def χ).mp hχ).symm) (fun m _ ↦ hprim m)
  rw [(isPrimitive_def χ).mp hχ] at hEq
  cases hEq
  exact hprim n

end PrimitiveSign

/-! ### Naturality under `changeLevel` -/

/-- Lifting a Dirichlet character to a nonzero multiple level leaves its signed conductor
`if χ (-1) = 1 then χ.conductor else -χ.conductor` unchanged. In particular, a quadratic
character and any lift of it share the same primitive fundamental discriminant. -/
theorem ite_conductor_changeLevel [DecidableEq R] {N M : ℕ} [NeZero M] (hNM : N ∣ M)
    (χ : DirichletCharacter R N) :
    (if changeLevel hNM χ (-1) = 1 then ((changeLevel hNM χ).conductor : ℤ)
      else -((changeLevel hNM χ).conductor : ℤ)) =
      if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ) := by
  rw [changeLevel_apply_neg_one, conductor_changeLevel]

/-- If `χ` at level `N` agrees with the character of `D` on integers coprime to `N`, then its lift
`changeLevel hNM χ` to a multiple level `M` agrees with the character of the same `D` on integers
coprime to `M`. -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast {N M : ℕ} (hNM : N ∣ M)
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℤ} (hn : IsCoprime n M) :
    changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [changeLevel_eq_cast_of_dvd' χ hNM hn]
  exact hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))

/-! ### The odd-prime dictionary and squarefree-radicand form -/

/-- **The squarefree radicand of a quadratic character.** Every quadratic Dirichlet character `χ`
of positive level `N` determines a unique squarefree integer `d` such that
`D = fundamentalDiscriminant d` satisfies `|D| = χ.conductor` and
`χ n = fundamentalDiscriminantCharCast R D _ n` at every integer `n` coprime to `N`. -/
theorem existsUnique_squarefree_apply_eq_fundamentalDiscriminantCharCast {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d,
      (fundamentalDiscriminant d).natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N →
        χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
          (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniq⟩ := existsUnique_isFundamentalDiscr_apply_eq hq
  obtain ⟨d, ⟨hd, rfl⟩, -⟩ := existsUnique_squarefree_fundamentalDiscriminant_eq hD
  refine ⟨d, ⟨hd, hDc, hval⟩, ?_⟩
  rintro d' ⟨hd', hDc', hval'⟩
  exact fundamentalDiscriminant_injective
    (huniq _ ⟨isFundamentalDiscr_fundamentalDiscriminant hd', hDc', hval'⟩)

/-- If `χ` agrees with the character of `D` on integers coprime to `N`, then at every odd natural
number `m` coprime to `N`, `χ m` is the Jacobi symbol `(jacobiSym D m : R)`. -/
theorem apply_natCast_eq_jacobiSym_of_apply_eq_fundamentalDiscriminantCharCast {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {m : ℕ} (hm : _root_.Odd m) (hmN : m.Coprime N) :
    χ m = (jacobiSym D m : R) := by
  have h := hval m (Nat.isCoprime_iff_coprime.mpr hmN)
  rw [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hm] at h
  simpa using h

/-- If `χ` agrees with the character of `D` on integers coprime to `N`, then at every odd prime
`p ∤ N`, `χ p` is the Legendre symbol `(legendreSym p D : R)`. -/
theorem apply_natCast_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  have h := hval p
    (Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN))
  rw [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2] at h
  simpa using h

/-- **Squarefree-radicand Legendre form of a quadratic character.** For any quadratic Dirichlet
character `χ` of positive level `N`, there is a squarefree integer `d` with `d = 1 ↔ χ = 1`,
`|d| ≤ χ.conductor`, `χ n = (jacobiSym d n : R)` for every odd `n` coprime to `N`,
and `χ p = (legendreSym p d : R)` for every odd prime `p ∤ N`. -/
theorem exists_squarefree_apply_eq_legendreSym {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃ d : ℤ, Squarefree d ∧ (d = 1 ↔ χ = 1) ∧ d.natAbs ≤ χ.conductor ∧
      (∀ n : ℕ, _root_.Odd n → n.Coprime N → χ n = (jacobiSym d n : R)) ∧
      (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ N → χ p = (legendreSym p d : R)) := by
  obtain ⟨d, ⟨hd, hDc, hval⟩, -⟩ :=
    existsUnique_squarefree_apply_eq_fundamentalDiscriminantCharCast hq
  have hD := isFundamentalDiscr_fundamentalDiscriminant hd
  refine ⟨d, hd, ?_, (natAbs_le_natAbs_fundamentalDiscriminant d).trans_eq hDc,
    fun n hn hnN ↦ ?_, fun p _ hp2 hpN ↦ ?_⟩
  · rw [← fundamentalDiscriminant_eq_one_iff, ← hD.natAbs_eq_one_iff, hDc,
      ← eq_one_iff_conductor_eq_one]
  · rw [apply_natCast_eq_jacobiSym_of_apply_eq_fundamentalDiscriminantCharCast hval hn hnN,
      jacobiSym_fundamentalDiscriminant d hn]
  · rw [apply_natCast_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast hval hp2 hpN,
      legendreSym_fundamentalDiscriminant d hp2]

/-! ### Nonsquare and square criteria at odd primes -/

section Nonsquare

variable [NeZero (2 : R)]

/-- If `χ` agrees with the character of a fundamental discriminant `D` on integers coprime to `N`,
and `χ p = -1` at an odd prime `p` (with `2 ≠ 0` in `R`), then `D` is not a square modulo `p`.
No divisibility hypothesis `¬ p ∣ N` is required: `χ p = -1 ≠ 0` already forces `p ∤ N`. -/
theorem not_isSquare_of_apply_natCast_eq_neg_one {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hχp : χ p = -1) :
    ¬ IsSquare (D : ZMod p) := by
  have : Nontrivial R := nontrivial_of_ne _ _ (NeZero.ne (2 : R))
  have hu : IsUnit (p : ZMod N) := by
    by_contra hnu
    exact neg_ne_zero.mpr one_ne_zero (hχp ▸ χ.map_nonunit hnu)
  have hcop : IsCoprime (p : ℤ) N := by
    rw [isCoprime_comm, ← ZMod.isUnit_intCast_iff_isCoprime]
    simpa using hu
  have hleg : (legendreSym p D : R) = -1 := by
    have h := hval p hcop
    rw [fundamentalDiscriminantCharCast_apply,
      fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2] at h
    simpa [hχp] using h.symm
  intro hsq
  by_cases hD0 : (D : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p D).mpr hD0, Int.cast_zero] at hleg
    exact neg_ne_zero.mpr one_ne_zero hleg.symm
  · rw [(legendreSym.eq_one_iff p hD0).mpr hsq, Int.cast_one, eq_comm,
      neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hleg
    exact NeZero.ne (2 : R) hleg

/-- At an odd prime `p ∤ N` (with `2 ≠ 0` in `R`), `χ p = -1` holds if and only if the
associated fundamental discriminant `D` is not a square modulo `p`. -/
theorem apply_natCast_eq_neg_one_iff_not_isSquare {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = -1 ↔ ¬ IsSquare (D : ZMod p) := by
  refine ⟨not_isSquare_of_apply_natCast_eq_neg_one hval hp2, fun hns ↦ ?_⟩
  rw [apply_natCast_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast hval hp2 hpN,
    (legendreSym.eq_neg_one_iff p).mpr hns, Int.cast_neg, Int.cast_one]

/-- If `χ` agrees with the character of a fundamental discriminant `D` on integers coprime to `N`,
and `χ p = 1` at an odd prime `p` (with `2 ≠ 0` in `R`), then `D` is a square modulo `p`. -/
theorem isSquare_of_apply_natCast_eq_one {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hχp : χ p = 1) :
    IsSquare (D : ZMod p) := by
  have : Nontrivial R := nontrivial_of_ne _ _ (NeZero.ne (2 : R))
  have hu : IsUnit (p : ZMod N) := by
    by_contra hnu
    exact one_ne_zero (hχp ▸ χ.map_nonunit hnu)
  have hcop : IsCoprime (p : ℤ) N := by
    rw [isCoprime_comm, ← ZMod.isUnit_intCast_iff_isCoprime]
    simpa using hu
  have hleg : (legendreSym p D : R) = 1 := by
    have h := hval p hcop
    rw [fundamentalDiscriminantCharCast_apply,
      fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2] at h
    simpa [hχp] using h.symm
  by_contra hns
  rw [(legendreSym.eq_neg_one_iff p).mpr hns, Int.cast_neg, Int.cast_one,
    neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hleg
  exact NeZero.ne (2 : R) hleg

/-- At an odd prime `p ∤ N` (with `2 ≠ 0` in `R`), `χ p = 1` holds if and only if the
associated fundamental discriminant `D` is a square modulo `p`. Since `|D| = χ.conductor ∣ N`,
`p ∤ N` automatically guarantees `(D : ZMod p) ≠ 0`. -/
theorem apply_natCast_eq_one_iff_isSquare {N : ℕ} {χ : DirichletCharacter R N}
    {D : ℤ} {hD : Int.IsFundamentalDiscr D}
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = 1 ↔ IsSquare (D : ZMod p) := by
  refine ⟨isSquare_of_apply_natCast_eq_one hval hp2, fun hsq ↦ ?_⟩
  have : NeZero N := ⟨fun h ↦ hpN (h ▸ dvd_zero p)⟩
  have hDN : D.natAbs ∣ N :=
    (natAbs_eq_conductor_of_apply_eq_fundamentalDiscriminantCharCast hD hval).symm ▸
      χ.conductor_dvd_level
  have hD0 : (D : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
    exact fun h ↦ hpN (h.trans hDN)
  rw [apply_natCast_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast hval hp2 hpN,
    (legendreSym.eq_one_iff p hD0).mpr hsq, Int.cast_one]

end Nonsquare

/-! ### Checks -/

-- Concrete fundamental discriminants and non-examples.
example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧ Int.IsFundamentalDiscr 8 ∧
    Int.IsFundamentalDiscr (-8) ∧ Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) ∧
    ¬ Int.IsFundamentalDiscr (-1) := by
  have h3 : Squarefree (3 : ℤ) := Int.squarefree_natAbs.mp Nat.prime_three.prime.squarefree
  have h5 : Squarefree (5 : ℤ) := Int.squarefree_natAbs.mp Nat.prime_five.prime.squarefree
  refine ⟨Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by norm_num, squarefree_one⟩),
    isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr,
    isPrimeDiscriminant_neg_eight.isFundamentalDiscr,
    Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by norm_num, h5⟩),
    Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨by norm_num, by simpa using h3.neg⟩),
    Int.isFundamentalDiscr_four_mul.mpr ⟨h3, by norm_num⟩, ?_, ?_⟩
  · intro h
    rcases Int.isFundamentalDiscr_iff_squarefree.mp h with ⟨h1, _⟩ | ⟨_, _, hmod⟩ <;> omega
  · intro h
    have := h.emod_four_eq_zero_or_one
    omega

-- Imprimitive lift: `χ₄` lifted to level `12` has conductor `4`, `χ (-1) = -1`, primitive
-- discriminant `D = -4`, agrees with `χ_{-4}` at integers coprime to `12`, and disagrees at `3`.
example :
    let χ : DirichletCharacter ℤ 12 := changeLevel (by decide : 4 ∣ 12) ZMod.χ₄
    let h4 : Int.IsFundamentalDiscr (-4) := isPrimeDiscriminant_neg_four.isFundamentalDiscr
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -(χ.conductor : ℤ)) = -4 ∧
      (∀ n : ℤ, IsCoprime n 12 →
        χ n = fundamentalDiscriminantCharCast ℤ (-4) h4 n) ∧
      χ (3 : ℤ) ≠ fundamentalDiscriminantCharCast ℤ (-4) h4 (3 : ℤ) := by
  intro χ h4
  have hcond : conductor (ZMod.χ₄ : DirichletCharacter ℤ 4) = 4 :=
    conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
  have hneg : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
  refine ⟨?_, fun n hn ↦ ?_, ?_⟩
  · rw [ite_conductor_changeLevel, hcond, hneg]
    norm_num
  · rw [changeLevel_eq_cast_of_dvd' ZMod.χ₄ (by decide : 4 ∣ 12) hn,
      fundamentalDiscriminantCharCast_apply, Int.cast_id]
    exact (fundamentalDiscriminantChar_neg_four n).symm
  · have h0 : χ (3 : ℤ) = 0 :=
      χ.map_nonunit (by rw [ZMod.isUnit_intCast_iff_isCoprime]; decide)
    have hv : fundamentalDiscriminantCharCast ℤ (-4) h4 (3 : ℤ) = -1 := by
      rw [fundamentalDiscriminantCharCast_apply, Int.cast_id, fundamentalDiscriminantChar_neg_four]
      decide
    rw [h0, hv]
    norm_num

-- Principal character at composite level `6`: primitive discriminant is `1` (not `-1`).
example :
    (if (1 : DirichletCharacter ℤ 6) (-1) = 1 then
        ((1 : DirichletCharacter ℤ 6).conductor : ℤ)
      else -((1 : DirichletCharacter ℤ 6).conductor : ℤ)) = 1 :=
  ite_conductor_eq_one_iff.mpr rfl

-- Same conductor `8`, opposite signs: `χ₈` (`D = 8`) vs `χ₈'` (`D = -8`).
example :
    let χ₈ : DirichletCharacter ℤ 8 := ZMod.χ₈
    let χ₈' : DirichletCharacter ℤ 8 := ZMod.χ₈'
    (if χ₈ (-1) = 1 then (χ₈.conductor : ℤ) else -(χ₈.conductor : ℤ)) = 8 ∧
    (if χ₈' (-1) = 1 then (χ₈'.conductor : ℤ) else -(χ₈'.conductor : ℤ)) = -8 := by
  intro χ₈ χ₈'
  have h8 : χ₈.conductor = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five χ₈ (by decide)
  have h8' : χ₈'.conductor = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five χ₈' (by decide)
  have hneg8 : χ₈ (-1 : ZMod 8) = 1 := by decide
  have hneg8' : χ₈' (-1 : ZMod 8) = -1 := by decide
  rw [h8, h8', hneg8, hneg8']
  norm_num

-- Odd-prime dictionary for `D = 12 = fundamentalDiscriminant 3`: `p = 5` is inert
-- (`χ₁₂(5) = -1`, `3` is not a square mod `5`), while `p = 3` is ramified (`χ₁₂(3) = 0`).
example (h12 : Int.IsFundamentalDiscr 12) :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    fundamentalDiscriminantCharCast ℤ 12 h12 (5 : ℕ) = (legendreSym 5 3 : ℤ) ∧
      ¬ IsSquare ((3 : ℤ) : ZMod 5) ∧
      fundamentalDiscriminantCharCast ℤ 12 h12 (3 : ℕ) = 0 := by
  intro _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfd : fundamentalDiscriminant 3 = 12 := by
    rw [fundamentalDiscriminant_of_mod_four_ne_one (by norm_num)]
    norm_num
  have h5 : fundamentalDiscriminantCharCast ℤ 12 h12 (5 : ℕ) = legendreSym 5 3 := by
    rw [fundamentalDiscriminantCharCast_apply, Int.cast_id]
    have h := (fundamentalDiscriminantChar_natCast_eq_legendreSym h12 (q := 5) (by decide)).trans
      (hfd ▸ legendreSym_fundamentalDiscriminant 3 (p := 5) (by decide))
    simpa using h
  have hns : ¬ IsSquare ((3 : ℤ) : ZMod 5) := by
    rw [← isSquare_fundamentalDiscriminant_zmod_iff 3 (by decide : _root_.Odd 5), hfd]
    exact not_isSquare_of_apply_natCast_eq_neg_one
      (χ := fundamentalDiscriminantCharCast ℤ 12 h12) (hD := h12) (fun _ _ ↦ rfl) (by decide)
      (by rw [h5]; decide)
  have h30 : fundamentalDiscriminantCharCast ℤ 12 h12 (3 : ℕ) = 0 := by
    rw [fundamentalDiscriminantCharCast_apply, Int.cast_id]
    have h := (fundamentalDiscriminantChar_natCast_eq_legendreSym h12 (q := 3) (by decide)).trans
      (hfd ▸ legendreSym_fundamentalDiscriminant 3 (p := 3) (by decide))
    simpa using h.trans ((legendreSym.eq_zero_iff 3 3).mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd 3 3).mpr dvd_rfl))
  exact ⟨h5, hns, h30⟩

-- Sharpness of `p ≠ 2`: `χ₅(2) = -1`, yet `5 ≡ 1 = 1^2` is a square modulo `2`.
example :
    let h5 : Int.IsFundamentalDiscr 5 :=
      Int.isFundamentalDiscr_iff_squarefree.mpr
        (Or.inl ⟨by norm_num, Int.squarefree_natAbs.mp Nat.prime_five.prime.squarefree⟩)
    fundamentalDiscriminantCharCast ℤ 5 h5 (2 : ℕ) = -1 ∧ IsSquare (5 : ZMod 2) := by
  intro h5
  refine ⟨?_, ⟨1, by decide⟩⟩
  rw [fundamentalDiscriminantCharCast_apply, Int.cast_id]
  simpa using fundamentalDiscriminantChar_two (D := 5) h5

-- Real complex character pipeline: a real-valued complex Dirichlet character has a unique
-- fundamental discriminant `D`, and `χ p = -1` at an odd prime `p` gives
-- `¬ IsSquare (D : ZMod p)`.
example {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hreal : ∀ a, (χ a).im = 0)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hχp : χ p = -1) :
    ∃ (D : ℤ), Int.IsFundamentalDiscr D ∧ D.natAbs = χ.conductor ∧
      ¬ IsSquare (D : ZMod p) := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, -⟩ :=
    existsUnique_isFundamentalDiscr_apply_eq (isQuadratic_of_forall_im_eq_zero χ hreal)
  exact ⟨D, hD, hDc, not_isSquare_of_apply_natCast_eq_neg_one hval hp2 hχp⟩

end DirichletCharacter
