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
import TauCeti.NumberTheory.DirichletCharacter.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# Quadratic Dirichlet characters and their primitive fundamental discriminants

A primitive quadratic Dirichlet character `χ` of level `N ≠ 0` is the character of a unique
fundamental discriminant `D` with `|D| = N`: `χ n = fundamentalDiscriminantCharCast R D hD n` at
every integer `n`, the left side read modulo `N` and the right side modulo `|D|`. More generally,
passing to `χ.primitiveCharacter` shows that *every* quadratic Dirichlet character `χ` of level
`N ≠ 0` agrees, at every integer coprime to `N`, with the character of a unique fundamental
discriminant `D` of absolute value `χ.conductor` (and equivalently with the character of
`fundamentalDiscriminant d` for a unique squarefree radicand `d`). Over `ℂ`, real-valued Dirichlet
characters are precisely the quadratic ones (`MulChar.isQuadratic_iff_forall_im_eq_zero` in
`TauCeti.NumberTheory.MulChar.Real`).

The fundamental discriminant of `χ` is explicitly `χ.conductor` if `χ (-1) = 1` and `-χ.conductor`
otherwise. Both this formula and uniqueness hold in every commutative ring without assuming
`2 ≠ 0`: when `2 = 0` in `R`, every unit value `±1` collapses to `1`, forcing `χ = 1`,
`χ.conductor = 1`, and `D = 1` (as `-1` is not a fundamental discriminant). The assignment is
natural under `changeLevel`, which preserves both the conductor and the coprime character values.

At an odd prime `p ∤ N`, `χ p` equals both `legendreSym p D` and
`legendreSym p (fundamentalDiscriminantRadicand D)` in `R`; when `2 ≠ 0`, `χ p = -1` holds if and
only if neither `D` nor its squarefree radicand is a square in `ZMod p`.

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of absolute
  value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a unique fundamental discriminant of absolute
  value `N`.
* `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.existsUnique_squarefree_apply_eq`: a quadratic character of any level `N ≠ 0`
  agrees on integers coprime to `N` with the character of a unique fundamental discriminant `D`
  with `|D| = χ.conductor` (and a unique squarefree radicand `d`).
* `DirichletCharacter.natAbs_eq_conductor_and_forall_isCoprime_changeLevel_iff`: naturality of the
  primitive discriminant under `changeLevel`.
* `DirichletCharacter.isFundamentalDiscr_ite_conductor`,
  `DirichletCharacter.apply_eq_fundamentalDiscriminantCharCast_ite_conductor`,
  `DirichletCharacter.eq_ite_conductor_of_isFundamentalDiscr`: the fundamental discriminant of `χ`
  is `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise.
* `DirichletCharacter.apply_prime_eq_legendreSym`,
  `DirichletCharacter.apply_prime_eq_legendreSym_radicand`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare_radicand`: the odd-prime Legendre
  dictionary and inert nonsquare criterion for both `D` and its squarefree radicand.

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

/-- If `-1 = 1` in `R` and `χ` agrees on integers coprime to `N` with the character of a
fundamental discriminant `D` whose absolute value divides `N`, then `χ = 1`. -/
private theorem eq_one_of_neg_one_eq_one_of_forall_isCoprime {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D) (hDN : D.natAbs ∣ N)
    (h1eq : (-1 : R) = 1)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    χ = 1 := MulChar.ext fun u ↦ by
  have hu : IsCoprime ((u : ZMod N).val : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime u)
  have hv := hval ((u : ZMod N).val : ℤ) hu
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at hv
  have huD : IsUnit ((u : ZMod N).val : ZMod D.natAbs) := by
    rw [← Int.cast_natCast]
    exact (ZMod.isUnit_intCast_iff_isCoprime _ _).mpr <| isCoprime_comm.mp <|
      hu.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hDN)
  rcases fundamentalDiscriminantChar_isQuadratic hD ((u : ZMod N).val : ZMod D.natAbs) with
    h0 | h1 | hm1
  · exact absurd (h0 ▸ huD.map (fundamentalDiscriminantChar D hD)) not_isUnit_zero
  · rw [hv, fundamentalDiscriminantCharCast_apply, h1, Int.cast_one, MulChar.one_apply u.isUnit]
  · rw [hv, fundamentalDiscriminantCharCast_apply, hm1, Int.cast_neg, Int.cast_one, h1eq,
      MulChar.one_apply u.isUnit]

/-- **Uniqueness of the fundamental discriminant of a Dirichlet character.** At any level `N`, at
most one fundamental discriminant `D` has `|D| = χ.conductor` and agrees with `χ` through
`fundamentalDiscriminantCharCast` at every integer coprime to `N` (with no assumption on `2` in
`R`). -/
theorem eq_of_isFundamentalDiscr_of_natAbs_eq_conductor {N : ℕ}
    {χ : DirichletCharacter R N} {D₁ D₂ : ℤ}
    (hD₁ : Int.IsFundamentalDiscr D₁) (hD₂ : Int.IsFundamentalDiscr D₂)
    (hN₁ : D₁.natAbs = χ.conductor) (hN₂ : D₂.natAbs = χ.conductor)
    (hval₁ : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D₁ hD₁ n)
    (hval₂ : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D₂ hD₂ n) :
    D₁ = D₂ := by
  have : NeZero N := ⟨fun hN ↦ Int.natAbs_ne_zero.mpr hD₁.ne_zero
    (hN₁.trans (χ.conductor_eq_zero_iff_level_eq_zero.mpr hN))⟩
  rcases Int.natAbs_eq_natAbs_iff.mp (hN₁.trans hN₂.symm) with h | h
  · exact h
  -- Otherwise `D₁ = -D₂`; comparing values at `-1` forces `(-1 : R) = 1`, hence `χ = 1` and
  -- `|D₁| = 1`, which excludes `D₁ = -1` since `-1` is not a fundamental discriminant.
  have hneg1 : IsCoprime (-1 : ℤ) N := isCoprime_one_left.neg_left
  have hsign : (D₁.sign : R) = (D₂.sign : R) := by
    have hs₁ := hval₁ (-1) hneg1
    have hs₂ := hval₂ (-1) hneg1
    rw [hs₁] at hs₂
    simpa [fundamentalDiscriminantChar_neg_one] using hs₂
  have h1eq : (-1 : R) = 1 := by
    rcases hD₂.ne_zero.lt_or_gt with hlt | hgt
    · rw [h, Int.sign_eq_one_of_pos (neg_pos.mpr hlt), Int.sign_eq_neg_one_of_neg hlt] at hsign
      simpa using hsign.symm
    · rw [h, Int.sign_eq_neg_one_of_neg (neg_neg_of_pos hgt), Int.sign_eq_one_of_pos hgt] at hsign
      simpa using hsign
  have hχ1 : χ = 1 := eq_one_of_neg_one_eq_one_of_forall_isCoprime hD₁
    (hN₁ ▸ χ.conductor_dvd_level) h1eq hval₁
  have habs1 : D₁.natAbs = 1 := by rw [hN₁, hχ1, conductor_one]
  have := hD₁.emod_four_eq_zero_or_one
  have := hD₂.emod_four_eq_zero_or_one
  omega

/-- **Primitive quadratic characters correspond to a unique fundamental discriminant.** A primitive
quadratic character `χ` of level `N ≠ 0` agrees at every integer with the character of a unique
fundamental discriminant `D` with `|D| = N`. -/
theorem IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = N ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  refine ⟨D, ⟨hD, hDN, hval⟩, fun D' ⟨hD', hD'N, hval'⟩ ↦ ?_⟩
  have hcond : χ.conductor = N := (isPrimitive_def _).mp hχ
  exact eq_of_isFundamentalDiscr_of_natAbs_eq_conductor hD' hD
    (hD'N.trans hcond.symm) (hDN.trans hcond.symm) (fun n _ ↦ hval' n) (fun n _ ↦ hval n)

/-- **The primitive discriminant of a quadratic character.** Every quadratic Dirichlet character `χ`
of level `N ≠ 0` agrees, at every integer coprime to `N`, with the character of a unique fundamental
discriminant `D` of absolute value `χ.conductor` (Montgomery–Vaughan, Theorem 9.13). The principal
character corresponds to `D = 1`. -/
theorem existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, hDc, hval⟩ :=
    χ.primitiveCharacter_isPrimitive.exists_isFundamentalDiscr_apply_eq hq.primitiveCharacter
  refine ⟨D, ⟨hD, hDc, fun n hn ↦ by rw [← χ.primitiveCharacter_apply_of_isCoprime hn, hval]⟩,
    fun D' ⟨hD', hD'c, hval'⟩ ↦ ?_⟩
  exact eq_of_isFundamentalDiscr_of_natAbs_eq_conductor hD' hD hD'c hDc hval'
    fun n hn ↦ by rw [← χ.primitiveCharacter_apply_of_isCoprime hn, hval]

/-- **Squarefree-radicand form of the primitive discriminant.** Every quadratic Dirichlet character
`χ` of level `N ≠ 0` corresponds to a unique squarefree integer `d` such that
`|fundamentalDiscriminant d| = χ.conductor` and `χ` agrees at every integer coprime to `N` with the
character of `fundamentalDiscriminant d`; the principal character corresponds to `d = 1`. -/
theorem existsUnique_squarefree_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d, (fundamentalDiscriminant d).natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N →
        χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
          (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniq⟩ := existsUnique_isFundamentalDiscr_apply_eq hq
  refine ⟨fundamentalDiscriminantRadicand D, ⟨squarefree_fundamentalDiscriminantRadicand hD, ?_⟩,
    fun d ⟨hd, hdc, hvald⟩ ↦ ?_⟩
  · refine ⟨by rw [fundamentalDiscriminant_fundamentalDiscriminantRadicand hD, hDc], fun n hn ↦ ?_⟩
    rw [hval n hn]
    simp only [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast,
      fundamentalDiscriminant_fundamentalDiscriminantRadicand hD]
  · have hD' := huniq (fundamentalDiscriminant d)
      ⟨isFundamentalDiscr_fundamentalDiscriminant hd, hdc, hvald⟩
    rw [← hD', fundamentalDiscriminantRadicand_fundamentalDiscriminant]

/-- **Naturality of the primitive discriminant under `changeLevel`.** For `N ∣ M` with `M ≠ 0`, a
fundamental discriminant `D` has `|D|` equal to the conductor of `changeLevel hNM χ` and agrees with
`changeLevel hNM χ` on integers coprime to `M` if and only if `|D| = χ.conductor` and `D` agrees
with `χ` on integers coprime to `N`. -/
theorem natAbs_eq_conductor_and_forall_isCoprime_changeLevel_iff {N M : ℕ} [NeZero M]
    (hNM : N ∣ M) (χ : DirichletCharacter R N) {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    (D.natAbs = (changeLevel hNM χ).conductor ∧
      ∀ n : ℤ, IsCoprime n M →
        changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n) ↔
    (D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) := by
  have : NeZero N := ⟨fun hN ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (hN ▸ hNM))⟩
  rw [conductor_changeLevel]
  refine and_congr_right fun hDc ↦ ⟨fun hval n hn ↦ ?_, fun hval n hn ↦ ?_⟩
  · obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hNM (ZMod.unitOfIsCoprime n hn)
    let m : ℤ := (v : ZMod M).val
    have hmM : IsCoprime m M := Nat.isCoprime_iff_coprime.mpr (ZMod.val_coe_unit_coprime v)
    have hmN : (m : ZMod N) = (n : ZMod N) := by
      have hv' := congrArg Units.val hv
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfIsCoprime] at hv'
      simpa [m, ZMod.cast_intCast hNM] using hv'
    have hmD : (m : ZMod D.natAbs) = (n : ZMod D.natAbs) := by
      rw [ZMod.intCast_eq_intCast_iff] at hmN ⊢
      exact hmN.of_dvd (Int.natCast_dvd_natCast.mpr (hDc ▸ χ.conductor_dvd_level))
    have hχm := hval m hmM
    rw [changeLevel_eq_cast_of_dvd' χ hNM hmM, hmN, hmD] at hχm
    exact hχm
  · rw [changeLevel_eq_cast_of_dvd' χ hNM hn]
    exact hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))

/-- Any fundamental discriminant `D` with `|D| = χ.conductor` whose character agrees with `χ` at
integers coprime to `N` equals `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise. -/
theorem eq_ite_conductor_of_isFundamentalDiscr [DecidableEq R] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hDc : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  by_cases h2 : (2 : R) = 0
  · have : NeZero N := ⟨fun hN ↦ Int.natAbs_ne_zero.mpr hD.ne_zero
      (hDc.trans (χ.conductor_eq_zero_iff_level_eq_zero.mpr hN))⟩
    have h1eq : (-1 : R) = 1 := by linear_combination -h2
    have hχ1 : χ = 1 := eq_one_of_neg_one_eq_one_of_forall_isCoprime hD
      (hDc ▸ χ.conductor_dvd_level) h1eq hval
    subst hχ1
    have h1 : (1 : DirichletCharacter R N) (-1) = 1 := MulChar.one_apply isUnit_one.neg
    rw [conductor_one] at hDc ⊢
    have := hD.emod_four_eq_zero_or_one
    simp only [h1, ↓reduceIte, Nat.cast_one]
    omega
  · have hsign : χ (-1) = D.sign := by
      simpa [fundamentalDiscriminantChar_neg_one] using hval (-1) isCoprime_one_left.neg_left
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

/-- The fundamental discriminant of a primitive quadratic character `χ` of nonzero level `N` is `N`
if `χ (-1) = 1` and `-N` otherwise. -/
private theorem IsPrimitive.exists_eq_ite_apply_eq (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D = (if χ (-1) = 1 then (N : ℤ) else -N) ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  have hcond : χ.conductor = N := (isPrimitive_def _).mp hχ
  have hite := eq_ite_conductor_of_isFundamentalDiscr hD (hDN.trans hcond.symm) fun n _ ↦ hval n
  rw [hcond] at hite
  exact ⟨D, hD, hite, hval⟩

/-- The integer `N` if `χ (-1) = 1` and `-N` otherwise is a fundamental discriminant for every
primitive quadratic character `χ` of nonzero level `N`. -/
theorem IsPrimitive.isFundamentalDiscr_ite (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (N : ℤ) else -N) := by
  obtain ⟨D, hD, rfl, -⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hD

/-- **Primitive quadratic characters are Kronecker characters, with their discriminant.** A
primitive quadratic character `χ` of nonzero level `N` is the character of the fundamental
discriminant `D = N` if `χ (-1) = 1` and `D = -N` otherwise:
`χ n = fundamentalDiscriminantCharCast R D _ n` at every integer `n`. For the principal character,
primitive only at level `1`, this is `D = 1`. -/
theorem IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ n = fundamentalDiscriminantCharCast R _ (hχ.isFundamentalDiscr_ite hq) n := by
  obtain ⟨D, hD, rfl, hval⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hval n

/-- The integer `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise is a fundamental
discriminant for every quadratic character `χ` of nonzero level `N`. -/
theorem isFundamentalDiscr_ite_conductor (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hneg : χ.primitiveCharacter (-1) = χ (-1) := by
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter, changeLevel_apply_neg_one]
  rw [← hneg]
  exact χ.primitiveCharacter_isPrimitive.isFundamentalDiscr_ite hq.primitiveCharacter

/-- The primitive character of a quadratic character `χ` of nonzero level `N` agrees at every
integer with the character of `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise. -/
theorem primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ.primitiveCharacter n =
      fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_ite_conductor hq) n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hneg : χ.primitiveCharacter (-1) = χ (-1) := by
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter, changeLevel_apply_neg_one]
  rw [χ.primitiveCharacter_isPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite
    hq.primitiveCharacter]
  simp only [fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantChar_intCast, hneg]

/-- **Quadratic characters are Kronecker characters on coprime integers, with explicit
discriminant.** A quadratic character `χ` of nonzero level `N` agrees at every integer `n` coprime
to `N` with the character of `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise. -/
theorem apply_eq_fundamentalDiscriminantCharCast_ite_conductor (hq : χ.IsQuadratic) {n : ℤ}
    (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_ite_conductor hq) n := by
  rw [← χ.primitiveCharacter_apply_of_isCoprime hn,
    primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor hq]

end Sign

section OddPrime

/-- **Odd-prime Legendre dictionary (discriminant form).** If `χ` agrees on integers coprime to `N`
with the character of a fundamental discriminant `D`, then at every odd prime `p ∤ N` the value
`χ p` equals `legendreSym p D` cast to `R`. -/
theorem apply_prime_eq_legendreSym {N : ℕ} {χ : DirichletCharacter R N} {D : ℤ}
    (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  have hcop : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hpN)
  rw [← Int.cast_natCast p, hval p hcop, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2]

/-- **Odd-prime Legendre dictionary (radicand form).** Under the same hypotheses, `χ p` also equals
`legendreSym p (fundamentalDiscriminantRadicand D)` cast to `R`. -/
theorem apply_prime_eq_legendreSym_radicand {N : ℕ} {χ : DirichletCharacter R N} {D : ℤ}
    (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p (fundamentalDiscriminantRadicand D) : R) := by
  rw [apply_prime_eq_legendreSym hD hval hp2 hpN,
    legendreSym_fundamentalDiscriminantRadicand hp2 hD]

/-- **Inert odd-prime criterion (discriminant form).** When `2 ≠ 0` in `R` and `χ` agrees on
integers coprime to `N` with the character of a fundamental discriminant `D`, for every odd prime
`p ∤ N` one has `χ p = -1` if and only if `D` is not a square in `ZMod p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = -1 ↔ ¬ IsSquare (D : ZMod p) := by
  have : Nontrivial R := ⟨0, 2, (NeZero.ne (2 : R)).symm⟩
  have hR : ringChar R ≠ 2 := fun h ↦
    NeZero.ne (2 : R) (by simpa [h] using ringChar.Nat.cast_ringChar (R := R))
  rw [apply_prime_eq_legendreSym hD hval hp2 hpN, ← legendreSym.eq_neg_one_iff p, legendreSym]
  refine ⟨fun h ↦ Int.cast_injOn_of_ringChar_ne_two hR
    (quadraticChar_isQuadratic (ZMod p) (D : ZMod p)) (by simp) (by simpa using h),
    fun h ↦ by simp [h]⟩

/-- **Inert odd-prime criterion (radicand form).** When `2 ≠ 0` in `R` and `χ` agrees on integers
coprime to `N` with the character of a fundamental discriminant `D`, for every odd prime `p ∤ N`
one has `χ p = -1` if and only if `fundamentalDiscriminantRadicand D` is not a square in
`ZMod p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare_radicand [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = -1 ↔ ¬ IsSquare (fundamentalDiscriminantRadicand D : ZMod p) := by
  rw [apply_prime_eq_neg_one_iff_not_isSquare hD hval hp2 hpN, ← legendreSym.eq_neg_one_iff p,
    ← legendreSym.eq_neg_one_iff p, legendreSym_fundamentalDiscriminantRadicand hp2 hD]

end OddPrime

end DirichletCharacter
