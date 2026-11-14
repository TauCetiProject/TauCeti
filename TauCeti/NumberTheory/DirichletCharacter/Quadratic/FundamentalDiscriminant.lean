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
import TauCeti.NumberTheory.FundamentalDiscriminant
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Basic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# Quadratic Dirichlet characters and their fundamental discriminants

A primitive quadratic Dirichlet character `χ` of level `N ≠ 0` is the character of a unique
fundamental discriminant: there is a unique fundamental discriminant `D` with `|D| = N` such that
`χ n = fundamentalDiscriminantCharCast R D hD n` at every integer `n`, the left side read modulo
`N` and the right side modulo `|D|`. More generally, for any quadratic Dirichlet character `χ` of
nonzero level `N`, passing to `χ.primitiveCharacter` shows that there is a unique fundamental
discriminant `D` with `|D| = χ.conductor` such that `χ n = fundamentalDiscriminantCharCast R D hD n`
at every integer `n` coprime to `N`. When `2 ≠ 0` in the coefficient ring, `D` is `χ.conductor` if
`χ (-1) = 1` and `-χ.conductor` otherwise. The principal character is included and corresponds to
`D = 1` (`χ.conductor = 1`).

Through the bijection `fundamentalDiscriminant` between squarefree integers `d` and fundamental
discriminants `D`, each quadratic character at level `N ≠ 0` also corresponds to a unique
squarefree radicand `d`. At an odd prime `p ∤ N`, `χ p` is the Legendre symbol `legendreSym p D =
legendreSym p d`, and when `2 ≠ 0` in `R`, `χ p = -1` holds if and only if `p ∤ N` and `D`
(equivalently `d`) is not a square modulo `p`.

The proof of existence in the primitive case is local. At a prime power `p ^ k`, `k ≠ 0`, a
primitive quadratic character is the Legendre character modulo `p` (so `k = 1`) when `p` is odd,
and `χ₄`, `χ₈` or `χ₈'` (so `k = 2` or `k = 3`) when `p = 2`; in each case it is the character of a
prime discriminant `p*`, `-4`, `8` or `-8` of absolute value `p ^ k`. The local factors of a
primitive character are primitive, and the character of a product of prime discriminants at
distinct primes is the product of their characters, so `D` is the product of the prime
discriminants of the local factors. Uniqueness uses `χ (-1) = sign D` when `2 ≠ 0`, while when
`2 = 0` in `R` every unit value `±1` equals `1`, forcing `χ = 1`, `χ.conductor = 1` and `D = 1`.

The results hold for characters with values in any commutative ring (with complex real-valued
characters covered via `DirichletCharacter.isQuadratic_of_forall_im_eq_zero`).

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of absolute
  value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a unique fundamental discriminant of absolute
  value `N`.
* `DirichletCharacter.eq_of_isFundamentalDiscr_conductor_apply_eq`,
  `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`: a quadratic character of any
  level `N ≠ 0` agrees on integers coprime to `N` with the character of a unique fundamental
  discriminant `D` of absolute value `χ.conductor`.
* `DirichletCharacter.existsUnique_squarefree_fundamentalDiscriminant_apply_eq`,
  `DirichletCharacter.changeLevel_apply_eq_fundamentalDiscriminantCharCast`: the corresponding
  unique squarefree-radicand realization and naturality under `changeLevel`.
* `DirichletCharacter.apply_prime_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast`,
  `DirichletCharacter.apply_prime_eq_legendreSym_of_apply_eq_fundamentalDiscriminant`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare_of_fundamentalDiscriminant`: the
  odd-prime Legendre evaluation and nonsquare criterion for `D` and for `d`.
* `DirichletCharacter.eq_conductor_ite_of_isFundamentalDiscr`,
  `DirichletCharacter.IsPrimitive.isFundamentalDiscr_ite`,
  `DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite`,
  `DirichletCharacter.isFundamentalDiscr_conductor_ite`,
  `DirichletCharacter.apply_eq_fundamentalDiscriminantCharCast_conductor_ite`: when `2 ≠ 0`, the
  unique fundamental discriminant is `χ (-1) * χ.conductor`.

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

/-- **Uniqueness of the fundamental discriminant of a Dirichlet character.** At any nonzero level
`N` and over any commutative ring `R`, at most one fundamental discriminant `D` satisfies
`|D| = χ.conductor` and agrees with `χ` at every integer coprime to `N`. -/
theorem eq_of_isFundamentalDiscr_conductor_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D₁ D₂ : ℤ}
    (hD₁ : Int.IsFundamentalDiscr D₁) (hD₂ : Int.IsFundamentalDiscr D₂)
    (hc₁ : D₁.natAbs = χ.conductor) (hc₂ : D₂.natAbs = χ.conductor)
    (h₁ : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D₁ hD₁ n)
    (h₂ : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D₂ hD₂ n) :
    D₁ = D₂ := by
  by_cases h2 : (2 : R) = 0
  · have hneg : (-1 : R) = 1 := by linear_combination -h2
    have hχ1 : χ = 1 := by
      refine MulChar.ext fun u ↦ ?_
      obtain ⟨n, hn⟩ := ZMod.intCast_surjective (u : ZMod N)
      have hnN : IsCoprime n N :=
        ((ZMod.isUnit_intCast_iff_isCoprime n N).mp (hn ▸ u.isUnit)).symm
      have hnD : IsCoprime n D₁.natAbs :=
        hnN.of_isCoprime_of_dvd_right
          (Int.natCast_dvd_natCast.mpr (hc₁ ▸ χ.conductor_dvd_level))
      have hu₁ : IsUnit (n : ZMod D₁.natAbs) :=
        (ZMod.isUnit_intCast_iff_isCoprime n D₁.natAbs).mpr hnD.symm
      rw [MulChar.one_apply u.isUnit, ← hn, h₁ n hnN, fundamentalDiscriminantCharCast_apply]
      rcases fundamentalDiscriminantChar_isQuadratic hD₁ (n : ZMod D₁.natAbs) with h0 | h | h
      · exact absurd h0 (hu₁.map (fundamentalDiscriminantChar D₁ hD₁)).ne_zero
      · simp [h]
      · simp [h, hneg]
    rw [hχ1, conductor_one] at hc₁ hc₂
    rw [hD₁.natAbs_eq_one_iff.mp hc₁, hD₂.natAbs_eq_one_iff.mp hc₂]
  · have hcop : IsCoprime (-1 : ℤ) N := IsCoprime.neg_left isCoprime_one_left
    have hs : (D₁.sign : R) = (D₂.sign : R) := by
      have hs₁ := h₁ (-1) hcop
      have hs₂ := h₂ (-1) hcop
      simp only [Int.cast_neg, Int.cast_one, fundamentalDiscriminantCharCast_apply,
        fundamentalDiscriminantChar_neg_one] at hs₁ hs₂
      exact hs₁.symm.trans hs₂
    have hsign : D₁.sign = D₂.sign := by
      rcases hD₁.ne_zero.lt_or_gt with hlt₁ | hgt₁ <;>
        rcases hD₂.ne_zero.lt_or_gt with hlt₂ | hgt₂
      · rw [Int.sign_eq_neg_one_of_neg hlt₁, Int.sign_eq_neg_one_of_neg hlt₂]
      · rw [Int.sign_eq_neg_one_of_neg hlt₁, Int.sign_eq_one_of_pos hgt₂, Int.cast_neg,
          Int.cast_one] at hs
        exact absurd (by linear_combination -hs : (2 : R) = 0) h2
      · rw [Int.sign_eq_one_of_pos hgt₁, Int.sign_eq_neg_one_of_neg hlt₂, Int.cast_one,
          Int.cast_neg] at hs
        exact absurd (by linear_combination hs : (2 : R) = 0) h2
      · rw [Int.sign_eq_one_of_pos hgt₁, Int.sign_eq_one_of_pos hgt₂]
    rw [← Int.sign_mul_natAbs D₁, ← Int.sign_mul_natAbs D₂, hsign, hc₁, hc₂]

/-- **Primitive quadratic characters correspond to a unique fundamental discriminant.** A primitive
quadratic character `χ` of level `N ≠ 0` is the character of a unique fundamental discriminant `D`
with `|D| = N` (Montgomery–Vaughan, Theorem 9.13). -/
theorem IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = N ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  have hc : χ.conductor = N := (isPrimitive_def _).mp hχ
  exact ⟨D, ⟨hD, hDN, hval⟩, fun D' ⟨hD', hD'N, hval'⟩ ↦
    eq_of_isFundamentalDiscr_conductor_apply_eq hD' hD (hD'N.trans hc.symm) (hDN.trans hc.symm)
      (fun n _ ↦ hval' n) (fun n _ ↦ hval n)⟩

/-- **The primitive discriminant of a quadratic character.** Over any commutative ring `R`, a
quadratic Dirichlet character `χ` of any positive level `N` agrees, at every integer coprime to
`N`, with `fundamentalDiscriminantCharCast R D hD` for a unique fundamental discriminant `D` with
`|D| = χ.conductor`. The principal character corresponds to `D = 1` (Montgomery–Vaughan, §9.3,
Theorem 9.13). -/
theorem existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D,
      D.natAbs = χ.conductor ∧ ∀ n : ℤ, IsCoprime n N →
        χ n = fundamentalDiscriminantCharCast R D hD n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, hDc, hval⟩ :=
    χ.primitiveCharacter_isPrimitive.exists_isFundamentalDiscr_apply_eq hq.primitiveCharacter
  have hvalN (n : ℤ) (hn : IsCoprime n N) :
      χ n = fundamentalDiscriminantCharCast R D hD n := by
    rw [← χ.primitiveCharacter_apply_of_isCoprime hn, hval]
  exact ⟨D, ⟨hD, hDc, hvalN⟩, fun D' ⟨hD', hD'c, hval'⟩ ↦
    eq_of_isFundamentalDiscr_conductor_apply_eq hD' hD hD'c hDc hval' hvalN⟩

/-- **Squarefree-radicand form at any positive level.** Every quadratic Dirichlet character `χ` of
nonzero level `N` over a commutative ring `R` comes from a unique squarefree integer `d` such that
`|fundamentalDiscriminant d| = χ.conductor` and `χ` agrees at every integer coprime to `N` with the
character of `fundamentalDiscriminant d`. -/
theorem existsUnique_squarefree_fundamentalDiscriminant_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d,
      (fundamentalDiscriminant d).natAbs = χ.conductor ∧ ∀ n : ℤ, IsCoprime n N →
        χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
          (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, hDc, hval⟩, huniq⟩ := existsUnique_isFundamentalDiscr_apply_eq hq
  obtain ⟨d, ⟨hd, hdD⟩, hduniq⟩ := existsUnique_squarefree_fundamentalDiscriminant_eq hD
  have hval_d (n : ℤ) (hn : IsCoprime n N) :
      χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d)
        (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
    rw [hval n hn, fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantCharCast_apply,
      fundamentalDiscriminantChar_intCast, fundamentalDiscriminantChar_intCast, hdD]
  refine ⟨d, ⟨hd, hdD ▸ hDc, hval_d⟩, fun d' ⟨hd', hd'c, hval'⟩ ↦ hduniq d' ⟨hd', ?_⟩⟩
  exact huniq (fundamentalDiscriminant d')
    ⟨isFundamentalDiscr_fundamentalDiscriminant hd', hd'c, hval'⟩

/-- **Naturality under level change.** If `χ` agrees at integers coprime to `N` with the character
of a fundamental discriminant `D`, then its lift `changeLevel hNM χ` to any multiple `M` of `N`
agrees with the character of the same `D` at integers coprime to `M` (and retains conductor `|D|`
when `M ≠ 0`, by `conductor_changeLevel`). -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast {N M : ℕ} (hNM : N ∣ M)
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℤ} (hn : IsCoprime n M) :
    changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [changeLevel_eq_cast_of_dvd' χ hNM hn,
    hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))]

/-- **Odd-prime evaluation in terms of `D`.** If `χ` agrees at integers coprime to `N` with
`fundamentalDiscriminantCharCast R D hD`, then at every odd prime `p ∤ N` one has
`χ p = legendreSym p D`. -/
theorem apply_prime_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  have hp : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)
  have h := hval p hp
  rw [Int.cast_natCast, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2] at h
  exact h

/-- **Odd-prime evaluation in terms of the radicand `d`.** If `χ` agrees at integers coprime to `N`
with `fundamentalDiscriminantCharCast R (fundamentalDiscriminant d) hD`, then at every odd prime
`p ∤ N` one has `χ p = legendreSym p d`. -/
theorem apply_prime_eq_legendreSym_of_apply_eq_fundamentalDiscriminant {N : ℕ}
    {χ : DirichletCharacter R N} {d : ℤ} (hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d))
    (hval : ∀ n : ℤ, IsCoprime n N →
      χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d) hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p d : R) := by
  rw [apply_prime_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast hD hval hp2 hpN,
    legendreSym_fundamentalDiscriminant hp2]

/-- **Nonsquare criterion at an odd prime in terms of `D`.** When `2 ≠ 0` in `R`, if `χ` agrees at
integers coprime to `N` with `fundamentalDiscriminantCharCast R D hD`, then at any odd prime `p`
one has `χ p = -1` if and only if `p ∤ N` and `D` is not a square modulo `p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (D : ZMod p) := by
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  by_cases hpN : p ∣ N
  · suffices χ p ≠ -1 by simp [hpN, this]
    rw [χ.map_nonunit (by rwa [ZMod.isUnit_prime_iff_not_dvd Fact.out, not_not])]
    exact fun h ↦ h2 (by linear_combination 2 * h)
  · rw [apply_prime_eq_legendreSym_of_apply_eq_fundamentalDiscriminantCharCast hD hval hp2 hpN,
      ← legendreSym.eq_neg_one_iff, and_iff_right hpN]
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    by_cases hD0 : (D : ZMod p) = 0
    · have h0 : legendreSym p D = 0 := (legendreSym.eq_zero_iff p D).mpr hD0
      exact absurd (by simpa [h0] using h : (0 : R) = -1)
        (fun h' ↦ h2 (by linear_combination 2 * h'))
    · rcases legendreSym.eq_one_or_neg_one p hD0 with h1 | hneg
      · exact absurd (by simpa [h1] using h : (1 : R) = -1)
          (fun h' ↦ h2 (by linear_combination h'))
      · exact hneg

/-- **Nonsquare criterion at an odd prime in terms of the radicand `d`.** When `2 ≠ 0` in `R`, if
`χ` agrees at integers coprime to `N` with
`fundamentalDiscriminantCharCast R (fundamentalDiscriminant d) hD`, then at any odd prime `p` one
has `χ p = -1` if and only if `p ∤ N` and `d` is not a square modulo `p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare_of_fundamentalDiscriminant [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {d : ℤ} (hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d))
    (hval : ∀ n : ℤ, IsCoprime n N →
      χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d) hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (d : ZMod p) := by
  have h2u : IsUnit (2 : ZMod p) := by
    simpa using ZMod.isUnit_prime_of_not_dvd Nat.prime_two
      (mt (Nat.prime_dvd_prime_iff_eq Nat.prime_two Fact.out).mp hp2.symm)
  rw [apply_prime_eq_neg_one_iff_not_isSquare hD hval hp2, isSquare_fundamentalDiscriminant_iff h2u]

section Sign

variable [DecidableEq R] [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N}

/-- When `2 ≠ 0`, any fundamental discriminant `D` with `|D| = χ.conductor` agreeing with `χ` at
integers coprime to `N` equals `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise. -/
theorem eq_conductor_ite_of_isFundamentalDiscr {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hc : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  have hsign : χ (-1) = D.sign := by
    simpa [fundamentalDiscriminantChar_neg_one] using
      hval (-1) (IsCoprime.neg_left isCoprime_one_left)
  split_ifs with h1 <;> rw [hsign] at h1 <;> rcases hD.ne_zero.lt_or_gt with h | h
  · rw [Int.sign_eq_neg_one_of_neg h, Int.cast_neg, Int.cast_one, neg_eq_iff_add_eq_zero,
      one_add_one_eq_two] at h1
    exact absurd h1 two_ne_zero
  · omega
  · omega
  · rw [Int.sign_eq_one_of_pos h, Int.cast_one] at h1
    exact absurd rfl h1

variable [NeZero N]

/-- When `2 ≠ 0`, the fundamental discriminant of a primitive quadratic character `χ` of level `N`
is `N` if `χ (-1) = 1` and `-N` otherwise, its sign being `χ (-1)`. -/
private theorem IsPrimitive.exists_eq_ite_apply_eq (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D = (if χ (-1) = 1 then (N : ℤ) else -N) ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  have hc : χ.conductor = N := (isPrimitive_def _).mp hχ
  have hite := eq_conductor_ite_of_isFundamentalDiscr hD (hDN.trans hc.symm) (fun n _ ↦ hval n)
  rw [hc] at hite
  exact ⟨D, hD, hite, hval⟩

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

/-- When `2 ≠ 0`, the integer `χ (-1) * χ.conductor`, that is `χ.conductor` if `χ (-1) = 1` and
`-χ.conductor` otherwise, is a fundamental discriminant for every quadratic character `χ` of
nonzero level `N`. -/
theorem isFundamentalDiscr_conductor_ite (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [primitiveCharacter_apply_neg_one] using
    χ.primitiveCharacter_isPrimitive.isFundamentalDiscr_ite hq.primitiveCharacter

/-- **Quadratic characters at any level are induced by a Kronecker character, with explicit
discriminant.** When `2 ≠ 0`, a quadratic character `χ` of nonzero level `N` agrees at every
integer `n` coprime to `N` with the character of the fundamental discriminant
`D = χ (-1) * χ.conductor`. -/
theorem apply_eq_fundamentalDiscriminantCharCast_conductor_ite (hq : χ.IsQuadratic) {n : ℤ}
    (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ (isFundamentalDiscr_conductor_ite hq) n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  rw [← χ.primitiveCharacter_apply_of_isCoprime hn,
    χ.primitiveCharacter_isPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite
      hq.primitiveCharacter n,
    fundamentalDiscriminantCharCast_apply, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_intCast, fundamentalDiscriminantChar_intCast,
    primitiveCharacter_apply_neg_one]

end Sign

section Examples

-- Real-valued complex Dirichlet characters at any positive level have a unique fundamental
-- discriminant via `isQuadratic_of_forall_im_eq_zero`.
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hreal : ∀ a, (χ a).im = 0) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D,
      D.natAbs = χ.conductor ∧ ∀ n : ℤ, IsCoprime n N →
        χ n = fundamentalDiscriminantCharCast ℂ D hD n :=
  existsUnique_isFundamentalDiscr_apply_eq (isQuadratic_of_forall_im_eq_zero χ hreal)

-- The principal character at level `6` has conductor `1` and fundamental discriminant `D = 1`.
example :
    let χ : DirichletCharacter ℂ 6 := 1
    χ.conductor = 1 ∧ (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 := by
  simp [conductor_one, MulChar.one_apply isUnit_one.neg]

-- `χ₄` lifted to level `12` has conductor `4` and `D = -4`; agreement fails at `3` (`3 ∣ 12`).
example :
    let χ : DirichletCharacter ℂ 12 :=
      changeLevel (by decide : 4 ∣ 12) (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    χ.conductor = 4 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = -4 ∧
      χ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) =
        -1 := by
  have hc : (changeLevel (by decide : 4 ∣ 12)
      (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))).conductor = 4 := by
    rw [conductor_changeLevel, conductor_χ₄_ringHomComp]
  have hneg1 : changeLevel (by decide : 4 ∣ 12)
      (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (-1) = -1 := by
    rw [changeLevel_apply_neg_one, MulChar.ringHomComp_apply,
      (by decide : ZMod.χ₄ (-1 : ZMod 4) = -1)]
    norm_num
  have h3 : changeLevel (by decide : 4 ∣ 12)
      (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) (3 : ℤ) = 0 :=
    MulChar.map_nonunit _ (by decide)
  have hD3 :
      fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) =
        -1 := by
    rw [fundamentalDiscriminantChar_neg_four]
    decide
  refine ⟨hc, ?_, h3, hD3⟩
  rw [hc, hneg1]
  norm_num

-- At conductor `8`, `χ₈` (`D = 8`) and `χ₈'` (`D = -8`) share `|D| = 8` and are separated by `-1`.
example :
    (if ZMod.χ₈ (-1) = 1 then ((conductor ZMod.χ₈) : ℤ) else -(conductor ZMod.χ₈)) = 8 ∧
      (if ZMod.χ₈' (-1) = 1 then ((conductor ZMod.χ₈') : ℤ) else -(conductor ZMod.χ₈')) = -8 := by
  have hc8 : conductor ZMod.χ₈ = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five ZMod.χ₈ (by decide)
  have hc8' : conductor ZMod.χ₈' = 8 :=
    conductor_eq_eight_of_apply_one_ne_apply_five ZMod.χ₈' (by decide)
  rw [hc8, hc8', (by decide : ZMod.χ₈ (-1) = 1), (by decide : ZMod.χ₈' (-1) = -1)]
  decide

-- Running conductor-`12` example `DirichletCharacter.mul χ₄ (quadraticChar (ZMod 3))`: conductor
-- `12`, discriminant `D = 12`, radicand `d = 3`, values `-1, -1, 1` at `5, 7, 11`, and invariance
-- under lifting to level `24`.
private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

example :
    let χ : DirichletCharacter ℤ (Nat.lcm 4 3) :=
      DirichletCharacter.mul ZMod.χ₄ (quadraticChar (ZMod 3))
    χ.conductor = 12 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 12 ∧
      fundamentalDiscriminant 3 = 12 ∧
      χ (5 : ℕ) = -1 ∧ χ (7 : ℕ) = -1 ∧ χ (11 : ℕ) = 1 ∧
      (let ψ := changeLevel (by decide : Nat.lcm 4 3 ∣ 24) χ
       ψ.conductor = 12 ∧ (if ψ (-1) = 1 then (ψ.conductor : ℤ) else -ψ.conductor) = 12) := by
  have : NeZero (Nat.lcm 4 3) := ⟨by decide⟩
  have hc4 : conductor ZMod.χ₄ = 4 :=
    conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
  have hc3 : conductor (quadraticChar (ZMod 3)) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp (conductor_dvd_level _)).resolve_left fun h1 ↦ by
      have h2 := DFunLike.congr_fun (eq_one_iff_conductor_eq_one.mpr h1) 2
      rw [MulChar.one_apply (by decide)] at h2
      exact absurd h2 (by decide)
  have hc : (DirichletCharacter.mul ZMod.χ₄ (quadraticChar (ZMod 3))).conductor = 12 := by
    rw [DirichletCharacter.mul, conductor_mul_of_coprime, conductor_changeLevel,
      conductor_changeLevel, hc4, hc3]
    rw [conductor_changeLevel, conductor_changeLevel, hc4, hc3]
    decide
  have hneg1 : DirichletCharacter.mul ZMod.χ₄ (quadraticChar (ZMod 3)) (-1) = 1 := by
    rw [DirichletCharacter.mul, MulChar.mul_apply, changeLevel_apply_neg_one,
      changeLevel_apply_neg_one]
    decide
  have hfd : fundamentalDiscriminant 3 = 12 := by
    rw [fundamentalDiscriminant_of_mod_four_ne_one (by decide)]
    norm_num
  have h5 : DirichletCharacter.mul ZMod.χ₄ (quadraticChar (ZMod 3)) (5 : ℕ) = -1 := by
    rw [mul_natCast]; decide
  have h7 : DirichletCharacter.mul ZMod.χ₄ (quadraticChar (ZMod 3)) (7 : ℕ) = -1 := by
    rw [mul_natCast]; decide
  have h11 : DirichletCharacter.mul ZMod.χ₄ (quadraticChar (ZMod 3)) (11 : ℕ) = 1 := by
    rw [mul_natCast]; decide
  refine ⟨hc, ?_, hfd, h5, h7, h11, ?_, ?_⟩
  · rw [hc, hneg1]
    decide
  · rw [conductor_changeLevel, hc]
  · rw [changeLevel_apply_neg_one, conductor_changeLevel, hc, hneg1]
    decide

-- Odd-prime dictionary at `D = 12` (`d = 3`) for `p = 5` and `p = 3`, and exclusion of `p = 2`
-- (`D = 5` has `χ_5(2) = -1` while `legendreSym 2 5 = 1`).
example (h5 : Int.IsFundamentalDiscr 5) :
    have : Fact (Nat.Prime 5) := ⟨by decide⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    legendreSym 5 12 = -1 ∧ legendreSym 5 3 = -1 ∧
      legendreSym 3 12 = 0 ∧ legendreSym 3 3 = 0 ∧
      fundamentalDiscriminantChar 5 h5 2 = -1 ∧
      legendreSym 2 5 = 1 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h52 : fundamentalDiscriminantChar 5 h5 2 = -1 := by
    rw [fundamentalDiscriminantChar_two]
    decide
  exact ⟨by decide, by decide, by decide, by decide, h52, by decide⟩

end Examples

end DirichletCharacter
