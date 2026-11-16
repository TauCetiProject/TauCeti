/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LocalFactor
public import TauCeti.NumberTheory.MulChar.Real
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
import Mathlib.Tactic.NormNum.LegendreSymbol
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Dyadic.Classification
import TauCeti.NumberTheory.DirichletCharacter.OddPrimePower.Quadratic
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Values

/-!
# The fundamental discriminant of a quadratic or real Dirichlet character

Every quadratic Dirichlet character `χ` of level `N ≠ 0` is induced by the Kronecker character of a
unique fundamental discriminant `D` with `|D| = χ.conductor`: at every integer `n` coprime to `N`,
`χ n = fundamentalDiscriminantCharCast R D hD n`, and equivalently `χ` is the lift along
`|D| ∣ N` of `fundamentalDiscriminantCharCast R D hD`. The principal character corresponds to
`D = 1`. That unique discriminant is `χ.conductor` if `χ (-1) = 1` and `-χ.conductor` otherwise.
Over any `RCLike` field (such as `ℝ` or `ℂ`), real-valued Dirichlet characters coincide with
quadratic ones (`MulChar.isQuadratic_iff_forall_im_eq_zero`), so every real Dirichlet character of
nonzero level has a unique primitive fundamental discriminant.

The construction first classifies primitive quadratic characters locally. At a prime power `p ^ k`,
`k ≠ 0`, a primitive quadratic character is the Legendre character modulo `p` (so `k = 1`) when `p`
is odd, and `χ₄`, `χ₈` or `χ₈'` (so `k = 2` or `k = 3`) when `p = 2`; in each case it is the
character of a prime discriminant `p*`, `-4`, `8` or `-8` of absolute value `p ^ k`. Assembling
the local factors gives existence for primitive characters
(`IsPrimitive.exists_isFundamentalDiscr_apply_eq`).
An arbitrary quadratic character `χ` of level `N ≠ 0` descends to its primitive character `χ*` of
level `χ.conductor ≠ 0`, which remains quadratic (`MulChar.IsQuadratic.primitiveCharacter`) and
agrees with `χ` at integers coprime to `N`. Uniqueness uses `χ (-1) = sign D` when `2 ≠ 0` in `R`,
while when `2 = 0` every quadratic character is principal of conductor `1`, where `D = 1` is the
only fundamental discriminant of absolute value `1`.

At an odd prime `p ∤ N`, `χ p` equals both `legendreSym p D` and
`legendreSym p (fundamentalDiscriminantRadicand D)`, and when `2 ≠ 0` in `R`, `χ p = -1` holds if
and only if `p ∤ N` and `D` (equivalently `fundamentalDiscriminantRadicand D`) is a nonsquare in
`ZMod p`.

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`: a primitive quadratic
  character of level `p ^ k`, `k ≠ 0`, is the character of a prime discriminant of absolute
  value `p ^ k`.
* `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq`: a primitive quadratic
  character of level `N ≠ 0` is the character of a unique fundamental discriminant of absolute
  value `N`.
* `MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq`: a quadratic Dirichlet character
  of any level `N ≠ 0` agrees on integers coprime to `N` with the character of a unique fundamental
  discriminant `D` of absolute value `χ.conductor`.
* `DirichletCharacter.existsUnique_isFundamentalDiscr_of_forall_im_eq_zero`: the real-character
  form over any `RCLike` field (`ℝ`, `ℂ`).
* `MulChar.IsQuadratic.isFundamentalDiscr_ite`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_ite`: the explicit formula
  `D = if χ (-1) = 1 then χ.conductor else -χ.conductor`.
* `DirichletCharacter.changeLevel_isFundamentalDiscr_apply_eq_iff`: invariance of `D` under
  `changeLevel` to a nonzero multiple level.
* `DirichletCharacter.apply_prime_eq_legendreSym`,
  `DirichletCharacter.apply_prime_eq_legendreSym_radicand`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare`,
  `DirichletCharacter.apply_prime_eq_neg_one_iff_not_isSquare_radicand`: the odd-prime Legendre
  and nonsquare dictionary for both `D` and its squarefree radicand.

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

/-- Two fundamental discriminants of absolute value `χ.conductor` whose Kronecker characters agree
with a quadratic character `χ` at `-1` are equal: when `2 ≠ 0` in `R`, `χ (-1)` fixes their sign,
and when `2 = 0`, `χ = 1` has conductor `1`, forcing both discriminants to equal `1`. -/
private theorem eq_of_isFundamentalDiscr_apply_neg_one_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) {D₁ D₂ : ℤ}
    (hD₁ : Int.IsFundamentalDiscr D₁) (hD₂ : Int.IsFundamentalDiscr D₂)
    (habs₁ : D₁.natAbs = χ.conductor) (habs₂ : D₂.natAbs = χ.conductor)
    (h₁ : χ ((-1 : ℤ) : ZMod N) = fundamentalDiscriminantCharCast R D₁ hD₁ (-1 : ℤ))
    (h₂ : χ ((-1 : ℤ) : ZMod N) = fundamentalDiscriminantCharCast R D₂ hD₂ (-1 : ℤ)) :
    D₁ = D₂ := by
  by_cases h2 : (2 : R) = 0
  · have hc : χ.conductor = 1 := by rw [hχ.eq_one_of_two_eq_zero h2, conductor_one]
    rw [hD₁.natAbs_eq_one_iff.mp (habs₁.trans hc), hD₂.natAbs_eq_one_iff.mp (habs₂.trans hc)]
  · have hsigncast : (D₁.sign : R) = (D₂.sign : R) := by
      simpa [fundamentalDiscriminantChar_neg_one] using h₁.symm.trans h₂
    have hsign : D₁.sign = D₂.sign := by
      rcases hD₁.ne_zero.lt_or_gt with hn₁ | hp₁ <;>
        rcases hD₂.ne_zero.lt_or_gt with hn₂ | hp₂
      · rw [Int.sign_eq_neg_one_of_neg hn₁, Int.sign_eq_neg_one_of_neg hn₂]
      · exfalso
        rw [Int.sign_eq_neg_one_of_neg hn₁, Int.sign_eq_one_of_pos hp₂, Int.cast_neg,
          Int.cast_one, neg_eq_iff_add_eq_zero, one_add_one_eq_two] at hsigncast
        exact h2 hsigncast
      · exfalso
        rw [Int.sign_eq_one_of_pos hp₁, Int.sign_eq_neg_one_of_neg hn₂, Int.cast_neg,
          Int.cast_one, eq_neg_iff_add_eq_zero, one_add_one_eq_two] at hsigncast
        exact h2 hsigncast
      · rw [Int.sign_eq_one_of_pos hp₁, Int.sign_eq_one_of_pos hp₂]
    rw [← Int.sign_mul_natAbs D₁, ← Int.sign_mul_natAbs D₂, hsign, habs₁, habs₂]

/-- **Unique fundamental discriminant of a primitive quadratic character.** A primitive quadratic
character `χ` of level `N ≠ 0` is the character of a unique fundamental discriminant `D` of
absolute value `N`. -/
theorem IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = N ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  have hcond : χ.conductor = N := (isPrimitive_def χ).mp hχ
  refine ⟨D, ⟨hD, hDN, hval⟩, fun D' ⟨hD', hD'N, hval'⟩ ↦
    eq_of_isFundamentalDiscr_apply_neg_one_eq hq hD' hD (hD'N.trans hcond.symm)
      (hDN.trans hcond.symm) (hval' (-1)) (hval (-1))⟩

/-! ### Quadratic and real characters of arbitrary nonzero level -/

/-- A Dirichlet character of level `N` is the lift along `|D| ∣ N` of
`fundamentalDiscriminantCharCast R D hD` if and only if the two agree at every integer coprime to
`N`. -/
theorem eq_changeLevel_fundamentalDiscriminantCharCast_iff {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hdvd : D.natAbs ∣ N) :
    χ = changeLevel hdvd (fundamentalDiscriminantCharCast R D hD) ↔
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  refine ⟨fun h n hn ↦ by rw [h, changeLevel_eq_cast_of_dvd' _ hdvd hn], fun h ↦ ?_⟩
  refine MulChar.ext' fun x ↦ ?_
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  exact apply_intCast_eq_of_forall_isCoprime rfl
    (fun m hm ↦ by rw [h m hm, changeLevel_eq_cast_of_dvd' _ hdvd hm]) n

/-- For a fundamental discriminant `D` with `|D| = χ.conductor` and `N ≠ 0`, `χ.primitiveCharacter`
agrees with `fundamentalDiscriminantCharCast R D hD` at every integer if and only if `χ` agrees
with it at every integer coprime to `N`. -/
theorem primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_iff {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (habs : D.natAbs = χ.conductor) :
    (∀ n : ℤ, χ.primitiveCharacter n = fundamentalDiscriminantCharCast R D hD n) ↔
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  refine ⟨fun h n hn ↦ by rw [← χ.primitiveCharacter_apply_of_isCoprime hn, h n], fun h ↦ ?_⟩
  have hdvd : D.natAbs ∣ N := habs ▸ χ.conductor_dvd_level
  have hχeq : χ = changeLevel hdvd (fundamentalDiscriminantCharCast R D hD) :=
    (eq_changeLevel_fundamentalDiscriminantCharCast_iff hD hdvd).mpr h
  have hprim : χ.primitiveCharacter =
      changeLevel (dvd_of_eq habs) (fundamentalDiscriminantCharCast R D hD) :=
    changeLevel_injective χ.conductor_dvd_level <| by
      rw [changeLevel_primitiveCharacter, ← changeLevel_trans, ← hχeq]
  intro n
  rw [hprim, changeLevel_dvd_of_eq_apply habs]

/-- For a fundamental discriminant `D` with `|D| = χ.conductor` at a nonzero level `N`, `χ` is
principal if and only if `D = 1`. -/
theorem eq_one_iff_of_natAbs_eq_conductor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (habs : D.natAbs = χ.conductor) : χ = 1 ↔ D = 1 := by
  rw [eq_one_iff_conductor_eq_one, ← habs, hD.natAbs_eq_one_iff]

/-- A quadratic Dirichlet character `χ` of level `N ≠ 0` agrees, at every integer coprime to `N`,
with the character of a fundamental discriminant `D` of absolute value `χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.exists_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨D, hD, habs, hval⟩ :=
    χ.primitiveCharacter_isPrimitive.exists_isFundamentalDiscr_apply_eq hχ.primitiveCharacter
  exact ⟨D, hD, habs,
    (primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_iff hD habs).mp hval⟩

/-- **The primitive discriminant of a quadratic character.** Every quadratic Dirichlet character
`χ` of level `N ≠ 0` agrees, at every integer coprime to `N`, with the character of a unique
fundamental discriminant `D` of absolute value `χ.conductor` (Montgomery–Vaughan, Theorem 9.13 for
primitive nonprincipal characters; the principal character corresponds to `D = 1`). -/
theorem _root_.MulChar.IsQuadratic.existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, habs, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq
  have hneg1 : IsCoprime (-1 : ℤ) N := IsCoprime.neg_left isCoprime_one_left
  refine ⟨D, ⟨hD, habs, hval⟩, fun D' ⟨hD', habs', hval'⟩ ↦
    eq_of_isFundamentalDiscr_apply_neg_one_eq hχ hD' hD habs' habs
      (hval' (-1) hneg1) (hval (-1) hneg1)⟩

/-- **The primitive discriminant of a real character.** Over `ℝ`, `ℂ`, or any `RCLike` field `K`,
every real-valued Dirichlet character `χ` of level `N ≠ 0` agrees, at every integer coprime to `N`,
with the scalar realization of the character of a unique fundamental discriminant `D` of absolute
value `χ.conductor`. -/
theorem existsUnique_isFundamentalDiscr_of_forall_im_eq_zero {K : Type*} [RCLike K]
    {N : ℕ} [NeZero N] {χ : DirichletCharacter K N} (hχ : ∀ a, RCLike.im (χ a) = 0) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast K D hD n :=
  (MulChar.isQuadratic_iff_forall_im_eq_zero.mpr hχ).existsUnique_isFundamentalDiscr_apply_eq

/-! ### Naturality under level change -/

/-- Lifting a Dirichlet character along `N ∣ M` to a nonzero level `M` preserves both its
conductor and the condition that `D` is an associated fundamental discriminant. -/
theorem changeLevel_isFundamentalDiscr_apply_eq_iff {N M : ℕ} [NeZero M] (hNM : N ∣ M)
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D) :
    (D.natAbs = (changeLevel hNM χ).conductor ∧
      ∀ n : ℤ, IsCoprime n M →
        changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n) ↔
    (D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) := by
  have : NeZero N := ⟨fun h0 ↦ NeZero.ne M (Nat.eq_zero_of_zero_dvd (h0 ▸ hNM))⟩
  rw [conductor_changeLevel]
  refine and_congr_right fun habs ↦ ?_
  have hdvdN : D.natAbs ∣ N := habs ▸ χ.conductor_dvd_level
  have hdvdM : D.natAbs ∣ M := hdvdN.trans hNM
  rw [← eq_changeLevel_fundamentalDiscriminantCharCast_iff hD hdvdM,
    ← eq_changeLevel_fundamentalDiscriminantCharCast_iff hD hdvdN,
    changeLevel_trans _ hdvdN hNM, (changeLevel_injective hNM).eq_iff]

section Sign

variable [NeZero (2 : R)] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} [Decidable (χ (-1) = 1)]

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

section ConductorSign

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter R N} [Decidable (χ (-1) = 1)]

/-- For every quadratic Dirichlet character `χ` of level `N ≠ 0`, the signed conductor
`if χ (-1) = 1 then χ.conductor else -χ.conductor` is its unique fundamental discriminant, and
`χ.primitiveCharacter` agrees with its Kronecker character at every integer. -/
private theorem _root_.MulChar.IsQuadratic.exists_eq_ite_conductor_apply_eq (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D),
      D = (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) ∧
        ∀ n : ℤ, χ.primitiveCharacter n = fundamentalDiscriminantCharCast R D hD n := by
  by_cases h2 : (2 : R) = 0
  · rcases hq.eq_one_of_two_eq_zero h2 with rfl
    refine ⟨1, Int.isFundamentalDiscr_one, ?_, fun n ↦ ?_⟩
    · rw [ite_eq_left (MulChar.one_apply isUnit_one.neg), conductor_one, Nat.cast_one]
    · rw [primitiveCharacter_one, fundamentalDiscriminantCharCast_apply,
        fundamentalDiscriminantChar_intCast, TauCeti.kroneckerSym_one_left, Int.cast_one,
        MulChar.one_apply ((ZMod.isUnit_intCast_iff_isCoprime n _).mpr
          (by rw [conductor_one]; exact isCoprime_one_left))]
  · have : NeZero (2 : R) := ⟨h2⟩
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hneg1 : χ.primitiveCharacter (-1) = χ (-1) := by
      simpa using χ.primitiveCharacter_apply_of_isCoprime (IsCoprime.neg_left isCoprime_one_left)
    have : Decidable (χ.primitiveCharacter (-1) = 1) :=
      decidable_of_iff (χ (-1) = 1) (by rw [hneg1])
    obtain ⟨D, hD, hDite, hval⟩ :=
      χ.primitiveCharacter_isPrimitive.exists_eq_ite_apply_eq hq.primitiveCharacter
    simp only [hneg1] at hDite
    exact ⟨D, hD, hDite, hval⟩

/-- The signed conductor `if χ (-1) = 1 then χ.conductor else -χ.conductor` of a quadratic
Dirichlet character `χ` of level `N ≠ 0` is a fundamental discriminant. -/
theorem _root_.MulChar.IsQuadratic.isFundamentalDiscr_ite (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  obtain ⟨_, hD, rfl, -⟩ := hq.exists_eq_ite_conductor_apply_eq
  exact hD

/-- The primitive character of a quadratic Dirichlet character `χ` of level `N ≠ 0` agrees at
every integer with the Kronecker character of `if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ.primitiveCharacter n =
      fundamentalDiscriminantCharCast R _ hq.isFundamentalDiscr_ite n := by
  obtain ⟨_, hD, rfl, hval⟩ := hq.exists_eq_ite_conductor_apply_eq
  exact hval n

/-- **Quadratic characters at any nonzero level, with their explicit discriminant.** A quadratic
Dirichlet character `χ` of level `N ≠ 0` agrees, at every integer `n` coprime to `N`, with the
character of `D = if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_ite
    (hq : χ.IsQuadratic) {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ hq.isFundamentalDiscr_ite n := by
  rw [← χ.primitiveCharacter_apply_of_isCoprime hn,
    hq.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite n]

/-- A quadratic Dirichlet character `χ` of level `N ≠ 0` is the lift by `changeLevel` of the
Kronecker character of `if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.eq_changeLevel_fundamentalDiscriminantCharCast_ite
    (hq : χ.IsQuadratic)
    (hdvd : (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor).natAbs ∣ N := by
      split_ifs <;> simpa using χ.conductor_dvd_level) :
    χ = changeLevel hdvd (fundamentalDiscriminantCharCast R _ hq.isFundamentalDiscr_ite) :=
  (eq_changeLevel_fundamentalDiscriminantCharCast_iff hq.isFundamentalDiscr_ite hdvd).mpr
    fun _ hn ↦ hq.apply_eq_fundamentalDiscriminantCharCast_ite hn

/-- For a quadratic Dirichlet character `χ` of level `N ≠ 0`, its signed conductor equals `1` if
and only if `χ = 1`. -/
theorem _root_.MulChar.IsQuadratic.ite_conductor_eq_one_iff (hq : χ.IsQuadratic) :
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 ↔ χ = 1 :=
  (eq_one_iff_of_natAbs_eq_conductor hq.isFundamentalDiscr_ite (by split_ifs <;> simp)).symm

end ConductorSign

/-- Lifting a Dirichlet character to a nonzero multiple of its level preserves the signed
conductor formula `if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem ite_changeLevel_conductor {N M : ℕ} [NeZero M] (hNM : N ∣ M)
    (χ : DirichletCharacter R N) [Decidable (changeLevel hNM χ (-1) = 1)]
    [Decidable (χ (-1) = 1)] :
    (if changeLevel hNM χ (-1) = 1 then ((changeLevel hNM χ).conductor : ℤ)
      else -(changeLevel hNM χ).conductor) =
      if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  simp only [changeLevel_apply_neg_one, conductor_changeLevel]

/-! ### Odd-prime Legendre and nonsquare dictionary -/

section OddPrime

variable {N : ℕ} {χ : DirichletCharacter R N} {D : ℤ}

/-- If `χ` agrees on integers coprime to `N` with `fundamentalDiscriminantCharCast R D hD`, then
at every odd prime `p ∤ N`, `χ p` is the cast of `legendreSym p D` (including `0` when `p ∣ D`). -/
theorem apply_prime_eq_legendreSym (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = legendreSym p D := by
  have hcop : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)
  have hp := hval p hcop
  rw [Int.cast_natCast] at hp
  rw [hp, fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2]

/-- Under the same hypothesis, at every odd prime `p ∤ N`, `χ p` also equals the cast of
`legendreSym p (fundamentalDiscriminantRadicand D)`. -/
theorem apply_prime_eq_legendreSym_radicand (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = legendreSym p (fundamentalDiscriminantRadicand D) := by
  rw [apply_prime_eq_legendreSym hD hval hp2 hpN,
    legendreSym_fundamentalDiscriminantRadicand hD hp2]

/-- When `2 ≠ 0` in `R` and `χ` agrees on integers coprime to `N` with
`fundamentalDiscriminantCharCast R D hD`, at an odd prime `p`, `χ p = -1` holds if and only if
`p ∤ N` and `D` is not a square in `ZMod p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare [NeZero (2 : R)]
    (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (D : ZMod p) := by
  have h0 : (0 : R) ≠ -1 := fun h ↦ by
    have h10 : (1 : R) = 0 := neg_eq_zero.mp h.symm
    exact NeZero.ne (2 : R) (by rw [← one_add_one_eq_two, h10, add_zero])
  have h1 : (1 : R) ≠ -1 := fun h ↦ by
    have h2 := eq_neg_iff_add_eq_zero.mp h
    rw [one_add_one_eq_two] at h2
    exact NeZero.ne (2 : R) h2
  by_cases hpN : p ∣ N
  · have hnu : ¬ IsUnit (p : ZMod N) := fun hu ↦
      (Fact.out : p.Prime).coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p N).mp hu) hpN
    rw [MulChar.map_nonunit χ hnu]
    exact ⟨fun h ↦ absurd h h0, fun h ↦ absurd hpN h.1⟩
  · rw [apply_prime_eq_legendreSym hD hval hp2 hpN, ← legendreSym.eq_neg_one_iff p]
    simp only [hpN, not_false_eq_true, true_and]
    rcases quadraticChar_isQuadratic (ZMod p) D with hL | hL | hL <;>
      simp [legendreSym, hL, h0, h1]

/-- When `2 ≠ 0` in `R` and `χ` agrees on integers coprime to `N` with
`fundamentalDiscriminantCharCast R D hD`, at an odd prime `p`, `χ p = -1` holds if and only if
`p ∤ N` and the squarefree radicand `fundamentalDiscriminantRadicand D` is not a square in
`ZMod p`. -/
theorem apply_prime_eq_neg_one_iff_not_isSquare_radicand [NeZero (2 : R)]
    (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare (fundamentalDiscriminantRadicand D : ZMod p) := by
  rw [apply_prime_eq_neg_one_iff_not_isSquare hD hval hp2, ← legendreSym.eq_neg_one_iff p,
    ← legendreSym_fundamentalDiscriminantRadicand hD hp2, legendreSym.eq_neg_one_iff p]

/-- At an odd prime `p ∤ N`, a quadratic Dirichlet character `χ` of level `N ≠ 0` takes the value
`legendreSym p D` for `D = if χ (-1) = 1 then χ.conductor else -χ.conductor`. -/
theorem _root_.MulChar.IsQuadratic.apply_prime_eq_legendreSym_ite [NeZero N]
    [Decidable (χ (-1) = 1)] (hq : χ.IsQuadratic) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpN : ¬ p ∣ N) :
    χ p = legendreSym p (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) :=
  apply_prime_eq_legendreSym hq.isFundamentalDiscr_ite
    (fun _ hn ↦ hq.apply_eq_fundamentalDiscriminantCharCast_ite hn) hp2 hpN

/-- At an odd prime `p ∤ N`, a quadratic Dirichlet character `χ` of level `N ≠ 0` takes the value
`legendreSym p (fundamentalDiscriminantRadicand D)` for its signed conductor `D`. -/
theorem _root_.MulChar.IsQuadratic.apply_prime_eq_legendreSym_radicand_ite [NeZero N]
    [Decidable (χ (-1) = 1)] (hq : χ.IsQuadratic) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hpN : ¬ p ∣ N) :
    χ p = legendreSym p (fundamentalDiscriminantRadicand
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor)) :=
  apply_prime_eq_legendreSym_radicand hq.isFundamentalDiscr_ite
    (fun _ hn ↦ hq.apply_eq_fundamentalDiscriminantCharCast_ite hn) hp2 hpN

/-- When `2 ≠ 0` in `R`, a quadratic Dirichlet character `χ` of level `N ≠ 0` satisfies
`χ p = -1` at an odd prime `p` if and only if `p ∤ N` and its signed conductor is not a square in
`ZMod p`. -/
theorem _root_.MulChar.IsQuadratic.apply_prime_eq_neg_one_iff_not_isSquare_ite
    [NeZero (2 : R)] [NeZero N] [Decidable (χ (-1) = 1)] (hq : χ.IsQuadratic) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧
      ¬ IsSquare ((if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor : ℤ) : ZMod p) :=
  apply_prime_eq_neg_one_iff_not_isSquare hq.isFundamentalDiscr_ite
    (fun _ hn ↦ hq.apply_eq_fundamentalDiscriminantCharCast_ite hn) hp2

/-- When `2 ≠ 0` in `R`, a quadratic Dirichlet character `χ` of level `N ≠ 0` satisfies
`χ p = -1` at an odd prime `p` if and only if `p ∤ N` and the squarefree radicand of its signed
conductor is not a square in `ZMod p`. -/
theorem _root_.MulChar.IsQuadratic.apply_prime_eq_neg_one_iff_not_isSquare_radicand_ite
    [NeZero (2 : R)] [NeZero N] [Decidable (χ (-1) = 1)] (hq : χ.IsQuadratic) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = -1 ↔ ¬ p ∣ N ∧ ¬ IsSquare ((fundamentalDiscriminantRadicand
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) : ℤ) : ZMod p) :=
  apply_prime_eq_neg_one_iff_not_isSquare_radicand hq.isFundamentalDiscr_ite
    (fun _ hn ↦ hq.apply_eq_fundamentalDiscriminantCharCast_ite hn) hp2

end OddPrime

end DirichletCharacter

/-! ## Examples

Fundamental discriminants include `1, -4, 8, -8, 5, -3, 12`, whereas `-12 = 4 · (-3)` is not
fundamental because `-3 ≡ 1 (mod 4)`. -/

example : Int.IsFundamentalDiscr 1 ∧ Int.IsFundamentalDiscr (-4) ∧
    Int.IsFundamentalDiscr 8 ∧ Int.IsFundamentalDiscr (-8) ∧
    Int.IsFundamentalDiscr 5 ∧ Int.IsFundamentalDiscr (-3) ∧
    Int.IsFundamentalDiscr 12 ∧ ¬ Int.IsFundamentalDiscr (-12) := by
  have h5 : Int.IsFundamentalDiscr 5 := by
    simpa [oddPrimeDiscriminant_of_mod_four_eq_one (p := 5) (by norm_num)] using
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_five (by decide)).isFundamentalDiscr
  have h3 : Int.IsFundamentalDiscr (-3) := by
    simpa [oddPrimeDiscriminant_of_mod_four_eq_three (p := 3) (by norm_num)] using
      (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_three (by decide)).isFundamentalDiscr
  have h12 : Int.IsFundamentalDiscr 12 := by
    simpa using isPrimeDiscriminant_neg_four.isFundamentalDiscr.mul h3 (by decide)
  have hn12 : ¬ Int.IsFundamentalDiscr (-12) := by
    have h4 : ¬ Int.IsFundamentalDiscr (4 * (-3)) := by
      rw [Int.isFundamentalDiscr_four_mul]
      omega
    simpa using h4
  exact ⟨Int.isFundamentalDiscr_one, isPrimeDiscriminant_neg_four.isFundamentalDiscr,
    isPrimeDiscriminant_eight.isFundamentalDiscr, isPrimeDiscriminant_neg_eight.isFundamentalDiscr,
    h5, h3, h12, hn12⟩

/-! The principal character at level `6` has conductor `1` and unique fundamental discriminant
`D = 1`. At `5` (coprime to `6`) both evaluate to `1`, whereas `D = -3` has `|-3| = 3 ≠ 1`. -/

example :
    let χ : DirichletCharacter ℂ 6 := 1
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 ∧
      χ (5 : ℤ) = fundamentalDiscriminantCharCast ℂ 1 Int.isFundamentalDiscr_one (5 : ℤ) ∧
      (-3 : ℤ).natAbs ≠ χ.conductor := by
  intro χ
  refine ⟨?_, ?_, ?_⟩
  · simp [χ, MulChar.one_apply isUnit_one.neg, DirichletCharacter.conductor_one]
  · rw [(fundamentalDiscriminantCharCast_eq_one_iff Int.isFundamentalDiscr_one).mpr rfl,
      MulChar.one_apply (by decide : IsUnit ((5 : ℤ) : ZMod 6)),
      MulChar.one_apply (by decide : IsUnit ((5 : ℤ) : ZMod (1 : ℤ).natAbs))]
  · simp [χ, DirichletCharacter.conductor_one]

/-! Lifting `χ₄` to level `12` gives conductor `4` and discriminant `D = -4` (radicand `-1`). At
`3` (not coprime to `12`), the lifted character vanishes while `χ_{-4}(3) = -1`, showing that
agreement holds only on integers coprime to `N`. -/

example :
    let χ : DirichletCharacter ℂ 12 :=
      DirichletCharacter.changeLevel (by norm_num : 4 ∣ 12)
        (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
    χ.conductor = 4 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = -4 ∧
      fundamentalDiscriminantRadicand (-4) = -1 ∧
      χ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr
        (3 : ℤ) = -1 := by
  intro χ
  have hcond : χ.conductor = 4 := by
    simp [χ, DirichletCharacter.conductor_changeLevel, DirichletCharacter.conductor_χ₄_ringHomComp]
  have hχ₄ : ZMod.χ₄ (-1) = -1 := by decide
  have hneg1 : χ (-1) = -1 := by simp [χ, hχ₄]
  refine ⟨hcond, ?_, by norm_num [fundamentalDiscriminantRadicand_def], ?_, ?_⟩
  · rw [hcond, hneg1, ite_eq_right (by norm_num)]
    norm_num
  · exact MulChar.map_nonunit χ (by decide)
  · rw [fundamentalDiscriminantChar_neg_four]
    decide

/-! At conductor `8`, `χ₈` and `χ₈'` have the same absolute discriminant `8` and are separated by
their value at `-1`, giving `D = 8` and `D = -8`. -/

example :
    let χpos : DirichletCharacter ℂ 8 := ZMod.χ₈.ringHomComp (Int.castRingHom ℂ)
    let χneg : DirichletCharacter ℂ 8 := ZMod.χ₈'.ringHomComp (Int.castRingHom ℂ)
    (if χpos (-1) = 1 then (χpos.conductor : ℤ) else -χpos.conductor) = 8 ∧
      (if χneg (-1) = 1 then (χneg.conductor : ℤ) else -χneg.conductor) = -8 := by
  intro χpos χneg
  have hχ₈ : ZMod.χ₈ (-1) = 1 := by decide
  have hχ₈' : ZMod.χ₈' (-1) = -1 := by decide
  have hpos1 : χpos (-1) = 1 := by simp [χpos, hχ₈]
  have hneg1 : χneg (-1) = -1 := by simp [χneg, hχ₈']
  refine ⟨?_, ?_⟩
  · rw [hpos1, ite_eq_left rfl, DirichletCharacter.conductor_χ₈_ringHomComp]
    norm_num
  · rw [hneg1, ite_eq_right (by norm_num), DirichletCharacter.conductor_χ₈'_ringHomComp]
    norm_num

/-! The conductor-`12` character `χ = χ₄ · (Legendre mod 3)` has `χ (-1) = 1`, fundamental
discriminant `D = 12` (with squarefree radicand `3`), and values `-1, -1, 1` at `5, 7, 11`. At
`p = 5`, `χ 5 = -1` certifies that both `12` and `3` are nonsquares modulo `5`, and lifting `χ`
to level `24` leaves its conductor `12` and discriminant `12` unchanged. -/

example :
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    let χ : DirichletCharacter ℂ 12 :=
      DirichletCharacter.changeLevel (by norm_num : 4 ∣ 12)
          (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) *
        DirichletCharacter.changeLevel (by norm_num : 3 ∣ 12)
          ((quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ))
    let χ24 : DirichletCharacter ℂ 24 := DirichletCharacter.changeLevel (by norm_num : 12 ∣ 24) χ
    χ.conductor = 12 ∧
      (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 12 ∧
      fundamentalDiscriminantRadicand 12 = 3 ∧
      χ (5 : ℤ) = -1 ∧ χ (7 : ℤ) = -1 ∧ χ (11 : ℤ) = 1 ∧
      ¬ IsSquare (12 : ZMod 5) ∧ ¬ IsSquare (3 : ZMod 5) ∧
      χ24.conductor = 12 ∧
      (if χ24 (-1) = 1 then (χ24.conductor : ℤ) else -χ24.conductor) = 12 := by
  intro _ χ χ24
  have hR : ringChar ℂ ≠ 2 := by simp [ringChar.eq_zero]
  have hq : χ.IsQuadratic :=
    ((ZMod.isQuadratic_χ₄.comp _).changeLevel _).mul
      ((quadraticChar_isQuadratic (ZMod 3) |>.comp _).changeLevel _)
  have hcond : χ.conductor = 12 := by
    rw [DirichletCharacter.conductor_mul_of_coprime] <;>
      simp only [DirichletCharacter.conductor_changeLevel,
        DirichletCharacter.conductor_χ₄_ringHomComp,
        DirichletCharacter.conductor_changeLevel_quadraticChar hR (by norm_num : 3 ≠ 2)]
    norm_num
  have hχ₄ : ZMod.χ₄ (-1) = -1 := by decide
  have hq3 : quadraticChar (ZMod 3) (-1) = -1 := by decide
  have hneg1 : χ (-1) = 1 := by simp [χ, hχ₄, hq3]
  have hD : (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 12 := by
    rw [hneg1, ite_eq_left rfl, hcond]
    norm_num
  have hrad : fundamentalDiscriminantRadicand 12 = 3 := by
    norm_num [fundamentalDiscriminantRadicand_def]
  have hval (n : ℕ) (hn : IsCoprime (n : ℤ) 12) (ho : Odd n) :
      χ n = (jacobiSym 12 n : ℂ) := by
    have hn' := hq.apply_eq_fundamentalDiscriminantCharCast_ite hn
    rw [Int.cast_natCast] at hn'
    rw [hn', fundamentalDiscriminantCharCast_apply]
    have key : ∀ (D : ℤ) (hD' : Int.IsFundamentalDiscr D), D = 12 →
        (fundamentalDiscriminantChar D hD' (n : ℤ) : ℂ) = (jacobiSym 12 n : ℂ) := by
      rintro _ hD' rfl
      rw [fundamentalDiscriminantChar_natCast_eq_jacobiSym hD' ho]
    exact key _ hq.isFundamentalDiscr_ite hD
  have h5 : χ (5 : ℤ) = -1 := by
    simpa using (hval 5 (by decide) (by decide)).trans (by norm_num)
  have h7 : χ (7 : ℤ) = -1 := by
    simpa using (hval 7 (by decide) (by decide)).trans (by norm_num)
  have h11 : χ (11 : ℤ) = 1 := by
    simpa using (hval 11 (by decide) (by decide)).trans (by norm_num)
  have h5nat : χ (5 : ℕ) = -1 := by simpa using h5
  have hnsqD : ¬ IsSquare (12 : ZMod 5) := by
    have h := (hq.apply_prime_eq_neg_one_iff_not_isSquare_ite (p := 5) (by decide)).mp h5nat
    simpa [hD] using h.2
  have hnsqd : ¬ IsSquare (3 : ZMod 5) := by
    have h :=
      (hq.apply_prime_eq_neg_one_iff_not_isSquare_radicand_ite (p := 5) (by decide)).mp h5nat
    simpa [hD, hrad] using h.2
  refine ⟨hcond, hD, hrad, h5, h7, h11, hnsqD, hnsqd, ?_, ?_⟩
  · simp [χ24, DirichletCharacter.conductor_changeLevel, hcond]
  · rw [DirichletCharacter.ite_changeLevel_conductor, hD]

/-! The odd-prime hypothesis `p ≠ 2` in `apply_prime_eq_legendreSym` is sharp: for `D = 5`,
`χ_5(2) = χ₈(5) = -1`, whereas `legendreSym 2 5 = 1`. -/

example :
    ∃ h5 : Int.IsFundamentalDiscr 5,
      fundamentalDiscriminantChar 5 h5 (2 : ℤ) = -1 ∧ legendreSym 2 5 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨by simpa [oddPrimeDiscriminant_of_mod_four_eq_one (p := 5) (by norm_num)] using
    (isPrimeDiscriminant_oddPrimeDiscriminant Nat.prime_five (by decide)).isFundamentalDiscr,
    ?_, by decide⟩
  rw [Int.cast_ofNat, fundamentalDiscriminantChar_two]
  decide
