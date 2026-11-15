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
# The primitive discriminant of a quadratic Dirichlet character

Every quadratic Dirichlet character `χ` of nonzero level `N` over a commutative ring `R` agrees,
at all integers coprime to `N`, with the scalar realization `fundamentalDiscriminantCharCast R D hD`
of a unique fundamental discriminant `D` of absolute value `χ.conductor`
(`DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`). Explicitly, `D` is `χ.conductor`
when `χ (-1) = 1` and `-χ.conductor` otherwise
(`MulChar.IsQuadratic.isFundamentalDiscr_ite_conductor`,
`MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_ite_conductor`). The principal
character at any nonzero level corresponds to `D = 1`, and when `2 = 0` in `R` every quadratic
character is principal so `D = 1` still holds without any characteristic assumption on `R`.

When `χ` is primitive (`χ.conductor = N`), the agreement holds at *all* integers, not only those
coprime to `N` (`DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`,
`DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite`). That primitive case
is proved locally: at a prime power `p ^ k`, `k ≠ 0`, a primitive quadratic character is the
Legendre character modulo `p` (`k = 1`, `P = p*`) for odd `p`, and `χ₄`, `χ₈` or `χ₈'` (`k = 2` or
`3`, `P = -4`, `8` or `-8`) for `p = 2`, and `D` is the product of the prime discriminants of the
local factors of `χ`. The general-level theorem then passes to `χ.primitiveCharacter`, which has
the same conductor, quadraticity and value at `-1` as `χ`, and agrees with `χ` on integers coprime
to `N`.

Writing `D = fundamentalDiscriminant d` for the unique squarefree radicand `d` of `D` (`d = D` when
`D ≡ 1 (mod 4)` and `d = D / 4` otherwise), the character `χ_D` takes at every odd prime `p` the
common value `legendreSym p D = legendreSym p d` (including `0` when `p ∣ D`), and `χ p` takes that
value whenever `p ∤ N`. In particular, when `2 ≠ 0` in `R`, a value `χ p = -1` at an odd prime `p`
implies that neither `D` nor `d` is a square modulo `p`.

## Main results

* `DirichletCharacter.IsPrimitive.exists_isPrimeDiscriminant_apply_eq`,
  `DirichletCharacter.IsPrimitive.exists_isFundamentalDiscr_apply_eq`,
  `DirichletCharacter.IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq`: primitive quadratic
  characters of level `N ≠ 0` are Kronecker characters of a unique fundamental discriminant of
  absolute value `N`.
* `DirichletCharacter.IsPrimitive.isFundamentalDiscr_ite`,
  `DirichletCharacter.IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite`: for primitive
  quadratic `χ` of level `N ≠ 0`, that discriminant is `N` if `χ (-1) = 1` and `-N` otherwise.
* `DirichletCharacter.eq_ite_conductor_of_isFundamentalDiscr_of_apply_eq`: uniqueness of `D` from
  `|D| = χ.conductor` and agreement on integers coprime to `N`.
* `MulChar.IsQuadratic.isFundamentalDiscr_ite_conductor`,
  `MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_ite_conductor`,
  `MulChar.IsQuadratic.apply_eq_intCast_fundamentalDiscriminantChar_ite_conductor`: the explicit
  discriminant and character values (both scalar-cast and integer-cast) for quadratic `χ` at any
  level `N ≠ 0`.
* `DirichletCharacter.existsUnique_isFundamentalDiscr_apply_eq`: existence and uniqueness of the
  fundamental discriminant `D` of a quadratic Dirichlet character at any level `N ≠ 0`.
* `DirichletCharacter.existsUnique_squarefree_apply_eq_fundamentalDiscriminantCharCast`: the
  corresponding existence and uniqueness for the squarefree radicand `d` with
  `D = fundamentalDiscriminant d`.
* `DirichletCharacter.apply_natCast_eq_legendreSym_of_apply_eq`,
  `DirichletCharacter.apply_natCast_eq_legendreSym_radicand_of_apply_eq`,
  `DirichletCharacter.not_isSquare_of_apply_natCast_eq_neg_one`,
  `DirichletCharacter.not_isSquare_radicand_of_apply_natCast_eq_neg_one`: the odd-prime Legendre
  dictionary for `D` and `d`, and the nonsquare criterion modulo `p` from `χ p = -1`.

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

/-! ### Uniqueness and the signed-conductor formula -/

/-- Any fundamental discriminant `D` of absolute value `χ.conductor` whose character agrees with
`χ` at all integers coprime to the level `N` equals `χ.conductor` when `χ (-1) = 1` and
`-χ.conductor` otherwise. Both `N ≠ 0` and the quadraticity of `χ` follow from the hypotheses:
when `2 ≠ 0` in `R` the sign is read off `χ (-1) = D.sign`, and when `2 = 0` in `R` the character
`χ` is `1` so `|D| = 1` forces `D = 1`. -/
theorem eq_ite_conductor_of_isFundamentalDiscr_of_apply_eq [DecidableEq R] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (habs : D.natAbs = χ.conductor)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n) :
    D = if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  have : NeZero N := ⟨by
    rintro rfl
    rw [conductor_eq_zero_iff_level_eq_zero.mpr rfl] at habs
    exact hD.ne_zero (Int.natAbs_eq_zero.mp habs)⟩
  have hq : χ.IsQuadratic := fun a ↦ by
    by_cases ha : IsUnit a
    · have hcop : IsCoprime (a.val : ℤ) N :=
        Nat.isCoprime_iff_coprime.mpr
          ((ZMod.isUnit_iff_coprime a.val N).mp (by rwa [ZMod.natCast_zmod_val]))
      have heq : χ a = fundamentalDiscriminantCharCast R D hD (a.val : ℤ) := by
        simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hval a.val hcop
      rw [heq]
      exact fundamentalDiscriminantCharCast_isQuadratic hD _
    · exact Or.inl (MulChar.map_nonunit χ ha)
  by_cases h2 : (2 : R) = 0
  · obtain rfl : χ = 1 := hq.eq_one_of_two_eq_zero h2
    rw [conductor_one] at habs ⊢
    rw [ite_eq_left (MulChar.one_apply isUnit_one.neg)]
    rcases Int.natAbs_eq_iff.mp habs with rfl | rfl
    · rfl
    · exact absurd hD (by decide)
  · have : NeZero (2 : R) := ⟨h2⟩
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

section Sign

variable [DecidableEq R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- The fundamental discriminant of a primitive quadratic character `χ` of nonzero level `N` is
`N` if `χ (-1) = 1` and `-N` otherwise. -/
private theorem IsPrimitive.exists_eq_ite_apply_eq (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : Int.IsFundamentalDiscr D), D = (if χ (-1) = 1 then (N : ℤ) else -N) ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  obtain ⟨D, hD, hDN, hval⟩ := hχ.exists_isFundamentalDiscr_apply_eq hq
  refine ⟨D, hD, ?_, hval⟩
  simpa only [(isPrimitive_def _).mp hχ] using
    eq_ite_conductor_of_isFundamentalDiscr_of_apply_eq hD
      (hDN.trans ((isPrimitive_def _).mp hχ).symm) (fun n _ ↦ hval n)

/-- The integer `N` if `χ (-1) = 1` and `-N` otherwise is a fundamental discriminant for every
primitive quadratic character `χ` of nonzero level `N`. -/
theorem IsPrimitive.isFundamentalDiscr_ite (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (N : ℤ) else -N) := by
  obtain ⟨D, hD, rfl, -⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hD

/-- **Primitive quadratic characters are Kronecker characters, with their discriminant.** A
primitive quadratic character `χ` of nonzero level `N` is the character of the fundamental
discriminant `D = N` if `χ (-1) = 1` and `-N` otherwise:
`χ n = fundamentalDiscriminantCharCast R D n` at every integer `n`. For the principal character,
primitive only at level `1`, this is `D = 1`. -/
theorem IsPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ n = fundamentalDiscriminantCharCast R _ (hχ.isFundamentalDiscr_ite hq) n := by
  obtain ⟨D, hD, rfl, hval⟩ := hχ.exists_eq_ite_apply_eq hq
  exact hval n

/-- At an odd natural number `n`, a primitive quadratic character `χ` of nonzero level `N` takes
the Jacobi-symbol value `jacobiSym D n`, including `0` when `n` is not coprime to `N`. -/
theorem IsPrimitive.apply_natCast_eq_jacobiSym_ite (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    {n : ℕ} (hn : _root_.Odd n) :
    χ n = (jacobiSym (if χ (-1) = 1 then (N : ℤ) else -N) n : R) := by
  have h := hχ.apply_eq_fundamentalDiscriminantCharCast_ite hq n
  rwa [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym _ hn, Int.cast_natCast] at h

/-- At an odd prime `p`, a primitive quadratic character `χ` of nonzero level `N` takes the
Legendre-symbol value `legendreSym p D`, including `0` when `p ∣ N`. -/
theorem IsPrimitive.apply_natCast_eq_legendreSym_ite (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ p = (legendreSym p (if χ (-1) = 1 then (N : ℤ) else -N) : R) := by
  have h := hχ.apply_eq_fundamentalDiscriminantCharCast_ite hq p
  rwa [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym _ hp2, Int.cast_natCast] at h

end Sign

/-- **Uniqueness of the discriminant of a primitive quadratic character.** A primitive quadratic
character `χ` of nonzero level `N` agrees at all integers with the character of a unique
fundamental discriminant `D` of absolute value `N`. -/
theorem IsPrimitive.existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = N ∧
      ∀ n : ℤ, χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  refine ⟨if χ (-1) = 1 then (N : ℤ) else -N,
    ⟨hχ.isFundamentalDiscr_ite hq, by split_ifs <;> simp,
      hχ.apply_eq_fundamentalDiscriminantCharCast_ite hq⟩, ?_⟩
  rintro D ⟨hD, habs, hval⟩
  simpa only [(isPrimitive_def _).mp hχ] using
    eq_ite_conductor_of_isFundamentalDiscr_of_apply_eq hD
      (habs.trans ((isPrimitive_def _).mp hχ).symm) (fun n _ ↦ hval n)

/-! ### Arbitrary positive levels -/

end DirichletCharacter

namespace MulChar.IsQuadratic

open DirichletCharacter

variable {R : Type*} [CommRing R] [DecidableEq R] {N : ℕ} [NeZero N] {χ : DirichletCharacter R N}

/-- For every quadratic Dirichlet character `χ` of nonzero level `N`, the signed conductor
(`χ.conductor` when `χ (-1) = 1` and `-χ.conductor` otherwise) is a fundamental discriminant. -/
theorem isFundamentalDiscr_ite_conductor (hq : χ.IsQuadratic) :
    Int.IsFundamentalDiscr (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  simpa only [primitiveCharacter_apply_neg_one] using
    χ.primitiveCharacter_isPrimitive.isFundamentalDiscr_ite hq.primitiveCharacter

/-- The primitive character of a quadratic Dirichlet character `χ` of nonzero level `N` agrees at
every integer `n` with the character of its signed conductor. -/
theorem primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor
    (hq : χ.IsQuadratic) (n : ℤ) :
    χ.primitiveCharacter n =
      fundamentalDiscriminantCharCast R _ hq.isFundamentalDiscr_ite_conductor n := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have h := χ.primitiveCharacter_isPrimitive.apply_eq_fundamentalDiscriminantCharCast_ite
    hq.primitiveCharacter n
  generalize_proofs h1 at h
  revert h1 h
  rw [primitiveCharacter_apply_neg_one]
  intro _ h
  exact h

/-- A quadratic Dirichlet character `χ` of nonzero level `N` agrees at every integer `n` coprime
to `N` with the scalar realization of the character of its signed conductor. -/
theorem apply_eq_fundamentalDiscriminantCharCast_ite_conductor
    (hq : χ.IsQuadratic) {n : ℤ} (hn : IsCoprime n N) :
    χ n = fundamentalDiscriminantCharCast R _ hq.isFundamentalDiscr_ite_conductor n := by
  rw [← χ.primitiveCharacter_apply_of_isCoprime hn,
    hq.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor]

/-- Integer-valued form of
`MulChar.IsQuadratic.apply_eq_fundamentalDiscriminantCharCast_ite_conductor`: at every integer `n`
coprime to `N`, `χ n` is the cast to `R` of `fundamentalDiscriminantChar D _ n`. -/
theorem apply_eq_intCast_fundamentalDiscriminantChar_ite_conductor
    (hq : χ.IsQuadratic) {n : ℤ} (hn : IsCoprime n N) :
    χ n = (fundamentalDiscriminantChar _ hq.isFundamentalDiscr_ite_conductor n : R) := by
  rw [hq.apply_eq_fundamentalDiscriminantCharCast_ite_conductor hn,
    fundamentalDiscriminantCharCast_apply]

/-- At every odd natural number `n`, including those sharing prime factors with the conductor,
`χ.primitiveCharacter n` is the Jacobi symbol of the signed conductor of `χ`. -/
theorem primitiveCharacter_apply_natCast_eq_jacobiSym_ite_conductor
    (hq : χ.IsQuadratic) {n : ℕ} (hn : _root_.Odd n) :
    χ.primitiveCharacter n =
      (jacobiSym (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) n : R) := by
  have h := hq.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor n
  rwa [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym _ hn, Int.cast_natCast] at h

/-- At every odd prime `p`, including primes dividing the conductor, `χ.primitiveCharacter p` is
the Legendre symbol of the signed conductor of `χ` modulo `p`. -/
theorem primitiveCharacter_apply_natCast_eq_legendreSym_ite_conductor
    (hq : χ.IsQuadratic) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    χ.primitiveCharacter p =
      (legendreSym p (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) : R) := by
  have h := hq.primitiveCharacter_apply_eq_fundamentalDiscriminantCharCast_ite_conductor p
  rwa [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym _ hp2, Int.cast_natCast] at h

/-- At an odd natural number `n` coprime to `N`, a quadratic Dirichlet character `χ` of nonzero
level `N` takes the Jacobi-symbol value of its signed conductor. -/
theorem apply_natCast_eq_jacobiSym_ite_conductor (hq : χ.IsQuadratic)
    {n : ℕ} (hn : _root_.Odd n) (hcop : n.Coprime N) :
    χ n = (jacobiSym (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) n : R) := by
  have h := hq.apply_eq_intCast_fundamentalDiscriminantChar_ite_conductor
    (Nat.isCoprime_iff_coprime.mpr hcop)
  rwa [fundamentalDiscriminantChar_natCast_eq_jacobiSym _ hn, Int.cast_natCast] at h

/-- At an odd prime `p ∤ N`, a quadratic Dirichlet character `χ` of nonzero level `N` takes the
Legendre-symbol value of its signed conductor modulo `p`. -/
theorem apply_natCast_eq_legendreSym_ite_conductor (hq : χ.IsQuadratic)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) : R) := by
  have hcop : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)
  have h := hq.apply_eq_intCast_fundamentalDiscriminantChar_ite_conductor hcop
  rwa [fundamentalDiscriminantChar_natCast_eq_legendreSym _ hp2, Int.cast_natCast] at h

end MulChar.IsQuadratic

namespace DirichletCharacter

variable {R : Type*} [CommRing R]

/-- **Naturality of the signed conductor under `changeLevel`.** Lifting `χ` to a nonzero multiple
`M` of its level preserves both `χ (-1)` and `χ.conductor`, hence preserves the signed conductor. -/
theorem ite_conductor_changeLevel {S : Type*} [CommMonoidWithZero S] [DecidableEq S]
    {N M : ℕ} [NeZero M] (hNM : N ∣ M) (χ : DirichletCharacter S N) :
    (if changeLevel hNM χ (-1) = 1 then ((changeLevel hNM χ).conductor : ℤ)
      else -(changeLevel hNM χ).conductor) =
      if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor := by
  rw [changeLevel_apply_neg_one, conductor_changeLevel]

/-- **Naturality of coprime character agreement under `changeLevel`.** If `χ` agrees with
`fundamentalDiscriminantCharCast R D hD` on integers coprime to `N`, then for `N ∣ M` its lift
`changeLevel hNM χ` agrees with the same character on integers coprime to `M`. -/
theorem changeLevel_apply_eq_fundamentalDiscriminantCharCast_of_apply_eq {N M : ℕ} (hNM : N ∣ M)
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℤ} (hn : IsCoprime n M) :
    changeLevel hNM χ n = fundamentalDiscriminantCharCast R D hD n := by
  rw [changeLevel_eq_cast_of_dvd' χ hNM hn,
    hval n (hn.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hNM))]

/-- **The primitive discriminant of a quadratic Dirichlet character.** Every quadratic Dirichlet
character `χ` of nonzero level `N` over a commutative ring `R` agrees, at all integers coprime to
`N`, with the scalar realization `fundamentalDiscriminantCharCast R D hD` of a unique fundamental
discriminant `D` of absolute value `χ.conductor` (Montgomery–Vaughan, Theorem 9.13). The principal
character corresponds to `D = 1`; in general `D` is `χ.conductor` when `χ (-1) = 1` and
`-χ.conductor` otherwise. -/
theorem existsUnique_isFundamentalDiscr_apply_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! D : ℤ, ∃ hD : Int.IsFundamentalDiscr D, D.natAbs = χ.conductor ∧
      ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n := by
  classical
  refine ⟨if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor,
    ⟨hq.isFundamentalDiscr_ite_conductor, by split_ifs <;> simp,
      fun _ hn ↦ hq.apply_eq_fundamentalDiscriminantCharCast_ite_conductor hn⟩, ?_⟩
  rintro D ⟨hD, habs, hval⟩
  exact eq_ite_conductor_of_isFundamentalDiscr_of_apply_eq hD habs hval

/-! ### Squarefree radicands, odd primes, and nonsquares modulo `p` -/

/-- **The primitive squarefree radicand of a quadratic Dirichlet character.** Every quadratic
Dirichlet character `χ` of nonzero level `N` corresponds to a unique squarefree integer `d` such
that `fundamentalDiscriminant d` has absolute value `χ.conductor` and its character agrees with `χ`
at every integer coprime to `N`. -/
theorem existsUnique_squarefree_apply_eq_fundamentalDiscriminantCharCast {N : ℕ} [NeZero N]
    {χ : DirichletCharacter R N} (hq : χ.IsQuadratic) :
    ∃! d : ℤ, ∃ hd : Squarefree d,
      (fundamentalDiscriminant d).natAbs = χ.conductor ∧
        ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R
          (fundamentalDiscriminant d) (isFundamentalDiscr_fundamentalDiscriminant hd) n := by
  obtain ⟨D, ⟨hD, habs, hval⟩, huniq⟩ := χ.existsUnique_isFundamentalDiscr_apply_eq hq
  obtain ⟨d, ⟨hd, rfl⟩, -⟩ := hD.existsUnique_squarefree_and_fundamentalDiscriminant_eq
  refine ⟨d, ⟨hd, habs, hval⟩, fun d' ⟨hd', habs', hval'⟩ ↦
    fundamentalDiscriminant_injective
      (huniq _ ⟨isFundamentalDiscr_fundamentalDiscriminant hd', habs', hval'⟩)⟩

/-- If `χ` agrees with `fundamentalDiscriminantCharCast R D hD` on integers coprime to `N`, then at
every odd natural number `n` coprime to `N` its value is `jacobiSym D n`. -/
theorem apply_natCast_eq_jacobiSym_of_apply_eq {N : ℕ} {χ : DirichletCharacter R N} {D : ℤ}
    (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {n : ℕ} (hn : _root_.Odd n) (hcop : n.Coprime N) :
    χ n = (jacobiSym D n : R) := by
  have h := hval n (Nat.isCoprime_iff_coprime.mpr hcop)
  rwa [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_jacobiSym hD hn, Int.cast_natCast] at h

/-- Radicand form of `apply_natCast_eq_jacobiSym_of_apply_eq`: when
`D = fundamentalDiscriminant d`, `χ n = jacobiSym d n` at every odd natural number `n` coprime to
`N`. -/
theorem apply_natCast_eq_jacobiSym_radicand_of_apply_eq {N : ℕ} {χ : DirichletCharacter R N}
    {d : ℤ} (hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d))
    (hval : ∀ n : ℤ, IsCoprime n N →
      χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d) hD n)
    {n : ℕ} (hn : _root_.Odd n) (hcop : n.Coprime N) :
    χ n = (jacobiSym d n : R) := by
  rw [apply_natCast_eq_jacobiSym_of_apply_eq hD hval hn hcop,
    jacobiSym_fundamentalDiscriminant d hn]

/-- If `χ` agrees with `fundamentalDiscriminantCharCast R D hD` on integers coprime to `N`, then at
every odd prime `p ∤ N` its value is `legendreSym p D`. -/
theorem apply_natCast_eq_legendreSym_of_apply_eq {N : ℕ} {χ : DirichletCharacter R N} {D : ℤ}
    (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p D : R) := by
  have hcop : IsCoprime (p : ℤ) N :=
    Nat.isCoprime_iff_coprime.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpN)
  have h := hval p hcop
  rwa [fundamentalDiscriminantCharCast_apply,
    fundamentalDiscriminantChar_natCast_eq_legendreSym hD hp2, Int.cast_natCast] at h

/-- **Odd-prime dictionary for the squarefree radicand.** If `χ` agrees on integers coprime to `N`
with the character of `fundamentalDiscriminant d`, then at every odd prime `p ∤ N` its value is
`legendreSym p d`. -/
theorem apply_natCast_eq_legendreSym_radicand_of_apply_eq {N : ℕ} {χ : DirichletCharacter R N}
    {d : ℤ} (hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d))
    (hval : ∀ n : ℤ, IsCoprime n N →
      χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d) hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpN : ¬ p ∣ N) :
    χ p = (legendreSym p d : R) := by
  rw [apply_natCast_eq_legendreSym_of_apply_eq hD hval hp2 hpN,
    legendreSym_fundamentalDiscriminant d hp2]

/-- **Nonsquare criterion for the discriminant `D`.** When `2 ≠ 0` in `R` and `χ` agrees on
integers coprime to `N` with the character of `D`, a value `χ p = -1` at an odd prime `p` forces
`p ∤ N` and `¬ IsSquare (D : ZMod p)`. -/
theorem not_isSquare_of_apply_natCast_eq_neg_one [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {D : ℤ} (hD : Int.IsFundamentalDiscr D)
    (hval : ∀ n : ℤ, IsCoprime n N → χ n = fundamentalDiscriminantCharCast R D hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : χ p = -1) :
    ¬ IsSquare (D : ZMod p) := by
  have : Nontrivial R := ⟨⟨2, 0, two_ne_zero⟩⟩
  have hm1 : (-1 : R) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hcop : IsCoprime (p : ℤ) N :=
    (χ.apply_ne_zero_iff p).mp (by simpa only [Int.cast_natCast, hp] using hm1)
  have hpN : ¬ p ∣ N :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp (Nat.isCoprime_iff_coprime.mp hcop)
  have hleg : (legendreSym p D : R) = -1 := by
    rw [← apply_natCast_eq_legendreSym_of_apply_eq hD hval hp2 hpN, hp]
  refine (legendreSym.eq_neg_one_iff p).mp ?_
  by_cases h0 : (D : ZMod p) = 0
  · rw [(legendreSym.eq_zero_iff p D).mpr h0, Int.cast_zero] at hleg
    exact absurd hleg.symm hm1
  · rcases legendreSym.eq_one_or_neg_one p h0 with h | h
    · rw [h, Int.cast_one] at hleg
      exact absurd (by linear_combination hleg : (2 : R) = 0) two_ne_zero
    · exact h

/-- **Nonsquare criterion for the squarefree radicand `d`.** When `2 ≠ 0` in `R` and `χ` agrees on
integers coprime to `N` with the character of `fundamentalDiscriminant d`, a value `χ p = -1` at an
odd prime `p` implies `¬ IsSquare (d : ZMod p)`. -/
theorem not_isSquare_radicand_of_apply_natCast_eq_neg_one [NeZero (2 : R)] {N : ℕ}
    {χ : DirichletCharacter R N} {d : ℤ} (hD : Int.IsFundamentalDiscr (fundamentalDiscriminant d))
    (hval : ∀ n : ℤ, IsCoprime n N →
      χ n = fundamentalDiscriminantCharCast R (fundamentalDiscriminant d) hD n)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : χ p = -1) :
    ¬ IsSquare (d : ZMod p) := by
  rw [← legendreSym.eq_neg_one_iff p, ← legendreSym_fundamentalDiscriminant d hp2,
    legendreSym.eq_neg_one_iff p]
  exact not_isSquare_of_apply_natCast_eq_neg_one hD hval hp2 hp

/-- Direct signed-conductor form of `not_isSquare_of_apply_natCast_eq_neg_one`: when `2 ≠ 0` in
`R`, `χ` is quadratic, and `χ p = -1` at an odd prime `p`, the signed conductor of `χ` is not a
square modulo `p`. -/
theorem _root_.MulChar.IsQuadratic.not_isSquare_ite_conductor_of_apply_natCast_eq_neg_one
    [DecidableEq R] [NeZero (2 : R)] {N : ℕ} {χ : DirichletCharacter R N}
    (hq : χ.IsQuadratic) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : χ p = -1) :
    ¬ IsSquare ((if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor : ℤ) : ZMod p) := by
  have : Nontrivial R := ⟨⟨2, 0, two_ne_zero⟩⟩
  have hm1 : (-1 : R) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hcop : IsCoprime (p : ℤ) N :=
    (χ.apply_ne_zero_iff p).mp (by simpa only [Int.cast_natCast, hp] using hm1)
  have : NeZero N := ⟨by
    rintro rfl
    exact (Fact.out : p.Prime).ne_one
      (Nat.isUnit_iff.mp (Int.ofNat_isUnit.mp (isCoprime_zero_right.mp hcop)))⟩
  exact not_isSquare_of_apply_natCast_eq_neg_one hq.isFundamentalDiscr_ite_conductor
    (fun _ hn ↦ hq.apply_eq_fundamentalDiscriminantCharCast_ite_conductor hn) hp2 hp

/-! ### Examples -/

/-- `D = 12` has squarefree radicand `d = 3`, while `D = -4` has squarefree radicand `d = -1`. -/
example : fundamentalDiscriminant 3 = 12 ∧ fundamentalDiscriminant (-1) = -4 := by
  norm_num [fundamentalDiscriminant_def]

/-- For `χ₄` lifted to level `12`, the conductor is `4`, `χ (-1) = -1`, so the primitive
discriminant is `-4`; at `n = 3` (not coprime to `12`) the lifted character vanishes whereas
`χ_{-4}(3) = -1`. -/
example :
    let χ : DirichletCharacter ℤ 12 := changeLevel (by decide : 4 ∣ 12) ZMod.χ₄
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = -4 ∧
      χ (3 : ℤ) = 0 ∧
      fundamentalDiscriminantChar (-4) isPrimeDiscriminant_neg_four.isFundamentalDiscr (3 : ℤ) =
        -1 := by
  refine ⟨?_, ?_, ?_⟩
  · have hc : (changeLevel (by decide : 4 ∣ 12) ZMod.χ₄).conductor = 4 := by
      rw [conductor_changeLevel]
      exact conductor_eq_four_of_apply_one_ne_apply_three ZMod.χ₄ (by decide)
    have hm1 : changeLevel (by decide : 4 ∣ 12) ZMod.χ₄ (-1) = -1 := by
      rw [changeLevel_apply_neg_one]
      decide
    simp [hc, hm1]
  · exact MulChar.map_nonunit _ (by decide)
  · rw [fundamentalDiscriminantChar_neg_four]
    decide

/-- For the principal character at level `6`, the primitive discriminant is `1`. -/
example :
    let χ : DirichletCharacter ℤ 6 := 1
    (if χ (-1) = 1 then (χ.conductor : ℤ) else -χ.conductor) = 1 := by
  simp [conductor_one, MulChar.one_apply isUnit_one.neg]

end DirichletCharacter
