/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.NormCoeff
public import TauCeti.RingTheory.DedekindDomain.Ideal
public import TauCeti.RingTheory.Ideal.Norm.AbsNorm

/-!
# Completely multiplicative ideal weights

The completely multiplicative specializations of `TauCeti.IdealArithmeticFunction`: the two
carriers on which every Euler product, Hecke character and character-family argument of this
development is stated.

A `TauCeti.MultiplicativeIdealWeight K` is a monoid-with-zero homomorphism
`Ideal (𝓞 K) →*₀ ℂ` killing only finitely many height-one primes, and
`TauCeti.UnitaryIdealWeight K` is the subtype of those whose values have modulus `1` away from
that finite bad set. Using Mathlib's `→*₀` vocabulary is what pins the zero-ideal law
`χ ⊥ = 0`; the finiteness condition is what bounds the bad local factors of the Euler product.

Both carriers are *degree one*: the value at `𝔭 ^ n` is forced to be `χ 𝔭 ^ n`. They are
therefore deliberately too narrow for the ideal Möbius function or for coefficient systems
whose prime-power values are independent local data; those get separate carriers.

The organising notion is `Ideal.IsPrimeTo`, an ideal of a Dedekind domain being nonzero and
divisible by no prime of a given set; it is stated for a general Dedekind domain because
nothing in it is specific to a number field. The good ideals of a weight are the ideals
prime to its bad primes, and `Ideal.IsPrimeTo.induction_on` factors such an ideal into
good primes; this is the engine behind both
`TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood` and
`TauCeti.UnitaryIdealWeight.norm_eq_one`.

## Main declarations

* `Ideal.IsPrimeTo`: an ideal is nonzero and no prime of `S` divides it, with its
  multiplicativity (`Ideal.isPrimeTo_mul_iff`) and its induction principle
  (`Ideal.IsPrimeTo.induction_on`);
* `TauCeti.MultiplicativeIdealWeight`: the general completely multiplicative carrier, its
  `TauCeti.MultiplicativeIdealWeight.badPrimes` and its good ideals
  (`TauCeti.MultiplicativeIdealWeight.IsGood`);
* `TauCeti.MultiplicativeIdealWeight.apply_ne_zero_iff_isGood`: a weight is nonzero exactly on
  the good ideals;
* `TauCeti.MultiplicativeIdealWeight.ext_heightOneSpectrum`: a weight is determined by its
  values at the height-one primes;
* `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`, the pointwise `CommMonoid` structure (whose
  unit is the trivial weight), `TauCeti.MultiplicativeIdealWeight.restrict`,
  `TauCeti.MultiplicativeIdealWeight.conj` and
  `TauCeti.MultiplicativeIdealWeight.normTwist`: the constructors and operations;
* `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood` and
  `TauCeti.MultiplicativeIdealWeight.IsTrivialOnGood`: the weights agreeing with a purely
  imaginary norm twist, respectively with the trivial weight, on their good ideals, with the
  structure theorem `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.eq_normTwist`, its
  converse `TauCeti.MultiplicativeIdealWeight.isNormTwistOnGood_normTwist_ofBadPrimes`, and the
  behaviour of the parameter under conjugation, the pointwise product and a further twist;
* `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction`: passage to the general
  carrier, inverted by `TauCeti.IdealArithmeticFunction.zeroExtend`;
* `TauCeti.UnitaryIdealWeight`: the unitary subtype, with
  `TauCeti.UnitaryIdealWeight.norm_eq_one` on all good ideals,
  `TauCeti.UnitaryIdealWeight.norm_normTwist` for the modulus of an arbitrary norm twist,
  `TauCeti.UnitaryIdealWeight.ofPowEqOne` for finite-order weights, and the operations
  `TauCeti.UnitaryIdealWeight.conj`, `TauCeti.UnitaryIdealWeight.restrict` and
  `TauCeti.UnitaryIdealWeight.normTwist` (the last for the imaginary norm twists only), and
  `TauCeti.UnitaryIdealWeight.toIdealArithmeticFunction` for its passage to the general carrier;
* `TauCeti.MultiplicativeIdealWeight.map` and `TauCeti.UnitaryIdealWeight.map`, with their
  equivalences `mapEquiv`: functoriality under an isomorphism `K ≃+* L` of the ambient fields,
  together with the identity and composition laws, the preservation of the pointwise product
  (`map_one` and `map_mul` on both carriers), the naturality of restriction, conjugation and norm
  twists, and the compatibilities
  `TauCeti.MultiplicativeIdealWeight.badPrimes_map` and
  `TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_map`.

## Rejection tests

The two worked negative examples of this layer are proved here.
`TauCeti.MultiplicativeIdealWeight.coe_ne_const_one` says the everywhere-one function on *all*
integral ideals underlies no weight, because `→*₀` forces the value `0` at `⊥` — the
everywhere-one function on the *nonzero* ideals is the trivial weight instead
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`).
`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one` says that a norm twist with
`Re z ≠ 0` changes the modulus at every good ideal of absolute norm greater than one, so such
twists live only in the general carrier.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* `TauCetiRoadmap/ArithmeticDirichletSeries/README.md` and its `Suggested.lean` target
  signatures: this file implements the Layer 0 export contract stated there, and follows its
  naming and organization for the two weight carriers.
-/

public section

namespace TauCeti

open NumberField IsDedekindDomain nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem absNorm_ne_zero_of_ne_bot {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Ideal.absNorm I ≠ 0 := by
  simpa [Ideal.absNorm_eq_zero_iff] using hI

/-!
### The general carrier of completely multiplicative ideal weights
-/

/-- A **multiplicative ideal weight** on a number field `K`: a completely multiplicative
complex-valued function on *all* integral ideals of `𝓞 K`, packaged as a monoid-with-zero
homomorphism `Ideal (𝓞 K) →*₀ ℂ`, which kills only finitely many height-one primes.

Being a `→*₀` forces the value `0` at the zero ideal `⊥` and the value `1` at `⊤`; the
finiteness condition is what makes the associated Euler product have finitely many bad local
factors. This carrier is *degree one*: its value at a prime power `𝔭 ^ n` is forced to be
`χ 𝔭 ^ n`, so it excludes the ideal Möbius function and any coefficient system whose
prime-power values are independent local data. -/
structure MultiplicativeIdealWeight (K : Type*) [Field K] [NumberField K] where
  /-- The underlying completely multiplicative map on all integral ideals. -/
  toMonoidWithZeroHom : Ideal (𝓞 K) →*₀ ℂ
  /-- Only finitely many height-one primes are killed. -/
  finite_setOf_apply_eq_zero :
    {𝔭 : HeightOneSpectrum (𝓞 K) | toMonoidWithZeroHom 𝔭.asIdeal = 0}.Finite

namespace MultiplicativeIdealWeight

instance : FunLike (MultiplicativeIdealWeight K) (Ideal (𝓞 K)) ℂ where
  coe χ := χ.toMonoidWithZeroHom
  coe_injective χ ψ h := by
    cases χ; cases ψ
    congr 1
    exact DFunLike.coe_injective h

instance : MonoidWithZeroHomClass (MultiplicativeIdealWeight K) (Ideal (𝓞 K)) ℂ where
  map_zero χ := χ.toMonoidWithZeroHom.map_zero
  map_one χ := χ.toMonoidWithZeroHom.map_one
  map_mul χ := χ.toMonoidWithZeroHom.map_mul

@[simp]
theorem coe_toMonoidWithZeroHom (χ : MultiplicativeIdealWeight K) :
    ⇑χ.toMonoidWithZeroHom = ⇑χ := rfl

@[ext]
theorem ext {χ ψ : MultiplicativeIdealWeight K} (h : ∀ I, χ I = ψ I) : χ = ψ :=
  DFunLike.ext _ _ h

/-- **The zero-ideal law.** Every multiplicative ideal weight kills the zero ideal, so no
weight is the everywhere-one function on all ideals. -/
@[simp]
theorem apply_bot (χ : MultiplicativeIdealWeight K) : χ ⊥ = 0 := map_zero χ

@[simp]
theorem apply_top (χ : MultiplicativeIdealWeight K) : χ ⊤ = 1 := by
  simpa using map_one χ

/-- A multiplicative ideal weight is determined by its values at the height-one primes: every
nonzero ideal of `𝓞 K` is a product of them. -/
theorem ext_heightOneSpectrum {χ ψ : MultiplicativeIdealWeight K}
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), χ 𝔭.asIdeal = ψ 𝔭.asIdeal) : χ = ψ := by
  ext I
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => rw [map_zero, map_zero]
  | h₂ x hx => rw [Ideal.isUnit_iff.mp hx, apply_top, apply_top]
  | h₃ a p _ hp ih =>
    rw [_root_.map_mul, _root_.map_mul, ih, h ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩]

/-- The **bad primes** of an ideal weight: the height-one primes it kills. This is a derived,
canonically determined accessor, not extra data. -/
def badPrimes (χ : MultiplicativeIdealWeight K) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | χ 𝔭.asIdeal = 0}

@[simp]
theorem mem_badPrimes {χ : MultiplicativeIdealWeight K} {𝔭 : HeightOneSpectrum (𝓞 K)} :
    𝔭 ∈ χ.badPrimes ↔ χ 𝔭.asIdeal = 0 := Iff.rfl

theorem finite_badPrimes (χ : MultiplicativeIdealWeight K) : χ.badPrimes.Finite :=
  χ.finite_setOf_apply_eq_zero

variable {χ : MultiplicativeIdealWeight K}

/-- An ideal is **good** for `χ` when it is prime to the bad primes of `χ`. In particular a
good ideal is nonzero, even when `χ` has no bad primes at all. -/
abbrev IsGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) : Prop :=
  Ideal.IsPrimeTo I χ.badPrimes

/-- **A completely multiplicative ideal weight is nonzero exactly on the good ideals.** Thus the
good ideals are precisely the nonvanishing locus of the weight. -/
theorem apply_ne_zero_iff_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I ≠ 0 ↔ χ.IsGood I := by
  constructor
  · intro h
    apply Ideal.isPrimeTo_iff.mpr
    constructor
    · exact fun hbot ↦ h (by simp [hbot])
    · intro 𝔭 h𝔭 ⟨J, hJ⟩
      apply h
      rw [hJ, map_mul, mem_badPrimes.mp h𝔭, zero_mul]
  · intro hI
    refine hI.induction_on (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
    exact (map_mul χ _ _).trans_ne (mul_ne_zero h𝔭 ih)

theorem apply_eq_zero_iff_not_isGood (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ I = 0 ↔ ¬ χ.IsGood I := by
  rw [← not_ne_iff, χ.apply_ne_zero_iff_isGood]

/-!
### Constructors and operations
-/

section Operations

variable {S : Set (HeightOneSpectrum (𝓞 K))}

open scoped Classical in
/-- The **indicator weight** of a finite set `S` of height-one primes: the value is `1` on the
ideals prime to `S` and `0` elsewhere. Its bad primes are exactly `S`, and `ofBadPrimes ∅` is
the trivial weight `1`. -/
noncomputable def ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun I := if Ideal.IsPrimeTo I S then 1 else 0
      map_zero' := by simp
      map_one' := by simp [Ideal.one_eq_top]
      map_mul' I J := by
        by_cases h : Ideal.IsPrimeTo (I * J) S
        · simp [h, (Ideal.isPrimeTo_mul_iff.mp h).1, (Ideal.isPrimeTo_mul_iff.mp h).2]
        · rcases not_and_or.mp (fun hc ↦ h (Ideal.isPrimeTo_mul_iff.mpr hc)) with h' | h' <;>
            simp [h, h'] }
  finite_setOf_apply_eq_zero := by
    convert hS using 1
    ext 𝔭
    simp

open scoped Classical in
/-- Defining equation of `TauCeti.MultiplicativeIdealWeight.ofBadPrimes`; its body is not
exposed. -/
@[simp]
theorem ofBadPrimes_apply (hS : S.Finite) (I : Ideal (𝓞 K)) :
    ofBadPrimes S hS I = if Ideal.IsPrimeTo I S then 1 else 0 := (rfl)

@[simp]
theorem badPrimes_ofBadPrimes (hS : S.Finite) : (ofBadPrimes S hS).badPrimes = S := by
  classical
  ext 𝔭
  simp [badPrimes, ofBadPrimes_apply]

@[simp]
theorem isGood_ofBadPrimes_iff (hS : S.Finite) {I : Ideal (𝓞 K)} :
    (ofBadPrimes S hS).IsGood I ↔ Ideal.IsPrimeTo I S := by
  simp only [IsGood, badPrimes_ofBadPrimes]

/-- The pointwise product of two multiplicative ideal weights. -/
noncomputable instance : Mul (MultiplicativeIdealWeight K) where
  mul χ ψ :=
    { toMonoidWithZeroHom := χ.toMonoidWithZeroHom * ψ.toMonoidWithZeroHom
      finite_setOf_apply_eq_zero := by
        refine (χ.finite_badPrimes.union ψ.finite_badPrimes).subset fun 𝔭 h𝔭 ↦ ?_
        -- the product of two `→*₀` is built from the product of the underlying `→*`, so the
        -- value of the product is computed by `MonoidHom.mul_apply`
        have hzero : χ 𝔭.asIdeal * ψ 𝔭.asIdeal = 0 :=
          (MonoidHom.mul_apply χ.toMonoidWithZeroHom.toMonoidHom
            ψ.toMonoidWithZeroHom.toMonoidHom 𝔭.asIdeal).symm.trans h𝔭
        exact mul_eq_zero.mp hzero }

@[simp]
theorem mul_apply (χ ψ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    (χ * ψ) I = χ I * ψ I := (rfl)

/-- The trivial multiplicative ideal weight. -/
noncomputable instance : One (MultiplicativeIdealWeight K) where
  one :=
    { toMonoidWithZeroHom := 1
      finite_setOf_apply_eq_zero := by
        refine Set.finite_empty.subset fun 𝔭 h𝔭 ↦ ?_
        exact 𝔭.ne_bot (MonoidWithZeroHom.one_apply_eq_zero_iff.mp h𝔭) }

/-- The trivial weight is the indicator of the nonzero ideals. -/
@[simp]
theorem one_apply (I : Ideal (𝓞 K)) :
    (1 : MultiplicativeIdealWeight K) I = if I = ⊥ then 0 else 1 := by
  split_ifs with hI
  · subst I
    simp
  · exact MonoidWithZeroHom.one_apply_of_ne_zero hI

@[simp]
theorem badPrimes_one : (1 : MultiplicativeIdealWeight K).badPrimes = ∅ := by
  ext 𝔭
  simp [badPrimes, one_apply, 𝔭.ne_bot]

@[simp]
theorem badPrimes_mul (χ ψ : MultiplicativeIdealWeight K) :
    (χ * ψ).badPrimes = χ.badPrimes ∪ ψ.badPrimes := by
  ext 𝔭
  simp [badPrimes, mul_eq_zero]

/-- The pointwise product of multiplicative ideal weights, with the trivial weight as unit.
Ideal convolution (roadmap Layer 2) will instead be an operation on
`TauCeti.IdealArithmeticFunction`. -/
noncomputable instance : CommMonoid (MultiplicativeIdealWeight K) where
  mul_assoc χ ψ ω := by ext I; simp [mul_assoc]
  one_mul χ := by
    ext I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [one_apply, hI]
  mul_one χ := by
    ext I
    rcases eq_or_ne I ⊥ with rfl | hI
    · simp
    · simp [one_apply, hI]
  mul_comm χ ψ := by ext I; simp [mul_comm]

@[simp]
theorem isGood_one_iff {I : Ideal (𝓞 K)} :
    (1 : MultiplicativeIdealWeight K).IsGood I ↔ I ≠ ⊥ := by
  simp only [IsGood, badPrimes_one, Ideal.isPrimeTo_empty]

/-- **Restriction away from a finite set of primes**: `χ` is left unchanged on the ideals prime
to `S` and set to `0` on the others. -/
noncomputable def restrict (χ : MultiplicativeIdealWeight K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) : MultiplicativeIdealWeight K :=
  χ * ofBadPrimes S hS

open scoped Classical in
@[simp]
theorem restrict_apply (χ : MultiplicativeIdealWeight K) (hS : S.Finite) (I : Ideal (𝓞 K)) :
    χ.restrict S hS I = if Ideal.IsPrimeTo I S then χ I else 0 := by
  by_cases h : Ideal.IsPrimeTo I S <;> simp [restrict, ofBadPrimes_apply, h]

@[simp]
theorem badPrimes_restrict (χ : MultiplicativeIdealWeight K) (hS : S.Finite) :
    (χ.restrict S hS).badPrimes = χ.badPrimes ∪ S := by
  simp [restrict]

/-- Restricting away from no prime at all changes nothing. -/
@[simp]
theorem restrict_empty (χ : MultiplicativeIdealWeight K)
    (hS : (∅ : Set (HeightOneSpectrum (𝓞 K))).Finite) : χ.restrict ∅ hS = χ := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [hI]

open scoped Classical in
/-- **Forbidding one more prime.** Restricting away from `insert 𝔭 S` kills the ideals divisible
by `𝔭` and agrees with the restriction away from `S` on the others. -/
theorem restrict_insert_apply (χ : MultiplicativeIdealWeight K)
    {𝔭 : HeightOneSpectrum (𝓞 K)} (hS : S.Finite) (I : Ideal (𝓞 K)) :
    χ.restrict (insert 𝔭 S) (hS.insert 𝔭) I =
      if 𝔭.asIdeal ∣ I then 0 else χ.restrict S hS I := by
  rw [restrict_apply, restrict_apply, Ideal.isPrimeTo_insert_iff]
  by_cases hdvd : 𝔭.asIdeal ∣ I <;> simp [hdvd]

/-- Restricting the trivial weight away from `S` gives the indicator weight of ideals prime to
every prime in `S`. -/
@[simp]
theorem one_restrict (hS : S.Finite) :
    (1 : MultiplicativeIdealWeight K).restrict S hS = ofBadPrimes S hS :=
  one_mul _

/-- The **conjugate weight** `I ↦ conj (χ I)`. -/
def conj (χ : MultiplicativeIdealWeight K) : MultiplicativeIdealWeight K where
  toMonoidWithZeroHom := ((starRingEnd ℂ) : ℂ →+* ℂ).toMonoidWithZeroHom.comp
    χ.toMonoidWithZeroHom
  finite_setOf_apply_eq_zero := χ.finite_badPrimes.subset fun 𝔭 h𝔭 ↦ by
    simpa [badPrimes, MonoidWithZeroHom.comp_apply] using h𝔭

@[simp]
theorem conj_apply (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    χ.conj I = starRingEnd ℂ (χ I) := (rfl)

@[simp]
theorem badPrimes_conj (χ : MultiplicativeIdealWeight K) : χ.conj.badPrimes = χ.badPrimes := by
  ext 𝔭
  simp [badPrimes]

@[simp]
theorem conj_conj (χ : MultiplicativeIdealWeight K) : χ.conj.conj = χ := by
  ext I
  simp

/-- The **norm twist** `I ↦ χ I * N(I) ^ (-z)`. For general `z` this leaves the unitary
carrier; only the purely imaginary twists preserve it
(`TauCeti.UnitaryIdealWeight.normTwist`). -/
noncomputable def normTwist (z : ℂ) (χ : MultiplicativeIdealWeight K) :
    MultiplicativeIdealWeight K where
  toMonoidWithZeroHom :=
    { toFun I := χ I * (Ideal.absNorm I : ℂ) ^ (-z)
      map_zero' := by simp
      map_one' := by simp
      map_mul' I J := by
        rw [map_mul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        ring }
  finite_setOf_apply_eq_zero := χ.finite_badPrimes.subset fun 𝔭 h𝔭 ↦ by
    have h : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast absNorm_ne_zero_of_ne_bot 𝔭.ne_bot
    have h' : χ 𝔭.asIdeal * ((Ideal.absNorm 𝔭.asIdeal : ℕ) : ℂ) ^ (-z) = 0 := by
      simpa [badPrimes] using h𝔭
    rcases mul_eq_zero.mp h' with h₁ | h₂
    · exact h₁
    · exact absurd ((Complex.cpow_eq_zero_iff _ _).mp h₂).1 h

@[simp]
theorem normTwist_apply (z : ℂ) (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 K)) :
    normTwist z χ I = χ I * (Ideal.absNorm I : ℂ) ^ (-z) := (rfl)

@[simp]
theorem badPrimes_normTwist (z : ℂ) (χ : MultiplicativeIdealWeight K) :
    (normTwist z χ).badPrimes = χ.badPrimes := by
  ext 𝔭
  have h := absNorm_ne_zero_of_ne_bot 𝔭.ne_bot
  simp [badPrimes, mul_eq_zero, Complex.cpow_eq_zero_iff, h]

@[simp]
theorem normTwist_zero (χ : MultiplicativeIdealWeight K) : normTwist 0 χ = χ := by
  ext I
  simp

/-- Successive norm twists combine by adding their parameters. -/
theorem normTwist_normTwist (z w : ℂ) (χ : MultiplicativeIdealWeight K) :
    normTwist z (normTwist w χ) = normTwist (z + w) χ := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · have h : ((Ideal.absNorm I : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast absNorm_ne_zero_of_ne_bot hI
    rw [normTwist_apply, normTwist_apply, normTwist_apply, neg_add, Complex.cpow_add _ _ h]
    ring

/-!
### Weights that are norm twists on their good locus
-/

/-- A weight **is a norm twist on its good ideals**, with parameter `u`, when
`χ I = N(I) ^ (u * I)` at every ideal `I` prime to its bad primes. Away from the bad primes such
a weight is the purely imaginary norm twist `TauCeti.MultiplicativeIdealWeight.normTwist` of the
trivial weight, and it is the whole of that twist once the bad primes are taken into account
(`TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.eq_normTwist`).

These weights give degenerate examples in families of ideal weights: their `L`-series is a
Dedekind zeta function with finitely many Euler factors deleted, read after an imaginary
translation, so it has a pole and no cancellation in its ideal partial sums
(`TauCeti.not_hasCancellation_of_isNormTwistOnGood`). -/
def IsNormTwistOnGood (χ : MultiplicativeIdealWeight K) (u : ℝ) : Prop :=
  ∀ I : Ideal (𝓞 K), χ.IsGood I → χ I = (Ideal.absNorm I : ℂ) ^ ((u : ℂ) * Complex.I)

/-- A weight **is trivial on its good ideals** when it takes the value `1` at every ideal prime
to its bad primes; equivalently it is a norm twist on its good ideals with parameter `0`
(`TauCeti.MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff`). -/
def IsTrivialOnGood (χ : MultiplicativeIdealWeight K) : Prop :=
  ∀ I : Ideal (𝓞 K), χ.IsGood I → χ I = 1

/-- The norm twists with parameter `0` on the good ideals are the weights that are trivial
there. -/
@[simp]
theorem isNormTwistOnGood_zero_iff (χ : MultiplicativeIdealWeight K) :
    χ.IsNormTwistOnGood 0 ↔ χ.IsTrivialOnGood := by
  simp [IsNormTwistOnGood, IsTrivialOnGood]

/-- The trivial weight is trivial on its good ideals, which are all the nonzero ideals. -/
theorem isTrivialOnGood_one : (1 : MultiplicativeIdealWeight K).IsTrivialOnGood :=
  fun _ hI ↦ by rw [one_apply]; simp [hI.ne_bot]

/-- The indicator of the ideals prime to a finite set `S` of primes is trivial on its good
ideals, which are exactly those ideals. -/
theorem isTrivialOnGood_ofBadPrimes (hS : S.Finite) : (ofBadPrimes S hS).IsTrivialOnGood := by
  classical
  intro I hI
  rw [ofBadPrimes_apply]
  simp [(isGood_ofBadPrimes_iff hS).mp hI]

/-- **A norm twist on the good ideals is a norm twist of an indicator weight.** A weight that is
a norm twist with parameter `u` on its good ideals is the twist by `N(I) ^ (u * I)` of the
indicator of the ideals prime to its bad primes. The bad set is a parameter, so that a caller
holding it as a `Finset` need not convert. -/
theorem IsNormTwistOnGood.eq_normTwist {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (h : χ.IsNormTwistOnGood u) (hSbad : χ.badPrimes = S) :
    χ = normTwist (-((u : ℂ) * Complex.I))
      (ofBadPrimes S (hSbad ▸ χ.finite_badPrimes)) := by
  classical
  ext I
  by_cases hI : χ.IsGood I
  · have hI' : Ideal.IsPrimeTo I S := hI.mono hSbad.symm.subset
    rw [h I hI, normTwist_apply, ofBadPrimes_apply, neg_neg]
    simp [hI']
  · have hI' : ¬ Ideal.IsPrimeTo I S := fun hc ↦ hI (hc.mono hSbad.subset)
    rw [(χ.apply_eq_zero_iff_not_isGood I).mpr hI, normTwist_apply, ofBadPrimes_apply]
    simp [hI']

/-- **A twist adds to the parameter.** Twisting by `N(I) ^ (v * I)` turns a norm twist with
parameter `u` on the good ideals into one with parameter `u + v`; the good ideals are unchanged.
-/
theorem IsNormTwistOnGood.normTwist {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (h : χ.IsNormTwistOnGood u) (v : ℝ) :
    (MultiplicativeIdealWeight.normTwist (-((v : ℂ) * Complex.I)) χ).IsNormTwistOnGood
      (u + v) := by
  intro I hI
  have hI' : χ.IsGood I := hI.mono (by rw [badPrimes_normTwist])
  have hN : ((Ideal.absNorm I : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast absNorm_ne_zero_of_ne_bot hI'.ne_bot
  rw [normTwist_apply, h I hI', neg_neg, ← Complex.cpow_add _ _ hN]
  congr 1
  push_cast
  ring

/-- **Converse of `TauCeti.MultiplicativeIdealWeight.IsNormTwistOnGood.eq_normTwist`.** The
twist by `N(I) ^ (u * I)` of the indicator of the ideals prime to a finite set of primes is a
norm twist with parameter `u` on its good ideals. -/
theorem isNormTwistOnGood_normTwist_ofBadPrimes (hS : S.Finite) (u : ℝ) :
    (normTwist (-((u : ℂ) * Complex.I)) (ofBadPrimes S hS)).IsNormTwistOnGood u := by
  have h0 : (ofBadPrimes S hS).IsNormTwistOnGood 0 :=
    (isNormTwistOnGood_zero_iff _).mpr (isTrivialOnGood_ofBadPrimes hS)
  simpa using h0.normTwist u

/-- **Conjugation negates the parameter** of a norm twist on the good ideals. -/
theorem IsNormTwistOnGood.conj {χ : MultiplicativeIdealWeight K} {u : ℝ}
    (h : χ.IsNormTwistOnGood u) : χ.conj.IsNormTwistOnGood (-u) := by
  intro I hI
  have hI' : χ.IsGood I := hI.mono (by rw [badPrimes_conj])
  have hN : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (absNorm_ne_zero_of_ne_bot hI'.ne_bot)
  have hnorm : ‖((Ideal.absNorm I : ℕ) : ℂ) ^ ((u : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hN]
    simp
  rw [conj_apply, h I hI', ← Complex.inv_eq_conj hnorm, ← Complex.cpow_neg]
  congr 1
  push_cast
  ring

/-- **The pointwise product adds the parameters** of two norm twists on the good ideals. Both
factors are good at every ideal good for the product, since the bad primes of a product are the
union of those of its factors. -/
theorem IsNormTwistOnGood.mul {χ ψ : MultiplicativeIdealWeight K} {u v : ℝ}
    (hχ : χ.IsNormTwistOnGood u) (hψ : ψ.IsNormTwistOnGood v) :
    (χ * ψ).IsNormTwistOnGood (u + v) := by
  intro I hI
  have hχI : χ.IsGood I := hI.mono (by rw [badPrimes_mul]; exact Set.subset_union_left)
  have hψI : ψ.IsGood I := hI.mono (by rw [badPrimes_mul]; exact Set.subset_union_right)
  have hN : ((Ideal.absNorm I : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast absNorm_ne_zero_of_ne_bot hχI.ne_bot
  rw [mul_apply, hχ I hχI, hψ I hψI, ← Complex.cpow_add _ _ hN]
  congr 1
  push_cast
  ring

end Operations

/-!
### Passage to the general carrier, and the zero-ideal rejection test
-/

/-- The ideal arithmetic function underlying an ideal weight: its restriction to the nonzero
ideals. -/
def toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) : IdealArithmeticFunction K :=
  fun I ↦ χ I

@[simp]
theorem toIdealArithmeticFunction_apply (χ : MultiplicativeIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ I := (rfl)

/-- **Regrouping absorbs a norm twist.** Twisting a weight by `N(I) ^ (-z)` twists its `n`-th norm
coefficient by `n ^ (-z)`. -/
@[simp]
theorem normCoeff_normTwist (z : ℂ) (χ : MultiplicativeIdealWeight K) (n : ℕ) :
    normCoeff K (normTwist z χ).toIdealArithmeticFunction n =
      normCoeff K χ.toIdealArithmeticFunction n * (n : ℂ) ^ (-z) := by
  have h : (normTwist z χ).toIdealArithmeticFunction =
      fun I ↦ χ.toIdealArithmeticFunction I * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-z) :=
    funext fun I ↦ by simp [normTwist_apply]
  rw [h, normCoeff_mul_absNorm_cpow]

/-- The ideal arithmetic function underlying a completely multiplicative ideal weight is
multiplicative on relatively prime ideals. -/
theorem isMultiplicative_toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) :
    χ.toIdealArithmeticFunction.IsMultiplicative := by
  constructor <;> simp

/-- An ideal weight is recovered from its restriction to the nonzero ideals by extending by
zero: the zero-ideal law `χ ⊥ = 0` is exactly what makes this work. -/
@[simp]
theorem zeroExtend_toIdealArithmeticFunction (χ : MultiplicativeIdealWeight K) :
    χ.toIdealArithmeticFunction.zeroExtend = ⇑χ := by
  ext I
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp
  · simp [IdealArithmeticFunction.zeroExtend_of_ne _ hI]

theorem toIdealArithmeticFunction_injective :
    Function.Injective
      (toIdealArithmeticFunction : MultiplicativeIdealWeight K → IdealArithmeticFunction K) := by
  intro χ ψ h
  exact DFunLike.coe_injective (by
    rw [← zeroExtend_toIdealArithmeticFunction χ, ← zeroExtend_toIdealArithmeticFunction ψ, h])

@[simp]
theorem toIdealArithmeticFunction_one :
    (1 : MultiplicativeIdealWeight K).toIdealArithmeticFunction = 1 := by
  ext I
  have hI : (I : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  simp [one_apply, hI]

@[simp]
theorem toIdealArithmeticFunction_mul (χ ψ : MultiplicativeIdealWeight K) :
    (χ * ψ).toIdealArithmeticFunction =
      χ.toIdealArithmeticFunction * ψ.toIdealArithmeticFunction := by
  ext I
  simp

/-- **Rejection test.** The everywhere-one function on *all* integral ideals underlies no
multiplicative ideal weight, since `Ideal (𝓞 K) →*₀ ℂ` forces the value `0` at `⊥`. The
everywhere-one function on the *nonzero* ideals is the trivial weight
(`TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_one`). -/
theorem coe_ne_const_one (χ : MultiplicativeIdealWeight K) :
    ⇑χ ≠ Function.const _ 1 := by
  intro h
  simpa using congrFun h ⊥

/-!
### Functoriality under an isomorphism of fields
-/

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]

omit [NumberField K] [NumberField L] in
private theorem asIdeal_equivOfRingEquiv_symm (e : K ≃+* L) (𝔮 : HeightOneSpectrum (𝓞 L)) :
    ((HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)).symm 𝔮).asIdeal =
      Ideal.comap (RingOfIntegers.mapRingEquiv e) 𝔮.asIdeal := rfl

/-- **Transport along an isomorphism of fields.** An isomorphism `e : K ≃+* L` carries a
multiplicative ideal weight on `K` to one on `L`, by pulling ideals of `𝓞 L` back to `𝓞 K`
along `NumberField.RingOfIntegers.mapRingEquiv e`. -/
noncomputable def map (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    MultiplicativeIdealWeight L where
  toMonoidWithZeroHom := χ.toMonoidWithZeroHom.comp
    (Ideal.mapHom (RingOfIntegers.mapRingEquiv e).symm).toMonoidWithZeroHom
  finite_setOf_apply_eq_zero := by
    refine (χ.finite_badPrimes.image
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e))).subset fun 𝔮 h𝔮 ↦ ?_
    refine ⟨_, ?_, Equiv.apply_symm_apply _ 𝔮⟩
    rw [mem_badPrimes, asIdeal_equivOfRingEquiv_symm]
    simpa [badPrimes] using h𝔮

@[simp]
theorem map_apply (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) (I : Ideal (𝓞 L)) :
    map e χ I = χ (Ideal.comap (RingOfIntegers.mapRingEquiv e) I) :=
  congrArg ⇑χ (Ideal.map_symm (RingOfIntegers.mapRingEquiv e))

/-- **The bad primes transport too**: they are carried along by the induced bijection of
height-one spectra. -/
@[simp]
theorem badPrimes_map (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    (map e χ).badPrimes =
      HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) '' χ.badPrimes := by
  ext 𝔮
  rw [Equiv.image_eq_preimage_symm, Set.mem_preimage, mem_badPrimes, mem_badPrimes,
    asIdeal_equivOfRingEquiv_symm, map_apply]

@[simp]
theorem toIdealArithmeticFunction_map (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    (map e χ).toIdealArithmeticFunction =
      IdealArithmeticFunction.map e χ.toIdealArithmeticFunction :=
  IdealArithmeticFunction.zeroExtend_injective <| funext fun I ↦ by
    rw [zeroExtend_toIdealArithmeticFunction, IdealArithmeticFunction.zeroExtend_map,
      zeroExtend_toIdealArithmeticFunction, map_apply]

@[simp]
theorem map_id (χ : MultiplicativeIdealWeight K) : map (RingEquiv.refl K) χ = χ :=
  toIdealArithmeticFunction_injective <| by
    rw [toIdealArithmeticFunction_map, IdealArithmeticFunction.map_id]

/-- **Transport is functorial**: transporting along `e` and then along `e'` is the same as
transporting along `e.trans e'`. -/
theorem map_map (e : K ≃+* L) (e' : L ≃+* M) (χ : MultiplicativeIdealWeight K) :
    map e' (map e χ) = map (e.trans e') χ :=
  toIdealArithmeticFunction_injective <| by
    rw [toIdealArithmeticFunction_map, toIdealArithmeticFunction_map,
      toIdealArithmeticFunction_map, IdealArithmeticFunction.map_map]

/-- **Transport along an isomorphism of fields, as an equivalence** of the two carriers, with
inverse the transport along `e.symm`. -/
noncomputable def mapEquiv (e : K ≃+* L) :
    MultiplicativeIdealWeight K ≃ MultiplicativeIdealWeight L where
  toFun := map e
  invFun := map e.symm
  left_inv χ := by rw [map_map, e.self_trans_symm, map_id]
  right_inv χ := by rw [map_map, e.symm_trans_self, map_id]

@[simp]
theorem mapEquiv_apply (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    mapEquiv e χ = map e χ := (rfl)

@[simp]
theorem mapEquiv_symm_apply (e : K ≃+* L) (χ : MultiplicativeIdealWeight L) :
    (mapEquiv e).symm χ = map e.symm χ := (rfl)

/-! Transport preserves the pointwise `CommMonoid` structure. -/

@[simp]
theorem map_one (e : K ≃+* L) : map e (1 : MultiplicativeIdealWeight K) = 1 :=
  toIdealArithmeticFunction_injective <| by
    rw [toIdealArithmeticFunction_map, toIdealArithmeticFunction_one,
      IdealArithmeticFunction.map_one, toIdealArithmeticFunction_one]

@[simp]
theorem map_mul (e : K ≃+* L) (χ ψ : MultiplicativeIdealWeight K) :
    map e (χ * ψ) = map e χ * map e ψ := by
  ext I
  rw [map_apply, mul_apply, mul_apply, map_apply, map_apply]

/-- Transport carries an indicator weight to the indicator of the image prime set. -/
@[simp]
theorem map_ofBadPrimes (e : K ≃+* L) (hS : S.Finite) :
    map e (ofBadPrimes S hS) = ofBadPrimes
      (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) '' S)
      (hS.image _) := by
  ext I
  rw [map_apply, ofBadPrimes_apply, ofBadPrimes_apply, Ideal.isPrimeTo_comap_iff]

/-- Transport commutes with restriction after carrying the excluded prime set forward. -/
@[simp]
theorem map_restrict (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) (hS : S.Finite) :
    map e (χ.restrict S hS) =
      (map e χ).restrict
        (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) '' S)
        (hS.image _) := by
  rw [restrict, map_mul, map_ofBadPrimes, restrict]

/-- Transport commutes with complex conjugation. -/
@[simp]
theorem map_conj (e : K ≃+* L) (χ : MultiplicativeIdealWeight K) :
    map e χ.conj = (map e χ).conj := by
  ext I
  rw [map_apply, conj_apply, conj_apply, map_apply]

/-- Transport commutes with norm twists because absolute ideal norm is invariant under a ring
equivalence. -/
@[simp]
theorem map_normTwist (e : K ≃+* L) (z : ℂ) (χ : MultiplicativeIdealWeight K) :
    map e (normTwist z χ) = normTwist z (map e χ) := by
  ext I
  rw [map_apply, normTwist_apply, normTwist_apply, map_apply,
    Ideal.absNorm_comap_of_ringEquiv]

end Transport

end MultiplicativeIdealWeight

/-!
### The unitary subtype
-/

/-- A **unitary ideal weight**: a multiplicative ideal weight whose values have modulus `1`
away from its bad primes. Finite-order Hecke characters land here
(`TauCeti.UnitaryIdealWeight.ofPowEqOne`), and so do the purely imaginary norm twists
(`TauCeti.UnitaryIdealWeight.normTwist`); a norm twist with `Re z ≠ 0` does not
(`TauCeti.UnitaryIdealWeight.norm_normTwist_apply_ne_one`). -/
abbrev UnitaryIdealWeight (K : Type*) [Field K] [NumberField K] : Type _ :=
  {χ : MultiplicativeIdealWeight K //
    ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → ‖χ 𝔭.asIdeal‖ = 1}

namespace UnitaryIdealWeight

/-- **A unitary weight has modulus one on every good ideal**, extending its defining condition
from good primes to the entire good-ideal locus. -/
theorem norm_eq_one (χ : UnitaryIdealWeight K) {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) :
    ‖χ.1 I‖ = 1 := by
  refine hI.induction_on (by simp) fun 𝔭 J h𝔭 _ ih ↦ ?_
  rw [map_mul, norm_mul, χ.2 𝔭 h𝔭, ih, one_mul]

-- Source. The statement and its proof follow `DirichletCharacter.norm_le_one` in Mathlib's
-- `Mathlib/NumberTheory/DirichletCharacter/Bounds.lean`, transposed from a Dirichlet character on
-- `ZMod n` to a unitary ideal weight: the case split there is on `IsUnit a` and closes with
-- `map_nonunit`, here it is on `MultiplicativeIdealWeight.IsGood` and closes with
-- `apply_eq_zero_iff_not_isGood`.

/-- **A unitary weight is bounded by one on every ideal.** The bound is unconditional: it carries
no goodness hypothesis, so a comparison indexed by all of `(Ideal (𝓞 K))⁰` can apply it termwise.
`norm_eq_one` is sharper where it applies, but obliges the caller to split that index type first;
this is the form a convergence estimate wants. -/
theorem norm_le_one (χ : UnitaryIdealWeight K) (I : Ideal (𝓞 K)) : ‖χ.1 I‖ ≤ 1 := by
  by_cases hI : χ.1.IsGood I
  · exact (norm_eq_one χ hI).le
  · rw [(MultiplicativeIdealWeight.apply_eq_zero_iff_not_isGood χ.1 I).mpr hI, norm_zero]
    exact zero_le_one

/-- The trivial weight is unitary. -/
noncomputable instance : One (UnitaryIdealWeight K) :=
  ⟨1, fun 𝔭 _ ↦ by simp [MultiplicativeIdealWeight.one_apply, 𝔭.ne_bot]⟩

@[simp]
theorem val_one : (1 : UnitaryIdealWeight K).1 = 1 := rfl

/-- The pointwise product of unitary weights is unitary. -/
noncomputable instance : Mul (UnitaryIdealWeight K) where
  mul χ ψ :=
    ⟨χ.1 * ψ.1, fun 𝔭 h𝔭 ↦ by
      rw [MultiplicativeIdealWeight.badPrimes_mul, Set.mem_union, not_or] at h𝔭
      rw [MultiplicativeIdealWeight.mul_apply, norm_mul, χ.2 𝔭 h𝔭.1, ψ.2 𝔭 h𝔭.2,
        one_mul]⟩

@[simp]
theorem val_mul (χ ψ : UnitaryIdealWeight K) : (χ * ψ).1 = χ.1 * ψ.1 := rfl

/-- Pointwise multiplication makes the unitary weights a commutative monoid. -/
noncomputable instance : CommMonoid (UnitaryIdealWeight K) where
  mul_assoc χ ψ ω := Subtype.ext (by simp only [val_mul]; exact mul_assoc _ _ _)
  one_mul χ := Subtype.ext (by simp only [val_mul, val_one]; exact one_mul _)
  mul_one χ := Subtype.ext (by simp only [val_mul, val_one]; exact mul_one _)
  mul_comm χ ψ := Subtype.ext (by simp only [val_mul]; exact mul_comm _ _)

/-- **Finite-order weights are unitary.** If a positive power of `χ` takes the value `1` at
every good prime — as for a finite-order Hecke character — then `χ` is unitary. -/
def ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    UnitaryIdealWeight K :=
  ⟨χ, fun 𝔭 h𝔭 ↦ by
    refine (pow_left_inj₀ (norm_nonneg _) zero_le_one hn).mp ?_
    rw [← norm_pow, h 𝔭 h𝔭, norm_one, one_pow]⟩

@[simp]
theorem val_ofPowEqOne (χ : MultiplicativeIdealWeight K) {n : ℕ} (hn : n ≠ 0)
    (h : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭 ∉ χ.badPrimes → χ 𝔭.asIdeal ^ n = 1) :
    (ofPowEqOne χ hn h).1 = χ := (rfl)

/-- **Imaginary norm twists preserve unitarity.** For `Re z = 0` the factor `N(I) ^ (-z)` has
modulus `1`, so the twisted weight is again unitary. -/
noncomputable def normTwist (z : ℂ) (hz : z.re = 0) (χ : UnitaryIdealWeight K) :
    UnitaryIdealWeight K :=
  ⟨MultiplicativeIdealWeight.normTwist z χ.1, fun 𝔭 h𝔭 ↦ by
    have hN : 0 < Ideal.absNorm 𝔭.asIdeal :=
      Nat.pos_of_ne_zero (absNorm_ne_zero_of_ne_bot 𝔭.ne_bot)
    rw [MultiplicativeIdealWeight.normTwist_apply, norm_mul, χ.2 𝔭 (by simpa using h𝔭),
      one_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re, hz, neg_zero,
      Real.rpow_zero]⟩

@[simp]
theorem val_normTwist (z : ℂ) (hz : z.re = 0) (χ : UnitaryIdealWeight K) :
    (normTwist z hz χ).1 = MultiplicativeIdealWeight.normTwist z χ.1 := (rfl)

/-- The zero norm twist acts trivially on unitary weights. -/
@[simp]
theorem normTwist_zero (χ : UnitaryIdealWeight K) : normTwist 0 (by simp) χ = χ :=
  Subtype.ext (by rw [val_normTwist, MultiplicativeIdealWeight.normTwist_zero])

/-- Successive imaginary norm twists of a unitary weight combine by adding their parameters. -/
@[simp]
theorem normTwist_normTwist (z w : ℂ) (hz : z.re = 0) (hw : w.re = 0)
    (χ : UnitaryIdealWeight K) :
    normTwist z hz (normTwist w hw χ) = normTwist (z + w) (by simp [hz, hw]) χ :=
  Subtype.ext (by
    rw [val_normTwist, val_normTwist, val_normTwist,
      MultiplicativeIdealWeight.normTwist_normTwist])

/-- **The modulus of an arbitrary norm twist.** At a good ideal, twisting a unitary weight by
`z` gives modulus `N(I) ^ (-Re z)`; only the purely imaginary twists therefore stay unitary. -/
theorem norm_normTwist (χ : UnitaryIdealWeight K) (z : ℂ) {I : Ideal (𝓞 K)}
    (hI : χ.1.IsGood I) :
    ‖MultiplicativeIdealWeight.normTwist z χ.1 I‖ = (Ideal.absNorm I : ℝ) ^ (-z.re) := by
  have hN : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (absNorm_ne_zero_of_ne_bot hI.ne_bot)
  rw [MultiplicativeIdealWeight.normTwist_apply, norm_mul, norm_eq_one χ hI, one_mul,
    Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re]

/-- **Rejection test.** A norm twist with `Re z ≠ 0` leaves the unitary carrier: at every good
ideal of absolute norm greater than one its modulus differs from `1`. Such twists therefore
live only in `TauCeti.MultiplicativeIdealWeight`. -/
theorem norm_normTwist_apply_ne_one (χ : UnitaryIdealWeight K) {z : ℂ} (hz : z.re ≠ 0)
    {I : Ideal (𝓞 K)} (hI : χ.1.IsGood I) (hN : 1 < Ideal.absNorm I) :
    ‖MultiplicativeIdealWeight.normTwist z χ.1 I‖ ≠ 1 := by
  have hN' : (1 : ℝ) < (Ideal.absNorm I : ℝ) := by exact_mod_cast hN
  rw [norm_normTwist χ z hI]
  rcases lt_trichotomy z.re 0 with h | h | h
  · exact ne_of_gt ((Real.one_lt_rpow_iff_of_pos (by linarith)).mpr (Or.inl ⟨hN', by linarith⟩))
  · exact absurd h hz
  · exact ne_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hN' (by linarith))

/-- The conjugate of a unitary weight is unitary. -/
def conj (χ : UnitaryIdealWeight K) : UnitaryIdealWeight K :=
  ⟨χ.1.conj, fun 𝔭 h𝔭 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_conj] at h𝔭
    simpa using χ.2 𝔭 h𝔭⟩

@[simp]
theorem val_conj (χ : UnitaryIdealWeight K) : (conj χ).1 = χ.1.conj := (rfl)

/-- Restricting a unitary weight away from a finite set of primes keeps it unitary: the
restricted weight is unchanged at the primes that are good for it. -/
noncomputable def restrict (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : UnitaryIdealWeight K :=
  ⟨χ.1.restrict S hS, fun 𝔭 h𝔭 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_restrict, Set.mem_union, not_or] at h𝔭
    rw [MultiplicativeIdealWeight.restrict_apply]
    simp [h𝔭.2, χ.2 𝔭 h𝔭.1]⟩

@[simp]
theorem val_restrict (χ : UnitaryIdealWeight K) (S : Set (HeightOneSpectrum (𝓞 K)))
    (hS : S.Finite) : (restrict χ S hS).1 = χ.1.restrict S hS := (rfl)

/-- Restricting a unitary weight away from no prime at all changes nothing. -/
@[simp]
theorem restrict_empty (χ : UnitaryIdealWeight K)
    (hS : (∅ : Set (HeightOneSpectrum (𝓞 K))).Finite) : restrict χ ∅ hS = χ :=
  Subtype.ext (by rw [val_restrict, MultiplicativeIdealWeight.restrict_empty])

section Transport

variable {L M : Type*} [Field L] [NumberField L] [Field M] [NumberField M]

/-- **Transport along an isomorphism of fields preserves unitarity**: the transported weight has
the same values as `χ`, read off at the corresponding primes. -/
noncomputable def map (e : K ≃+* L) (χ : UnitaryIdealWeight K) : UnitaryIdealWeight L :=
  ⟨MultiplicativeIdealWeight.map e χ.1, fun 𝔮 h𝔮 ↦ by
    rw [MultiplicativeIdealWeight.badPrimes_map, Equiv.image_eq_preimage_symm,
      Set.mem_preimage] at h𝔮
    rw [MultiplicativeIdealWeight.map_apply,
      ← MultiplicativeIdealWeight.asIdeal_equivOfRingEquiv_symm]
    exact χ.2 _ h𝔮⟩

@[simp]
theorem val_map (e : K ≃+* L) (χ : UnitaryIdealWeight K) :
    (map e χ).1 = MultiplicativeIdealWeight.map e χ.1 := (rfl)

@[simp]
theorem map_id (χ : UnitaryIdealWeight K) : map (RingEquiv.refl K) χ = χ :=
  Subtype.ext (by rw [val_map, MultiplicativeIdealWeight.map_id])

/-- **Transport is functorial** on the unitary carrier as well. -/
theorem map_map (e : K ≃+* L) (e' : L ≃+* M) (χ : UnitaryIdealWeight K) :
    map e' (map e χ) = map (e.trans e') χ :=
  Subtype.ext (by rw [val_map, val_map, val_map, MultiplicativeIdealWeight.map_map])

/-- **Transport along an isomorphism of fields, as an equivalence** of the unitary carriers. -/
noncomputable def mapEquiv (e : K ≃+* L) : UnitaryIdealWeight K ≃ UnitaryIdealWeight L where
  toFun := map e
  invFun := map e.symm
  left_inv χ := by rw [map_map, e.self_trans_symm, map_id]
  right_inv χ := by rw [map_map, e.symm_trans_self, map_id]

@[simp]
theorem mapEquiv_apply (e : K ≃+* L) (χ : UnitaryIdealWeight K) :
    mapEquiv e χ = map e χ := (rfl)

@[simp]
theorem mapEquiv_symm_apply (e : K ≃+* L) (χ : UnitaryIdealWeight L) :
    (mapEquiv e).symm χ = map e.symm χ := (rfl)

/-! Transport preserves the pointwise `CommMonoid` structure of the unitary carrier too. -/

@[simp]
theorem map_one (e : K ≃+* L) : map e (1 : UnitaryIdealWeight K) = 1 :=
  Subtype.ext (by rw [val_map, val_one, MultiplicativeIdealWeight.map_one, val_one])

@[simp]
theorem map_mul (e : K ≃+* L) (χ ψ : UnitaryIdealWeight K) :
    map e (χ * ψ) = map e χ * map e ψ :=
  Subtype.ext (by
    rw [val_map, val_mul, val_mul, val_map, val_map, MultiplicativeIdealWeight.map_mul])

/-- Transport commutes with restriction on unitary weights after carrying the excluded prime set
forward. -/
@[simp]
theorem map_restrict (e : K ≃+* L) (χ : UnitaryIdealWeight K)
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite) :
    map e (χ.restrict S hS) =
      (map e χ).restrict
        (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e) '' S)
        (hS.image _) :=
  Subtype.ext (by
    rw [val_map, val_restrict, val_restrict, val_map,
      MultiplicativeIdealWeight.map_restrict])

/-- Transport commutes with complex conjugation on unitary weights. -/
@[simp]
theorem map_conj (e : K ≃+* L) (χ : UnitaryIdealWeight K) :
    map e χ.conj = (map e χ).conj :=
  Subtype.ext (by
    rw [val_map, val_conj, val_conj, val_map, MultiplicativeIdealWeight.map_conj])

/-- Transport commutes with purely imaginary norm twists on unitary weights. -/
@[simp]
theorem map_normTwist (e : K ≃+* L) (z : ℂ) (hz : z.re = 0)
    (χ : UnitaryIdealWeight K) :
    map e (normTwist z hz χ) = normTwist z hz (map e χ) :=
  Subtype.ext (by
    rw [val_map, val_normTwist, val_normTwist, val_map,
      MultiplicativeIdealWeight.map_normTwist])

end Transport

/-- The ideal arithmetic function underlying a unitary weight: the restriction of the
underlying multiplicative weight to the nonzero ideals. -/
def toIdealArithmeticFunction (χ : UnitaryIdealWeight K) : IdealArithmeticFunction K :=
  χ.1.toIdealArithmeticFunction

@[simp]
theorem toIdealArithmeticFunction_apply (χ : UnitaryIdealWeight K) (I : (Ideal (𝓞 K))⁰) :
    χ.toIdealArithmeticFunction I = χ.1 I := (rfl)

/-- The ideal arithmetic function of a unitary weight agrees with that of its underlying
multiplicative weight. -/
theorem toIdealArithmeticFunction_eq_val (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction = χ.1.toIdealArithmeticFunction := by
  funext I
  rw [toIdealArithmeticFunction_apply,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]

/-- **Regrouping absorbs an imaginary norm twist.** For `z.re = 0`, twisting a unitary weight by
`N(I) ^ (-z)` multiplies its `n`-th norm coefficient by `n ^ (-z)`. -/
@[simp]
theorem normCoeff_normTwist (z : ℂ) (hz : z.re = 0) (χ : UnitaryIdealWeight K) (n : ℕ) :
    normCoeff K (normTwist z hz χ).toIdealArithmeticFunction n =
      normCoeff K χ.toIdealArithmeticFunction n * (n : ℂ) ^ (-z) := by
  simpa only [toIdealArithmeticFunction, val_normTwist] using
    MultiplicativeIdealWeight.normCoeff_normTwist z χ.1 n

/-- The ideal arithmetic function underlying a unitary ideal weight is multiplicative on
relatively prime ideals. -/
theorem isMultiplicative_toIdealArithmeticFunction (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction.IsMultiplicative :=
  MultiplicativeIdealWeight.isMultiplicative_toIdealArithmeticFunction χ.1

/-- A unitary weight is recovered from its underlying ideal arithmetic function by extending
by zero, just as in `TauCeti.MultiplicativeIdealWeight.zeroExtend_toIdealArithmeticFunction`. -/
@[simp]
theorem zeroExtend_toIdealArithmeticFunction (χ : UnitaryIdealWeight K) :
    χ.toIdealArithmeticFunction.zeroExtend = ⇑χ.1 :=
  χ.1.zeroExtend_toIdealArithmeticFunction

/-- The trivial unitary weight restricts to the constant-one ideal arithmetic function. -/
@[simp]
theorem toIdealArithmeticFunction_one :
    (1 : UnitaryIdealWeight K).toIdealArithmeticFunction = 1 := by
  rw [toIdealArithmeticFunction, val_one,
    MultiplicativeIdealWeight.toIdealArithmeticFunction_one]

/-- **A unitary weight is determined by its ideal arithmetic function.** -/
theorem toIdealArithmeticFunction_injective :
    Function.Injective
      (toIdealArithmeticFunction : UnitaryIdealWeight K → IdealArithmeticFunction K) :=
  fun _ _ h ↦ Subtype.ext (MultiplicativeIdealWeight.toIdealArithmeticFunction_injective h)

end UnitaryIdealWeight

end TauCeti
