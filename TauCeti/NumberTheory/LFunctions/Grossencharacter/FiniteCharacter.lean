/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Approximation
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.RingTheory.Ideal.Quotient.Representative

/-!
# The finite character of a presentation

Let `χ` be a presentation at the modulus `𝔪` of an algebraic Hecke character, with unitary weight
`χ_u`, ideal-side shift `σ` and algebraic infinity type `n`. Hecke's twisted theta series and the
Gauss sums of `χ` do not evaluate the ideal values `χ_u((a)) N(a) ^ σ` directly: they evaluate the
**finite character** `χ_f`, the ideal value corrected by the whole archimedean character,

`χ_f(a) = χ_u((a)) * N(a) ^ σ * χ_∞(a)`.

Here `χ_∞(a)` is the **archimedean value** `Grossencharacter.archimedeanValue`: the product of the
components of the presented Hecke character at the infinite places, evaluated at `a`. This is the
idelic archimedean component, which by Neukirch VII (6.13) is the inverse of the classical infinity
character in `χ((a)) = χ_f(a) χ_∞(a)` of VII (6.1) (see `Grossencharacter.compatibility`), so
Neukirch's `χ_f(a) = χ((a)) χ_∞(a)⁻¹` becomes multiplication by the archimedean value. It is the
monomial `∏_τ τ(a) ^ (n τ)` of the infinity type when `a` is positive at the real places of `𝔪`
(`Grossencharacter.archimedeanValue_eq_embeddingCharacter`). In general it is the monomial times,
at each real place `w`, the sign of `a` there to the power `ε_w - n_w`, the difference between the
sign parity `ε_w` of the Hecke character and the parity `n_w` of `n` at `w`
(`Grossencharacter.coe_archimedeanValue_eq_embeddingCharacter_mul_sign`); this sign factor is
trivial at the real places outside `𝔪`. With the
monomial alone, the odd character `χ₄` modulo `4∞` of `ℚ`, of exponent `0`, would give the even
function `a ↦ χ₄(|a|)` on `ℤ`, which is `1` at `-1` and `-1` at `3`, so does not even factor
through the residues modulo `4`.

The point of the correction is that `χ_f` only sees residues modulo the finite part `𝔪₀` of `𝔪`.
On the fractions prime to `𝔪₀` (the subgroup `primeToSubgroup 𝔪` of `Kˣ`), the finite character
`Grossencharacter.finiteCharacterK` is the ideal character of the presented Hecke character at
`(x)` times `χ_∞(x)`. An `x ≡ 1 mod 𝔪₀` is congruent to `1` modulo the finite conductor, where
the ideal character at `(x)` is `χ_∞(x)⁻¹` because the Hecke character is trivial on the principal
idele of `x` (`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal`). So the finite character is
trivial on every `x ≡ 1 mod 𝔪₀`, whatever the signs of `x` at the real places, and it factors
through the reduction to `(𝓞 K ⧸ 𝔪₀)ˣ`. The factor is the **residue character**
`Grossencharacter.residueCharacter`, a Mathlib `MulChar` of `𝓞 K ⧸ 𝔪₀`. On algebraic integers,
`Grossencharacter.finiteCharacter` is the coefficient that the twisted theta series attaches to a
lattice point: it is `0` exactly at the integers not prime to `𝔪` (`0` included), and the residue
character at the class of every nonzero integer
(`Grossencharacter.finiteCharacter_eq_residueCharacter`), which pins the residue character down
(`Grossencharacter.existsUnique_residueCharacter`).

Read through the triviality of the Hecke character on the principal idele of `x`, the finite
character is the inverse of the product of the local components at the primes dividing the
finite conductor `𝔣` of the Hecke character,
`χ_f(x) = ∏_{v ∣ 𝔣} χ_v(x)⁻¹` (`Grossencharacter.finiteCharacterK_eq_prod_finiteComponent_inv`).
Approximating a local unit by an integer, this shows that the finite conductor is the conductor of
the residue character: it divides an ideal `𝔫` exactly when the residue character is trivial on
the residue units congruent to `1` modulo `𝔫`
(`Grossencharacter.finiteConductor_dvd_iff_residueCharacter_eq_one`).

The coefficient and the residue character must be kept apart at `0`. When `𝔪₀ = 𝓞 K`, the residue
ring has one element, a unit, at which the residue character is `1`, while the coefficient at the
integer `0` is `0` (`Grossencharacter.residueCharacter_eq_one_of_finitePart_eq_top`).
Accordingly the comparison is stated for nonzero integers only.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue`: the archimedean value `χ_∞` on `Kˣ`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK`: the finite character on the fractions
  prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter`: the induced character of `𝓞 K ⧸ 𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter`: the finite character on `𝓞 K`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.coe_archimedeanValue_eq_embeddingCharacter_mul_sign`: the
  archimedean value is the monomial of the infinity type times the signs at the real places.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK_eq_one_of_residueHom_eq_one`: the finite
  character is trivial on the fractions congruent to `1` modulo `𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.coe_finiteCharacterK_of_algebraMap_eq`: on an algebraic
  integer `a` prime to `𝔪`, the finite character is `χ_u((a)) N(a) ^ σ χ_∞(a)`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter_residue`: the residue character at the
  reduction of `x` is the finite character at `x`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_residueCharacter` and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_of_sub_mem`: on nonzero integers the
  finite character is a function of the residue modulo `𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_zero_iff`: it vanishes exactly at the
  integers not prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_one_of_mk_eq_one`: it is `1` on the
  nonzero integers congruent to one modulo `𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_unit`: on a unit it is the archimedean
  value.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK_eq_prod_finiteComponent_inv`: the finite
  character is the inverse of the product of the components at the primes of the finite conductor.
* `TauCeti.LFunctions.Grossencharacter.finiteConductor_dvd_iff_residueCharacter_eq_one`: the
  finite conductor divides `𝔫` exactly when the residue character is trivial on the residue units
  congruent to `1` modulo `𝔫`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.1) and (6.13).
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §3.1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

namespace Grossencharacter

/-! ### The archimedean value -/

/-- **The archimedean value** `χ_∞(x)` of a presentation at `x ∈ Kˣ`: the product, over the
infinite places `w`, of the component of the presented Hecke character at `w` evaluated at the
image of `x` in `K_w`. It is the monomial `∏_τ τ(x) ^ (n τ)` of the infinity type on the elements
positive at the real places of `𝔪` (`archimedeanValue_eq_embeddingCharacter`). -/
def archimedeanValue (χ : Grossencharacter K 𝔪) : Kˣ →* ℂˣ :=
  ∏ w : InfinitePlace K, (χ.toHeckeCharacter.infiniteComponent w : w.Completionˣ →* ℂˣ).comp
    (Units.map (algebraMap K w.Completion).toMonoidHom)

/-- The archimedean value as the product of the infinite components. -/
theorem archimedeanValue_apply (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    χ.archimedeanValue x = ∏ w : InfinitePlace K,
      χ.toHeckeCharacter.infiniteComponent w
        (Units.map (algebraMap K w.Completion).toMonoidHom x) := by
  simp [archimedeanValue]

/-- **On the elements positive at the real places of `𝔪`, the archimedean value is the monomial**
`∏_τ τ(x) ^ (n τ)` of the algebraic infinity type `n`. At a real place outside `𝔪` the parities of
the Hecke character and of `n` agree, so no sign condition is needed there. -/
theorem archimedeanValue_eq_embeddingCharacter (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.property (x : K)) :
    χ.archimedeanValue x = χ.infinityType.embeddingCharacter x := by
  refine Units.ext ?_
  rw [archimedeanValue_apply, Units.coe_prod]
  exact χ.toHeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity
    χ.infinityType χ.agreesOnIdentityComponent x
    fun w hw ↦ hx w (not_imp_comm.mp (χ.realParity_eq w) hw)

open scoped Classical in
/-- **The archimedean value is the monomial of the infinity type times signs at the real places**:
at each real place `w`, the sign of `x` there to the power `ε_w - n_w`, the difference between the
sign parity of the Hecke character and the parity of the algebraic infinity type `n` at `w`. The
factor is trivial at the real places outside `𝔪` (`realParity_eq`). -/
theorem coe_archimedeanValue_eq_embeddingCharacter_mul_sign (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    (χ.archimedeanValue x : ℂ) = (χ.infinityType.embeddingCharacter x : ℂ) *
      ∏ w : {w : InfinitePlace K // w.IsReal},
        (SignType.sign (InfinitePlace.embedding_of_isReal w.property (x : K)) : ℂ) ^
          (χ.toHeckeCharacter.infinityType.realParity w -
            (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w).val := by
  rw [archimedeanValue_apply, Units.coe_prod]
  exact χ.toHeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_mul_sign
    χ.infinityType χ.agreesOnIdentityComponent x

/-! ### The finite character on the fractions prime to the modulus -/

/-- **The finite character on the fractions prime to `𝔪`**: at `x ∈ Kˣ`, a unit at the primes
dividing `𝔪`, it is the ideal character of the presented Hecke character at the principal ideal
`(x)` times the archimedean value `χ_∞(x)`. On an algebraic integer `a` it is
`χ_u((a)) N(a) ^ σ χ_∞(a)` (`coe_finiteCharacterK_of_algebraMap_eq`), and it only depends on the
residue of `x` modulo the finite part of `𝔪` (`residueCharacter_residue`). -/
def finiteCharacterK (χ : Grossencharacter K 𝔪) : primeToSubgroup 𝔪 →* ℂˣ :=
  χ.toHeckeCharacter.idealCharacter.comp
      ((NumberFieldArithmetic.idealsAwayInclusion K
        (Modulus.support_mono χ.mk_finiteConductor_dvd)).comp
        (NumberFieldArithmetic.principalIdealAway K 𝔪.support)) *
    χ.archimedeanValue.comp (primeToSubgroup 𝔪).subtype

/-- The finite character as the ideal character of `(x)` times the archimedean value. -/
theorem finiteCharacterK_apply (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.finiteCharacterK x = χ.toHeckeCharacter.idealCharacter
        (NumberFieldArithmetic.idealsAwayInclusion K
          (Modulus.support_mono χ.mk_finiteConductor_dvd)
          (NumberFieldArithmetic.principalIdealAway K 𝔪.support x)) *
      χ.archimedeanValue x :=
  (rfl)

/-- **The finite character is trivial on the fractions congruent to `1` modulo `𝔪₀`**, with no
condition at the real places. Such an `x` is congruent to `1` modulo the finite conductor, where
the ideal character of `(x)` is the inverse of `χ_∞(x)`
(`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal`). -/
theorem finiteCharacterK_eq_one_of_residueHom_eq_one (χ : Grossencharacter K 𝔪)
    {x : primeToSubgroup 𝔪} (hx : residueHom 𝔪 x = 1) : χ.finiteCharacterK x = 1 := by
  set 𝔪₀ : Modulus K := ⟨𝔪.finitePart, 𝔪.finitePart_ne_bot, ∅⟩
  -- `x` is congruent to one modulo the finite part of `𝔪` without real places, hence modulo the
  -- finite conductor.
  have hx₀ : IsCongrOne 𝔪₀ (x : Kˣ) :=
    (isCongrOne_iff_residueHom_eq_one_of_finitePart_eq (𝔪 := 𝔪₀) (𝔫 := 𝔪) rfl x.property).mpr
      ⟨hx, by simp [𝔪₀]⟩
  have hx𝔣 : IsCongrOne
      ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ (x : Kˣ) :=
    hx₀.mono χ.mk_finiteConductor_dvd_mk_finitePart
  -- There the ideal character of `(x)` is the inverse of the archimedean value.
  have harg : NumberFieldArithmetic.idealsAwayInclusion K
        (Modulus.support_mono χ.mk_finiteConductor_dvd)
        (NumberFieldArithmetic.principalIdealAway K 𝔪.support x) =
      ⟨toPrincipalIdeal (𝓞 K) K x, hx𝔣.toPrincipalIdeal_mem_idealsPrimeTo⟩ :=
    Subtype.ext (by rw [NumberFieldArithmetic.coe_idealsAwayInclusion,
      NumberFieldArithmetic.coe_principalIdealAway])
  rw [finiteCharacterK_apply, harg,
    χ.toHeckeCharacter.idealCharacter_apply_toPrincipalIdeal (x : Kˣ) hx𝔣,
    archimedeanValue_apply, inv_mul_cancel]

/-- **The finite character at an algebraic integer** `a` prime to `𝔪` is
`χ_u((a)) N(a) ^ σ χ_∞(a)`: the ideal character of the presented Hecke character at an integral
ideal prime to `𝔪` is the unitary weight times the norm to the ideal-side shift
(`coe_idealCharacter_integralIdealsAwayHom`). -/
theorem coe_finiteCharacterK_of_algebraMap_eq (χ : Grossencharacter K 𝔪)
    (x : primeToSubgroup 𝔪) {a : 𝓞 K} (ha : algebraMap (𝓞 K) K a = ((x : Kˣ) : K)) :
    (χ.finiteCharacterK x : ℂ) =
      χ.unitaryWeight.val (Ideal.span {a}) *
        ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
          (χ.archimedeanValue x : ℂ) := by
  -- The ideal `(a)` is prime to `𝔪`, since `x` is a unit at the primes dividing `𝔪`.
  have hmem : Ideal.span {a} ∈ integralIdealsPrimeTo 𝔪 :=
    Modulus.mem_integralIdealsPrimeTo.mpr (Modulus.isCoprimeTo_span_singleton_iff.mpr ⟨x, ha.symm⟩)
  have hideal : NumberFieldArithmetic.integralIdealsAwayHom K _
        (integralIdealsPrimeToInclusion χ.mk_finiteConductor_dvd ⟨_, hmem⟩) =
      NumberFieldArithmetic.idealsAwayInclusion K
        (Modulus.support_mono χ.mk_finiteConductor_dvd)
        (NumberFieldArithmetic.principalIdealAway K 𝔪.support x) :=
    Subtype.ext (Units.ext (by
      rw [NumberFieldArithmetic.coe_integralIdealsAwayHom, coe_integralIdealsPrimeToInclusion,
        NumberFieldArithmetic.coe_idealsAwayInclusion,
        ← NumberFieldArithmetic.integralIdealsAwayHom_eq_principalIdealAway
          (J := ⟨_, hmem⟩) rfl ha,
        NumberFieldArithmetic.coe_integralIdealsAwayHom]))
  rw [finiteCharacterK_apply, Units.val_mul, ← hideal,
    χ.coe_idealCharacter_integralIdealsAwayHom ⟨_, hmem⟩]

/-! ### The residue character -/

/-- **The residue character** of a presentation: the character of `𝓞 K ⧸ 𝔪₀` through which the
finite character factors (`residueCharacter_residue`). It is `0` at the non-units of the residue
ring, and it is the unique such character with the value of `finiteCharacter` at the class of
every nonzero integer (`existsUnique_residueCharacter`). -/
def residueCharacter (χ : Grossencharacter K 𝔪) : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ :=
  MulChar.ofUnitHom ((residueHom 𝔪).liftOfSurjective (residueHom_surjective 𝔪)
    ⟨χ.finiteCharacterK, fun _ hx ↦ χ.finiteCharacterK_eq_one_of_residueHom_eq_one hx⟩)

/-- **The residue character at the reduction of `x` is the finite character at `x`.** -/
@[simp]
theorem residueCharacter_residue (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.residueCharacter (residue 𝔪 x) = χ.finiteCharacterK x := by
  rw [← coe_residueHom, residueCharacter, MulChar.ofUnitHom_coe,
    MonoidHom.liftOfRightInverse_comp_apply]

/-! ### The finite character on algebraic integers -/

/-- **Hecke's finite character** of a presentation on the algebraic integers:
`χ_f(a) = χ_u((a)) N(a) ^ σ χ_∞(a)` at `a ≠ 0`, and `0` at `a = 0`. It is the product of the norm
twist of the unitary weight at `(a)` and the archimedean value, extended by `0` to a character of
`K`, at `a`. It is the coefficient of the twisted theta series: it vanishes exactly at the integers
not prime to `𝔪` (`finiteCharacter_eq_zero_iff`), and at a nonzero integer it is the residue
character at its class modulo `𝔪₀` (`finiteCharacter_eq_residueCharacter`). -/
def finiteCharacter (χ : Grossencharacter K 𝔪) : 𝓞 K →*₀ ℂ :=
  (MultiplicativeIdealWeight.normTwist (-(χ.idealShift : ℂ))
      χ.unitaryWeight.val).toMonoidWithZeroHom.comp (Submodule.spanSingleton (𝓞 K)) *
    (MulChar.ofUnitHom χ.archimedeanValue).toMonoidWithZeroHom.comp
      (algebraMap (𝓞 K) K : 𝓞 K →*₀ K)

/-- The finite character as the norm twist of the unitary weight at `(a)` times the archimedean
value, extended by `0`, at `a`. -/
private theorem finiteCharacter_apply (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacter a =
      MultiplicativeIdealWeight.normTwist (-(χ.idealShift : ℂ)) χ.unitaryWeight.val
          (Ideal.span {a}) *
        MulChar.ofUnitHom χ.archimedeanValue (algebraMap (𝓞 K) K a) :=
  (rfl)

/-- The defining formula of the finite character at an algebraic integer `a` whose image in `K`
is the unit `x`; such an `a` is nonzero. -/
theorem finiteCharacter_apply_of_algebraMap_eq (χ : Grossencharacter K 𝔪) {a : 𝓞 K} {x : Kˣ}
    (hx : algebraMap (𝓞 K) K a = x) :
    χ.finiteCharacter a = χ.unitaryWeight.val (Ideal.span {a}) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
        (χ.archimedeanValue x : ℂ) := by
  simp [finiteCharacter_apply, hx]

/-- **The finite character vanishes at the integers not prime to `𝔪`**, `0` included. -/
theorem finiteCharacter_eq_zero_of_not_isCoprimeTo (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (ha : ¬ 𝔪.IsCoprimeTo (Ideal.span {a})) : χ.finiteCharacter a = 0 := by
  simp [finiteCharacter_apply, χ.unitaryWeight_eq_zero _ ha]

/-- **At an integer prime to `𝔪`, the finite character is `finiteCharacterK`.** -/
theorem finiteCharacter_eq_finiteCharacterK (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (x : primeToSubgroup 𝔪) (ha : algebraMap (𝓞 K) K a = ((x : Kˣ) : K)) :
    χ.finiteCharacter a = χ.finiteCharacterK x := by
  rw [χ.coe_finiteCharacterK_of_algebraMap_eq x ha, χ.finiteCharacter_apply_of_algebraMap_eq ha]

/-- **On a unit the finite character is the archimedean value**, since `(u) = 𝓞 K` and
`N(u) = 1`. -/
theorem finiteCharacter_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    χ.finiteCharacter (u : 𝓞 K) =
      χ.archimedeanValue (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := by
  rw [χ.finiteCharacter_apply_of_algebraMap_eq
      (x := Units.map (algebraMap (𝓞 K) K).toMonoidHom u) rfl,
    Ideal.span_singleton_eq_top.mpr u.isUnit]
  simp

/-- **On a unit the finite character on the fractions prime to `𝔪` is the archimedean value.** -/
@[simp]
theorem finiteCharacterK_unitsToPrimeToSubgroup (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) :
    χ.finiteCharacterK (unitsToPrimeToSubgroup 𝔪 u) =
      χ.archimedeanValue (Units.map (algebraMap (𝓞 K) K).toMonoidHom u) := by
  refine Units.ext ?_
  rw [← χ.finiteCharacter_eq_finiteCharacterK (a := u) _ (by simp), finiteCharacter_unit]

/-- **The finite character vanishes exactly at the integers not prime to `𝔪`.** -/
theorem finiteCharacter_eq_zero_iff (χ : Grossencharacter K 𝔪) {a : 𝓞 K} :
    χ.finiteCharacter a = 0 ↔ ¬ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  refine ⟨fun h ha ↦ ?_, χ.finiteCharacter_eq_zero_of_not_isCoprimeTo⟩
  obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp ha
  rw [χ.finiteCharacter_eq_finiteCharacterK x hx.symm] at h
  exact (χ.finiteCharacterK x).ne_zero h

/-- **On nonzero integers, the finite character is the residue character** at the class modulo
`𝔪₀`. At an integer not prime to `𝔪` both vanish, the class not being a unit. The integer `0` is
excluded: when `𝔪₀ = 𝓞 K` its class is the unit of the zero ring. -/
theorem finiteCharacter_eq_residueCharacter (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha : a ≠ 0) :
    χ.finiteCharacter a = χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart a) := by
  by_cases hcop : 𝔪.IsCoprimeTo (Ideal.span {a})
  · obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp hcop
    rw [χ.finiteCharacter_eq_finiteCharacterK x hx.symm, ← residueCharacter_residue,
      residue_eq x (a := a) (b := 1) (by simp) (by rw [map_one, one_mul, hx])]
  · rw [χ.finiteCharacter_eq_zero_of_not_isCoprimeTo hcop, MulChar.map_nonunit]
    exact fun hu ↦ hcop (Modulus.isCoprimeTo_iff_sup_eq_top.mpr
      ⟨Ideal.span_singleton_eq_bot.not.mpr ha, Ideal.Quotient.isUnit_mk_iff.mp hu⟩)

/-- **The finite character only sees residues modulo `𝔪₀`**: nonzero integers congruent modulo
the finite part of `𝔪` have the same finite character. -/
theorem finiteCharacter_eq_of_sub_mem (χ : Grossencharacter K 𝔪) {a b : 𝓞 K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a - b ∈ 𝔪.finitePart) : χ.finiteCharacter a = χ.finiteCharacter b := by
  rw [χ.finiteCharacter_eq_residueCharacter ha, χ.finiteCharacter_eq_residueCharacter hb,
    Ideal.Quotient.eq.mpr hab]

/-- **The finite character is `1` on the nonzero integers congruent to one modulo `𝔪₀`**, with no
sign condition at the real places of `𝔪`. The integer `0` is excluded: when `𝔪₀ = 𝓞 K` it is
congruent to one, while `χ_f(0) = 0`. -/
theorem finiteCharacter_eq_one_of_mk_eq_one (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha₀ : a ≠ 0)
    (ha : Ideal.Quotient.mk 𝔪.finitePart a = 1) : χ.finiteCharacter a = 1 := by
  rw [χ.finiteCharacter_eq_residueCharacter ha₀, ha, MulChar.map_one]

/-- **The residue character is determined by the finite character**: it is the unique character
of `𝓞 K ⧸ 𝔪₀` whose value at the class of every nonzero integer `a` is `χ_f(a)`. Every class has a
nonzero representative, since `𝔪₀ ≠ 0`. -/
theorem existsUnique_residueCharacter (χ : Grossencharacter K 𝔪) :
    ∃! ψ : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ,
      ∀ a : 𝓞 K, a ≠ 0 → ψ (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a := by
  refine ⟨χ.residueCharacter, fun a ha ↦ (χ.finiteCharacter_eq_residueCharacter ha).symm,
    fun ψ hψ ↦ MulChar.ext' fun r ↦ ?_⟩
  obtain ⟨b, hb₀, rfl⟩ := Ideal.Quotient.exists_ne_zero_mk_eq 𝔪.finitePart_ne_bot r
  rw [hψ b hb₀, χ.finiteCharacter_eq_residueCharacter hb₀]

/-- **At finite part `𝓞 K` the residue character is trivial**: the residue ring has a single
element, the unit `1`. The finite character is nevertheless `0` at `0`. -/
theorem residueCharacter_eq_one_of_finitePart_eq_top (χ : Grossencharacter K 𝔪)
    (h : 𝔪.finitePart = ⊤) : χ.residueCharacter = 1 := by
  have : Subsingleton (𝓞 K ⧸ 𝔪.finitePart) := Ideal.Quotient.subsingleton_iff.mpr h
  refine MulChar.ext fun u ↦ ?_
  rw [Subsingleton.elim (u : 𝓞 K ⧸ 𝔪.finitePart) 1, MulChar.map_one, MulChar.map_one]

/-! ### The finite character as a product of local components -/

/-- **The finite character is the inverse of the product of the components at the ramified
primes**: at `x` prime to `𝔪`, `χ_f(x) = ∏_{v ∣ 𝔣} χ_v(x)⁻¹`, the product running over the primes
dividing the finite conductor `𝔣` of the presented Hecke character. This is the triviality of
the Hecke character on the principal idele of `x`
(`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal_eq_prod_inv_mul_prod_inv`). -/
theorem finiteCharacterK_eq_prod_finiteComponent_inv (χ : Grossencharacter K 𝔪)
    (x : primeToSubgroup 𝔪) :
    χ.finiteCharacterK x =
      (∏ v ∈ (⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot,
          ∅⟩ : Modulus K).support,
        χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)))⁻¹ := by
  set I := NumberFieldArithmetic.idealsAwayInclusion K
    (Modulus.support_mono χ.mk_finiteConductor_dvd)
    (NumberFieldArithmetic.principalIdealAway K 𝔪.support x) with hIdef
  have hI : (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) = toPrincipalIdeal (𝓞 K) K (x : Kˣ) := by
    rw [NumberFieldArithmetic.coe_idealsAwayInclusion,
      NumberFieldArithmetic.coe_principalIdealAway]
  have hmem : toPrincipalIdeal (𝓞 K) K (x : Kˣ) ∈ idealsPrimeTo
      ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ :=
    hI ▸ I.property
  rw [finiteCharacterK_apply, ← hIdef, show I = ⟨_, hmem⟩ from Subtype.ext hI,
    HeckeCharacter.idealCharacter_apply_toPrincipalIdeal_eq_prod_inv_mul_prod_inv,
    archimedeanValue_apply, mul_right_comm, inv_mul_cancel, one_mul]

/-! ### The finite conductor and the residue character -/

/-- An integer close to a given integral element of `K_v` at `v`, and congruent to `1` modulo the
exponent of `𝔪` at every other prime dividing `𝔪`. -/
private theorem exists_sub_one_mem_and_valued_sub_le (𝔪 : Modulus K) (v : HeightOneSpectrum (𝓞 K))
    (t : v.adicCompletionIntegers K) :
    ∃ r : 𝓞 K, (∀ w ∈ 𝔪.support, w ≠ v → r - 1 ∈ w.asIdeal ^ 𝔪.exponent w) ∧
      Valued.v ((t : v.adicCompletion K) - algebraMap (𝓞 K) (v.adicCompletion K) r) ≤
        WithZero.exp (-(𝔪.exponent v : ℤ)) := by
  classical
  obtain ⟨r, hr⟩ := HeightOneSpectrum.exists_forall_valued_sub_le (insert v 𝔪.support)
    (Function.update (1 : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletionIntegers K) v t)
    𝔪.exponent
  refine ⟨r, fun w hw hwv ↦ ?_, ?_⟩
  · have hrw := hr w (Finset.mem_insert_of_mem hw)
    rw [Function.update_of_ne hwv, Pi.one_apply, OneMemClass.coe_one] at hrw
    rw [w.mem_asIdeal_pow_iff_valued_algebraMap_le (K := K), map_sub, map_one,
      Valuation.map_sub_swap]
    exact hrw
  · have hrv := hr v (Finset.mem_insert_self v _)
    rw [Function.update_self] at hrv
    exact hrv

/-- An integer close to an element `t ≡ 1 mod v ^ n(v)` of `K_v` at `v`, `n(v)` the multiplicity of
`v` in `𝔫 ⊇ 𝔪₀`, and congruent to `1` modulo the exponent of `𝔪` at every other prime of `𝔪`, is
congruent to `1` modulo `𝔫`. -/
private theorem sub_one_mem_of_valued_sub_le {𝔫 : Ideal (𝓞 K)} (h𝔫 : 𝔪.finitePart ≤ 𝔫)
    {v : HeightOneSpectrum (𝓞 K)} {t : v.adicCompletion K}
    (ht : Valued.v (t - 1) ≤
      WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk 𝔫).factors : ℤ)))
    {r : 𝓞 K} (hrw : ∀ w ∈ 𝔪.support, w ≠ v → r - 1 ∈ w.asIdeal ^ 𝔪.exponent w)
    (hrv : Valued.v (t - algebraMap (𝓞 K) (v.adicCompletion K) r) ≤
      WithZero.exp (-(𝔪.exponent v : ℤ))) :
    r - 1 ∈ 𝔫 := by
  have h𝔫ne : 𝔫 ≠ ⊥ := fun h0 ↦ 𝔪.finitePart_ne_bot (le_bot_iff.mp (h0 ▸ h𝔫))
  -- The multiplicity of a prime in `𝔫` is at most its exponent in `𝔪`.
  have hn𝔪 (w : HeightOneSpectrum (𝓞 K)) :
      (Associates.mk w.asIdeal).count (Associates.mk 𝔫).factors ≤ 𝔪.exponent w := by
    rw [Modulus.exponent_def,
      HeightOneSpectrum.le_count_associates_iff_le_pow w 𝔪.finitePart_ne_bot]
    exact h𝔫.trans ((HeightOneSpectrum.le_count_associates_iff_le_pow w h𝔫ne _).mp le_rfl)
  -- Check the congruence one prime power at a time.
  rw [← Ideal.iInf_maxPowDividing_eq h𝔫ne, Submodule.mem_iInf]
  intro w
  rw [HeightOneSpectrum.maxPowDividing]
  by_cases hw : w ∈ 𝔪.support
  · by_cases hwv : w = v
    · subst hwv
      rw [w.mem_asIdeal_pow_iff_valued_algebraMap_le (K := K), map_sub, map_one,
        ← sub_add_sub_cancel _ t]
      refine (Valuation.map_add _ _ _).trans (max_le ?_ ht)
      rw [Valuation.map_sub_swap]
      exact hrv.trans (WithZero.exp_le_exp.mpr (by have := hn𝔪 w; omega))
    · exact Ideal.pow_le_pow_right (hn𝔪 w) (hrw w hw hwv)
  · have h0 := hn𝔪 w
    rw [(Modulus.mem_support_iff_exponent_ne_zero 𝔪 w).not, not_not] at hw
    rw [hw, Nat.le_zero] at h0
    rw [h0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top

/-- An integer outside `v` and congruent to `1` modulo the exponent of `𝔪` at every other prime of
`𝔪` lies outside every prime of `𝔪`. -/
private theorem notMem_of_sub_one_mem {v : HeightOneSpectrum (𝓞 K)} {r : 𝓞 K} (hrv : r ∉ v.asIdeal)
    (hrw : ∀ w ∈ 𝔪.support, w ≠ v → r - 1 ∈ w.asIdeal ^ 𝔪.exponent w) :
    ∀ w ∈ 𝔪.support, r ∉ w.asIdeal := by
  intro w hw hrw0
  by_cases hwv : w = v
  · exact hrv (hwv ▸ hrw0)
  have h1 := Ideal.pow_le_self (Modulus.exponent_pos_of_mem_support hw).ne' (hrw w hw hwv)
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using sub_mem hrw0 h1))

/-- The component at `v` of the presented Hecke character takes the same value at two units of
`𝒪_v` congruent modulo `v ^ 𝔪.exponent v`. -/
private theorem finiteComponent_eq_of_valued_sub_le (χ : Grossencharacter K 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} {s t : (v.adicCompletion K)ˣ}
    (hs : Valued.v (s : v.adicCompletion K) = 1) (ht : Valued.v (t : v.adicCompletion K) = 1)
    (hst : Valued.v ((t : v.adicCompletion K) - s) ≤ WithZero.exp (-(𝔪.exponent v : ℤ))) :
    χ.toHeckeCharacter.finiteComponent v t = χ.toHeckeCharacter.finiteComponent v s := by
  -- `s⁻¹ t` lies in `U(K_v, 𝔪.exponent v)`, on which the component is trivial.
  have hq : s⁻¹ * t ∈ TauCeti.unitFiltration (v.adicCompletion K)
      (χ.toHeckeCharacter.conductorExponent v) := by
    refine TauCeti.unitFiltration_antitone (χ.conductorExponent_le_exponent v) ?_
    have hs0 : (s : v.adicCompletion K) ≠ 0 := s.ne_zero
    -- The key factorization: `s⁻¹ t - 1 = s⁻¹ (t - s)`.
    have hfac : (s : v.adicCompletion K)⁻¹ * t - 1 =
        (s : v.adicCompletion K)⁻¹ * ((t : v.adicCompletion K) - s) := by
      field_simp
    rw [HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff, Units.val_mul,
      Units.val_inv_eq_inv_val, hfac]
    simpa [hs, ht] using hst
  rw [← mul_inv_cancel_left s t, map_mul,
    χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration hq, mul_one]

/-- If the residue character is trivial on the residue units of the integers congruent to `1`
modulo an ideal `𝔫 ⊇ 𝔪₀`, then `𝔫` is contained in `v ^ a_v(χ)` for every prime `v`. -/
private theorem le_pow_conductorExponent_of_residueCharacter_eq_one (χ : Grossencharacter K 𝔪)
    {𝔫 : Ideal (𝓞 K)} (h𝔫 : 𝔪.finitePart ≤ 𝔫)
    (h : ∀ u : 𝓞 K, IsUnit (Ideal.Quotient.mk 𝔪.finitePart u) → u - 1 ∈ 𝔫 →
      χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart u) = 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    𝔫 ≤ v.asIdeal ^ χ.toHeckeCharacter.conductorExponent v := by
  set 𝔣 : Modulus K :=
    ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩
  have h𝔫ne : 𝔫 ≠ ⊥ := fun h0 ↦ 𝔪.finitePart_ne_bot (le_bot_iff.mp (h0 ▸ h𝔫))
  refine ((HeightOneSpectrum.le_count_associates_iff_le_pow v h𝔫ne _).mp le_rfl).trans
    (Ideal.pow_le_pow_right ?_)
  -- Away from the primes of the finite conductor there is nothing to prove.
  by_cases hv𝔣 : v ∈ 𝔣.support
  swap
  · have h0 : χ.toHeckeCharacter.conductorExponent v = 0 := by
      by_contra hne
      exact hv𝔣 ((𝔣.mem_support_iff v).mpr ((χ.toHeckeCharacter.dvd_finiteConductor_iff v).mpr hne))
    rw [h0]
    exact Nat.zero_le _
  have h𝔣𝔪 : 𝔣.support ⊆ 𝔪.support := Modulus.support_mono χ.mk_finiteConductor_dvd
  -- Given `t ∈ U(K_v, n)`, choose an integer `r` close to `t` at `v` and to `1` at the other
  -- primes of `𝔪`. Then `r ≡ 1 mod 𝔫`, so `1 = χ_f(r) = χ_v(r)⁻¹`, and `χ_v(t) = χ_v(r)`.
  rw [HeckeCharacter.conductorExponent_le_iff]
  intro t ht
  have ht' := (HeightOneSpectrum.mem_unitFiltration_adicCompletion_iff (v := v)).mp ht
  obtain ⟨r, hrw, hrv⟩ := exists_sub_one_mem_and_valued_sub_le 𝔪 v ⟨t, ht'.1.le⟩
  have hmem := sub_one_mem_of_valued_sub_le h𝔫 ht'.2 hrw hrv
  -- `r` is a unit at every prime of `𝔪`.
  have hr1 : Valued.v (algebraMap (𝓞 K) (v.adicCompletion K) r) = 1 := by
    rw [← ht'.1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [Valuation.map_sub_swap, ht'.1]
    exact hrv.trans_lt (WithZero.exp_lt_one_iff.mpr (by
      have := Modulus.exponent_pos_of_mem_support (h𝔣𝔪 hv𝔣); omega))
  have hrw' := notMem_of_sub_one_mem
    ((v.notMem_asIdeal_iff_valued_algebraMap_eq_one (K := K)).mpr hr1) hrw
  have hr0 : r ≠ 0 := fun h0 ↦ hrw' v (h𝔣𝔪 hv𝔣) (by rw [h0]; exact zero_mem _)
  have hcop : 𝔪.IsCoprimeTo (Ideal.span {r}) :=
    Modulus.isCoprimeTo_iff.mpr ⟨Ideal.span_singleton_eq_bot.not.mpr hr0,
      fun w hw hdvd ↦ hrw' w hw (Ideal.dvd_span_singleton.mp hdvd)⟩
  obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp hcop
  set xv := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)
  have hxv : (xv : v.adicCompletion K) = algebraMap (𝓞 K) (v.adicCompletion K) r := by
    simp [xv, hx, ← IsScalarTower.algebraMap_apply]
  -- `1 = χ_f(r) = χ_v(r)⁻¹`, the components at the other primes of `𝔣` being trivial at `r`.
  have hχr := h r (Ideal.Quotient.isUnit_mk_iff.mpr (Modulus.isCoprimeTo_iff_sup_eq_top.mp hcop).2)
    hmem
  rw [← χ.finiteCharacter_eq_residueCharacter hr0,
    χ.finiteCharacter_eq_finiteCharacterK x hx.symm, Units.val_eq_one,
    finiteCharacterK_eq_prod_finiteComponent_inv, inv_eq_one,
    Finset.prod_eq_single_of_mem v hv𝔣 fun w hw hwv ↦ ?_] at hχr
  · rw [χ.finiteComponent_eq_of_valued_sub_le (s := xv) (by rwa [hxv]) ht'.1 (by rwa [hxv]), hχr]
  refine χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
    (TauCeti.unitFiltration_antitone (χ.conductorExponent_le_exponent w) ?_)
  exact (w.unitsMap_algebraMap_mem_unitFiltration_iff hx.symm).mpr
    ⟨hrw' w (h𝔣𝔪 hw), hrw w (h𝔣𝔪 hw) hwv⟩

/-- **The finite conductor is read off the residue character.** The finite conductor of a
presentation divides an ideal `𝔫` exactly when the residue character is trivial on the residue
units modulo `𝔪₀` of the integers congruent to `1` modulo `𝔫`. -/
theorem finiteConductor_dvd_iff_residueCharacter_eq_one (χ : Grossencharacter K 𝔪)
    (𝔫 : Ideal (𝓞 K)) :
    χ.toHeckeCharacter.finiteConductor ∣ 𝔫 ↔
      ∀ u : 𝓞 K, IsUnit (Ideal.Quotient.mk 𝔪.finitePart u) → u - 1 ∈ 𝔫 →
        χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart u) = 1 := by
  refine ⟨fun h𝔣 u hu hu1 ↦ ?_, fun h ↦ ?_⟩
  · by_cases hu0 : u = 0
    · -- A residue ring in which `0` is a unit has a single element.
      rw [hu0, map_zero, isUnit_zero_iff] at hu
      have := subsingleton_of_zero_eq_one hu
      rw [Subsingleton.elim (Ideal.Quotient.mk 𝔪.finitePart u) 1, map_one]
    have hcop : 𝔪.IsCoprimeTo (Ideal.span {u}) :=
      Modulus.isCoprimeTo_iff_sup_eq_top.mpr
        ⟨Ideal.span_singleton_eq_bot.not.mpr hu0, Ideal.Quotient.isUnit_mk_iff.mp hu⟩
    obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp hcop
    rw [← χ.finiteCharacter_eq_residueCharacter hu0,
      χ.finiteCharacter_eq_finiteCharacterK x hx.symm, finiteCharacterK_eq_prod_finiteComponent_inv,
      Finset.prod_eq_one fun w hw ↦ ?_, inv_one, Units.val_one]
    -- At a prime `w` of the finite conductor, `u ≡ 1` modulo `w ^ a_w(χ)`.
    have hw𝔪 := Modulus.support_mono χ.mk_finiteConductor_dvd hw
    refine χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
      ((w.unitsMap_algebraMap_mem_unitFiltration_iff hx.symm).mpr ⟨fun huw ↦
        (Modulus.isCoprimeTo_iff.mp hcop).2 w hw𝔪 (Ideal.dvd_span_singleton.mpr huw), ?_⟩)
    exact Ideal.dvd_iff_le.mp ((χ.toHeckeCharacter.pow_dvd_finiteConductor_iff w _).mpr le_rfl)
      (Ideal.dvd_iff_le.mp h𝔣 hu1)
  -- Conversely, pass to `𝔫 ⊔ 𝔪₀`, which contains `𝔪₀`, and compare prime by prime.
  have h' : ∀ u : 𝓞 K, IsUnit (Ideal.Quotient.mk 𝔪.finitePart u) →
      u - 1 ∈ 𝔫 ⊔ 𝔪.finitePart → χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart u) = 1 := by
    intro u hu hu1
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hu1
    have hmk : Ideal.Quotient.mk 𝔪.finitePart (u - b) = Ideal.Quotient.mk 𝔪.finitePart u :=
      Ideal.Quotient.eq.mpr (by rw [sub_sub_cancel_left]; exact neg_mem hb)
    rw [← hmk] at hu ⊢
    exact h _ hu (by rwa [show u - b - 1 = a by linear_combination -hab])
  rw [Ideal.dvd_iff_le]
  refine (le_sup_left (b := 𝔪.finitePart)).trans ((le_iInf fun v ↦ ?_).trans
    (Ideal.iInf_maxPowDividing_eq χ.toHeckeCharacter.finiteConductor_ne_bot).le)
  rw [HeightOneSpectrum.maxPowDividing, χ.toHeckeCharacter.count_finiteConductor]
  exact le_pow_conductorExponent_of_residueCharacter_eq_one χ le_sup_right h' v

end Grossencharacter

end TauCeti.LFunctions
