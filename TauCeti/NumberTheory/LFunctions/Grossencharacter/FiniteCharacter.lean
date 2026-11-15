/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.Analysis.SpecialFunctions.Complex.ArchimedeanCharacter
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.UnitCompatibility
import TauCeti.RingTheory.Ideal.Quotient.Coprime
import TauCeti.RingTheory.Ideal.Quotient.Representative

/-!
# The finite character of a Grossencharacter presentation

Let `χ` be a presentation at the modulus `𝔪` of an algebraic Hecke character, with unitary weight
`χ_u`, ideal-side shift `σ` and algebraic infinity type `n`. Hecke's finite character is not a
field of the presentation; it is derived from the idele class character. Its archimedean side is
the **full archimedean value** `χ_∞(x) = ∏_τ τ(x) ^ n_τ · ∏_{w real} sgn(τ_w x) ^ (ε_w - n_w)`
(`Grossencharacter.archimedeanValue`), the algebraic monomial corrected, at each real place `w`,
by the sign by which the parity `ε_w` of the archimedean restriction differs from the parity of
the algebraic exponent `n_w`. It is exactly the product of the archimedean components of the idele
class character on the diagonal (`Grossencharacter.archimedeanValue_eq_prod_infiniteComponent`).
The finite character of an algebraic integer `a` is then

`χ_f(a) = χ_u((a)) N(a) ^ σ χ_∞(a)`  (`Grossencharacter.finiteCharacter`),

Neukirch's `χ_f = χ((a)) χ_∞(a)⁻¹` in the idelic sign convention of
`Grossencharacter.compatibility`. It is completely multiplicative, vanishes exactly at the elements
whose ideal is not prime to `𝔪`, is `1` on the elements congruent to one modulo `𝔪`, and on nonzero
elements depends only on the residue class modulo the finite part `𝔪₀` of `𝔪`.

The last property comes from the idelic picture. The same formula, with the ideal character of the
Hecke character in place of `χ_u N ^ σ`, defines a character of the elements of `Kˣ` that are
units at the primes dividing `𝔪₀` (`Grossencharacter.finiteCharacterK`); on an element congruent
to one at those primes it is trivial, because the principal idele of such an element is trivial
for the character and its local components at the conductor primes are. It therefore factors
through the reduction `GlobalNumberFields.residueHom` onto `(𝓞 K ⧸ 𝔪₀)ˣ`, and the factored
character is the **residue character** `Grossencharacter.residueCharacter`, a Dirichlet-type
`MulChar` of `𝓞 K ⧸ 𝔪₀`, the unique one agreeing with `χ_f` at every nonzero element
(`Grossencharacter.existsUnique_residueCharacter`).

The two must be kept apart: `χ_f(0) = 0`, since `(0)` is not prime to `𝔪`, while for a character
of finite part `𝓞 K` the residue ring has a single element, a unit, at which the residue character
is `1` (`Grossencharacter.residueCharacter_of_finitePart_eq_top`). The twisted theta series of a
Grossencharacter evaluates the coefficient `χ_f`, and its Gauss sums evaluate the residue
character.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue`: the full archimedean value `χ_∞`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter`: Hecke's finite character `χ_f`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK`: its extension to the elements of `Kˣ`
  that are units at the primes dividing `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter`: the residue character modulo the finite
  part of `𝔪`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue_eq_prod_infiniteComponent`: the full
  archimedean value is the product of the archimedean components of the idele class character.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_zero_iff`: `χ_f(a) = 0` exactly when
  `(a)` is not prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_one_of_isCongrOne`: `χ_f(a) = 1` for
  `a ≡ 1 mod* 𝔪`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK_eq_one_of_residueHom_eq_one`: the
  extended character is trivial on the elements reducing to one modulo the finite part.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter_mk` and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_of_sub_mem`: on nonzero elements, `χ_f`
  is the residue character of the residue class.
* `TauCeti.LFunctions.Grossencharacter.existsUnique_residueCharacter`: the residue character is
  the unique multiplicative character of `𝓞 K ⧸ 𝔪₀` agreeing with `χ_f` at nonzero elements.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.1), (6.13) and (7.4).
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

namespace Grossencharacter

/-! ### The full archimedean value -/

open scoped Classical in
/-- **The full archimedean value** `χ_∞` of a presentation: the monomial `∏_τ τ(x) ^ n_τ` of the
algebraic infinity type `n`, times, at each real place `w`, the sign of `x` at `w` raised to the
difference between the parity of the archimedean restriction of the presented Hecke character and
the parity of `n` at `w`. That difference vanishes at the real places outside `𝔪`
(`Grossencharacter.realParity_eq`). The value is the product of the archimedean components of the
presented idele class character (`archimedeanValue_eq_prod_infiniteComponent`). -/
def archimedeanValue (χ : Grossencharacter K 𝔪) : Kˣ →* ℂˣ where
  toFun x := χ.infinityType.embeddingCharacter x * ∏ w : {w : InfinitePlace K // w.IsReal},
    realSignCharacter (Units.map (InfinitePlace.embedding_of_isReal w.2).toMonoidHom x) ^
      (χ.toHeckeCharacter.infinityType.realParity w -
        (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w).val
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_pow, Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

open scoped Classical in
/-- The full archimedean value at `x` is `∏_τ τ(x) ^ n_τ · ∏_{w real} sgn(τ_w x) ^ (ε_w - n_w)`. -/
theorem coe_archimedeanValue_apply (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    (χ.archimedeanValue x : ℂ) = (χ.infinityType.embeddingCharacter x : ℂ) *
      ∏ w : {w : InfinitePlace K // w.IsReal},
        (SignType.sign (InfinitePlace.embedding_of_isReal w.2 (x : K)) : ℂ) ^
          (χ.toHeckeCharacter.infinityType.realParity w -
            (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w).val := by
  simp [archimedeanValue, coe_realSignCharacter_apply]

/-- **The full archimedean value is the product of the archimedean components** of the presented
idele class character, evaluated on the diagonal image of `x`. -/
theorem archimedeanValue_eq_prod_infiniteComponent (χ : Grossencharacter K 𝔪) (x : Kˣ) :
    χ.archimedeanValue x = ∏ w : InfinitePlace K, χ.toHeckeCharacter.infiniteComponent w
      (Units.map (algebraMap K w.Completion).toMonoidHom x) :=
  Units.ext <| by
    rw [Units.coe_prod, coe_archimedeanValue_apply,
      χ.toHeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_mul_prod_sign
        χ.infinityType χ.agreesOnIdentityComponent x]

/-- On an element positive at the real places of `𝔪`, for instance one congruent to one modulo
`𝔪`, the full archimedean value is the monomial of the algebraic infinity type: at the other real
places the two parities agree, so no sign intervenes. -/
theorem archimedeanValue_eq_embeddingCharacter_of_pos (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K)) :
    χ.archimedeanValue x = χ.infinityType.embeddingCharacter x := by
  refine Units.ext ?_
  rw [coe_archimedeanValue_apply, Finset.prod_eq_one fun w _ ↦ ?_, mul_one]
  by_cases hw : w ∈ 𝔪.infinitePart
  · rw [sign_pos (hx w hw), SignType.coe_one, one_pow]
  · rw [χ.realParity_eq w hw, sub_self, ZMod.val_zero, pow_zero]

/-! ### The finite character -/

/-- The value of the finite character at a nonzero algebraic integer `a`, with `x = a` in `Kˣ`. -/
private def finiteCharacterAux (χ : Grossencharacter K 𝔪) (a : 𝓞 K) (x : Kˣ) : ℂ :=
  χ.unitaryWeight.1 (Ideal.span {a}) *
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) * χ.archimedeanValue x

private theorem finiteCharacterAux_mul (χ : Grossencharacter K 𝔪) (a b : 𝓞 K) (x y : Kˣ) :
    χ.finiteCharacterAux (a * b) (x * y) = χ.finiteCharacterAux a x * χ.finiteCharacterAux b y := by
  simp only [finiteCharacterAux, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Units.val_mul]
  ring

/-- **Hecke's finite character** of a presentation: at an algebraic integer `a ≠ 0` it is
`χ_f(a) = χ_u((a)) N(a) ^ σ χ_∞(a)` (`finiteCharacter_apply`), the full ideal value of the
presentation times the full archimedean value, and `χ_f(0) = 0`. It vanishes exactly at the
elements whose ideal is not prime to `𝔪` (`finiteCharacter_eq_zero_iff`), is `1` on the elements
congruent to one modulo `𝔪` (`finiteCharacter_eq_one_of_isCongrOne`), and on nonzero elements
it is the residue character of the residue class modulo the finite part of `𝔪`
(`residueCharacter_mk`). -/
def finiteCharacter (χ : Grossencharacter K 𝔪) : 𝓞 K →*₀ ℂ where
  toFun a := by
    classical
    exact if ha : a = 0 then 0 else
      χ.finiteCharacterAux a (Units.mk0 _ (RingOfIntegers.coe_ne_zero_iff.mpr ha))
  map_zero' := by simp
  map_one' := by
    rw [dite_eq_right_of_eq_false (eq_false one_ne_zero), finiteCharacterAux,
      Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one, map_one, Nat.cast_one,
      Complex.one_cpow, one_mul, one_mul, Units.val_eq_one, ← map_one χ.archimedeanValue]
    exact congrArg _ (Units.ext (map_one _))
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    rw [dite_eq_right_of_eq_false (eq_false (mul_ne_zero ha hb)),
      dite_eq_right_of_eq_false (eq_false ha), dite_eq_right_of_eq_false (eq_false hb),
      ← finiteCharacterAux_mul]
    exact congrArg _ (Units.ext (map_mul _ a b))

/-- The finite character at a nonzero algebraic integer `a`, with `x = a` in `Kˣ`, is
`χ_u((a)) N(a) ^ σ χ_∞(x)`. -/
theorem finiteCharacter_apply (χ : Grossencharacter K 𝔪) (x : Kˣ) (a : 𝓞 K)
    (ha : algebraMap (𝓞 K) K a = x) :
    χ.finiteCharacter a = χ.unitaryWeight.1 (Ideal.span {a}) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) * χ.archimedeanValue x := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [← ha, map_zero])
  simp only [finiteCharacter, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, ha0, ↓reduceDIte,
    finiteCharacterAux]
  congr
  exact Units.ext ha

/-- **The finite character vanishes exactly off the elements prime to the modulus.** -/
theorem finiteCharacter_eq_zero_iff (χ : Grossencharacter K 𝔪) {a : 𝓞 K} :
    χ.finiteCharacter a = 0 ↔ ¬ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  by_cases ha : a = 0
  · simp [ha, Modulus.isCoprimeTo_iff]
  set x := Units.mk0 _ (RingOfIntegers.coe_ne_zero_iff.mpr ha)
  rw [χ.finiteCharacter_apply x a rfl]
  refine ⟨fun h hc ↦ ?_, fun hc ↦ by rw [χ.unitaryWeight_eq_zero _ hc, zero_mul, zero_mul]⟩
  -- On an ideal prime to `𝔪`, the full ideal value is a value of the ideal character.
  have hx : x ∈ primeToSubgroup 𝔪 := (Modulus.isCoprimeTo_span_singleton_iff rfl).mp hc
  rw [← χ.coe_idealCharacter_toPrincipalIdeal x hx a rfl, ← Units.val_mul] at h
  exact Units.ne_zero _ h

/-- **The finite character is `1` on the elements congruent to one modulo `𝔪`**: this is Hecke's
unit relation `Grossencharacter.compatibility`, the full archimedean value being the algebraic
monomial there. -/
theorem finiteCharacter_eq_one_of_isCongrOne (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : IsCongrOne 𝔪 x) (a : 𝓞 K) (ha : algebraMap (𝓞 K) K a = x) :
    χ.finiteCharacter a = 1 := by
  rw [χ.finiteCharacter_apply x a ha,
    χ.archimedeanValue_eq_embeddingCharacter_of_pos fun _ ↦ hx.pos,
    AlgebraicInfinityType.coe_embeddingCharacter_apply]
  exact χ.compatibility x hx a ha

/-! ### The extension to elements prime to the modulus -/

/-- The principal fractional ideal of an element that is a unit at the primes dividing `𝔪`, as a
fractional ideal prime to the finite conductor of the presented character. -/
private def principalIdeal (χ : Grossencharacter K 𝔪) :
    primeToSubgroup 𝔪 →* idealsPrimeTo
      ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ :=
  MonoidHom.codRestrict ((toPrincipalIdeal (𝓞 K) K).comp (primeToSubgroup 𝔪).subtype) _
    fun x ↦ χ.toPrincipalIdeal_mem_idealsPrimeTo x.2

/-- **The finite character on the elements prime to the modulus**: for `x ∈ Kˣ` a unit at every
prime dividing `𝔪`, the ideal character of the presented Hecke character at `(x)` times the full
archimedean value of `x`. On algebraic integers it is the finite character
(`coe_finiteCharacterK_of_algebraMap_eq`), and it is trivial on the elements reducing to one modulo
the finite part of `𝔪` (`finiteCharacterK_eq_one_of_residueHom_eq_one`). -/
def finiteCharacterK (χ : Grossencharacter K 𝔪) : primeToSubgroup 𝔪 →* ℂˣ :=
  χ.toHeckeCharacter.idealCharacter.comp χ.principalIdeal *
    χ.archimedeanValue.comp (primeToSubgroup 𝔪).subtype

/-- The extended finite character at `x` is the ideal character at `(x)` times the full
archimedean value of `x`. -/
theorem finiteCharacterK_apply (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.finiteCharacterK x = χ.toHeckeCharacter.idealCharacter
        ⟨toPrincipalIdeal (𝓞 K) K x, χ.toPrincipalIdeal_mem_idealsPrimeTo x.2⟩ *
      χ.archimedeanValue x :=
  (rfl)

/-- **The extended finite character restricts to the finite character** on algebraic integers. -/
theorem coe_finiteCharacterK_of_algebraMap_eq (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪)
    (a : 𝓞 K) (ha : algebraMap (𝓞 K) K a = ((x : Kˣ) : K)) :
    (χ.finiteCharacterK x : ℂ) = χ.finiteCharacter a := by
  rw [finiteCharacterK_apply, Units.val_mul, χ.coe_idealCharacter_toPrincipalIdeal _ x.2 a ha,
    χ.finiteCharacter_apply _ a ha]

/-- **The extended finite character only sees the residue modulo the finite part.** An element
reducing to one modulo the finite part of `𝔪` is congruent to one modulo the finite conductor of the
presented character, so its principal idele is trivial and its ideal character is the inverse of
its archimedean components (`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal`). No positivity
is needed: the full archimedean value records the signs. -/
theorem finiteCharacterK_eq_one_of_residueHom_eq_one (χ : Grossencharacter K 𝔪)
    {x : primeToSubgroup 𝔪} (hx : residueHom 𝔪 x = 1) : χ.finiteCharacterK x = 1 := by
  -- `x` is congruent to one modulo the finite part of `𝔪`, so modulo the finite conductor.
  set 𝔪₀ : Modulus K := ⟨𝔪.finitePart, 𝔪.finitePart_ne_bot, ∅⟩
  set 𝔣 : Modulus K :=
    ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩
  have h₀ : IsCongrOne 𝔪₀ (x : Kˣ) :=
    (isCongrOne_iff_residueHom_eq_one_of_finitePart_eq (𝔪 := 𝔪₀) (𝔫 := 𝔪) rfl x.2).mpr
      ⟨hx, by simp [𝔪₀]⟩
  have h𝔣 : IsCongrOne 𝔣 (x : Kˣ) := IsCongrOne.mono (𝔫 := 𝔪₀)
    (Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, Finset.empty_subset _⟩) h₀
  rw [finiteCharacterK_apply, χ.toHeckeCharacter.idealCharacter_apply_toPrincipalIdeal _ h𝔣,
    archimedeanValue_eq_prod_infiniteComponent, inv_mul_cancel]

/-! ### The residue character -/

/-- **The residue character** of a presentation: the multiplicative character of `𝓞 K ⧸ 𝔪₀`, for
`𝔪₀` the finite part of `𝔪`, through which the extended finite character factors along the
reduction `residueHom 𝔪`. At a nonzero algebraic integer it is the finite character
(`residueCharacter_mk`), and it is the unique such character (`existsUnique_residueCharacter`).
Unlike the finite character it need not vanish at `0`: when `𝔪₀ = 𝓞 K`, the class of `0` is the
unit `1` (`residueCharacter_of_finitePart_eq_top`). -/
def residueCharacter (χ : Grossencharacter K 𝔪) : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ :=
  MulChar.ofUnitHom <| (residueHom 𝔪).liftOfSurjective (residueHom_surjective 𝔪)
    ⟨χ.finiteCharacterK, fun _ hx ↦ χ.finiteCharacterK_eq_one_of_residueHom_eq_one hx⟩

/-- The residue character at the reduction of `x` is the extended finite character at `x`. -/
theorem residueCharacter_residueHom (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.residueCharacter (residueHom 𝔪 x : 𝓞 K ⧸ 𝔪.finitePart) = χ.finiteCharacterK x := by
  rw [residueCharacter, MulChar.ofUnitHom_coe, MonoidHom.liftOfRightInverse_comp_apply]

/-- **On nonzero algebraic integers, the finite character is the residue character** of the residue
class modulo the finite part of `𝔪`. -/
theorem residueCharacter_mk (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha : a ≠ 0) :
    χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a := by
  set x := Units.mk0 _ (RingOfIntegers.coe_ne_zero_iff.mpr ha)
  by_cases hc : 𝔪.IsCoprimeTo (Ideal.span {a})
  · have hx : x ∈ primeToSubgroup 𝔪 := (Modulus.isCoprimeTo_span_singleton_iff rfl).mp hc
    have hres : (residueHom 𝔪 ⟨x, hx⟩ : 𝓞 K ⧸ 𝔪.finitePart) = Ideal.Quotient.mk _ a := by
      rw [coe_residueHom]
      exact residue_eq _ (b := 1) (by simp) (by simp [x])
    rw [← hres, residueCharacter_residueHom, χ.coe_finiteCharacterK_of_algebraMap_eq _ a rfl]
  · -- Off the elements prime to `𝔪`, both vanish: `a` is not a unit modulo the finite part.
    rw [(χ.finiteCharacter_eq_zero_iff).mpr hc]
    refine MulChar.map_nonunit _ fun hu ↦ hc ?_
    exact Modulus.isCoprimeTo_iff_sup_eq_top.mpr
      ⟨by simpa using ha, Ideal.Quotient.isUnit_mk_iff.mp hu⟩

/-- **The finite character depends only on the residue class** of a nonzero algebraic integer
modulo the finite part of `𝔪`. -/
theorem finiteCharacter_eq_of_sub_mem (χ : Grossencharacter K 𝔪) {a b : 𝓞 K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a - b ∈ 𝔪.finitePart) : χ.finiteCharacter a = χ.finiteCharacter b := by
  rw [← χ.residueCharacter_mk ha, ← χ.residueCharacter_mk hb, Ideal.Quotient.eq.mpr hab]

/-- **The residue character is unique**: it is the only multiplicative character of
`𝓞 K ⧸ 𝔪₀` agreeing with the finite character at every nonzero algebraic integer. -/
theorem existsUnique_residueCharacter (χ : Grossencharacter K 𝔪) :
    ∃! ψ : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ,
      ∀ a : 𝓞 K, a ≠ 0 → ψ (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a := by
  refine ⟨χ.residueCharacter, fun a ha ↦ χ.residueCharacter_mk ha, fun ψ hψ ↦ ?_⟩
  refine MulChar.ext fun u ↦ ?_
  -- Every residue class, in particular every unit, has a nonzero representative.
  obtain ⟨a, ha, hau⟩ := Ideal.Quotient.exists_ne_zero_mk_eq 𝔪.finitePart_ne_bot (u : 𝓞 K ⧸ _)
  rw [← hau, hψ a ha, χ.residueCharacter_mk ha]

/-- **At finite part `𝓞 K` the residue character is trivial**: the residue ring has a single
element, the unit `1`. The finite character is nevertheless `0` at `0`. -/
theorem residueCharacter_of_finitePart_eq_top (χ : Grossencharacter K 𝔪)
    (h : 𝔪.finitePart = ⊤) : χ.residueCharacter = 1 := by
  have : Subsingleton (𝓞 K ⧸ 𝔪.finitePart) := Ideal.Quotient.subsingleton_iff.mpr h
  refine MulChar.ext fun u ↦ ?_
  rw [Subsingleton.elim (u : 𝓞 K ⧸ 𝔪.finitePart) 1, MulChar.map_one, MulChar.map_one]

end Grossencharacter

end TauCeti.LFunctions
