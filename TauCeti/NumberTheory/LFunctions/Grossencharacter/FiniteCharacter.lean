/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue

/-!
# The finite character of a presentation

Let `χ` be a presentation at the modulus `𝔪` of an algebraic Hecke character, with unitary weight
`χ_u`, ideal-side shift `σ` and algebraic infinity type `n`. Hecke's twisted theta series and the
Gauss sums of `χ` do not evaluate the ideal values `χ_u((a)) N(a) ^ σ` directly: they evaluate the
**finite character** `χ_f`, the ideal value corrected by the whole archimedean character,

`χ_f(a) = χ_u((a)) * N(a) ^ σ * χ_∞(a)`  (Neukirch VII (6.1)).

Here `χ_∞(a)` is the **archimedean value** `Grossencharacter.archimedeanValue`: the product of the
components of the presented Hecke character at the infinite places, evaluated at `a`. It is the
monomial `∏_τ τ(a) ^ (n τ)` of the infinity type when `a` is positive at the real places of `𝔪`
(`Grossencharacter.archimedeanValue_eq_embeddingCharacter`), and differs from it by a sign at a
real place of `𝔪` where the parity of the Hecke character differs from that of `n`. With the
monomial alone, the odd character modulo `4∞` of `ℚ`, of exponent `0`, would get the even finite
character.

The point of the correction is that `χ_f` only sees residues modulo the finite part `𝔪₀` of `𝔪`.
On the fractions prime to `𝔪₀` (the subgroup `primeToSubgroup 𝔪` of `Kˣ`), the finite character
`Grossencharacter.finiteCharacterK` is the ideal character of the presented Hecke character at
`(x)` times `χ_∞(x)`. By Hecke's unit relation it is trivial on every `x ≡ 1 mod 𝔪₀`, whatever
the signs of `x` at the real places, so it factors through the reduction to `(𝓞 K ⧸ 𝔪₀)ˣ`. The
factor is the **residue character** `Grossencharacter.residueCharacter`, a Mathlib `MulChar` of
`𝓞 K ⧸ 𝔪₀`. On algebraic integers, `Grossencharacter.finiteCharacter` is the coefficient that the
twisted theta series attaches to a lattice point: it is `0` exactly at the integers not prime to
`𝔪` (`0` included), and the residue character at the class of every nonzero integer
(`Grossencharacter.finiteCharacter_eq_residueCharacter`), which pins the residue character down
(`Grossencharacter.existsUnique_residueCharacter`).

The coefficient and the residue character must be kept apart at `0`. When `𝔪₀ = 𝓞 K`, the residue
ring has one element, a unit, at which the residue character is `1`, while the coefficient at the
integer `0` is `0`. Accordingly the comparison is stated for nonzero integers only.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue`: the archimedean value `χ_∞` on `Kˣ`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK`: the finite character on the fractions
  prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter`: the induced character of `𝓞 K ⧸ 𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter`: the finite character on `𝓞 K`.

## Main results

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

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.1) and (6.13).
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
    (hx : ∀ w ∈ 𝔪.infinitePart, 0 < InfinitePlace.embedding_of_isReal w.2 (x : K)) :
    χ.archimedeanValue x = χ.infinityType.embeddingCharacter x := by
  refine Units.ext ?_
  rw [archimedeanValue_apply, Units.coe_prod]
  exact χ.toHeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity
    χ.infinityType χ.agreesOnIdentityComponent x
    fun w hw ↦ hx w (not_imp_comm.mp (χ.realParity_eq w) hw)

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
    (isCongrOne_iff_residueHom_eq_one_of_finitePart_eq (𝔪 := 𝔪₀) (𝔫 := 𝔪) rfl x.2).mpr
      ⟨hx, by simp [𝔪₀]⟩
  have hx𝔣 : IsCongrOne
      ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ (x : Kˣ) :=
    IsCongrOne.mono (𝔫 := 𝔪₀)
      (Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, Finset.empty_subset _⟩) hx₀
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
      χ.unitaryWeight.1 (Ideal.span {a}) *
        ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
          (χ.archimedeanValue x : ℂ) := by
  have hspan : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ((toPrincipalIdeal (𝓞 K) K (x : Kˣ) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, ha]
  -- The ideal `(a)` is prime to `𝔪`, since `x` is a unit at the primes dividing `𝔪`.
  have hmem : Ideal.span {a} ∈ integralIdealsPrimeTo 𝔪 := by
    refine (NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero (K := K)).mpr
      ⟨?_, fun v hv ↦ ?_⟩
    · rw [Ne, Ideal.span_singleton_eq_bot]
      rintro rfl
      exact (x : Kˣ).ne_zero (by rw [← ha, map_zero])
    · rw [hspan]
      exact NumberFieldArithmetic.mem_idealsAway_iff.mp
        (NumberFieldArithmetic.toPrincipalIdeal_mem_idealsAway_iff.mpr x.2) v hv
  have hideal : NumberFieldArithmetic.integralIdealsAwayHom K _
        (integralIdealsPrimeToInclusion χ.mk_finiteConductor_dvd ⟨_, hmem⟩) =
      NumberFieldArithmetic.idealsAwayInclusion K
        (Modulus.support_mono χ.mk_finiteConductor_dvd)
        (NumberFieldArithmetic.principalIdealAway K 𝔪.support x) :=
    Subtype.ext (Units.ext (by
      rw [NumberFieldArithmetic.coe_integralIdealsAwayHom, coe_integralIdealsPrimeToInclusion,
        NumberFieldArithmetic.coe_idealsAwayInclusion,
        NumberFieldArithmetic.coe_principalIdealAway, hspan]))
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

/-- The image in `Kˣ` of a nonzero algebraic integer. -/
private def unitOfNeZero {a : 𝓞 K} (ha : a ≠ 0) : Kˣ :=
  Units.mk0 (algebraMap (𝓞 K) K a)
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr ha)

open scoped Classical in
/-- **Hecke's finite character** of a presentation on the algebraic integers:
`χ_f(a) = χ_u((a)) N(a) ^ σ χ_∞(a)` at `a ≠ 0`, and `0` at `a = 0`. It is the coefficient of the
twisted theta series: it vanishes exactly at the integers not prime to `𝔪`
(`finiteCharacter_eq_zero_iff`), and at a nonzero integer it is the residue character at its
class modulo `𝔪₀` (`finiteCharacter_eq_residueCharacter`). -/
def finiteCharacter (χ : Grossencharacter K 𝔪) : 𝓞 K →*₀ ℂ where
  toFun a := if ha : a = 0 then 0 else
    χ.unitaryWeight.1 (Ideal.span {a}) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
        (χ.archimedeanValue (unitOfNeZero ha) : ℂ)
  map_zero' := by simp
  map_one' := by
    have h1 : unitOfNeZero (one_ne_zero (α := 𝓞 K)) = 1 := Units.ext (map_one _)
    simp [h1]
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    have hab : unitOfNeZero (mul_ne_zero ha hb) = unitOfNeZero ha * unitOfNeZero hb :=
      Units.ext (map_mul _ _ _)
    simp only [ha, hb, mul_ne_zero ha hb, ↓reduceDIte, hab, map_mul, Units.val_mul,
      ← Ideal.span_singleton_mul_span_singleton, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring

/-- The defining formula of the finite character at a nonzero algebraic integer. -/
theorem finiteCharacter_apply_of_ne_zero (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha : a ≠ 0)
    {x : Kˣ} (hx : (x : K) = algebraMap (𝓞 K) K a) :
    χ.finiteCharacter a = χ.unitaryWeight.1 (Ideal.span {a}) *
      ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
        (χ.archimedeanValue x : ℂ) := by
  have : x = unitOfNeZero ha := Units.ext hx
  subst this
  simp [finiteCharacter, ha]

/-- **The finite character vanishes at the integers not prime to `𝔪`**, `0` included. -/
theorem finiteCharacter_eq_zero_of_not_isCoprimeTo (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (ha : ¬ 𝔪.IsCoprimeTo (Ideal.span {a})) : χ.finiteCharacter a = 0 := by
  by_cases ha₀ : a = 0
  · rw [ha₀, map_zero]
  · rw [χ.finiteCharacter_apply_of_ne_zero ha₀ (x := unitOfNeZero ha₀) rfl,
      χ.unitaryWeight_eq_zero _ ha, zero_mul, zero_mul]

/-- **At an integer prime to `𝔪`, the finite character is `finiteCharacterK`.** -/
theorem finiteCharacter_eq_finiteCharacterK (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (x : primeToSubgroup 𝔪) (ha : algebraMap (𝓞 K) K a = ((x : Kˣ) : K)) :
    χ.finiteCharacter a = χ.finiteCharacterK x := by
  have ha₀ : a ≠ 0 := by
    rintro rfl
    exact (x : Kˣ).ne_zero (by rw [← ha, map_zero])
  rw [χ.coe_finiteCharacterK_of_algebraMap_eq x ha, χ.finiteCharacter_apply_of_ne_zero ha₀ ha.symm]

/-- An integer `a` prime to `𝔪` is a unit at the primes dividing `𝔪`. -/
private theorem exists_primeToSubgroup_of_isCoprimeTo {a : 𝓞 K}
    (ha : 𝔪.IsCoprimeTo (Ideal.span {a})) :
    ∃ x : primeToSubgroup 𝔪, ((x : Kˣ) : K) = algebraMap (𝓞 K) K a := by
  have ha₀ : a ≠ 0 := by
    rintro rfl
    exact (Modulus.isCoprimeTo_iff.mp ha).1 (Ideal.span_singleton_eq_bot.mpr rfl)
  refine ⟨⟨unitOfNeZero ha₀, ?_⟩, rfl⟩
  rw [← NumberFieldArithmetic.toPrincipalIdeal_mem_idealsAway_iff,
    NumberFieldArithmetic.mem_idealsAway_iff]
  intro v hv
  have hspan : ((toPrincipalIdeal (𝓞 K) K (unitOfNeZero ha₀) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, unitOfNeZero, Units.val_mk0]
  rw [hspan]
  exact (NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero (K := K)).mp
    (Modulus.mem_integralIdealsPrimeTo.mpr ha) |>.2 v hv

/-- **The finite character vanishes exactly at the integers not prime to `𝔪`.** -/
theorem finiteCharacter_eq_zero_iff (χ : Grossencharacter K 𝔪) {a : 𝓞 K} :
    χ.finiteCharacter a = 0 ↔ ¬ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  refine ⟨fun h ha ↦ ?_, χ.finiteCharacter_eq_zero_of_not_isCoprimeTo⟩
  obtain ⟨x, hx⟩ := exists_primeToSubgroup_of_isCoprimeTo ha
  rw [χ.finiteCharacter_eq_finiteCharacterK x hx.symm] at h
  exact (χ.finiteCharacterK x).ne_zero h

/-- **On nonzero integers, the finite character is the residue character** at the class modulo
`𝔪₀`. At an integer not prime to `𝔪` both vanish, the class not being a unit. The integer `0` is
excluded: when `𝔪₀ = 𝓞 K` its class is the unit of the zero ring. -/
theorem finiteCharacter_eq_residueCharacter (χ : Grossencharacter K 𝔪) {a : 𝓞 K} (ha : a ≠ 0) :
    χ.finiteCharacter a = χ.residueCharacter (Ideal.Quotient.mk 𝔪.finitePart a) := by
  by_cases hcop : 𝔪.IsCoprimeTo (Ideal.span {a})
  · obtain ⟨x, hx⟩ := exists_primeToSubgroup_of_isCoprimeTo hcop
    rw [χ.finiteCharacter_eq_finiteCharacterK x hx.symm, ← residueCharacter_residue,
      residue_eq x (a := a) (b := 1) (by simp) (by rw [map_one, one_mul, hx])]
  · rw [χ.finiteCharacter_eq_zero_of_not_isCoprimeTo hcop, MulChar.map_nonunit]
    -- A unit modulo `𝔪₀` stays a unit modulo every prime `v` dividing `𝔪₀`, so `a ∉ v`.
    intro hu
    refine hcop (Modulus.isCoprimeTo_iff.mpr ⟨by simpa using ha, fun v hv hva ↦ ?_⟩)
    have hv := (hu.map (Ideal.Quotient.factor
      (Ideal.le_of_dvd ((𝔪.mem_support_iff v).mp hv)))).ne_zero
    rw [Ideal.Quotient.factor_mk, Ne, Ideal.Quotient.eq_zero_iff_mem] at hv
    exact hv (Ideal.dvd_span_singleton.mp hva)

/-- **The finite character only sees residues modulo `𝔪₀`**: nonzero integers congruent modulo
the finite part of `𝔪` have the same finite character. -/
theorem finiteCharacter_eq_of_sub_mem (χ : Grossencharacter K 𝔪) {a b : 𝓞 K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a - b ∈ 𝔪.finitePart) : χ.finiteCharacter a = χ.finiteCharacter b := by
  rw [χ.finiteCharacter_eq_residueCharacter ha, χ.finiteCharacter_eq_residueCharacter hb,
    Ideal.Quotient.eq.mpr hab]

/-- **The residue character is determined by the finite character**: it is the unique character
of `𝓞 K ⧸ 𝔪₀` whose value at the class of every nonzero integer `a` is `χ_f(a)`. Every class has a
nonzero representative, since `𝔪₀ ≠ 0`. -/
theorem existsUnique_residueCharacter (χ : Grossencharacter K 𝔪) :
    ∃! ψ : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ,
      ∀ a : 𝓞 K, a ≠ 0 → ψ (Ideal.Quotient.mk 𝔪.finitePart a) = χ.finiteCharacter a := by
  refine ⟨χ.residueCharacter, fun a ha ↦ (χ.finiteCharacter_eq_residueCharacter ha).symm,
    fun ψ hψ ↦ MulChar.ext' fun r ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  -- Replace `a` by a nonzero representative of its class.
  obtain ⟨c, hc, hc₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot 𝔪.finitePart_ne_bot
  obtain ⟨b, hb₀, hb⟩ : ∃ b : 𝓞 K, b ≠ 0 ∧ Ideal.Quotient.mk 𝔪.finitePart b =
      Ideal.Quotient.mk 𝔪.finitePart a := by
    by_cases ha : a = 0
    · exact ⟨c, hc₀, by rw [ha, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hc⟩
    · exact ⟨a, ha, rfl⟩
  rw [← hb, hψ b hb₀, χ.finiteCharacter_eq_residueCharacter hb₀]

end Grossencharacter

end TauCeti.LFunctions
