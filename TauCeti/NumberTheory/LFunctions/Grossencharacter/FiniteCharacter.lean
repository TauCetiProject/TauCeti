/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Lemmas
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.ArchimedeanValue
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue

import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.NumberTheory.MulChar.Real
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

The point of the correction is that on `primeToSubgroup 𝔪` and on **nonzero** algebraic integers,
`χ_f` only depends on the residue class modulo the finite part `𝔪₀` of `𝔪`. On the fractions prime
to `𝔪₀` (the subgroup `primeToSubgroup 𝔪` of `Kˣ`), the finite character
`Grossencharacter.finiteCharacterK` is the ideal character of the presented Hecke character at
`(x)` times `χ_∞(x)`. An `x ≡ 1 mod 𝔪₀` is congruent to `1` modulo the finite conductor, where
the ideal character at `(x)` is `χ_∞(x)⁻¹` because the Hecke character is trivial on the principal
idele of `x` (`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal`). So the finite character is
trivial on every `x ≡ 1 mod 𝔪₀`, whatever the signs of `x` at the real places, and it factors
through the reduction to `(𝓞 K ⧸ 𝔪₀)ˣ`. The factor is the **residue character**
`Grossencharacter.residueCharacter`, a Mathlib `MulChar` of `𝓞 K ⧸ 𝔪₀`, which captures the finite
conductor of `χ.toHeckeCharacter` (`finiteConductor_dvd_iff_residueCharacter_eq_one`) and is
primitive when `𝔪₀ = 𝔣(χ)` (`exists_residueCharacter_ne_one_of_finiteConductor_eq`). On algebraic
integers, `Grossencharacter.finiteCharacter` is the coefficient that the twisted theta series
attaches to a lattice point: it is `0` exactly at the integers not prime to `𝔪` (`0` included),
and the residue character at the class of every nonzero integer
(`Grossencharacter.finiteCharacter_eq_residueCharacter`), which pins the residue character down
(`Grossencharacter.existsUnique_residueCharacter`). Separately,
`Grossencharacter.finiteCharacterField` is the coefficient function `K → ℂ` extending
`Grossencharacter.finiteCharacterK` by `0` outside `primeToSubgroup 𝔪` (and at `0`), restricting to
`Grossencharacter.finiteCharacter` on `𝓞 K`.

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

* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK`: the finite character on the fractions
  prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter`: the induced character of `𝓞 K ⧸ 𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter`: the finite character on `𝓞 K`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterField`: the coefficient function `K → ℂ`
  extending `finiteCharacterK` by `0` off `primeToSubgroup 𝔪` and restricting to `finiteCharacter`
  on `𝓞 K`.

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
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_zero_iff` and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_ne_zero_iff`: it vanishes exactly at the
  integers not prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_one_of_mk_eq_one`: it is `1` on the
  nonzero integers congruent to one modulo `𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_unit`: on a unit it is the archimedean
  value.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK_eq_prod_finiteComponent_inv` and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_prod_finiteComponent_inv`: the finite
  character is the inverse of the product of the components at the primes of the finite conductor.
* `TauCeti.LFunctions.Grossencharacter.finiteConductor_dvd_iff_residueCharacter_eq_one` and
  `TauCeti.LFunctions.Grossencharacter.exists_residueCharacter_ne_one_of_finiteConductor_eq`:
  finite-conductor characterization and primitivity of `residueCharacter`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.1) and (6.13).
* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels and
  A. Fröhlich, eds., *Algebraic Number Theory*, §3.1.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
  NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

namespace Grossencharacter

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

/-- The finite character at a fraction prime to `𝔪`, through the ideal character of the presented
Hecke character at the principal ideal it generates. -/
private theorem exists_finiteCharacterK_eq_idealCharacter (χ : Grossencharacter K 𝔪)
    (x : primeToSubgroup 𝔪) :
    ∃ hx : toPrincipalIdeal (𝓞 K) K (x : Kˣ) ∈
        idealsPrimeTo ⟨χ.toHeckeCharacter.finiteConductor,
          χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩,
      χ.finiteCharacterK x = χ.toHeckeCharacter.idealCharacter ⟨_, hx⟩ *
        ∏ w : InfinitePlace K, χ.toHeckeCharacter.infiniteComponent w
          (Units.map (algebraMap K w.Completion).toMonoidHom x) := by
  have hx : toPrincipalIdeal (𝓞 K) K (x : Kˣ) ∈ idealsPrimeTo
      ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ :=
    NumberFieldArithmetic.toPrincipalIdeal_mem_idealsAway_iff.mpr
      (primeToSubgroup_le_of_dvd χ.finiteConductor_dvd_finitePart x.property)
  refine ⟨hx, ?_⟩
  rw [finiteCharacterK_apply,
    NumberFieldArithmetic.idealsAwayInclusion_principalIdealAway
      (Modulus.support_mono χ.mk_finiteConductor_dvd) x hx,
    archimedeanValue_apply]

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
  obtain ⟨hx, h⟩ := χ.exists_finiteCharacterK_eq_idealCharacter x
  rw [h, HeckeCharacter.idealCharacter_apply_toPrincipalIdeal_eq_prod_inv_mul_prod_inv,
    mul_right_comm, inv_mul_cancel, one_mul]

/-- **The finite character depends only on the Hecke character**: two presentations of the same
Hecke character agree at every fraction prime to both moduli. -/
theorem finiteCharacterK_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (x : primeToSubgroup 𝔪) (hx : (x : Kˣ) ∈ primeToSubgroup 𝔫) :
    χ.finiteCharacterK x = ψ.finiteCharacterK ⟨x, hx⟩ := by
  obtain ⟨h₁, e₁⟩ := χ.exists_finiteCharacterK_eq_idealCharacter x
  obtain ⟨h₂, e₂⟩ := ψ.exists_finiteCharacterK_eq_idealCharacter ⟨x, hx⟩
  rw [e₁, e₂]
  -- the membership proof `h₁` mentions the finite conductor of `χ.toHeckeCharacter`, so the
  -- Hecke character is generalized before it is substituted along `h`
  generalize χ.toHeckeCharacter = H at h h₁ ⊢
  subst h
  rfl

/-- **The finite character is trivial on the fractions congruent to `1` modulo `𝔪₀`**, with no
condition at the real places. Such an `x` is congruent to `1` modulo the finite conductor, where
the ideal character of `(x)` is the inverse of `χ_∞(x)`
(`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal`). -/
theorem finiteCharacterK_eq_one_of_residueHom_eq_one (χ : Grossencharacter K 𝔪)
    {x : primeToSubgroup 𝔪} (hx : residueHom 𝔪 x = 1) : χ.finiteCharacterK x = 1 := by
  set 𝔪₀ : Modulus K := ⟨𝔪.finitePart, 𝔪.finitePart_ne_bot, ∅⟩
  have hx₀ : IsCongrOne 𝔪₀ (x : Kˣ) :=
    (isCongrOne_iff_residueHom_eq_one_of_finitePart_eq (𝔪 := 𝔪₀) (𝔫 := 𝔪) rfl x.property).mpr
      ⟨hx, by simp [𝔪₀]⟩
  have hx𝔣 : IsCongrOne
      ⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ (x : Kˣ) :=
    hx₀.mono χ.mk_finiteConductor_dvd_mk_finitePart
  rw [finiteCharacterK_apply,
    NumberFieldArithmetic.idealsAwayInclusion_principalIdealAway
      (Modulus.support_mono χ.mk_finiteConductor_dvd) x hx𝔣.toPrincipalIdeal_mem_idealsPrimeTo,
    χ.toHeckeCharacter.idealCharacter_apply_toPrincipalIdeal (x : Kˣ) hx𝔣,
    archimedeanValue_apply, inv_mul_cancel]

/-- On any element of `primeToSubgroup 𝔪` congruent to `1` modulo `𝔪`, `finiteCharacterK` takes
the value `1`. -/
theorem finiteCharacterK_eq_one_of_isCongrOne (χ : Grossencharacter K 𝔪) {x : primeToSubgroup 𝔪}
    (hx : IsCongrOne 𝔪 (x : Kˣ)) : χ.finiteCharacterK x = 1 :=
  χ.finiteCharacterK_eq_one_of_residueHom_eq_one
    (residueHom_eq_one_of_mem_congruenceSubgroup (mem_congruenceSubgroup.mpr hx))

/-- **At a trivial finite modulus the finite character is trivial**: the residue ring modulo
`𝓞 K` has a single element. -/
theorem finiteCharacterK_eq_one_of_finitePart_eq_top (χ : Grossencharacter K 𝔪)
    (h : 𝔪.finitePart = ⊤) (x : primeToSubgroup 𝔪) : χ.finiteCharacterK x = 1 := by
  have : Subsingleton (𝓞 K ⧸ 𝔪.finitePart) := Ideal.Quotient.subsingleton_iff.mpr h
  exact χ.finiteCharacterK_eq_one_of_residueHom_eq_one (Subsingleton.elim _ _)

/-- Inversion of a presentation inverts `finiteCharacterK`. -/
@[simp]
theorem finiteCharacterK_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.finiteCharacterK = χ.finiteCharacterK⁻¹ := by
  refine MonoidHom.ext fun x ↦ ?_
  rw [MonoidHom.inv_apply, finiteCharacterK_eq_prod_finiteComponent_inv,
    finiteCharacterK_eq_prod_finiteComponent_inv, inv_inj, ← Finset.prod_inv_distrib]
  have hsup : (⟨χ.inverse.toHeckeCharacter.finiteConductor,
      χ.inverse.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ : Modulus K).support =
      (⟨χ.toHeckeCharacter.finiteConductor,
      χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ : Modulus K).support := by
    ext v
    simp [Modulus.mem_support_iff]
  rw [hsup]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [toHeckeCharacter_inverse, HeckeCharacter.finiteComponent_inv_apply]

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

private def residueUnitHom (χ : Grossencharacter K 𝔪) : (𝓞 K ⧸ 𝔪.finitePart)ˣ →* ℂˣ :=
  (residueHom 𝔪).liftOfSurjective (residueHom_surjective 𝔪)
    ⟨χ.finiteCharacterK, fun _ hx ↦ χ.finiteCharacterK_eq_one_of_residueHom_eq_one hx⟩

private theorem residueUnitHom_residueHom (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.residueUnitHom (residueHom 𝔪 x) = χ.finiteCharacterK x :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- **The residue character** of a presentation: the character of `𝓞 K ⧸ 𝔪₀` through which the
finite character factors (`residueCharacter_residue`). It is `0` at the non-units of the residue
ring, and it is the unique such character with the value of `finiteCharacter` at the class of
every nonzero integer (`existsUnique_residueCharacter`). -/
def residueCharacter (χ : Grossencharacter K 𝔪) : MulChar (𝓞 K ⧸ 𝔪.finitePart) ℂ :=
  MulChar.ofUnitHom χ.residueUnitHom

/-- **The residue character at the reduction of `x` is the finite character at `x`.** -/
@[simp]
theorem residueCharacter_residue (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.residueCharacter (residue 𝔪 x) = χ.finiteCharacterK x := by
  rw [← coe_residueHom, residueCharacter, MulChar.ofUnitHom_coe, residueUnitHom_residueHom]

/-- Every value of the residue character on a unit of `𝓞 K ⧸ 𝔪.finitePart` has absolute
value `1`. -/
theorem norm_residueCharacter_unit (χ : Grossencharacter K 𝔪)
    (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ) : ‖χ.residueCharacter u‖ = 1 := by
  have : Finite (𝓞 K ⧸ 𝔪.finitePart) :=
    Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  exact χ.residueCharacter.norm_apply_unit u

/-- **The finite character takes values of norm `1`**: it factors through the finite group of
residue units modulo `𝔪₀` (`residueCharacter_residue`), so its values are roots of unity. -/
theorem norm_finiteCharacterK (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    ‖(χ.finiteCharacterK x : ℂ)‖ = 1 := by
  have : Finite (𝓞 K ⧸ 𝔪.finitePart) :=
    Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  have := Fintype.ofFinite (𝓞 K ⧸ 𝔪.finitePart)ˣ
  rw [← residueCharacter_residue, ← coe_residueHom, ← MulChar.coe_equivToUnitHom]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (MulChar.apply_mem_rootsOfUnity _)

/-- Inversion conjugates `finiteCharacterK` as a complex value. -/
theorem coe_finiteCharacterK_inverse (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    (χ.inverse.finiteCharacterK x : ℂ) = starRingEnd ℂ (χ.finiteCharacterK x : ℂ) := by
  rw [finiteCharacterK_inverse, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj (χ.norm_finiteCharacterK x)

/-- Inversion conjugates the residue character. -/
@[simp]
theorem residueCharacter_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.residueCharacter = star χ.residueCharacter := by
  refine MulChar.ext fun u ↦ ?_
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔪 u
  rw [coe_residueHom, χ.inverse.residueCharacter_residue x, MulChar.star_apply,
    χ.residueCharacter_residue x, Complex.star_def, coe_finiteCharacterK_inverse]

/-- **At finite part `𝓞 K` the residue character is trivial**: the residue ring has a single
element, the unit `1`. The finite character is nevertheless `0` at `0`. -/
theorem residueCharacter_eq_one_of_finitePart_eq_top (χ : Grossencharacter K 𝔪)
    (h : 𝔪.finitePart = ⊤) : χ.residueCharacter = 1 := by
  have : Subsingleton (𝓞 K ⧸ 𝔪.finitePart) := Ideal.Quotient.subsingleton_iff.mpr h
  refine MulChar.ext fun u ↦ ?_
  rw [Subsingleton.elim (u : 𝓞 K ⧸ 𝔪.finitePart) 1, MulChar.map_one, MulChar.map_one]

/-- Two presentations of the same Hecke character at moduli with `𝔪.finitePart ∣ 𝔫.finitePart`
have compatible residue characters along `finiteUnitsMap`. -/
theorem residueCharacter_eq_residueCharacter_finiteUnitsMap
    {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (hdvd : 𝔪.finitePart ∣ 𝔫.finitePart) (u : (𝓞 K ⧸ 𝔫.finitePart)ˣ) :
    ψ.residueCharacter u = χ.residueCharacter (finiteUnitsMap hdvd u) := by
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔫 u
  rw [finiteUnitsMap_residueHom, coe_residueHom, coe_residueHom, ψ.residueCharacter_residue x,
    χ.residueCharacter_residue (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x)]
  exact congrArg Units.val (finiteCharacterK_congr h.symm _ _)

/-! ### The finite character on algebraic integers -/

/-- **Hecke's finite character** of a presentation on the algebraic integers:
`χ_f(a) = χ_u((a)) N(a) ^ σ χ_∞(a)` at `a ≠ 0`, and `0` at `a = 0`. In this formula, the norm
twist of the unitary weight at `(a)` is multiplied by the archimedean value `χ.archimedeanValue`
extended from `Kˣ` to `K` by `0` at `0` (via `MulChar.ofUnitHom`) and evaluated at `a`. It is the
coefficient of the twisted theta series: it vanishes exactly at the integers not prime to `𝔪`
(`finiteCharacter_eq_zero_iff`), and at a nonzero integer it is the residue character at its class
modulo `𝔪₀` (`finiteCharacter_eq_residueCharacter`). -/
def finiteCharacter (χ : Grossencharacter K 𝔪) : 𝓞 K →*₀ ℂ :=
  (MultiplicativeIdealWeight.normTwist (-(χ.idealShift : ℂ))
      χ.unitaryWeight.val).toMonoidWithZeroHom.comp (Submodule.spanSingleton (𝓞 K)) *
    (MulChar.ofUnitHom χ.archimedeanValue).toMonoidWithZeroHom.comp
      (algebraMap (𝓞 K) K : 𝓞 K →*₀ K)

/-- The finite character as the norm twist of the unitary weight at `(a)` times the archimedean
value (extended from `Kˣ` to `K` by `0` at `0`) evaluated at `a`. -/
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

/-- **Idelic formula for Hecke's finite character.** For `a ∈ 𝓞 K` generating an ideal prime to
`𝔪`, with image `x ∈ primeToSubgroup 𝔪`, `χ.finiteCharacter a` equals the inverse product of the
local finite components of `χ.toHeckeCharacter` at the primes dividing the finite conductor. -/
theorem finiteCharacter_eq_prod_finiteComponent_inv (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    {x : Kˣ} (ha : algebraMap (𝓞 K) K a = x) (hx : x ∈ primeToSubgroup 𝔪) :
    χ.finiteCharacter a =
      (∏ v ∈ (⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot,
          ∅⟩ : Modulus K).support,
        (χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom x) : ℂ))⁻¹ := by
  rw [χ.finiteCharacter_eq_finiteCharacterK ⟨x, hx⟩ ha,
    χ.finiteCharacterK_eq_prod_finiteComponent_inv ⟨x, hx⟩, Units.val_inv_eq_inv_val,
    Units.coe_prod]

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

/-- Hecke's finite character is nonzero at `a` if and only if `(a)` is coprime to `𝔪`. -/
theorem finiteCharacter_ne_zero_iff (χ : Grossencharacter K 𝔪) {a : 𝓞 K} :
    χ.finiteCharacter a ≠ 0 ↔ 𝔪.IsCoprimeTo (Ideal.span {a}) := by
  rw [ne_eq, χ.finiteCharacter_eq_zero_iff, not_not]

/-- On an integer congruent to `1` modulo `𝔪`, Hecke's finite character evaluates to `1`. -/
theorem finiteCharacter_eq_one_of_isCongrOne (χ : Grossencharacter K 𝔪) {a : 𝓞 K} {x : Kˣ}
    (ha : algebraMap (𝓞 K) K a = x) (hx : IsCongrOne 𝔪 x) : χ.finiteCharacter a = 1 := by
  have hxp : x ∈ primeToSubgroup 𝔪 :=
    congruenceSubgroup_le_primeToSubgroup 𝔪 (mem_congruenceSubgroup.mpr hx)
  rw [χ.finiteCharacter_eq_finiteCharacterK ⟨x, hxp⟩ ha,
    χ.finiteCharacterK_eq_one_of_isCongrOne hx, Units.val_one]

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
    exact fun hu ↦ hcop ((Modulus.isUnit_mk_iff_isCoprimeTo ha).mp hu)

/-- **On nonzero algebraic integers, the finite character only depends on residues modulo `𝔪₀`**:
nonzero integers congruent modulo the finite part of `𝔪` have the same finite character. -/
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

/-- Inversion conjugates Hecke's finite character on `𝓞 K`. -/
@[simp]
theorem finiteCharacter_inverse (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.inverse.finiteCharacter a = starRingEnd ℂ (χ.finiteCharacter a) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [χ.inverse.finiteCharacter_eq_residueCharacter ha, χ.residueCharacter_inverse,
      MulChar.star_apply, ← χ.finiteCharacter_eq_residueCharacter ha, starRingEnd_apply]

/-- Every value of Hecke's finite character on an integer coprime to `𝔪` has absolute value
`1`. -/
theorem norm_finiteCharacter_of_isCoprimeTo (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    (ha : 𝔪.IsCoprimeTo (Ideal.span {a})) : ‖χ.finiteCharacter a‖ = 1 := by
  obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp ha
  rw [χ.finiteCharacter_eq_finiteCharacterK x hx.symm]
  exact χ.norm_finiteCharacterK x

/-- Every value of Hecke's finite character has absolute value at most `1`. -/
theorem norm_finiteCharacter_le_one (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    ‖χ.finiteCharacter a‖ ≤ 1 := by
  by_cases ha : 𝔪.IsCoprimeTo (Ideal.span {a})
  · exact (χ.norm_finiteCharacter_of_isCoprimeTo ha).le
  · simp [χ.finiteCharacter_eq_zero_of_not_isCoprimeTo ha]

/-- Two presentations of the same Hecke character agree on every integer whose principal ideal
is coprime to both moduli. -/
theorem finiteCharacter_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) {a : 𝓞 K}
    (h𝔪 : 𝔪.IsCoprimeTo (Ideal.span {a})) (h𝔫 : 𝔫.IsCoprimeTo (Ideal.span {a})) :
    χ.finiteCharacter a = ψ.finiteCharacter a := by
  obtain ⟨x𝔪, hx𝔪⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp h𝔪
  obtain ⟨x𝔫, hx𝔫⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp h𝔫
  have hx : (x𝔪 : Kˣ) = (x𝔫 : Kˣ) := Units.ext (hx𝔪.trans hx𝔫.symm)
  rw [χ.finiteCharacter_eq_finiteCharacterK x𝔪 hx𝔪.symm,
    ψ.finiteCharacter_eq_finiteCharacterK x𝔫 hx𝔫.symm]
  exact congrArg Units.val (by
    simpa [hx] using χ.finiteCharacterK_congr h x𝔪 (hx ▸ x𝔫.property))

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

/-- **Existence and uniqueness of `finiteCharacterK`.** `χ.finiteCharacterK` is the unique group
homomorphism `primeToSubgroup 𝔪 →* ℂˣ` agreeing with `χ.finiteCharacter` on algebraic integers
prime to `𝔪`. -/
theorem existsUnique_finiteCharacterK (χ : Grossencharacter K 𝔪) :
    ∃! f : primeToSubgroup 𝔪 →* ℂˣ,
      ∀ (a : 𝓞 K) (x : primeToSubgroup 𝔪),
        algebraMap (𝓞 K) K a = ((x : Kˣ) : K) → (f x : ℂ) = χ.finiteCharacter a := by
  refine ⟨χ.finiteCharacterK,
    fun a x ha ↦ (χ.finiteCharacter_eq_finiteCharacterK x ha).symm,
    fun f hf ↦ MonoidHom.ext fun x ↦ Units.ext ?_⟩
  obtain ⟨a, b, xa, xb, ha, hb, hxeq⟩ := exists_primeToSubgroup_div_eq x
  have hxa : f xa = f xb * f x := by rw [hxeq, map_mul]
  have h1 : (f xb : ℂ) * (f x : ℂ) =
      (χ.finiteCharacterK xb : ℂ) * (χ.finiteCharacterK x : ℂ) := by
    rw [← Units.val_mul, ← hxa, hf a xa ha, χ.finiteCharacter_eq_finiteCharacterK xa ha, hxeq,
      map_mul, Units.val_mul]
  have hb_eq : (f xb : ℂ) = χ.finiteCharacterK xb :=
    (hf b xb hb).trans (χ.finiteCharacter_eq_finiteCharacterK xb hb)
  rw [hb_eq] at h1
  exact mul_left_cancel₀ (χ.finiteCharacterK xb).ne_zero h1

/-! ### The finite character on `K` -/

/-- **Hecke's finite character on `K`**: the finite character `finiteCharacterK` at the elements
of `K` that are units at the primes dividing `𝔪`, extended by `0` to every other element, `0`
included. It extends `finiteCharacter` from `𝓞 K` to `K` (`finiteCharacterField_algebraMap`), and
it is the coefficient of the twisted theta series of a fractional ideal. It is multiplicative
along the fractions prime to `𝔪` (`finiteCharacterField_coe_mul`), but not on all of `K`: a
uniformizer at a prime dividing `𝔪₀` and its inverse are both sent to `0`, their product to `1`. -/
def finiteCharacterField (χ : Grossencharacter K 𝔪) (x : K) : ℂ :=
  Function.extend (fun y : primeToSubgroup 𝔪 ↦ ((y : Kˣ) : K)) (fun y ↦ (χ.finiteCharacterK y : ℂ))
    0 x

/-- **At a fraction prime to `𝔪`, the finite character on `K` is `finiteCharacterK`.** -/
@[simp]
theorem finiteCharacterField_coe (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.finiteCharacterField ((x : Kˣ) : K) = χ.finiteCharacterK x :=
  Function.Injective.extend_apply (fun _ _ h ↦ Subtype.ext (Units.ext h)) _ _ x

/-- **Off the fractions prime to `𝔪`, the finite character on `K` vanishes.** -/
theorem finiteCharacterField_eq_zero (χ : Grossencharacter K 𝔪) {x : K}
    (hx : ∀ y : primeToSubgroup 𝔪, ((y : Kˣ) : K) ≠ x) : χ.finiteCharacterField x = 0 :=
  Function.extend_apply' _ _ x (not_exists.mpr hx)

/-- **The finite character on `K` vanishes exactly off the fractions prime to `𝔪`.** -/
theorem finiteCharacterField_eq_zero_iff (χ : Grossencharacter K 𝔪) {x : K} :
    χ.finiteCharacterField x = 0 ↔ ∀ y : primeToSubgroup 𝔪, ((y : Kˣ) : K) ≠ x := by
  refine ⟨fun h y hy ↦ ?_, χ.finiteCharacterField_eq_zero⟩
  rw [← hy, finiteCharacterField_coe] at h
  exact (χ.finiteCharacterK y).ne_zero h

@[simp]
theorem finiteCharacterField_zero (χ : Grossencharacter K 𝔪) : χ.finiteCharacterField 0 = 0 :=
  χ.finiteCharacterField_eq_zero fun y ↦ (y : Kˣ).ne_zero

/-- `finiteCharacterField` evaluates to `1` at `1`. -/
@[simp]
theorem finiteCharacterField_one (χ : Grossencharacter K 𝔪) : χ.finiteCharacterField 1 = 1 := by
  simpa using χ.finiteCharacterField_coe 1

/-- Outside `primeToSubgroup 𝔪`, the finite character on `K` vanishes on `x : Kˣ`. -/
theorem finiteCharacterField_eq_zero_of_notMem (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : x ∉ primeToSubgroup 𝔪) : χ.finiteCharacterField (x : K) = 0 :=
  χ.finiteCharacterField_eq_zero fun y hy ↦ hx (Units.ext hy ▸ y.property)

/-- **The finite character on `K` extends the finite character on `𝓞 K`.** -/
@[simp]
theorem finiteCharacterField_algebraMap (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacterField (algebraMap (𝓞 K) K a) = χ.finiteCharacter a := by
  by_cases ha : 𝔪.IsCoprimeTo (Ideal.span {a})
  · obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp ha
    rw [χ.finiteCharacter_eq_finiteCharacterK x hx.symm, ← finiteCharacterField_coe]
    exact congrArg χ.finiteCharacterField hx.symm
  · rw [χ.finiteCharacter_eq_zero_of_not_isCoprimeTo ha]
    exact χ.finiteCharacterField_eq_zero fun y hy ↦
      ha (Modulus.isCoprimeTo_span_singleton_iff.mpr ⟨y, hy⟩)

/-- **Multiplicativity along the fractions prime to `𝔪`**: multiplying by a fraction `y` prime
to `𝔪` multiplies the finite character on `K` by `finiteCharacterK y`. -/
theorem finiteCharacterField_coe_mul (χ : Grossencharacter K 𝔪) (y : primeToSubgroup 𝔪)
    (x : K) :
    χ.finiteCharacterField (((y : Kˣ) : K) * x) =
      χ.finiteCharacterK y * χ.finiteCharacterField x := by
  by_cases hx : ∃ z : primeToSubgroup 𝔪, ((z : Kˣ) : K) = x
  · obtain ⟨z, rfl⟩ := hx
    rw [← Units.val_mul, ← Subgroup.coe_mul, finiteCharacterField_coe, finiteCharacterField_coe,
      map_mul, Units.val_mul]
  · rw [χ.finiteCharacterField_eq_zero (not_exists.mp hx), mul_zero]
    refine χ.finiteCharacterField_eq_zero fun z hz ↦ hx ⟨y⁻¹ * z, ?_⟩
    rw [Subgroup.coe_mul, Units.val_mul, hz, Subgroup.coe_inv, ← mul_assoc, Units.inv_mul,
      one_mul]

/-- Multiplying any element of `K` by a global unit `u : (𝓞 K)ˣ` factors out
`χ.finiteCharacter u`. -/
theorem finiteCharacterField_mul_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) (x : K) :
    χ.finiteCharacterField (algebraMap (𝓞 K) K u * x) =
      χ.finiteCharacter u * χ.finiteCharacterField x := by
  have heq : algebraMap (𝓞 K) K (u : 𝓞 K) =
      (((unitsToPrimeToSubgroup 𝔪 u : primeToSubgroup 𝔪) : Kˣ) : K) := by
    simp
  rw [heq, χ.finiteCharacterField_coe_mul (unitsToPrimeToSubgroup 𝔪 u) x,
    finiteCharacterK_unitsToPrimeToSubgroup, finiteCharacter_unit]

/-- Inversion conjugates `finiteCharacterField` on all of `K`. -/
@[simp]
theorem finiteCharacterField_inverse (χ : Grossencharacter K 𝔪) (x : K) :
    χ.inverse.finiteCharacterField x = starRingEnd ℂ (χ.finiteCharacterField x) := by
  by_cases hx : ∃ z : primeToSubgroup 𝔪, ((z : Kˣ) : K) = x
  · obtain ⟨z, rfl⟩ := hx
    rw [finiteCharacterField_coe, finiteCharacterField_coe, coe_finiteCharacterK_inverse]
  · rw [χ.inverse.finiteCharacterField_eq_zero (not_exists.mp hx),
      χ.finiteCharacterField_eq_zero (not_exists.mp hx), map_zero]

/-- The values of the finite character on `K` have norm at most `1`. -/
theorem norm_finiteCharacterField_le (χ : Grossencharacter K 𝔪) (x : K) :
    ‖χ.finiteCharacterField x‖ ≤ 1 := by
  by_cases hx : ∃ z : primeToSubgroup 𝔪, ((z : Kˣ) : K) = x
  · obtain ⟨z, rfl⟩ := hx
    rw [finiteCharacterField_coe, norm_finiteCharacterK]
  · rw [χ.finiteCharacterField_eq_zero (not_exists.mp hx), norm_zero]
    exact zero_le_one

/-- **At a trivial finite modulus, the finite character on `K` is `1` at every nonzero element**:
every element of `Kˣ` is prime to `𝔪`, and the finite character is trivial
(`finiteCharacterK_eq_one_of_finitePart_eq_top`). -/
theorem finiteCharacterField_eq_one_of_finitePart_eq_top (χ : Grossencharacter K 𝔪)
    (h : 𝔪.finitePart = ⊤) {x : K} (hx : x ≠ 0) : χ.finiteCharacterField x = 1 := by
  have hmem : Units.mk0 x hx ∈ primeToSubgroup 𝔪 := mem_primeToSubgroup.mpr fun v hv ↦ by
    rw [h, Ideal.dvd_iff_le, top_le_iff] at hv
    exact (v.isPrime.ne_top hv).elim
  have := χ.finiteCharacterField_coe ⟨Units.mk0 x hx, hmem⟩
  rw [Units.val_mk0] at this
  rw [this, χ.finiteCharacterK_eq_one_of_finitePart_eq_top h, Units.val_one]

/-- **The finite character on `K` depends only on the Hecke character and the finite part of the
modulus.** -/
theorem finiteCharacterField_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (h𝔪 : 𝔪.finitePart = 𝔫.finitePart) :
    χ.finiteCharacterField = ψ.finiteCharacterField := by
  have hmem (x : Kˣ) : x ∈ primeToSubgroup 𝔪 ↔ x ∈ primeToSubgroup 𝔫 := by
    simp only [mem_primeToSubgroup, h𝔪]
  funext x
  by_cases hx : ∃ z : primeToSubgroup 𝔪, ((z : Kˣ) : K) = x
  · obtain ⟨⟨z, hz⟩, rfl⟩ := hx
    refine (χ.finiteCharacterField_coe ⟨z, hz⟩).trans
      (Eq.trans ?_ (ψ.finiteCharacterField_coe ⟨z, (hmem z).mp hz⟩).symm)
    exact congrArg _ (finiteCharacterK_congr h _ _)
  · rw [χ.finiteCharacterField_eq_zero (not_exists.mp hx), ψ.finiteCharacterField_eq_zero]
    exact fun z hz ↦ hx ⟨⟨z, (hmem z).mpr z.property⟩, hz⟩

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

/-- **Primitivity of `residueCharacter` at the finite conductor.** When `𝔪.finitePart` equals
the finite conductor of `χ.toHeckeCharacter`, `χ.residueCharacter` does not factor through any
proper divisor `I` of `𝔪.finitePart`: there exists a residue unit congruent to `1` modulo `I`
on which `χ.residueCharacter` is nontrivial. -/
theorem exists_residueCharacter_ne_one_of_finiteConductor_eq (χ : Grossencharacter K 𝔪)
    (hcond : χ.toHeckeCharacter.finiteConductor = 𝔪.finitePart) {I : Ideal (𝓞 K)}
    (hI : I ∣ 𝔪.finitePart) (hIne : I ≠ 𝔪.finitePart) :
    ∃ u : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
      Ideal.Quotient.factor (Ideal.le_of_dvd hI) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1 ∧
        χ.residueCharacter u ≠ 1 := by
  by_contra h
  push Not at h
  have hdvd : 𝔪.finitePart ∣ I := by
    rw [← hcond, χ.finiteConductor_dvd_iff_residueCharacter_eq_one I]
    intro a ha ha1
    have hfac : Ideal.Quotient.factor (Ideal.le_of_dvd hI)
        (ha.unit : 𝓞 K ⧸ 𝔪.finitePart) = 1 := by
      rw [IsUnit.unit_spec, Ideal.Quotient.factor_mk, ← map_one (Ideal.Quotient.mk I),
        Ideal.Quotient.eq]
      exact ha1
    simpa [IsUnit.unit_spec] using h ha.unit hfac
  exact hIne (le_antisymm (Ideal.le_of_dvd hdvd) (Ideal.le_of_dvd hI))

/-! ### Ray class presentations -/

/-- For the presentation of a ray class character `η`, the finite character at an integer `a`
prime to `𝔪` is the ray class value of the principal ideal `(a)` multiplied by the archimedean
value. -/
theorem finiteCharacter_ofRayClassCharacter (η : RayClassCharacter 𝔪) {a : 𝓞 K} {x : Kˣ}
    (ha : algebraMap (𝓞 K) K a = x) (hx : x ∈ primeToSubgroup 𝔪) :
    (ofRayClassCharacter η).finiteCharacter a =
      (η (principalRayClass 𝔪 ⟨x, hx⟩) : ℂ) *
        ((ofRayClassCharacter η).archimedeanValue x : ℂ) := by
  have hcop : 𝔪.IsCoprimeTo (Ideal.span {a}) :=
    Modulus.isCoprimeTo_span_singleton_iff.mpr ⟨⟨x, hx⟩, ha.symm⟩
  have hJ : Ideal.span {a} ∈ integralIdealsPrimeTo 𝔪 :=
    Modulus.mem_integralIdealsPrimeTo.mpr hcop
  obtain ⟨y, hy, hclass⟩ :=
    exists_idealClass_eq_principalRayClass (𝔪 := 𝔪) (J := ⟨Ideal.span {a}, hJ⟩) rfl
  have hxy : y = ⟨x, hx⟩ := Subtype.ext (Units.ext (hy.trans ha))
  rw [finiteCharacter_apply_of_algebraMap_eq _ ha, idealShift_ofRayClassCharacter,
    Complex.ofReal_zero, Complex.cpow_zero, mul_one, unitaryWeight_ofRayClassCharacter,
    RayClassCharacter.val_toUnitaryIdealWeight,
    RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo η
      (Ideal.isPrimeTo_iff.mpr (Modulus.isCoprimeTo_iff.mp hcop)),
    RayClassCharacter.onIdeals_apply, hclass, hxy]

open scoped Classical in
/-- For the trivial ray class character at modulus `𝔪`, Hecke's finite character is the
indicator of integers generating ideals coprime to `𝔪`. -/
theorem finiteCharacter_ofRayClassCharacter_one (a : 𝓞 K) :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter a =
      if 𝔪.IsCoprimeTo (Ideal.span {a}) then 1 else 0 := by
  split_ifs with hcop
  · obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp hcop
    rw [finiteCharacter_ofRayClassCharacter 1 hx.symm x.property,
      archimedeanValue_ofRayClassCharacter_one]
    simp
  · exact (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter_eq_zero_of_not_isCoprimeTo
      hcop

/-- The residue character of the trivial ray class character is the trivial `MulChar`. -/
@[simp]
theorem residueCharacter_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).residueCharacter = 1 := by
  classical
  refine (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).existsUnique_residueCharacter.unique
    (fun a ha ↦ ((ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter_eq_residueCharacter
      ha).symm)
    fun a ha ↦ ?_
  rw [finiteCharacter_ofRayClassCharacter_one]
  split_ifs with hcop
  · have hunit : IsUnit (Ideal.Quotient.mk 𝔪.finitePart a) :=
      (Modulus.isUnit_mk_iff_isCoprimeTo ha).mpr hcop
    rw [← hunit.unit_spec, MulChar.one_apply_coe]
  · exact MulChar.map_nonunit _ fun hu ↦ hcop ((Modulus.isUnit_mk_iff_isCoprimeTo ha).mp hu)

end Grossencharacter

end TauCeti.LFunctions
