/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Lemmas
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Compatibility
public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Inverse
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Residue

import TauCeti.NumberTheory.MulChar.Lemmas
import TauCeti.NumberTheory.MulChar.Real
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.NumberTheory.NumberField.Global.RayClass.Exact
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
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
idelic archimedean component, which is the inverse of the classical infinity character `χ_∞'` in
`χ((a)) = χ_f(a) χ_∞'(a)` (Neukirch VII §6, (6.1); see `Grossencharacter.compatibility`). Thus
in terms of the idelic archimedean value we have `χ((a)) = χ_f(a) χ_∞(a)⁻¹`, and the classical
rearrangement `χ_f(a) = χ((a)) χ_∞'(a)⁻¹` becomes multiplication `χ_f(a) = χ((a)) χ_∞(a)`. It is
the monomial
`∏_τ τ(a) ^ (n τ)` of the infinity type when `a` is positive at the real places of `𝔪`
(`Grossencharacter.archimedeanValue_eq_embeddingCharacter`), and differs from it by a sign at a
real place of `𝔪` where the parity of the Hecke character differs from that of `n`. With the
monomial alone, the odd character `χ₄` modulo `4∞` of `ℚ`, of exponent `0`, would give the even
function `a ↦ χ₄(|a|)` on `ℤ`, which is `1` at `-1` and `-1` at `3`, so does not even factor
through the residues modulo `4`.

The point of the correction is that `χ_f` only sees residues modulo the finite part `𝔪₀` of `𝔪`.
On the fractions prime to `𝔪₀` (the subgroup `primeToSubgroup 𝔪` of `Kˣ`), the finite character
`Grossencharacter.finiteCharacterK` is the ideal character of the presented Hecke character at
`(x)` times `χ_∞(x)`, which also equals the inverse product of the local finite components at
`𝔪.support` (`finiteCharacterK_eq_prod_finiteComponent_inv`). An `x ≡ 1 mod 𝔪₀` is congruent to `1`
modulo the finite conductor, where the ideal character at `(x)` is `χ_∞(x)⁻¹` because the Hecke
character is trivial on the principal idele of `x`
(`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal`). So the finite character is trivial on
every `x ≡ 1 mod 𝔪₀`, whatever the signs of `x` at the real places, and it factors through the
reduction to `(𝓞 K ⧸ 𝔪₀)ˣ`. The factor is the **residue character**
`Grossencharacter.residueCharacter`, a Mathlib `MulChar` of `𝓞 K ⧸ 𝔪₀`, which captures the finite
conductor of `χ.toHeckeCharacter` (`finiteConductor_dvd_iff_residueCharacter_eq_one`) and is
primitive when `𝔪₀ = 𝔣(χ)` (`exists_residueCharacter_ne_one_of_finiteConductor_eq`). On algebraic
integers, `Grossencharacter.finiteCharacter` is the coefficient that the twisted theta series
attaches to a lattice point: it is `0` exactly at the integers not prime to `𝔪` (`0` included),
and the residue character at the class of every nonzero integer
(`Grossencharacter.finiteCharacter_eq_residueCharacter`), which pins the residue character down
(`Grossencharacter.existsUnique_residueCharacter`). Its zero-extension to `K` is
`Grossencharacter.finiteCharacterK'`.

The coefficient and the residue character must be kept apart at `0`. When `𝔪₀ = 𝓞 K`, the residue
ring has one element, a unit, at which the residue character is `1`, while the coefficient at the
integer `0` is `0`. Accordingly the comparison is stated for nonzero integers only.

## Main definitions

* `TauCeti.LFunctions.Grossencharacter.archimedeanValue`: the archimedean value `χ_∞` on `Kˣ`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK`: the finite character on the fractions
  prime to `𝔪`.
* `TauCeti.LFunctions.Grossencharacter.residueCharacter`: the induced character of `𝓞 K ⧸ 𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter`: the finite character on `𝓞 K`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK'`: the finite character extended by `0`
  to all of `K`.

## Main results

* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK_eq_one_of_residueHom_eq_one`: the finite
  character is trivial on the fractions congruent to `1` modulo `𝔪₀`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacterK_eq_prod_finiteComponent_inv` and
  `TauCeti.LFunctions.Grossencharacter.finiteCharacter_eq_prod_finiteComponent_inv`: idelic local
  product formula for the finite character.
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
* `TauCeti.LFunctions.Grossencharacter.finiteConductor_dvd_iff_residueCharacter_eq_one` and
  `TauCeti.LFunctions.Grossencharacter.exists_residueCharacter_ne_one_of_finiteConductor_eq`:
  finite-conductor characterization and primitivity of `residueCharacter`.
* `TauCeti.LFunctions.Grossencharacter.finiteCharacter_unit`: on a unit it is the archimedean
  value.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.1) and (6.13).
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

/-- Inversion of a presentation inverts its archimedean value. -/
@[simp]
theorem archimedeanValue_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.archimedeanValue = χ.archimedeanValue⁻¹ := by
  refine MonoidHom.ext fun x ↦ ?_
  rw [MonoidHom.inv_apply, archimedeanValue_apply, archimedeanValue_apply,
    ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [toHeckeCharacter_inverse, HeckeCharacter.infiniteComponent_inv]
  rfl

/-- The archimedean value depends only on the underlying Hecke character. -/
theorem archimedeanValue_congr {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter) :
    χ.archimedeanValue = ψ.archimedeanValue := by
  ext x
  simp [archimedeanValue_apply, h]

/-- The trivial ray class character has identically `1` archimedean value. -/
@[simp]
theorem archimedeanValue_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).archimedeanValue = 1 := by
  ext x
  simp [archimedeanValue_apply]

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

/-- Reduce the product of local finite components over `𝔪.support` to the support of the
finite conductor of `χ.toHeckeCharacter`. -/
private theorem prod_finiteComponent_eq_finiteConductor_support (χ : Grossencharacter K 𝔪)
    (x : primeToSubgroup 𝔪) :
    (∏ v ∈ 𝔪.support,
        χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ))) =
      ∏ v ∈ (⟨χ.toHeckeCharacter.finiteConductor,
          χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ : Modulus K).support,
        χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)) := by
  classical
  set ψ := χ.toHeckeCharacter
  set 𝔣 : Modulus K := ⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩
  exact ψ.prod_finiteComponent_eq_of_subset (Modulus.support_mono χ.mk_finiteConductor_dvd)
    (fun v _ hv𝔣 ↦ not_not.mp ((ψ.dvd_finiteConductor_iff v).not.mp
      fun hdvd ↦ hv𝔣 ((𝔣.mem_support_iff v).mpr hdvd)))
    (fun v hv𝔪 ↦ mem_primeToSubgroup.mp x.property v ((𝔪.mem_support_iff v).mp hv𝔪))

/-- **Idelic formula for `finiteCharacterK`.** For `x ∈ primeToSubgroup 𝔪`, `χ.finiteCharacterK x`
equals the inverse product of the local finite components of `χ.toHeckeCharacter` at the primes
dividing `𝔪`. -/
theorem finiteCharacterK_eq_prod_finiteComponent_inv (χ : Grossencharacter K 𝔪)
    (x : primeToSubgroup 𝔪) :
    χ.finiteCharacterK x =
      (∏ v ∈ 𝔪.support,
        χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)))⁻¹ := by
  classical
  set ψ := χ.toHeckeCharacter
  set 𝔣 : Modulus K := ⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩
  have h𝔣 : 𝔣 ∣ 𝔪 := χ.mk_finiteConductor_dvd
  have hx𝔣 : (x : Kˣ) ∈ primeToSubgroup 𝔣 :=
    primeToSubgroup_le_of_dvd (Modulus.dvd_iff.mp h𝔣).1 x.property
  have hxideal : toPrincipalIdeal (𝓞 K) K (x : Kˣ) ∈ idealsPrimeTo 𝔣 :=
    NumberFieldArithmetic.toPrincipalIdeal_mem_idealsAway_iff.mpr hx𝔣
  let y : finiteIdelesAway K 𝔣.support := ⟨unitEmbedding (𝓞 K) K (x : Kˣ), by
    rw [mem_finiteIdelesAway_iff]
    exact (toFractionalIdeal_mem_idealsAway_iff 𝔣.support _).mp
      ((toFractionalIdeal_unitEmbedding (R := 𝓞 K) (x : Kˣ)).symm ▸ hxideal)⟩
  have hyideal : toIdealsAway K 𝔣.support y =
      NumberFieldArithmetic.idealsAwayInclusion K (Modulus.support_mono h𝔣)
        (NumberFieldArithmetic.principalIdealAway K 𝔪.support x) := by
    apply Subtype.ext
    rw [coe_toIdealsAway, toFractionalIdeal_unitEmbedding,
      NumberFieldArithmetic.coe_idealsAwayInclusion,
      NumberFieldArithmetic.coe_principalIdealAway]
  have hprincipal :
      (QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 K) K (x : Kˣ)) :
        IdeleClassGroup (𝓞 K) K) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨(x : Kˣ), rfl⟩
  have hsplit := congrArg (fun z : IdeleGroup (𝓞 K) K ↦ ψ (QuotientGroup.mk z))
    (IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele
      (IdeleGroup.unitEmbedding (𝓞 K) K (x : Kˣ)))
  rw [QuotientGroup.mk_mul, map_mul, hprincipal, map_one, QuotientGroup.mk_prod, map_prod,
    IdeleGroup.toFiniteIdele_unitEmbedding] at hsplit
  have hinf : (∏ w : InfinitePlace K,
      ψ (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 K) K w
        (w.ideleInfiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K (x : Kˣ)))))) =
      χ.archimedeanValue (x : Kˣ) := by
    rw [archimedeanValue_apply]
    simp only [ψ, HeckeCharacter.infiniteComponent_apply, IdeleClassGroup.ofCompletion_apply,
      InfinitePlace.ideleInfiniteCoord_unitEmbedding]
  rw [hinf] at hsplit
  have hprod_eq := χ.prod_finiteComponent_eq_finiteConductor_support x
  rw [finiteCharacterK_apply, ← hyideal, ψ.idealCharacter_apply_toIdealsAway y]
  simp only [y, HeightOneSpectrum.ideleFiniteCoord_ofFiniteIdele_unitEmbedding]
  rw [← hprod_eq]
  calc
    ψ (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 K) K (unitEmbedding (𝓞 K) K (x : Kˣ)))) *
        (∏ v ∈ 𝔪.support,
          ψ.finiteComponent v
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)))⁻¹ *
        χ.archimedeanValue (x : Kˣ)
      = (χ.archimedeanValue (x : Kˣ) *
          ψ (QuotientGroup.mk
            (IdeleGroup.ofFiniteIdele (𝓞 K) K (unitEmbedding (𝓞 K) K (x : Kˣ))))) *
          (∏ v ∈ 𝔪.support,
            ψ.finiteComponent v
              (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)))⁻¹ := by
        ac_rfl
    _ = (∏ v ∈ 𝔪.support,
          ψ.finiteComponent v
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)))⁻¹ := by
        rw [hsplit, one_mul]

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
  have harg : NumberFieldArithmetic.idealsAwayInclusion K
        (Modulus.support_mono χ.mk_finiteConductor_dvd)
        (NumberFieldArithmetic.principalIdealAway K 𝔪.support x) =
      ⟨toPrincipalIdeal (𝓞 K) K x, hx𝔣.toPrincipalIdeal_mem_idealsPrimeTo⟩ :=
    Subtype.ext (by rw [NumberFieldArithmetic.coe_idealsAwayInclusion,
      NumberFieldArithmetic.coe_principalIdealAway])
  rw [finiteCharacterK_apply, harg,
    χ.toHeckeCharacter.idealCharacter_apply_toPrincipalIdeal (x : Kˣ) hx𝔣,
    archimedeanValue_apply, inv_mul_cancel]

/-- On any element of `primeToSubgroup 𝔪` congruent to `1` modulo `𝔪`, `finiteCharacterK` takes
the value `1`. -/
theorem finiteCharacterK_eq_one_of_isCongrOne (χ : Grossencharacter K 𝔪) {x : primeToSubgroup 𝔪}
    (hx : IsCongrOne 𝔪 (x : Kˣ)) : χ.finiteCharacterK x = 1 :=
  χ.finiteCharacterK_eq_one_of_residueHom_eq_one
    (residueHom_eq_one_of_mem_congruenceSubgroup (mem_congruenceSubgroup.mpr hx))

/-- Inversion of a presentation inverts `finiteCharacterK`. -/
@[simp]
theorem finiteCharacterK_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.finiteCharacterK = χ.finiteCharacterK⁻¹ := by
  refine MonoidHom.ext fun x ↦ ?_
  rw [MonoidHom.inv_apply, finiteCharacterK_eq_prod_finiteComponent_inv,
    finiteCharacterK_eq_prod_finiteComponent_inv, inv_inj, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [toHeckeCharacter_inverse, HeckeCharacter.finiteComponent_inv]
  rfl

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

private theorem residueUnitHom_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.residueUnitHom = χ.residueUnitHom⁻¹ := by
  refine MonoidHom.ext fun u ↦ ?_
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔪 u
  rw [residueUnitHom_residueHom, MonoidHom.inv_apply, residueUnitHom_residueHom,
    finiteCharacterK_inverse, MonoidHom.inv_apply]

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

/-- Every value of `finiteCharacterK` has absolute value `1`. -/
theorem norm_finiteCharacterK (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    ‖(χ.finiteCharacterK x : ℂ)‖ = 1 := by
  rw [← χ.residueCharacter_residue x, ← coe_residueHom]
  exact χ.norm_residueCharacter_unit (residueHom 𝔪 x)

/-- Inversion conjugates `finiteCharacterK` as a complex value. -/
theorem coe_finiteCharacterK_inverse (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    (χ.inverse.finiteCharacterK x : ℂ) = starRingEnd ℂ (χ.finiteCharacterK x : ℂ) := by
  rw [finiteCharacterK_inverse, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact Complex.inv_eq_conj (χ.norm_finiteCharacterK x)

/-- The residue character of the inverse presentation is the inverse character. -/
theorem residueCharacter_inverse_eq_inv (χ : Grossencharacter K 𝔪) :
    χ.inverse.residueCharacter = χ.residueCharacter⁻¹ := by
  rw [residueCharacter, residueCharacter, χ.residueUnitHom_inverse, MulChar.ofUnitHom_inv]

/-- Inversion conjugates the residue character, since `(𝓞 K ⧸ 𝔪.finitePart)ˣ` is finite. -/
@[simp]
theorem residueCharacter_inverse (χ : Grossencharacter K 𝔪) :
    χ.inverse.residueCharacter = star χ.residueCharacter := by
  have : Finite (𝓞 K ⧸ 𝔪.finitePart) :=
    Ring.HasFiniteQuotients.finiteQuotient 𝔪.finitePart_ne_bot
  rw [residueCharacter, residueCharacter, χ.residueUnitHom_inverse]
  exact MulChar.ofUnitHom_inv_eq_star χ.residueUnitHom

/-- At trivial finite modulus `𝔪.finitePart = ⊤`, the residue ring has one element, a unit, on
which the residue character is identically `1`. -/
theorem residueCharacter_of_finitePart_eq_top (χ : Grossencharacter K 𝔪)
    (h : 𝔪.finitePart = ⊤) (q : 𝓞 K ⧸ 𝔪.finitePart) : χ.residueCharacter q = 1 := by
  have h1 : q = 1 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [← map_one (Ideal.Quotient.mk 𝔪.finitePart), Ideal.Quotient.eq, h]
    exact Submodule.mem_top
  rw [h1, map_one]

/-- Two presentations of the same Hecke character at moduli with `𝔪.finitePart ∣ 𝔫.finitePart`
have compatible residue characters along `finiteUnitsMap`. -/
theorem residueCharacter_comp_finiteUnitsMap {𝔫 : Modulus K} {χ : Grossencharacter K 𝔪}
    {ψ : Grossencharacter K 𝔫} (h : χ.toHeckeCharacter = ψ.toHeckeCharacter)
    (hdvd : 𝔪.finitePart ∣ 𝔫.finitePart) (u : (𝓞 K ⧸ 𝔫.finitePart)ˣ) :
    ψ.residueCharacter u = χ.residueCharacter (finiteUnitsMap hdvd u) := by
  classical
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔫 u
  rw [finiteUnitsMap_residueHom, coe_residueHom, coe_residueHom, ψ.residueCharacter_residue x,
    χ.residueCharacter_residue (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x),
    ψ.finiteCharacterK_eq_prod_finiteComponent_inv x,
    χ.finiteCharacterK_eq_prod_finiteComponent_inv
      (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x)]
  simp only [Subgroup.coe_inclusion, ← h]
  congr 2
  have hsub : 𝔪.support ⊆ 𝔫.support := fun v hv ↦
    (𝔫.mem_support_iff v).mpr (((𝔪.mem_support_iff v).mp hv).trans hdvd)
  refine χ.toHeckeCharacter.prod_finiteComponent_eq_of_subset hsub (fun v _ hv𝔪 ↦ ?_)
    (fun v hv𝔫 ↦ mem_primeToSubgroup.mp x.property v ((𝔫.mem_support_iff v).mp hv𝔫))
  have h0 : 𝔪.exponent v = 0 :=
    not_not.mp ((Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).not.mp hv𝔪)
  exact Nat.le_zero.mp (h0 ▸ χ.conductorExponent_le_exponent v)

/-! ### Finite-conductor characterization and primitivity -/

/-- Forward direction of `finiteConductor_dvd_iff_residueCharacter_eq_one`. -/
private theorem residueCharacter_eq_one_of_finiteConductor_dvd (χ : Grossencharacter K 𝔪)
    {𝔫 : Modulus K} (hdvd : 𝔫.finitePart ∣ 𝔪.finitePart)
    (hcond : χ.toHeckeCharacter.finiteConductor ∣ 𝔫.finitePart)
    (u : (𝓞 K ⧸ 𝔪.finitePart)ˣ)
    (hu : Ideal.Quotient.factor (Ideal.le_of_dvd hdvd) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1) :
    χ.residueCharacter u = 1 := by
  obtain ⟨x, rfl⟩ := residueHom_surjective 𝔪 u
  have hres𝔫 : residue 𝔫 (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x) = 1 := by
    have hf := finiteUnitsMap_residueHom hdvd x
    rw [Units.ext_iff, coe_finiteUnitsMap, coe_residueHom, coe_residueHom] at hf
    exact hf.symm.trans (by simpa only [coe_residueHom] using hu)
  have hval :=
    (residue_eq_one_iff (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x)).mp hres𝔫
  rw [coe_residueHom, χ.residueCharacter_residue x,
    χ.finiteCharacterK_eq_prod_finiteComponent_inv x]
  have hprod : (∏ v ∈ 𝔪.support,
      χ.toHeckeCharacter.finiteComponent v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ))) = 1 := by
    refine Finset.prod_eq_one fun v hv ↦ ?_
    have hexp : χ.toHeckeCharacter.conductorExponent v ≤ 𝔫.exponent v := by
      rw [Modulus.exponent_def, v.le_count_associates_iff_le_pow 𝔫.finitePart_ne_bot,
        ← Ideal.dvd_iff_le]
      exact ((χ.toHeckeCharacter.pow_dvd_finiteConductor_iff v _).mpr le_rfl).trans hcond
    refine χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
      (TauCeti.unitFiltration_antitone hexp ?_)
    by_cases hvI : v.asIdeal ∣ 𝔫.finitePart
    · exact (v.unitsMap_algebraMap_mem_unitFiltration_iff (𝔫.exponent v) (x : Kˣ)).mpr
        ⟨mem_primeToSubgroup.mp x.property v ((𝔪.mem_support_iff v).mp hv), hval v hvI⟩
    · have h0 : 𝔫.exponent v = 0 :=
        not_not.mp ((Modulus.mem_support_iff_exponent_ne_zero 𝔫 v).not.mp
          ((𝔫.mem_support_iff v).not.mpr hvI))
      rw [h0]
      exact (v.unitsMap_algebraMap_mem_unitFiltration_zero_iff (x : Kˣ)).mpr
        (mem_primeToSubgroup.mp x.property v ((𝔪.mem_support_iff v).mp hv))
  rw [hprod, inv_one, Units.val_one]

/-- Local conductor-exponent bound from residue-kernel triviality modulo `𝔫.finitePart`:
for each finite place `v`, `χ.toHeckeCharacter.conductorExponent v ≤ 𝔫.exponent v`. -/
private theorem conductorExponent_le_exponent_of_residueCharacter_eq_one
    (χ : Grossencharacter K 𝔪) {𝔫 : Modulus K} (hdvd : 𝔫.finitePart ∣ 𝔪.finitePart)
    (htriv : ∀ u : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
      Ideal.Quotient.factor (Ideal.le_of_dvd hdvd) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1 →
        χ.residueCharacter u = 1)
    (v : HeightOneSpectrum (𝓞 K)) :
    χ.toHeckeCharacter.conductorExponent v ≤ 𝔫.exponent v := by
  classical
  by_cases hv : v ∈ 𝔪.support
  · rw [χ.toHeckeCharacter.conductorExponent_le_iff]
    intro z hz
    -- Approximate `z` at `v` and `1` at all other primes of `𝔪.support` by a global element `x`.
    have hle_exp (w : HeightOneSpectrum (𝓞 K)) : 𝔫.exponent w ≤ 𝔪.exponent w := by
      rw [Modulus.exponent_def (m := 𝔪),
        w.le_count_associates_iff_le_pow 𝔪.finitePart_ne_bot, ← Ideal.dvd_iff_le]
      exact (𝔫.pow_exponent_dvd_finitePart w).trans hdvd
    obtain ⟨x, hxz, hother, hxv⟩ := exists_primeToSubgroup_approx_localUnit hv (hle_exp v) z hz
    -- Show `x` reduces to `1` modulo `𝔫.finitePart`, so `χ.residueCharacter (residueHom 𝔪 x) = 1`.
    have hres𝔫 : residue 𝔫 (Subgroup.inclusion (primeToSubgroup_le_of_dvd hdvd) x) = 1 := by
      rw [residue_eq_one_iff]
      intro w hwI
      have hw𝔪 : w ∈ 𝔪.support := (𝔪.mem_support_iff w).mpr (hwI.trans hdvd)
      by_cases hwv : w = v
      · subst hwv
        exact hxv
      · have hw_mem :=
          (w.unitsMap_algebraMap_mem_unitFiltration_iff (𝔪.exponent w) (x : Kˣ)).mp
            (hother w hw𝔪 hwv)
        exact hw_mem.2.trans (WithZero.exp_le_exp.mpr (by have := hle_exp w; omega))
    have hfactor : Ideal.Quotient.factor (Ideal.le_of_dvd hdvd)
        ((residueHom 𝔪 x : (𝓞 K ⧸ 𝔪.finitePart)ˣ) : 𝓞 K ⧸ 𝔪.finitePart) = 1 := by
      have hf := congrArg Units.val (finiteUnitsMap_residueHom hdvd x)
      simpa only [coe_finiteUnitsMap, coe_residueHom] using
        hf.trans ((coe_residueHom 𝔫 _).trans hres𝔫)
    have h1 := htriv (residueHom 𝔪 x) hfactor
    rw [coe_residueHom, χ.residueCharacter_residue x,
      χ.finiteCharacterK_eq_prod_finiteComponent_inv x] at h1
    have h1' : (∏ w ∈ 𝔪.support,
        χ.toHeckeCharacter.finiteComponent w
          (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom (x : Kˣ))) = 1 :=
      inv_eq_one.mp (Units.ext h1)
    -- Isolate the `v`-component: all other components in `𝔪.support` vanish by `hother`.
    have hprod_single :
        (∏ w ∈ 𝔪.support,
          χ.toHeckeCharacter.finiteComponent w
            (Units.map (algebraMap K (w.adicCompletion K)).toMonoidHom (x : Kˣ))) =
        χ.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ)) := by
      refine Finset.prod_eq_single v (fun w hw hne ↦ ?_) (fun hnv ↦ absurd hv hnv)
      exact χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
        (TauCeti.unitFiltration_antitone (χ.conductorExponent_le_exponent w) (hother w hw hne))
    rw [hprod_single] at h1'
    -- Transfer triviality from `x` to `z` using `x * z⁻¹ ∈ U(K_v, 𝔪.exponent v)`.
    have hdiff : χ.toHeckeCharacter.finiteComponent v
        (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (x : Kˣ) * z⁻¹) = 1 :=
      χ.toHeckeCharacter.finiteComponent_eq_one_of_mem_unitFiltration
        (TauCeti.unitFiltration_antitone (χ.conductorExponent_le_exponent v) hxz)
    rw [map_mul, map_inv, h1', one_mul, inv_eq_one] at hdiff
    exact hdiff
  · have h0 : 𝔪.exponent v = 0 :=
      not_not.mp ((Modulus.mem_support_iff_exponent_ne_zero 𝔪 v).not.mp hv)
    exact (Nat.le_zero.mp (h0 ▸ χ.conductorExponent_le_exponent v)).le.trans (Nat.zero_le _)

/-- Converse direction of `finiteConductor_dvd_iff_residueCharacter_eq_one`. -/
private theorem finiteConductor_dvd_of_residueCharacter_eq_one (χ : Grossencharacter K 𝔪)
    {𝔫 : Modulus K} (hdvd : 𝔫.finitePart ∣ 𝔪.finitePart)
    (htriv : ∀ u : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
      Ideal.Quotient.factor (Ideal.le_of_dvd hdvd) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1 →
        χ.residueCharacter u = 1) :
    χ.toHeckeCharacter.finiteConductor ∣ 𝔫.finitePart := by
  rw [Ideal.dvd_iff_le]
  refine (le_iInf fun v ↦ ?_).trans
    (Ideal.iInf_maxPowDividing_eq χ.toHeckeCharacter.finiteConductor_ne_bot).le
  rw [HeightOneSpectrum.maxPowDividing, χ.toHeckeCharacter.count_finiteConductor]
  exact (Ideal.dvd_iff_le.mp (𝔫.pow_exponent_dvd_finitePart v)).trans
    (Ideal.pow_le_pow_right
      (χ.conductorExponent_le_exponent_of_residueCharacter_eq_one hdvd htriv v))

/-- **Finite-conductor criterion for `residueCharacter`.** For an ideal `I ∣ 𝔪.finitePart`, the
finite conductor of `χ.toHeckeCharacter` divides `I` if and only if `χ.residueCharacter` is
trivial on every unit of `𝓞 K ⧸ 𝔪.finitePart` that reduces to `1` modulo `I`. -/
theorem finiteConductor_dvd_iff_residueCharacter_eq_one (χ : Grossencharacter K 𝔪)
    {I : Ideal (𝓞 K)} (hI : I ∣ 𝔪.finitePart) :
    χ.toHeckeCharacter.finiteConductor ∣ I ↔
      ∀ u : (𝓞 K ⧸ 𝔪.finitePart)ˣ,
        Ideal.Quotient.factor (Ideal.le_of_dvd hI) (u : 𝓞 K ⧸ 𝔪.finitePart) = 1 →
          χ.residueCharacter u = 1 := by
  have hI0 : I ≠ ⊥ := fun hbot ↦ 𝔪.finitePart_ne_bot (by
    obtain ⟨J, hJ⟩ := hI
    rw [hJ, hbot, Ideal.bot_mul])
  exact ⟨fun hcond u hu ↦
      χ.residueCharacter_eq_one_of_finiteConductor_dvd (𝔫 := ⟨I, hI0, ∅⟩) hI hcond u hu,
    fun htriv ↦
      χ.finiteConductor_dvd_of_residueCharacter_eq_one (𝔫 := ⟨I, hI0, ∅⟩) hI htriv⟩

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
  have hdvd : 𝔪.finitePart ∣ I :=
    hcond ▸ (χ.finiteConductor_dvd_iff_residueCharacter_eq_one hI).mpr h
  exact hIne (le_antisymm (Ideal.le_of_dvd hdvd) (Ideal.le_of_dvd hI))

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

/-- **Idelic formula for Hecke's finite character.** For `a ∈ 𝓞 K` generating an ideal prime to
`𝔪`, with image `x ∈ primeToSubgroup 𝔪`, `χ.finiteCharacter a` equals the inverse product of the
local finite components of `χ.toHeckeCharacter` at the primes dividing `𝔪`. -/
theorem finiteCharacter_eq_prod_finiteComponent_inv (χ : Grossencharacter K 𝔪) {a : 𝓞 K}
    {x : Kˣ} (ha : algebraMap (𝓞 K) K a = x) (hx : x ∈ primeToSubgroup 𝔪) :
    χ.finiteCharacter a =
      (∏ v ∈ 𝔪.support,
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
    exact fun hu ↦ hcop (Modulus.isCoprimeTo_iff_sup_eq_top.mpr
      ⟨Ideal.span_singleton_eq_bot.not.mpr ha, Ideal.Quotient.isUnit_mk_iff.mp hu⟩)

/-- **The finite character only sees residues modulo `𝔪₀`**: nonzero integers congruent modulo
the finite part of `𝔪` have the same finite character. -/
theorem finiteCharacter_eq_of_sub_mem (χ : Grossencharacter K 𝔪) {a b : 𝓞 K} (ha : a ≠ 0)
    (hb : b ≠ 0) (hab : a - b ∈ 𝔪.finitePart) : χ.finiteCharacter a = χ.finiteCharacter b := by
  rw [χ.finiteCharacter_eq_residueCharacter ha, χ.finiteCharacter_eq_residueCharacter hb,
    Ideal.Quotient.eq.mpr hab]

/-- Inversion conjugates Hecke's finite character on `𝓞 K`. -/
@[simp]
theorem finiteCharacter_inverse (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.inverse.finiteCharacter a = starRingEnd ℂ (χ.finiteCharacter a) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [χ.inverse.finiteCharacter_eq_residueCharacter ha, χ.residueCharacter_inverse,
      MulChar.star_apply, ← χ.finiteCharacter_eq_residueCharacter ha]
    rfl

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
    ψ.finiteCharacter_eq_finiteCharacterK x𝔫 hx𝔫.symm,
    χ.finiteCharacterK_eq_prod_finiteComponent_inv x𝔪,
    ψ.finiteCharacterK_eq_prod_finiteComponent_inv x𝔫,
    χ.prod_finiteComponent_eq_finiteConductor_support x𝔪,
    ψ.prod_finiteComponent_eq_finiteConductor_support x𝔫,
    hx]
  simp [h]

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

/-! ### Extension of `finiteCharacterK` by zero to `K` -/

open scoped Classical in
/-- **Hecke's finite character on `K`**, extended by `0` at `0` and outside `primeToSubgroup 𝔪`:
the finite-character coefficient evaluated on elements of fractional ideals. -/
def finiteCharacterK' (χ : Grossencharacter K 𝔪) (x : K) : ℂ :=
  if h : x = 0 then 0 else
    if hx : Units.mk0 x h ∈ primeToSubgroup 𝔪 then
      (χ.finiteCharacterK ⟨Units.mk0 x h, hx⟩ : ℂ)
    else 0

/-- `finiteCharacterK'` vanishes at `0`. -/
@[simp]
theorem finiteCharacterK'_zero (χ : Grossencharacter K 𝔪) : χ.finiteCharacterK' 0 = 0 := by
  classical
  exact dite_eq_left rfl

/-- `finiteCharacterK'` evaluates to `1` at `1`. -/
@[simp]
theorem finiteCharacterK'_one (χ : Grossencharacter K 𝔪) : χ.finiteCharacterK' 1 = 1 := by
  classical
  rw [finiteCharacterK', dite_eq_right one_ne_zero]
  have h1 : Units.mk0 (1 : K) one_ne_zero ∈ primeToSubgroup 𝔪 := by
    rw [Units.mk0_one]
    exact (primeToSubgroup 𝔪).one_mem
  rw [dite_eq_left h1]
  have hsub : (⟨Units.mk0 (1 : K) one_ne_zero, h1⟩ : primeToSubgroup 𝔪) = 1 :=
    Subtype.ext Units.mk0_one
  rw [hsub, map_one, Units.val_one]

/-- On `x : primeToSubgroup 𝔪`, `finiteCharacterK'` agrees with `finiteCharacterK`. -/
theorem finiteCharacterK'_of_mem (χ : Grossencharacter K 𝔪) (x : primeToSubgroup 𝔪) :
    χ.finiteCharacterK' ((x : Kˣ) : K) = χ.finiteCharacterK x := by
  classical
  rw [finiteCharacterK', dite_eq_right (x : Kˣ).ne_zero]
  have hx : Units.mk0 ((x : Kˣ) : K) (x : Kˣ).ne_zero ∈ primeToSubgroup 𝔪 := by
    simpa [Units.mk0_val] using x.property
  rw [dite_eq_left hx]
  congr 2
  exact Subtype.ext (Units.ext rfl)

/-- Outside `primeToSubgroup 𝔪`, `finiteCharacterK'` vanishes on `x : Kˣ`. -/
theorem finiteCharacterK'_of_not_mem (χ : Grossencharacter K 𝔪) {x : Kˣ}
    (hx : x ∉ primeToSubgroup 𝔪) : χ.finiteCharacterK' (x : K) = 0 := by
  classical
  rw [finiteCharacterK', dite_eq_right x.ne_zero]
  exact dite_eq_right (by simpa [Units.mk0_val] using hx)

/-- On algebraic integers, `finiteCharacterK'` agrees with `finiteCharacter`. -/
@[simp]
theorem finiteCharacterK'_algebraMap (χ : Grossencharacter K 𝔪) (a : 𝓞 K) :
    χ.finiteCharacterK' (algebraMap (𝓞 K) K a) = χ.finiteCharacter a := by
  by_cases ha : a = 0
  · simp [ha]
  · have hx0 : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha
    by_cases hcop : 𝔪.IsCoprimeTo (Ideal.span {a})
    · obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp hcop
      have hax : algebraMap (𝓞 K) K a = ((x : Kˣ) : K) := hx.symm
      rw [hax, χ.finiteCharacterK'_of_mem x, χ.finiteCharacter_eq_finiteCharacterK x hax]
    · rw [χ.finiteCharacter_eq_zero_of_not_isCoprimeTo hcop]
      exact χ.finiteCharacterK'_of_not_mem (x := Units.mk0 _ hx0) fun hmem ↦
        hcop (Modulus.isCoprimeTo_span_singleton_iff.mpr ⟨⟨_, hmem⟩, rfl⟩)

/-- Multiplying any element of `K` by an element of `primeToSubgroup 𝔪` factors out
`finiteCharacterK`. -/
theorem finiteCharacterK'_mul_of_mem_left (χ : Grossencharacter K 𝔪) (u : primeToSubgroup 𝔪)
    (x : K) :
    χ.finiteCharacterK' (((u : Kˣ) : K) * x) = χ.finiteCharacterK u * χ.finiteCharacterK' x := by
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  · let xK : Kˣ := Units.mk0 x hx0
    have hx_eq : x = (xK : K) := rfl
    have hux_eq : ((u : Kˣ) : K) * x = ((u : Kˣ) * xK : Kˣ) := rfl
    rw [hux_eq, hx_eq]
    by_cases hxm : xK ∈ primeToSubgroup 𝔪
    · have huxm : (u : Kˣ) * xK ∈ primeToSubgroup 𝔪 := mul_mem u.property hxm
      rw [χ.finiteCharacterK'_of_mem ⟨(u : Kˣ) * xK, huxm⟩, χ.finiteCharacterK'_of_mem ⟨xK, hxm⟩]
      have hmul : (⟨(u : Kˣ) * xK, huxm⟩ : primeToSubgroup 𝔪) = u * ⟨xK, hxm⟩ :=
        Subtype.ext rfl
      rw [hmul, map_mul, Units.val_mul]
    · have huxm : (u : Kˣ) * xK ∉ primeToSubgroup 𝔪 := fun h ↦
        hxm (by simpa using mul_mem (inv_mem u.property) h)
      rw [χ.finiteCharacterK'_of_not_mem huxm, χ.finiteCharacterK'_of_not_mem hxm, mul_zero]

/-- Multiplying any element of `K` by a global unit `u : (𝓞 K)ˣ` factors out
`χ.finiteCharacter u`. -/
theorem finiteCharacterK'_mul_unit (χ : Grossencharacter K 𝔪) (u : (𝓞 K)ˣ) (x : K) :
    χ.finiteCharacterK' (algebraMap (𝓞 K) K u * x) =
      χ.finiteCharacter u * χ.finiteCharacterK' x := by
  have heq : algebraMap (𝓞 K) K (u : 𝓞 K) =
      (((unitsToPrimeToSubgroup 𝔪 u : primeToSubgroup 𝔪) : Kˣ) : K) := by
    simp
  rw [heq, χ.finiteCharacterK'_mul_of_mem_left (unitsToPrimeToSubgroup 𝔪 u) x,
    finiteCharacterK_unitsToPrimeToSubgroup, finiteCharacter_unit]

/-- Inversion conjugates `finiteCharacterK'` on all of `K`. -/
@[simp]
theorem finiteCharacterK'_inverse (χ : Grossencharacter K 𝔪) (x : K) :
    χ.inverse.finiteCharacterK' x = starRingEnd ℂ (χ.finiteCharacterK' x) := by
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  · by_cases hx : Units.mk0 x hx0 ∈ primeToSubgroup 𝔪
    · have hx_eq : x = ((⟨Units.mk0 x hx0, hx⟩ : primeToSubgroup 𝔪) : Kˣ) := rfl
      rw [hx_eq, χ.inverse.finiteCharacterK'_of_mem, χ.finiteCharacterK'_of_mem,
        χ.coe_finiteCharacterK_inverse]
    · have hx_eq : x = (Units.mk0 x hx0 : Kˣ) := rfl
      rw [hx_eq, χ.inverse.finiteCharacterK'_of_not_mem hx, χ.finiteCharacterK'_of_not_mem hx,
        map_zero]

/-- Every value of `finiteCharacterK'` has absolute value at most `1`. -/
theorem norm_finiteCharacterK'_le_one (χ : Grossencharacter K 𝔪) (x : K) :
    ‖χ.finiteCharacterK' x‖ ≤ 1 := by
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  · by_cases hx : Units.mk0 x hx0 ∈ primeToSubgroup 𝔪
    · have hx_eq : x = ((⟨Units.mk0 x hx0, hx⟩ : primeToSubgroup 𝔪) : Kˣ) := rfl
      rw [hx_eq, χ.finiteCharacterK'_of_mem]
      exact (χ.norm_finiteCharacterK _).le
    · have hx_eq : x = (Units.mk0 x hx0 : Kˣ) := rfl
      rw [hx_eq, χ.finiteCharacterK'_of_not_mem hx]
      simp

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

/-- The residue character of the trivial ray class character is the trivial `MulChar`. -/
@[simp]
theorem residueCharacter_ofRayClassCharacter_one :
    (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).residueCharacter = 1 := by
  refine (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).existsUnique_residueCharacter.unique
    (fun a ha ↦ ((ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter_eq_residueCharacter
      ha).symm)
    fun a ha ↦ ?_
  by_cases hcop : 𝔪.IsCoprimeTo (Ideal.span {a})
  · obtain ⟨x, hx⟩ := Modulus.isCoprimeTo_span_singleton_iff.mp hcop
    rw [finiteCharacter_ofRayClassCharacter 1 hx.symm x.property,
      archimedeanValue_ofRayClassCharacter_one]
    have hunit : IsUnit (Ideal.Quotient.mk 𝔪.finitePart a) :=
      Ideal.Quotient.isUnit_mk_iff.mpr (Modulus.isCoprimeTo_iff_sup_eq_top.mp hcop).2
    rw [← hunit.unit_spec, MulChar.one_apply_coe]
    simp
  · rw [MulChar.map_nonunit _ fun hu ↦ hcop (Modulus.isCoprimeTo_iff_sup_eq_top.mpr
        ⟨Ideal.span_singleton_eq_bot.not.mpr ha, Ideal.Quotient.isUnit_mk_iff.mp hu⟩),
      (ofRayClassCharacter (1 : RayClassCharacter 𝔪)).finiteCharacter_eq_zero_of_not_isCoprimeTo
        hcop]

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

end Grossencharacter

end TauCeti.LFunctions
