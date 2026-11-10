/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Basic
import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Ideal
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic

/-!
# Hecke's unit relation for a presentation

Let `χ` be a presentation at the modulus `𝔪` of an algebraic Hecke character, with unitary weight
`χ_u`, ideal-side shift `σ` and algebraic infinity type `n`. For `a ∈ 𝓞_K` with `a ≡ 1 mod* 𝔪`
(`GlobalNumberFields.IsCongrOne`, positivity at the real places of `𝔪` included), the full ideal
value `χ_u((a)) N(a) ^ σ` is the **inverse** of the archimedean monomial:

`χ_u((a)) * N(a) ^ σ * ∏_τ τ(a) ^ (n τ) = 1`  (`Grossencharacter.compatibility`).

This is Hecke's description of a Größencharakter on principal ideals, read off the idele class
character: the principal idele of `a` is trivial for `χ`, its finite coordinates evaluate to
`χ_u((a)) N(a) ^ σ`, and its archimedean coordinates to `∏_τ τ(a) ^ (n τ)`. The inverse is
forced by this; Hecke's classical infinity type, the one in `χ((a)) = χ_f(a) χ_∞(a)`, is `-n`.
Over `ℚ(i)` the angular character `(α) ↦ (α / conj α) ^ (2k)` has finite value
`((3 + 4i) / 5) ^ (2k)` at `a = 2 + i` and archimedean value `((3 + 4i) / 5) ^ (-2k)`, so for
`k ≠ 0` the relation with the two sides equal instead of inverse fails.

## Main results

* `TauCeti.LFunctions.Grossencharacter.conductorExponent_le_exponent` and
  `TauCeti.LFunctions.Grossencharacter.finiteConductor_dvd_finitePart`: the finite conductor of
  the presented character divides the finite part of the modulus.
* `TauCeti.LFunctions.Grossencharacter.compatibility`: Hecke's unit relation, and
  `TauCeti.LFunctions.Grossencharacter.compatibility_inv` its form solved for the finite value.

## Implementation notes

The finite side is the supplier's ideal character `HeckeCharacter.idealCharacter` on the
principal ideal, which is the inverse of the archimedean components
(`HeckeCharacter.idealCharacter_apply_toPrincipalIdeal`). It needs `a ≡ 1` modulo the finite
conductor of `χ`, which divides the finite part of `𝔪`
(`Grossencharacter.finiteConductor_dvd_finitePart`), and it agrees with `χ_u N ^ σ` on the
integral ideals prime to `𝔪` because both are multiplicative and agree at the primes
(`Grossencharacter.toHeckeCharacter_primeIdele`). On the archimedean side, the components agree
with the monomial of `n` at the complex places, and at a real place either the parities agree
or the place divides `𝔪` and `a` is positive there
(`HeckeCharacter.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity`).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, (6.1) and (6.13).
* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section

open IsDedekindDomain NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.LFunctions

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

namespace Grossencharacter

/-! ### The finite conductor of a presentation -/

/-- **The conductor exponents of a presentation are bounded by its modulus**: at every finite
place `v`, the conductor exponent of the presented character is at most the exponent of `v` in
`𝔪`, that is, the character is trivial on `U(K_v, 𝔪.exponent v)`. -/
theorem conductorExponent_le_exponent (χ : Grossencharacter K 𝔪)
    (v : HeightOneSpectrum (𝓞 K)) :
    χ.toHeckeCharacter.conductorExponent v ≤ 𝔪.exponent v :=
  (χ.toHeckeCharacter.conductorExponent_le_iff v _).mpr fun u hu ↦ by
    rw [HeckeCharacter.finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply]
    exact χ.eq_one_of_mem _ (ofAdicCompletion_mem_ideleCongruenceSubgroup_iff.mpr hu)
      fun w ↦ InfinitePlace.ideleInfiniteCoord_ofAdicCompletion w v u

/-- **The finite conductor of a presentation divides the finite part of its modulus.** -/
theorem finiteConductor_dvd_finitePart (χ : Grossencharacter K 𝔪) :
    χ.toHeckeCharacter.finiteConductor ∣ 𝔪.finitePart := by
  rw [Ideal.dvd_iff_le]
  refine (le_iInf fun v ↦ ?_).trans
    (Ideal.iInf_maxPowDividing_eq χ.toHeckeCharacter.finiteConductor_ne_bot).le
  -- `maxPowDividing` is the prime power recorded by the conductor exponent.
  rw [HeightOneSpectrum.maxPowDividing, χ.toHeckeCharacter.count_finiteConductor]
  exact (Ideal.dvd_iff_le.mp (𝔪.pow_exponent_dvd_finitePart v)).trans
    (Ideal.pow_le_pow_right (χ.conductorExponent_le_exponent v))

/-! ### The unit relation -/

/-- On the integral ideals prime to `𝔪`, the ideal character of the presented Hecke character is
the unitary weight times the norm to the ideal-side shift: both are multiplicative, and at a prime
both are the local component at a uniformizer (`toHeckeCharacter_primeIdele`). -/
private theorem coe_idealCharacter_integralIdealsAwayHom (χ : Grossencharacter K 𝔪)
    {J : Ideal (𝓞 K)} (hJ : J.IsPrimeTo (𝔪.support : Set (HeightOneSpectrum (𝓞 K))))
    (hJ' : J ∈ NumberFieldArithmetic.integralIdealsAway
      (⟨χ.toHeckeCharacter.finiteConductor, χ.toHeckeCharacter.finiteConductor_ne_bot, ∅⟩ :
        Modulus K).support) :
    (χ.toHeckeCharacter.idealCharacter
        (NumberFieldArithmetic.integralIdealsAwayHom K _ ⟨J, hJ'⟩) : ℂ) =
      χ.unitaryWeight.1 J * (Ideal.absNorm J : ℂ) ^ (χ.idealShift : ℂ) := by
  refine Ideal.IsPrimeTo.induction_on (motive := fun J ↦ ∀ hJ' : J ∈ _,
    (χ.toHeckeCharacter.idealCharacter
        (NumberFieldArithmetic.integralIdealsAwayHom K _ ⟨J, hJ'⟩) : ℂ) =
      χ.unitaryWeight.1 J * (Ideal.absNorm J : ℂ) ^ (χ.idealShift : ℂ)) hJ (fun htop ↦ ?_)
    (fun v J hv _ ih hvJ ↦ ?_) hJ'
  · have hone : (⟨⊤, htop⟩ : NumberFieldArithmetic.integralIdealsAway _) = 1 :=
      Subtype.ext Ideal.one_eq_top.symm
    rw [hone, map_one, map_one, Units.val_one, ← Ideal.one_eq_top, map_one]
    simp
  obtain ⟨hv', hJ''⟩ := Ideal.isPrimeTo_mul_iff.mp
    (NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp hvJ)
  replace hv' := NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr hv'
  replace hJ'' := NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr hJ''
  rw [← Submonoid.mk_mul_mk _ _ _ hv' hJ'', map_mul, map_mul, Units.val_mul, ih hJ'']
  -- At the prime `v`, evaluate both sides at a uniformizer of `K_v`.
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
  have hu := v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu
  rw [χ.toHeckeCharacter.idealCharacter_apply_prime _ v
      (NumberFieldArithmetic.coe_integralIdealsAwayHom _ _) u hu,
    χ.toHeckeCharacter_primeIdele v ((𝔪.mem_support_iff v).not.mp hv) u hu, map_mul,
    map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-- **Hecke's unit relation.** For `a ∈ 𝓞_K` with `a ≡ 1 mod* 𝔪`, the full ideal value
`χ_u((a)) N(a) ^ σ` of a presentation is the inverse of the archimedean monomial
`∏_τ τ(a) ^ (n τ)` of its algebraic infinity type `n`:
`χ_u((a)) * N(a) ^ σ * ∏_τ τ(a) ^ (n τ) = 1`. -/
theorem compatibility (χ : Grossencharacter K 𝔪) (x : Kˣ) (hx : IsCongrOne 𝔪 x) (a : 𝓞 K)
    (ha : algebraMap (𝓞 K) K a = x) :
    χ.unitaryWeight.1 (Ideal.span {a}) *
        ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) *
      ∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ = 1 := by
  set ψ := χ.toHeckeCharacter
  set 𝔣 : Modulus K := ⟨ψ.finiteConductor, ψ.finiteConductor_ne_bot, ∅⟩
  have hx𝔣 : IsCongrOne 𝔣 x :=
    hx.mono (Modulus.dvd_iff.mpr ⟨χ.finiteConductor_dvd_finitePart, Finset.empty_subset _⟩)
  -- The fractional ideal of `x` is the integral ideal `(a)`, prime to `𝔪` and to `𝔣`.
  have hspan : ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      ((toPrincipalIdeal (𝓞 K) K x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton, ha]
  have hne : Ideal.span {a} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    rintro rfl
    exact x.ne_zero (by rw [← ha, map_zero])
  have hmem {𝔫 : Modulus K} (h𝔫 : IsCongrOne 𝔫 x) :
      Ideal.span {a} ∈ NumberFieldArithmetic.integralIdealsAway 𝔫.support :=
    NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero.mpr ⟨hne, fun v hv ↦ by
      rw [hspan]
      exact NumberFieldArithmetic.mem_idealsAway_iff.mp h𝔫.toPrincipalIdeal_mem_idealsPrimeTo v hv⟩
  have hideal : NumberFieldArithmetic.integralIdealsAwayHom K 𝔣.support ⟨_, hmem hx𝔣⟩ =
      ⟨toPrincipalIdeal (𝓞 K) K x, hx𝔣.toPrincipalIdeal_mem_idealsPrimeTo⟩ :=
    Subtype.ext (Units.ext (by rw [NumberFieldArithmetic.coe_integralIdealsAwayHom, hspan]))
  have hfinite := coe_idealCharacter_integralIdealsAwayHom χ
    (NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp (hmem hx)) (hmem hx𝔣)
  -- The ideal character of `(x)` is the inverse of the archimedean monomial: at a real place
  -- where the parities differ, the place divides `𝔪`, where `x` is positive.
  have hpos (w : {w : InfinitePlace K // w.IsReal})
      (hw : ψ.infinityType.realParity w ≠
        (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w) :
      0 < InfinitePlace.embedding_of_isReal w.2 (x : K) :=
    (isCongrOne_iff.mp hx).2 w (not_imp_comm.mp (χ.realParity_eq w) hw)
  rw [hideal, HeckeCharacter.idealCharacter_apply_toPrincipalIdeal ψ x hx𝔣,
    Units.val_inv_eq_inv_val, Units.coe_prod,
    ψ.coe_prod_infiniteComponent_eq_embeddingCharacter_of_realParity χ.infinityType
      χ.agreesOnIdentityComponent x hpos,
    AlgebraicInfinityType.coe_embeddingCharacter_apply] at hfinite
  rw [← hfinite]
  refine inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ ↦ zpow_ne_zero _ ?_)
  exact (map_ne_zero τ).mpr x.ne_zero

/-- **Hecke's unit relation, solved for the finite value**: for `a ∈ 𝓞_K` with `a ≡ 1 mod* 𝔪`,
`χ_u((a)) N(a) ^ σ = (∏_τ τ(a) ^ (n τ))⁻¹`. -/
theorem compatibility_inv (χ : Grossencharacter K 𝔪) (x : Kˣ) (hx : IsCongrOne 𝔪 x) (a : 𝓞 K)
    (ha : algebraMap (𝓞 K) K a = x) :
    χ.unitaryWeight.1 (Ideal.span {a}) *
        ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℂ) ^ (χ.idealShift : ℂ) =
      (∏ τ : K →+* ℂ, τ (x : K) ^ χ.infinityType τ)⁻¹ :=
  eq_inv_of_mul_eq_one_left (χ.compatibility x hx a ha)

end Grossencharacter

end TauCeti.LFunctions
