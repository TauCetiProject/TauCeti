/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Basic
public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Ideal
import TauCeti.NumberTheory.LocalField.Uniformizer

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

/-! ### The unit relation -/

/-- On the integral ideals prime to `𝔪`, the ideal character of the presented Hecke character is
the unitary weight times the norm to the ideal-side shift: both are multiplicative, and at a prime
both are the local component at a uniformizer (`toHeckeCharacter_primeIdele`). -/
theorem coe_idealCharacter_integralIdealsAwayHom (χ : Grossencharacter K 𝔪)
    (J : integralIdealsPrimeTo 𝔪) :
    (χ.toHeckeCharacter.idealCharacter (NumberFieldArithmetic.integralIdealsAwayHom K _
        (integralIdealsPrimeToInclusion χ.mk_finiteConductor_dvd J)) : ℂ) =
      χ.unitaryWeight.1 J * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (χ.idealShift : ℂ) := by
  have h𝔣 := χ.mk_finiteConductor_dvd
  let g : integralIdealsPrimeTo 𝔪 →* ℂ :=
    { toFun J := χ.unitaryWeight.1 J * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℂ) ^ (χ.idealShift : ℂ)
      map_one' := by simp
      map_mul' I J := by
        rw [Submonoid.coe_mul, map_mul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
        ring }
  refine DFunLike.congr_fun (NumberFieldArithmetic.integralIdealsAway_hom_ext
    (f := (Units.coeHom ℂ).comp (χ.toHeckeCharacter.idealCharacter.comp
      ((NumberFieldArithmetic.integralIdealsAwayHom K _).comp (integralIdealsPrimeToInclusion h𝔣))))
    (g := g) fun v hv ↦ ?_) J
  -- At a prime `v`, evaluate both sides at a uniformizer of `K_v`.
  have hv𝔪 : ¬ v.asIdeal ∣ 𝔪.finitePart := (𝔪.mem_support_iff v).not.mp fun h ↦
    (NumberFieldArithmetic.mem_integralIdealsAway_iff.mp hv).2 v h dvd_rfl
  have : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  obtain ⟨u, hu⟩ := TauCeti.exists_isUniformizer (v.adicCompletion K)
  have hu := v.isUniformizer_iff_valued_eq_exp_neg_one.mp hu
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, Units.coeHom_apply,
    χ.toHeckeCharacter.idealCharacter_apply_prime _ v
      ((NumberFieldArithmetic.coe_integralIdealsAwayHom _ _).trans
        (congrArg _ (coe_integralIdealsPrimeToInclusion h𝔣 _))) u hu,
    χ.toHeckeCharacter_primeIdele v hv𝔪 u hu]
  simp only [g, MonoidHom.coe_mk, OneHom.coe_mk]

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
  have h𝔣 : 𝔣 ∣ 𝔪 := χ.mk_finiteConductor_dvd
  have hx𝔣 : IsCongrOne 𝔣 x := hx.mono h𝔣
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
  have hideal : NumberFieldArithmetic.integralIdealsAwayHom K 𝔣.support
        (integralIdealsPrimeToInclusion h𝔣 ⟨_, hmem hx⟩) =
      ⟨toPrincipalIdeal (𝓞 K) K x, hx𝔣.toPrincipalIdeal_mem_idealsPrimeTo⟩ :=
    Subtype.ext (Units.ext (by
      rw [NumberFieldArithmetic.coe_integralIdealsAwayHom, coe_integralIdealsPrimeToInclusion,
        hspan]))
  have hfinite := coe_idealCharacter_integralIdealsAwayHom χ ⟨_, hmem hx⟩
  -- The ideal character of `(x)` is the inverse of the archimedean monomial: at a real place
  -- where the parities differ, the place divides `𝔪`, where `x` is positive.
  have hpos (w : {w : InfinitePlace K // w.IsReal})
      (hw : ψ.infinityType.realParity w ≠
        (AlgebraicInfinityType.toContinuous χ.infinityType).realParity w) :
      0 < InfinitePlace.embedding_of_isReal w.2 (x : K) :=
    (isCongrOne_iff.mp hx).2 w (not_imp_comm.mp (χ.realParity_eq w) hw)
  rw [hideal, ψ.idealCharacter_apply_toPrincipalIdeal_eq_embeddingCharacter_inv χ.infinityType
      χ.agreesOnIdentityComponent x hx𝔣 hpos,
    Units.val_inv_eq_inv_val, AlgebraicInfinityType.coe_embeddingCharacter_apply] at hfinite
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
