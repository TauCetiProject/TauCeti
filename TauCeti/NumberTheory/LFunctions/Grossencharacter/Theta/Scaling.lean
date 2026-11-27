/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Grossencharacter.Theta

/-!
# Change of ideal representative for Hecke theta series

Multiplication of an ideal by a principal ideal prime to the finite conductor rescales each
Gaussian parameter by the squared absolute value of a generator. For the archimedean-weighted
series with the constant term removed, the multiplier is the unitary ideal character at the
principal ideal. This is the change of representative used in Hecke's Mellin formula.

See J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8.
-/

public section

open IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors

namespace TauCeti.LFunctions.Grossencharacter

open GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- Changing an ideal `I` to `(a)I`, for a generator prime to the finite conductor, rescales
its theta parameters and multiplies the nonconstant part by `χ_f(a) N(a^p)`. -/
theorem heckeTheta_toPrincipalIdeal_mul_sub_heckeEpsilon
    (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : primeToSubgroup χ.conductor) (y : realSpace K) :
    χ.heckeTheta (toPrincipalIdeal (𝓞 K) K (a : Kˣ) * I) y - χ.heckeEpsilon =
      ((χ.primitive.finiteCharacterK a : ℂ) * χ.harmonicFactor (mixedEmbedding K (a : Kˣ))) *
        (χ.heckeTheta I (fun w ↦ normAtPlace w (mixedEmbedding K (a : Kˣ)) ^ 2 * y w) -
          χ.heckeEpsilon) := by
  have hmem (b : K) : b ∈ ((toPrincipalIdeal (𝓞 K) K (a : Kˣ) * I :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule (𝓞 K) K) ↔
      ∃ c ∈ (I : Submodule (𝓞 K) K), (a : Kˣ) * c = b := by
    rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.coeToSubmodule_mul,
      FractionalIdeal.coeToSubmodule_spanSingleton, Submodule.mem_span_singleton_mul]
  let e : (I : Submodule (𝓞 K) K) ≃ ((toPrincipalIdeal (𝓞 K) K (a : Kˣ) * I :
      (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule (𝓞 K) K) :=
    Equiv.ofBijective (fun b ↦ ⟨(a : Kˣ) * (b : K), (hmem _).2 ⟨b, b.property, rfl⟩⟩)
      ⟨fun b c h ↦ Subtype.ext (mul_left_cancel₀ (a : Kˣ).ne_zero (congrArg Subtype.val h)),
        fun b ↦ by
          obtain ⟨c, hc, h⟩ := (hmem b).1 b.property
          exact ⟨⟨c, hc⟩, Subtype.ext h⟩⟩
  have he (b : (I : Submodule (𝓞 K) K)) : (e b : K) = (a : Kˣ) * (b : K) := rfl
  simp only [heckeTheta_def, add_sub_cancel_left, ← tsum_mul_left]
  conv_lhs => rw [← e.tsum_eq]
  refine tsum_congr fun b ↦ ?_
  rw [he, χ.primitive.finiteCharacterField_coe_mul, map_mul, χ.harmonicFactor_mul,
    archGaussian_mul]
  ring

/-- The multiplier `χ_f(a) N(a^p)` is the unitary ideal character of `(a)` times the
absolute value of the harmonic polynomial. -/
theorem finiteCharacterK_mul_harmonicFactor_eq_unitaryPart_idealCharacter_mul_norm
    (χ : Grossencharacter K 𝔪) (a : primeToSubgroup χ.conductor)
    (ha : toPrincipalIdeal (𝓞 K) K (a : Kˣ) ∈ idealsPrimeTo
      ⟨χ.toHeckeCharacter.unitaryPart.finiteConductor,
        χ.toHeckeCharacter.unitaryPart.finiteConductor_ne_bot, ∅⟩) :
    (χ.primitive.finiteCharacterK a : ℂ) * χ.harmonicFactor (mixedEmbedding K (a : Kˣ)) =
      (χ.toHeckeCharacter.unitaryPart.idealCharacter ⟨_, ha⟩ : ℂ) *
        (‖χ.harmonicFactor (mixedEmbedding K (a : Kˣ))‖ : ℂ) := by
  let H := χ.toHeckeCharacter
  let m (η : HeckeCharacter K) : Modulus K :=
    ⟨η.finiteConductor, η.finiteConductor_ne_bot, ∅⟩
  have hfin : (m H.unitaryPart).support = (m χ.primitive.toHeckeCharacter).support := by
    ext v
    simp only [Modulus.mem_support_iff, m, HeckeCharacter.finiteConductor_unitaryPart,
      χ.toHeckeCharacter_primitive, H]
  -- The norm twist is trivial on the local units at the primes of the finite conductor.
  have hlocal v (hv : v ∈ (m H.unitaryPart).support) :
      H.unitaryPart.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a) =
        χ.primitive.toHeckeCharacter.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a) := by
    have hv' : v.asIdeal ∣ χ.conductor.finitePart := by
      simpa only [m, Modulus.mem_support_iff, HeckeCharacter.finiteConductor_unitaryPart,
        χ.finitePart_conductor, H] using hv
    have hval := mem_primeToSubgroup.mp a.property v hv'
    rw [χ.toHeckeCharacter_primitive]
    conv_rhs => rw [← χ.toHeckeCharacter.unitaryPart_mul_normPow_shift,
      HeckeCharacter.finiteComponent_mul,
      ContinuousMonoidHom.mul_apply, HeckeCharacter.finiteComponent_normPow_of_valued_eq_one _ _
        (by simpa only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
          HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
          Algebra.algebraMap_self_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
          using hval), mul_one]
  have hprod : (∏ v ∈ (m H.unitaryPart).support,
        H.unitaryPart.finiteComponent v
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a))⁻¹ =
      χ.primitive.finiteCharacterK a := by
    rw [χ.primitive.finiteCharacterK_eq_prod_finiteComponent_inv]
    exact congrArg Inv.inv (Finset.prod_congr hfin fun v hv ↦ hlocal v (hfin ▸ hv))
  have hinf := χ.prod_unitaryPart_infiniteComponent_mul_harmonicFactor (a : Kˣ)
  rw [← χ.norm_harmonicFactor, ← Units.coe_prod] at hinf
  rw [HeckeCharacter.idealCharacter_apply_toPrincipalIdeal_eq_prod_inv_mul_prod_inv, hprod,
    Units.val_mul, Units.val_inv_eq_inv_val, ← hinf, mul_mul_mul_comm, inv_mul_cancel₀,
    one_mul]
  exact Units.ne_zero _

/-- For the weighted Hecke theta series minus its constant term, changing `I` to `(a)I`
rescales the parameters by `|a|_w²` and multiplies the result by the unitary ideal character
at `(a)`. -/
theorem archWeight_mul_heckeTheta_toPrincipalIdeal_mul_sub_heckeEpsilon
    (χ : Grossencharacter K 𝔪) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : primeToSubgroup χ.conductor)
    (ha : toPrincipalIdeal (𝓞 K) K (a : Kˣ) ∈ idealsPrimeTo
      ⟨χ.toHeckeCharacter.unitaryPart.finiteConductor,
        χ.toHeckeCharacter.unitaryPart.finiteConductor_ne_bot, ∅⟩)
    (y : realSpace K) :
    (χ.archWeight y : ℂ) *
        (χ.heckeTheta (toPrincipalIdeal (𝓞 K) K (a : Kˣ) * I) y - χ.heckeEpsilon) =
      (χ.toHeckeCharacter.unitaryPart.idealCharacter ⟨_, ha⟩ : ℂ) *
        ((χ.archWeight (fun w ↦ normAtPlace w (mixedEmbedding K (a : Kˣ)) ^ 2 * y w) : ℂ) *
          (χ.heckeTheta I (fun w ↦ normAtPlace w (mixedEmbedding K (a : Kˣ)) ^ 2 * y w) -
            χ.heckeEpsilon)) := by
  have hweight := χ.toHeckeCharacter.infinityType.archWeight_mul_sq_normAtPlace
    (mixedEmbedding K (a : Kˣ)) y
  simp only [← archWeight_eq_infinityType, ← harmonicFactor_eq_infinityType] at hweight
  rw [χ.heckeTheta_toPrincipalIdeal_mul_sub_heckeEpsilon,
    χ.finiteCharacterK_mul_harmonicFactor_eq_unitaryPart_idealCharacter_mul_norm a ha,
    hweight, Complex.ofReal_mul]
  ring

end TauCeti.LFunctions.Grossencharacter
