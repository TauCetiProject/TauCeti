/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.MulIndicator

/-!
# The finite idele for a Weil lattice

The finite Weil idele records the local denominator factors of the Weil lattice.
`TauCeti.GlobalNumberFields.finiteWeilIdele` uses `FiniteAdeleRing.mulIndicator` to put
`c⁻¹` at the primes containing `β` and `1` elsewhere. Its inverse is integral, and a
multiple of `c` clears its denominators.

`RingEquiv.finiteWeilIdele_mul_map_mul_mem_integralUnits` computes the product with an
automorphic image modulo integral units. In the CM case,
`TauCeti.GlobalNumberFields.finiteWeilIdele_mul_star_mul_mem_integralUnits` identifies
the product with its conjugate with the principal idele of `c⁻¹` modulo integral units.
Since conjugation preserves the finite modulus and integral units have modulus one, this
determines the square of the finite modulus of the Weil idele.

This construction and normalization follow `New.Parameters.α`, `New.Parameters.inv_alpha_mem`,
`New.Parameters.q₁_mul_alpha_mem`, and `New.Parameters.v_alpha_mul_star_mul_relDifferentGen`
in `grh/src/New/Derivatives/Field/WeilData.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`
(Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
open NumberField NumberField.IsCMField
open scoped NumberField.AdeleRing FiniteAdeleRing

namespace TauCeti.GlobalNumberFields

section DedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
variable {c : R}

/-- The finite Weil idele has component `c⁻¹` at primes containing `β` and `1` elsewhere. -/
noncomputable def finiteWeilIdele (β : R) (hc : c ≠ 0) : 𝔸ᶠ[R, K]ˣ :=
  Units.map (mulIndicator {w : HeightOneSpectrum R | β ∈ w.asIdeal})
    ((unitEmbedding R K (Units.mk0 (algebraMap R K c) (by
      simpa only [map_zero] using (IsFractionRing.injective R K).ne hc)))⁻¹)

open Classical in
/-- Evaluate the finite Weil idele at a finite place. -/
@[simp]
theorem finiteWeilIdele_apply (β : R) (hc : c ≠ 0) (w : HeightOneSpectrum R) :
    (finiteWeilIdele K β hc : 𝔸ᶠ[R, K]) w =
      if β ∈ w.asIdeal then (((algebraMap R K c)⁻¹ : K) : w.adicCompletion K) else 1 := by
  rw [finiteWeilIdele, Units.coe_map, mulIndicator_apply, ← map_inv (unitEmbedding R K)]
  simp only [unitEmbedding_apply, FiniteAdeleRing.algebraMap_apply, Units.val_inv_eq_inv_val,
    Units.val_mk0, Set.mem_ofPred_eq]

/-- The inverse of the finite Weil idele is integral at every finite place. -/
theorem inv_finiteWeilIdele_mem_integralAdeles (β : R) (hc : c ≠ 0) :
    (↑((finiteWeilIdele K β hc)⁻¹) : 𝔸ᶠ[R, K]) ∈ integralAdeles R K := by
  let S : Set (HeightOneSpectrum R) := {w | β ∈ w.asIdeal}
  rw [finiteWeilIdele, ← map_inv (Units.map (mulIndicator (K := K) S)), inv_inv]
  rw [Units.coe_map, unitEmbedding_apply, Units.val_mk0, mulIndicator_mem_integralAdeles]
  exact fun w _ ↦ coe_algebraMap_mem R K w c

/-- Multiplication by an integral multiple of `c` clears the denominators of the
finite Weil idele. -/
theorem algebraMap_mul_finiteWeilIdele_mem_integralAdeles_of_dvd
    (β : R) (hc : c ≠ 0) {q : R} (hq : c ∣ q) :
    algebraMap R 𝔸ᶠ[R, K] q * (finiteWeilIdele K β hc : 𝔸ᶠ[R, K]) ∈
      integralAdeles R K := by
  classical
  refine mem_integralAdeles.mpr fun w ↦ ?_
  rw [FiniteAdeleRing.mul_apply, IsScalarTower.algebraMap_apply R K 𝔸ᶠ[R, K],
    FiniteAdeleRing.algebraMap_apply, finiteWeilIdele_apply]
  split_ifs
  · obtain ⟨t, rfl⟩ := hq
    have hcK : algebraMap R K c ≠ 0 := by
      simpa only [map_zero] using (IsFractionRing.injective R K).ne hc
    have he : algebraMap R K (c * t) * (algebraMap R K c)⁻¹ = algebraMap R K t := by
      rw [map_mul, mul_right_comm, mul_inv_cancel₀ hcK, one_mul]
    rw [← adicCompletion.coe_mul, he]
    exact coe_algebraMap_mem R K w t
  · simpa only [mul_one] using coe_algebraMap_mem R K w q

end DedekindDomain

variable {E : Type*} [Field E] [NumberField E]
variable {β c : 𝓞 E}

/-- Transporting a finite Weil idele by a field automorphism transports both the integer
selecting the places and the integer inverted there. -/
theorem _root_.RingEquiv.map_finiteWeilIdele (σ : E ≃+* E) (β : 𝓞 E) (hc : c ≠ 0) :
    Units.map (finiteAdeleEquiv E E σ).toMonoidHom (finiteWeilIdele E β hc) =
      finiteWeilIdele E (c := RingOfIntegers.mapRingEquiv σ c) (RingOfIntegers.mapRingEquiv σ β)
        (by simpa only [map_zero] using (RingOfIntegers.mapRingEquiv σ).injective.ne hc) := by
  classical
  apply Units.ext
  refine FiniteAdeleRing.ext E fun w ↦ ?_
  have hcoe : (↑(Units.map (finiteAdeleEquiv E E σ).toMonoidHom (finiteWeilIdele E β hc)) :
      𝔸ᶠ[E]) = finiteAdeleEquiv E E σ (finiteWeilIdele E β hc) := Units.coe_map _ _
  obtain ⟨v, rfl⟩ := (equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ)).surjective w
  have hmem : RingOfIntegers.mapRingEquiv σ β ∈
      (equivOfRingEquiv (RingOfIntegers.mapRingEquiv σ) v).asIdeal ↔ β ∈ v.asIdeal := by
    rw [asIdeal_equivOfRingEquiv, ← Ideal.symm_apply_mem_of_equiv_iff, RingEquiv.symm_apply_apply]
  rw [hcoe, finiteAdeleEquiv_apply_eq_adicCompletionCongr σ (σ.valuation_equivOfRingEquiv v),
    finiteWeilIdele_apply, finiteWeilIdele_apply, hmem]
  split_ifs
  · have hinv : σ ((c : E)⁻¹) = ((RingOfIntegers.mapRingEquiv σ c : 𝓞 E) : E)⁻¹ := by
      rw [RingOfIntegers.mapRingEquiv_apply, map_inv₀]
    have hdiag := adicCompletionCongr_algebraMap (σ.valuation_equivOfRingEquiv v) ((c : E)⁻¹)
    rw [hinv] at hdiag
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self_apply]
      using hdiag
  · exact map_one _

/-- If `β` is coprime to its image under `σ`, `c` is associated to its image, and every prime
containing `c` contains `β` or its image, multiplying the finite Weil idele, its image and
the principal idele of `c` gives an everywhere-integral unit. -/
theorem _root_.RingEquiv.finiteWeilIdele_mul_map_mul_mem_integralUnits
    (σ : E ≃+* E) (hc : c ≠ 0) (hβ : IsCoprime β (RingOfIntegers.mapRingEquiv σ β))
    (hassoc : Associated c (RingOfIntegers.mapRingEquiv σ c))
    (hsupport : ∀ w : HeightOneSpectrum (𝓞 E), c ∈ w.asIdeal →
      β ∈ w.asIdeal ∨ RingOfIntegers.mapRingEquiv σ β ∈ w.asIdeal) :
    finiteWeilIdele E β hc *
      Units.map (finiteAdeleEquiv E E σ).toMonoidHom (finiteWeilIdele E β hc) *
      unitEmbedding (𝓞 E) E (Units.mk0 (c : E) (RingOfIntegers.coe_ne_zero_iff.mpr hc)) ∈
        integralUnits (𝓞 E) E := by
  classical
  refine mem_integralUnits_iff.mpr fun w ↦ ?_
  have hcσ : w.intValuation (RingOfIntegers.mapRingEquiv σ c) = w.intValuation c := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu, map_mul, intValuation_eq_one_iff.mpr (w.asIdeal.notMem_of_isUnit u.isUnit), mul_one]
  have hcval := w.intValuation_ne_zero c hc
  simp only [σ.map_finiteWeilIdele, Units.val_mul, FiniteAdeleRing.mul_apply, finiteWeilIdele_apply,
    unitEmbedding_apply, FiniteAdeleRing.algebraMap_apply, Units.val_mk0, map_mul]
  split_ifs with hb hσ hσ <;>
    simp only [valuedAdicCompletion_eq_valuation', map_inv₀, valuation_of_algebraMap,
      hcσ, map_one, mul_one, one_mul, inv_mul_cancel₀ hcval]
  · exact (w.isPrime.notMem_of_isCoprime_of_mem hβ hb hσ).elim
  · exact intValuation_eq_one_iff.mpr fun hm ↦ (hsupport w hm).elim hb hσ

/-- Complex conjugation of a finite Weil idele conjugates its two defining integers. -/
@[simp]
theorem star_finiteWeilIdele [IsCMField E] (β : 𝓞 E) (hc : c ≠ 0) :
    star (finiteWeilIdele E β hc) =
      finiteWeilIdele E (c := ringOfIntegersComplexConj E c) (ringOfIntegersComplexConj E β)
        (by simpa only [map_zero] using (ringOfIntegersComplexConj E).injective.ne hc) := by
  apply Units.ext
  rw [Units.coe_star, ← finiteAdeleConj_apply, finiteAdeleConj_def]
  exact congrArg Units.val ((complexConj E).toRingEquiv.map_finiteWeilIdele β hc)

/-- If `β` is coprime to its conjugate, `c` is associated to its conjugate, and every prime
containing `c` contains `β` or its conjugate, the product of the finite Weil idele, its
conjugate and the principal idele of `c` is an integral unit. -/
theorem finiteWeilIdele_mul_star_mul_mem_integralUnits [IsCMField E]
    (hc : c ≠ 0) (hβ : IsCoprime β (ringOfIntegersComplexConj E β))
    (hassoc : Associated c (ringOfIntegersComplexConj E c))
    (hsupport : ∀ w : HeightOneSpectrum (𝓞 E), c ∈ w.asIdeal →
      β ∈ w.asIdeal ∨ ringOfIntegersComplexConj E β ∈ w.asIdeal) :
    finiteWeilIdele E β hc * star (finiteWeilIdele E β hc) *
      unitEmbedding (𝓞 E) E (Units.mk0 (c : E) (RingOfIntegers.coe_ne_zero_iff.mpr hc)) ∈
        integralUnits (𝓞 E) E := by
  have hstar : Units.map (finiteAdeleEquiv E E (complexConj E).toRingEquiv).toMonoidHom
      (finiteWeilIdele E β hc) = star (finiteWeilIdele E β hc) := by
    apply Units.ext
    rw [Units.coe_star, ← finiteAdeleConj_apply, finiteAdeleConj_def]
    exact Units.coe_map _ _
  rw [← hstar]
  exact (complexConj E).toRingEquiv.finiteWeilIdele_mul_map_mul_mem_integralUnits
    hc hβ hassoc hsupport

end TauCeti.GlobalNumberFields
