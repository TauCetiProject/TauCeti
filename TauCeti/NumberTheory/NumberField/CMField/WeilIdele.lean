/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.AdeleStar
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.MulIndicator

/-!
# Finite Weil ideles for CM fields

The construction `finiteWeilIdele` uses `FiniteAdeleRing.mulIndicator` to place the inverse
of a nonzero integer `c` at the primes containing `β`. The inverse idele is integral, and
multiplication by a multiple of `c` clears the denominators.

The theorem `finiteWeilIdele_mul_star_mul_mem_integralUnits` shows that the finite Weil idele
times its conjugate and `c` is an integral unit. It applies when `β` and its conjugate are
coprime, `c` and its conjugate are associated, and the primes containing `c` are covered by
`β` and its conjugate.

This is the finite-idele construction `New.Parameters.α` and its identities in
`grh/src/New/Derivatives/Field/WeilData.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`
(Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDedekindDomain.FiniteAdeleRing
open scoped NumberField NumberField.AdeleRing

namespace NumberField.IsCMField

variable {E : Type*} [Field E] [NumberField E]
variable {β c : 𝓞 E}

/-- The finite Weil idele has component `c⁻¹` at the primes containing `β`,
and component 1 elsewhere. -/
noncomputable def finiteWeilIdele (β : 𝓞 E) (hc : c ≠ 0) : (𝔸ᶠ[E])ˣ :=
  Units.map (mulIndicator {w : HeightOneSpectrum (𝓞 E) | β ∈ w.asIdeal})
    ((unitEmbedding (𝓞 E) E (Units.mk0 (c : E) (RingOfIntegers.coe_ne_zero_iff.mpr hc)))⁻¹)

open Classical in
/-- The coordinates of the finite Weil idele are the inverse of `c` on the support of
`β` and `1` off that support. -/
@[simp]
theorem finiteWeilIdele_apply (β : 𝓞 E) (hc : c ≠ 0)
    (w : HeightOneSpectrum (𝓞 E)) :
    (finiteWeilIdele β hc : 𝔸ᶠ[E]) w =
      if β ∈ w.asIdeal then (algebraMap E (w.adicCompletion E) (c : E))⁻¹ else 1 := by
  rw [finiteWeilIdele, Units.coe_map, mulIndicator_apply]
  simp only [Set.mem_ofPred_eq, ← coe_unitsProj_apply, map_inv, unitsProj_unitEmbedding,
    Units.val_inv_eq_inv_val, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass]

/-- The inverse of the finite Weil idele is integral at every finite place. -/
theorem inv_finiteWeilIdele_mem_integralAdeles
    (β : 𝓞 E) (hc : c ≠ 0) :
    (↑((finiteWeilIdele β hc)⁻¹) : 𝔸ᶠ[E]) ∈ integralAdeles (𝓞 E) E := by
  classical
  refine mem_integralAdeles.mpr fun w ↦ ?_
  rw [← coe_unitsProj_apply, map_inv, Units.val_inv_eq_inv_val, coe_unitsProj_apply,
    finiteWeilIdele_apply]
  split_ifs
  · rw [inv_inv, w.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers,
      ValuationSubring.algebraMap_apply]
    exact Subtype.property _
  · simp

/-- Multiplication by an integral multiple of `c` clears the denominators of the
finite Weil idele. -/
theorem algebraMap_mul_finiteWeilIdele_mem_integralAdeles_of_dvd
    (β : 𝓞 E) (hc : c ≠ 0) {q : 𝓞 E} (hq : c ∣ q) :
    algebraMap (𝓞 E) (𝔸ᶠ[E]) q * (finiteWeilIdele β hc : 𝔸ᶠ[E]) ∈
      integralAdeles (𝓞 E) E := by
  classical
  refine mem_integralAdeles.mpr fun w ↦ ?_
  have hqmem (t : 𝓞 E) :
      algebraMap E (w.adicCompletion E) (t : E) ∈ w.adicCompletionIntegers E := by
    rw [w.algebraMap_adicCompletion_eq_algebraMap_adicCompletionIntegers,
      ValuationSubring.algebraMap_apply]
    exact Subtype.property _
  have hdiag : (algebraMap (𝓞 E) (𝔸ᶠ[E]) q) w = algebraMap E (w.adicCompletion E) (q : E) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 E) E 𝔸ᶠ[E], FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply]
  rw [FiniteAdeleRing.mul_apply, hdiag, finiteWeilIdele_apply]
  split_ifs
  · obtain ⟨t, rfl⟩ := hq
    have hc' := (algebraMap E (w.adicCompletion E)).injective.ne
      (RingOfIntegers.coe_ne_zero_iff.mpr hc)
    have hct : ((c * t : 𝓞 E) : E) = (c : E) * (t : E) :=
      map_mul (algebraMap (𝓞 E) E) c t
    rw [hct, map_mul, mul_right_comm, mul_inv_cancel₀ hc', one_mul]
    exact hqmem t
  · simpa only [mul_one] using hqmem q

/-- Conjugating a finite Weil idele conjugates the integer specifying the selected places
and the integer inverted at those places. -/
@[simp]
theorem star_finiteWeilIdele [IsCMField E] (β : 𝓞 E) (hc : c ≠ 0) :
    star (finiteWeilIdele β hc) =
      finiteWeilIdele (ringOfIntegersComplexConj E β)
        (by simpa only [map_zero] using (ringOfIntegersComplexConj E).injective.ne hc :
          ringOfIntegersComplexConj E c ≠ 0) := by
  classical
  apply Units.ext
  refine FiniteAdeleRing.ext E fun w ↦ ?_
  have hconjmem : β ∈ w.conjPlace.asIdeal ↔ ringOfIntegersComplexConj E β ∈ w.asIdeal := by
    simp only [← intValuation_lt_one_iff_mem, ← valuation_of_algebraMap (K := E),
      coe_ringOfIntegersComplexConj, ← w.valuation_complexConj (β : E), AlgEquiv.coe_toRingEquiv]
  rw [Units.coe_star, star_apply_eq_adicCompletionCongr (valuation_complexConj w)]
  simp only [finiteWeilIdele_apply, hconjmem, apply_ite, map_inv₀, adicCompletionCongr_algebraMap,
    AlgEquiv.coe_toRingEquiv, ← coe_ringOfIntegersComplexConj, map_one]
  split_ifs <;> rfl

/-- If `β` is coprime to its conjugate, `c` is associated to its conjugate, and every prime
containing `c` contains `β` or its conjugate, the product of the finite Weil idele, its
conjugate and `c` is an integral unit. -/
theorem finiteWeilIdele_mul_star_mul_mem_integralUnits [IsCMField E]
    (hc : c ≠ 0) (hβ : IsCoprime β (ringOfIntegersComplexConj E β))
    (hassoc : Associated c (ringOfIntegersComplexConj E c))
    (hsupport : ∀ w : HeightOneSpectrum (𝓞 E), c ∈ w.asIdeal →
      β ∈ w.asIdeal ∨ ringOfIntegersComplexConj E β ∈ w.asIdeal) :
    finiteWeilIdele β hc * star (finiteWeilIdele β hc) *
      unitEmbedding (𝓞 E) E (Units.mk0 (c : E) (RingOfIntegers.coe_ne_zero_iff.mpr hc)) ∈
        integralUnits (𝓞 E) E := by
  classical
  refine mem_integralUnits_iff.mpr fun w ↦ ?_
  have hval (t : 𝓞 E) :
      Valued.v (algebraMap E (w.adicCompletion E) (t : E)) = w.intValuation t := by
    rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self_apply, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  have hcconj : w.intValuation (ringOfIntegersComplexConj E c) = w.intValuation c := by
    obtain ⟨u, hu⟩ := hassoc
    rw [← hu, map_mul, intValuation_eq_one_iff.mpr (w.asIdeal.notMem_of_isUnit u.isUnit), mul_one]
  have hcval : w.intValuation c ≠ 0 := w.intValuation_ne_zero c hc
  rw [← coe_unitsProj_apply, map_mul, map_mul, unitsProj_unitEmbedding]
  simp only [star_finiteWeilIdele, Units.val_mul, coe_unitsProj_apply, finiteWeilIdele_apply,
    Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, map_mul]
  split_ifs with hb hcb hcb
  · exact (w.isPrime.notMem_of_isCoprime_of_mem hβ hb hcb).elim
  · rw [map_inv₀, hval, map_one, mul_one, inv_mul_cancel₀ hcval]
  · simp only [map_one, one_mul, map_inv₀, hval, hcconj, inv_mul_cancel₀ hcval]
  · rw [map_one, one_mul, one_mul, hval]
    exact intValuation_eq_one_iff.mpr fun hm ↦ (hsupport w hm).elim hb hcb

end NumberField.IsCMField
