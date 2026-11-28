/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.HostField
public import TauCeti.NumberTheory.NumberField.Global.Adeles.GaloisAction
import TauCeti.NumberTheory.ModularForms.ThetaLift.WeilIdele
import TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Field
import TauCeti.NumberTheory.NumberField.Cyclotomic.Different
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Cyclotomic.RealDerivative
import TauCeti.NumberTheory.NumberField.IntegralSqrt

/-!
# The finite Weil idele of the cyclotomic host

The cyclotomic derivative generates the relative different and divides the cyclotomic
order. The quadratic half-integer splits its prime support into two conjugate halves.
The finite Weil idele is the inverse derivative on one half, and `1` off that half.
In particular its inverse and its multiple by the cyclotomic order are integral.

The relative different formula is the one used in `New.Parameters.relDifferent_spec`
(`New/Derivatives/Field/PrimeDecomposition.lean`); the normalization is that of
`New.Parameters.α` and `New.Parameters.v_alpha_mul_star_mul_relDifferentGen`
(`New/Derivatives/Field/WeilData.lean`), in lsernau/grh-lean (`72fead1`).
-/

public section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField NumberField.IsCMField
  Polynomial
open scoped NumberField.AdeleRing

namespace TauCeti.OneSidedBound.Parameters

private theorem exists_weil_support (P : Parameters) (s : ℕ) {x : 𝓞 (P.hostField s)}
    (hx : x ∣ (P.q₁ s : 𝓞 (P.hostField s))) :
    ∃ β : 𝓞 (P.hostField s),
      ((β : P.hostField s) : ℂ) = (1 + (P.baseRoot : ℂ)) / 2 ∧
      IsCoprime β (ringOfIntegersComplexConj (P.hostField s) β) ∧
      β * ringOfIntegersComplexConj (P.hostField s) β ∈ (Ideal.span {x}).radical := by
  let E := P.hostField s
  let φ : E →+* ℂ := algebraMap E ℂ
  let δ : E := algebraMap P.baseField E P.baseRoot
  have hd := P.d_mod_eight
  have hδ : δ ^ 2 = algebraMap ℤ E (-(P.d : ℤ)) := by simp [δ, ← map_pow]
  let β : 𝓞 E := ⟨(1 + δ) / 2, isIntegral_one_add_div_two_of_sq_eq hδ (by omega)⟩
  have he : φ (β : E) = (1 + (P.baseRoot : ℂ)) / 2 := by
    have hβ : (β : E) = (1 + δ) / 2 := (rfl)
    simp [hβ, φ, δ, map_ofNat]
  have hconj : φ ((ringOfIntegersComplexConj E β : 𝓞 E) : E) =
      (1 - (P.baseRoot : ℂ)) / 2 := by
    rw [coe_ringOfIntegersComplexConj, complexEmbedding_complexConj, he, P.coe_baseRoot]
    simp [QuadraticAlgebra.conj_sqrtRadicand (neg_nonpos.mpr (Nat.cast_nonneg _)), sub_eq_add_neg,
      map_ofNat]
  have htrace : β + ringOfIntegersComplexConj E β = 1 := by
    apply RingOfIntegers.ext
    apply φ.injective
    simp only [RingOfIntegers.coe_eq_algebraMap, map_add, map_one] at he hconj ⊢
    rw [he, hconj]
    ring
  have hnorm : β * ringOfIntegersComplexConj E β = (((P.d + 1) / 4 : ℕ) : 𝓞 E) := by
    apply RingOfIntegers.ext
    apply φ.injective
    have hs : (P.baseRoot : ℂ) ^ 2 = -(P.d : ℂ) := by
      rw [P.coe_baseRoot]
      simp [sq]
    have h4 : 4 * ((P.d + 1) / 4) = P.d + 1 := by omega
    have h4C : (4 : ℂ) * (((P.d + 1) / 4 : ℕ) : ℂ) = (P.d : ℂ) + 1 := by exact_mod_cast h4
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_natCast] at he hconj ⊢
    rw [he, hconj]
    linear_combination -hs / 4 - h4C / 4
  refine ⟨β, he, ⟨1, 1, by simpa only [one_mul] using htrace⟩, ?_⟩
  rw [Ideal.mem_radical_iff]
  refine ⟨P.q₁ s, Ideal.mem_span_singleton.mpr (hx.trans ?_)⟩
  rw [hnorm, ← Nat.cast_pow]
  exact Nat.cast_dvd_cast (P.q₁_dvd_norm_pow s)

open Classical in
/-- In the cyclotomic host, take the inverse relative different generator at the finite
places containing the quadratic half-integer and `1` elsewhere. The resulting idele has
integral inverse, the cyclotomic order clears its denominators, and its product with its
conjugate and the derivative is a unit at every finite place. -/
theorem exists_host_weilFiniteIdele (P : Parameters) (s : ℕ) :
    let E := P.hostField s
    let x := aeval (P.isPrimitiveRoot_hostRoot s).toInteger (cyclotomic (P.q₁ s) ℤ).derivative
    differentIdeal (𝓞 P.baseField) (𝓞 E) = Ideal.span {x} ∧
    ∃ β : 𝓞 E, ((β : E) : ℂ) = (1 + (P.baseRoot : ℂ)) / 2 ∧
      ∃ α : 𝔸ᶠ[E]ˣ,
        (∀ v : HeightOneSpectrum (𝓞 E), (α : 𝔸ᶠ[E]) v =
          if β ∈ v.asIdeal then ((x : E)⁻¹ : v.adicCompletion E) else 1) ∧
        (↑(α⁻¹) : 𝔸ᶠ[E]) ∈ integralAdeles (𝓞 E) E ∧
        algebraMap (𝓞 E) 𝔸ᶠ[E] (P.q₁ s) * (α : 𝔸ᶠ[E]) ∈ integralAdeles (𝓞 E) E ∧
        ∀ v : HeightOneSpectrum (𝓞 E),
          Valued.v (((α : 𝔸ᶠ[E]) *
            GlobalNumberFields.finiteAdeleEquiv E E (complexConj E).toRingEquiv ↑α *
            algebraMap (𝓞 E) 𝔸ᶠ[E] x) v) = 1 := by
  classical
  intro E x
  have hz := P.isPrimitiveRoot_hostRoot s
  have hdisc : (discr P.baseField).natAbs = P.d := by
    have h₄ : P.d % 4 = 3 := by have := P.d_mod_eight; omega
    have he := Multiquadratic.oddPrimeDiscriminant_of_mod_four_eq_three h₄
    have h := Multiquadratic.discr_adjoin_singleton_eq_primeDiscriminant
      (Multiquadratic.isPrimeDiscriminant_oddPrimeDiscriminant P.prime_d P.odd_d)
      (x := (P.baseRoot : ℂ)) (by
        rw [Multiquadratic.primeDiscriminantRadicand_oddPrimeDiscriminant P.odd_d, he]
        rw [P.coe_baseRoot]
        simp [sq])
    let e := IntermediateField.equivOfEq (P.baseField_eq_adjoin.trans (by rw [P.coe_baseRoot]) :
      P.baseField = IntermediateField.adjoin ℚ {(P.baseRoot : ℂ)})
    let : NumberField (IntermediateField.adjoin ℚ {(P.baseRoot : ℂ)}) :=
      { to_finiteDimensional := Module.Finite.of_injective e.symm.toLinearMap e.symm.injective }
    rw [discr_eq_discr_of_algEquiv _ e, h, he, Int.natAbs_neg, Int.natAbs_natCast]
  have hrel : differentIdeal (𝓞 P.baseField) (𝓞 E) = Ideal.span {x} :=
    hz.differentIdeal_eq_span_derivative_cyclotomic_of_coprime_discr
      (hdisc ▸ (P.coprime_q₁_d s).symm)
  refine ⟨hrel, ?_⟩
  have hdvd : x ∣ (P.q₁ s : 𝓞 E) := Ideal.mem_span_singleton.mp <|
    hrel ▸ IsCyclotomicExtension.natCast_mem_differentIdeal P.baseField E (P.q₁ s)
  obtain ⟨β, hβ, hcop, hsupport⟩ := P.exists_weil_support s hdvd
  let σ := ringOfIntegersComplexConj E
  have h₄ : 4 ∣ P.q₁ s := ((by decide : 4 ∣ 18480).trans P.dvd_q₀).trans (P.q₀_dvd_q₁ s)
  obtain ⟨u, _, hu⟩ := hz.toInteger_isPrimitiveRoot.exists_unit_mul_cyclotomic_derivative_real h₄
  have hreal : σ ((u : 𝓞 E) * x) = (u : 𝓞 E) * x := by
    apply RingOfIntegers.ext
    simp only [σ, coe_ringOfIntegersComplexConj, RingOfIntegers.coe_eq_algebraMap, map_mul]
    have hcoe : algebraMap (𝓞 E) E x =
        aeval (hz.toInteger : E) (cyclotomic (P.q₁ s) ℤ).derivative :=
      (aeval_algHom_apply (IsScalarTower.toAlgHom ℤ (𝓞 E) E) _ _).symm
    simpa only [hcoe, map_mul] using hu
  rw [map_mul] at hreal
  have hσ : Associated (σ x) x :=
    (associated_unit_mul_right (σ x) (σ (u : 𝓞 E)) (u.isUnit.map σ)).trans
      (hreal ▸ associated_unit_mul_left x (u : 𝓞 E) u.isUnit)
  exact ⟨β, hβ, (complexConj E).toRingEquiv.exists_weilFiniteIdele hcop hσ hsupport hdvd⟩

end TauCeti.OneSidedBound.Parameters
