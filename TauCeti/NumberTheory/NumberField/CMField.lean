/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# The Hasse unit index of a CM field

For a number field `K` with maximal real subfield `K⁺`, Mathlib defines the real-unit subgroup
`NumberField.IsCMField.realUnits K ≤ (𝓞 K)ˣ` and the Hasse unit index
`NumberField.IsCMField.indexRealUnits K = [(𝓞 K)ˣ : realUnits K ⊔ torsion K]`. When `K` is a CM
number field, this index is `1` or `2`.

This file supplies the general algebraic and ramification criteria for `indexRealUnits K = 1`,
together with the induced unit-quotient isomorphism:

* If `K` is totally real, then `K⁺ = ⊤`, so every unit is real and `indexRealUnits K = 1`.
* Whenever `indexRealUnits K = 1` and `H ≤ (𝓞 K)ˣ` contains all roots of unity, the inclusion of
  real units induces an isomorphism `(𝓞 K⁺)ˣ ⧸ H⁺ ≃* (𝓞 K)ˣ ⧸ H` and equality of indices
  `[(𝓞 K⁺)ˣ : H⁺] = [(𝓞 K)ˣ : H]` (Sharifi, Lemma 4.2.19).
* For a CM number field `K`, `indexRealUnits K = 1` holds if and only if `u / conj u` is a square
  in `torsion K` for every unit `u : (𝓞 K)ˣ`.
* If a prime ideal `P` of `𝓞 K` has even ramification index over `𝓞 K⁺` and an element `π : 𝓞 K`
  satisfies `conj π = η * π` for some root of unity `η : torsion K` with `Odd (multiplicity P (π))`,
  then `η` does not lie in the image of `u ↦ u / conj u`, forcing `indexRealUnits K = 1`.

## Main definitions and results

* `TauCeti.NumberField.IsCMField.realUnits_eq_top_of_isTotallyReal`: in a totally real field,
  every integral unit is real.
* `TauCeti.NumberField.IsCMField.indexRealUnits_eq_one_of_isTotallyReal`: every totally real field
  has Hasse unit index `1`.
* `TauCeti.NumberField.IsCMField.quotientRealUnitsEquiv`: when `indexRealUnits K = 1` and
  `torsion K ≤ H`, the real unit quotient `(𝓞 K⁺)ˣ ⧸ H⁺` is isomorphic to `(𝓞 K)ˣ ⧸ H`.
* `TauCeti.NumberField.IsCMField.index_comap_realUnits_eq`: equality of indices
  `[(𝓞 K⁺)ˣ : H⁺] = [(𝓞 K)ˣ : H]` under the same hypotheses.
* `TauCeti.NumberField.IsCMField.coe_unitsComplexConj`: coercion of `unitsComplexConj K u` to
  `𝓞 K` agrees with `ringOfIntegersComplexConj K`.
* `TauCeti.NumberField.IsCMField.ringOfIntegersComplexConj_torsion`: complex conjugation acts by
  inversion on torsion units in `𝓞 K`.
* `TauCeti.NumberField.IsCMField.ringOfIntegersComplexConj_torsion_sub_one`: the identity
  `conj (ζ - 1) = (-ζ⁻¹) * (ζ - 1)` for a torsion unit `ζ`.
* `TauCeti.NumberField.IsCMField.indexRealUnits_eq_one_iff`: for a CM number field,
  `indexRealUnits K = 1` iff every `unitsMulComplexConjInv K u` is a square in `torsion K`.
* `TauCeti.NumberField.IsCMField.not_mem_range_unitsMulComplexConjInv_of_odd_multiplicity`:
  parity obstruction at a prime with even ramification index over `𝓞 K⁺`.
* `TauCeti.NumberField.IsCMField.indexRealUnits_eq_one_of_odd_multiplicity`: ramification
  criterion for `indexRealUnits K = 1`.

## References

* R. Sharifi, *Iwasawa theory*, Lemmas 4.2.17 and 4.2.19.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.12.
-/

public section

open NumberField NumberField.IsCMField NumberField.Units

open scoped NumberField

namespace TauCeti.NumberField.IsCMField

section TotallyReal

/-- **In a totally real field, every integral unit is real.** Since `maximalRealSubfield K = ⊤`,
every unit of `𝓞 K` lies in the image of `(𝓞 (maximalRealSubfield K))ˣ`. -/
theorem realUnits_eq_top_of_isTotallyReal (K : Type*) [Field K] [IsTotallyReal K] :
    realUnits K = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [mem_realUnits_iff]
  have htop : maximalRealSubfield K = ⊤ := IsTotallyReal.maximalRealSubfield_eq_top
  let x : 𝓞 (maximalRealSubfield K) :=
    ⟨⟨(u : K), htop.symm ▸ trivial⟩, isIntegral_algebraMap_iff.mp u.1.isIntegral_coe⟩
  have hx : algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x = u := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply _ (maximalRealSubfield K) K]
    rfl
  have hxu : IsUnit x :=
    IsUnit.of_map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) x (hx ▸ u.isUnit)
  exact ⟨hxu.unit, by simpa using hx⟩

/-- **Every totally real field has Hasse unit index one.** -/
theorem indexRealUnits_eq_one_of_isTotallyReal (K : Type*) [Field K] [IsTotallyReal K] :
    indexRealUnits K = 1 :=
  Subgroup.index_eq_one.mpr (by rw [realUnits_eq_top_of_isTotallyReal K, top_sup_eq])

end TotallyReal

section Quotient

private theorem mk'_comp_realUnits_surjective (K : Type*) [Field K]
    (hindex : indexRealUnits K = 1) (H : Subgroup (𝓞 K)ˣ) (htors : torsion K ≤ H) :
    Function.Surjective ((QuotientGroup.mk' H).comp
      (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) :
        𝓞 (maximalRealSubfield K) →* 𝓞 K))) := by
  have htop : realUnits K ⊔ torsion K = ⊤ := Subgroup.index_eq_one.mp hindex
  intro q
  induction q using QuotientGroup.induction_on with
  | H u =>
    have hu : u ∈ realUnits K ⊔ torsion K := htop.symm ▸ Subgroup.mem_top u
    obtain ⟨r, hr, ζ, hζ, rfl⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨v, rfl⟩ := hr
    refine ⟨v, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq.mpr (by simpa using htors hζ)).symm

private theorem mk'_comp_realUnits_ker (K : Type*) [Field K] (H : Subgroup (𝓞 K)ˣ) :
    ((QuotientGroup.mk' H).comp
        (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) :
          𝓞 (maximalRealSubfield K) →* 𝓞 K))).ker =
      H.comap (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) :
        𝓞 (maximalRealSubfield K) →* 𝓞 K)) := by
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- **Real-to-full unit quotient isomorphism (Sharifi, Lemma 4.2.19).** When `indexRealUnits K = 1`
and `H ≤ (𝓞 K)ˣ` contains all roots of unity, the inclusion of real units induces an isomorphism
`(𝓞 K⁺)ˣ ⧸ H⁺ ≃* (𝓞 K)ˣ ⧸ H`, where `H⁺` is the preimage of `H` in `(𝓞 K⁺)ˣ`. -/
noncomputable def quotientRealUnitsEquiv (K : Type*) [Field K]
    (hindex : indexRealUnits K = 1) (H : Subgroup (𝓞 K)ˣ) (htors : torsion K ≤ H) :
    (𝓞 (maximalRealSubfield K))ˣ ⧸
        H.comap (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) :
          𝓞 (maximalRealSubfield K) →* 𝓞 K)) ≃*
      (𝓞 K)ˣ ⧸ H :=
  (QuotientGroup.quotientMulEquivOfEq (mk'_comp_realUnits_ker K H).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (mk'_comp_realUnits_surjective K hindex H htors))

/-- Applying `quotientRealUnitsEquiv` to a coset of a real unit gives the coset of its image in
`(𝓞 K)ˣ`. -/
@[simp]
theorem quotientRealUnitsEquiv_mk (K : Type*) [Field K]
    (hindex : indexRealUnits K = 1) (H : Subgroup (𝓞 K)ˣ) (htors : torsion K ≤ H)
    (u : (𝓞 (maximalRealSubfield K))ˣ) :
    quotientRealUnitsEquiv K hindex H htors (QuotientGroup.mk u) =
      QuotientGroup.mk
        (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) :
          𝓞 (maximalRealSubfield K) →* 𝓞 K) u) :=
  (rfl)

/-- Applying the inverse of `quotientRealUnitsEquiv` to the coset of a real unit recovers its
coset in `(𝓞 K⁺)ˣ`. -/
@[simp]
theorem quotientRealUnitsEquiv_symm_mk_map (K : Type*) [Field K]
    (hindex : indexRealUnits K = 1) (H : Subgroup (𝓞 K)ˣ) (htors : torsion K ≤ H)
    (u : (𝓞 (maximalRealSubfield K))ˣ) :
    (quotientRealUnitsEquiv K hindex H htors).symm
        (QuotientGroup.mk
          (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) :
            𝓞 (maximalRealSubfield K) →* 𝓞 K) u)) =
      QuotientGroup.mk u :=
  (MulEquiv.symm_apply_eq _).mpr (quotientRealUnitsEquiv_mk K hindex H htors u).symm

/-- **Real and full unit indices coincide when the Hasse unit index is one.** If
`indexRealUnits K = 1` and `torsion K ≤ H`, then the preimage of `H` in `(𝓞 K⁺)ˣ` has the same
index as `H` in `(𝓞 K)ˣ`. -/
theorem index_comap_realUnits_eq (K : Type*) [Field K]
    (hindex : indexRealUnits K = 1) (H : Subgroup (𝓞 K)ˣ) (htors : torsion K ≤ H) :
    (H.comap (Units.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) :
      𝓞 (maximalRealSubfield K) →* 𝓞 K))).index =
      H.index :=
  Nat.card_congr (quotientRealUnitsEquiv K hindex H htors).toEquiv

end Quotient

section CMField

/-- Coercing `unitsComplexConj K u` to `𝓞 K` agrees with applying `ringOfIntegersComplexConj K`. -/
theorem coe_unitsComplexConj (K : Type*) [Field K] [CharZero K] [IsCMField K]
    [Algebra.IsIntegral ℚ K] (u : (𝓞 K)ˣ) :
    ((unitsComplexConj K u : (𝓞 K)ˣ) : 𝓞 K) = ringOfIntegersComplexConj K (u : 𝓞 K) :=
  RingOfIntegers.ext (by simp)

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- **Complex conjugation acts by inversion on torsion units in `𝓞 K`.** -/
@[simp]
theorem ringOfIntegersComplexConj_torsion (ζ : torsion K) :
    ringOfIntegersComplexConj K ((ζ : (𝓞 K)ˣ) : 𝓞 K) = (((ζ : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
  rw [← coe_unitsComplexConj, unitsComplexConj_torsion, Subgroup.coe_inv]

/-- **Complex conjugation on `ζ - 1` for a torsion unit `ζ`.** Multiplying `ζ - 1` by `-ζ⁻¹`
gives `conj (ζ - 1) = ζ⁻¹ - 1`. -/
theorem ringOfIntegersComplexConj_torsion_sub_one (ζ : torsion K) :
    ringOfIntegersComplexConj K (((ζ : (𝓞 K)ˣ) : 𝓞 K) - 1) =
      ((-(ζ : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (((ζ : (𝓞 K)ˣ) : 𝓞 K) - 1) := by
  rw [map_sub, map_one, ringOfIntegersComplexConj_torsion, Units.val_neg]
  have hmul : (((ζ : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((ζ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  linear_combination hmul

/-- **Characterization of Hasse unit index one.** A CM number field `K` has `indexRealUnits K = 1`
if and only if `u / conj u` is a square in `torsion K` for every unit `u : (𝓞 K)ˣ`. -/
theorem indexRealUnits_eq_one_iff :
    indexRealUnits K = 1 ↔ ∀ u : (𝓞 K)ˣ, IsSquare (unitsMulComplexConjInv K u) := by
  rw [Subgroup.index_eq_one, Subgroup.eq_top_iff']
  constructor
  · intro h u
    obtain ⟨r, hr, ζ, hζ, rfl⟩ := Subgroup.mem_sup.mp (h u)
    refine ⟨⟨ζ, hζ⟩, ?_⟩
    have hrk : unitsMulComplexConjInv K r = 1 := by
      rwa [← MonoidHom.mem_ker, unitsMulComplexConjInv_ker]
    rw [map_mul, hrk, one_mul, unitsMulComplexConjInv_apply_torsion K ⟨ζ, hζ⟩, sq]
  · intro h u
    obtain ⟨ζ, hζ⟩ := h u
    have hmem : u * (ζ : (𝓞 K)ˣ)⁻¹ ∈ realUnits K := by
      rw [← unitsMulComplexConjInv_ker, MonoidHom.mem_ker, map_mul, map_inv, hζ,
        unitsMulComplexConjInv_apply_torsion K ζ, sq, mul_inv_cancel]
    have hu : (u * (ζ : (𝓞 K)ˣ)⁻¹) * (ζ : (𝓞 K)ˣ) = u := inv_mul_cancel_right _ _
    exact hu ▸ Subgroup.mul_mem_sup hmem ζ.2

/-- **Valuation-parity obstruction to hitting a torsion factor with `u / conj u`.** Let `P` be a
prime ideal of `𝓞 K` whose ramification index over `𝓞 K⁺` is even. If `π : 𝓞 K` has odd
`P`-multiplicity and satisfies `conj π = η * π` for a root of unity `η : torsion K`, then `η` is
not in the image of `unitsMulComplexConjInv K`. -/
theorem not_mem_range_unitsMulComplexConjInv_of_odd_multiplicity
    {P : Ideal (𝓞 K)} [P.IsPrime]
    (he : Even (P.ramificationIdx (𝓞 (maximalRealSubfield K))))
    {π : 𝓞 K} {η : torsion K}
    (hconj : ringOfIntegersComplexConj K π = ((η : (𝓞 K)ˣ) : 𝓞 K) * π)
    (hodd : Odd (multiplicity P (Ideal.span {π}))) :
    η ∉ (unitsMulComplexConjInv K).range := by
  have hP0 : P ≠ ⊥ := fun h ↦ by simp [h] at he
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_zero, ← Submodule.zero_eq_bot] at hodd
    simp at hodd
  rintro ⟨v, hv⟩
  have hvc : unitsComplexConj K v = (η : (𝓞 K)ˣ)⁻¹ * v := by
    have hv' : v * (unitsComplexConj K v)⁻¹ = (η : (𝓞 K)ˣ) := congrArg Subtype.val hv
    rw [mul_inv_eq_iff_eq_mul] at hv'
    exact eq_inv_mul_iff_mul_eq.mpr hv'.symm
  -- Multiply `π` by `v` to obtain a real associate `x = v * π`.
  have hxconj : ringOfIntegersComplexConj K ((v : 𝓞 K) * π) = (v : 𝓞 K) * π := by
    rw [map_mul, hconj, ← coe_unitsComplexConj, hvc, Units.val_mul]
    calc
      (((η : (𝓞 K)ˣ)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K) * (((η : (𝓞 K)ˣ) : 𝓞 K) * π)
          = ((((η : (𝓞 K)ˣ)⁻¹ * (η : (𝓞 K)ˣ) : (𝓞 K)ˣ) : 𝓞 K)) * ((v : 𝓞 K) * π) := by
              rw [Units.val_mul]; ring
      _ = (v : 𝓞 K) * π := by simp
  obtain ⟨y, hy⟩ := (ringOfIntegersComplexConj_eq_self_iff K _).mp hxconj
  have hy0 : Ideal.span {y} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    rintro rfl
    rw [map_zero] at hy
    exact mul_ne_zero v.ne_zero hπ0 hy.symm
  have hspan : Ideal.span {π} =
      Ideal.map (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) (Ideal.span {y}) := by
    rw [Ideal.map_span, Set.image_singleton, hy, Ideal.span_singleton_mul_left_unit v.isUnit]
  -- Compute the `P`-multiplicity of `span {π}` via the ramification index of `P` over `𝓞 K⁺`.
  set q := P.under (𝓞 (maximalRealSubfield K))
  have hq0 : q ≠ ⊥ := Ideal.IsIntegral.under_ne_bot (𝓞 (maximalRealSubfield K)) hP0
  have hqprime : Prime q := Ideal.prime_of_isPrime hq0 inferInstance
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 inferInstance
  have hemult := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul
    hy0 hqprime.irreducible hPprime.irreducible hP0
  rw [← hspan, Ideal.ramificationIdx'_eq_ramificationIdx q P hq0,
    (FiniteMultiplicity.of_prime_left hPprime (by simp [hπ0])).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left hqprime hy0).emultiplicity_eq_multiplicity,
    ← Nat.cast_mul, Nat.cast_inj] at hemult
  exact Nat.not_odd_iff_even.mpr (hemult ▸ he.mul_right _) hodd

/-- **Ramification criterion for Hasse unit index one.** If a CM number field `K` has a prime ideal
`P` with even ramification index over `𝓞 K⁺` and an element `π : 𝓞 K` of odd `P`-multiplicity such
that `conj π = η * π` for some root of unity `η : torsion K`, then `indexRealUnits K = 1`. -/
theorem indexRealUnits_eq_one_of_odd_multiplicity
    {P : Ideal (𝓞 K)} [P.IsPrime]
    (he : Even (P.ramificationIdx (𝓞 (maximalRealSubfield K))))
    {π : 𝓞 K} {η : torsion K}
    (hconj : ringOfIntegersComplexConj K π = ((η : (𝓞 K)ˣ) : 𝓞 K) * π)
    (hodd : Odd (multiplicity P (Ideal.span {π}))) :
    indexRealUnits K = 1 := by
  have hne : (unitsMulComplexConjInv K).range ≠ ⊤ := fun htop ↦
    not_mem_range_unitsMulComplexConjInv_of_odd_multiplicity K he hconj hodd
      (htop.symm ▸ Subgroup.mem_top η)
  have hidx : (unitsMulComplexConjInv K).range.index ≠ 1 := by
    rwa [ne_eq, Subgroup.index_eq_one]
  have hmul := indexRealUnits_mul_eq K
  rcases indexRealUnits_eq_one_or_two K with h | h
  · exact h
  · exfalso
    rw [h] at hmul
    exact hidx (by omega)

end CMField

end TauCeti.NumberField.IsCMField
