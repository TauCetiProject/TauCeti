/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified
public import TauCeti.RingTheory.DedekindDomain.Different

/-!
# The different exponent of an extension of local fields

Let `L/K` be a separable extension of nonarchimedean local fields whose valuations are
compatible, in the sense of `ValuativeExtension K L`. The different ideal `𝔡(L/K)` of Mathlib's
`differentIdeal 𝒪[K] 𝒪[L]` is a nonzero ideal of the discrete valuation ring `𝒪[L]`, hence a power
of its maximal ideal. This file defines the exponent,

`TauCeti.differentExponent K L : ℕ`,

so that `𝔡(L/K) = 𝓂[L] ^ d(L/K)`, and compares it with the ramification index `e = e(L/K)`:

* `e - 1 ≤ d(L/K)` always;
* `d(L/K) = e - 1` exactly when `L/K` is tamely ramified (`TauCeti.IsTamelyRamified`), that is,
  when the residue characteristic does not divide `e`;
* `e ≤ d(L/K)` exactly when `L/K` is wildly ramified (`TauCeti.IsWildlyRamified`);
* `d(L/K) = 0` exactly when `L/K` is unramified.

These are the local form of Dedekind's different theorem. The residue fields of local fields are
finite, so the residue extension is always separable and tameness is a condition on `e` alone.
The proofs apply the Dedekind-domain statements `pow_sub_one_dvd_differentIdeal` (Mathlib) and
`TauCeti.pow_ramificationIdx_dvd_differentIdeal_iff` to `𝒪[K] ⊆ 𝒪[L]`, through the comparison
`TauCeti.ramificationIndex_eq_ramificationIdx` of the intrinsic ramification index with the
ideal-theoretic one.

## Main definitions

* `TauCeti.differentExponent`: the exponent `d(L/K)` of the maximal ideal of `𝒪[L]` in the
  different ideal.

## Main results

* `TauCeti.isSeparable_fractionRing_integerRing`: separability of `L/K` in the form taken by
  Mathlib's different ideal, on the fraction fields of `𝒪[K]` and `𝒪[L]`.
* `TauCeti.pow_dvd_differentIdeal_iff_le_differentExponent`: the characteristic property,
  `𝓂[L] ^ n ∣ 𝔡(L/K) ↔ n ≤ d(L/K)`.
* `TauCeti.differentIdeal_eq_maximalIdeal_pow`: `𝔡(L/K) = 𝓂[L] ^ d(L/K)`.
* `TauCeti.ramificationIndex_sub_one_le_differentExponent`: `e - 1 ≤ d(L/K)`.
* `TauCeti.ramificationIndex_le_differentExponent_iff`: `e ≤ d(L/K)` exactly in the wild case.
* `TauCeti.differentExponent_eq_ramificationIndex_sub_one_iff`: `d(L/K) = e - 1` exactly in the
  tame case.
* `TauCeti.differentExponent_eq_zero_iff` and `TauCeti.differentIdeal_eq_top_iff`: the different is
  trivial exactly when `L/K` is unramified.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, Proposition 13.
* J. Neukirch, *Algebraic Number Theory*, Chapter III, Theorem 2.6.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

section FractionRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Separability of `L / K` transported to the canonical fraction fields of `𝒪[K]` and `𝒪[L]`,
which is the form of the hypothesis taken by Mathlib's theory of the different ideal. -/
instance isSeparable_fractionRing_integerRing [Algebra.IsSeparable K L] :
    Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L]) := by
  have := isLocalization_integerRing K L
  refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv 𝒪[K] K).symm.toRingEquiv
    (FractionRing.algEquiv 𝒪[L] L).symm.toRingEquiv ?_
  apply IsLocalization.ringHom_ext (nonZeroDivisors 𝒪[K])
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[L] L, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

end FractionRing

/-- The different exponent `d(L/K)` of an extension of nonarchimedean local fields: the
multiplicity of the maximal ideal of `𝒪[L]` in the different ideal `differentIdeal 𝒪[K] 𝒪[L]`.
For `L/K` separable the different ideal is `𝓂[L] ^ d(L/K)`, by
`differentIdeal_eq_maximalIdeal_pow`. -/
def differentExponent : ℕ :=
  multiplicity 𝓂[L] (differentIdeal 𝒪[K] 𝒪[L])

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- The defining formula of `differentExponent`. -/
theorem differentExponent_def :
    differentExponent K L = multiplicity 𝓂[L] (differentIdeal 𝒪[K] 𝒪[L]) := (rfl)

variable [Algebra.IsSeparable K L]

/-- **The characteristic property of the different exponent**: the `n`-th power of the maximal
ideal of `𝒪[L]` divides the different ideal exactly when `n ≤ d(L/K)`. -/
theorem pow_dvd_differentIdeal_iff_le_differentExponent {n : ℕ} :
    𝓂[L] ^ n ∣ differentIdeal 𝒪[K] 𝒪[L] ↔ n ≤ differentExponent K L :=
  (FiniteMultiplicity.of_prime_left
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field 𝒪[L]) inferInstance)
    differentIdeal_ne_bot).pow_dvd_iff_le_multiplicity

/-- The different ideal of a separable extension of nonarchimedean local fields is the
`d(L/K)`-th power of the maximal ideal of `𝒪[L]`. -/
theorem differentIdeal_eq_maximalIdeal_pow :
    differentIdeal 𝒪[K] 𝒪[L] = 𝓂[L] ^ differentExponent K L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (differentIdeal_ne_bot (A := 𝒪[K]) (B := 𝒪[L])) hϖ
  rw [← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq] at hn
  rw [differentExponent_def, hn, multiplicity_pow_self_of_prime
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field 𝒪[L]) inferInstance)]

/-- **The first half of Dedekind's different theorem**: `e(L/K) - 1 ≤ d(L/K)`. -/
theorem ramificationIndex_sub_one_le_differentExponent :
    ramificationIndex K L - 1 ≤ differentExponent K L := by
  rw [← pow_dvd_differentIdeal_iff_le_differentExponent]
  exact pow_sub_one_dvd_differentIdeal 𝒪[K] 𝓂[L] _ (IsDiscreteValuationRing.not_a_field 𝒪[K])
    (map_maximalIdeal_eq_maximalIdeal_pow K L).symm.dvd

attribute [local instance] Ideal.Quotient.field in
/-- **The different exponent reaches the ramification index exactly in the wild case**:
`e(L/K) ≤ d(L/K)` if and only if the residue characteristic divides `e(L/K)`. -/
theorem ramificationIndex_le_differentExponent_iff :
    ramificationIndex K L ≤ differentExponent K L ↔ IsWildlyRamified K L := by
  rw [← pow_dvd_differentIdeal_iff_le_differentExponent, isWildlyRamified_iff,
    ramificationIndex_eq_ramificationIdx,
    pow_ramificationIdx_dvd_differentIdeal_iff 𝒪[K] (IsDiscreteValuationRing.not_a_field 𝒪[K])]
  -- `𝓀[K]` is by definition the quotient `𝒪[K] ⧸ 𝓂[K]` of the Dedekind-domain statement, so that
  -- quotient is finite and has the characteristic of `𝓀[K]`. Finite residue fields are perfect,
  -- so the residue extension is separable.
  have : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  have : Algebra.IsSeparable (𝒪[K] ⧸ 𝓂[K]) (𝒪[L] ⧸ 𝓂[L]) := inferInstance
  simp only [this, not_true_eq_false, false_or]
  exact ringChar.spec 𝓀[K] _

/-- **Dedekind's different theorem, the tame case**: `d(L/K) = e(L/K) - 1` exactly when `L/K` is
tamely ramified. -/
theorem differentExponent_eq_ramificationIndex_sub_one_iff :
    differentExponent K L = ramificationIndex K L - 1 ↔ IsTamelyRamified K L := by
  have h := ramificationIndex_sub_one_le_differentExponent K L
  have he := ramificationIndex_pos (K := K) (L := L)
  rw [← not_isWildlyRamified_iff, ← ramificationIndex_le_differentExponent_iff]
  omega

/-- **The different of a local extension is trivial exactly when the extension is
unramified**: `d(L/K) = 0` if and only if `L/K` is unramified. -/
theorem differentExponent_eq_zero_iff : differentExponent K L = 0 ↔ IsUnramified K L := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
  · have := ramificationIndex_sub_one_le_differentExponent K L
    have := ramificationIndex_pos (K := K) (L := L)
    exact (isUnramified_iff_ramificationIndex_eq_one K L).2 (by omega)
  · rw [(differentExponent_eq_ramificationIndex_sub_one_iff K L).2
      (IsUnramified.isTamelyRamified K L), IsUnramified.ramificationIndex_eq_one]

/-- The different ideal of a separable extension of nonarchimedean local fields is the unit ideal
exactly when the extension is unramified. -/
theorem differentIdeal_eq_top_iff : differentIdeal 𝒪[K] 𝒪[L] = ⊤ ↔ IsUnramified K L := by
  rw [← differentExponent_eq_zero_iff, differentIdeal_eq_maximalIdeal_pow]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, pow_zero, Ideal.one_eq_top]⟩
  by_contra hd
  exact (maximalIdeal.isMaximal 𝒪[L]).ne_top (eq_top_mono (Ideal.pow_le_self hd) h)

end TauCeti
