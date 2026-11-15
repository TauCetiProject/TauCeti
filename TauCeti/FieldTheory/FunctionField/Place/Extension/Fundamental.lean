/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
-- Proof-only: the affine model `R_t`, Dedekind integral closures, the finiteness of normalization
-- without separability, and the tower law for integral closures.
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import TauCeti.RingTheory.IntegralClosure.Transfer

/-!
# The fundamental identity at an arbitrary place

Let `F' / k'` be an extension of the field extension `F / k` in which `F' / F` is finite; of the
constant fields only integrality of `k' / k` is asked.  This file proves **the fundamental
identity**

`∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]`

at **every** place `P` of `F / k`, upgrading the inequality of
`TauCeti/FieldTheory/FunctionField/Place/Extension/Fibre.lean` and removing the restriction of
`TauCeti/FieldTheory/FunctionField/AffineModel/Extension.lean` to the places of a chosen finite
chart.  It is proved in two forms, with incomparable hypotheses: for `F' / F` separable, and for
`F / k` an algebraic function field with no separability.

Both reduce to the affine-model identity, which needs an affine model of `F` carrying `P` whose
integral closure in `F'` is a finite module over it — the hypothesis of Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank`.

* For `F' / F` separable, the model is the valuation ring `𝒪_P` itself, a discrete valuation ring
  with fraction field `F`: separability makes its integral closure in `F'` a finite
  `𝒪_P`-module, by Mathlib's `IsIntegralClosure.finite`.  No hypothesis on `F / k` is used.  The
  local model is the one set up in `TauCeti/FieldTheory/FunctionField/Place/Extension/Basic.lean`;
  the action of `𝒪_P` on `F'` and the scalar tower it sits in are not global instances, so they
  are reinstalled here.
* For `F / k` a function field, the model is the integral closure `R_t` of `k[t]` in `F` for a
  uniformizer `t` at `P`.  As `t` has no pole at `P`, the place `P` lies on the finite chart of
  `R_t`; as `t` is transcendental, the integral closure of `k[t]` in the finite extension `F'` of
  `k(t)` is a finite `k[t]`-module with no separability hypothesis
  (`TauCeti.IsIntegralClosure.finite_adjoin`), hence a finite `R_t`-module.
  The valuation ring `𝒪_P` is not used as the model in this case: the integral closure of a
  discrete valuation ring in an inseparable extension need not be finite in general, and it is
  the finiteness of the normalization of `k[t]` that supplies finiteness here.

## Main results

* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`: the
  fundamental identity at an arbitrary place, for a separable extension (Stichtenoth,
  Theorem 3.1.11).
* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField`: the
  fundamental identity at an arbitrary place of an algebraic function field, for any finite
  extension (Stichtenoth, Theorem 3.1.11, which assumes no separability).
* `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional`: for any
  finite extension `F' / F` with `k' / k` integral, the integral closure of `𝒪_P` in `F'` is the
  intersection of the valuation rings of the places above `P`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.1.11.
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']
variable [FiniteDimensional F F'] [Algebra.IsIntegral k k']

variable (k F)

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- **The fundamental identity** (Stichtenoth, Theorem 3.1.11) at an arbitrary place `P` of
`F / k`, for an extension `F' / k'` whose extension of function fields `F' / F` is finite and
**separable**: the ramification indices and relative degrees of the places of `F' / k'` lying
over `P` satisfy `∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]`.

The finite set `s` is the fibre of `TauCeti.Place.restrict` over `P`, which is finite by
`TauCeti.Place.finite_setOf_restrict_eq`.

Separability is the hypothesis of Mathlib's finiteness theorem for integral closures, and is used
only there. When `F / k` is an algebraic function field the identity holds for every finite
extension; that is
`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField`. -/
theorem sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable [Algebra.IsSeparable F F']
    (P : Place k F)
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) :
    ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' = Module.finrank F F' := by
  -- The valuation ring of `P` is an affine model of `F / k` carrying `P` itself: it is a discrete
  -- valuation ring, hence Dedekind, and `F` is its fraction field.
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ by
    rw [ValuationSubring.algebraMap_apply]
    exact r.2
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  -- The integral closure `S` of `𝒪_P` in `F'` is the matching affine model of `F' / k'`: it
  -- contains the constants `k'`, because they are integral over `k ⊆ 𝒪_P`.
  have hk' : ∀ c : k', algebraMap k' F' c ∈ integralClosure P.integers F' := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' (integralClosure P.integers F') :=
    ((algebraMap k' F').codRestrict (integralClosure P.integers F') hk').toAlgebra
  have : IsScalarTower k' (integralClosure P.integers F') F' := .of_algebraMap_eq fun _ ↦ rfl
  -- `P` is the place of the maximal ideal of `𝒪_P`, so the affine-model identity applies to it.
  refine sum_ramificationIdx_mul_relativeDegree_eq_finrank (S := integralClosure P.integers F')
    k F (P.center hR) fun P' ↦ ?_
  rw [hs P', ofPrime_center]

open _root_.IntermediateField _root_.IntermediateField.algebraAdjoinAdjoin in
/-- **The fundamental identity** (Stichtenoth, Theorem 3.1.11) at an arbitrary place `P` of an
algebraic function field `F / k`, for an extension `F' / k'` whose extension of function fields
`F' / F` is finite, **with no separability hypothesis**: the ramification indices and relative
degrees of the places of `F' / k'` lying over `P` satisfy
`∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]`.

The finite set `s` is the fibre of `TauCeti.Place.restrict` over `P`, which is finite by
`TauCeti.Place.finite_setOf_restrict_eq`.

For a separable `F' / F` the identity holds without assuming that `F / k` is a function field;
that is `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`. -/
theorem sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField
    (hF : IsFunctionField k F) (P : Place k F) {s : Finset (Place k' F')}
    (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) :
    ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' = Module.finrank F F' := by
  -- A uniformizer `t` at `P` is transcendental over `k` and has no pole at `P`.
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have htP : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by omega)
  have hti : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin htr
  have : FiniteDimensional k⟮t⟯ F' := Module.Finite.trans F F'
  -- The integral closure `R` of `k[t]` in `F` is an affine model of `F / k`, and the integral
  -- closure `S` of `R` in `F'` is one of `F' / k'`.
  let R := integralClosure (Algebra.adjoin k {t}) F
  have : IsDedekindDomain R := isDedekindDomain_integralClosure_adjoin hF t
  have : IsFractionRing R F := isFractionRing_integralClosure_adjoin hF htr
  let S := integralClosure R F'
  have : IsDedekindDomain S := integralClosure.isDedekindDomain R F F'
  have : IsFractionRing S F' := integralClosure.isFractionRing_of_finite_extension F F'
  -- `S` is also the integral closure of `k[t]` in `F'`, hence finite over `k[t]` and over `R`.
  have : Module.Finite R S :=
    IsIntegralClosure.finite_integralClosure_integralClosure_adjoin k t F'
  -- `P` is finite on `R`, since `t` has no pole at `P`.
  have hR : ∀ r : R, algebraMap R F r ∈ P.integers := fun r ↦
    P.mem_integers_iff.mpr
      (P.forall_algebraMap_mem_integers_integralClosure_adjoin_iff.mpr hti r r.2)
  -- `S` contains the constants `k'`, because they are integral over `k ⊆ R`.
  have hk' : ∀ c : k', algebraMap k' F' c ∈ S := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' S := ((algebraMap k' F').codRestrict S hk').toAlgebra
  have : IsScalarTower k' S F' := .of_algebraMap_eq fun _ ↦ rfl
  -- `P` is the place of its centre on `R`, so the affine-model identity applies to it.
  refine sum_ramificationIdx_mul_relativeDegree_eq_finrank (R := R) (S := S) k F
    (P.center hR) fun P' ↦ ?_
  rw [hs P', ofPrime_center]

variable {k F} (k') in
/-- **The integral closure of `𝒪_P` is the intersection of the valuation rings above `P`** for any
finite extension `F' / F` with `k' / k` integral, with no function-field or separability
hypothesis: `𝒪'_P` is a Dedekind domain (`TauCeti.integralClosure.isDedekindDomain`) whose height
one primes all lie over the maximal ideal of `𝒪_P`, hence define places of `F' / k'` over `P`.
Compare `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`, which drops finiteness of
`F' / F` in favour of `IsFunctionField k' F'`. -/
theorem isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional (P : Place k F)
    {x : F'} :
    IsIntegral P.integers x ↔ ∀ P' : Place k' F', P'.restrict k F = P → x ∈ P'.integers := by
  have := Algebra.IsIntegral.of_finite F F'
  refine ⟨fun hx P' hP' ↦ P'.mem_integers_of_isIntegral (fun a ↦ ?_) hx, fun h ↦ ?_⟩
  · subst hP'
    exact (mem_integers_restrict_iff k F P' (a : F)).mp a.2
  let S := integralClosure P.integers F'
  have : IsDedekindDomain S := TauCeti.integralClosure.isDedekindDomain P.integers F F'
  have : IsFractionRing S F' := integralClosure.isFractionRing_of_finite_extension F F'
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  have : IsScalarTower k P.integers F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']
  have hk' : ∀ c : k', algebraMap k' F' c ∈ S := fun c ↦
    (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top
  let _ : Algebra k' S := ((algebraMap k' F').codRestrict S hk').toAlgebra
  have : IsScalarTower k' S F' := .of_algebraMap_eq fun _ ↦ rfl
  have hxS : x ∈ Set.range (algebraMap S F') := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := S) F' x fun 𝔓 ↦ ?_
    have hmax : (𝔓.asIdeal.under P.integers).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔓.asIdeal
    have hp : (P.center hR).asIdeal = IsLocalRing.maximalIdeal P.integers := by
      ext r
      rw [mem_center_asIdeal, mem_maximalIdeal_iff_valuation_lt_one]
      exact Iff.rfl
    have hlies : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal :=
      ⟨hp.trans (IsLocalRing.eq_maximalIdeal hmax).symm⟩
    have hP' : (ofPrime k' F' 𝔓).restrict k F = P := by
      rw [restrict_ofPrime k F (P.center hR) 𝔓, ofPrime_center]
    simpa [valuation_ofPrime] using (ofPrime k' F' 𝔓).mem_integers_iff.mp (h _ hP')
  obtain ⟨y, rfl⟩ := hxS
  exact y.2

end Place

end TauCeti
