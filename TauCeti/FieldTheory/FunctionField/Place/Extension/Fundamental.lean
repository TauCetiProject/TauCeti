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
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
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

* `TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional`: for any
  finite field extension `F' / F` over an integral constant extension `k' / k`, an element of `F'`
  is integral over `P.integers` if and only if it belongs to `P'.integers` for every place `P'` of
  `F' / k'` lying over `P` (requiring neither `IsFunctionField` nor separability of `F' / F`).
* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`: the
  fundamental identity at an arbitrary place, for a separable extension (Stichtenoth,
  Theorem 3.1.11).
* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField`: the
  fundamental identity at an arbitrary place of an algebraic function field, for any finite
  extension (Stichtenoth, Theorem 3.1.11, which assumes no separability).

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

omit [FiniteDimensional F F'] in
/-- Constants of `k'` lie in `integralClosure P.integers F'` because `k' / k` is integral, giving
the local model `integralClosure P.integers F'` its `k'`-algebra structure. -/
@[instance_reducible]
private noncomputable def algebraIntegralClosure (P : Place k F) :
    Algebra k' (integralClosure P.integers F') :=
  ((algebraMap k' F').codRestrict (integralClosure P.integers F')
    (isIntegral_integers_algebraMap (k := k) P)).toAlgebra

omit [FiniteDimensional F F'] in
private theorem isScalarTower_algebraIntegralClosure (P : Place k F) :
    letI := algebraIntegralClosure (k := k) (k' := k') (F := F) (F' := F') P
    IsScalarTower k' (integralClosure P.integers F') F' :=
  letI := algebraIntegralClosure (k := k) (k' := k') (F := F) (F' := F') P
  .of_algebraMap_eq fun _ ↦ rfl

variable {k F} in
/-- **The integral closure of `P.integers` in a finite field extension `F' / F` over an integral
constant extension `k' / k` is the intersection of the valuation rings above `P`.** Unlike
`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers`, no `IsFunctionField` hypothesis (and
no separability of `F' / F`) is required. -/
theorem isIntegral_iff_forall_restrict_eq_mem_integers_of_finiteDimensional
    (P : Place k F) {x : F'} :
    IsIntegral P.integers x ↔ ∀ P' : Place k' F', P'.restrict k F = P → x ∈ P'.integers := by
  refine ⟨fun hx P' hP' ↦ ?_, fun h ↦ ?_⟩
  · subst hP'
    exact algebraMap_mem_integers_of_mem_integralClosure k F P' ⟨x, hx⟩
  -- By Krull–Akizuki (`TauCeti.integralClosure.isDedekindDomain`), `integralClosure P.integers F'`
  -- is a Dedekind domain with fraction field `F'` even without separability, and every height-one
  -- prime of it contracts to the unique maximal ideal of `P.integers` and therefore comes from a
  -- place of `F' / k'` lying over `P`.
  have : IsDedekindDomain (integralClosure P.integers F') :=
    integralClosure.isDedekindDomain P.integers F F'
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  let _ : Algebra k' (integralClosure P.integers F') :=
    algebraIntegralClosure (k := k) (k' := k') (F := F) (F' := F') P
  have : IsScalarTower k' (integralClosure P.integers F') F' :=
    isScalarTower_algebraIntegralClosure (k := k) (k' := k') (F := F) (F' := F') P
  have hpmax : (P.center hR).asIdeal = IsLocalRing.maximalIdeal P.integers :=
    IsLocalRing.eq_maximalIdeal (P.center hR).isMaximal
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one
    (R := integralClosure P.integers F') F' x fun 𝔓 ↦ by
      have : 𝔓.asIdeal.IsMaximal := 𝔓.isMaximal
      have hunder : 𝔓.asIdeal.under P.integers = (P.center hR).asIdeal :=
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under P.integers 𝔓.asIdeal)).trans
          hpmax.symm
      have : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal := ⟨hunder.symm⟩
      have hres : (ofPrime k' F' 𝔓).restrict k F = P :=
        (restrict_ofPrime k F (P.center hR) 𝔓).trans (ofPrime_center k F P hR)
      simpa only [mem_integers_iff, valuation_ofPrime] using h (ofPrime k' F' 𝔓) hres
  exact hy ▸ y.2

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
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.2
  let _ : Algebra k' (integralClosure P.integers F') :=
    algebraIntegralClosure (k := k) (k' := k') (F := F) (F' := F') P
  have : IsScalarTower k' (integralClosure P.integers F') F' :=
    isScalarTower_algebraIntegralClosure (k := k) (k' := k') (F := F) (F' := F') P
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

end Place

end TauCeti
