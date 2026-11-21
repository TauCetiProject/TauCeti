/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.AffineModel.Extension
-- Proof-only: the affine model `R_t`, Dedekind integral closures, finiteness of normalization
-- without separability, and localization of integral closures.
import TauCeti.FieldTheory.FunctionField.AffineModel.IntegralClosure
import TauCeti.RingTheory.DedekindDomain.IntegralClosure
import TauCeti.RingTheory.IntegralClosure.MvPolynomial
import TauCeti.RingTheory.Localization.Integral

/-!
# The fundamental identity and local integral closure at an arbitrary place

Let `F' / k'` be an extension of the field extension `F / k` in which `F' / F` is finite; of the
constant fields only integrality of `k' / k` is asked.  This file establishes structural properties
of the local integral closure `𝒪'_P = integralClosure 𝒪_P F'` and proves **the fundamental
identity**

`∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]`

at **every** place `P` of `F / k`, upgrading the inequality of
`TauCeti/FieldTheory/FunctionField/Place/Extension/Fibre.lean` and removing the restriction of
`TauCeti/FieldTheory/FunctionField/AffineModel/Extension.lean` to the places of a chosen finite
chart.

Using the local model `𝒪_P ⊆ 𝒪'_P` from
`TauCeti/FieldTheory/FunctionField/Place/Extension/Basic.lean`:

* `𝒪'_P` is always a Dedekind domain with fraction field `F'`
  (`TauCeti.integralClosure.isDedekindDomain`), and equals the intersection of the valuation rings
  `𝒪_{P'}` over all places `P'` lying over `P`
  (`TauCeti.Place.mem_integralClosure_iff_forall_restrict_eq_mem_integers`).
* Whenever `𝒪'_P` is a finite `𝒪_P`-module, the affine-model identity at the centre of `P` on
  `𝒪_P` directly gives the fundamental identity
  (`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_moduleFinite`).
* For `F' / F` separable, finiteness of `𝒪'_P` over `𝒪_P` comes from
  `TauCeti.Place.moduleFinite_integralClosure`, with no hypothesis on `F / k`.
* For `F / k` an algebraic function field with no separability hypothesis, choosing a uniformizer
  `t` at `P` produces the affine model `R_t = integralClosure k[t] F`, whose integral closure in
  `F'` is finite over `R_t`
  (`TauCeti.IsIntegralClosure.finite_integralClosure_integralClosure_adjoin`); localizing at the
  centre of `P` gives finiteness of `𝒪'_P` over `𝒪_P`
  (`TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`), and hence the fundamental
  identity as well.

## Main results

* `TauCeti.Place.moduleFinite_integralClosure_of_isFunctionField`: over an algebraic function field
  `F / k`, `𝒪'_P` is a finite `𝒪_P`-module for any finite extension `F' / F`, without separability.
* `TauCeti.Place.mem_integralClosure_iff_forall_restrict_eq_mem_integers`: for any finite extension
  `F' / F` over an integral constant extension, `𝒪'_P` is the intersection of `𝒪_{P'}` over
  `P' ∣ P`.
* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_moduleFinite`: the
  fundamental identity at an arbitrary place whenever `𝒪'_P` is module-finite over `𝒪_P`.
* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable`: the
  fundamental identity at an arbitrary place, for a separable extension (Stichtenoth,
  Theorem 3.1.11).
* `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField`: the
  fundamental identity at an arbitrary place of an algebraic function field, for any finite
  extension (Stichtenoth, Theorem 3.1.11, which assumes no separability).

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.1.11 and Section III.2.
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u u' v v'

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

open _root_.IntermediateField _root_.IntermediateField.algebraAdjoinAdjoin in
/-- Over an algebraic function field `F / k`, the integral closure `𝒪'_P` of `𝒪_P` in any finite
extension `F' / F` is a finite `𝒪_P`-module, with no separability hypothesis on `F' / F`: it is the
localization at the centre of `P` of the integral closure of `k[t]` in `F'` for a uniformizer `t`
at `P`. -/
theorem moduleFinite_integralClosure_of_isFunctionField {k : Type u} {F : Type v} [Field k]
    [Field F] [Algebra k F] (F' : Type v') [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (P : Place k F) (hF : IsFunctionField k F) :
    Module.Finite P.integers (integralClosure P.integers F') := by
  let _ : Algebra k F' := Algebra.compHom F' (algebraMap k F)
  have : IsScalarTower k F F' := .of_compHom k F F'
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have htP : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have htr : Transcendental k t := P.transcendental_of_ord_ne_zero (by omega)
  have hti : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  have : FiniteDimensional k⟮t⟯ F := hF.finiteDimensional_adjoin htr
  have : FiniteDimensional k⟮t⟯ F' := Module.Finite.trans F F'
  let R := integralClosure (Algebra.adjoin k {t}) F
  have : IsDedekindDomain R := isDedekindDomain_integralClosure_adjoin hF t
  have : IsFractionRing R F := isFractionRing_integralClosure_adjoin hF htr
  have : Module.Finite R (integralClosure R F') :=
    IsIntegralClosure.finite_integralClosure_integralClosure_adjoin k t F'
  have hR : ∀ r : R, algebraMap R F r ∈ P.integers := fun r ↦
    P.mem_integers_iff.mpr
      (P.forall_algebraMap_mem_integers_integralClosure_adjoin_iff.mpr hti r r.property)
  let p : HeightOneSpectrum R := P.center hR
  let _ : Algebra R P.integers := ((algebraMap R F).codRestrict P.integers hR).toAlgebra
  have : IsScalarTower R P.integers F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R P.integers F' := .of_algebraMap_eq fun x ↦
    IsScalarTower.algebraMap_apply R F F' x
  have : IsLocalization p.asIdeal.primeCompl P.integers :=
    P.isLocalization_integers_center hR
  exact TauCeti.finite_integralClosure_of_isLocalization p.asIdeal.primeCompl P.integers F'

section IntegralConstants

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- The scalar tower `k → 𝒪_P → F'` under `algebraIntegersExtension`. -/
private theorem isScalarTower_constants_integers (P : Place k F) :
    IsScalarTower k P.integers F' :=
  .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply P.integers F F',
      ← IsScalarTower.algebraMap_apply k P.integers F, ← IsScalarTower.algebraMap_apply k F F']

variable [Algebra.IsIntegral k k']

/-- The constants `k'` lie in the local integral closure `𝒪'_P` whenever `k' / k` is integral,
endowing `𝒪'_P` with a `k'`-algebra structure. -/
@[instance_reducible]
private noncomputable def algebraConstantsIntegralClosure (P : Place k F) :
    Algebra k' (integralClosure P.integers F') :=
  letI := isScalarTower_constants_integers (F' := F') P
  ((algebraMap k' F').codRestrict (integralClosure P.integers F') fun c ↦
    (mem_integralClosure_iff P.integers F').mpr
      (IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := k) c)).tower_top).toAlgebra

/-- The `k'`-algebra `algebraConstantsIntegralClosure` on `𝒪'_P` is compatible with the inclusion
into `F'`. -/
private theorem isScalarTower_constants_integralClosure (P : Place k F) :
    letI := algebraConstantsIntegralClosure (k' := k') (F' := F') P
    IsScalarTower k' (integralClosure P.integers F') F' :=
  letI := algebraConstantsIntegralClosure (k' := k') (F' := F') P
  .of_algebraMap_eq fun _ ↦ by
    rw [Subalgebra.algebraMap_apply, RingHom.algebraMap_toAlgebra, RingHom.codRestrict_apply]

variable [FiniteDimensional F F']

variable (k') in
/-- For any finite extension `F' / F` over an integral constant-field extension `k' / k`, an
element of `F'` lies in `𝒪'_P` if and only if it is regular at every place of `F' / k'` lying over
`P`. This removes the `IsFunctionField` hypothesis of
`TauCeti.Place.isIntegral_iff_forall_restrict_eq_mem_integers` when `F' / F` is finite. -/
theorem mem_integralClosure_iff_forall_restrict_eq_mem_integers (P : Place k F) {y : F'} :
    y ∈ integralClosure P.integers F' ↔
      ∀ P' : Place k' F', P'.restrict k F = P → y ∈ P'.integers := by
  refine ⟨fun hy P' hP' ↦ ?_, fun hy ↦ ?_⟩
  · subst hP'
    exact algebraMap_mem_integers_of_mem_integralClosure k F P' ⟨y, hy⟩
  · let B := integralClosure P.integers F'
    have : IsDedekindDomain B := TauCeti.integralClosure.isDedekindDomain P.integers F F'
    have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.property
    let _ := algebraConstantsIntegralClosure (k' := k') (F' := F') P
    have := isScalarTower_constants_integralClosure (k' := k') (F' := F') P
    obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := B) F' y fun 𝔓 ↦ by
      have : 𝔓.asIdeal.LiesOver (P.center hR).asIdeal :=
        ⟨(IsLocalRing.eq_maximalIdeal (P.center hR).isMaximal).trans
          (IsLocalRing.eq_maximalIdeal
            (𝔓.asIdeal.isMaximal_under_of_isIntegral_of_isMaximal (R := P.integers)
              (hI := 𝔓.isMaximal))).symm⟩
      have hP' : (ofPrime k' F' 𝔓).restrict k F = P :=
        (restrict_ofPrime k F (P.center hR) 𝔓).trans (ofPrime_center k F P hR)
      simpa only [mem_integers_iff, valuation_ofPrime] using hy (ofPrime k' F' 𝔓) hP'
    exact hb ▸ b.property

variable (k F)

/-- **The fundamental identity** (Stichtenoth, Theorem 3.1.11) at an arbitrary place `P` of
`F / k`, whenever the local integral closure `𝒪'_P` is module-finite over `𝒪_P`:
`∑_{P' ∣ P} e(P' ∣ P) · f(P' ∣ P) = [F' : F]`.

Both `TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable` and
`TauCeti.Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField` are
specializations of this result. -/
theorem sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_moduleFinite
    (P : Place k F) [Module.Finite P.integers (integralClosure P.integers F')]
    {s : Finset (Place k' F')} (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) :
    ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' = Module.finrank F F' := by
  have : IsDedekindDomain (integralClosure P.integers F') :=
    TauCeti.integralClosure.isDedekindDomain P.integers F F'
  have hR : ∀ r : P.integers, algebraMap P.integers F r ∈ P.integers := fun r ↦ r.property
  let _ := algebraConstantsIntegralClosure (k' := k') (F' := F') P
  have := isScalarTower_constants_integralClosure (k' := k') (F' := F') P
  refine sum_ramificationIdx_mul_relativeDegree_eq_finrank (S := integralClosure P.integers F')
    k F (P.center hR) fun P' ↦ ?_
  rw [hs P', ofPrime_center]

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
    ∑ P' ∈ s, ramificationIdx F P' * relativeDegree k F P' = Module.finrank F F' :=
  sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_moduleFinite k F P hs

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
  have := moduleFinite_integralClosure_of_isFunctionField F' P hF
  exact sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_moduleFinite k F P hs

end IntegralConstants

end Place

end TauCeti
