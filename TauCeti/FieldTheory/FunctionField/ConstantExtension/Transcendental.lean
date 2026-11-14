/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.Separable.Regular
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.FieldTheory.FunctionField.Different.Tame
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.RingTheory.Localization.FractionRing

/-!
# Transcendental linearly disjoint constant extensions of function fields

Let `F' = F · k'` be the compositum of a function field `F / k` with an arbitrary — possibly
transcendental — extension `k' / k`, linearly disjoint over `k`. Unlike an algebraic extension of
constants, `F' / F` is no longer integral, so a place of `F'` need not restrict to a place of `F`:
its valuation ring may contain all of `F` (the generic point of the curve over `k`). Nevertheless,
both directions of the ramification and constant-field comparison survive.

First, multiplication `F ⊗[k] k' → F'` is injective, making `F'` the fraction field of `F ⊗[k] k'`
and hence of `A ⊗[k] k'` whenever `F = Frac(A)`. Tensoring further with an algebraic closure of
`k'` shows that a geometrically reduced field with exact constants keeps exact constants after any
linearly disjoint extension `k' / k`.

Second, for every place `P` of `F / k`, `𝒪_P ⊗[k] k'` has fraction field `F'` and admits a quotient
`F_P ⊗[k] k'` in which a uniformizer `t` of `P` maps to `0`. Extending the localization at a
maximal ideal above `ker(𝒪_P ⊗[k] k' → F_P ⊗[k] k')` to a valuation subring of `F'` produces a
place `P'` of `F' / k'` whose valuation ring contains `𝒪_P` and whose order restricts to a positive
multiple of `ord_P`. Over a perfect field `k`, comparing the order of a coordinate on `RatFunc`
shows that `e(P ∣ k(t))` divides `e(P' ∣ k'(t))` and `P'` lies over infinity or `X - a` (`a ∈ k`)
exactly when `P` does.

Third, in the opposite direction, a place `P'` of `F' / k'` intersects `RatFunc k` either in the
whole field `RatFunc k` or in the valuation ring of a unique place `Q` of `RatFunc k`. In the first
case any `RatFunc k`-basis of `F` transports to an integral basis at `P'` with unit discriminant;
in the second case, if `Q` is unramified in `F`, the local integral basis of `F` at `Q` has unit
discriminant (`TauCeti.Place.ord_discr_localIntegralBasis_eq_zero`) and transports to a basis of
`F'` integral at `P'` with unit discriminant. Either way `d(P' ∣ k'(t)) = 0`, so
`e(P' ∣ k'(t)) = 1`.

## Main results

* `TauCeti.productMap_injective_of_linearDisjoint` and
  `TauCeti.isFractionRing_tensorProduct_of_linearDisjoint`: `F ⊗[k] k'` embeds into `F'` and
  `F' = Frac(A ⊗[k] k')` whenever `F = Frac(A)`.
* `TauCeti.IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint`: exact constants
  persist under any linearly disjoint constant extension of a geometrically reduced field.
* `TauCeti.Place.exists_place_integers_le_and_ord_eq_mul_of_linearDisjoint`: every place `P` of
  `F / k` is dominated by a place `P'` of `F' / k'` whose order restricts to a positive multiple of
  `ord_P`.
* `TauCeti.Place.exists_place_ramificationIdx_ratFunc_dvd_of_linearDisjoint`: over a perfect base
  field, `P'` preserves `∞` and rational places `X - a` (`a ∈ k`), with
  `e(P ∣ k(X)) ∣ e(P' ∣ k'(X))`.
* `TauCeti.Place.ord_discr_localIntegralBasis_eq_zero`: at an unramified place `P`, the local
  integral basis has unit discriminant.
* `TauCeti.Place.ramificationIdx_ratFunc_eq_one_of_linearDisjoint`: a place `P'` of `F' / k'` is
  unramified over `k'(X)` whenever any place of `k(X)` induced by `P'` is unramified in `F`.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge Algebra Geom. **45** (2004), no. 1, 253–265,
  Section 2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections 3.3–3.6.
-/

public section

open Polynomial
open scoped IntermediateField TensorProduct nonZeroDivisors

namespace TauCeti

section TensorAndConstants

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **Linear disjointness makes multiplication `F ⊗[k] k' → F'` injective**, with no algebraicity
hypothesis on `k' / k`. -/
theorem productMap_injective_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F) :
    Function.Injective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')) := by
  let fF := IsScalarTower.toAlgHom k F F'
  let fk := IsScalarTower.toAlgHom k k' F'
  let e : F ⊗[k] k' ≃ₐ[k] fF.range ⊗[k] fk.range :=
    Algebra.TensorProduct.congr (AlgEquiv.ofInjectiveField fF) (AlgEquiv.ofInjectiveField fk)
  have hdisj : fF.range.LinearDisjoint fk.range := by
    rw [← AlgHom.fieldRange_toSubalgebra]
    exact Subalgebra.LinearDisjoint.symm H
  have hcomp : Algebra.TensorProduct.productMap fF fk =
      (Algebra.TensorProduct.productMap fF.range.val fk.range.val).comp e.toAlgHom :=
    Algebra.TensorProduct.ext' fun _ _ ↦ rfl
  rw [hcomp, AlgHom.coe_comp]
  exact hdisj.injective.comp e.injective

/-- **The linearly disjoint compositum `F · k'` is the fraction field of `F ⊗[k] k'`.** -/
theorem isFractionRing_field_tensorProduct_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    letI := (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F') : F ⊗[k] k' →+* F').toAlgebra
    IsFractionRing (F ⊗[k] k') F' := by
  set π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra (F ⊗[k] k') F' := (π : F ⊗[k] k' →+* F').toAlgebra
  have hπ : Function.Injective (algebraMap (F ⊗[k] k') F') :=
    productMap_injective_of_linearDisjoint H
  have : FaithfulSMul (F ⊗[k] k') F' := (faithfulSMul_iff_algebraMap_injective _ _).mpr hπ
  have hring : π.range.toSubring =
      Subring.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k' F')) := by
    change (π : F ⊗[k] k' →+* F').range = _
    rw [RingHom.range_eq_map, ← Algebra.TensorProduct.closure_range_union_range_eq_top k F k',
      RingHom.map_closure, Set.image_union, ← Set.range_comp, ← Set.range_comp]
    congr 2 <;> ext <;> simp [π]
  refine IsFractionRing.of_field (F ⊗[k] k') F' fun z ↦ ?_
  have hz : z ∈ Subfield.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k' F')) := by
    have htop := congrArg IntermediateField.toSubfield h
    rw [constantCompositum_def, IntermediateField.adjoin_toSubfield] at htop
    simp [htop]
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hz
  rw [← hring] at ha hb
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x, y, rfl⟩

/-- **The linearly disjoint compositum `F · k'` is the fraction field of `A ⊗[k] k'`** for every
`k`-algebra `A` with fraction field `F`, with no algebraicity assumption on `k' / k`. -/
theorem isFractionRing_tensorProduct_of_linearDisjoint {A : Type*} [CommRing A]
    [Algebra k A] [Algebra A F] [IsScalarTower k A F] [IsFractionRing A F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    letI := (((Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k k'))) :
        A ⊗[k] k' →+* F').toAlgebra
    IsFractionRing (A ⊗[k] k') F' := by
  set π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  set ρ := Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A F) (AlgHom.id k k')
  let _ := ((π.comp ρ : A ⊗[k] k' →ₐ[k] F') : A ⊗[k] k' →+* F').toAlgebra
  have hπ := productMap_injective_of_linearDisjoint H
  have hρ : Function.Injective ρ :=
    Module.Flat.rTensor_preserves_injective_linearMap (IsScalarTower.toAlgHom k A F).toLinearMap
      (IsFractionRing.injective A F)
  have hψ : Function.Injective (algebraMap (A ⊗[k] k') F') := hπ.comp hρ
  let _ : Algebra (A ⊗[k] k') (F ⊗[k] k') := (ρ : A ⊗[k] k' →+* F ⊗[k] k').toAlgebra
  have : IsScalarTower A (A ⊗[k] k') (F ⊗[k] k') := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, ρ]
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] k') A⁰) (F ⊗[k] k') :=
    IsLocalization.tensorProduct_tensorProduct k k' A⁰ F
      (by ext; simp [RingHom.algebraMap_toAlgebra, ρ])
  let _ : Algebra (F ⊗[k] k') F' := (π : F ⊗[k] k' →+* F').toAlgebra
  have : IsScalarTower (A ⊗[k] k') (F ⊗[k] k') F' := .of_algebraMap_eq fun _ ↦ rfl
  have : IsFractionRing (F ⊗[k] k') F' := isFractionRing_field_tensorProduct_of_linearDisjoint H h
  have : NoZeroDivisors (A ⊗[k] k') := hψ.noZeroDivisors _ (map_zero _) (map_mul _)
  exact IsFractionRing.of_isLocalization_of_isFractionRing
    (Algebra.algebraMapSubmonoid (A ⊗[k] k') A⁰) (F ⊗[k] k') F'
    (IsLocalization.le_nonZeroDivisors_of_nontrivial _ (F ⊗[k] k'))

/-- **Exact constants persist under any linearly disjoint constant extension of a geometrically
reduced field.** The extension `k' / k` may be transcendental. -/
theorem _root_.IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint
    (hex : IsIntegrallyClosedIn k F) [Algebra.IsGeometricallyReduced k F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (h : constantCompositum F k' F' = ⊤) :
    IsIntegrallyClosedIn k' F' := by
  let Ω := AlgebraicClosure k'
  let _ : Algebra k' (F ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k k' (F ⊗[k] k') := Algebra.TensorProduct.right_isScalarTower
  let R := F ⊗[k] k'
  let π := Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
    (IsScalarTower.toAlgHom k k' F')
  let _ : Algebra R F' := (π : R →+* F').toAlgebra
  have : IsScalarTower k' R F' := .of_algebraMap_eq fun c ↦ by
    symm
    change π (1 ⊗ₜ c) = algebraMap k' F' c
    simp [π]
  have : IsFractionRing R F' := isFractionRing_field_tensorProduct_of_linearDisjoint H h
  have : IsDomain (F ⊗[k] Ω) := isDomain_tensorProduct_of_isGeometricallyReduced hex Ω
  have : IsDomain (Ω ⊗[k] F) := (Algebra.TensorProduct.comm k F Ω).symm.toMulEquiv.isDomain
  let e₁ : R ⊗[k'] Ω ≃ₐ[k'] Ω ⊗[k'] (k' ⊗[k] F) :=
    (Algebra.TensorProduct.comm k' R Ω).trans
      (Algebra.TensorProduct.congr AlgEquiv.refl
        { (Algebra.TensorProduct.comm k F k') with commutes' := fun _ ↦ rfl })
  let e : R ⊗[k'] Ω ≃ₐ[k] Ω ⊗[k] F :=
    (e₁.restrictScalars k).trans
      ((Algebra.TensorProduct.cancelBaseChange k k' Ω Ω F).restrictScalars k)
  have : IsDomain (R ⊗[k'] Ω) := e.toMulEquiv.isDomain
  let _ := (Algebra.TensorProduct.map (Algebra.ofId R F') (AlgHom.id k' Ω)).toAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid (R ⊗[k'] Ω) R⁰) (F' ⊗[k'] Ω) := by
    refine IsLocalization.tensorProduct_tensorProduct k' Ω R⁰ F' ?_
    ext x
    simp [RingHom.algebraMap_toAlgebra]
  let M := Algebra.algebraMapSubmonoid (R ⊗[k'] Ω) R⁰
  have hM : M ≤ (R ⊗[k'] Ω)⁰ :=
    IsLocalization.le_nonZeroDivisors_of_nontrivial M (F' ⊗[k'] Ω)
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hM
  have : IsDomain (F' ⊗[k'] Ω) :=
    (IsLocalization.algEquiv M (Localization M) (F' ⊗[k'] Ω)).symm.toMulEquiv.isDomain
  have hbot : algebraicClosure k' F' = ⊥ :=
    algebraicClosure_eq_bot_of_isDomain_tensorProduct Ω
  refine isIntegrallyClosedIn_iff.mpr ⟨(algebraMap k' F').injective, fun {z} hz ↦ ?_⟩
  have hz' : z ∈ (⊥ : IntermediateField k' F') := hbot ▸ mem_algebraicClosure_iff.mpr hz.isAlgebraic
  exact IntermediateField.mem_bot.mp hz'

end TensorAndConstants

namespace Place

section DominatingPlace

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- Every place `P` of a function field `F / k` is dominated in a linearly disjoint constant
compositum `F' = F · k'` by a proper valuation subring `A` containing `k'` and `𝒪_P` in which the
inverse of a given uniformizer `t` of `P` does not lie. -/
private theorem exists_valuationSubring_dominating_of_linearDisjoint
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤) (P : Place k F)
    {t : F} (ht : P.valuation.IsUniformizer t) :
    ∃ A : ValuationSubring F',
      (∀ x ∈ P.integers, algebraMap F F' x ∈ A) ∧
      (∀ c : k', algebraMap k' F' c ∈ A) ∧ A ≠ ⊤ ∧
      (algebraMap F F' t)⁻¹ ∉ A := by
  let φ : P.integers ⊗[k] k' →ₐ[k] F' :=
    (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k F F')
      (IsScalarTower.toAlgHom k k' F')).comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k P.integers F) (AlgHom.id k k'))
  let _ : Algebra (P.integers ⊗[k] k') F' := (φ : P.integers ⊗[k] k' →+* F').toAlgebra
  have : IsFractionRing (P.integers ⊗[k] k') F' :=
    isFractionRing_tensorProduct_of_linearDisjoint H hcomp
  have hφ : Function.Injective φ := IsFractionRing.injective (P.integers ⊗[k] k') F'
  let e : P.integers ⊗[k] k' ≃+* φ.range.toSubring := (AlgEquiv.ofInjective φ hφ).toRingEquiv
  let ψ : P.integers ⊗[k] k' →ₐ[k] P.ResidueField ⊗[k] k' :=
    Algebra.TensorProduct.map
      { toRingHom := IsLocalRing.residue P.integers
        commutes' := fun _ ↦ rfl }
      (AlgHom.id k k')
  have : Nontrivial (P.ResidueField ⊗[k] k') :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_left k P.ResidueField k'
      (Algebra.linearMap k k') (algebraMap k k').injective
  let ψ' : φ.range.toSubring →+* P.ResidueField ⊗[k] k' := ψ.toRingHom.comp e.symm.toRingHom
  have hker : RingHom.ker ψ' ≠ ⊤ := fun h ↦
    one_ne_zero (α := P.ResidueField ⊗[k] k')
      (ψ'.map_one.symm.trans (RingHom.mem_ker.mp ((Ideal.eq_top_iff_one _).mp h)))
  obtain ⟨A, hSA, hnonu⟩ := Ideal.image_subset_nonunits_valuationSubring (RingHom.ker ψ') hker
  have htmem : t ∈ P.integers :=
    P.mem_integers_iff_ord_nonneg.mpr (by rw [P.isUniformizer_iff_ord_eq_one.mp ht]; norm_num)
  have htker : e (⟨t, htmem⟩ ⊗ₜ 1) ∈ RingHom.ker ψ' := by
    rw [RingHom.mem_ker]
    have hres : IsLocalRing.residue P.integers ⟨t, htmem⟩ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, P.mem_maximalIdeal_iff_ord_pos ht.ne_zero,
        P.isUniformizer_iff_ord_eq_one.mp ht]
      exact zero_lt_one
    have hzero : ({ toRingHom := IsLocalRing.residue P.integers
                    commutes' := fun _ ↦ rfl } : P.integers →ₐ[k] P.ResidueField)
        ⟨t, htmem⟩ = 0 := hres
    simp [ψ', ψ, hzero]
  have ht_nonu : algebraMap F F' t ∈ A.nonunits := by
    have hmem := hnonu ⟨e (⟨t, htmem⟩ ⊗ₜ 1), htker, rfl⟩
    have hcoe : ((e (⟨t, htmem⟩ ⊗ₜ 1) : φ.range.toSubring) : F') = algebraMap F F' t := by
      change ((AlgEquiv.ofInjective φ hφ) (⟨t, htmem⟩ ⊗ₜ 1) : F') = algebraMap F F' t
      rw [AlgEquiv.ofInjective_apply]
      simp [φ]
    exact hcoe ▸ hmem
  have htinv : (algebraMap F F' t)⁻¹ ∉ A :=
    (A.mem_nonunits_iff_or.mp ht_nonu).resolve_left ((_root_.map_ne_zero _).mpr ht.ne_zero)
  refine ⟨A, fun x hx ↦ ?_, fun c ↦ ?_, fun htop ↦ htinv (htop ▸ trivial), htinv⟩
  · exact hSA ⟨⟨x, hx⟩ ⊗ₜ 1, by simp [φ]⟩
  · exact hSA ⟨1 ⊗ₜ c, by simp [φ]⟩

/-- **Every place of `F / k` is dominated by a place of `F' / k'` in a linearly disjoint constant
compositum**, whose order restricts to a positive integer multiple of `ord_P`. -/
theorem exists_place_integers_le_and_ord_eq_mul_of_linearDisjoint
    (hF : IsFunctionField k F)
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤) (P : Place k F) :
    ∃ (P' : Place k' F') (m : ℕ), 0 < m ∧
      (∀ x ∈ P.integers, algebraMap F F' x ∈ P'.integers) ∧
      ∀ x : F, P'.ord (algebraMap F F' x) = m * P.ord x := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  obtain ⟨A, hPA, hk', hAne, htinv⟩ :=
    exists_valuationSubring_dominating_of_linearDisjoint H hcomp P ht
  let P' : Place k' F' :=
    ofValuationSubring (hF.of_constantCompositum_eq_top_of_linearDisjoint H hcomp) hk' hAne
  have hAeq : P'.integers = A := integers_ofValuationSubring _ hk' hAne
  have hPP' : ∀ x ∈ P.integers, algebraMap F F' x ∈ P'.integers := fun x hx ↦ hAeq ▸ hPA x hx
  have ht0' : algebraMap F F' t ≠ 0 := (_root_.map_ne_zero _).mpr ht.ne_zero
  have htpos : 0 < P'.ord (algebraMap F F' t) := by
    have htinv' : (algebraMap F F' t)⁻¹ ∉ P'.integers := hAeq ▸ htinv
    rw [P'.mem_integers_iff_ord_nonneg, P'.ord_inv] at htinv'
    omega
  refine ⟨P', (P'.ord (algebraMap F F' t)).toNat, by omega, hPP', fun x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨u, hu_eq⟩ := P.exists_eq_zpow_mul_unit ht hx0
  have hu_mem : algebraMap F F' (u : F) ∈ P'.integers := hPP' _ u.1.2
  have hu_inv : (algebraMap F F' (u : F))⁻¹ ∈ P'.integers := by
    have huinv_mem : (u : F)⁻¹ ∈ P.integers := by
      have hmul : (u : F) * ((u⁻¹ : P.integersˣ) : F) = 1 :=
        congrArg Subtype.val (Units.mul_inv u)
      rw [inv_eq_of_mul_eq_one_right hmul]
      exact (u⁻¹ : P.integersˣ).1.2
    rw [← map_inv₀]
    exact hPP' _ huinv_mem
  have hu_ord : P'.ord (algebraMap F F' (u : F)) = 0 := by
    have h1 := P'.mem_integers_iff_ord_nonneg.mp hu_mem
    have h2 := P'.mem_integers_iff_ord_nonneg.mp hu_inv
    rw [P'.ord_inv] at h2
    omega
  have hu0' : algebraMap F F' (u : F) ≠ 0 :=
    (_root_.map_ne_zero _).mpr fun h0 ↦ u.ne_zero (Subtype.ext h0)
  conv_lhs => rw [hu_eq]
  rw [map_mul, map_zpow₀, P'.ord_mul (zpow_ne_zero _ ht0') hu0', P'.ord_zpow, hu_ord, add_zero,
    Int.toNat_of_nonneg htpos.le, mul_comm]

end DominatingPlace

section RatFuncRamificationDvd

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

/-- Compatibility of `X` makes the two paths `k[X] → k(X) → F → F'` and
`k[X] → k'[X] → k'(X) → F'` agree. -/
private theorem algebraMap_ratFunc_polynomial_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (p : k[X]) :
    algebraMap F F' (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) p)) =
      algebraMap (RatFunc k') F' (algebraMap k'[X] (RatFunc k') (p.map (algebraMap k k'))) := by
  have h₁ := aeval_algHom_apply
    ((IsScalarTower.toAlgHom k F F').comp (IsScalarTower.toAlgHom k (RatFunc k) F)) RatFunc.X p
  have h₂ := aeval_algHom_apply (IsScalarTower.toAlgHom k' (RatFunc k') F') RatFunc.X
    (p.map (algebraMap k k'))
  simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
    RatFunc.aeval_X_left_eq_algebraMap] at h₁ h₂
  rw [← h₁, ← h₂, hX, aeval_map_algebraMap]

private theorem infty_iff_ord_X_lt_zero {K : Type*} [Field K] (Q : Place K (RatFunc K)) :
    Q = infty K ↔ Q.ord RatFunc.X < 0 := by
  refine ⟨by rintro rfl; simp [ord_infty], fun hlt ↦ ?_⟩
  by_contra hne
  exact (Q.mem_integers_iff_ord_nonneg.mp
    (not_not.mp (mt X_notMem_integers_iff_eq_infty.mp hne))).not_gt hlt

private theorem ramificationIdx_ratFunc_dvd_of_ord_eq_mul [PerfectField k]
    [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {P : Place k F} {P' : Place k' F'} {m : ℕ} (hm : 0 < m)
    (hord : ∀ x : F, P'.ord (algebraMap F F' x) = m * P.ord x) :
    ramificationIdx (RatFunc k) P ∣ ramificationIdx (RatFunc k') P' := by
  classical
  rcases eq_infty_or_exists_eq_adicOfIrreducible (P.restrict k (RatFunc k)) with hinf | ⟨q, hq, hqP⟩
  · have hXord := hord (algebraMap (RatFunc k) F RatFunc.X)
    rw [hX, ord_algebraMap_restrict k' (RatFunc k') P',
      ord_algebraMap_restrict k (RatFunc k) P, hinf, ord_infty, RatFunc.intDegree_X] at hXord
    have heF := ramificationIdx_pos (RatFunc k) P
    have heF' := ramificationIdx_pos (RatFunc k') P'
    have hneg : (P'.restrict k' (RatFunc k')).ord RatFunc.X < 0 := by nlinarith
    have hinf' : P'.restrict k' (RatFunc k') = infty k' :=
      (infty_iff_ord_X_lt_zero _).mpr hneg
    rw [hinf', ord_infty, RatFunc.intDegree_X] at hXord
    exact ⟨m, by exact_mod_cast (by linarith :
      (ramificationIdx (RatFunc k') P' : ℤ) = ramificationIdx (RatFunc k) P * m)⟩
  · have hqord := hord (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) q))
    rw [algebraMap_ratFunc_polynomial_eq hX q, ord_algebraMap_restrict k' (RatFunc k') P',
      ord_algebraMap_restrict k (RatFunc k) P, hqP,
      ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left Associated.rfl,
      mul_one] at hqord
    have hpos : 0 < (P'.restrict k' (RatFunc k')).ord
        (algebraMap k'[X] (RatFunc k') (q.map (algebraMap k k'))) := by
      have := ramificationIdx_pos (RatFunc k) P
      have := ramificationIdx_pos (RatFunc k') P'
      nlinarith
    rcases eq_infty_or_exists_eq_adicOfIrreducible (P'.restrict k' (RatFunc k')) with
      h' | ⟨r, hr, h'⟩
    · rw [h', ord_infty, RatFunc.intDegree_polynomial, natDegree_map] at hpos
      omega
    · have hsq : Squarefree (q.map (algebraMap k k')) :=
        ((PerfectField.separable_of_irreducible hq).map).squarefree
      rw [h', ord_adicOfIrreducible_algebraMap_of_squarefree hr hsq] at hqord hpos
      split_ifs at hqord hpos with hdvd
      · exact ⟨m, by exact_mod_cast (by linarith :
          (ramificationIdx (RatFunc k') P' : ℤ) = ramificationIdx (RatFunc k) P * m)⟩
      · omega

/-- **Dominating place over `RatFunc` in a linearly disjoint constant compositum**: over a perfect
field `k`, every place `P` of `F / k` is dominated by a place `P'` of `F' / k'` whose ramification
index over `k'(X)` is a multiple of `e(P ∣ k(X))`, and which lies over `∞` or `X - a` (`a ∈ k`)
exactly when `P` does. -/
theorem exists_place_ramificationIdx_ratFunc_dvd_of_linearDisjoint [PerfectField k]
    [FiniteDimensional (RatFunc k) F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (P : Place k F) :
    have : FiniteDimensional (RatFunc k') F' :=
      FiniteDimensional.of_finrank_pos (by
        rw [finrank_ratFunc_eq_of_linearDisjoint H hcomp hX]
        exact Module.finrank_pos)
    ∃ P' : Place k' F',
      ramificationIdx (RatFunc k) P ∣ ramificationIdx (RatFunc k') P' ∧
      (P'.restrict k' (RatFunc k') = infty k' ↔ P.restrict k (RatFunc k) = infty k) ∧
      ∀ a : k,
        P'.restrict k' (RatFunc k') =
            adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' a)) ↔
          P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a) := by
  have : FiniteDimensional (RatFunc k') F' :=
    FiniteDimensional.of_finrank_pos (by
      rw [finrank_ratFunc_eq_of_linearDisjoint H hcomp hX]
      exact Module.finrank_pos)
  obtain ⟨P', m, hm, _, hord⟩ := exists_place_integers_le_and_ord_eq_mul_of_linearDisjoint
    (IsFunctionField.ratFunc k).finite_extension H hcomp P
  have heF' : (0 : ℤ) < ramificationIdx (RatFunc k') P' := mod_cast ramificationIdx_pos _ P'
  have hme : (0 : ℤ) < m * ramificationIdx (RatFunc k) P := by
    have := ramificationIdx_pos (RatFunc k) P
    positivity
  refine ⟨P', ramificationIdx_ratFunc_dvd_of_ord_eq_mul hX hm hord, ?_, fun a ↦ ?_⟩
  · have hXord := hord (algebraMap (RatFunc k) F RatFunc.X)
    rw [hX, ord_algebraMap_restrict k' (RatFunc k') P',
      ord_algebraMap_restrict k (RatFunc k) P, ← mul_assoc] at hXord
    rw [infty_iff_ord_X_lt_zero, infty_iff_ord_X_lt_zero]
    constructor <;> intro h <;> nlinarith
  · have haord := hord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a))
    have haeq := algebraMap_ratFunc_polynomial_eq hX (X - C a)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      map_sub (algebraMap k[X] (RatFunc k)), map_sub (algebraMap k'[X] (RatFunc k')),
      RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C] at haeq
    rw [haeq, ord_algebraMap_restrict k' (RatFunc k') P',
      ord_algebraMap_restrict k (RatFunc k) P, ← mul_assoc] at haord
    rw [← ord_X_sub_C_pos_iff, ← ord_X_sub_C_pos_iff]
    constructor <;> intro h <;> nlinarith

end RatFuncRamificationDvd

section UnramifiedLocalBasisDiscriminant

variable {k F E : Type*} [Field k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E]

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- The trace matrices of a finite separable basis and its trace-dual basis are inverse to one
another, so their discriminants multiply to `1`. -/
private theorem discr_mul_discr_traceDual {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι F E) :
    Algebra.discr F b * Algebra.discr F b.traceDual = 1 := by
  have hmul : Algebra.traceMatrix F b * Algebra.traceMatrix F b.traceDual = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hsum : ∑ l, Algebra.traceMatrix F b i l * Algebra.traceMatrix F b.traceDual l j =
        Algebra.trace F E ((∑ l, b.traceDual.repr (b i) l • b.traceDual l) * b.traceDual j) := by
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [Algebra.traceMatrix_apply, b.traceDual_repr_apply, Algebra.traceForm_apply,
        smul_mul_assoc, LinearMap.map_smul, smul_eq_mul]
    rw [hsum, b.traceDual.sum_repr, b.trace_mul_traceDual]
  rw [Algebra.discr_def, Algebra.discr_def, ← Matrix.det_mul, hmul, Matrix.det_one]

/-- **At an unramified place, the local integral basis has unit discriminant**: `ord_P(disc b) = 0`.
Because every place of `E` above `P` has vanishing different exponent, the complementary module
equals the local integral closure, making the trace-dual basis integral at `P` as well. -/
theorem ord_discr_localIntegralBasis_eq_zero (hF : IsFunctionField k F) {P : Place k F}
    (hP : P.IsUnramified (k' := k) (F' := E)) :
    P.ord (Algebra.discr F (localIntegralBasis E P)) = 0 := by
  classical
  let b := localIntegralBasis E P
  have his := isIntegralBasis_localIntegralBasis E P
  have hb_int : ∀ i, IsIntegral P.integers (b i) := his.isIntegral
  have hspan : (1 : Submodule (integralClosure P.integers E) E).restrictScalars P.integers =
      Submodule.span P.integers (Set.range b) := by
    ext x
    rw [Submodule.restrictScalars_mem, his.mem_span_iff_isIntegral, ← mem_integralClosure_iff,
      Submodule.mem_one]
    exact ⟨by rintro ⟨y, rfl⟩; exact y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩
  have hbdual_int : ∀ i, IsIntegral P.integers (b.traceDual i) := fun i ↦ by
    have hmem : b.traceDual i ∈
        Submodule.traceDual P.integers F (1 : Submodule (integralClosure P.integers E) E) := by
      change b.traceDual i ∈ (Submodule.traceDual P.integers F _).restrictScalars P.integers
      rw [Submodule.traceDual_span_of_basis P.integers _ b hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    refine (isIntegral_iff_forall_restrict_eq_mem_integers hF.finite_extension P).mpr
      fun P' hP' ↦ ?_
    have hd0 : differentExponent k F P' = 0 :=
      (differentExponent_eq_zero_iff k F P').mpr
        ((ramificationIdx_eq_one_and_isSeparable_iff_isUnramifiedAt k F P').mp
          ⟨hP.ramificationIdx_eq_one hP', hP.isSeparable hP'⟩)
    have hval := (mem_traceDual_iff_forall_valuation_le k F hF.finite_extension P).mp hmem P' hP'
    rw [hd0, Nat.cast_zero, WithZero.exp_zero] at hval
    exact P'.mem_integers_iff.mpr hval
  obtain ⟨d₁, hd₁⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.discr_isIntegral F hb_int)
  obtain ⟨d₂, hd₂⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.discr_isIntegral F hbdual_int)
  have hnn₁ : 0 ≤ P.ord (Algebra.discr F b) :=
    P.mem_integers_iff_ord_nonneg.mp (by rw [← hd₁]; exact d₁.2)
  have hnn₂ : 0 ≤ P.ord (Algebra.discr F b.traceDual) :=
    P.mem_integers_iff_ord_nonneg.mp (by rw [← hd₂]; exact d₂.2)
  have hsum : P.ord (Algebra.discr F b) + P.ord (Algebra.discr F b.traceDual) = 0 := by
    rw [← P.ord_mul (Algebra.discr_not_zero_of_basis F b)
      (Algebra.discr_not_zero_of_basis F b.traceDual), discr_mul_discr_traceDual b, P.ord_one]
  change P.ord (Algebra.discr F b) = 0
  omega

end UnramifiedLocalBasisDiscriminant

section UnramifiedTranscendentalBaseChange

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- Coefficient map `RatFunc k →+* RatFunc k'` induced by `algebraMap k k'`. -/
private noncomputable def ratFuncMapRingHom : RatFunc k →+* RatFunc k' :=
  RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k k'))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Polynomial.map_injective _ (algebraMap k k').injective))

private theorem algebraMap_ratFuncMapRingHom
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) (f : RatFunc k) :
    algebraMap (RatFunc k') F' (ratFuncMapRingHom f) =
      algebraMap F F' (algebraMap (RatFunc k) F f) := by
  have hext : (algebraMap (RatFunc k') F').comp ratFuncMapRingHom =
      (algebraMap F F').comp (algebraMap (RatFunc k) F) := by
    refine IsFractionRing.ringHom_ext (A := k[X]) fun p ↦ ?_
    simp [RingHom.comp_apply, ratFuncMapRingHom, RatFunc.mapRingHom_algebraMap,
      Polynomial.coe_mapRingHom, algebraMap_ratFunc_polynomial_eq hX]
  exact RingHom.congr_fun hext f

/-- Transport a finite `RatFunc k`-basis of `F` along a linearly disjoint constant compositum
`F' = F · k'` to a `RatFunc k'`-basis of `F'`. -/
private noncomputable def constantExtensionRatFuncBasis [FiniteDimensional (RatFunc k) F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι (RatFunc k) F) :
    Module.Basis ι (RatFunc k') F' := by
  have : FiniteDimensional (RatFunc k') F' :=
    FiniteDimensional.of_finrank_pos (by
      rw [finrank_ratFunc_eq_of_linearDisjoint H hcomp hX]
      exact Module.finrank_pos)
  set C := (IsScalarTower.toAlgHom k (RatFunc k) F).fieldRange
  have : FiniteDimensional C F :=
    Module.Finite.of_equiv_equiv
      (IsScalarTower.toAlgHom k (RatFunc k) F).equivFieldRange.toRingEquiv
      (RingEquiv.refl F) (RingHom.ext fun _ ↦ rfl)
  let bC : Module.Basis ι C F :=
    Module.Basis.mk
      (b.linearIndependent.map_of_surjective_injective
        (IsScalarTower.toAlgHom k (RatFunc k) F).equivFieldRange (AddMonoidHom.id F)
        (AlgEquiv.surjective _) (by simp) fun _ _ ↦ by simp_rw [Algebra.smul_def]; rfl)
      (by
        intro y _
        rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply]
        refine Submodule.finsuppSum_mem _ _ _ _ fun i _ ↦ ?_
        have hsmul : ((IsScalarTower.toAlgHom k (RatFunc k) F).equivFieldRange (b.repr y i)) •
            b i = b.repr y i • b i := by
          simp_rw [Algebra.smul_def]
          rfl
        rw [← hsmul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have hspanC := span_range_basis_of_isAlgebraic_constantCompositum (k := k) hcomp C bC
  have hle : IntermediateField.adjoin k' (Set.range (algebraMap C F')) ≤
      (IsScalarTower.toAlgHom k' (RatFunc k') F').fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨_, ⟨f, rfl⟩⟩, rfl⟩
    exact ⟨ratFuncMapRingHom f, algebraMap_ratFuncMapRingHom hX f⟩
  have hspan : ⊤ ≤ Submodule.span (RatFunc k') (Set.range (algebraMap F F' ∘ b)) := by
    intro z _
    have hz : z ∈ Submodule.span (IntermediateField.adjoin k' (Set.range (algebraMap C F')))
        (Set.range (algebraMap F F' ∘ b)) := by
      have hbC : (algebraMap F F' ∘ bC) = (algebraMap F F' ∘ b) := by
        ext i; simp [bC]
      rw [← hbC, hspanC]
      trivial
    refine Submodule.span_induction (fun x hx ↦ Submodule.subset_span hx) (zero_mem _)
      (fun _ _ _ _ ↦ add_mem) (fun c x _ hx ↦ ?_) hz
    obtain ⟨q, hq⟩ := hle c.2
    have hsmul : c • x = q • x := by
      simp [Algebra.smul_def, ← hq]
    rw [hsmul]
    exact Submodule.smul_mem _ q hx
  have hli : LinearIndependent (RatFunc k') (algebraMap F F' ∘ b) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan
      (by rw [finrank_ratFunc_eq_of_linearDisjoint H hcomp hX, Module.finrank_eq_card_basis b])
  exact Module.Basis.mk hli hspan

private theorem coe_constantExtensionRatFuncBasis [FiniteDimensional (RatFunc k) F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    constantExtensionRatFuncBasis H hcomp hX b i = algebraMap F F' (b i) := by
  simp [constantExtensionRatFuncBasis]

private theorem constantExtensionRatFuncBasis_repr_algebraMap [FiniteDimensional (RatFunc k) F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι (RatFunc k) F) (y : F) (i : ι) :
    (constantExtensionRatFuncBasis H hcomp hX b).repr (algebraMap F F' y) i =
      ratFuncMapRingHom (b.repr y i) := by
  set b' := constantExtensionRatFuncBasis H hcomp hX b
  let f : ι →₀ RatFunc k' := (b.repr y).mapRange ratFuncMapRingHom ratFuncMapRingHom.map_zero
  have hsum : b'.repr.symm f = algebraMap F F' y := by
    rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply]
    dsimp only [f]
    rw [Finsupp.sum_mapRange_index (fun j ↦ zero_smul (RatFunc k') (b' j))]
    conv_rhs => rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply,
      Finsupp.sum, map_sum]
    rw [Finsupp.sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp [b', coe_constantExtensionRatFuncBasis, Algebra.smul_def, algebraMap_ratFuncMapRingHom hX]
  simpa [f] using congrArg (fun q : ι →₀ RatFunc k' ↦ q i) (b'.repr.symm_apply_eq.mp hsum).symm

private theorem discr_constantExtensionRatFuncBasis [FiniteDimensional (RatFunc k) F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι (RatFunc k) F) :
    Algebra.discr (RatFunc k') (constantExtensionRatFuncBasis H hcomp hX b) =
      ratFuncMapRingHom (Algebra.discr (RatFunc k) b) := by
  classical
  have htr : ∀ y : F, Algebra.trace (RatFunc k') F' (algebraMap F F' y) =
      ratFuncMapRingHom (Algebra.trace (RatFunc k) F y) := fun y ↦ by
    let b₀ := Module.finBasis (RatFunc k) F
    let b₀' := constantExtensionRatFuncBasis H hcomp hX b₀
    rw [Algebra.trace_eq_matrix_trace b₀', Algebra.trace_eq_matrix_trace b₀, Matrix.trace,
      Matrix.trace, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Matrix.diag_apply, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
      Algebra.leftMulMatrix_eq_repr_mul, coe_constantExtensionRatFuncBasis,
      ← map_mul (algebraMap F F'), constantExtensionRatFuncBasis_repr_algebraMap H hcomp hX]
  have hmat : ratFuncMapRingHom.mapMatrix (Algebra.traceMatrix (RatFunc k) b) =
      Algebra.traceMatrix (RatFunc k') (constantExtensionRatFuncBasis H hcomp hX b) := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.traceForm_apply,
      coe_constantExtensionRatFuncBasis, coe_constantExtensionRatFuncBasis,
      ← map_mul (algebraMap F F'), htr]
  rw [Algebra.discr_def, Algebra.discr_def, ← hmat, ← ratFuncMapRingHom.map_det]

/-- If `x ∈ F` is integral over a `RatFunc k`-subalgebra `S` mapped by `RatFunc k → F'` into
`P'.integers`, then the image of `x` in `F'` is integral over the restricted valuation ring
`(P'.restrict k' (RatFunc k')).integers`. -/
private theorem isIntegral_restrict_ratFunc_of_isIntegral_ring
    [Algebra.IsIntegral (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (P' : Place k' F') {S : Type*} [CommRing S] [Algebra S (RatFunc k)]
    [Algebra S F] [IsScalarTower S (RatFunc k) F]
    (hS : ∀ s : S,
      algebraMap F F' (algebraMap (RatFunc k) F (algebraMap S (RatFunc k) s)) ∈ P'.integers)
    {x : F} (hx : IsIntegral S x) :
    IsIntegral (P'.restrict k' (RatFunc k')).integers (algebraMap F F' x) := by
  let g : S →+* (P'.restrict k' (RatFunc k')).integers :=
    (ratFuncMapRingHom.comp (algebraMap S (RatFunc k))).codRestrict
      (P'.restrict k' (RatFunc k')).integers fun s ↦ by
        rw [mem_integers_restrict_iff, RingHom.comp_apply, algebraMap_ratFuncMapRingHom hX]
        exact hS s
  obtain ⟨p, hp_monic, hp_eval⟩ := hx
  refine ⟨p.map g, hp_monic.map g, ?_⟩
  rw [eval₂_map]
  have heq : (algebraMap (P'.restrict k' (RatFunc k')).integers F').comp g =
      (algebraMap F F').comp (algebraMap S F) := by
    ext s
    change algebraMap (RatFunc k') F'
        ((g s : (P'.restrict k' (RatFunc k')).integers) : RatFunc k') =
      algebraMap F F' (algebraMap S F s)
    rw [RingHom.codRestrict_apply, RingHom.comp_apply, algebraMap_ratFuncMapRingHom hX,
      ← IsScalarTower.algebraMap_apply S (RatFunc k) F]
  rw [heq]
  have hzero := congrArg (algebraMap F F') hp_eval
  rw [map_zero, Polynomial.hom_eval₂] at hzero
  exact hzero

private theorem differentExponent_eq_zero_of_discr_mem_and_inv_mem
    [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']
    [Algebra.IsSeparable (RatFunc k') F']
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (P' : Place k' F') {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι (RatFunc k) F)
    (hb : ∀ i, IsIntegral (P'.restrict k' (RatFunc k')).integers
      (constantExtensionRatFuncBasis H hcomp hX b i))
    (hd : algebraMap F F' (algebraMap (RatFunc k) F (Algebra.discr (RatFunc k) b)) ∈ P'.integers)
    (hd_inv : algebraMap F F' (algebraMap (RatFunc k) F (Algebra.discr (RatFunc k) b)⁻¹) ∈
      P'.integers) :
    differentExponent k' (RatFunc k') P' = 0 := by
  have hd_mem : ratFuncMapRingHom (Algebra.discr (RatFunc k) b) ∈
      (P'.restrict k' (RatFunc k')).integers := by
    rwa [mem_integers_restrict_iff, algebraMap_ratFuncMapRingHom hX]
  have hd_inv_mem : (ratFuncMapRingHom (Algebra.discr (RatFunc k) b))⁻¹ ∈
      (P'.restrict k' (RatFunc k')).integers := by
    rwa [← map_inv₀, mem_integers_restrict_iff, algebraMap_ratFuncMapRingHom hX]
  have hd_ord : (P'.restrict k' (RatFunc k')).ord
      (Algebra.discr (RatFunc k') (constantExtensionRatFuncBasis H hcomp hX b)) = 0 := by
    rw [discr_constantExtensionRatFuncBasis H hcomp hX b]
    have h1 := (P'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg.mp hd_mem
    have h2 := (P'.restrict k' (RatFunc k')).mem_integers_iff_ord_nonneg.mp hd_inv_mem
    rw [ord_inv] at h2
    omega
  exact differentExponent_eq_zero_of_ord_discr_eq_zero k' (RatFunc k') P' hb hd_ord

/-- **Separability over `RatFunc` persists in any constant compositum** with compatible `X`, even
when `k' / k` is transcendental or inseparable. -/
theorem _root_.TauCeti.isSeparable_ratFunc_of_constantCompositum_eq_top
    [Algebra.IsSeparable (RatFunc k) F]
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    Algebra.IsSeparable (RatFunc k') F' := by
  have hsep : ∀ y : F, IsSeparable (RatFunc k') (algebraMap F F' y) := fun y ↦ by
    let φ : RatFunc k →+* RatFunc k' := ratFuncMapRingHom (k := k) (k' := k')
    have hmap : ((minpoly (RatFunc k) y).map φ).Separable :=
      Polynomial.Separable.map (Algebra.IsSeparable.isSeparable (RatFunc k) y)
    have haeval : aeval (algebraMap F F' y) ((minpoly (RatFunc k) y).map φ) = 0 := by
      rw [aeval_def, eval₂_map]
      have heq : (algebraMap (RatFunc k') F').comp φ =
          (algebraMap F F').comp (algebraMap (RatFunc k) F) :=
        RingHom.ext (algebraMap_ratFuncMapRingHom hX)
      rw [heq, ← Polynomial.hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
    exact hmap.of_dvd (minpoly.dvd (RatFunc k') (algebraMap F F' y) haeval)
  have htop : IntermediateField.adjoin (RatFunc k') (Set.range (algebraMap F F')) = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    let E := IntermediateField.adjoin (RatFunc k') (Set.range (algebraMap F F'))
    have hFE : ∀ y : F, algebraMap F F' y ∈ E :=
      fun y ↦ IntermediateField.subset_adjoin (RatFunc k') _ ⟨y, rfl⟩
    have hle := (constantCompositum_le_iff F k' F' (K := E.toSubfield.toIntermediateField hFE)).mpr
      fun c ↦ by
        rw [IsScalarTower.algebraMap_apply k' (RatFunc k') F']
        exact E.algebraMap_mem _
    exact hle (hcomp ▸ IntermediateField.mem_top)
  rw [← IntermediateField.isSeparable_top, ← htop]
  exact (IntermediateField.isSeparable_adjoin_iff_isSeparable (RatFunc k') F').mpr
    fun _ ⟨y, hy⟩ ↦ hy ▸ hsep y

/-- **Unramified base change along an arbitrary linearly disjoint constant extension.** Let
`F / RatFunc k` be finite separable and `F' = F · k'` linearly disjoint over `k`, with compatible
`X`. For a place `P'` of `F' / k'`, if every place `Q` of `RatFunc k` whose valuation ring is the
preimage of `P'.integers` in `RatFunc k` is unramified in `F`, then `P'` has ramification index `1`
over `RatFunc k'`. -/
theorem ramificationIdx_ratFunc_eq_one_of_linearDisjoint
    [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    (P' : Place k' F')
    (hQ : ∀ Q : Place k (RatFunc k),
      (∀ f : RatFunc k,
        f ∈ Q.integers ↔ algebraMap F F' (algebraMap (RatFunc k) F f) ∈ P'.integers) →
      Q.IsUnramified (k' := k) (F' := F)) :
    have : FiniteDimensional (RatFunc k') F' :=
      FiniteDimensional.of_finrank_pos (by
        rw [finrank_ratFunc_eq_of_linearDisjoint H hcomp hX]
        exact Module.finrank_pos)
    ramificationIdx (RatFunc k') P' = 1 := by
  classical
  have : FiniteDimensional (RatFunc k') F' :=
    FiniteDimensional.of_finrank_pos (by
      rw [finrank_ratFunc_eq_of_linearDisjoint H hcomp hX]
      exact Module.finrank_pos)
  have : Algebra.IsSeparable (RatFunc k') F' :=
    isSeparable_ratFunc_of_constantCompositum_eq_top hcomp hX
  let A₀ : ValuationSubring (RatFunc k) :=
    P'.integers.comap ((algebraMap F F').comp (algebraMap (RatFunc k) F))
  have hd0 : differentExponent k' (RatFunc k') P' = 0 := by
    by_cases hA₀ : A₀ = ⊤
    · let b := Module.finBasis (RatFunc k) F
      have hall : ∀ f : RatFunc k, algebraMap F F' (algebraMap (RatFunc k) F f) ∈ P'.integers :=
        fun f ↦ by change f ∈ A₀; rw [hA₀]; trivial
      refine differentExponent_eq_zero_of_discr_mem_and_inv_mem H hcomp hX P' b
        (fun i ↦ ?_) (hall _) (hall _)
      rw [coe_constantExtensionRatFuncBasis]
      exact isIntegral_restrict_ratFunc_of_isIntegral_ring hX P' (S := RatFunc k)
        (fun s ↦ hall s) (IsIntegral.of_finite (RatFunc k) (b i))
    · have hkA₀ : ∀ c : k, algebraMap k (RatFunc k) c ∈ A₀ := fun c ↦ by
        change algebraMap F F' (algebraMap (RatFunc k) F (algebraMap k (RatFunc k) c)) ∈ P'.integers
        rw [← IsScalarTower.algebraMap_apply k (RatFunc k) F,
          ← IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply k k' F']
        exact P'.algebraMap_mem_integers _
      let Q := ofValuationSubring (IsFunctionField.ratFunc k) hkA₀ hA₀
      have hQint : Q.integers = A₀ := integers_ofValuationSubring _ hkA₀ hA₀
      have hQunr : Q.IsUnramified (k' := k) (F' := F) := hQ Q fun f ↦ by rw [hQint]; rfl
      let b := localIntegralBasis F Q
      have hdQ : Q.ord (Algebra.discr (RatFunc k) b) = 0 :=
        ord_discr_localIntegralBasis_eq_zero (IsFunctionField.ratFunc k) hQunr
      refine differentExponent_eq_zero_of_discr_mem_and_inv_mem H hcomp hX P' b
        (fun i ↦ ?_)
        (by change _ ∈ A₀; rw [← hQint, Q.mem_integers_iff_ord_nonneg, hdQ])
        (by change _ ∈ A₀; rw [← hQint, Q.mem_integers_iff_ord_nonneg, Q.ord_inv, hdQ, neg_zero])
      rw [coe_constantExtensionRatFuncBasis]
      have hb_int : ∀ j, IsIntegral Q.integers (b j) :=
        (isIntegralBasis_localIntegralBasis F Q).isIntegral
      exact isIntegral_restrict_ratFunc_of_isIntegral_ring hX P' (S := Q.integers)
        (fun s ↦ by change (s : RatFunc k) ∈ A₀; exact hQint ▸ s.2) (hb_int i)
  have hle := ramificationIdx_le_differentExponent_add_one k' (RatFunc k') P'
  have hpos := ramificationIdx_pos (RatFunc k') P'
  omega

end UnramifiedTranscendentalBaseChange

end Place

end TauCeti
