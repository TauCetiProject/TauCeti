/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.LinearDisjoint
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Unramified
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.Separable.Regular
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.FieldTheory.AlgebraicClosure
import TauCeti.FieldTheory.FunctionField.Different.Basic
import TauCeti.FieldTheory.FunctionField.Different.IntegralBasis
import TauCeti.FieldTheory.FunctionField.Place.Extension.IntegralBasis.Basic
import TauCeti.FieldTheory.FunctionField.Place.OfValuationSubring
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.FieldTheory.IntermediateField.FieldRange
import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.RingTheory.Discriminant.Equiv
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
* `IsIntegrallyClosedIn.of_constantCompositum_eq_top_of_linearDisjoint`: exact constants
  persist under any linearly disjoint constant extension of a geometrically reduced field.
* `TauCeti.isSeparable_ratFunc_of_constantCompositum_eq_top`: separability over `RatFunc` persists
  in any constant compositum with compatible `X`.
* `TauCeti.Place.exists_place_integers_le_and_ord_eq_mul_of_linearDisjoint`: every place `P` of
  `F / k` is dominated by a place `P'` of `F' / k'` whose order restricts to a positive multiple of
  `ord_P`.
* `TauCeti.Place.exists_place_ramificationIdx_ratFunc_dvd_of_linearDisjoint`: over a perfect base
  field, `P'` preserves `∞` and rational places `X - a` (`a ∈ k`), with
  `e(P ∣ k(X)) ∣ e(P' ∣ k'(X))`.
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
  have hring : (π : F ⊗[k] k' →+* F').range =
      Subring.closure (Set.range (algebraMap F F') ∪ Set.range (algebraMap k' F')) := by
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
    rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.right_algebraMap_apply,
      AlgHom.coe_toRingHom, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul,
      IsScalarTower.toAlgHom_apply]
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
      simp [e, φ, AlgEquiv.ofInjective_apply]
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
  have hu_ord : P'.ord (algebraMap F F' (u : F)) = 0 :=
    P'.ord_eq_zero_of_mem_integers_of_inv_mem hu_mem hu_inv
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

/-- From a place `P'` of `F' / k'` whose order restricts to a positive multiple `m · ord_P`,
over a perfect base field `k`, `e(P ∣ k(X))` divides `e(P' ∣ k'(X))`, and `P'` lies over `∞` or
`X - a` (`a ∈ k`) exactly when `P` does. -/
private theorem ramificationIdx_ratFunc_dvd_of_ord_eq_mul [PerfectField k]
    [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {P : Place k F} {P' : Place k' F'} {m : ℕ} (hm : 0 < m)
    (hord : ∀ x : F, P'.ord (algebraMap F F' x) = m * P.ord x) :
    ramificationIdx (RatFunc k) P ∣ ramificationIdx (RatFunc k') P' ∧
      (P'.restrict k' (RatFunc k') = infty k' ↔ P.restrict k (RatFunc k) = infty k) ∧
      ∀ a : k,
        P'.restrict k' (RatFunc k') =
            adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' a)) ↔
          P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a) := by
  classical
  have heF : (0 : ℤ) < ramificationIdx (RatFunc k) P := mod_cast ramificationIdx_pos _ P
  have heF' : (0 : ℤ) < ramificationIdx (RatFunc k') P' := mod_cast ramificationIdx_pos _ P'
  have hme : (0 : ℤ) < m * ramificationIdx (RatFunc k) P := by positivity
  have hXord := hord (algebraMap (RatFunc k) F RatFunc.X)
  rw [hX, ord_algebraMap_restrict k' (RatFunc k') P',
    ord_algebraMap_restrict k (RatFunc k) P, ← mul_assoc] at hXord
  have hinf_iff : P'.restrict k' (RatFunc k') = infty k' ↔ P.restrict k (RatFunc k) = infty k := by
    rw [← ord_X_neg_iff, ← ord_X_neg_iff]
    constructor <;> intro h <;> nlinarith
  refine ⟨?_, hinf_iff, fun a ↦ ?_⟩
  · rcases eq_infty_or_exists_eq_adicOfIrreducible (P.restrict k (RatFunc k)) with
      hinf | ⟨q, hq, hqP⟩
    · rw [hinf, hinf_iff.mpr hinf, ord_infty, ord_infty, RatFunc.intDegree_X,
        RatFunc.intDegree_X] at hXord
      exact ⟨m, by exact_mod_cast (by linarith :
        (ramificationIdx (RatFunc k') P' : ℤ) = ramificationIdx (RatFunc k) P * m)⟩
    · have hqord := hord (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) q))
      have hqeq : algebraMap F F' (algebraMap (RatFunc k) F (algebraMap k[X] (RatFunc k) q)) =
          algebraMap (RatFunc k') F' (algebraMap k'[X] (RatFunc k') (q.map (algebraMap k k'))) := by
        rw [← algebraMap_mapCoeffRingHom hX, RatFunc.mapCoeffRingHom_algebraMap]
      rw [hqeq, ord_algebraMap_restrict k' (RatFunc k') P',
        ord_algebraMap_restrict k (RatFunc k) P, hqP,
        ord_adicOfIrreducible_algebraMap_irreducible hq hq, ite_eq_left Associated.rfl,
        mul_one] at hqord
      have hpos : 0 < (P'.restrict k' (RatFunc k')).ord
          (algebraMap k'[X] (RatFunc k') (q.map (algebraMap k k'))) := by nlinarith
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
  · have haord := hord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a))
    have haeq : algebraMap F F' (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) =
        algebraMap (RatFunc k') F' (RatFunc.X - RatFunc.C (algebraMap k k' a)) := by
      rw [← algebraMap_mapCoeffRingHom hX, map_sub, RatFunc.mapCoeffRingHom_X,
        RatFunc.mapCoeffRingHom_C]
    rw [haeq, ord_algebraMap_restrict k' (RatFunc k') P',
      ord_algebraMap_restrict k (RatFunc k) P, ← mul_assoc] at haord
    rw [← ord_X_sub_C_pos_iff, ← ord_X_sub_C_pos_iff]
    constructor <;> intro h <;> nlinarith

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
    haveI := finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
    ∃ P' : Place k' F',
      ramificationIdx (RatFunc k) P ∣ ramificationIdx (RatFunc k') P' ∧
      (P'.restrict k' (RatFunc k') = infty k' ↔ P.restrict k (RatFunc k) = infty k) ∧
      ∀ a : k,
        P'.restrict k' (RatFunc k') =
            adicOfIrreducible (irreducible_X_sub_C (algebraMap k k' a)) ↔
          P.restrict k (RatFunc k) = adicOfIrreducible (irreducible_X_sub_C a) := by
  have := finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  obtain ⟨P', m, hm, _, hord⟩ := exists_place_integers_le_and_ord_eq_mul_of_linearDisjoint
    (IsFunctionField.ratFunc k).finite_extension H hcomp P
  exact ⟨P', ramificationIdx_ratFunc_dvd_of_ord_eq_mul hX hm hord⟩

end RatFuncRamificationDvd

section UnramifiedTranscendentalBaseChange

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [Algebra (RatFunc k') F'] [IsScalarTower k' (RatFunc k') F']

attribute [local instance 10] algebraIntegersExtension isScalarTowerIntegersExtension

/-- In a constant extension with compatible `X`, adjoining `k'` to the image of `k(X)` in `F'`
yields the image of `k'(X)` in `F'`. -/
private theorem adjoin_range_fieldRange_ratFunc_eq
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    IntermediateField.adjoin k'
        (Set.range (algebraMap (IsScalarTower.toAlgHom k (RatFunc k) F).fieldRange F')) =
      (IsScalarTower.toAlgHom k' (RatFunc k') F').fieldRange := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨_, ⟨f, rfl⟩⟩, rfl⟩
    exact ⟨RatFunc.mapCoeffRingHom (algebraMap k k') f, algebraMap_mapCoeffRingHom hX f⟩
  · rw [AlgHom.fieldRange_eq_map, ← RatFunc.adjoin_X, IntermediateField.adjoin_map,
      Set.image_singleton, IntermediateField.adjoin_simple_le_iff]
    refine IntermediateField.subset_adjoin k' _
      ⟨⟨algebraMap (RatFunc k) F RatFunc.X,
        ⟨RatFunc.X, IsScalarTower.toAlgHom_apply k (RatFunc k) F RatFunc.X⟩⟩, ?_⟩
    rw [IsScalarTower.algebraMap_apply (IsScalarTower.toAlgHom k (RatFunc k) F).fieldRange F F',
      IntermediateField.algebraMap_apply, hX, IsScalarTower.toAlgHom_apply]

/-- Transport a finite `RatFunc k`-basis of `F` along a linearly disjoint constant compositum
`F' = F · k'` to a `RatFunc k'`-basis of `F'`, via `constantExtensionBasisOfLinearDisjoint`. -/
private noncomputable def constantExtensionRatFuncBasis
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι (RatFunc k) F) :
    Module.Basis ι (RatFunc k') F' :=
  let C := (IsScalarTower.toAlgHom k (RatFunc k) F).fieldRange
  let e : RatFunc k ≃+* C := (IsScalarTower.toAlgHom k (RatFunc k) F).equivFieldRange.toRingEquiv
  let bC : Module.Basis ι C F := b.mapCoeffs e fun a x ↦
    (IsScalarTower.toAlgHom k (RatFunc k) F).equivFieldRange_smul
      (fun _ ↦ (IsScalarTower.toAlgHom_apply k (RatFunc k) F _).symm) a x
  have : FiniteDimensional C F := Module.Finite.of_basis bC
  have : Algebra.IsAlgebraic C F := Algebra.IsAlgebraic.of_finite C F
  let e' : IntermediateField.adjoin k' (Set.range (algebraMap C F')) ≃+* RatFunc k' :=
    (IntermediateField.equivOfEq (adjoin_range_fieldRange_ratFunc_eq hX)).toRingEquiv.trans
      (IsScalarTower.toAlgHom k' (RatFunc k') F').equivFieldRange.symm.toRingEquiv
  (constantExtensionBasisOfLinearDisjoint H hcomp C bC).mapCoeffs e' fun c x ↦ by
    rw [Algebra.smul_def, Algebra.smul_def]
    congr 1
    rw [RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv,
      IntermediateField.algebraMap_apply, ← IsScalarTower.toAlgHom_apply k' (RatFunc k') F',
      ← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply,
      IntermediateField.equivOfEq_apply]

private theorem coe_constantExtensionRatFuncBasis
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι (RatFunc k) F) (i : ι) :
    constantExtensionRatFuncBasis H hcomp hX b i = algebraMap F F' (b i) := by
  simp [constantExtensionRatFuncBasis, Module.Basis.mapCoeffs_apply]

private theorem discr_constantExtensionRatFuncBasis
    (H : (IsScalarTower.toAlgHom k k' F').fieldRange.LinearDisjoint F)
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι (RatFunc k) F) :
    Algebra.discr (RatFunc k') (constantExtensionRatFuncBasis H hcomp hX b) =
      RatFunc.mapCoeffRingHom (algebraMap k k') (Algebra.discr (RatFunc k) b) := by
  let C := (IsScalarTower.toAlgHom k (RatFunc k) F).fieldRange
  let e : RatFunc k ≃+* C := (IsScalarTower.toAlgHom k (RatFunc k) F).equivFieldRange.toRingEquiv
  let bC : Module.Basis ι C F := b.mapCoeffs e fun a x ↦
    (IsScalarTower.toAlgHom k (RatFunc k) F).equivFieldRange_smul
      (fun _ ↦ (IsScalarTower.toAlgHom_apply k (RatFunc k) F _).symm) a x
  have : FiniteDimensional C F := Module.Finite.of_basis bC
  have : Algebra.IsAlgebraic C F := Algebra.IsAlgebraic.of_finite C F
  let C' := IntermediateField.adjoin k' (Set.range (algebraMap C F'))
  let e' : C' ≃+* RatFunc k' :=
    (IntermediateField.equivOfEq (adjoin_range_fieldRange_ratFunc_eq hX)).toRingEquiv.trans
      (IsScalarTower.toAlgHom k' (RatFunc k') F').equivFieldRange.symm.toRingEquiv
  have he : (algebraMap C F).comp (e : RatFunc k →+* C) = algebraMap (RatFunc k) F := by
    ext r
    rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, AlgEquiv.coe_toRingEquiv,
      IntermediateField.algebraMap_apply, AlgHom.equivFieldRange_apply_coe,
      IsScalarTower.toAlgHom_apply]
  have he' : (algebraMap (RatFunc k') F').comp (e' : C' →+* RatFunc k') = algebraMap C' F' := by
    ext c
    rw [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
      AlgEquiv.coe_toRingEquiv, AlgEquiv.coe_toRingEquiv,
      ← IsScalarTower.toAlgHom_apply k' (RatFunc k') F', ← AlgHom.equivFieldRange_apply_coe,
      AlgEquiv.apply_symm_apply, IntermediateField.equivOfEq_apply,
      IntermediateField.algebraMap_apply]
  have hbC_fn : (bC : ι → F) = b := funext fun i ↦ Module.Basis.mapCoeffs_apply _ _ _ i
  have hb'_fn : (constantExtensionRatFuncBasis H hcomp hX b : ι → F') =
      constantExtensionBasisOfLinearDisjoint H hcomp C bC := by
    ext i
    rw [coe_constantExtensionRatFuncBasis, constantExtensionBasisOfLinearDisjoint_apply,
      Module.Basis.mapCoeffs_apply]
  apply (algebraMap (RatFunc k') F').injective
  rw [hb'_fn, ← Algebra.discr_eq_of_ringEquiv e' he', ← RingEquiv.coe_toRingHom,
    ← RingHom.comp_apply, he', IntermediateField.algebraMap_apply,
    coe_discr_constantExtensionBasisOfLinearDisjoint H hcomp C bC, hbC_fn,
    ← Algebra.discr_eq_of_ringEquiv e he, IsScalarTower.algebraMap_apply C F F',
    ← RingEquiv.coe_toRingHom, ← RingHom.comp_apply (algebraMap C F), he,
    algebraMap_mapCoeffRingHom hX]

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
    ((RatFunc.mapCoeffRingHom (algebraMap k k')).comp (algebraMap S (RatFunc k))).codRestrict
      (P'.restrict k' (RatFunc k')).integers fun s ↦ by
        rw [mem_integers_restrict_iff, RingHom.comp_apply, algebraMap_mapCoeffRingHom hX]
        exact hS s
  obtain ⟨p, hp_monic, hp_eval⟩ := hx
  refine ⟨p.map g, hp_monic.map g, ?_⟩
  rw [eval₂_map]
  have heq : (algebraMap (P'.restrict k' (RatFunc k')).integers F').comp g =
      (algebraMap F F').comp (algebraMap S F) := by
    ext s
    rw [RingHom.comp_apply, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (P'.restrict k' (RatFunc k')).integers (RatFunc k') F',
      ValuationSubring.algebraMap_apply, RingHom.codRestrict_apply, RingHom.comp_apply,
      algebraMap_mapCoeffRingHom hX, ← IsScalarTower.algebraMap_apply S (RatFunc k) F]
  rw [heq]
  have hzero := congrArg (algebraMap F F') hp_eval
  rw [map_zero, Polynomial.hom_eval₂] at hzero
  exact hzero

private theorem differentExponent_eq_zero_of_discr_mem_and_inv_mem
    [FiniteDimensional (RatFunc k') F'] [Algebra.IsSeparable (RatFunc k') F']
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
  have hd_mem : RatFunc.mapCoeffRingHom (algebraMap k k') (Algebra.discr (RatFunc k) b) ∈
      (P'.restrict k' (RatFunc k')).integers := by
    rwa [mem_integers_restrict_iff, algebraMap_mapCoeffRingHom hX]
  have hd_inv_mem :
      (RatFunc.mapCoeffRingHom (algebraMap k k') (Algebra.discr (RatFunc k) b))⁻¹ ∈
        (P'.restrict k' (RatFunc k')).integers := by
    rwa [← map_inv₀, mem_integers_restrict_iff, algebraMap_mapCoeffRingHom hX]
  have hd_ord : (P'.restrict k' (RatFunc k')).ord
      (Algebra.discr (RatFunc k') (constantExtensionRatFuncBasis H hcomp hX b)) = 0 := by
    rw [discr_constantExtensionRatFuncBasis H hcomp hX b]
    exact (P'.restrict k' (RatFunc k')).ord_eq_zero_of_mem_integers_of_inv_mem hd_mem hd_inv_mem
  exact differentExponent_eq_zero_of_ord_discr_eq_zero k' (RatFunc k') P' hb hd_ord

/-- **Separability over `RatFunc` persists in any constant compositum** with compatible `X`, even
when `k' / k` is transcendental or inseparable. -/
theorem _root_.TauCeti.isSeparable_ratFunc_of_constantCompositum_eq_top
    [Algebra.IsSeparable (RatFunc k) F]
    (hcomp : constantCompositum F k' F' = ⊤)
    (hX : algebraMap F F' (algebraMap (RatFunc k) F RatFunc.X) =
      algebraMap (RatFunc k') F' RatFunc.X) :
    Algebra.IsSeparable (RatFunc k') F' := by
  have : Algebra.IsSeparable k⟮algebraMap (RatFunc k) F RatFunc.X⟯ F :=
    isSeparable_adjoin_algebraMap_X_iff.mpr inferInstance
  have hsep := isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k) hcomp
    (S := {algebraMap (RatFunc k) F RatFunc.X})
  rw [Set.image_singleton, hX] at hsep
  exact isSeparable_adjoin_algebraMap_X_iff.mp hsep

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
    haveI := finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
    ramificationIdx (RatFunc k') P' = 1 := by
  classical
  have := finiteDimensional_ratFunc_of_constantCompositum_eq_top hcomp hX
  have : Algebra.IsSeparable (RatFunc k') F' :=
    isSeparable_ratFunc_of_constantCompositum_eq_top hcomp hX
  let A₀ : ValuationSubring (RatFunc k) :=
    P'.integers.comap ((algebraMap F F').comp (algebraMap (RatFunc k) F))
  have hd0 : differentExponent k' (RatFunc k') P' = 0 := by
    by_cases hA₀ : A₀ = ⊤
    · let b := Module.finBasis (RatFunc k) F
      have hall : ∀ f : RatFunc k, algebraMap F F' (algebraMap (RatFunc k) F f) ∈ P'.integers :=
        fun f ↦ ValuationSubring.mem_comap.mp (hA₀.symm ▸ trivial : f ∈ A₀)
      refine differentExponent_eq_zero_of_discr_mem_and_inv_mem H hcomp hX P' b
        (fun i ↦ ?_) (hall _) (hall _)
      rw [coe_constantExtensionRatFuncBasis]
      exact isIntegral_restrict_ratFunc_of_isIntegral_ring hX P' (S := RatFunc k)
        (fun s ↦ hall s) (IsIntegral.of_finite (RatFunc k) (b i))
    · have hkA₀ : ∀ c : k, algebraMap k (RatFunc k) c ∈ A₀ := fun c ↦ by
        rw [ValuationSubring.mem_comap, RingHom.comp_apply,
          ← IsScalarTower.algebraMap_apply k (RatFunc k) F,
          ← IsScalarTower.algebraMap_apply k F F', IsScalarTower.algebraMap_apply k k' F']
        exact P'.algebraMap_mem_integers _
      let Q := ofValuationSubring (IsFunctionField.ratFunc k) hkA₀ hA₀
      have hQint : Q.integers = A₀ := integers_ofValuationSubring _ hkA₀ hA₀
      have hQmem : ∀ f ∈ Q.integers,
          algebraMap F F' (algebraMap (RatFunc k) F f) ∈ P'.integers := fun f hf ↦ by
        rwa [hQint, ValuationSubring.mem_comap, RingHom.comp_apply] at hf
      have hQunr : Q.IsUnramified (k' := k) (F' := F) := hQ Q fun f ↦ by
        rw [hQint, ValuationSubring.mem_comap, RingHom.comp_apply]
      let b := localIntegralBasis F Q
      have hdQ : Q.ord (Algebra.discr (RatFunc k) b) = 0 :=
        ord_discr_localIntegralBasis_eq_zero (IsFunctionField.ratFunc k) hQunr
      refine differentExponent_eq_zero_of_discr_mem_and_inv_mem H hcomp hX P' b
        (fun i ↦ ?_)
        (hQmem _ (Q.mem_integers_iff_ord_nonneg.mpr hdQ.ge))
        (hQmem _ (Q.mem_integers_iff_ord_nonneg.mpr (by rw [Q.ord_inv, hdQ, neg_zero])))
      rw [coe_constantExtensionRatFuncBasis]
      have hb_int : ∀ j, IsIntegral Q.integers (b j) :=
        (isIntegralBasis_localIntegralBasis F Q).isIntegral
      exact isIntegral_restrict_ratFunc_of_isIntegral_ring hX P' (S := Q.integers)
        (fun s ↦ hQmem s s.2) (hb_int i)
  have hle := ramificationIdx_le_differentExponent_add_one k' (RatFunc k') P'
  have hpos := ramificationIdx_pos (RatFunc k') P'
  omega

end UnramifiedTranscendentalBaseChange

end Place

end TauCeti
