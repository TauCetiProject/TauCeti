/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import TauCeti.RingTheory.Valuation.ValuativeRel.Basic
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Valued extensions with unchanged value group

Let `B / A` be an extension of rings carrying compatible valuative relations
(`ValuativeExtension A B`). If the value-group map `ValuativeExtension.mapValueGroupWithZero A B`
is surjective, it upgrades to an order-monoid isomorphism. Consequently discreteness and rank at
most one pass to the extension.

For an extension of valued fields `L / K` with surjective `mapValueGroupWithZero K L`, every value
of `L` is already attained on `K`. Thus nonzero base-field values are coinitial in `L`, the maximal
ideal of `𝒪[K]` generates the maximal ideal of `𝒪[L]`, discrete valuation rings pass from `𝒪[K]`
to `𝒪[L]`, and an element of `𝒪[K]` is irreducible if and only if its image in `𝒪[L]` is
irreducible (with no discreteness assumption needed for irreducibility transfer). These statements
apply to unramified algebraic extensions and to completions without requiring finite degree.

## Main definitions

* `ValuativeExtension.valueGroupWithZeroOrderMonoidIsoOfSurjective`: the order-monoid isomorphism
  `ValueGroupWithZero A ≃*o ValueGroupWithZero B` when `mapValueGroupWithZero A B` is surjective.

## Main results

* `ValuativeExtension.mapValueGroupWithZero_comp`: functoriality of `mapValueGroupWithZero` in an
  algebra tower.
* `ValuativeExtension.mapValueGroupWithZero_surjective_of_forall_exists_veq` and
  `ValuativeExtension.mapValueGroupWithZero_surjective_iff`: value-level characterizations of
  surjectivity of `mapValueGroupWithZero`.
* `ValuativeRel.IsDiscrete.of_surjective_mapValueGroupWithZero` and
  `ValuativeRel.IsRankLeOne.of_surjective_mapValueGroupWithZero`: discreteness and rank at most one
  pass along extensions with surjective value-group map.
* `ValuativeExtension.map_maximalIdeal_eq_of_surjective_mapValueGroupWithZero`: `𝓂[K]` generates
  `𝓂[L]` when `mapValueGroupWithZero K L` is surjective.
* `ValuativeExtension.isDiscreteValuationRing_of_surjective_mapValueGroupWithZero`: discrete
  valuation rings pass along extensions with surjective value-group map.
* `Irreducible.algebraMap_integer_of_surjective_mapValueGroupWithZero` and
  `ValuativeExtension.irreducible_algebraMap_integer_iff_of_surjective_mapValueGroupWithZero`:
  irreducible integers pass in both directions along extensions with surjective value-group map.
-/

public section

open ValuativeRel IsLocalRing

section SingleField

variable {K : Type*} [Field K] [ValuativeRel K]

/-- When `𝒪[K]` is a discrete valuation ring, the canonical valuation of `K` is rank-one
discrete. -/
instance ValuativeRel.isRankOneDiscrete_valuation [IsDiscreteValuationRing 𝒪[K]] :
    (valuation K).IsRankOneDiscrete :=
  have := ValuationSubring.isRankOneDiscrete_valuation (valuation K).valuationSubring
  .of_isEquiv (valuation K).isEquiv_valuation_valuationSubring.symm

/-- Every irreducible element of `𝒪[K]` is a uniformizer for the canonical valuation `valuation K`
when `𝒪[K]` is a discrete valuation ring. -/
theorem Irreducible.isUniformizer_valuation [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) : (valuation K).IsUniformizer (ϖ : K) :=
  Valuation.isUniformizer_of_maximalIdeal_eq_span (valuation K) hϖ.maximalIdeal_eq

/-- An element of `𝒪[K]` is a uniformizer for `valuation K` if and only if it is irreducible. -/
theorem TauCeti.isUniformizer_valuation_coe_iff [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]} :
    (valuation K).IsUniformizer (ϖ : K) ↔ Irreducible ϖ :=
  ⟨fun h ↦ (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).2
    (Valuation.IsUniformizer.is_generator (π := ϖ) h), fun h ↦ h.isUniformizer_valuation⟩

end SingleField

/-- If every value in an extension is attained on the base, its value-group map is onto. -/
theorem ValuativeExtension.mapValueGroupWithZero_surjective_of_forall_exists_veq
    {A B : Type*} [CommRing A] [DivisionRing B] [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] [ValuativeExtension A B]
    (h : ∀ x : B, ∃ r : A, algebraMap A B r =ᵥ x) :
    Function.Surjective (mapValueGroupWithZero A B) := by
  intro γ
  obtain ⟨x, rfl⟩ := valuation_surjective γ
  obtain ⟨r, hr⟩ := h x
  exact ⟨valuation A r, by
    rw [mapValueGroupWithZero_valuation]
    exact (valuation B).veq_iff_eq.mp hr⟩

namespace ValuativeExtension

section Tower

variable (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
  [ValuativeRel A] [ValuativeRel B] [ValuativeRel C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  [ValuativeExtension A B] [ValuativeExtension B C] [ValuativeExtension A C]

/-- In a compatible algebra tower `A → B → C`, the induced maps on value groups with zero
compose. -/
theorem mapValueGroupWithZero_comp :
    (mapValueGroupWithZero B C).comp (mapValueGroupWithZero A B) =
      mapValueGroupWithZero A C := by
  ext γ
  induction γ using ValueGroupWithZero.ind with | mk r s =>
  simp only [MonoidWithZeroHom.comp_apply, mapValueGroupWithZero_mk]
  congr 1
  · exact (IsScalarTower.algebraMap_apply A B C r).symm
  · ext
    exact (IsScalarTower.algebraMap_apply A B C s.1).symm

/-- Applying `mapValueGroupWithZero` in two steps along a tower agrees with the composite map. -/
@[simp]
theorem mapValueGroupWithZero_comp_apply (γ : ValueGroupWithZero A) :
    mapValueGroupWithZero B C (mapValueGroupWithZero A B γ) =
      mapValueGroupWithZero A C γ :=
  DFunLike.congr_fun (mapValueGroupWithZero_comp A B C) γ

end Tower

section Ring

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-- When `mapValueGroupWithZero A B` is surjective, it upgrades to an order-monoid isomorphism
between the value groups with zero of `A` and `B`. -/
noncomputable def valueGroupWithZeroOrderMonoidIsoOfSurjective
    (h : Function.Surjective (mapValueGroupWithZero A B)) :
    ValueGroupWithZero A ≃*o ValueGroupWithZero B :=
  { MulEquiv.ofBijective (mapValueGroupWithZero A B)
      ⟨(mapValueGroupWithZero_strictMono (A := A) (B := B)).injective, h⟩ with
    map_le_map_iff' := (mapValueGroupWithZero_strictMono (A := A) (B := B)).le_iff_le }

@[simp]
theorem valueGroupWithZeroOrderMonoidIsoOfSurjective_apply
    (h : Function.Surjective (mapValueGroupWithZero A B)) (γ : ValueGroupWithZero A) :
    valueGroupWithZeroOrderMonoidIsoOfSurjective h γ = mapValueGroupWithZero A B γ :=
  (rfl)

@[simp]
theorem valueGroupWithZeroOrderMonoidIsoOfSurjective_symm_mapValueGroupWithZero
    (h : Function.Surjective (mapValueGroupWithZero A B)) (γ : ValueGroupWithZero A) :
    (valueGroupWithZeroOrderMonoidIsoOfSurjective h).symm (mapValueGroupWithZero A B γ) = γ := by
  rw [← valueGroupWithZeroOrderMonoidIsoOfSurjective_apply h, OrderMonoidIso.symm_apply_apply]

end Ring

end ValuativeExtension

namespace ValuativeRel

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-- A valued extension with surjective map on value groups preserves discreteness. -/
theorem IsDiscrete.of_surjective_mapValueGroupWithZero [IsDiscrete A]
    (h : Function.Surjective (ValuativeExtension.mapValueGroupWithZero A B)) : IsDiscrete B := by
  obtain ⟨γ, hγ, hmax⟩ := IsDiscrete.has_maximal_element (R := A)
  have hm := ValuativeExtension.mapValueGroupWithZero_strictMono (A := A) (B := B)
  refine ⟨ValuativeExtension.mapValueGroupWithZero A B γ, by simpa using hm hγ, ?_⟩
  intro δ hδ
  obtain ⟨δ, rfl⟩ := h δ
  exact hm.monotone (hmax δ (hm.lt_iff_lt.mp (by simpa using hδ)))

/-- A valued extension with surjective map on value groups preserves rank at most one. -/
theorem IsRankLeOne.of_surjective_mapValueGroupWithZero [IsRankLeOne A]
    (h : Function.Surjective (ValuativeExtension.mapValueGroupWithZero A B)) : IsRankLeOne B := by
  let e := ValuativeExtension.valueGroupWithZeroOrderMonoidIsoOfSurjective h
  obtain ⟨f⟩ := IsRankLeOne.nonempty (R := A)
  exact ⟨⟨f.emb.comp e.symm.toMonoidWithZeroHom, f.strictMono.comp e.symm.strictMono⟩⟩

end ValuativeRel

namespace Irreducible

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- An irreducible element remains irreducible in a valued extension with unchanged value group.
Neither valuation ring needs to be assumed discrete. -/
theorem algebraMap_integer_of_surjective_mapValueGroupWithZero {π : (valuation K).integer}
    (hπ : Irreducible π)
    (h : Function.Surjective (ValuativeExtension.mapValueGroupWithZero K L)) :
    Irreducible (algebraMap (valuation K).integer (valuation L).integer π) := by
  let π' := algebraMap (valuation K).integer (valuation L).integer π
  have he := ValuativeRel.isEquiv ((valuation L).comap (algebraMap K L)) (valuation K)
  have hπ' : valuation L (π' : L) < 1 := by
    rw [Valuation.HasExtension.val_algebraMap]
    exact he.lt_one_iff_lt_one.mpr (Valuation.integer.v_irreducible_lt_one hπ)
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π'
  · intro hz
    have hz' : algebraMap K L (π : K) = 0 := by
      simpa [π', Valuation.HasExtension.val_algebraMap] using congrArg Subtype.val hz
    exact hπ.ne_zero (Subtype.ext <| (algebraMap K L).injective (by simpa using hz'))
  · apply le_antisymm
    · intro x hx
      have hxv := (valuation L).mem_maximalIdeal_iff.mp hx
      obtain ⟨γ, hγ⟩ := h (valuation L (x : L))
      obtain ⟨r, rfl⟩ := valuation_surjective γ
      rw [ValuativeExtension.mapValueGroupWithZero_valuation] at hγ
      have hr : valuation K r < 1 := he.lt_one_iff_lt_one.mp (by simpa [hγ] using hxv)
      have hle : valuation K r ≤ valuation K (π : K) := by
        by_cases hle : valuation K r ≤ valuation K (π : K)
        · exact hle
        have hd : (⟨r, hr.le⟩ : (valuation K).integer) ∣ π :=
          (Valuation.integer.integers (valuation K)).dvd_iff_le.mpr (le_of_not_ge hle)
        have hn : ¬IsUnit (⟨r, hr.le⟩ : (valuation K).integer) :=
          Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hr
        exact (Valuation.integer.integers (valuation K)).dvd_iff_le.mp
          (((hπ.dvd_iff.mp hd).resolve_left hn).dvd)
      have hxπ : valuation L (x : L) ≤ valuation L (π' : L) := by
        rw [Valuation.HasExtension.val_algebraMap, ← hγ]
        simpa only [Valuation.comap_apply] using (he r (π : K)).mpr hle
      rw [Ideal.mem_span_singleton]
      exact (Valuation.integer.integers (valuation L)).dvd_iff_le.mpr hxπ
    · exact (Ideal.span_singleton_le_iff_mem _).mpr
        ((valuation L).mem_maximalIdeal_iff.mpr hπ')

end Irreducible

namespace ValuativeExtension

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- Between valued fields, `mapValueGroupWithZero K L` is surjective if and only if every element
of `L` has the same valuation as the image of some element of `K`. -/
theorem mapValueGroupWithZero_surjective_iff :
    Function.Surjective (mapValueGroupWithZero K L) ↔
      ∀ y : L, ∃ x : K, algebraMap K L x =ᵥ y := by
  refine ⟨fun h y ↦ ?_, mapValueGroupWithZero_surjective_of_forall_exists_veq⟩
  obtain ⟨γ, hγ⟩ := h (valuation L y)
  obtain ⟨x, rfl⟩ := valuation_surjective γ
  exact ⟨x, ((valuation L).veq_iff_eq).2 (by rwa [mapValueGroupWithZero_valuation] at hγ)⟩

/-- When `mapValueGroupWithZero K L` is surjective, nonzero base-field elements are coinitial in
`L` for the valuative relation. -/
theorem exists_ne_zero_vle_of_surjective_mapValueGroupWithZero
    (h : Function.Surjective (mapValueGroupWithZero K L)) {y : L} (hy : y ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ algebraMap K L x ≤ᵥ y := by
  obtain ⟨x, hxy⟩ := mapValueGroupWithZero_surjective_iff.1 h y
  refine ⟨x, ?_, hxy.1⟩
  rintro rfl
  exact hy (((valuation L).zero_iff).1 (((valuation L).veq_iff_eq).1 hxy.symm |>.trans (by simp)))

/-- When `mapValueGroupWithZero K L` is surjective, the maximal ideal of `𝒪[K]` generates the
maximal ideal of `𝒪[L]`. -/
theorem map_maximalIdeal_eq_of_surjective_mapValueGroupWithZero
    (h : Function.Surjective (mapValueGroupWithZero K L)) :
    𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) = 𝓂[L] := by
  refine le_antisymm ?_ fun z hz ↦ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact (valuation L).mem_maximalIdeal_iff.2 <| by
      rw [Valuation.HasExtension.val_algebraMap, valuation_algebraMap_lt_one_iff]
      exact (valuation K).mem_maximalIdeal_iff.1 hx
  · rcases eq_or_ne z 0 with rfl | hz0
    · exact Ideal.zero_mem _
    have hzl0 : (z : L) ≠ 0 := ZeroMemClass.coe_eq_zero.not.2 hz0
    obtain ⟨x, hxz⟩ := mapValueGroupWithZero_surjective_iff.1 h (z : L)
    have hval : valuation L (algebraMap K L x) = valuation L (z : L) :=
      ((valuation L).veq_iff_eq).1 hxz
    have hxlt1 : valuation K x < 1 := (valuation_algebraMap_lt_one_iff x).1 <|
      hval.trans_lt ((valuation L).mem_maximalIdeal_iff.1 hz)
    have hax0 : algebraMap K L x ≠ 0 :=
      (valuation L).ne_zero_iff.1 (hval.trans_ne ((valuation L).ne_zero_iff.2 hzl0))
    have hu_le : valuation L ((z : L) / algebraMap K L x) ≤ 1 := by
      rw [map_div₀, hval, div_self ((valuation L).ne_zero_iff.2 hzl0)]
    have hzu : z = algebraMap 𝒪[K] 𝒪[L] ⟨x, hxlt1.le⟩ * ⟨(z : L) / algebraMap K L x, hu_le⟩ :=
      Subtype.ext <| by
        rw [Subring.coe_mul, Valuation.HasExtension.val_algebraMap]
        exact (mul_div_cancel₀ (z : L) hax0).symm
    exact hzu ▸ Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem _ ((valuation K).mem_maximalIdeal_iff.2 hxlt1))

/-- When `𝒪[K]` is a discrete valuation ring and `mapValueGroupWithZero K L` is surjective, the
canonical valuation of `L` is rank-one discrete. -/
theorem isRankOneDiscrete_valuation_of_surjective_mapValueGroupWithZero
    [IsDiscreteValuationRing 𝒪[K]] (h : Function.Surjective (mapValueGroupWithZero K L)) :
    (valuation L).IsRankOneDiscrete := by
  obtain ⟨γ, hγgen, hγ1⟩ :=
    (inferInstance : (valuation K).IsRankOneDiscrete).exists_generator_lt_one
  let e := valueGroupWithZeroOrderMonoidIsoOfSurjective h
  let eu : (ValueGroupWithZero K)ˣ ≃* (ValueGroupWithZero L)ˣ := Units.mapEquiv e.toMulEquiv
  refine ⟨⟨eu γ, ?_, ?_⟩⟩
  · rw [TauCeti.valueGroup_valuation_eq_top L]
    refine (Subgroup.eq_top_iff' _).2 fun x ↦ ?_
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
      (hγgen.symm ▸ (TauCeti.valueGroup_valuation_eq_top K).symm ▸ Subgroup.mem_top (eu.symm x))
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← map_zpow, hn, eu.apply_symm_apply]⟩
  · rw [← Units.val_lt_val, Units.coe_mapEquiv, OrderMonoidIso.toMulEquiv_eq_coe,
      OrderMonoidIso.coe_mulEquiv, Units.val_one, ← map_one e, map_lt_map_iff, ← Units.val_one,
      Units.val_lt_val]
    exact hγ1

/-- When `𝒪[K]` is a discrete valuation ring and `mapValueGroupWithZero K L` is surjective, `𝒪[L]`
is also a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_surjective_mapValueGroupWithZero
    [IsDiscreteValuationRing 𝒪[K]] (h : Function.Surjective (mapValueGroupWithZero K L)) :
    IsDiscreteValuationRing 𝒪[L] := by
  have := isRankOneDiscrete_valuation_of_surjective_mapValueGroupWithZero h
  exact Valuation.valuationSubring_isDiscreteValuationRing (valuation L)

/-- When `mapValueGroupWithZero K L` is surjective, an element of `𝒪[K]` is irreducible if and
only if its image in `𝒪[L]` is irreducible, with no discreteness assumption on either valuation
ring. -/
theorem irreducible_algebraMap_integer_iff_of_surjective_mapValueGroupWithZero
    (h : Function.Surjective (mapValueGroupWithZero K L)) {ϖ : 𝒪[K]} :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ) ↔ Irreducible ϖ :=
  ⟨fun hL ↦ hL.of_map, fun hϖ ↦ hϖ.algebraMap_integer_of_surjective_mapValueGroupWithZero h⟩

end ValuativeExtension
