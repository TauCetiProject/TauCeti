/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Extensions of valued rings preserving the value group

Let `B / A` be an extension of commutative rings carrying compatible valuative relations
(`ValuativeExtension A B`). The structure morphism induces the strictly monotone homomorphism
`ValuativeExtension.mapValueGroupWithZero A B` of value groups with zero. When this map is
surjective — as holds for unramified extensions and for completions of valued fields — it upgrades
to an order-monoid isomorphism, so properties of the value group pass from `A` to `B`.

For an extension of valued fields `L / K` with surjective `mapValueGroupWithZero K L`, every value
of `L` is already realized by an element of `K`. Consequently, the maximal ideal of `𝒪[K]`
generates the maximal ideal of `𝒪[L]`, discrete valuation rings and their irreducible elements
(uniformizers) are preserved, and nonzero base-field values are coinitial in `L`.

## Main definitions

* `ValuativeExtension.valueGroupWithZeroOrderMonoidIsoOfSurjective`: the order-monoid isomorphism
  `ValueGroupWithZero A ≃*o ValueGroupWithZero B` when `mapValueGroupWithZero A B` is surjective.

## Main results

* `ValuativeExtension.mapValueGroupWithZero_comp`: functoriality of `mapValueGroupWithZero` in an
  algebra tower.
* `ValuativeRel.IsDiscrete.of_mapValueGroupWithZero_surjective` and
  `ValuativeRel.IsRankLeOne.of_mapValueGroupWithZero_surjective`: discreteness and rank at most one
  pass along extensions with surjective value-group map.
* `ValuativeExtension.map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective`: `𝓂[K]` generates
  `𝓂[L]` when `mapValueGroupWithZero K L` is surjective.
* `ValuativeExtension.isDiscreteValuationRing_of_mapValueGroupWithZero_surjective` and
  `ValuativeExtension.irreducible_algebraMap_of_mapValueGroupWithZero_surjective`: discrete
  valuation rings and irreducible integers (uniformizers) pass along such extensions.
-/

public section

open ValuativeRel IsLocalRing

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

/-- Discreteness of the valuative relation passes along an extension whose value-group map is
surjective. -/
theorem _root_.ValuativeRel.IsDiscrete.of_mapValueGroupWithZero_surjective [IsDiscrete A]
    (h : Function.Surjective (mapValueGroupWithZero A B)) : IsDiscrete B := by
  let e := valueGroupWithZeroOrderMonoidIsoOfSurjective h
  obtain ⟨γ, hγ1, hγmax⟩ := IsDiscrete.has_maximal_element (R := A)
  refine ⟨⟨e γ, ?_, fun δ hδ ↦ ?_⟩⟩
  · rwa [← map_one e, map_lt_map_iff]
  · rw [← e.apply_symm_apply δ, map_le_map_iff]
    refine hγmax _ ?_
    rwa [← map_lt_map_iff e, e.apply_symm_apply, map_one]

/-- Rank at most one passes along an extension whose value-group map is surjective. -/
theorem _root_.ValuativeRel.IsRankLeOne.of_mapValueGroupWithZero_surjective [IsRankLeOne A]
    (h : Function.Surjective (mapValueGroupWithZero A B)) : IsRankLeOne B := by
  let e := valueGroupWithZeroOrderMonoidIsoOfSurjective h
  obtain ⟨⟨f, hf⟩⟩ := IsRankLeOne.nonempty (R := A)
  exact ⟨⟨f.comp e.symm.toMonoidWithZeroHom, hf.comp e.symm.strictMono⟩⟩

end Ring

section Field

variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

/-- Between valued fields, `mapValueGroupWithZero K L` is surjective if and only if every element
of `L` has the same valuation as the image of some element of `K`. -/
theorem mapValueGroupWithZero_surjective_iff :
    Function.Surjective (mapValueGroupWithZero K L) ↔
      ∀ y : L, ∃ x : K, algebraMap K L x =ᵥ y := by
  refine ⟨fun h y ↦ ?_, fun h γ ↦ ?_⟩
  · obtain ⟨γ, hγ⟩ := h (valuation L y)
    obtain ⟨x, rfl⟩ := valuation_surjective γ
    rw [mapValueGroupWithZero_valuation] at hγ
    exact ⟨x, ((valuation L).veq_iff_eq).2 hγ⟩
  · obtain ⟨y, rfl⟩ := valuation_surjective γ
    obtain ⟨x, hxy⟩ := h y
    exact ⟨valuation K x, by rw [mapValueGroupWithZero_valuation, ((valuation L).veq_iff_eq).1 hxy]⟩

/-- When `mapValueGroupWithZero K L` is surjective, nonzero base-field elements are coinitial in
`L` for the valuative relation. -/
theorem exists_ne_zero_vle_of_mapValueGroupWithZero_surjective
    (h : Function.Surjective (mapValueGroupWithZero K L)) {y : L} (hy : y ≠ 0) :
    ∃ x : K, x ≠ 0 ∧ algebraMap K L x ≤ᵥ y := by
  obtain ⟨x, hxy⟩ := mapValueGroupWithZero_surjective_iff.1 h y
  refine ⟨x, ?_, hxy.1⟩
  rintro rfl
  exact hy (((valuation L).zero_iff).1
    (((valuation L).veq_iff_eq).1 hxy.symm |>.trans (by simp)))

/-- When `mapValueGroupWithZero K L` is surjective, the maximal ideal of `𝒪[K]` generates the
maximal ideal of `𝒪[L]`. -/
theorem map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective
    (h : Function.Surjective (mapValueGroupWithZero K L)) :
    𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]) = 𝓂[L] := by
  refine le_antisymm ?_ fun z hz ↦ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    refine (valuation L).mem_maximalIdeal_iff.2 ?_
    rw [TauCeti.coe_algebraMap_integerRing]
    have hx' : valuation K (x : K) < 1 := (valuation K).mem_maximalIdeal_iff.1 hx
    rw [← map_one (valuation K), ← (valuation K).vlt_iff_lt] at hx'
    rw [← map_one (valuation L), ← (valuation L).vlt_iff_lt, ← (algebraMap K L).map_one]
    exact vlt_iff_vlt.2 hx'
  · rcases eq_or_ne z 0 with rfl | hz0
    · exact Ideal.zero_mem _
    have hzl0 : (z : L) ≠ 0 := ZeroMemClass.coe_eq_zero.not.2 hz0
    obtain ⟨x, hxz⟩ := mapValueGroupWithZero_surjective_iff.1 h (z : L)
    have hval : valuation L (algebraMap K L x) = valuation L (z : L) :=
      ((valuation L).veq_iff_eq).1 hxz
    have hxlt1 : valuation K x < 1 := by
      have hzlt1 : valuation L (z : L) < 1 := (valuation L).mem_maximalIdeal_iff.1 hz
      rw [← hval, ← mapValueGroupWithZero_valuation, ← map_one (mapValueGroupWithZero K L)] at hzlt1
      exact (mapValueGroupWithZero_strictMono (A := K) (B := L)).lt_iff_lt.1 hzlt1
    let x₀ : 𝒪[K] := ⟨x, hxlt1.le⟩
    have hx₀m : x₀ ∈ 𝓂[K] := (valuation K).mem_maximalIdeal_iff.2 hxlt1
    have hax0 : algebraMap K L x ≠ 0 := by
      intro h0
      exact hzl0 (((valuation L).zero_iff).1 (hval.symm.trans (by simp [h0])))
    have hu_le : valuation L ((z : L) / algebraMap K L x) ≤ 1 := by
      rw [map_div₀, hval, div_self ((valuation L).ne_zero_iff.2 hzl0)]
    let u : 𝒪[L] := ⟨(z : L) / algebraMap K L x, hu_le⟩
    have hzu : z = algebraMap 𝒪[K] 𝒪[L] x₀ * u := by
      ext
      rw [Subring.coe_mul, TauCeti.coe_algebraMap_integerRing]
      exact (mul_div_cancel₀ (z : L) hax0).symm
    rw [hzu]
    exact Ideal.mul_mem_right u _ (Ideal.mem_map_of_mem _ hx₀m)

/-- When `𝒪[K]` is a discrete valuation ring, the canonical valuation of `K` is rank-one
discrete. -/
instance _root_.ValuativeRel.isRankOneDiscrete_valuation [IsDiscreteValuationRing 𝒪[K]] :
    (valuation K).IsRankOneDiscrete :=
  have := ValuationSubring.isRankOneDiscrete_valuation (valuation K).valuationSubring
  .of_isEquiv (valuation K).isEquiv_valuation_valuationSubring.symm

/-- Every irreducible element of `𝒪[K]` is a uniformizer for the canonical valuation `valuation K`
when `𝒪[K]` is a discrete valuation ring. -/
theorem _root_.Irreducible.isUniformizer_valuation [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]}
    (hϖ : Irreducible ϖ) : (valuation K).IsUniformizer (ϖ : K) :=
  Valuation.isUniformizer_of_maximalIdeal_eq_span (valuation K) hϖ.maximalIdeal_eq

/-- When `𝒪[K]` is a discrete valuation ring and `mapValueGroupWithZero K L` is surjective, the
canonical valuation of `L` is rank-one discrete. -/
theorem isRankOneDiscrete_valuation_of_mapValueGroupWithZero_surjective
    [IsDiscreteValuationRing 𝒪[K]] (h : Function.Surjective (mapValueGroupWithZero K L)) :
    (valuation L).IsRankOneDiscrete := by
  obtain ⟨γ, hγgen, hγ1⟩ :=
    (inferInstance : (valuation K).IsRankOneDiscrete).exists_generator_lt_one
  let e := valueGroupWithZeroOrderMonoidIsoOfSurjective h
  let eu : (ValueGroupWithZero K)ˣ ≃* (ValueGroupWithZero L)ˣ := Units.mapEquiv e.toMulEquiv
  refine ⟨⟨eu γ, ?_, ?_⟩⟩
  · have htopK : MonoidWithZeroHom.valueGroup (valuation K : K →*₀ ValueGroupWithZero K) = ⊤ :=
      (Subgroup.eq_top_iff' _).2 fun u ↦
        MonoidWithZeroHom.mem_valueGroup _ (valuation_surjective (K := K) u.1)
    have htopL : MonoidWithZeroHom.valueGroup (valuation L : L →*₀ ValueGroupWithZero L) = ⊤ :=
      (Subgroup.eq_top_iff' _).2 fun u ↦
        MonoidWithZeroHom.mem_valueGroup _ (valuation_surjective (K := L) u.1)
    rw [htopL]
    refine (Subgroup.eq_top_iff' _).2 fun x ↦ ?_
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.1 (hγgen.symm ▸ htopK.symm ▸ Subgroup.mem_top (eu.symm x))
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by rw [← map_zpow, hn, eu.apply_symm_apply]⟩
  · rw [← Units.val_lt_val]
    have hcoe : ((eu γ : (ValueGroupWithZero L)ˣ) : ValueGroupWithZero L) =
        mapValueGroupWithZero K L γ := by
      simp [eu, e]
    rw [hcoe, Units.val_one, ← map_one (mapValueGroupWithZero K L)]
    exact (mapValueGroupWithZero_strictMono (A := K) (B := L)) (Units.val_lt_val.2 hγ1)

/-- When `𝒪[K]` is a discrete valuation ring and `mapValueGroupWithZero K L` is surjective, `𝒪[L]`
is also a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_mapValueGroupWithZero_surjective
    [IsDiscreteValuationRing 𝒪[K]] (h : Function.Surjective (mapValueGroupWithZero K L)) :
    IsDiscreteValuationRing 𝒪[L] := by
  have : (valuation L).IsRankOneDiscrete :=
    isRankOneDiscrete_valuation_of_mapValueGroupWithZero_surjective h
  exact Valuation.valuationSubring_isDiscreteValuationRing (valuation L)

/-- When `𝒪[K]` is a discrete valuation ring and `mapValueGroupWithZero K L` is surjective, an
element of `𝒪[K]` is irreducible if and only if its image in `𝒪[L]` is irreducible. -/
theorem irreducible_algebraMap_iff_of_mapValueGroupWithZero_surjective
    [IsDiscreteValuationRing 𝒪[K]] (h : Function.Surjective (mapValueGroupWithZero K L))
    {ϖ : 𝒪[K]} :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ) ↔ Irreducible ϖ := by
  have : IsDiscreteValuationRing 𝒪[L] :=
    isDiscreteValuationRing_of_mapValueGroupWithZero_surjective h
  refine ⟨fun hL ↦ ?_, fun hϖ ↦ ?_⟩
  · have hvalL : valuation L (algebraMap K L (ϖ : K)) =
        (Valuation.IsRankOneDiscrete.generator (valuation L) : ValueGroupWithZero L) := by
      have hu := hL.isUniformizer_valuation
      rwa [TauCeti.coe_algebraMap_integerRing, Valuation.IsUniformizer.iff] at hu
    obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have hL₀ : Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ₀) := by
      rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
        ← map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective h,
        (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).1 hϖ₀,
        Ideal.map_span, Set.image_singleton]
    have hvalL₀ : valuation L (algebraMap K L (ϖ₀ : K)) =
        (Valuation.IsRankOneDiscrete.generator (valuation L) : ValueGroupWithZero L) := by
      have hu := hL₀.isUniformizer_valuation
      rwa [TauCeti.coe_algebraMap_integerRing, Valuation.IsUniformizer.iff] at hu
    have heqL : valuation L (algebraMap K L (ϖ : K)) = valuation L (algebraMap K L (ϖ₀ : K)) :=
      hvalL.trans hvalL₀.symm
    rw [← mapValueGroupWithZero_valuation, ← mapValueGroupWithZero_valuation] at heqL
    have heqK : valuation K (ϖ : K) = valuation K (ϖ₀ : K) :=
      (mapValueGroupWithZero_strictMono (A := K) (B := L)).injective heqL
    have hv := Valuation.integer.integers (valuation K)
    exact (associated_of_dvd_dvd (hv.dvd_iff_le.2 heqK.le) (hv.dvd_iff_le.2 heqK.ge)).irreducible
      hϖ₀
  · rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective h,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
      Ideal.map_span, Set.image_singleton]

/-- When `𝒪[K]` is a discrete valuation ring and `mapValueGroupWithZero K L` is surjective, every
irreducible element (uniformizer) of `𝒪[K]` stays irreducible in `𝒪[L]`. -/
theorem irreducible_algebraMap_of_mapValueGroupWithZero_surjective
    [IsDiscreteValuationRing 𝒪[K]] (h : Function.Surjective (mapValueGroupWithZero K L))
    {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap 𝒪[K] 𝒪[L] ϖ) :=
  (irreducible_algebraMap_iff_of_mapValueGroupWithZero_surjective h).2 hϖ

/-- The induced map on residue fields of a `ValuativeExtension` intertwines the residue maps. -/
theorem residueField_algebraMap_residue (x : 𝒪[K]) :
    algebraMap 𝓀[K] 𝓀[L] (residue 𝒪[K] x) = residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) :=
  Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap (valuation K) (valuation L) x

end Field

end ValuativeExtension
