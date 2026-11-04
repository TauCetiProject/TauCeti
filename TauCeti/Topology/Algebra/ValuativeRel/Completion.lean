/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.Topology.Algebra.ValuativeRel.Completion
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Valuation.ValuativeRel.ValueGroup
public import TauCeti.Topology.Algebra.IsUniformGroup.Subring
public import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology

/-!
# Arithmetic invariants of the completion of a valued field

Let `K` be a field carrying a valuative relation whose valuation topology comes from a uniform
additive group structure (`[UniformSpace K] [IsUniformAddGroup K] [IsValuativeTopology K]`).
Mathlib constructs the extended valuative relation and valuative topology on `Completion K` and
proves that every valuation value of `Completion K` is already attained on `K`.

This file packages the resulting algebraic consequences for the value group, valuation ring `𝒪[·]`,
maximal ideal `𝓂[·]`, and residue field `𝓀[·]` of `Completion K`, together with adic completeness
of `𝒪[K]` for any complete discretely valued field:

* For any complete discretely valued field `K`, the valuation ring `𝒪[K]` is closed in `K`, hence
  complete, hence `𝓂[K]`-adically complete (`TauCeti.isAdicComplete_maximalIdeal`) and therefore a
  Henselian local ring (`IsAdicComplete.henselianLocalRing`).
* `ValuativeExtension.mapValueGroupWithZero K (Completion K)` is surjective, inducing an
  order-monoid isomorphism `ValueGroupWithZero K ≃*o ValueGroupWithZero (Completion K)` and
  transferring `IsNontrivial`, `IsDiscrete`, `IsRankLeOne`, `IsDiscreteValuationRing`, and
  uniformizers from `K` to `Completion K`.
* `algebraMap 𝒪[K] 𝒪[Completion K]` has dense range, and `algebraMap 𝓀[K] 𝓀[Completion K]` is
  bijective (`UniformSpace.Completion.residueFieldRingEquiv`).

## Main definitions

* `UniformSpace.Completion.valueGroupWithZeroOrderMonoidIso`: the canonical order-monoid
  isomorphism `ValueGroupWithZero K ≃*o ValueGroupWithZero (Completion K)`.
* `UniformSpace.Completion.residueFieldRingEquiv`: the canonical ring isomorphism
  `𝓀[K] ≃+* 𝓀[Completion K]`.

## Main results

* `TauCeti.isAdicComplete_maximalIdeal`: `𝒪[K]` is `𝓂[K]`-adically complete when `K` is complete
  and `𝒪[K]` is a discrete valuation ring.
* `UniformSpace.Completion.mapValueGroupWithZero_surjective`: the value-group map into the
  completion is surjective.
* `UniformSpace.Completion.isDiscrete`, `UniformSpace.Completion.isRankLeOne`,
  `UniformSpace.Completion.isDiscreteValuationRing_integer`, and
  `UniformSpace.Completion.isAdicComplete_maximalIdeal_integer`: discreteness, rank at most one,
  discrete valuation rings, and adic completeness pass to `Completion K`.
* `UniformSpace.Completion.denseRange_algebraMap_integer`: `𝒪[K]` is dense in `𝒪[Completion K]`.
* `UniformSpace.Completion.algebraMap_residueField_bijective`: completion preserves the residue
  field up to canonical isomorphism.
* `UniformSpace.Completion.valuation_eq_of_continuous` and
  `UniformSpace.Completion.valuation_lt_one_of_continuous_integer`: valuation invariance and
  open-unit-ball bounds extend by continuity from `K` and `𝒪[K]` to `Completion K` and
  `𝒪[Completion K]`.

## References

* [N. Bourbaki, *Commutative Algebra*][bourbaki1989b], Chapter VI, §5, no. 3, Proposition 5.
-/

public section

open Filter Topology UniformSpace ValuativeRel IsLocalRing

namespace TauCeti

/-- In a complete valued field `K`, the valuation ring `𝒪[K]` is a complete uniform subspace. -/
theorem completeSpace_integer (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
    [IsValuativeTopology K] [CompleteSpace K] :
    CompleteSpace 𝒪[K] :=
  Valuation.isClosed_integer.completeSpace_coe

/-- In a complete discretely valued field `K`, the valuation ring `𝒪[K]` is `𝓂[K]`-adically
complete. Together with `IsAdicComplete.henselianLocalRing`, this makes `𝒪[K]` a Henselian local
ring without any local-compactness hypothesis on `K`. -/
theorem isAdicComplete_maximalIdeal (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K]
    [IsUniformAddGroup K] [IsValuativeTopology K] [CompleteSpace K]
    [IsDiscreteValuationRing 𝒪[K]] :
    IsAdicComplete 𝓂[K] 𝒪[K] :=
  (isAdic_maximalIdeal K).isAdicComplete_iff.2 ⟨completeSpace_integer K, inferInstance⟩

end TauCeti

namespace UniformSpace.Completion

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsValuativeTopology K]

/-- Every element of `Completion K` has the same valuation as the image of some element of `K`. -/
theorem exists_coe_veq (x : Completion K) : ∃ r : K, (r : Completion K) =ᵥ x := by
  obtain ⟨r, hr⟩ := (valuation K).exists_extension_eq_map x
  exact ⟨r, ((valuation K).extension).veq_iff_eq.2 (by rw [Valuation.extension_apply_coe, hr])⟩

/-- The canonical map of value groups with zero from `K` to `Completion K` is surjective. -/
theorem mapValueGroupWithZero_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero K (Completion K)) :=
  ValuativeExtension.mapValueGroupWithZero_surjective_iff.2 fun x ↦ exists_coe_veq K x

/-- The canonical order-monoid isomorphism between the value groups with zero of `K` and
`Completion K`. -/
noncomputable def valueGroupWithZeroOrderMonoidIso :
    ValueGroupWithZero K ≃*o ValueGroupWithZero (Completion K) :=
  ValuativeExtension.valueGroupWithZeroOrderMonoidIsoOfSurjective
    (mapValueGroupWithZero_surjective K)

@[simp]
theorem valueGroupWithZeroOrderMonoidIso_apply (γ : ValueGroupWithZero K) :
    valueGroupWithZeroOrderMonoidIso K γ =
      ValuativeExtension.mapValueGroupWithZero K (Completion K) γ := by
  rw [valueGroupWithZeroOrderMonoidIso,
    ValuativeExtension.valueGroupWithZeroOrderMonoidIsoOfSurjective_apply]

instance isNontrivial [IsNontrivial K] : IsNontrivial (Completion K) :=
  .of_valuativeExtension K

instance isDiscrete [IsDiscrete K] : IsDiscrete (Completion K) :=
  .of_mapValueGroupWithZero_surjective (mapValueGroupWithZero_surjective K)

instance isRankLeOne [IsRankLeOne K] : IsRankLeOne (Completion K) :=
  .of_mapValueGroupWithZero_surjective (mapValueGroupWithZero_surjective K)

/-- The maximal ideal of `𝒪[K]` generates the maximal ideal of `𝒪[Completion K]`. -/
@[simp]
theorem map_maximalIdeal_integer :
    𝓂[K].map (algebraMap 𝒪[K] 𝒪[Completion K]) = 𝓂[Completion K] :=
  ValuativeExtension.map_maximalIdeal_eq_of_mapValueGroupWithZero_surjective
    (mapValueGroupWithZero_surjective K)

instance isDiscreteValuationRing_integer [IsDiscreteValuationRing 𝒪[K]] :
    IsDiscreteValuationRing 𝒪[Completion K] :=
  ValuativeExtension.isDiscreteValuationRing_of_mapValueGroupWithZero_surjective
    (mapValueGroupWithZero_surjective K)

instance isAdicComplete_maximalIdeal_integer [IsDiscreteValuationRing 𝒪[K]] :
    IsAdicComplete 𝓂[Completion K] 𝒪[Completion K] :=
  TauCeti.isAdicComplete_maximalIdeal (Completion K)

@[simp]
theorem irreducible_algebraMap_integer_iff [IsDiscreteValuationRing 𝒪[K]] {ϖ : 𝒪[K]} :
    Irreducible (algebraMap 𝒪[K] 𝒪[Completion K] ϖ) ↔ Irreducible ϖ :=
  ValuativeExtension.irreducible_algebraMap_iff_of_mapValueGroupWithZero_surjective
    (mapValueGroupWithZero_surjective K)

/-- The valuation ring `𝒪[K]` has dense image inside the valuation ring `𝒪[Completion K]`. -/
theorem denseRange_algebraMap_integer :
    DenseRange (algebraMap 𝒪[K] 𝒪[Completion K]) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_induced, mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨r, hrV, hrv⟩ := (valuation K).exists_coe_mem_extension_eq hV
  have hr1 : valuation K r ≤ 1 := by
    rw [← hrv]
    have hx1 : (x : Completion K) ≤ᵥ 1 := by
      have hx' : valuation (Completion K) (x : Completion K) ≤ 1 := x.2
      rwa [← map_one (valuation (Completion K)), ← (valuation (Completion K)).vle_iff_le] at hx'
    simpa [map_one] using ((valuation K).extension).vle_iff_le.1 hx1
  let r₀ : 𝒪[K] := ⟨r, hr1⟩
  refine ⟨algebraMap 𝒪[K] 𝒪[Completion K] r₀, hVU ?_, r₀, rfl⟩
  have hcoe : ((algebraMap 𝒪[K] 𝒪[Completion K] r₀ : 𝒪[Completion K]) : Completion K) =
      (r : Completion K) :=
    TauCeti.coe_algebraMap_integerRing r₀
  simpa [hcoe] using hrV

/-- The canonical algebra map from the residue field of `K` to the residue field of `Completion K`
is bijective. -/
theorem algebraMap_residueField_bijective :
    Function.Bijective (algebraMap 𝓀[K] 𝓀[Completion K]) := by
  refine ⟨(algebraMap 𝓀[K] 𝓀[Completion K]).injective, fun z ↦ ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z
  have hball : {u : Completion K | valuation (Completion K) u < 1} ∈ 𝓝 (0 : Completion K) := by
    simpa using (IsValuativeTopology.hasBasis_nhds_zero (Completion K)).mem_of_mem (i := 1) trivial
  have hsub : Continuous fun y : Completion K ↦ y - (x : Completion K) :=
    continuous_id.sub continuous_const
  have hVx : ((fun y : Completion K ↦ y - (x : Completion K)) ⁻¹'
      {u : Completion K | valuation (Completion K) u < 1}) ∈ 𝓝 (x : Completion K) := by
    refine (hsub.continuousAt (x := (x : Completion K))).preimage_mem_nhds ?_
    simpa using hball
  have hU : (((↑) : 𝒪[Completion K] → Completion K) ⁻¹'
      ((fun y : Completion K ↦ y - (x : Completion K)) ⁻¹'
        {u : Completion K | valuation (Completion K) u < 1})) ∈ 𝓝 x :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hVx
  obtain ⟨_, hmem, r₀, rfl⟩ := mem_closure_iff_nhds.1 (denseRange_algebraMap_integer K x) _ hU
  refine ⟨residue 𝒪[K] r₀, ?_⟩
  rw [ValuativeExtension.residueField_algebraMap_residue]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 ?_
  exact (valuation (Completion K)).mem_maximalIdeal_iff.2 hmem

/-- The canonical ring isomorphism between the residue fields of `K` and `Completion K`. -/
noncomputable def residueFieldRingEquiv : 𝓀[K] ≃+* 𝓀[Completion K] :=
  RingEquiv.ofBijective (algebraMap 𝓀[K] 𝓀[Completion K]) (algebraMap_residueField_bijective K)

@[simp]
theorem residueFieldRingEquiv_apply (z : 𝓀[K]) :
    residueFieldRingEquiv K z = algebraMap 𝓀[K] 𝓀[Completion K] z :=
  (rfl)

theorem residueFieldRingEquiv_residue (r : 𝒪[K]) :
    residueFieldRingEquiv K (residue 𝒪[K] r) = residue 𝒪[Completion K] (algebraMap _ _ r) := by
  rw [residueFieldRingEquiv_apply, ValuativeExtension.residueField_algebraMap_residue]

section Extension

variable {K}

/-- A continuous map `g : Completion K → Completion K` satisfying `g x = 0 ↔ x = 0` that extends a
valuation-preserving map `f : K → K` preserves the canonical valuation of `Completion K`. -/
theorem valuation_eq_of_continuous {g : Completion K → Completion K} (hg : Continuous g)
    (hg0 : ∀ x, g x = 0 ↔ x = 0) {f : K → K} (hcoe : ∀ r : K, g r = (f r : Completion K))
    (hval : ∀ r : K, valuation K (f r) = valuation K r) (x : Completion K) :
    valuation (Completion K) (g x) = valuation (Completion K) x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [(hg0 0).2 rfl]
  have hgx0 : g x ≠ 0 := (hg0 x).not.2 hx0
  have hloc := (valuation K).extension_locally_const hgx0
  have hpre := hg.continuousAt.preimage_mem_nhds hloc
  obtain ⟨r, hr, hvr⟩ := (valuation K).exists_coe_mem_extension_eq hpre
  refine ((valuation (Completion K)).veq_iff_eq).1
    (((valuation K).extension).veq_iff_eq.2 ?_)
  have hr' : (valuation K).extension (g (r : Completion K)) =
      (valuation K).extension (g x) := hr
  rw [← hr', hcoe, Valuation.extension_apply_coe, hval, hvr]

/-- If a continuous map `h : 𝒪[Completion K] → Completion K` sends the image of every `y : 𝒪[K]`
into the open unit ball `{w | valuation (Completion K) w < 1}`, then it sends all of
`𝒪[Completion K]` into the open unit ball. -/
theorem valuation_lt_one_of_continuous_integer {h : 𝒪[Completion K] → Completion K}
    (hh : Continuous h)
    (hK : ∀ y : 𝒪[K], valuation (Completion K) (h (algebraMap 𝒪[K] 𝒪[Completion K] y)) < 1)
    (x : 𝒪[Completion K]) :
    valuation (Completion K) (h x) < 1 := by
  have hball : IsClosed {w : Completion K | valuation (Completion K) w < 1} := by
    simpa only [Valuation.restrict_lt_one_iff] using (valuation (Completion K)).isClosed_ball 1
  refine closure_minimal ?_ (hball.preimage hh) (denseRange_algebraMap_integer K x)
  rintro _ ⟨y, rfl⟩
  exact hK y

end Extension

end UniformSpace.Completion
