/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.ValuativeRel.Completion
public import TauCeti.RingTheory.Valuation.ValuativeRel.ValueGroup
public import TauCeti.Topology.Algebra.ValuativeRel.AdicTopology

/-!
# Arithmetic invariants of the completion of a valued field

Let `K` be a field carrying a valuative relation whose valuation topology comes from a uniform
additive group structure (`[UniformSpace K] [IsUniformAddGroup K] [IsValuativeTopology K]`).
Mathlib constructs the extended valuative relation and valuative topology on `Completion K` and
proves (`Valuation.exists_extension_eq_map`) that every valuation value of `Completion K` is
already attained on `K`.

This file packages the resulting algebraic consequences for the value group, valuation ring `𝒪[·]`,
maximal ideal `𝓂[·]`, and residue field `𝓀[·]` of `Completion K`:

* `ValuativeExtension.mapValueGroupWithZero K (Completion K)` is surjective, transferring
  `IsNontrivial`, `IsDiscrete`, `IsRankLeOne`, `IsDiscreteValuationRing`, `IsAdicComplete`, and
  irreducible uniformizers from `K` to `Completion K`.
* `algebraMap 𝒪[K] 𝒪[Completion K]` has dense range, and `algebraMap 𝓀[K] 𝓀[Completion K]` is
  bijective (`UniformSpace.Completion.residueFieldRingEquiv`).
* Continuous maps on `Completion K` and `𝒪[Completion K]` inherit valuation invariance and
  open-unit-ball bounds from `K` and `𝒪[K]`.

## Main definitions

* `UniformSpace.Completion.residueFieldRingEquiv`: the canonical ring isomorphism
  `𝓀[K] ≃+* 𝓀[Completion K]`.

## Main results

* `UniformSpace.Completion.exists_coe_veq` and
  `UniformSpace.Completion.mapValueGroupWithZero_surjective`: completion introduces no new
  valuation values.
* `UniformSpace.Completion.isNontrivial`, `UniformSpace.Completion.isDiscrete`,
  `UniformSpace.Completion.isRankLeOne`, `UniformSpace.Completion.isDiscreteValuationRing_integer`,
  and `UniformSpace.Completion.isAdicComplete_maximalIdeal_integer`: valuation invariants and adic
  completeness pass to `Completion K`.
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

namespace UniformSpace.Completion

variable {K : Type*} [Field K] [ValuativeRel K] [UniformSpace K]
  [IsValuativeTopology K] [IsUniformAddGroup K]

/-- Every value in the completion is attained on the original field. -/
theorem exists_coe_veq (x : Completion K) : ∃ r : K, (r : Completion K) =ᵥ x := by
  obtain ⟨r, hr⟩ := (valuation K).exists_extension_eq_map x
  refine ⟨r, ((valuation K).extension.veq_iff_eq).2 ?_⟩
  simpa using hr.symm

/-- The canonical map on value groups from a valued field to its completion is surjective. -/
theorem mapValueGroupWithZero_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero K (Completion K)) := by
  apply ValuativeExtension.mapValueGroupWithZero_surjective_of_forall_exists_veq
  simpa only [Completion.algebraMap_def, Algebra.algebraMap_self_apply] using
    exists_coe_veq (K := K)

/-- Completion preserves nontriviality of a valued field. -/
instance isNontrivial [IsNontrivial K] : IsNontrivial (Completion K) :=
  .of_valuativeExtension K

/-- Completion preserves discreteness of a valued field, with no rank hypothesis. -/
instance isDiscrete [IsDiscrete K] : IsDiscrete (Completion K) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_surjective

/-- Completion preserves rank at most one. -/
instance isRankLeOne [IsRankLeOne K] : IsRankLeOne (Completion K) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_surjective

/-- The maximal ideal of `𝒪[K]` generates the maximal ideal of `𝒪[Completion K]`. -/
@[simp]
theorem map_maximalIdeal_integer :
    𝓂[K].map (algebraMap 𝒪[K] 𝒪[Completion K]) = 𝓂[Completion K] :=
  ValuativeExtension.map_maximalIdeal_eq_of_surjective_mapValueGroupWithZero
    mapValueGroupWithZero_surjective

/-- Completion preserves discrete valuation rings. -/
instance isDiscreteValuationRing_integer [IsDiscreteValuationRing 𝒪[K]] :
    IsDiscreteValuationRing 𝒪[Completion K] :=
  ValuativeExtension.isDiscreteValuationRing_of_surjective_mapValueGroupWithZero
    mapValueGroupWithZero_surjective

/-- When `𝒪[K]` is a discrete valuation ring, `𝒪[Completion K]` is `𝓂[Completion K]`-adically
complete. -/
instance isAdicComplete_maximalIdeal_integer [IsDiscreteValuationRing 𝒪[K]] :
    IsAdicComplete 𝓂[Completion K] 𝒪[Completion K] :=
  TauCeti.isAdicComplete_maximalIdeal (Completion K)

/-- An integer of `K` is irreducible if and only if its image in `𝒪[Completion K]` is
irreducible. -/
@[simp]
theorem irreducible_algebraMap_integer_iff {ϖ : 𝒪[K]} :
    Irreducible (algebraMap 𝒪[K] 𝒪[Completion K] ϖ) ↔ Irreducible ϖ :=
  ValuativeExtension.irreducible_algebraMap_integer_iff_of_surjective_mapValueGroupWithZero
    mapValueGroupWithZero_surjective

/-- The valuation ring `𝒪[K]` has dense image inside the valuation ring `𝒪[Completion K]`. -/
theorem denseRange_algebraMap_integer :
    DenseRange (algebraMap 𝒪[K] 𝒪[Completion K]) := by
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [nhds_induced] at hU
  obtain ⟨V, hV, hVU⟩ := mem_comap.1 hU
  obtain ⟨r, hrV, hrv⟩ := (valuation K).exists_coe_mem_extension_eq hV
  have hx1 : (x : Completion K) ≤ᵥ 1 := by
    simpa using (valuation (Completion K)).vle_iff_le.2 x.2
  have hr1 : valuation K r ≤ 1 := by
    rw [← hrv]
    simpa using ((valuation K).extension).vle_iff_le.1 hx1
  refine ⟨algebraMap 𝒪[K] 𝒪[Completion K] ⟨r, hr1⟩, hVU ?_, ⟨r, hr1⟩, rfl⟩
  simpa [Valuation.HasExtension.val_algebraMap, Completion.algebraMap_def] using hrV

/-- The canonical algebra map from the residue field of `K` to the residue field of `Completion K`
is bijective. -/
theorem algebraMap_residueField_bijective :
    Function.Bijective (algebraMap 𝓀[K] 𝓀[Completion K]) := by
  refine ⟨(algebraMap 𝓀[K] 𝓀[Completion K]).injective, fun z ↦ ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective z
  have hball : {u : Completion K | valuation (Completion K) u < 1} ∈ 𝓝 (0 : Completion K) := by
    simpa using (IsValuativeTopology.hasBasis_nhds_zero (Completion K)).mem_of_mem (i := 1) trivial
  have hU : {y : 𝒪[Completion K] | valuation (Completion K) ((y : Completion K) - x) < 1} ∈ 𝓝 x :=
    (continuous_subtype_val.sub continuous_const).continuousAt.preimage_mem_nhds
      ((sub_self (x : Completion K)).symm ▸ hball)
  obtain ⟨_, hmem, r₀, rfl⟩ := mem_closure_iff_nhds.1 (denseRange_algebraMap_integer x) _ hU
  refine ⟨residue 𝒪[K] r₀, ?_⟩
  rw [ValuativeExtension.residueField_algebraMap_residue, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff]
  exact (valuation (Completion K)).mem_maximalIdeal_iff.2 hmem

variable (K) in
/-- The canonical ring isomorphism between the residue fields of `K` and `Completion K`. -/
noncomputable def residueFieldRingEquiv : 𝓀[K] ≃+* 𝓀[Completion K] :=
  RingEquiv.ofBijective (algebraMap 𝓀[K] 𝓀[Completion K]) algebraMap_residueField_bijective

variable (K) in
@[simp]
theorem residueFieldRingEquiv_apply (z : 𝓀[K]) :
    residueFieldRingEquiv K z = algebraMap 𝓀[K] 𝓀[Completion K] z :=
  (rfl)

variable (K) in
theorem residueFieldRingEquiv_residue (r : 𝒪[K]) :
    residueFieldRingEquiv K (residue 𝒪[K] r) = residue 𝒪[Completion K] (algebraMap _ _ r) := by
  rw [residueFieldRingEquiv_apply, ValuativeExtension.residueField_algebraMap_residue]

/-- A continuous map `g : Completion K → Completion K` satisfying `g x = 0 ↔ x = 0` that extends a
valuation-preserving map `f : K → K` preserves the canonical valuation of `Completion K`. -/
theorem valuation_eq_of_continuous {g : Completion K → Completion K} (hg : Continuous g)
    (hg0 : ∀ x, g x = 0 ↔ x = 0) {f : K → K} (hcoe : ∀ r : K, g r = (f r : Completion K))
    (hval : ∀ r : K, valuation K (f r) = valuation K r) (x : Completion K) :
    valuation (Completion K) (g x) = valuation (Completion K) x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [(hg0 0).2 rfl]
  obtain ⟨r, hr, hvr⟩ := (valuation K).exists_coe_mem_extension_eq
    (hg.continuousAt.preimage_mem_nhds ((valuation K).extension_locally_const ((hg0 x).not.2 hx0)))
  refine ((valuation (Completion K)).veq_iff_eq).1 (((valuation K).extension).veq_iff_eq.2 ?_)
  have hr' : (valuation K).extension (g (r : Completion K)) = (valuation K).extension (g x) := hr
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
  refine closure_minimal ?_ (hball.preimage hh) (denseRange_algebraMap_integer x)
  rintro _ ⟨y, rfl⟩
  exact hK y

end UniformSpace.Completion
