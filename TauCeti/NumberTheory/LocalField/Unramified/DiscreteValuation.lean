/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.LocalField.Unramified.Completion
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.Topology.Algebra.ValuativeRel.Completion
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Discreteness, uniformizers, and closed embedding of `Breve E`

The maximal unramified extension `E^{ur}` and its completion `Breve E` have the same value group
as the base local field `E`. Consequently their valuations are discrete of rank one, `𝒪[E^{ur}]`
and `𝒪[Breve E]` are discrete valuation rings, `𝒪[Breve E]` is `𝓂[Breve E]`-adically complete and
Henselian, every uniformizer of `E` remains a uniformizer of `Breve E` (and in particular is not a
square in `Breve E`), and `E` embeds into `Breve E` as a closed subfield.

Every element of the maximal unramified extension lies in a finite unramified subextension, where
the normalized valuation has the same image as that of `E`. Completion adds no values, by
`UniformSpace.Completion.exists_coe_veq`.

## Main results

* `TauCeti.MaxUnramifiedCompletion.mapValueGroupWithZero_unramified_surjective`,
  `TauCeti.MaxUnramifiedCompletion.mapValueGroupWithZero_breve_surjective`: `E^{ur}` and `Breve E`
  have the same value group as `E`.
* `TauCeti.MaxUnramifiedCompletion.unramifiedIsDiscreteValuationRing`,
  `TauCeti.MaxUnramifiedCompletion.breveIsDiscreteValuationRing`,
  `TauCeti.MaxUnramifiedCompletion.breveIsAdicComplete`,
  `TauCeti.MaxUnramifiedCompletion.breveHenselianLocalRing`: `𝒪[E^{ur}]` and `𝒪[Breve E]` are
  discrete valuation rings, and `𝒪[Breve E]` is adically complete and Henselian.
* `TauCeti.MaxUnramifiedCompletion.isUniformizer_algebraMap`,
  `Irreducible.not_isSquare_algebraMap_breve`: uniformizers of `E` remain uniformizers of
  `Breve E` and are not squares in `Breve E`.
* `TauCeti.MaxUnramifiedCompletion.isClosedEmbedding_algebraMap`: `algebraMap E (Breve E)` is a
  closed embedding.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §5.
* R. E. Kottwitz, *Isocrystals with additional structure. II*, Compositio Math. 109 (1997), §1.1.
-/

public section

open ValuativeRel UniformSpace IntermediateField

namespace TauCeti.MaxUnramifiedCompletion

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The maximal unramified extension has no values beyond those of the base field. -/
theorem exists_algebraMap_veq (x : Unramified E) :
    ∃ r : E, algebraMap E (Unramified E) r =ᵥ x := by
  obtain ⟨f, _, hxf⟩ := mem_maximalUnramifiedExtension_iff.mp x.property
  let L := unramifiedExtension E (AlgebraicClosure E) f
  let := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension
  let y : L := ⟨x, hxf⟩
  obtain ⟨r, hv⟩ := exists_algebraMap_veq_of_isUnramified (K := E) y
  let j : L →ₐ[E] Unramified E :=
    inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) f)
  let := j.toAlgebra
  have := j.valuativeExtension
  -- The structure map for `j.toAlgebra` is `j` itself.
  have h : j (algebraMap E L r) =ᵥ j y :=
    (ValuativeExtension.veq_iff_veq (A := L) (B := Unramified E)).mpr hv
  have hjy : j y = x := Subtype.ext (IntermediateField.coe_inclusion _ _)
  rw [j.commutes, hjy] at h
  exact ⟨r, h⟩

/-- The map on value groups from the base field to its maximal unramified extension is onto. -/
theorem mapValueGroupWithZero_unramified_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero E (Unramified E)) :=
  ValuativeExtension.mapValueGroupWithZero_surjective_of_forall_exists_veq exists_algebraMap_veq

/-- The valuation of the maximal unramified extension is nontrivial. -/
instance unramifiedIsNontrivial : IsNontrivial (Unramified E) :=
  .of_valuativeExtension E

/-- The valuation of the maximal unramified extension is discrete. -/
instance unramifiedIsDiscrete : IsDiscrete (Unramified E) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_unramified_surjective

/-- The valuation of the maximal unramified extension has rank at most one. -/
instance unramifiedIsRankLeOne : IsRankLeOne (Unramified E) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_unramified_surjective

/-- The valuation ring `𝒪[E^{ur}]` is a discrete valuation ring. -/
instance unramifiedIsDiscreteValuationRing : IsDiscreteValuationRing 𝒪[Unramified E] :=
  ValuativeExtension.isDiscreteValuationRing_of_surjective_mapValueGroupWithZero
    mapValueGroupWithZero_unramified_surjective

/-- Completion of the maximal unramified extension still introduces no new values. -/
theorem mapValueGroupWithZero_breve_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero E (Breve E)) := by
  apply ValuativeExtension.mapValueGroupWithZero_surjective_of_forall_exists_veq
  intro x
  obtain ⟨y, hy⟩ := Completion.exists_coe_veq x
  obtain ⟨r, hr⟩ := exists_algebraMap_veq y
  refine ⟨r, ?_⟩
  rw [Completion.algebraMap_def]
  exact (Completion.coe_veq_coe_iff.mpr hr).trans hy

variable (E) in
/-- The valuation ring `𝒪[Breve E]` is a discrete valuation ring. -/
theorem breveIsDiscreteValuationRing : IsDiscreteValuationRing 𝒪[Breve E] :=
  Completion.isDiscreteValuationRing_integer (K := Unramified E)

variable (E) in
/-- The valuation ring `𝒪[Breve E]` is `𝓂[Breve E]`-adically complete. -/
theorem breveIsAdicComplete : IsAdicComplete 𝓂[Breve E] 𝒪[Breve E] :=
  Completion.isAdicComplete_maximalIdeal_integer (K := Unramified E)

variable (E) in
/-- The valuation ring `𝒪[Breve E]` is a Henselian local ring. -/
theorem breveHenselianLocalRing : HenselianLocalRing 𝒪[Breve E] :=
  inferInstance

variable (E) in
/-- The maximal ideal of `𝒪[E]` generates the maximal ideal of `𝒪[Breve E]`. -/
@[simp]
theorem map_maximalIdeal_breve :
    𝓂[E].map (algebraMap 𝒪[E] 𝒪[Breve E]) = 𝓂[Breve E] :=
  ValuativeExtension.map_maximalIdeal_eq_of_surjective_mapValueGroupWithZero
    mapValueGroupWithZero_breve_surjective

/-- An element of `𝒪[E]` is irreducible if and only if its image in `𝒪[Breve E]` is irreducible. -/
@[simp]
theorem irreducible_algebraMap_integer_breve_iff {π : 𝒪[E]} :
    Irreducible (algebraMap 𝒪[E] 𝒪[Breve E] π) ↔ Irreducible π :=
  ValuativeExtension.irreducible_algebraMap_integer_iff_of_surjective_mapValueGroupWithZero
    mapValueGroupWithZero_breve_surjective

/-- A unit `π : Eˣ` is a uniformizer of `E` if and only if its image in `Breve E` is a uniformizer
for the canonical valuation of `Breve E`. -/
theorem isUniformizer_algebraMap_iff {π : Eˣ} :
    (valuation (Breve E)).IsUniformizer (algebraMap E (Breve E) (π : E)) ↔ IsUniformizer E π := by
  refine ⟨fun hπ ↦ ?_, fun hπ ↦ ?_⟩
  · have hπ1 : valuation E (π : E) ≤ 1 :=
      (ValuativeExtension.valuation_algebraMap_le_one_iff (π : E)).1 hπ.val_lt_one.le
    let ϖ : 𝒪[E] := ⟨(π : E), hπ1⟩
    have hϖB : (valuation (Breve E)).IsUniformizer (algebraMap 𝒪[E] 𝒪[Breve E] ϖ : Breve E) := by
      rwa [Valuation.HasExtension.val_algebraMap]
    exact (isUniformizer_iff_exists_irreducible E π).2
      ⟨ϖ, irreducible_algebraMap_integer_breve_iff.1
        ((isUniformizer_valuation_coe_iff (K := Breve E)).1 hϖB), rfl⟩
  · obtain ⟨ϖ, hϖ, hϖπ⟩ := (isUniformizer_iff_exists_irreducible E π).1 hπ
    have hu := (irreducible_algebraMap_integer_breve_iff.2 hϖ).isUniformizer_valuation
      (K := Breve E)
    rwa [Valuation.HasExtension.val_algebraMap, hϖπ] at hu

/-- **Every uniformizer of `E` remains a uniformizer of `Breve E`.** -/
theorem isUniformizer_algebraMap {π : Eˣ} (hπ : IsUniformizer E π) :
    (valuation (Breve E)).IsUniformizer (algebraMap E (Breve E) (π : E)) :=
  isUniformizer_algebraMap_iff.2 hπ

variable (E) in
/-- The canonical map `E → E^{ur}` is a topological embedding. -/
theorem isEmbedding_algebraMap_unramified :
    Topology.IsEmbedding (algebraMap E (Unramified E)) :=
  isEmbedding_algebraMap_of_coinitial E (Unramified E) fun _ hy ↦
    ValuativeExtension.exists_ne_zero_vle_of_surjective_mapValueGroupWithZero
      mapValueGroupWithZero_unramified_surjective hy

variable (E) in
/-- **The base local field `E` embeds into `Breve E` as a closed subfield.** -/
theorem isClosedEmbedding_algebraMap :
    Topology.IsClosedEmbedding (algebraMap E (Breve E)) := by
  let _ := IsTopologicalAddGroup.rightUniformSpace E
  have := isUniformAddGroup_of_addCommGroup (G := E)
  exact isClosedEmbedding_algebraMap_of_coinitial E (Breve E) fun _ hy ↦
    ValuativeExtension.exists_ne_zero_vle_of_surjective_mapValueGroupWithZero
      mapValueGroupWithZero_breve_surjective hy

end TauCeti.MaxUnramifiedCompletion

open TauCeti.MaxUnramifiedCompletion

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- A uniformizer of the base field remains a uniformizer in the completed maximal
unramified extension, expressed as irreducibility in its valuation ring. -/
theorem Irreducible.algebraMap_integer_breve {π : 𝒪[E]} (hπ : Irreducible π) :
    Irreducible (algebraMap 𝒪[E] 𝒪[Breve E] π) :=
  hπ.algebraMap_integer_of_surjective_mapValueGroupWithZero mapValueGroupWithZero_breve_surjective

/-- No uniformizer `π` of `𝒪[E]` is a square in `Breve E`, since `Breve E` has ramification index
`1` over `E`. -/
theorem Irreducible.not_isSquare_algebraMap_breve {π : 𝒪[E]} (hπ : Irreducible π) :
    ¬ IsSquare (algebraMap E (Breve E) (π : E)) := by
  rintro ⟨z, hz⟩
  have hz1 : valuation (Breve E) z ≤ 1 := by
    refine (pow_le_one_iff_of_nonneg zero_le two_ne_zero).1 ?_
    rw [← map_pow, sq, ← hz, ← Valuation.HasExtension.val_algebraMap (vA := valuation (Breve E))]
    exact (algebraMap 𝒪[E] 𝒪[Breve E] π).2
  let z₀ : 𝒪[Breve E] := ⟨z, hz1⟩
  have hsq : algebraMap 𝒪[E] 𝒪[Breve E] π = z₀ * z₀ :=
    Subtype.ext (by simpa [z₀, Valuation.HasExtension.val_algebraMap] using hz)
  exact hπ.algebraMap_integer_breve.not_isSquare ⟨z₀, hsq⟩
