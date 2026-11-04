/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Completion
public import TauCeti.Topology.Algebra.ValuativeRel.Completion

/-!
# Discreteness of the completed maximal unramified extension

The maximal unramified extension and its completion have the same value group as the base
local field. In particular their valuations are discrete and of rank one. This supplies the
valued-field hypotheses for integral models over the completed unramified field, even though
that field is not locally compact.

Every element of the maximal unramified extension lies in a finite unramified subextension.
The normalized valuation there has the same image as that of the base. Completion adds no
values, by `UniformSpace.Completion.exists_coe_veq`.

## References

* J.-P. Serre, *Corps Locaux*, Chapter III, §5.
* R. E. Kottwitz, *Isocrystals with additional structure. II*, §1.1.
-/

public section

open ValuativeRel UniformSpace IntermediateField

namespace TauCeti.MaxUnramifiedCompletion

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- The maximal unramified extension has no values beyond those of the base field. -/
theorem exists_algebraMap_veq (x : Unramified E) :
    ∃ r : E, algebraMap E (Unramified E) r =ᵥ x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  obtain ⟨f, hf, hxf⟩ := mem_maximalUnramifiedExtension_iff.mp x.property
  let L := unramifiedExtension E (AlgebraicClosure E) f
  let := finiteIntermediateFieldValuativeRel E (AlgebraicClosure E) L
  let := finiteIntermediateFieldTopology E (AlgebraicClosure E) L
  have := finiteIntermediateField_isNonarchimedeanLocalField E (AlgebraicClosure E) L
  have := finiteIntermediateField_valuativeExtension E (AlgebraicClosure E) L
  have : IsUnramified E L := isUnramified_unramifiedExtension hf
  let y : L := ⟨x, hxf⟩
  have hy : y ≠ 0 := fun h ↦ hx (Subtype.ext <| by
    simpa [y] using congrArg (fun a : L ↦ (a : AlgebraicClosure E)) h)
  obtain ⟨r, hr⟩ :=
    (isUnramified_iff_normalizedValuation_comp_unitsMap_surjective E L).mp
      inferInstance (normalizedValuation L (Units.mk0 y hy))
  have hv : algebraMap E L (r : E) =ᵥ y := by
    apply (valuation L).veq_iff_eq.mpr
    have heq := congrArg Multiplicative.toAdd hr
    apply le_antisymm
    · exact (toAdd_normalizedValuation_le_iff_valuation_le _ _).mp heq.ge
    · exact (toAdd_normalizedValuation_le_iff_valuation_le _ _).mp heq.le
  let j : L →ₐ[E] Unramified E :=
    inclusion (unramifiedExtension_le_maximalUnramifiedExtension E (AlgebraicClosure E) f)
  let := j.toAlgebra
  have := j.valuativeExtension
  -- The structure map for `j.toAlgebra` is `j` itself.
  have h : j (algebraMap E L (r : E)) =ᵥ j y :=
    (ValuativeExtension.veq_iff_veq (A := L) (B := Unramified E)).mpr hv
  have hjy : j y = x := Subtype.ext (by rfl)
  rw [j.commutes, hjy] at h
  exact ⟨r, h⟩

/-- The map on value groups from the base field to its maximal unramified extension is onto. -/
theorem mapValueGroupWithZero_unramified_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero E (Unramified E)) := by
  intro γ
  obtain ⟨x, rfl⟩ := valuation_surjective γ
  obtain ⟨r, hr⟩ := exists_algebraMap_veq x
  exact ⟨valuation E r, by
    rw [ValuativeExtension.mapValueGroupWithZero_valuation]
    exact (valuation (Unramified E)).veq_iff_eq.mp hr⟩

/-- The valuation of the maximal unramified extension is discrete. -/
instance unramifiedIsDiscrete : IsDiscrete (Unramified E) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_unramified_surjective

/-- The valuation of the maximal unramified extension has rank at most one. -/
instance unramifiedIsRankLeOne : IsRankLeOne (Unramified E) :=
  .of_surjective_mapValueGroupWithZero mapValueGroupWithZero_unramified_surjective

/-- Completion of the maximal unramified extension still introduces no new values. -/
theorem mapValueGroupWithZero_breve_surjective :
    Function.Surjective (ValuativeExtension.mapValueGroupWithZero E (Breve E)) := by
  intro γ
  obtain ⟨x, rfl⟩ := valuation_surjective γ
  obtain ⟨y, hy⟩ := Completion.exists_coe_veq x
  obtain ⟨r, hr⟩ := exists_algebraMap_veq y
  have hv := (Completion.coe_veq_coe_iff.mpr hr).trans hy
  refine ⟨valuation E r, ?_⟩
  rw [ValuativeExtension.mapValueGroupWithZero_valuation]
  -- The completion's `E`-algebra structure is the composite through `Unramified E`.
  exact (valuation (Breve E)).veq_iff_eq.mp hv

end TauCeti.MaxUnramifiedCompletion

open TauCeti.MaxUnramifiedCompletion

variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E]

/-- A uniformizer of the base field remains a uniformizer in the completed maximal
unramified extension, expressed as irreducibility in its valuation ring. -/
theorem Irreducible.algebraMap_integer_breve {π : 𝒪[E]} (hπ : Irreducible π) :
    Irreducible (algebraMap 𝒪[E] 𝒪[Breve E] π) :=
  hπ.algebraMap_integer_of_surjective_valueGroup mapValueGroupWithZero_breve_surjective
