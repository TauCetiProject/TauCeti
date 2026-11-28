/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalUnits
import TauCeti.Topology.Algebra.ContinuousMonoidHom.Basic

/-!
# Reduction of an integral finite idele

An everywhere-integral finite idele has a unit component in each completed valuation ring.
Reducing that component gives the homomorphism through which tame local characters are read.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

open FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- Reduce the component of an everywhere-integral finite idele at `v` to a residue-field unit. -/
noncomputable def integralUnitsReduction (v : HeightOneSpectrum R) :
    integralUnits R K →* (IsLocalRing.ResidueField (v.adicCompletionIntegers K))ˣ :=
  (v.adicCompletionIntegers K).unitGroupToResidueFieldUnits.comp
    (((unitsProj K v).comp (integralUnits R K).subtype).codRestrict
      (v.adicCompletionIntegers K).unitGroup fun x ↦ by
        apply (Valuation.mem_unitGroup_iff _ Valued.v _).2
        simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_unitsProj_apply] using
          mem_integralUnits_iff.1 x.property v)

/-- Reduction of an integral finite idele is reduction of its local unit component. -/
theorem integralUnitsReduction_eq_of_unitsProj_eq (v : HeightOneSpectrum R)
    (x : integralUnits R K) (u : (v.adicCompletionIntegers K).unitGroup)
    (hu : unitsProj K v x = (u : (v.adicCompletion K)ˣ)) :
    integralUnitsReduction v x = (v.adicCompletionIntegers K).unitGroupToResidueFieldUnits u := by
  rw [integralUnitsReduction, MonoidHom.comp_apply]
  exact congrArg _ (Subtype.ext hu)

/-- Every unit in the residue field is the reduction of an integral finite idele. -/
theorem integralUnitsReduction_surjective (v : HeightOneSpectrum R) :
    Function.Surjective (integralUnitsReduction (K := K) v) := by
  intro a
  obtain ⟨u, rfl⟩ := (v.adicCompletionIntegers K).surjective_unitGroupToResidueFieldUnits a
  have hu : Valued.v ((u : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 :=
    (Valuation.mem_unitGroup_iff _ Valued.v _).1 u.property
  obtain ⟨x, hx, hxu⟩ := (image_unitsProj_integralUnits (K := K) v).ge hu
  exact ⟨⟨x, hx⟩, integralUnitsReduction_eq_of_unitsProj_eq v ⟨x, hx⟩ u hxu⟩

/-- A finite idele reduces to `1` at `v` exactly when its `v`-component differs from `1`
by an element of the maximal ideal of the completed valuation ring. -/
theorem integralUnitsReduction_eq_one_iff (v : HeightOneSpectrum R) (x : integralUnits R K) :
    v.integralUnitsReduction x = 1 ↔ Valued.v ((unitsProj K v x : v.adicCompletion K) - 1) < 1 := by
  let u : (v.adicCompletionIntegers K).unitGroup := ⟨unitsProj K v x, by
    apply (Valuation.mem_unitGroup_iff _ Valued.v _).2
    simpa only [coe_unitsProj_apply] using mem_integralUnits_iff.1 x.property v⟩
  rw [integralUnitsReduction_eq_of_unitsProj_eq v x u rfl, ← MonoidHom.mem_ker,
    ValuationSubring.ker_unitGroupToResidueFieldUnits, Subgroup.mem_comap,
    Subgroup.coe_subtype, ValuationSubring.mem_principalUnitGroup_iff]
  exact (Valuation.isEquiv_valuation_valuationSubring Valued.v).symm.lt_one_iff_lt_one

/-- The kernel of reduction at `v` is open in the integral finite ideles. -/
theorem isOpen_ker_integralUnitsReduction (v : HeightOneSpectrum R) :
    IsOpen ((v.integralUnitsReduction (K := K)).ker : Set (integralUnits R K)) := by
  have hball : IsOpen {y : v.adicCompletion K | Valued.v y < 1} := by
    simpa only [Valuation.restrict_lt_iff_lt_embedding, map_one] using
      (Valued.isOpen_ball (v.adicCompletion K) 1)
  have hker : ((v.integralUnitsReduction (K := K)).ker : Set (integralUnits R K)) =
      (fun x : integralUnits R K ↦ (unitsProj K v x : v.adicCompletion K) - 1) ⁻¹'
        {y | Valued.v y < 1} := Set.ext v.integralUnitsReduction_eq_one_iff
  rw [hker]
  exact hball.preimage (((Units.continuous_val.comp (continuous_unitsProj v)).comp
    continuous_subtypeVal).sub continuous_const)

/-- Any character of the residue-field units pulls back to a continuous homomorphism on
integral finite ideles. Continuity does not require putting a topology on the residue field. -/
theorem continuous_comp_integralUnitsReduction (v : HeightOneSpectrum R) {A : Type*}
    [MulOneClass A] [TopologicalSpace A]
    (χ : (IsLocalRing.ResidueField (v.adicCompletionIntegers K))ˣ →* A) :
    Continuous (χ.comp v.integralUnitsReduction) :=
  (χ.comp v.integralUnitsReduction).continuous_of_isOpen_ker <|
    Subgroup.isOpen_mono (fun _ hx ↦ by simp [MonoidHom.mem_ker.mp hx])
      v.isOpen_ker_integralUnitsReduction

end IsDedekindDomain.HeightOneSpectrum
