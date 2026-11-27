/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.LocalUnits

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

end IsDedekindDomain.HeightOneSpectrum
