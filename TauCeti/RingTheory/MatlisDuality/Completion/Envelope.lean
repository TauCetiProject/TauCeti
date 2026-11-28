/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.ResidueField
public import TauCeti.RingTheory.MatlisDuality.Endomorphism
import TauCeti.RingTheory.AdicCompletion.Injective
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.AdicCompletion.Small

/-!
# The injective hull of the residue field over the completion

Let `R` be a commutative Noetherian local ring with maximal ideal `𝔪`, residue field `κ`, and
`𝔪`-adic completion `R̂`, and let `ι : κ →ₗ[R] E` be an injective envelope of `κ`. Because every
element of `E` is killed by a power of `𝔪`, `E` carries a canonical `R̂`-module structure
(`TauCeti.AdicCompletion.torsionModule`), and `ι` induces an `R̂`-linear map
`TauCeti.IsInjectiveEnvelope.adicCompletionResidueMap` from the residue field of `R̂` into `E`.

This file shows that when `[Small.{v} R]` holds (for `E : Type v`), `E`, with that `R̂`-module
structure, is an injective envelope of the residue field of `R̂`
(`TauCeti.IsInjectiveEnvelope.adicCompletion`), without needing complete Matlis biduality. Note
that `TauCeti.IsInjectiveEnvelope.adicCompletionResidueMap` does not require `[Small.{v} R]`.

## Main results

* `TauCeti.IsInjectiveEnvelope.adicCompletionResidueMap`: the induced embedding of the residue field
  of `R̂` into `E` (without `[Small.{v} R]`).
* `TauCeti.IsInjectiveEnvelope.adicCompletion`: assuming `[Small.{v} R]` for `E : Type v`, `E`
  with its canonical `R̂`-module structure is an injective envelope of the residue field of `R̂`.

## References

* The Stacks Project, Remark 47.7.9, Tag 0EGL.
-/

public section

noncomputable section

open IsLocalRing LinearMap

namespace TauCeti

universe u v

namespace IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

include hι

/-- The embedding of the residue field of `R̂` into `E`, induced by `ι : κ →ₗ[R] E` via the
`R`-algebra equivalence `ResidueField R ≃ₐ[R] ResidueField R̂`. -/
def adicCompletionResidueMap :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    ResidueField (_root_.AdicCompletion (maximalIdeal R) R) →ₗ[_root_.AdicCompletion
      (maximalIdeal R) R] E :=
  letI := AdicCompletion.torsionModule hι.mem_primaryComponent
  (AdicCompletion.restrictScalarsEquivOfPrimaryComponent
    (maximalIdeal R).fg_of_isNoetherianRing
    (AdicCompletion.mem_primaryComponent_maximalIdeal_residueField (R := R))).symm
    (ι.comp (AdicCompletion.residueFieldEquiv R).symm.toLinearMap)

/-- Restricting scalars to `R` identifies `adicCompletionResidueMap` with `ι` composed with the
inverse of `AdicCompletion.residueFieldEquiv`. -/
theorem adicCompletionResidueMap_restrictScalars :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    hι.adicCompletionResidueMap.restrictScalars R =
      ι.comp (AdicCompletion.residueFieldEquiv R).symm.toLinearMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  ext x
  simp [adicCompletionResidueMap]

@[simp]
theorem adicCompletionResidueMap_apply_map (x : ResidueField R) :
    hι.adicCompletionResidueMap
      (ResidueField.map (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) x) = ι x := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  simp [adicCompletionResidueMap, ← AdicCompletion.residueFieldEquiv_apply]

@[simp]
theorem adicCompletionResidueMap_residue_algebraMap (r : R) :
    hι.adicCompletionResidueMap
      (residue (_root_.AdicCompletion (maximalIdeal R) R)
        (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) r)) = ι (residue R r) := by
  rw [← ResidueField.map_residue (algebraMap R (_root_.AdicCompletion (maximalIdeal R) R)) r,
    hι.adicCompletionResidueMap_apply_map]

variable [Small.{v} R]

/-- **The injective hull of `κ` over `R` is also an injective hull of the residue field of `R̂`
over `R̂`** (Stacks Remark 47.7.9, Tag 0EGL), assuming `[Small.{v} R]` for `E : Type v`. -/
theorem adicCompletion :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsInjectiveEnvelope hι.adicCompletionResidueMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := hι.moduleInjective
  refine
    { moduleInjective := AdicCompletion.moduleInjective_of_primaryComponent
        (maximalIdeal R).fg_of_isNoetherianRing
        hι.mem_primaryComponent
      injective := fun x y hxy ↦ ?_
      isEssential_range := isEssential_iff.mpr fun K hK ↦ ?_ }
  · obtain ⟨x, rfl⟩ := (_root_.AdicCompletion.residueField_map_bijective R).surjective x
    obtain ⟨y, rfl⟩ := (_root_.AdicCompletion.residueField_map_bijective R).surjective y
    rw [hι.adicCompletionResidueMap_apply_map, hι.adicCompletionResidueMap_apply_map] at hxy
    rw [hι.injective hxy]
  · -- Restricting to `R`, `range ι̂` has the same elements as `range ι`, which is essential.
    have hrange : (LinearMap.range hι.adicCompletionResidueMap).restrictScalars R =
        LinearMap.range ι := by
      rw [← LinearMap.range_restrictScalars, hι.adicCompletionResidueMap_restrictScalars,
        LinearMap.range_comp_of_range_eq_top _
          (LinearMap.range_eq_top.mpr (AdicCompletion.residueFieldEquiv R).symm.surjective)]
    have hK' : LinearMap.range ι ⊓ K.restrictScalars R = ⊥ := by
      simpa [hrange, Submodule.restrictScalars_inf] using
        congrArg (Submodule.restrictScalars R) hK
    exact (Submodule.restrictScalars_eq_bot_iff R _ _).mp
      (isEssential_iff.mp hι.isEssential_range _ hK')

end IsInjectiveEnvelope

end TauCeti
