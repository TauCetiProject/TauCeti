/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.Envelope.ResidueField
public import TauCeti.RingTheory.AdicCompletion.Injective
public import TauCeti.RingTheory.AdicCompletion.ResidueField

/-!
# Injective envelopes of the residue field over the adic completion

Let `R` be a Noetherian local ring with maximal ideal `𝔪`, residue field `κ`, and `𝔪`-adic
completion `R̂ = AdicCompletion 𝔪 R`, and let `ι : κ →ₗ[R] E` be an injective envelope of `κ` over
`R`. Because every element of `E` is annihilated by a power of `𝔪`
(`TauCeti.IsInjectiveEnvelope.mem_primaryComponent`), `E` carries the canonical `R̂`-module
structure `TauCeti.AdicCompletion.torsionModule`.

By `TauCeti.AdicCompletion.torsionModule_injective`, `E` is injective over `R̂`. Composing `ι` with
the canonical identification `ResidueField R̂ ≃ₐ[R] κ`
(`TauCeti.AdicCompletion.residueFieldAlgEquiv`) exhibits `E` as an injective envelope of the
residue field of the complete Noetherian local ring `R̂`
(`TauCeti.IsInjectiveEnvelope.adicCompletion`).

## Main declarations

* `TauCeti.IsInjectiveEnvelope.adicCompletionResidueMap`: `ι` lifted across
  `ResidueField R̂ ≃ₐ[R] κ` to an `R̂`-linear map `ResidueField R̂ →ₗ[R̂] E`.
* `TauCeti.IsInjectiveEnvelope.adicCompletion`: `E` is an injective envelope of
  `ResidueField R̂` over `R̂`.

## References

* [Stacks Project, Lemma 47.7.7](https://stacks.math.columbia.edu/tag/08Z8)
* W. Bruns, J. Herzog, *Cohen–Macaulay rings*, Section 3.2.
-/

public section

noncomputable section

universe u v

open IsLocalRing LinearMap

namespace TauCeti.IsInjectiveEnvelope

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {E : Type v} [AddCommGroup E] [Module R E]
  {ι : ResidueField R →ₗ[R] E} (hι : IsInjectiveEnvelope ι)

/-- An injective envelope `ι : ResidueField R →ₗ[R] E` lifted across
`ResidueField R̂ ≃ₐ[R] ResidueField R` to an `R̂`-linear embedding of `ResidueField R̂` into `E`. -/
def adicCompletionResidueMap :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    ResidueField (_root_.AdicCompletion (maximalIdeal R) R)
      →ₗ[_root_.AdicCompletion (maximalIdeal R) R] E := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have hres : ∀ y : ResidueField (_root_.AdicCompletion (maximalIdeal R) R),
      y ∈ (maximalIdeal R).primaryComponent _ := fun y ↦ by
    refine ((maximalIdeal R).primaryComponent_mem _ y).mpr ⟨1, ?_⟩
    rw [pow_one, Submodule.mem_torsionBySet_iff]
    rintro ⟨m, hm⟩
    have hm' : algebraMap R (_root_.AdicCompletion (maximalIdeal R) R) m ∈
        maximalIdeal (_root_.AdicCompletion (maximalIdeal R) R) := by
      rw [_root_.AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ hm
    rw [← algebraMap_smul (_root_.AdicCompletion (maximalIdeal R) R), Algebra.smul_def,
      ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr hm', zero_mul]
  exact (AdicCompletion.restrictScalarsEquivOfMemPrimaryComponent
    (maximalIdeal R).fg_of_isNoetherianRing hres).symm
      (ι ∘ₗ (AdicCompletion.residueFieldAlgEquiv R).symm.toLinearMap)

@[simp]
theorem adicCompletionResidueMap_apply
    (y : ResidueField (_root_.AdicCompletion (maximalIdeal R) R)) :
    hι.adicCompletionResidueMap y = ι ((AdicCompletion.residueFieldAlgEquiv R).symm y) := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  simp [adicCompletionResidueMap]

variable [Small.{v} R]

include hι

/-- Over a Noetherian local ring `R`, an injective envelope `E` of `ResidueField R` is also an
injective envelope of `ResidueField R̂` over `R̂ = AdicCompletion (maximalIdeal R) R`. -/
@[stacks 08Z8]
theorem adicCompletion :
    letI := AdicCompletion.torsionModule hι.mem_primaryComponent
    IsInjectiveEnvelope hι.adicCompletionResidueMap := by
  let := AdicCompletion.torsionModule hι.mem_primaryComponent
  have := AdicCompletion.torsionModule_isScalarTower hι.mem_primaryComponent
  have := hι.moduleInjective
  refine ⟨AdicCompletion.torsionModule_injective hι.mem_primaryComponent, ?_, ?_⟩
  · intro y₁ y₂ hy
    rw [adicCompletionResidueMap_apply, adicCompletionResidueMap_apply] at hy
    exact (AdicCompletion.residueFieldAlgEquiv R).symm.injective (hι.injective hy)
  · rw [← AdicCompletion.isEssential_restrictScalars_torsionModule_iff hι.mem_primaryComponent]
    have hrange : (range hι.adicCompletionResidueMap).restrictScalars R = range ι := by
      ext x
      simp only [Submodule.restrictScalars_mem, mem_range, adicCompletionResidueMap_apply]
      exact ⟨fun ⟨y, hy⟩ ↦ ⟨(AdicCompletion.residueFieldAlgEquiv R).symm y, hy⟩,
        fun ⟨z, hz⟩ ↦ ⟨AdicCompletion.residueFieldAlgEquiv R z, by simpa using hz⟩⟩
    rw [hrange]
    exact hι.isEssential_range

end TauCeti.IsInjectiveEnvelope
