/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Completion
import Mathlib.RingTheory.MvPowerSeries.Ideal
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Kernels of coefficientwise maps of weighted restricted series

The ring homomorphism `TauCeti.Huber.weightedMap` induced by a continuous ring homomorphism
`φ : A → B` acts on coefficients, so its kernel is coefficientwise: a series is killed exactly
when every coefficient lies in the kernel of `φ`. Likewise every series in the extension
`J · A⟨X⟩_T` of an ideal `J` of `A` has all of its coefficients in `J`. Both statements hold for
arbitrary weight families and need no completeness, surjectivity or open-mapping hypotheses.
Continuity of `weightedMap` and `weightedMapCompletion` also makes their kernels closed whenever
the target is `T₁` (automatic for the separated completion `weightedMapCompletion`).

## Main results

* `TauCeti.Huber.mem_ker_weightedMap_iff` and `TauCeti.Huber.mem_ker_weightedMapCompletion_iff`:
  the kernels of `weightedMap` and (when the source weighted restricted-series ring is complete and
  `T₀` and the target is `T₀`) `weightedMapCompletion` are coefficientwise.
* `TauCeti.Huber.weightedMap_injective` and `TauCeti.Huber.weightedMapCompletion_injective`: an
  injective coefficient map induces an injective map on weighted restricted series, and on their
  completions when the source weighted restricted-series ring is complete and `T₀` and the target
  is `T₀`.
* `TauCeti.Huber.isClosed_ker_weightedMap` and `TauCeti.Huber.isClosed_ker_weightedMapCompletion`:
  closedness of the kernels of `weightedMap` (for a `T₁` target) and `weightedMapCompletion` for
  arbitrary compatible weight families.
* `Ideal.coeff_mem_of_mem_map_weightedC`: series in `J · A⟨X⟩_T` have coefficients in `J`.
-/

public section

namespace TauCeti.Huber

variable {k : ℕ} {A B : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]
  [CommRing B] [TopologicalSpace B] [NonarchimedeanRing B]

/-- **The kernel of `weightedMap` is coefficientwise**: a series is killed by the map induced by
`φ` exactly when each of its coefficients is killed by `φ`. -/
theorem mem_ker_weightedMap_iff {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} {hT : IsWeightFamily T} {hS : IsWeightFamily S}
    {hTS : ∀ i, φ '' T i ⊆ S i} {f : weightedRestrictedSubring T hT} :
    f ∈ RingHom.ker (weightedMap hφ hT hS hTS) ↔
      ∀ ν, MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ RingHom.ker φ := by
  simp only [RingHom.mem_ker]
  refine ⟨fun h ν ↦ ?_, fun h ↦ Subtype.ext <| MvPowerSeries.ext fun ν ↦ ?_⟩
  · simpa using congrArg (fun g : weightedRestrictedSubring S hS ↦
      MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B)) h
  · simpa using h ν

/-- An injective continuous ring homomorphism induces an injective homomorphism on weighted
restricted series for any compatible weight families. -/
theorem weightedMap_injective {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} {hT : IsWeightFamily T} {hS : IsWeightFamily S}
    {hTS : ∀ i, φ '' T i ⊆ S i} (hφinj : Function.Injective φ) :
    Function.Injective (weightedMap hφ hT hS hTS) := fun _ _ h ↦
  Subtype.ext <| MvPowerSeries.ext fun ν ↦ hφinj <| by
    simpa only [coe_weightedMap, MvPowerSeries.coeff_map] using
      congrArg (fun g : weightedRestrictedSubring S hS ↦
        MvPowerSeries.coeff ν (g : MvPowerSeries (Fin k) B)) h

/-- **The kernel of `weightedMapCompletion` is coefficientwise** whenever the source weighted
restricted-series ring is complete and `T₀` and the target is `T₀`: an element of the completion
lies in the kernel exactly when every coefficient of its identified uncompleted series lies in
`RingHom.ker φ`. -/
theorem mem_ker_weightedMapCompletion_iff {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} {hT : IsWeightFamily T} {hS : IsWeightFamily S}
    {hTS : ∀ i, φ '' T i ⊆ S i}
    [CompleteSpace (weightedRestrictedSubring T hT)]
    [T0Space (weightedRestrictedSubring T hT)]
    [T0Space (weightedRestrictedSubring S hS)]
    (f : UniformSpace.Completion (weightedRestrictedSubring T hT)) :
    f ∈ RingHom.ker (weightedMapCompletion hφ hT hS hTS) ↔
      ∀ ν, MvPowerSeries.coeff ν
        ((UniformSpace.Completion.completeRingEquivSelf (weightedRestrictedSubring T hT) f :
          weightedRestrictedSubring T hT) : MvPowerSeries (Fin k) A) ∈ RingHom.ker φ := by
  have hf : f = ((UniformSpace.Completion.completeRingEquivSelf (weightedRestrictedSubring T hT) f :
      weightedRestrictedSubring T hT) :
      UniformSpace.Completion (weightedRestrictedSubring T hT)) := by
    rw [← UniformSpace.Completion.completeRingEquivSelf_symm_apply, RingEquiv.symm_apply_apply]
  conv_lhs => rw [hf]
  rw [RingHom.mem_ker, weightedMapCompletion_coe, ← UniformSpace.Completion.coe_zero,
    UniformSpace.Completion.coe_inj, ← RingHom.mem_ker, mem_ker_weightedMap_iff]

/-- An injective continuous ring homomorphism induces an injective homomorphism on completed
weighted restricted series for arbitrary compatible weight families whenever the source weighted
restricted-series ring is complete and `T₀` and the target is `T₀`. -/
theorem weightedMapCompletion_injective {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} {hT : IsWeightFamily T} {hS : IsWeightFamily S}
    {hTS : ∀ i, φ '' T i ⊆ S i}
    [CompleteSpace (weightedRestrictedSubring T hT)]
    [T0Space (weightedRestrictedSubring T hT)]
    [T0Space (weightedRestrictedSubring S hS)]
    (hφinj : Function.Injective φ) :
    Function.Injective (weightedMapCompletion hφ hT hS hTS) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h0 := (mem_ker_weightedMapCompletion_iff hφ f).mp hf
  have he0 : UniformSpace.Completion.completeRingEquivSelf (weightedRestrictedSubring T hT) f = 0 :=
    Subtype.ext <| MvPowerSeries.ext fun ν ↦ hφinj (by simpa using h0 ν)
  exact (UniformSpace.Completion.completeRingEquivSelf _).map_eq_zero_iff.mp he0

/-- The kernel of `weightedMap` is closed whenever the target weighted restricted-series ring is
`T₁` (in particular, at trivial weights over any `T₀` nonarchimedean ring). -/
instance isClosed_ker_weightedMap {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} {hT : IsWeightFamily T} {hS : IsWeightFamily S}
    {hTS : ∀ i, φ '' T i ⊆ S i} [T1Space (weightedRestrictedSubring S hS)] :
    IsClosed (RingHom.ker (weightedMap hφ hT hS hTS) : Set (weightedRestrictedSubring T hT)) :=
  RingHom.isClosed_ker (continuous_weightedMap hφ hT hS hTS)

/-- The kernel of `weightedMapCompletion` is closed for any compatible weight families, without
completeness or separation assumptions on the coefficient rings. -/
instance isClosed_ker_weightedMapCompletion {φ : A →+* B} (hφ : Continuous φ) {T : Fin k → Set A}
    {S : Fin k → Set B} {hT : IsWeightFamily T} {hS : IsWeightFamily S}
    {hTS : ∀ i, φ '' T i ⊆ S i} :
    IsClosed (RingHom.ker (weightedMapCompletion hφ hT hS hTS) :
      Set (UniformSpace.Completion (weightedRestrictedSubring T hT))) :=
  RingHom.isClosed_ker (continuous_weightedMapCompletion hφ hT hS hTS)

end TauCeti.Huber

namespace Ideal

open TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **Series in `J · A⟨X⟩_T` have coefficients in `J`**, for any ideal `J` and any weights. -/
theorem coeff_mem_of_mem_map_weightedC {T : Fin k → Set A} {hT : IsWeightFamily T}
    {J : Ideal A} {f : weightedRestrictedSubring T hT} (hf : f ∈ J.map (weightedC T hT))
    (ν : Fin k →₀ ℕ) : MvPowerSeries.coeff ν (f : MvPowerSeries (Fin k) A) ∈ J := by
  have hC : (weightedRestrictedSubring T hT).subtype.comp (weightedC T hT) = MvPowerSeries.C :=
    RingHom.ext coe_weightedC
  have hf' := mem_map_of_mem (weightedRestrictedSubring T hT).subtype hf
  rw [map_map, hC] at hf'
  exact MvPowerSeries.coeff_mem_of_mem_map_C hf' ν

end Ideal

end
