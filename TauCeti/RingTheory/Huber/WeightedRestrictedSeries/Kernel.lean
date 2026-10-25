/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Ideal

/-!
# Kernels of coefficientwise maps of weighted restricted series

The ring homomorphism `TauCeti.Huber.weightedMap` induced by a continuous ring homomorphism
`φ : A → B` acts on coefficients, so its kernel is coefficientwise: a series is killed exactly
when every coefficient lies in the kernel of `φ`. Likewise every series in the extension
`J · A⟨X⟩_T` of an ideal `J` of `A` has all of its coefficients in `J`. Both statements hold for
arbitrary weight families and need no completeness, surjectivity or open-mapping hypotheses.

## Main results

* `TauCeti.Huber.mem_ker_weightedMap_iff`: the kernel of `weightedMap` is coefficientwise.
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
