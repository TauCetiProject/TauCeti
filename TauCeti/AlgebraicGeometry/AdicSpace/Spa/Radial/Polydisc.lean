/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Radial.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.PuncturedDisc
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# Radial regions in the closed polydisc

This file specializes the radial regions of `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Radial.Basic`
to the closed polydisc `Spa (A⟨T₁, …, Tₖ⟩, A⟨T₁, …, Tₖ⟩°)`, with a coordinate `Tᵢ` and constant
radii.

* `TauCeti.ValuationSpectrum.classicalPoint_mem_closedDisc_iff`: the classical point at a
  power-bounded tuple `c` over a base point `x` lies in the closed disc `|Tᵢ| ≤ |b|` exactly when
  `x` compares `cᵢ` with `b` in the same way. The radius `b` is an arbitrary constant; for
  `b = 1` both sides always hold.
* `TauCeti.ValuationSpectrum.puncturedDisc_eq_val_preimage_puncturedClosedDisc` and
  `TauCeti.ValuationSpectrum.puncturedDiscAnnulus_eq_val_preimage_closedAnnulus`: the punctured
  closed unit disc `TauCeti.ValuationSpectrum.puncturedDisc` and its exhaustion annuli
  `|c|^(n+1) ≤ |T|` are the punctured closed disc `𝔻^×(A⟨T⟩°, T, 1)` and the closed annuli
  `𝔸(A⟨T⟩°, T, c^(n+1), 1)` of the general construction.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section ClassicalPoint

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T3Space A]

/-- **Classical points of a closed disc.** The classical point at a power-bounded tuple `c` over
`x ∈ Spa (A, A°)` lies in the closed disc `𝔻(A⟨T⟩°, Tᵢ, b)` with constant radius `b` exactly when
`x(cᵢ) ≤ x(b)`. -/
theorem classicalPoint_mem_closedDisc_iff (x : spa (powerBoundedSubring A)) (c : Fin k → A)
    (hc : ∀ i, IsPowerBounded (c i)) (i : Fin k) (b : A) :
    (classicalPoint x c hc).1 ∈ closedDisc
        (powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
          isWeightFamily_one_weight))
        (weightedX _ isWeightFamily_one_weight i) (weightedC _ isWeightFamily_one_weight b) ↔
      x.1.toValuativeRel.vle (c i) b := by
  rw [mem_closedDisc_iff, classicalPoint_vle, evalAtHom_weightedX, evalAtHom_weightedC,
    ← closedPolydisc_def]
  exact and_iff_right (classicalPoint x c hc).2

end ClassicalPoint

section UnitDisc

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

local notation "𝒯" => weightedRestrictedSubring (fun _ : Fin 1 ↦ ({1} : Set A))
  isWeightFamily_one_weight
local notation "T" => weightedX (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight 0
local notation "C" => weightedC (fun _ : Fin 1 ↦ ({1} : Set A)) isWeightFamily_one_weight

/-- **The punctured closed unit disc is a punctured closed disc**: `puncturedDisc A` is the
trace on the closed unit disc of `𝔻^×(A⟨T⟩°, T, 1)`. -/
theorem puncturedDisc_eq_val_preimage_puncturedClosedDisc :
    puncturedDisc A = Subtype.val ⁻¹' puncturedClosedDisc (powerBoundedSubring 𝒯) T 1 := by
  ext v
  have hv : v.1 ∈ spa (powerBoundedSubring 𝒯) := closedPolydisc_def 1 A ▸ v.2
  -- the coordinate is power-bounded, so it has valuation at most `1` on the closed unit disc
  have hT : v.1.toValuativeRel.vle T 1 := ((mem_closedPolydisc_iff 1 A v.1).mp v.2).2 T
    (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight 0))
  simp [hv, hT]

/-- **The exhaustion annuli of the punctured unit disc are closed annuli**: the annulus
`|c|^(n+1) ≤ |T|` of `puncturedDiscAnnulus` is the trace on the closed unit disc of
`𝔸(A⟨T⟩°, T, c^(n+1), 1)`. -/
theorem puncturedDiscAnnulus_eq_val_preimage_closedAnnulus (c : A) (n : ℕ) :
    puncturedDiscAnnulus c n =
      Subtype.val ⁻¹' closedAnnulus (powerBoundedSubring 𝒯) T (C (c ^ (n + 1))) 1 := by
  ext v
  have hv : v.1 ∈ spa (powerBoundedSubring 𝒯) := closedPolydisc_def 1 A ▸ v.2
  -- the coordinate is power-bounded, so it has valuation at most `1` on the closed unit disc
  have hT : v.1.toValuativeRel.vle T 1 := ((mem_closedPolydisc_iff 1 A v.1).mp v.2).2 T
    (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight 0))
  simp [hv, hT]

end UnitDisc

end TauCeti.ValuationSpectrum
