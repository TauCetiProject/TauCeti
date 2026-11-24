/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Radial.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.Basic
import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.PowerBounded

/-!
# Radial regions in the closed polydisc

This file specializes the radial regions of `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Radial.Basic`
to the closed polydisc `Spa (A⟨T₁, …, Tₖ⟩, A⟨T₁, …, Tₖ⟩°)`, with a coordinate `Tᵢ` and constant
radii.

* `TauCeti.ValuationSpectrum.val_mem_closedDisc_one`: every point of the closed polydisc lies in
  the closed disc `|Tᵢ| ≤ 1` of each coordinate, since the coordinate is power-bounded.
* `TauCeti.ValuationSpectrum.classicalPoint_mem_closedDisc_iff`: the classical point at a
  power-bounded tuple `c` over a base point `x` lies in the closed disc `|Tᵢ| ≤ |b|` exactly when
  `x` compares `cᵢ` with `b` in the same way. The radius `b` is an arbitrary constant; for
  `b = 1` both sides always hold.

The punctured closed unit disc `TauCeti.ValuationSpectrum.puncturedDisc` and its exhaustion
annuli are defined in `TauCeti.AlgebraicGeometry.AdicSpace.Spa.Polydisc.PuncturedDisc` as traces
of `puncturedClosedDisc` and `closedAnnulus`.
-/

public section

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

section TopologicalRing

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- Every point of the closed polydisc lies in the closed disc `|Tᵢ| ≤ 1` of each coordinate:
the coordinate is power-bounded. -/
theorem val_mem_closedDisc_one {k : ℕ} (v : closedPolydisc k A) (i : Fin k) :
    v.val ∈ closedDisc
      (powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
        isWeightFamily_one_weight))
      (weightedX (fun _ : Fin k ↦ ({1} : Set A)) isWeightFamily_one_weight i) 1 :=
  (mem_closedDisc_iff _ _ _ _).mpr ⟨closedPolydisc_def k A ▸ v.property,
    ((mem_closedPolydisc_iff k A v.val).mp v.property).2 _
      (mem_powerBoundedSubring.mpr (isPowerBounded_weightedX_one_weight i))⟩

end TopologicalRing

section ClassicalPoint

variable {k : ℕ} {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
  [NonarchimedeanRing A] [CompleteSpace A] [T3Space A]

/-- **Classical points of a closed disc.** The classical point at a power-bounded tuple `c` over
`x ∈ Spa (A, A°)` lies in the closed disc `𝔻(A⟨T⟩°, Tᵢ, b)` with constant radius `b` exactly when
`x(cᵢ) ≤ x(b)`. -/
theorem classicalPoint_mem_closedDisc_iff (x : spa (powerBoundedSubring A)) (c : Fin k → A)
    (hc : ∀ i, IsPowerBounded (c i)) (i : Fin k) (b : A) :
    (classicalPoint x c hc).val ∈ closedDisc
        (powerBoundedSubring (weightedRestrictedSubring (fun _ : Fin k ↦ ({1} : Set A))
          isWeightFamily_one_weight))
        (weightedX _ isWeightFamily_one_weight i) (weightedC _ isWeightFamily_one_weight b) ↔
      x.val.toValuativeRel.vle (c i) b := by
  rw [mem_closedDisc_iff, classicalPoint_vle, evalAtHom_weightedX, evalAtHom_weightedC,
    ← closedPolydisc_def]
  exact and_iff_right (classicalPoint x c hc).property

end ClassicalPoint

end TauCeti.ValuationSpectrum
