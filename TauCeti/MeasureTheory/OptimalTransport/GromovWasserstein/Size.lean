/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.GromovWasserstein.Basic
public import Mathlib.Topology.EMetricSpace.Weak

/-!
# Size and stability for measured kernels

The size of a measured kernel is the `Lᵖ` distance of its values from a chosen point in the
target. The Gromov–Wasserstein distance controls the difference of these sizes: compare each
kernel with the one-point kernel at the same target point and apply the triangle inequality.
This is the size-stability part of the profile hierarchy for measured-kernel invariants.

The normalization follows Bauer–Mémoli–Needham–Nishino, *The Z-Gromov–Wasserstein distance*,
Theorem 50; no factor `1 / 2` is used here.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [PseudoEMetricSpace Z]
  {μ : Measure X} {ν : Measure Y} {ωX : X × X → Z} {ωY : Y × Y → Z}

/-- The `p`-size of a measured kernel about `z₀`: the `Lᵖ(μ ⊗ μ)` norm of its distance from
`z₀`. -/
def gromovWassersteinSize (p : ℝ≥0∞) (μ : Measure X) (ω : X × X → Z) (z₀ : Z) : ℝ≥0∞ :=
  eLpNorm (fun q ↦ edist (ω q) z₀) p (μ.prod μ)

/-- The defining `Lᵖ` formula for kernel size. -/
@[simp] theorem gromovWassersteinSize_def (p : ℝ≥0∞) (μ : Measure X) (ω : X × X → Z)
    (z₀ : Z) :
    gromovWassersteinSize p μ ω z₀ = eLpNorm (fun q ↦ edist (ω q) z₀) p (μ.prod μ) := (rfl)

/-- Kernel size is `1`-Lipschitz with respect to Gromov–Wasserstein distance. The target point
is shared by the two sizes, and the estimate includes `p = ∞`. -/
theorem edist_gromovWassersteinSize_le_gromovWassersteinEDist
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hp : 1 ≤ p)
    (hωX : AEStronglyMeasurable ωX (μ.prod μ)) (hωY : AEStronglyMeasurable ωY (ν.prod ν))
    (z₀ : Z) :
    edist (gromovWassersteinSize p μ ωX z₀) (gromovWassersteinSize p ν ωY z₀) ≤
      gromovWassersteinEDist p μ ωX ν ωY := by
  let ω₀ : Unit × Unit → Z := fun _ ↦ z₀
  have hμ : gromovWassersteinEDist p μ ωX (Measure.dirac ()) ω₀ =
      gromovWassersteinSize p μ ωX z₀ := by
    rw [gromovWassersteinEDist_dirac_right () ω₀ hωX]
    rfl
  have hμ' : gromovWassersteinEDist p ν ωY (Measure.dirac ()) ω₀ =
      gromovWassersteinSize p ν ωY z₀ := by
    rw [gromovWassersteinEDist_dirac_right () ω₀ hωY]
    rfl
  have htri₁ := gromovWassersteinEDist_triangle (p := p) (μ := μ) (ν := ν)
    (ρ := Measure.dirac ()) (ωX := ωX) (ωY := ωY) (ωW := ω₀) hp hωX hωY
    aestronglyMeasurable_const
  have htri₂ := gromovWassersteinEDist_triangle (p := p) (μ := ν)
    (ν := μ) (ρ := Measure.dirac ()) (ωX := ωY) (ωY := ωX) (ωW := ω₀) hp hωY
    hωX aestronglyMeasurable_const
  rw [hμ, hμ'] at htri₁
  rw [hμ', hμ] at htri₂
  rw [gromovWassersteinEDist_comm] at htri₂
  rw [ENNReal.edist_le_iff_le_add_right]
  exact ⟨by simpa [add_comm] using htri₁, by simpa [add_comm] using htri₂⟩

end TauCeti
