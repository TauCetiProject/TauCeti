/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic

/-!
# Half-planes bounded by a geodesic line

The imaginary axis splits `ℍ` into two open half-planes, `{z | 0 < z.re}` and
`{z | z.re < 0}`, with the axis itself as their shared boundary. This file transports that
picture by `g : PSL(2, ℝ)`, the same idiom `Geodesic.lean` uses for the line itself:
`rightHalfPlane g` and `leftHalfPlane g` are the two open half-planes bounded by
`geodesicLine g`, disjoint from each other and from the line.

## Main declarations

* `TauCeti.UpperHalfPlane.rightHalfPlane g`, `TauCeti.UpperHalfPlane.leftHalfPlane g` — the two
  open half-planes bounded by `geodesicLine g`, as `g`-translates of the canonical pair for the
  raw imaginary axis. `mem_rightHalfPlane_iff` and `mem_leftHalfPlane_iff` test membership
  directly, without unfolding the translate.
* `TauCeti.UpperHalfPlane.isOpen_rightHalfPlane`, `isOpen_leftHalfPlane` — both are open.
* `TauCeti.UpperHalfPlane.disjoint_rightHalfPlane_leftHalfPlane` — the two half-planes are
  disjoint.
* `TauCeti.UpperHalfPlane.range_geodesicLine` — the geodesic line itself, as a set, is exactly
  the `g`-translate of `{z | z.re = 0}`, matching the two half-planes' own description, so all
  three pieces of the transported picture (line, right half-plane, left half-plane) are stated
  the same way.
-/

public section

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-- The right half-plane bounded by `geodesicLine g`: the `g`-translate of the points with
positive real part. -/
def rightHalfPlane (g : PSL(2, ℝ)) : Set ℍ := g • {z : ℍ | 0 < z.re}

/-- The left half-plane bounded by `geodesicLine g`: the `g`-translate of the points with
negative real part. -/
def leftHalfPlane (g : PSL(2, ℝ)) : Set ℍ := g • {z : ℍ | z.re < 0}

theorem mem_rightHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ rightHalfPlane g ↔ 0 < (g⁻¹ • z : ℍ).re := by
  rw [rightHalfPlane, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq]

theorem mem_leftHalfPlane_iff (g : PSL(2, ℝ)) (z : ℍ) :
    z ∈ leftHalfPlane g ↔ (g⁻¹ • z : ℍ).re < 0 := by
  rw [leftHalfPlane, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_ofPred_eq]

theorem isOpen_rightHalfPlane (g : PSL(2, ℝ)) : IsOpen (rightHalfPlane g) := by
  have heq : rightHalfPlane g = (fun z : ℍ => (g⁻¹ • z : ℍ).re) ⁻¹' Set.Ioi 0 := by
    ext z
    rw [mem_rightHalfPlane_iff, Set.mem_preimage, Set.mem_Ioi]
  rw [heq]
  exact (UpperHalfPlane.continuous_re.comp (continuous_const_smul g⁻¹)).isOpen_preimage _ isOpen_Ioi

theorem isOpen_leftHalfPlane (g : PSL(2, ℝ)) : IsOpen (leftHalfPlane g) := by
  have heq : leftHalfPlane g = (fun z : ℍ => (g⁻¹ • z : ℍ).re) ⁻¹' Set.Iio 0 := by
    ext z
    rw [mem_leftHalfPlane_iff, Set.mem_preimage, Set.mem_Iio]
  rw [heq]
  exact (UpperHalfPlane.continuous_re.comp (continuous_const_smul g⁻¹)).isOpen_preimage _ isOpen_Iio

theorem disjoint_rightHalfPlane_leftHalfPlane (g : PSL(2, ℝ)) :
    Disjoint (rightHalfPlane g) (leftHalfPlane g) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [mem_rightHalfPlane_iff] at hz
  rw [mem_leftHalfPlane_iff] at hz'
  linarith

theorem range_geodesicLine_one :
    Set.range (geodesicLine (1 : PSL(2, ℝ))) = {z : ℍ | z.re = 0} := by
  ext z
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl⟩
    simp [geodesicLine_def, UpperHalfPlane.re]
  · intro hz
    refine ⟨Real.log z.im, ?_⟩
    rw [geodesicLine_def, one_smul]
    apply UpperHalfPlane.ext
    change (⟨0, Real.exp (Real.log z.im)⟩ : ℂ) = (z : ℂ)
    rw [Real.exp_log z.im_pos]
    exact Complex.ext hz.symm rfl

/-- The geodesic line, as a set, is the `g`-translate of `{z | z.re = 0}` — the boundary the two
half-planes share, described the same way they are. -/
theorem range_geodesicLine (g : PSL(2, ℝ)) :
    Set.range (geodesicLine g) = g • {z : ℍ | z.re = 0} := by
  rw [← range_geodesicLine_one, smul_range_geodesicLine, mul_one]

end TauCeti.UpperHalfPlane
