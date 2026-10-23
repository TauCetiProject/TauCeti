/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.SpaceTime.Basic
public import TauCeti.Topology.MetricSpace.Holder

/-!
# Parabolic Hölder seminorms on time slabs

For a function `v` on a set of parabolic space-time, typically the closed time slab `E × [a, b]`,
the parabolic `α`-Hölder seminorm `[v]_{α,par}` is Mathlib's `eHolderNorm α v`, taken with respect
to the parabolic distance `dist x y + √|t - s|`. This file identifies it with the supremum of the
parabolic difference quotients and, on slabs, compares it with two separate seminorms:

* the *spatial* seminorm `spaceEHolderNorm α v`, the supremum over times `t` of the `α`-Hölder
  seminorms of the slices `x ↦ v (x, t)`;
* the *temporal* seminorm `timeEHolderNorm γ v`, the supremum over positions `x` of the
  `γ`-Hölder seminorms of the slices `t ↦ v (x, t)`, with respect to the ordinary time distance
  `|t - s|`.

A function is parabolically `α`-Hölder exactly when it is `α`-Hölder in space and `α / 2`-Hölder
in time, uniformly, with
`max (spaceEHolderNorm α v) (timeEHolderNorm (α / 2) v) ≤ eHolderNorm α v`
and `eHolderNorm α v ≤ spaceEHolderNorm α v + timeEHolderNorm (α / 2) v`.

## Main declarations

* `TauCeti.ParabolicSpaceTime.eHolderNorm_eq_iSup_dist_add_sqrt`: the parabolic seminorm is the
  supremum of `dist (v p) (v q) / (dist x y + √|t - s|) ^ α`.
* `TauCeti.ParabolicSpaceTime.spaceEHolderNorm`, `TauCeti.ParabolicSpaceTime.timeEHolderNorm`:
  the separate spatial and temporal seminorms.
* `TauCeti.ParabolicSpaceTime.spaceEHolderNorm_le_eHolderNorm`,
  `TauCeti.ParabolicSpaceTime.timeEHolderNorm_div_two_le_eHolderNorm`,
  `TauCeti.ParabolicSpaceTime.eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm`: the
  comparison of the parabolic seminorm with the separate ones.
* `TauCeti.ParabolicSpaceTime.memHolder_slab_iff`: the corresponding characterisation of
  parabolic Hölder functions.

## References

* N. V. Krylov, *Lectures on elliptic and parabolic equations in Hölder spaces*, AMS, 1996.
* A. Lunardi, *Linear and nonlinear diffusion problems*, lecture notes, Cortona, 2004.
-/

public section
noncomputable section

open Set
open scoped ENNReal NNReal

namespace TauCeti.ParabolicSpaceTime

variable {E F : Type*} {a b : ℝ}

/-- The parabolic Hölder seminorm of a function on a set of parabolic space-time is the supremum
of the parabolic difference quotients `dist (v p) (v q) / (dist x y + √|t - s|) ^ α` over distinct
points `p = (x, t)` and `q = (y, s)`. -/
theorem eHolderNorm_eq_iSup_dist_add_sqrt [MetricSpace E] [PseudoMetricSpace F] (α : ℝ≥0)
    {S : Set (ParabolicSpaceTime E)} (v : S → F) :
    eHolderNorm α v = ⨆ (p) (q) (_ : p ≠ q), ENNReal.ofReal (dist (v p) (v q) /
      (dist (p : ParabolicSpaceTime E).space (q : ParabolicSpaceTime E).space +
        √|(p : ParabolicSpaceTime E).time - (q : ParabolicSpaceTime E).time|) ^ (α : ℝ)) := by
  simp_rw [eHolderNorm_eq_iSup_dist, Subtype.dist_eq, dist_eq]

variable [PseudoEMetricSpace F]

/-- The spatial `α`-Hölder seminorm of a function on the slab `E × [a, b]`: the supremum over
times `t ∈ [a, b]` of the `α`-Hölder seminorms of the slices `x ↦ v (x, t)`. -/
def spaceEHolderNorm [PseudoEMetricSpace E] (α : ℝ≥0) (v : slab (E := E) a b → F) : ℝ≥0∞ :=
  ⨆ t : Icc a b, eHolderNorm α fun x => v (slabMk x t)

/-- The temporal `γ`-Hölder seminorm of a function on the slab `E × [a, b]`: the supremum over
positions `x` of the `γ`-Hölder seminorms of the slices `t ↦ v (x, t)`, with respect to the
ordinary distance `|t - s|` on `[a, b]`. -/
def timeEHolderNorm (γ : ℝ≥0) (v : slab (E := E) a b → F) : ℝ≥0∞ :=
  ⨆ x : E, eHolderNorm γ fun t : Icc a b => v (slabMk x t)

/-- The spatial seminorm is bounded by `C` exactly when every time slice satisfies the
`α`-Hölder inequality with constant `C`. -/
theorem spaceEHolderNorm_le_iff [MetricSpace E] {α : ℝ≥0} {v : slab (E := E) a b → F} {C : ℝ≥0∞} :
    spaceEHolderNorm α v ≤ C ↔ ∀ (t : Icc a b) (x y : E),
      edist (v (slabMk x t)) (v (slabMk y t)) ≤ C * edist x y ^ (α : ℝ) := by
  simp only [spaceEHolderNorm, iSup_le_iff, eHolderNorm_le_iff]

/-- The temporal seminorm is bounded by `C` exactly when every spatial position satisfies the
`γ`-Hölder inequality in time with constant `C`. -/
theorem timeEHolderNorm_le_iff {γ : ℝ≥0} {v : slab (E := E) a b → F} {C : ℝ≥0∞} :
    timeEHolderNorm γ v ≤ C ↔ ∀ (x : E) (t s : Icc a b),
      edist (v (slabMk x t)) (v (slabMk x s)) ≤ C * edist t s ^ (γ : ℝ) := by
  simp only [timeEHolderNorm, iSup_le_iff, eHolderNorm_le_iff]

variable [MetricSpace E]

/-- The spatial seminorm is bounded by the parabolic seminorm: at a common time, the parabolic
distance is the spatial distance. -/
theorem spaceEHolderNorm_le_eHolderNorm (α : ℝ≥0) (v : slab (E := E) a b → F) :
    spaceEHolderNorm α v ≤ eHolderNorm α v := by
  refine spaceEHolderNorm_le_iff.2 fun t x y => ?_
  simpa [edist_slabMk] using edist_le_eHolderNorm_mul α v (slabMk x t) (slabMk y t)

/-- The temporal `α / 2`-seminorm is bounded by the parabolic `α`-seminorm: at a common position,
the parabolic distance is the square root of the time distance. -/
theorem timeEHolderNorm_div_two_le_eHolderNorm (α : ℝ≥0) (v : slab (E := E) a b → F) :
    timeEHolderNorm (α / 2) v ≤ eHolderNorm α v := by
  refine timeEHolderNorm_le_iff.2 fun x t s => ?_
  have h := edist_le_eHolderNorm_mul α v (slabMk x t) (slabMk x s)
  rw [edist_slabMk, edist_self x, zero_add, ← ENNReal.rpow_mul, one_div_mul_eq_div] at h
  rwa [NNReal.coe_div, NNReal.coe_two]

/-- The parabolic `α`-seminorm is bounded by the sum of the spatial `α`-seminorm and the temporal
`α / 2`-seminorm. -/
theorem eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm (α : ℝ≥0)
    (v : slab (E := E) a b → F) :
    eHolderNorm α v ≤ spaceEHolderNorm α v + timeEHolderNorm (α / 2) v := by
  refine eHolderNorm_le_iff.2 fun p q => ?_
  obtain ⟨x, t, rfl⟩ : ∃ x t, slabMk x t = p := ⟨_, _, slabMk_space_slabTime p⟩
  obtain ⟨y, s, rfl⟩ : ∃ y s, slabMk y s = q := ⟨_, _, slabMk_space_slabTime q⟩
  have hspace : edist x y ^ (α : ℝ) ≤ edist (slabMk x t) (slabMk y s) ^ (α : ℝ) := by
    rw [edist_slabMk]
    gcongr
    exact le_self_add
  have htime : edist t s ^ ((α / 2 : ℝ≥0) : ℝ) ≤ edist (slabMk x t) (slabMk y s) ^ (α : ℝ) := by
    rw [NNReal.coe_div, NNReal.coe_two, ← one_div_mul_eq_div, ENNReal.rpow_mul, edist_slabMk]
    gcongr
    exact le_add_self
  -- Move first in space at the time `t`, then in time at the position `y`.
  calc edist (v (slabMk x t)) (v (slabMk y s))
      ≤ edist (v (slabMk x t)) (v (slabMk y t)) + edist (v (slabMk y t)) (v (slabMk y s)) :=
        edist_triangle _ _ _
    _ ≤ spaceEHolderNorm α v * edist x y ^ (α : ℝ) +
        timeEHolderNorm (α / 2) v * edist t s ^ ((α / 2 : ℝ≥0) : ℝ) := by
        gcongr
        · exact spaceEHolderNorm_le_iff.1 le_rfl t x y
        · exact timeEHolderNorm_le_iff.1 le_rfl y t s
    _ ≤ (spaceEHolderNorm α v + timeEHolderNorm (α / 2) v) *
        edist (slabMk x t) (slabMk y s) ^ (α : ℝ) := by
        rw [add_mul]
        gcongr

/-- A function on a slab is parabolically `α`-Hölder exactly when it is `α`-Hölder in space and
`α / 2`-Hölder in time, uniformly in the other variable. -/
theorem memHolder_slab_iff {α : ℝ≥0} {v : slab (E := E) a b → F} :
    MemHolder α v ↔ spaceEHolderNorm α v < ∞ ∧ timeEHolderNorm (α / 2) v < ∞ := by
  rw [← eHolderNorm_lt_top]
  refine ⟨fun h => ⟨(spaceEHolderNorm_le_eHolderNorm α v).trans_lt h,
    (timeEHolderNorm_div_two_le_eHolderNorm α v).trans_lt h⟩, fun h => ?_⟩
  exact (eHolderNorm_le_spaceEHolderNorm_add_timeEHolderNorm α v).trans_lt
    (ENNReal.add_lt_top.2 h)

end TauCeti.ParabolicSpaceTime
