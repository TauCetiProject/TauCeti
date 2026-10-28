/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.QuaternionicProjectiveSpace.Charts
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth

/-!
# The standard smooth manifold structure on quaternionic projective space

The homogeneous-ratio charts on the quotient of the unit sphere by the unit quaternions form the
standard atlas on `QuaternionicProjectiveSpace n`, modelled on `ℍⁿ = Fin n → ℍ`, a real vector
space of dimension `4n`. Their transition maps are products of affine coordinate functions with
the inverse of a nonvanishing one. Multiplication of quaternions is real bilinear and inversion is
analytic on the nonzero quaternions, so the transition maps are smooth and `HPⁿ` is a real smooth
manifold of dimension `4n`.

## Main declarations

* `TauCeti.QuaternionicProjectiveSpace.instChartedSpace`: the atlas of homogeneous-ratio charts.
* `TauCeti.QuaternionicProjectiveSpace.contDiffOn_affineChart_transition`: the transition maps
  are smooth.
* `TauCeti.QuaternionicProjectiveSpace.instIsManifold`: `HPⁿ` is a smooth manifold modelled on
  `ℍⁿ`.

## References

* The atlas follows Tau Ceti's complex manifold structure on complex projective space in
  `TauCeti/Geometry/Manifold/Instances/ComplexProjectiveSpace.lean`.
-/

public section

open Set
open scoped ContDiff Manifold Quaternion

namespace TauCeti.QuaternionicProjectiveSpace

noncomputable section

variable {n : ℕ}

/-- The standard atlas consists of the `n + 1` homogeneous-ratio charts. -/
instance instChartedSpace : ChartedSpace (Fin n → ℍ) (QuaternionicProjectiveSpace n) where
  atlas := range affineChart
  chartAt p := affineChart (exists_mem_affineOpen p).choose
  mem_chart_source p := by
    simpa only [affineChart_source] using (exists_mem_affineOpen p).choose_spec
  chart_mem_atlas p := mem_range_self _

/-- Membership in the standard projective atlas means being a homogeneous-ratio chart. -/
@[simp]
theorem mem_atlas_iff (e : OpenPartialHomeomorph (QuaternionicProjectiveSpace n) (Fin n → ℍ)) :
    e ∈ atlas (Fin n → ℍ) (QuaternionicProjectiveSpace n) ↔ ∃ k, affineChart k = e :=
  Iff.rfl

/-- Homogeneous-ratio transitions are smooth wherever the new denominator is nonzero. -/
theorem contDiffOn_affineChart_transition (k l : Fin (n + 1)) (r : ℕ∞ω) :
    ContDiffOn ℝ r ((affineChart k).symm.trans (affineChart l))
      ((affineChart k).symm.trans (affineChart l)).source := by
  have hcoord (j : Fin (n + 1)) :
      ContDiff ℝ r (fun z : Fin n → ℍ ↦ Fin.insertNth (α := fun _ ↦ ℍ) k 1 z j) :=
    contDiff_pi.1 ((contDiff_const (c := (1 : ℍ))).finInsertNth (𝕜 := ℝ) (F := fun _ ↦ ℍ) k
      contDiff_id) j
  apply contDiffOn_pi.2
  intro j
  have hden (z) (hz : z ∈ ((affineChart k).symm.trans (affineChart l)).source) :
      Fin.insertNth (α := fun _ ↦ ℍ) k 1 z l ≠ 0 := by
    apply (affineParam_mem_affineOpen_iff k l z).1
    simpa only [OpenPartialHomeomorph.symm_symm, Set.mem_preimage,
      affineChart_symm_apply, affineChart_source] using hz.2
  -- Quaternionic inversion is smooth away from zero, as the ring inverse of a complete normed
  -- algebra.
  have hinv : ContDiffOn ℝ r (fun z : Fin n → ℍ ↦ (Fin.insertNth (α := fun _ ↦ ℍ) k 1 z l)⁻¹)
      ((affineChart k).symm.trans (affineChart l)).source := fun z hz ↦ by
    have h := contDiffAt_ringInverse ℝ (n := r) (Units.mk0 _ (hden z hz))
    rw [Units.val_mk0, Ring.inverse_eq_inv'] at h
    exact h.comp_contDiffWithinAt z (hcoord l).contDiffWithinAt
  exact ((hcoord (l.succAbove j)).contDiffOn.mul hinv).congr
    (fun z _ ↦ affineChart_transition k l z j)

/-- Quaternionic projective space with its standard homogeneous-coordinate atlas is a real smooth
manifold, at every differentiability order. -/
instance instIsManifold (r : ℕ∞ω) :
    IsManifold 𝓘(ℝ, Fin n → ℍ) r (QuaternionicProjectiveSpace n) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨k, rfl⟩ := (mem_atlas_iff e).1 he
  obtain ⟨l, rfl⟩ := (mem_atlas_iff e').1 he'
  simpa using contDiffOn_affineChart_transition k l r

end

end TauCeti.QuaternionicProjectiveSpace
