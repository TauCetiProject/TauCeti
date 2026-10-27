/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Basic
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Orientations from nowhere-vanishing top forms

A nowhere-vanishing continuous top form selects the orientation on which it is positive.
This file supplies the first direction of the top-form/orientation correspondence used by
orientation-sensitive differential geometry. The fibrewise characterization is the local algebraic
part of J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 15.5.
-/

public section

noncomputable section

open Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private def topFormBasis [IsManifold I 1 M] (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (trivializationAt E (TangentSpace I) x).basisAt (Module.finBasis ℝ E)
    (FiberBundle.mem_baseSet_trivializationAt' x)

/-- The fibre orientation selected by a nonzero top-degree form using the chart-local basis. -/
def topFormOrientationAt [IsManifold I 1 M]
    (φ : RoughForm I M ℝ (Module.finrank ℝ E)) (x : M) :
    _root_.Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)) :=
  if 0 < φ x (topFormBasis (I := I) x) then
    (topFormBasis (I := I) x).orientation
  else
    -(topFormBasis (I := I) x).orientation

/-- A basis is positive for `topFormOrientationAt` exactly when the form evaluates positively. -/
theorem topFormOrientationAt_spec [IsManifold I 1 M]
    {φ : RoughForm I M ℝ (Module.finrank ℝ E)} (x : M) (h0 : φ x ≠ 0)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x)) :
    b.orientation = topFormOrientationAt (I := I) φ x ↔ 0 < φ x b := by
  let b₀ := topFormBasis (I := I) x
  have hbase : φ x b₀ ≠ 0 := by
    intro hz
    apply h0
    ext v
    rw [ContinuousAlternatingMap.apply_eq_det_mul (φ x) b₀ v, hz, mul_zero]
    simp
  have hformula : φ x b = b₀.det b * φ x b₀ := by
    exact ContinuousAlternatingMap.apply_eq_det_mul (φ x) b₀ b
  have hformula' : φ x b₀ = b.det b₀ * φ x b := by
    exact ContinuousAlternatingMap.apply_eq_det_mul (φ x) b b₀
  by_cases hp : 0 < φ x b₀
  -- `topFormOrientationAt` is defined with the chart basis; expose that branch before
  -- applying the basis-orientation characterization.
  · change b.orientation = (if 0 < φ x b₀ then b₀.orientation else -b₀.orientation) ↔ _
    rw [ite_eq_left hp]
    have hor : b.orientation = b₀.orientation ↔ 0 < b₀.det b := by
      simpa only [eq_comm] using (b₀.orientation_eq_iff_det_pos b)
    rw [hor]
    constructor
    · intro hd
      rw [hformula]
      exact mul_pos hd hp
    · intro hb
      rw [hformula] at hb
      rcases (mul_pos_iff.mp hb) with ⟨hd, _⟩ | ⟨_, hneg⟩
      · exact hd
      · exact False.elim ((not_lt_of_ge (le_of_lt hp)) hneg)
  · have hn : φ x b₀ < 0 := lt_of_le_of_ne (le_of_not_gt hp) hbase
    change b.orientation = (if 0 < φ x b₀ then b₀.orientation else -b₀.orientation) ↔ _
    rw [ite_eq_right hp]
    rw [Module.Basis.orientation_eq_neg_iff_det_neg]
    constructor
    · intro hd
      have hprod : b.det b₀ * φ x b < 0 := by rw [← hformula']; exact hn
      rcases (mul_neg_iff.mp hprod) with ⟨hdetpos, hφneg⟩ | ⟨hdet, hφ⟩
      · exact False.elim ((not_lt_of_ge (le_of_lt hdetpos)) hd)
      · exact hφ
    · intro hφ
      have hprod : b.det b₀ * φ x b < 0 := by rw [← hformula']; exact hn
      rcases (mul_neg_iff.mp hprod) with ⟨hdetpos, hφneg⟩ | ⟨hdet, _⟩
      · exact False.elim ((not_lt_of_ge (le_of_lt hφ)) hφneg)
      · exact hdet


end TauCeti
