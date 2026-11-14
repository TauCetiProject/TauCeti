/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# Examples of polar graph separation

A height linear in the unrestricted polar angle separates every pair of distinct deck sheets
when its slope is nonzero. A constant height has zero separation and cannot give an injective
parametrization of the punctured plane.

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed
  genus in a 3-manifold IV*, Section 0.
-/

public noncomputable section

namespace TauCeti.PolarGraph

/-- Height with constant angular slope; its graph is the elementary helicoidal model. -/
def linearHeight (c : ℝ) (p : PolarPoint) : ℝ := c * angle p

@[simp] theorem separation_linearHeight (c : ℝ) (k : ℤ) (p : PolarPoint) :
    separation (linearHeight c) k p = c * ((k : ℝ) * (2 * Real.pi)) := by
  simp only [separation, linearHeight, angle_deckShift]
  ring

/-- A nonzero angular slope separates all sheets of the polar cover. -/
theorem graph_linearHeight_injective {c : ℝ} (hc : c ≠ 0) :
    Function.Injective (graph (linearHeight c)) := by
  rw [← Set.injOn_univ, graph_injOn_iff]
  intro k hk p _
  rw [separation_linearHeight]
  exact mul_ne_zero hc (mul_ne_zero (by exact_mod_cast hk)
    (mul_ne_zero (by norm_num) Real.pi_ne_zero))

@[simp] theorem separation_const (c : ℝ) (k : ℤ) (p : PolarPoint) :
    separation (fun _ ↦ c) k p = 0 := by
  simp [separation]

/-- A constant-height polar graph identifies points on different deck sheets. -/
theorem not_injective_graph_const (c : ℝ) :
    ¬ Function.Injective (graph (fun _ : PolarPoint ↦ c)) := by
  intro h
  let p : PolarPoint := ⟨(1, 0), by norm_num⟩
  have hs := (graph_injOn_iff (fun _ : PolarPoint ↦ c) Set.univ).mp
    (Set.injOn_univ.mpr h) 1 (by norm_num) p (by simp [overlap])
  exact hs (separation_const c 1 p)

/-- The sector of angular width `3π` in the polar cover. -/
def threePiSector : Set PolarPoint := {p | 0 < angle p ∧ angle p < 3 * Real.pi}

/-- A one-step separation on the `3π` sector is defined precisely over its first `π` radians. -/
theorem mem_overlap_threePiSector_iff (p : PolarPoint) :
    p ∈ overlap threePiSector 1 ↔ 0 < angle p ∧ angle p < Real.pi := by
  simp only [mem_overlap_iff, threePiSector, Set.mem_ofPred_eq, angle_deckShift,
    Int.cast_one, one_mul]
  constructor
  · rintro ⟨⟨h0, _⟩, ⟨_, h3⟩⟩
    constructor
    · exact h0
    · nlinarith
  · rintro ⟨h0, hpi⟩
    constructor
    · exact ⟨h0, by nlinarith [Real.pi_pos]⟩
    · constructor <;> nlinarith [Real.pi_pos]

end TauCeti.PolarGraph
