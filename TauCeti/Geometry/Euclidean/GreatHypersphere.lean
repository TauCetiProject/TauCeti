/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Intersections of great hyperspheres

Two great hyperspheres in a Euclidean unit sphere of dimension at least two meet. The point of
intersection is a unit vector orthogonal to both defining normals.
-/

public section

open InnerProductSpace Set

noncomputable section

namespace TauCeti

private theorem exists_unit_orthogonal_pair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 < Module.finrank ℝ E) (a b : E) :
    ∃ x : E, ‖x‖ = 1 ∧ ⟪x, a⟫_ℝ = 0 ∧ ⟪x, b⟫_ℝ = 0 := by
  let K : Submodule ℝ E := Submodule.span ℝ ({a, b} : Set E)
  have hK : Module.finrank ℝ K ≤ 2 := by
    calc
      Module.finrank ℝ K ≤ Set.ncard ({a, b} : Set E) :=
        finrank_span_le_ncard (R := ℝ) ({a, b} : Set E) (by simp)
      _ ≤ Set.ncard ({b} : Set E) + 1 := Set.ncard_insert_le a {b}
      _ = 2 := by simp
  have hdimK := K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero).mp hpos
  have hv0 : (v : E) ≠ 0 := by
    intro h
    apply hv
    exact Subtype.ext h
  have haK : a ∈ K := Submodule.subset_span (by simp)
  have hbK : b ∈ K := Submodule.subset_span (by simp)
  have ha : ⟪(v : E), a⟫_ℝ = 0 := K.inner_left_of_mem_orthogonal haK v.property
  have hb : ⟪(v : E), b⟫_ℝ = 0 := K.inner_left_of_mem_orthogonal hbK v.property
  let x : E := ‖(v : E)‖⁻¹ • (v : E)
  refine ⟨x, ?_, ?_, ?_⟩
  · simp [x, norm_smul, hv0]
  · simp only [x, real_inner_smul_left, ha, mul_zero]
  · simp only [x, real_inner_smul_left, hb, mul_zero]

/-- Two great hyperspheres in a unit sphere of dimension at least two meet. The defining
normals may be equal or zero. -/
theorem nonempty_unitSphere_inter_orthogonal_pair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (hdim : 2 < Module.finrank ℝ E) (a b : E) :
    (Metric.sphere (0 : E) 1 ∩ {x : E | ⟪x, a⟫_ℝ = 0} ∩
      {x : E | ⟪x, b⟫_ℝ = 0}).Nonempty := by
  obtain ⟨x, hx, hxa, hxb⟩ := exists_unit_orthogonal_pair hdim a b
  exact ⟨x, ⟨⟨by simpa [Metric.mem_sphere] using hx, hxa⟩, hxb⟩⟩

/-- The great hyperspheres with normals `a` and `b` in `S^(n+1)` intersect for `n ≥ 1`. -/
theorem nonempty_greatHyperspheres_fin (n : ℕ) (hn : 0 < n)
    (a b : EuclideanSpace ℝ (Fin (n + 2))) :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 ∩
      {x | ⟪x, a⟫_ℝ = 0} ∩ {x | ⟪x, b⟫_ℝ = 0}).Nonempty := by
  apply nonempty_unitSphere_inter_orthogonal_pair
  simpa only [finrank_euclideanSpace_fin] using (show 2 < n + 2 by omega)

end TauCeti
