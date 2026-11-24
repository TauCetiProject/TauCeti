/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Cover
import TauCeti.Analysis.InnerProductSpace.BasisSpan
import TauCeti.Analysis.Normed.Module.CoveringNumber

/-!
# Covering coordinate spheres

The volumetric bound for a unit sphere in a subspace gives finite nets in Euclidean
coordinate subspaces, with the bound depending only on the selected coordinates.
-/

public section

open Metric Set
open scoped NNReal

namespace TauCeti

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]

/-- The unit sphere supported on `s` has an `η`-net of points on that sphere, with at
most `(1 + 2 / η) ^ (dim_ℝ 𝕜 * s.card)` points. -/
theorem exists_finset_isCover_coordinateSphere (s : Finset ι) {η : ℝ≥0} (hη : η ≠ 0) :
    ∃ N : Finset (EuclideanSpace 𝕜 ι),
      (↑N : Set (EuclideanSpace 𝕜 ι)) ⊆ {x : EuclideanSpace 𝕜 ι | ‖x‖ = 1 ∧ ∀ i ∉ s, x i = 0} ∧
      IsCover η {x : EuclideanSpace 𝕜 ι | ‖x‖ = 1 ∧ ∀ i ∉ s, x i = 0} N ∧
      (N.card : ℝ) ≤ (1 + 2 / (η : ℝ)) ^ (Module.finrank ℝ 𝕜 * s.card) := by
  classical
  let V := (EuclideanSpace.basisFun ι 𝕜).spanIndices (s : Set ι)
  have hV (x : EuclideanSpace 𝕜 ι) : x ∈ V ↔ ∀ i ∉ s, x i = 0 := by
    simp only [V, OrthonormalBasis.mem_spanIndices_iff, EuclideanSpace.basisFun_repr,
      Finset.mem_coe]
  have : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ 𝕜 V
  obtain ⟨N, hNs, hN, hcard⟩ := exists_finset_isCover_sphere (E := V) hη
  let f : V → EuclideanSpace 𝕜 ι := Subtype.val
  have hf : Isometry f := isometry_subtypeVal
  have himage : f '' sphere (0 : V) 1 = {x : EuclideanSpace 𝕜 ι | ‖x‖ = 1 ∧ ∀ i ∉ s, x i = 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨mem_sphere_zero_iff_norm.mp hy, (hV _).mp y.property⟩
    · rintro ⟨hx, hs⟩
      exact ⟨⟨x, (hV x).mpr hs⟩, mem_sphere_zero_iff_norm.mpr hx, rfl⟩
  have hdim : Module.finrank ℝ V = Module.finrank ℝ 𝕜 * s.card := by
    rw [← Module.finrank_mul_finrank ℝ 𝕜 V, OrthonormalBasis.finrank_spanIndices]
  refine ⟨N.image f, ?_, ?_, ?_⟩
  · rw [Finset.coe_image, ← himage]
    exact Set.image_mono hNs
  · rw [Finset.coe_image, ← himage]
    exact (hf.isCover_image_iff _).mpr hN
  · rw [hdim] at hcard
    exact (Nat.cast_le.mpr Finset.card_image_le).trans hcard

end TauCeti
