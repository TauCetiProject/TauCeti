/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Smooth
public import TauCeti.Geometry.Manifold.Degree.Global
import TauCeti.Analysis.InnerProductSpace.Sphere.Hersch.Stereographic
import TauCeti.Geometry.Sphere.Connected

/-!
# The mapping degree of Hersch's sphere transformation

Hersch's sphere transformation `T_a` has degree one, and postcomposing a smooth map from a
closed oriented manifold with `T_a` preserves its signed mapping degree. Thus Hersch balancing
preserves the degree in eigenvalue estimates for maps to the sphere.

For nonzero `a`, the existing sphere-boost diffeotopy joins the identity to `T_a`. Homotopy
invariance gives degree one on a positive-dimensional sphere. On the zero-sphere, `T_a` fixes
both points.
-/

public section

noncomputable section

open Metric
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- Hersch's transformation has mapping degree one on every unit sphere. -/
@[simp]
theorem degree_herschHomeomorph
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n))
    {a : E} (ha : ‖a‖ < 1) : degree o o (herschHomeomorph ha) = 1 := by
  rcases n with _ | n
  · have hE := Fact.out (p := Module.finrank ℝ E = 0 + 1)
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hE
    rw [herschHomeomorph_eq_id_of_finrank_eq_one hE ha, degree_id]
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (n + 1)
    have := connectedSpace_sphere (E := E) (n + 1)
    by_cases ha0 : a = 0
    · have hid : (herschHomeomorph ha : sphere (0 : E) 1 → sphere (0 : E) 1) = id := by
        funext x
        exact Subtype.ext (by simp [ha0])
      rw [hid, degree_id]
    · let Φ := sphereBoostDiffeotopy (n := n + 1) (m := ∞)
        (NormedSpace.norm_normalize ha0) (Real.artanh ‖a‖)
      rw [← sphereBoostDiffeotopy_final_eq_herschHomeomorph (n := n + 1) ha ha0 (m := ∞)]
      have hdeg := degree_eq_of_homotopy o o contMDiff_id Φ.final.contMDiff
        Φ.contMDiff_cylinderMap
        (fun x ↦ congrFun Φ.cylinderMap_comp_zero x)
        (fun x ↦ congrFun Φ.cylinderMap_comp_one x)
      simpa using hdeg.symm

/-- Postcomposing a smooth map from a closed oriented manifold into an oriented unit sphere
with Hersch's transformation preserves its mapping degree. -/
@[simp]
theorem degree_herschHomeomorph_comp
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [BoundarylessManifold I M]
    [T2Space M] [CompactSpace M]
    (o : Manifold.Orientation I M (Fin n))
    (o' : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n))
    {f : M → sphere (0 : E) 1} (hf : ContMDiff I (𝓡 n) ∞ f)
    {a : E} (ha : ‖a‖ < 1) :
    degree o o' ((herschHomeomorph ha) ∘ f) = degree o o' f := by
  rcases n with _ | n
  · rw [herschHomeomorph_eq_id_of_finrank_eq_one (Fact.out (p := Module.finrank ℝ E = 0 + 1)) ha,
      Function.id_comp]
  · have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ (n + 1)
    have := connectedSpace_sphere (E := E) (n + 1)
    rw [degree_comp o o' o' hf (contMDiff_herschHomeomorph ha)
      hf.continuous.isProperMap (herschHomeomorph ha).isProperMap,
      degree_herschHomeomorph o' ha, one_mul]

end TauCeti
