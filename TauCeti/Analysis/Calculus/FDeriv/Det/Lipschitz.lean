/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Lipschitz
public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# The determinant is Lipschitz on bounded sets

Over a complete nontrivially normed field, the determinant of a continuous linear endomorphism of
a normed space is Lipschitz on every bounded set of endomorphisms. In finite dimension it is a
continuous multilinear map of the rows of the matrix in a basis, and these rows depend linearly
and continuously on the endomorphism; in infinite dimension it is the constant `1`. This bounds
the change of the Jacobian determinant `det DΦ` of a map with Lipschitz derivative, as needed for
coefficients transformed by a change of variables.

## Main results

* `ContinuousLinearMap.exists_lipschitzOnWith_det_of_isBounded`: the determinant is Lipschitz on
  every bounded set of continuous linear endomorphisms.
-/

public section

namespace ContinuousLinearMap

/-- The determinant of a continuous linear endomorphism of a normed space over a complete
nontrivially normed field is Lipschitz on every bounded set of endomorphisms. -/
theorem exists_lipschitzOnWith_det_of_isBounded {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [CompleteSpace 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {s : Set (E →L[𝕜] E)}
    (hs : Bornology.IsBounded s) : ∃ K, LipschitzOnWith K (fun f : E →L[𝕜] E ↦ f.det) s := by
  by_cases hE : FiniteDimensional 𝕜 E
  · obtain ⟨r, hr⟩ := hs.subset_closedBall 0
    let b := Module.finBasis 𝕜 E
    set n := Module.finrank 𝕜 E
    -- The rows of the matrix of `f` in the basis `b`.
    let R : (E →L[𝕜] E) →L[𝕜] (Fin n → Fin n → 𝕜) :=
      LinearMap.toContinuousLinearMap ((Matrix.ofLinearEquiv 𝕜).symm.toLinearMap ∘ₗ
        (LinearMap.toMatrix b b).toLinearMap ∘ₗ ContinuousLinearMap.coeLM 𝕜)
    -- The determinant as a continuous multilinear map of the rows.
    let D : ContinuousMultilinearMap 𝕜 (fun _ : Fin n ↦ Fin n → 𝕜) 𝕜 :=
      { (Matrix.detRowAlternating : (Fin n → 𝕜) [⋀^Fin n]→ₗ[𝕜] 𝕜).toMultilinearMap with
        cont := (continuous_id (X := Fin n → Fin n → 𝕜)).matrix_det }
    have hD (f : E →L[𝕜] E) : D (R f) = f.det := LinearMap.det_toMatrix b f
    have hR : ∀ f ∈ s, ‖R f‖ ≤ ‖R‖ * max r 0 := fun f hf =>
      (R.le_opNorm f).trans (by
        gcongr
        exact (mem_closedBall_zero_iff.1 (hr hf)).trans (le_max_left _ _))
    have hC : 0 ≤ ‖D‖ * n * (‖R‖ * max r 0) ^ (n - 1) * ‖R‖ := by positivity
    refine ⟨Real.toNNReal (‖D‖ * n * (‖R‖ * max r 0) ^ (n - 1) * ‖R‖),
      LipschitzOnWith.of_dist_le_mul fun f hf g hg => ?_⟩
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hC, ← hD, ← hD]
    calc ‖D (R f) - D (R g)‖ ≤ ‖D‖ * n * max ‖R f‖ ‖R g‖ ^ (n - 1) * ‖R f - R g‖ := by
          simpa only [Fintype.card_fin] using D.norm_image_sub_le (R f) (R g)
      _ ≤ ‖D‖ * n * (‖R‖ * max r 0) ^ (n - 1) * (‖R‖ * ‖f - g‖) := by
          gcongr
          · exact max_le (hR f hf) (hR g hg)
          · rw [← map_sub]
            exact R.le_opNorm _
      _ = _ := by ring
  · -- In infinite dimension the determinant is the constant `1`.
    refine ⟨0, LipschitzOnWith.of_dist_le_mul fun f _ g _ ↦ ?_⟩
    rw [ContinuousLinearMap.det, ContinuousLinearMap.det,
      LinearMap.det_eq_one_of_not_module_finite hE, LinearMap.det_eq_one_of_not_module_finite hE,
      dist_self, NNReal.coe_zero, zero_mul]

end ContinuousLinearMap
