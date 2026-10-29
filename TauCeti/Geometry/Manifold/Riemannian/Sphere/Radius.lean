/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature

/-!
# The round sphere of radius `r`

The round `n`-sphere `Sⁿ(r)` of radius `r > 0` is the unit sphere `Sⁿ` of a real inner product
space `E` of dimension `n + 1`, carrying `r²` times its round metric. This is the metric induced by
the embedding `p ↦ r • p` of the unit sphere into `E`, whose image is the sphere of radius `r`.

Since the unit sphere has scalar curvature `n (n - 1)` and multiplying a metric by `c > 0`
multiplies its scalar curvature by `c⁻¹`, the scalar curvature of `Sⁿ(r)` is `n (n - 1) / r²`.
Hence `Sⁿ(r)` has positive scalar curvature exactly when `n ≥ 2`: the two-point sphere `S⁰` and
the circle `S¹` are flat.

## Main definitions

* `TauCeti.sphereRoundMetricOfRadius`: the round metric of radius `r` on the unit sphere.

## Main statements

* `TauCeti.sphereRoundMetricOfRadius_inner_eq_inner_mvfderiv_smul`: the round metric of radius `r`
  is induced by the embedding `p ↦ r • p`.
* `TauCeti.scalarCurvature_sphereRoundMetricOfRadius`: the round `n`-sphere of radius `r` has
  scalar curvature `n (n - 1) / r²`.
* `TauCeti.hasPositiveScalarCurvature_sphereRoundMetricOfRadius_iff`: the round `n`-sphere of
  radius `r` has positive scalar curvature if and only if `2 ≤ n`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 3 (the round sphere of radius `R`) and Chapter 8 (its curvature).
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {r : ℝ}

/-- The round metric of radius `r > 0` on the unit `n`-sphere: `r²` times the round metric. It is
the metric induced by the embedding `p ↦ r • p` onto the sphere of radius `r`; see
`sphereRoundMetricOfRadius_inner_eq_inner_mvfderiv_smul`. -/
def sphereRoundMetricOfRadius (r : ℝ) (hr : 0 < r) :
    ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  ((sphereRoundMetric (E := E)).ofLE le_top).rescale (fun _ ↦ r ^ 2) contMDiff_const
    fun _ ↦ pow_pos hr 2

/-- The round metric of radius `r` is `r²` times the round inner product. -/
@[simp]
theorem sphereRoundMetricOfRadius_inner (hr : 0 < r) (p : sphere (0 : E) 1)
    (v w : TangentSpace (𝓡 n) p) :
    (sphereRoundMetricOfRadius r hr).inner p v w = r ^ 2 * inner ℝ v w := by
  rw [sphereRoundMetricOfRadius, ContMDiffRiemannianMetric.rescale_inner,
    ContMDiffRiemannianMetric.ofLE_inner, sphereRoundMetric_inner, inner_tangentSpace_sphere]

/-- The round metric of radius `r` is the metric induced by the embedding `p ↦ r • p` of the unit
sphere into `E`, whose image is the sphere of radius `r`. -/
theorem sphereRoundMetricOfRadius_inner_eq_inner_mvfderiv_smul (hr : 0 < r)
    (p : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) p) :
    (sphereRoundMetricOfRadius r hr).inner p v w =
      inner ℝ (mvfderiv (𝓡 n) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) p v)
        (mvfderiv (𝓡 n) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) p w) := by
  have hι := (contMDiff_coe_sphere (E := E) (n := n) (m := 1) p).mdifferentiableAt one_ne_zero
  have h (u : TangentSpace (𝓡 n) p) :
      mvfderiv (𝓡 n) (fun q : sphere (0 : E) 1 ↦ r • (q : E)) p u =
        r • mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p u := by
    simp [mvfderiv_fun_smul mdifferentiableAt_const hι, mvfderiv_const,
      -mvfderiv_apply_eq_mfderiv_apply]
  rw [h, h, real_inner_smul_left, real_inner_smul_right, sphereRoundMetricOfRadius_inner,
    inner_tangentSpace_sphere, ← mul_assoc, sq]

/-- **Scalar curvature of the round sphere.** The round `n`-sphere of radius `r` has scalar
curvature `n (n - 1) / r²`. -/
@[simp]
theorem scalarCurvature_sphereRoundMetricOfRadius (hr : 0 < r) (p : sphere (0 : E) 1) :
    (sphereRoundMetricOfRadius (E := E) (n := n) r hr).scalarCurvature p =
      n * ((n : ℝ) - 1) / r ^ 2 := by
  rw [sphereRoundMetricOfRadius, ContMDiffRiemannianMetric.scalarCurvature_rescale_const,
    scalarCurvature_sphereRoundMetric_ofLE, inv_mul_eq_div]
  exact pow_pos hr 2

/-- The round `n`-sphere of radius `r` has positive scalar curvature if and only if `2 ≤ n`. -/
@[simp]
theorem hasPositiveScalarCurvature_sphereRoundMetricOfRadius_iff (hr : 0 < r) :
    (sphereRoundMetricOfRadius (E := E) (n := n) r hr).HasPositiveScalarCurvature ↔ 2 ≤ n := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
  obtain ⟨p⟩ : Nonempty (sphere (0 : E) 1) := (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  have hpos (m : ℕ) : 0 < (m : ℝ) * ((m : ℝ) - 1) ↔ 2 ≤ m := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · by_contra! hm
      interval_cases m <;> simp at h
    · have : (2 : ℝ) ≤ m := by exact_mod_cast h
      exact mul_pos (by linarith) (by linarith)
  simp only [ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff,
    scalarCurvature_sphereRoundMetricOfRadius, div_pos_iff_of_pos_right (pow_pos hr 2), hpos]
  exact ⟨fun h ↦ h p, fun h _ ↦ h⟩

/-- The round `n`-sphere of every radius has positive scalar curvature when `2 ≤ n`. -/
theorem hasPositiveScalarCurvature_sphereRoundMetricOfRadius (hr : 0 < r) (hn : 2 ≤ n) :
    (sphereRoundMetricOfRadius (E := E) (n := n) r hr).HasPositiveScalarCurvature :=
  (hasPositiveScalarCurvature_sphereRoundMetricOfRadius_iff hr).2 hn

end TauCeti
