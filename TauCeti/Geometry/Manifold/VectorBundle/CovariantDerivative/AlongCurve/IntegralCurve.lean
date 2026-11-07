/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Metric

/-!
# The variational equation for integral curves

For a family `F(q,t)` of integral curves of a vector field `X`, its transverse velocity
`V(t) = ∂q F(0,t)` satisfies `D_t V = ∇_V X` for every torsion-free connection.
This equation controls the differential of a flow without choosing coordinates. For a metric
connection, `IsMetricCompatible.hasDerivAt_inner_curveVelocity_self_of_integralCurve` gives
the resulting squared-length derivative `2⟨∇_V X,V⟩`. The Killing equation therefore implies
conservation of the length of `V`.

The proof uses `CovariantDerivative.alongCurve_curveVelocity_comm` and
`CovariantDerivative.alongCurve_pullback`. Only the integral-curve equation near the tested
transverse parameter is needed.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 6
  (variations and the symmetry lemma).
-/

public section

open Bundle CovariantDerivative
open scoped ContDiff Manifold Topology

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 2 M]
  {X : Π x : M, TangentSpace I x} {F : ℝ → ℝ → M} {q t : ℝ}

open TauCeti.Manifold

/-- The transverse velocity of a `C²` family of integral curves satisfies the variational
equation `D_t V = ∇_V X`. The integral-curve equation is needed only near `q`, at time `t`.
No regularity of the torsion-free connection itself is required. -/
theorem alongCurve_curveVelocity_eq_covariantDerivative
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (htor : cov.IsTorsionFree)
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t))
    (hX : MDiffAt (T% X) (F q t))
    (hcurve : ∀ᶠ r in 𝓝 q, curveVelocity I (F r) t = X (F r t)) :
    alongCurve cov (F q) (fun s ↦ curveVelocity I (fun r ↦ F r s) q) t =
      cov X (F q t) (curveVelocity I (fun r ↦ F r t) q) := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  rw [alongCurve_curveVelocity_comm cov htor (by
    simpa only [minSmoothness_of_isRCLikeNormedField] using hF),
    alongCurve_congr cov (fun r ↦ F r t) _ hcurve]
  have htrans := hF.comp q
    (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 2) t)).contMDiffAt
  exact alongCurve_pullback cov _ X
    (hasMFDerivAt_curveVelocity (htrans.mdifferentiableAt (by norm_num))) hX

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

/-- For a metric-compatible torsion-free connection, the squared transverse speed of a `C²`
family of integral curves has derivative `2⟨∇_V X,V⟩`. The field equation is needed only near
the transverse parameter at the tested time. -/
theorem IsMetricCompatible.hasDerivAt_inner_curveVelocity_self_of_integralCurve
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun x : M ↦ TangentSpace I x) cov)
    (htor : cov.IsTorsionFree)
    (hF : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2 (fun z : ℝ × ℝ ↦ F z.1 z.2) (q, t))
    (hX : MDiffAt (T% X) (F q t))
    (hcurve : ∀ᶠ r in 𝓝 q, curveVelocity I (F r) t = X (F r t)) :
    HasDerivAt (fun s ↦ inner ℝ (curveVelocity I (fun r ↦ F r s) q)
        (curveVelocity I (fun r ↦ F r s) q))
      (2 * inner ℝ (cov X (F q t) (curveVelocity I (fun r ↦ F r t) q))
        (curveVelocity I (fun r ↦ F r t) q)) t := by
  have htime := hF.comp t
    (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 2) q)).contMDiffAt
  have hγ : MDifferentiableAt 𝓘(ℝ) I (F q) t := by
    simpa only [Function.comp_def] using htime.mdifferentiableAt (by norm_num)
  have hV := hF.differentiableAt_sectionCoord_curveVelocity_fst
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (F q t))
  have hp := hcov.hasDerivAt_inner_alongCurve hγ hV hV
  rw [alongCurve_curveVelocity_eq_covariantDerivative cov htor hF hX hcurve,
    real_inner_comm, ← two_mul] at hp
  simpa only [real_inner_comm] using hp

end CovariantDerivative
