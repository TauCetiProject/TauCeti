/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate

/-!
# Prescribing initial covariant data

A tangent field along a smooth curve can have any prescribed value and covariant derivative
at one parameter. Consequently, at a tangent vector `(p, v)` one can choose a smooth curve
of initial tangent vectors with any prescribed base velocity and covariant velocity. Such
curves give variations of geodesic initial data, with the two independent initial data of
the resulting Jacobi field specified in advance.

These are local smoothness assertions: the curves are defined everywhere but need only be
smooth near the parameter in question. No metric, torsion condition or regularity of the
connection is needed. The field construction also works within a parameter set with unique
derivatives, including endpoints of intervals, and does not require a boundaryless manifold.

The construction uses Mathlib's `FiberBundle.extend` and the existing pullback and Leibniz
laws for `CovariantDerivative.alongCurveWithin`: if `A` extends the desired value, add
`(r - t) B` along the curve, choosing `B` to correct the initial covariant derivative.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10
  (geodesic variations with prescribed Jacobi initial data).
-/

public section

open Bundle FiberBundle
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- A smooth tangent field along a curve can realize any value and covariant derivative
at a parameter with unique derivatives. Smoothness is required only within the parameter
set near that parameter, and the connection need not be smooth. -/
theorem exists_contMDiffWithinAt_alongCurveWithin_eq {γ : 𝕜 → M} {s : Set 𝕜} {t : 𝕜}
    (hγ : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I ∞ γ s t) (hs : UniqueDiffWithinAt 𝕜 s t)
    (v w : TangentSpace I (γ t)) :
    ∃ V : ∀ r, TangentSpace I (γ r),
      ContMDiffWithinAt 𝓘(𝕜, 𝕜) I.tangent ∞
        (fun r ↦ TotalSpace.mk' E (γ r) (V r)) s t ∧
      V t = v ∧ cov.alongCurveWithin γ V s t = w := by
  let A := extend E v
  let B := extend E (w - cov A (γ t) (curveVelocityWithin I γ s t))
  have hA := contMDiffAt_extend (k := ∞) I E v
  have hB := contMDiffAt_extend (k := ∞) I E
    (w - cov A (γ t) (curveVelocityWithin I γ s t))
  have hAp := hA.comp_contMDiffWithinAt t hγ
  have hBp := hB.comp_contMDiffWithinAt t hγ
  have hf : ContMDiff 𝓘(𝕜, 𝕜) 𝓘(𝕜) ∞ (fun r : 𝕜 ↦ r - t) :=
    contMDiff_id.sub contMDiff_const
  refine ⟨fun r ↦ A (γ r) + (r - t) • B (γ r),
    hAp.add_sectionAlong ((hf t).contMDiffWithinAt.smul_totalSpace hBp), ?_, ?_⟩
  · simp [A]
  · have hcoordA := differentiableWithinAt_sectionCoord γ (fun r ↦ A (γ r))
      (hAp.mdifferentiableWithinAt (by simp))
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    have hcoordB := differentiableWithinAt_sectionCoord γ (fun r ↦ B (γ r))
      (hBp.mdifferentiableWithinAt (by simp))
      (mem_baseSet_trivializationAt E (TangentSpace I) (γ t))
    have hcoordMul : DifferentiableWithinAt 𝕜
        (sectionCoord (F := E) γ (fun r ↦ (r - t) • B (γ r)) (γ t)) s t := by
      rw [sectionCoord_smul]
      exact (differentiableWithinAt_id.sub_const t).smul hcoordB
    have hdt : derivWithin (fun r : 𝕜 ↦ r - t) s t = 1 := by
      simpa only [id_eq] using ((hasDerivWithinAt_id t s).sub_const t).derivWithin hs
    rw [alongCurveWithin_add cov γ _ _ s hcoordA hcoordMul,
      alongCurveWithin_smul cov γ _ (fun r ↦ r - t) s
        (differentiableWithinAt_id.sub_const t) hcoordB,
      alongCurveWithin_pullback_curveVelocityWithin cov γ A hs
        (hγ.mdifferentiableWithinAt (by simp)) (hA.mdifferentiableAt (by simp)),
      hdt]
    simp [B]

/-- Every pair of tangent vectors `(u, w)` is realized as the base velocity and covariant
velocity of a locally smooth curve in the tangent bundle through `(p, v)`. This constructs
arbitrary infinitesimal variations of geodesic initial data, without a metric or a smoothness
assumption on the connection. -/
theorem exists_contMDiffAt_tangentCurve_initialData [I.Boundaryless]
    (p : M) (v u w : TangentSpace I p) (t : 𝕜) :
    ∃ σ : 𝕜 → TangentBundle I M,
      σ t = TotalSpace.mk' E p v ∧ ContMDiffAt 𝓘(𝕜, 𝕜) I.tangent ∞ σ t ∧
      curveVelocity I (fun r ↦ (σ r).proj) t = u ∧
      cov.alongCurve (fun r ↦ (σ r).proj) (fun r ↦ (σ r).2) t = w := by
  obtain ⟨γ, hγt, hγ, hvel⟩ :=
    exists_contMDiffAt_curveVelocity_eq (I := I) (n := ∞) (by simp) p u t
  obtain ⟨V, hV, hVt, hDV⟩ := cov.exists_contMDiffWithinAt_alongCurveWithin_eq
    hγ.contMDiffWithinAt (s := Set.univ) uniqueDiffWithinAt_univ v w
  refine ⟨fun r ↦ TotalSpace.mk' E (γ r) (V r), ?_,
    contMDiffWithinAt_univ.mp hV, hvel, ?_⟩
  · exact TotalSpace.ext hγt (heq_of_eq hVt)
  · simpa only [alongCurveWithin_univ] using hDV

end CovariantDerivative
