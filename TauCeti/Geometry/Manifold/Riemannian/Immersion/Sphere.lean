/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic

/-!
# Round rigidity from a unit position differential

An injective isometric immersion of a compact connected hypersurface into Euclidean space is
Riemannian isometric to the round unit sphere if it has a smooth unit field with the same
differential as the position map. The unit field itself is the isometry. The injectivity
assumption retains the conclusion for circle hypersurfaces, where immersions can cover the
circle more than once.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8.
* [Poincaré formalization](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public noncomputable section

open Bundle Function Manifold Metric Module
open scoped Bundle ContDiff Manifold

namespace ContMDiff

variable {E F H S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  [TopologicalSpace S] [ChartedSpace H S] [IsManifold I ∞ S]
  [BoundarylessManifold I S]
  [Bundle.RiemannianBundle (fun x : S ↦ TangentSpace I x)]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] [CompactSpace S] [ConnectedSpace S]

/-- A compact injective isometric immersion with a smooth unit field sharing its differential
is Riemannian isometric to the round unit sphere by that unit field. -/
theorem exists_riemannianIsometry_sphere {f N : S → E}
    (hN : ContMDiff I 𝓘(ℝ, E) ∞ N)
    (hdim : finrank ℝ F = n) (hn : 0 < n)
    (hunit : ∀ x, ‖N x‖ = 1) (hderiv : ∀ x, mvfderiv I N x = mvfderiv I f x)
    (hinj : Injective f)
    (hmetric : ∀ x (v w : TangentSpace I x),
      inner ℝ (mvfderiv I f x v) (mvfderiv I f x w) = inner ℝ v w) :
    ∃ e : TauCeti.RiemannianIsometry I (𝓡 n) S (sphere (0 : E) 1),
      ∀ x, (e x : E) = N x := by
  have himm (x : S) : Injective (mvfderiv I f x) :=
    ((mvfderiv I f x).toLinearMap.isometryOfInner (hmetric x)).injective
  obtain ⟨e, he⟩ := hN.exists_diffeomorph_sphere (by simp) hdim hn himm hunit hderiv hinj
  have he_comp : ((↑) : sphere (0 : E) 1 → E) ∘ e = N := funext he
  have hcomp (x : S) (v : TangentSpace I x) :
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (e x) (mfderiv I (𝓡 n) e x v) =
        mvfderiv I f x v := by
    rw [← mvfderiv_comp_apply x
      ((contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp) (e x))
      (e.mdifferentiable (by simp) x)]
    rw [he_comp, hderiv x]
  refine ⟨{ toDiffeomorph := e, inner_mfderiv' := ?_ }, he⟩
  intro x v w
  rw [TauCeti.inner_tangentSpace_sphere, hcomp, hcomp]
  exact hmetric x v w

end ContMDiff
