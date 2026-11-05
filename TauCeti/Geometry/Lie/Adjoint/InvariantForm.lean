/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Infinitesimal
public import Mathlib.Algebra.Lie.InvariantForm
import TauCeti.Geometry.Lie.Exponential.Derivative.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Constancy

/-!
# Ad-invariant and infinitesimally invariant bilinear forms

An Ad-invariant bilinear form on the tangent Lie algebra of a smooth real Lie group is
infinitesimally invariant. Conversely, on a connected group infinitesimal invariance implies
Ad-invariance. No symmetry or positivity is required of the form.

These implications connect the inner products defining bi-invariant Riemannian metrics with
the Lie-invariant forms used to compute their Levi-Civita connections and curvature. The
connectedness hypothesis belongs only to the converse: infinitesimal invariance cannot detect
the action of other connected components.

We use `TauCeti.Lie.hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero` for `d Ad = ad`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3.
* J. Milnor, *Curvatures of left invariant metrics on Lie groups*, Advances in Math. 21
  (1976), 293–329.
-/

public noncomputable section

open Manifold
open scoped ContDiff Manifold

namespace TauCeti.Lie

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {b : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G →L[ℝ] ℝ}

/-- Along an exponential line, the derivative at zero of a bilinear form applied to two
adjoint orbits is the sum of its two Lie-bracket terms. -/
theorem _root_.ContinuousLinearMap.hasDerivAt_tangentAd_mulInvariantExp_smul_zero
    (b : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G →L[ℝ] ℝ)
    (X Y Z : GroupLieAlgebra I G) :
    letI : T2Space G := I.t2Space_of_lieGroup ∞
    HasDerivAt (fun t : ℝ ↦ b (tangentAd (mulInvariantExp (t • X)) Y)
      (tangentAd (mulInvariantExp (t • X)) Z)) (b Y ⁅X, Z⁆ + b ⁅X, Y⁆ Z) 0 := by
  let : T2Space G := I.t2Space_of_lieGroup ∞
  let : NormedAddCommGroup (GroupLieAlgebra I G) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (GroupLieAlgebra I G) := inferInstanceAs (NormedSpace ℝ E)
  have hY := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) X Y
  have hZ := hasDerivAt_tangentAd_mulInvariantExp_smul_apply_zero (I := I) X Z
  convert! ContinuousLinearMap.hasDerivAt_of_bilinear (B := b)
    (fun _ ↦ hY) (fun _ ↦ hZ) using 1
  simp only [zero_smul, mulInvariantExp_zero, tangentAd_one, LieEquiv.refl_apply,
    LieAlgebra.ad_apply]
  -- The derivative theorem uses `show E from` for each tangent vector. Here the tangent Lie
  -- algebra has exactly the model's norm instances, so the remaining model/tangent casts reduce.
  rfl

/-- An Ad-invariant bilinear form is invariant under the tangent Lie algebra. The group may
be disconnected, and the form need not be symmetric or nondegenerate. -/
theorem lieInvariant_of_adjoint_invariant
    (hb : ∀ (g : G) (Y Z : GroupLieAlgebra I G),
      b (adjointContinuousLinearMap g Y) (adjointContinuousLinearMap g Z) = b Y Z) :
    b.toBilinForm.lieInvariant (GroupLieAlgebra I G) := by
  let : T2Space G := I.t2Space_of_lieGroup ∞
  intro X Y Z
  have h := b.hasDerivAt_tangentAd_mulInvariantExp_smul_zero X Y Z
  have heq : (fun t : ℝ ↦ b (tangentAd (mulInvariantExp (t • X)) Y)
      (tangentAd (mulInvariantExp (t • X)) Z)) = fun _ ↦ b Y Z := by
    funext t
    simpa only [tangentAd_apply] using hb (mulInvariantExp (t • X)) Y Z
  rw [heq] at h
  simp only [ContinuousLinearMap.toBilinForm_apply]
  linarith [h.unique (hasDerivAt_const 0 (b Y Z))]

/-- On a connected Lie group, an infinitesimally invariant bilinear form is Ad-invariant. -/
theorem adjoint_invariant_of_lieInvariant [PreconnectedSpace G]
    (hb : b.toBilinForm.lieInvariant (GroupLieAlgebra I G))
    (g : G) (Y Z : GroupLieAlgebra I G) :
    b (adjointContinuousLinearMap g Y) (adjointContinuousLinearMap g Z) = b Y Z := by
  let : T2Space G := I.t2Space_of_lieGroup ∞
  -- Use the model's normed-space structure for smoothness and bilinear precomposition.
  let : NormedAddCommGroup (GroupLieAlgebra I G) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (GroupLieAlgebra I G) := inferInstanceAs (NormedSpace ℝ E)
  let : IsNormableSpace ℝ (GroupLieAlgebra I G) := inferInstanceAs (IsNormableSpace ℝ E)
  let f : G → ℝ := fun x ↦ b (tangentAd x Y) (tangentAd x Z)
  have hf : ContMDiff I 𝓘(ℝ) ∞ f :=
    (b.contMDiff.comp (contMDiff_tangentAd_apply_const (I := I) (G := G) Y)).clm_apply
      (contMDiff_tangentAd_apply_const (I := I) (G := G) Z)
  have hzero (x : G) : mfderiv I 𝓘(ℝ) f x = 0 := by
    ext v
    obtain ⟨X, rfl⟩ := exists_mulInvariantVectorField_eq v
    have hpath := (hf.mdifferentiable (by simp) x).hasMFDerivAt
      |>.hasDerivAt_comp_mul_mulInvariantExp_smul_zero X
    let A : GroupLieAlgebra I G →L[ℝ] GroupLieAlgebra I G := adjointContinuousLinearMap (I := I) x
    have h : HasDerivAt (fun t : ℝ ↦ f (x * mulInvariantExp (t • X)))
        (b (tangentAd x Y) (tangentAd x ⁅X, Z⁆) +
          b (tangentAd x ⁅X, Y⁆) (tangentAd x Z)) 0 := by
      simpa only [ContinuousLinearMap.bilinearComp_apply, A, f, tangentAd_apply,
        adjointContinuousLinearMap_mul, ContinuousLinearMap.comp_apply] using
        (b.bilinearComp A A).hasDerivAt_tangentAd_mulInvariantExp_smul_zero X Y Z
    have hskew := hb (tangentAd x X) (tangentAd x Y) (tangentAd x Z)
    have hderiv : HasDerivAt (fun t : ℝ ↦ f (x * mulInvariantExp (t • X))) 0 0 := by
      apply h.congr_deriv
      simp only [LieEquiv.map_lie, ContinuousLinearMap.toBilinForm_apply] at hskew ⊢
      linarith
    exact hpath.unique hderiv
  have heq := (hf.mdifferentiable (by simp)).apply_eq_of_mfderiv_eq_zero hzero g 1
  simpa only [f, tangentAd_apply, adjointContinuousLinearMap_one,
    ContinuousLinearMap.id_apply] using heq

/-- On a connected Lie group, group-level and infinitesimal invariance of a bilinear form
are equivalent. -/
theorem lieInvariant_iff_adjoint_invariant [PreconnectedSpace G] :
    b.toBilinForm.lieInvariant (GroupLieAlgebra I G) ↔
      ∀ (g : G) (Y Z : GroupLieAlgebra I G),
        b (adjointContinuousLinearMap g Y) (adjointContinuousLinearMap g Z) = b Y Z :=
  ⟨adjoint_invariant_of_lieInvariant, lieInvariant_of_adjoint_invariant⟩

end TauCeti.Lie
