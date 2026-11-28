/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Topology
public import TauCeti.Geometry.Sphere.LinearIsometry
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The frame of a self-map of a sphere

Let `Sⁿ` be the unit sphere of `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))` and fix a point `p` of it.
The **frame** of a self-map `f` of `Sⁿ` at `p` (`TauCeti.sphereFrame`) is the family of `n + 1`
vectors of `ℝⁿ⁺¹` consisting of `f p` and of the derivative of `f` at `p` applied to the standard
basis of the tangent model `ℝⁿ`, read in `ℝⁿ⁺¹`. It is a basis of `ℝⁿ⁺¹` when the derivative of `f`
at `p` is injective, for instance when `f` is a diffeomorphism; for an arbitrary self-map it is
only a family of vectors.

## Main definitions

* `TauCeti.sphereFrame p f`: the frame of `f` at `p`.

## Main results

* `Filter.EventuallyEq.sphereFrame_eq`: the frame depends only on the germ of `f` at `p`.
* `TauCeti.linearIndependent_sphereFrame`: where the derivative of `f` is injective, the frame is
  linearly independent, since the derivative maps onto the tangent space `(f p)ᗮ`.
* `TauCeti.continuous_sphereFrame`: the frame depends continuously on a `C^m` self-map, `1 ≤ m`,
  for the weak Whitney topology.
* `TauCeti.sphereFrame_unitSphereEquiv_comp`: postcomposing `f` with the restriction to the sphere
  of an orthogonal transformation `A`, that is, passing to `A ∘ f`, applies `A` to every vector of
  the frame.
-/

public section

open Metric Function Filter
open scoped Manifold ContDiff EuclideanSpace Topology TauCeti.ManifoldWeakWhitney

namespace TauCeti

variable {n : ℕ} {m : ℕ∞ω} (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The **frame** of a self-map `f` of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` at a point `p`: the point `f p`,
followed by the derivative of `f` at `p` applied to the standard basis vectors of the model space
`ℝⁿ` of the tangent space at `p`, all read in `ℝⁿ⁺¹` through the inclusion of the sphere. It is a
basis when the derivative of `f` at `p` is injective (`TauCeti.linearIndependent_sphereFrame`). -/
noncomputable def sphereFrame (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) :=
  Fin.cons (f p : EuclideanSpace ℝ (Fin (n + 1))) fun k ↦
    mvfderiv (𝓡 n) (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) p (EuclideanSpace.single k 1)

@[simp]
theorem sphereFrame_zero (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereFrame p f 0 = f p :=
  Fin.cons_zero _ _

@[simp]
theorem sphereFrame_succ (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (k : Fin n) :
    sphereFrame p f k.succ =
      mvfderiv (𝓡 n) (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) p
        (EuclideanSpace.single k 1) :=
  Fin.cons_succ _ _ _

/-- The frame of a self-map of the sphere at `p` depends only on the germ of the map at `p`. -/
theorem _root_.Filter.EventuallyEq.sphereFrame_eq
    {f g : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    (h : f =ᶠ[𝓝 p] g) : sphereFrame p f = sphereFrame p g := by
  have hval : (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) =ᶠ[𝓝 p]
      fun x ↦ (g x : EuclideanSpace ℝ (Fin (n + 1))) :=
    h.fun_comp Subtype.val
  rw [sphereFrame, sphereFrame, h.eq_of_nhds, hval.mvfderiv_eq]

/-- At a point where a self-map `f` of the sphere has injective derivative, the frame of `f` is
linearly independent: the derivative maps onto the tangent space `(f p)ᗮ`, which does not contain
the unit vector `f p`. -/
theorem linearIndependent_sphereFrame {f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    (hinj : Injective (mfderiv (𝓡 n) (𝓡 n) f p)) :
    LinearIndependent ℝ (sphereFrame p f) := by
  -- The standard basis of the tangent model, read in the tangent space at `p`.
  have hbasis : LinearIndependent ℝ fun k : Fin n ↦
      (EuclideanSpace.single k 1 : TangentSpace (𝓡 n) p) :=
    PiLp.linearIndependent_single_one 2 ℝ
  -- The derivative carries it to a linearly independent family of `(f p)ᗮ`.
  have h := (hbasis.map' (mfderiv (𝓡 n) (𝓡 n) f p : TangentSpace (𝓡 n) p →ₗ[ℝ] _)
    (LinearMap.ker_eq_bot_of_injective hinj)).finCons_mvfderiv_coe_sphere (f p)
  simp only [Function.comp_apply] at h
  have hframe : sphereFrame p f = Fin.cons (f p : EuclideanSpace ℝ (Fin (n + 1))) fun k ↦
      mvfderiv (𝓡 n) (Subtype.val : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        EuclideanSpace ℝ (Fin (n + 1))) (f p)
          ((mfderiv (𝓡 n) (𝓡 n) f p : TangentSpace (𝓡 n) p →ₗ[ℝ] TangentSpace (𝓡 n) (f p))
            (EuclideanSpace.single k 1)) := by
    -- `f` is differentiable at `p`, since its derivative there is injective.
    have hf := mdifferentiableAt_of_mfderiv_injective hinj
    refine funext fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j
    · rw [sphereFrame_zero, Fin.cons_zero]
    · rw [sphereFrame_succ, Fin.cons_succ]
      exact mvfderiv_comp_apply p (contMDiff_coe_sphere.mdifferentiableAt one_ne_zero) hf _
  rw [hframe]
  exact h

/-- Postcomposing a self-map `f` of the sphere with the restriction of a linear isometry `e`, that
is, passing to `e ∘ f`, applies `e` to every vector of the frame of `f`. -/
theorem sphereFrame_unitSphereEquiv_comp
    (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    sphereFrame p (e.unitSphereEquiv ∘ f) = e ∘ sphereFrame p f := by
  have h : (fun x ↦ ((e.unitSphereEquiv ∘ f) x : EuclideanSpace ℝ (Fin (n + 1)))) =
      e.toContinuousLinearEquiv ∘ fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1))) :=
    funext fun x ↦ LinearIsometryEquiv.coe_unitSphereEquiv_apply e (f x)
  refine funext fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j
  · simp [LinearIsometryEquiv.coe_unitSphereEquiv_apply]
  · rw [sphereFrame_succ, h, Function.comp_apply, sphereFrame_succ]
    exact ContinuousLinearEquiv.mvfderiv_comp_apply e.toContinuousLinearEquiv _ p _

/-- The frame at `p` of a `C^m` self-map of the sphere, `1 ≤ m`, depends continuously on the map
for the weak Whitney topology. -/
theorem continuous_sphereFrame (hm : 1 ≤ m) :
    Continuous fun f : C^m⟮𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1;
        𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1⟯ ↦
      sphereFrame p f := by
  refine continuous_pi fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j
  · simp only [sphereFrame_zero]
    exact continuous_subtypeVal.comp (ContMDiffMap.continuous_eval_const_manifoldWeakWhitney p)
  · let ι : C^m⟮𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1;
        𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))), EuclideanSpace ℝ (Fin (n + 1))⟯ :=
      ⟨Subtype.val, contMDiff_coe_sphere⟩
    have hcomp : Continuous fun f : C^m⟮𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1;
        𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1⟯ ↦ ι.comp f :=
      ContMDiffMap.continuous_comp_manifoldWeakWhitney.comp (continuous_const.prodMk continuous_id)
    have hderiv : Continuous fun f : C^m⟮𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1;
        𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1⟯ ↦
        mvfderiv (𝓡 n) (fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1)))) p :=
      ((ContMDiffMap.mvfderivCLM hm p).continuous.comp hcomp).congr fun f ↦ by
        have hι : ⇑(ι.comp f) = fun x ↦ (f x : EuclideanSpace ℝ (Fin (n + 1))) :=
          funext fun x ↦ by rw [ContMDiffMap.comp_apply, ContMDiffMap.coeFn_mk]
        rw [Function.comp_apply, ContMDiffMap.mvfderivCLM_apply, hι]
    simp only [sphereFrame_succ]
    exact (continuous_eval_const (EuclideanSpace.single k 1 : EuclideanSpace ℝ (Fin n))).comp hderiv

end TauCeti
