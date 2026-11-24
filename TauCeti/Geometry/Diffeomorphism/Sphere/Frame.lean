/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Diffeomorphism.Group
public import TauCeti.Geometry.Diffeomorphism.Topology
public import TauCeti.Geometry.Sphere.LinearIsometry
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Comp
import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.Differential
import TauCeti.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The frame of a self-map of a sphere

Let `Sⁿ` be the unit sphere of `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n + 1))` and fix a point `p` of it.
The **frame** of a self-map `f` of `Sⁿ` at `p` (`TauCeti.sphereFrame`) is the family of `n + 1`
vectors of `ℝⁿ⁺¹` consisting of `f p` and of the derivative of `f` at `p` applied to the standard
basis of the tangent model `ℝⁿ`, read in `ℝⁿ⁺¹`.

## Main definitions

* `TauCeti.sphereFrame p f`: the frame of `f` at `p`.

## Main results

* `TauCeti.linearIndependent_sphereFrame`: where the derivative of `f` is injective, the frame is
  linearly independent, since the derivative maps onto the tangent space `(f p)ᗮ`; in particular
  the frame of a diffeomorphism is a basis (`TauCeti.linearIndependent_sphereFrame_diffeomorph`).
* `TauCeti.continuous_sphereFrame`: each frame vector depends continuously on a `C^m` self-map,
  `1 ≤ m`, for the weak Whitney topology; likewise on a diffeomorphism
  (`TauCeti.continuous_sphereFrame_diffeomorph`).
* `TauCeti.sphereFrame_unitSphereEquiv_comp`: composing `f` with an orthogonal transformation `A`
  applies `A` to the frame.
-/

public section

open Metric Function
open scoped Manifold ContDiff EuclideanSpace TauCeti.ManifoldWeakWhitney
  TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {n : ℕ} {m : ℕ∞ω} (p : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)

/-- The **frame** of a self-map `f` of the unit sphere `Sⁿ ⊆ ℝⁿ⁺¹` at a point `p`: the point `f p`,
followed by the derivative of `f` at `p` applied to the standard basis vectors of the model space
`ℝⁿ` of the tangent space at `p`, all read in `ℝⁿ⁺¹` through the inclusion of the sphere. -/
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

/-- At a point where a self-map `f` of the sphere is differentiable with injective derivative, the
frame of `f` is linearly independent: the derivative maps onto the tangent space `(f p)ᗮ`, which
does not contain the unit vector `f p`. -/
theorem linearIndependent_sphereFrame {f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}
    (hf : MDifferentiableAt (𝓡 n) (𝓡 n) f p) (hinj : Injective (mfderiv (𝓡 n) (𝓡 n) f p)) :
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
    refine funext fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j
    · rw [sphereFrame_zero, Fin.cons_zero]
    · rw [sphereFrame_succ, Fin.cons_succ]
      exact mvfderiv_comp_apply p (contMDiff_coe_sphere.mdifferentiableAt one_ne_zero) hf _
  rw [hframe]
  exact h

/-- The frame of a `C^m` diffeomorphism of the sphere, `1 ≤ m`, is linearly independent. -/
theorem linearIndependent_sphereFrame_diffeomorph (hm : 1 ≤ m)
    (f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m) :
    LinearIndependent ℝ (sphereFrame p f) :=
  linearIndependent_sphereFrame p (f.contMDiff.mdifferentiableAt (zero_lt_one.trans_le hm).ne')
    (f.isInvertible_mfderiv (zero_lt_one.trans_le hm).ne').injective

/-- Composing a self-map of the sphere with the restriction of a linear isometry `e` applies `e` to
its frame. -/
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

/-- Each vector of the frame at `p` of a `C^m` self-map of the sphere, `1 ≤ m`, depends
continuously on the map for the weak Whitney topology. -/
theorem continuous_sphereFrame (hm : 1 ≤ m) (j : Fin (n + 1)) :
    Continuous fun f : C^m⟮𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1;
        𝓡 n, sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1⟯ ↦
      sphereFrame p f j := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
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

/-- Each vector of the frame at `p` of a `C^m` diffeomorphism of the sphere, `1 ≤ m`, depends
continuously on the diffeomorphism for the weak Whitney topology. -/
theorem continuous_sphereFrame_diffeomorph (hm : 1 ≤ m) (j : Fin (n + 1)) :
    Continuous fun f : Diff (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) m ↦
      sphereFrame p f j :=
  (continuous_sphereFrame p hm j).comp Diffeomorph.continuous_toContMDiffMap

end TauCeti
