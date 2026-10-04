/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
public import TauCeti.AlgebraicTopology.NotSimplyConnected
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Topology.Homotopy.PuncturedStarConvex
public import TauCeti.Topology.JordanCurve.Basic

import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.AlgebraicTopology.FundamentalGroup.Product
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# The fundamental group of a punctured star-convex set

Let `V` be star-convex about `p` in a real normed space, and let `sphere p r ⊆ V` with `r > 0`.
Since the inclusion of the sphere into `V \ {p}` is a homotopy equivalence
(`StarConvex.sphereHomotopyEquiv`), it induces an isomorphism of fundamental groups at every
point of the sphere. The isomorphism is the map `FundamentalGroup.map` of the inclusion itself,
so a loop on the sphere represents the same class in `V \ {p}` as on the sphere, and every loop of
`V \ {p}` based on the sphere is homotopic to one on the sphere.

In `ℂ` the sphere is a circle, so the fundamental group of `V \ {p}` is infinite cyclic. This is
the computation that identifies the fundamental group of a punctured convex domain in the plane,
such as the half-plane `{z | z.re < 1}` punctured at `0`, with that of a small circle about the
puncture.

## Main declarations

* `StarConvex.sphereFundamentalGroupMulEquiv`: the isomorphism
  `π₁(sphere p r, x) ≃* π₁(V \ {p}, x)` induced by the inclusion.
* `StarConvex.fundamentalGroupMulEquivInt`: for `V ⊆ ℂ`, `π₁(V \ {p}, x) ≃* ℤ` at a point `x` of
  the circle `sphere p r`.
* `Complex.sphereLoop` and `StarConvex.fundamentalGroupMulEquivInt_sphereLoop`: the loop going once
  counterclockwise around `sphere p r` from `p + r` is sent to the generator `ofAdd 1`, so its
  class generates `π₁(V \ {p}, p + r)`.
* `Complex.directionFrom` and `StarConvex.fundamentalGroup_map_directionFrom_bijective`: the
  direction map `z ↦ (z - p) / ‖z - p‖` to the unit circle induces a bijection of fundamental
  groups at every point of `V \ {p}`, on the circle or off it. Composed with
  `Circle.fundamentalGroupMulEquiv`, it identifies `π₁(V \ {p}, z)` with `ℤ` by the degree of the
  direction of a loop.
* `StarConvex.pathConnectedSpace_diff_singleton`: `V \ {p}` is path connected.
* `StarConvex.fundamentalGroup_map_directionFrom_comp_snd_bijective`: for simply connected `U`,
  the direction of the second coordinate induces a bijection of fundamental groups at every point
  of `U × (V \ {p})`.
* `Complex.loopAround` and `TauCeti.zpowers_loopAround_eq_top`: for simply connected `U`, the loop
  `t ↦ (u, p + (z - p) e^{2πit})` around the puncture generates `π₁(U × (ball p R \ {p}), (u, z))`.

## References

Hatcher, *Algebraic Topology*, Proposition 1.18 (homotopy equivalences induce isomorphisms on
`π₁`) and Theorem 1.7 (`π₁(S¹) ≅ ℤ`).
-/

public section

noncomputable section

open Metric Set

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Set E} {p : E} {r : ℝ}

/-- **The fundamental group of a punctured star-convex set is that of a sphere about the
puncture.** If `V` is star-convex about `p` and contains `sphere p r` with `r > 0`, the inclusion
of the sphere into `V \ {p}` induces an isomorphism of fundamental groups at every point `x` of the
sphere. -/
def _root_.StarConvex.sphereFundamentalGroupMulEquiv (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) (x : sphere p r) :
    FundamentalGroup (sphere p r) x ≃*
      FundamentalGroup ↥(V \ {p}) (hV.sphereHomotopyEquiv hr hS x) :=
  MulEquiv.ofBijective (FundamentalGroup.map (hV.sphereHomotopyEquiv hr hS).toFun x)
    ((hV.sphereHomotopyEquiv hr hS).fundamentalGroup_map_bijective x)

/-- The isomorphism `StarConvex.sphereFundamentalGroupMulEquiv` is the map induced on fundamental
groups by the inclusion of the sphere. -/
@[simp]
theorem _root_.StarConvex.sphereFundamentalGroupMulEquiv_apply (hV : StarConvex ℝ p V)
    (hr : 0 < r) (hS : sphere p r ⊆ V) (x : sphere p r) (γ : FundamentalGroup (sphere p r) x) :
    hV.sphereFundamentalGroupMulEquiv hr hS x γ =
      FundamentalGroup.map (hV.sphereHomotopyEquiv hr hS).toFun x γ :=
  (rfl)

end NormedSpace

section Complex

variable {V : Set ℂ} {p : ℂ} {r R : ℝ}

/-- **The fundamental group of a punctured star-convex subset of `ℂ` is infinite cyclic.** If `V`
is star-convex about `p` and contains the circle `sphere p r` with `r > 0`, then
`π₁(V \ {p}, x) ≃* ℤ` at every point `x` of that circle. It is the inverse of the isomorphism
induced by the inclusion of the circle, followed by the parametrization `w ↦ (w - p) / r` of the
circle by `Circle` and the computation `Circle.fundamentalGroupMulEquiv`. -/
def _root_.StarConvex.fundamentalGroupMulEquivInt (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) (x : sphere p r) :
    FundamentalGroup ↥(V \ {p}) (hV.sphereHomotopyEquiv hr hS x) ≃* Multiplicative ℤ :=
  (hV.sphereFundamentalGroupMulEquiv hr hS x).symm.trans
    ((FundamentalGroup.homeomorphMulEquiv (sphereCircleHomeomorph p hr) x).trans
      (Circle.fundamentalGroupMulEquiv _))

/-- `StarConvex.fundamentalGroupMulEquivInt` factors through the circle `sphere p r`. -/
theorem _root_.StarConvex.fundamentalGroupMulEquivInt_def (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) (x : sphere p r) :
    hV.fundamentalGroupMulEquivInt hr hS x =
      (hV.sphereFundamentalGroupMulEquiv hr hS x).symm.trans
        ((FundamentalGroup.homeomorphMulEquiv (sphereCircleHomeomorph p hr) x).trans
          (Circle.fundamentalGroupMulEquiv _)) :=
  (rfl)

/-- The loop `t ↦ p + r·exp(2πit)` going once counterclockwise around the circle `sphere p r`,
based at `p + r`. It is the image of `Circle.expLoop` under the parametrization of the circle by
`Circle`. -/
def _root_.Complex.sphereLoop (p : ℂ) (hr : 0 < r) :
    Path ((sphereCircleHomeomorph p hr).symm 1) ((sphereCircleHomeomorph p hr).symm 1) :=
  Circle.expLoop.map (sphereCircleHomeomorph p hr).symm.continuous

@[simp]
theorem _root_.Complex.coe_sphereLoop_apply (p : ℂ) (hr : 0 < r) (t : unitInterval) :
    (p.sphereLoop hr t : ℂ) = circleMap p r (2 * Real.pi * t) := by
  simp [Complex.sphereLoop, circleMap, mul_comm]

/-- **The counterclockwise circle generates the fundamental group of a punctured star-convex
set.** Under `StarConvex.fundamentalGroupMulEquivInt`, the class in `V \ {p}` of the loop going
once counterclockwise around `sphere p r` is `ofAdd 1`. -/
theorem _root_.StarConvex.fundamentalGroupMulEquivInt_sphereLoop (hV : StarConvex ℝ p V)
    (hr : 0 < r) (hS : sphere p r ⊆ V) :
    hV.fundamentalGroupMulEquivInt hr hS _
      (FundamentalGroup.map (hV.sphereHomotopyEquiv hr hS).toFun _
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (p.sphereLoop hr)))) =
      Multiplicative.ofAdd 1 := by
  rw [StarConvex.fundamentalGroupMulEquivInt_def, MulEquiv.trans_apply,
    ← StarConvex.sphereFundamentalGroupMulEquiv_apply, MulEquiv.symm_apply_apply,
    MulEquiv.trans_apply, TauCeti.FundamentalGroup.homeomorphMulEquiv_apply,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  -- Transported to `Circle`, the loop is `Circle.expLoop`, up to the basepoint equation
  -- `sphereCircleHomeomorph p hr ((sphereCircleHomeomorph p hr).symm 1) = 1`.
  have key : ∀ (y : Circle) (hy : y = 1) (γ : Path y y), (∀ t, γ t = Circle.expLoop t) →
      Circle.fundamentalGroupMulEquiv y
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) = Multiplicative.ofAdd 1 := by
    rintro y rfl γ hγ
    obtain rfl : γ = Circle.expLoop := Path.ext (funext hγ)
    exact Circle.fundamentalGroupMulEquiv_expLoop
  exact key _ ((sphereCircleHomeomorph p hr).apply_symm_apply 1) _ fun t => by
    simp [Complex.sphereLoop]

/-- A punctured star-convex subset of `ℂ` containing a circle about the puncture is not simply
connected. -/
theorem _root_.StarConvex.not_simplyConnectedSpace_diff_singleton (hV : StarConvex ℝ p V)
    (hr : 0 < r) (hS : sphere p r ⊆ V) : ¬ SimplyConnectedSpace ↥(V \ {p}) :=
  let x : sphere p r := (sphereCircleHomeomorph p hr).symm 1
  haveI := (hV.fundamentalGroupMulEquivInt hr hS x).toEquiv.nontrivial
  not_simplyConnectedSpace_of_nontrivial_fundamentalGroup (hV.sphereHomotopyEquiv hr hS x)

/-- The direction `(z - p) / ‖z - p‖` of a point `z` of `V \ {p}` seen from `p`, as a point of the
unit circle. -/
def _root_.Complex.directionFrom (p : ℂ) (V : Set ℂ) : C(↥(V \ {p}), Circle) where
  toFun z := ⟨((z : ℂ) - p) / ‖(z : ℂ) - p‖, by
    have hz : (z : ℂ) - p ≠ 0 := sub_ne_zero.2 z.2.2
    simp [Submonoid.unitSphere, hz]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk (Continuous.div (by fun_prop) (by fun_prop) fun z => ?_) _
    simpa [sub_eq_zero] using z.2.2

@[simp]
theorem _root_.Complex.coe_directionFrom_apply (p : ℂ) (V : Set ℂ) (z : ↥(V \ {p})) :
    (p.directionFrom V z : ℂ) = ((z : ℂ) - p) / ‖(z : ℂ) - p‖ :=
  (rfl)

/-- **The direction map of a punctured star-convex set is bijective on fundamental groups.** If
`V` is star-convex about `p` and contains a circle about `p`, then `z ↦ (z - p) / ‖z - p‖` induces
a bijection `π₁(V \ {p}, z) → π₁(Circle, (z - p) / ‖z - p‖)` at every point `z`, not only on the
circle. It is the forward map of the homotopy equivalence `StarConvex.sphereHomotopyEquiv`, inverted
and followed by the parametrization of the circle by `Circle`. -/
theorem _root_.StarConvex.fundamentalGroup_map_directionFrom_bijective (hV : StarConvex ℝ p V)
    (hr : 0 < r) (hS : sphere p r ⊆ V) (z : ↥(V \ {p})) :
    Function.Bijective (FundamentalGroup.map (p.directionFrom V) z) := by
  have h : ((hV.sphereHomotopyEquiv hr hS).symm.trans
      (sphereCircleHomeomorph p hr).toHomotopyEquiv).toFun = p.directionFrom V := by
    ext z
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    simp
    field_simp
  rw [← h]
  exact ContinuousMap.HomotopyEquiv.fundamentalGroup_map_bijective _ z

/-- A punctured star-convex subset of `ℂ` containing a circle about the puncture is path
connected, being homotopy equivalent to the circle. -/
theorem _root_.StarConvex.pathConnectedSpace_diff_singleton (hV : StarConvex ℝ p V) (hr : 0 < r)
    (hS : sphere p r ⊆ V) : PathConnectedSpace ↥(V \ {p}) :=
  ((hV.sphereHomotopyEquiv hr hS).symm.trans
    (sphereCircleHomeomorph p hr).toHomotopyEquiv).symm.pathConnectedSpace

/-- Rotating a point of a punctured ball about its centre stays in the punctured ball. -/
private theorem add_mul_exp_mem_ball_diff_singleton {z : ℂ} (hz : z ∈ ball p R \ {p})
    (θ : ℝ) : p + (z - p) * Complex.exp (θ * Complex.I) ∈ ball p R \ {p} := by
  have hzp : z - p ≠ 0 := sub_ne_zero.2 hz.2
  refine ⟨?_, ?_⟩
  · simpa [mem_ball, dist_eq_norm, Complex.norm_exp_ofReal_mul_I] using hz.1
  · simp [hzp, Complex.exp_ne_zero]

/-- The loop `t ↦ p + (z - p) e^{2πit}` based at `z`, going once counterclockwise around `p` along
the circle through `z`, in the punctured ball `ball p R \ {p}`. -/
def _root_.Complex.loopAround (p : ℂ) (z : ↥(ball p R \ {p})) : Path z z where
  toFun t := ⟨p + (z - p) * Complex.exp (↑(2 * Real.pi * t) * Complex.I),
    add_mul_exp_mem_ball_diff_singleton z.2 _⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  source' := by ext; simp
  target' := by ext; simp

@[simp]
theorem _root_.Complex.coe_loopAround_apply (p : ℂ) (z : ↥(ball p R \ {p})) (t : unitInterval) :
    (p.loopAround z t : ℂ) = p + (z - p) * Complex.exp (↑(2 * Real.pi * t) * Complex.I) :=
  (rfl)

end Complex

section Product

variable {U : Type*} [TopologicalSpace U] [SimplyConnectedSpace U] {V : Set ℂ} {p : ℂ} {r R : ℝ}

/-- **Loops in a simply connected space times a punctured star-convex set are detected by the
direction of their second coordinate.** If `U` is simply connected and `V` is star-convex about `p`
and contains a circle about `p`, then `(u, z) ↦ (z - p) / ‖z - p‖` induces a bijection of
fundamental groups at every point of `U × (V \ {p})`. -/
theorem _root_.StarConvex.fundamentalGroup_map_directionFrom_comp_snd_bijective
    (hV : StarConvex ℝ p V) (hr : 0 < r) (hS : sphere p r ⊆ V) (a : U × ↥(V \ {p})) :
    Function.Bijective
      (FundamentalGroup.map ((p.directionFrom V).comp ContinuousMap.snd) a) := by
  obtain ⟨u, z⟩ := a
  have : Unique (FundamentalGroup U u) := uniqueOfSubsingleton 1
  -- the first factor of `π₁(U × (V \ {p})) ≃* π₁(U) × π₁(V \ {p})` is trivial
  have hsnd : Function.Bijective
      (FundamentalGroup.map (ContinuousMap.snd : C(U × ↥(V \ {p}), _)) (u, z)) :=
    (Equiv.uniqueProd _ _).bijective.comp (FundamentalGroup.prodMulEquiv u z).bijective
  have hcomp : ⇑(FundamentalGroup.map ((p.directionFrom V).comp ContinuousMap.snd) (u, z)) =
      FundamentalGroup.map (p.directionFrom V) z ∘ FundamentalGroup.map ContinuousMap.snd (u, z) :=
    funext fun γ => FundamentalGroupoid.map_comp_map _ _ γ
  rw [hcomp]
  exact (hV.fundamentalGroup_map_directionFrom_bijective hr hS z).comp hsnd

/-- **The fundamental group of a simply connected space times a punctured disc is generated by the
loop around the puncture.** For simply connected `U`, the class of
`t ↦ (u, p + (z - p) e^{2πit})` generates `π₁(U × (ball p R \ {p}), (u, z))`. Its direction has
degree one, and the degree of the direction identifies the group with `ℤ`
(`StarConvex.fundamentalGroup_map_directionFrom_comp_snd_bijective`). -/
theorem zpowers_loopAround_eq_top (u : U) (z : ↥(ball p R \ {p})) :
    Subgroup.zpowers (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((Path.refl u).prod (p.loopAround z)))) = ⊤ := by
  have hR : 0 < R := (norm_nonneg _).trans_lt (mem_ball_iff_norm.1 z.2.1)
  let d := (p.directionFrom (ball p R)).comp (ContinuousMap.snd : C(U × ↥(ball p R \ {p}), _))
  -- the degree of the direction, a bijective homomorphism to `ℤ`
  let W := (Circle.fundamentalGroupMulEquiv _).toMonoidHom.comp (FundamentalGroup.map d (u, z))
  have hW : Function.Bijective W := (Circle.fundamentalGroupMulEquiv _).bijective.comp
    (((convex_ball p R).starConvex
      (mem_ball_self hR)).fundamentalGroup_map_directionFrom_comp_snd_bijective (half_pos hR)
      (sphere_subset_ball (half_lt_self hR)) (u, z))
  set γ := FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk ((Path.refl u).prod (p.loopAround z)))
  have hγ : W γ = Multiplicative.ofAdd 1 := by
    refine (Circle.fundamentalGroupMulEquiv_fromPath _).trans (congrArg _ ?_)
    refine Circle.degree_eq_of_sub_eq _
      (θ := fun t => Complex.arg (p.directionFrom (ball p R) z) + 2 * Real.pi * t)
      (by fun_prop) (fun t => ?_) (by simp)
    ext
    rw [Circle.exp_add, Circle.coe_mul, Circle.exp_arg]
    simp [d, Complex.norm_exp, div_mul_eq_mul_div]
  refine eq_top_iff.2 fun g _ => ⟨Multiplicative.toAdd (W g), hW.1 ?_⟩
  rw [map_zpow, hγ, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]

end Product

end TauCeti
