/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Analysis.InnerProductSpace.Euclidean.Space
public import TauCeti.Topology.Circle.Loop
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
public import TauCeti.Topology.Homotopy.GenLoop.Homeomorph
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.Analysis.InnerProductSpace.Hemisphere
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The projective-line generator of `π₂(CPⁿ)`

Let `v` and `w` be orthogonal unit vectors of `ℂⁿ⁺¹`; such vectors exist only for `n ≥ 1`. They
span a complex projective line through `[v]` in `CPⁿ`, and this file writes down an explicit
representative of its class in `π₂(CPⁿ, [v])`, computes its image under the boundary map of the
Hopf fibration `S¹ → S²ⁿ⁺¹ → CPⁿ`, and reads it as a map `j : S¹ → Ω CPⁿ`.

For `s, t ∈ I` put `κ(s, t) = (1 - s) + s e^{2πit}`, the point at parameter `s` on the chord of the
closed unit disc from `1` to `e^{2πit}`. On the open square, `κ` is injective onto the open disc,
and it carries the face `s = 0` and the sides `t = 0`, `t = 1` to `1`, while the face `s = 1` runs
once counterclockwise around the unit circle. The **Hopf lift of the projective line**
(`TauCeti.ComplexProjectiveSpace.projectiveLineLift`) is the map

`G(s, t) = κ(s, t) v + √(1 - |κ(s, t)|²) w`

from the square to the unit sphere `S²ⁿ⁺¹`. It is `v` on the face `s = 0` and on the sides
`t = 0`, `t = 1`, and it is `e^{2πit} v` on the face `s = 1`, which lies in the Hopf fibre over
`[v]`. It is built as `κ v`, a point of the closed unit ball orthogonal to `w`, lifted to the
hemisphere around `w` by `TauCeti.hemisphereHomeomorph`; `κ` is the affine segment
`AffineMap.lineMap 1 e^{2πit} s`. Its projection `(s, t) ↦ [G(s, t)]` lies in the line
`P(span(v, w))` and sends the boundary of the square to `[v]`. In the affine coordinate of the
line centred at `[w]` it is `κ / √(1 - |κ|²)`, which carries the open disc homeomorphically onto
`ℂ`; this is why it represents the projective line, although the results below use only its Hopf
boundary. Read as a loop of loops, this projection is the double loop
`TauCeti.ComplexProjectiveSpace.projectiveLineDoubleLoop`.

The Hopf boundary of its class is computed from the lift alone: `G` is a boundary lift in the
sense of `TauCeti.TopCat.IsBoundaryLift`, whose end `e^{2πit} v` is the counterclockwise loop of
the fibre. So the Hopf boundary of the class of the projective line is the class of
`Circle.expLoop`, the loop `t ↦ e^{2πit}` that `Circle.fundamentalGroupMulEquiv` sends to the
generator `1` of `ℤ`
(`TauCeti.ComplexProjectiveSpace.hopfBoundary_congrEquiv_fromDoubleLoop_projectiveLineDoubleLoop`).
This fixes the sign of the generator: the identification `π₂(CPⁿ, [v]) ≃* ℤ` of
`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt` sends the class of the projective line to `1`
(`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_fromDoubleLoop_projectiveLineDoubleLoop`), so it
generates `π₂(CPⁿ, [v])`
(`TauCeti.ComplexProjectiveSpace.zpowers_fromDoubleLoop_projectiveLineDoubleLoop_eq_top`).

The map `j : S¹ → Ω CPⁿ` adjoint to the projective line
(`TauCeti.ComplexProjectiveSpace.projectiveLineLoopMap`) is the double loop read as a map from the
circle, `e^{2πis} ↦ (t ↦ [G(s, t)])`. It sends `1` to the constant loop and has degree one:
followed by the loop-space shift `π₁(Ω CPⁿ) ≅ π₂(CPⁿ)` and `pi2MulEquivInt`, the map `j_*` on
fundamental groups is the degree `π₁(S¹, 1) ≃* ℤ` of `Circle.fundamentalGroupMulEquiv`
(`pi2MulEquivInt_fundamentalGroupLoopSpaceMulEquiv_mapOfEq_projectiveLineLoopMap`).
In particular `j_*` is bijective
(`TauCeti.ComplexProjectiveSpace.bijective_mapOfEq_projectiveLineLoopMap`), a statement that does
not see the sign. Bijectivity on `π₁` is the hypothesis of
`TauCeti.ComplexProjectiveSpace.isWeakHomotopyEquivalence_hopfProduct`, the weak equivalence of the
based Hopf product `S¹ × Ω S²ⁿ⁺¹ → Ω CPⁿ`, `(z, γ) ↦ j z · [γ]`. That theorem takes `j` with values
in the Moore loop space `TauCeti.MooreLoopSpace`, so `j` applies there only after it is transferred
from the fixed-interval loops used here to Moore loops, which this file does not do.

Loops are taken on the fixed interval, `Ω X x = Path x x`. The square of the double loop is
indexed by `Fin 2`, its first coordinate being the loop parameter `s`; the boundary map of the Hopf
fibration uses the cube `I^(Option (Fin 1))` with the lifting direction `none`, and the two are
compared by `finSuccEquiv 1`, which sends `0` to `none`.

## Main definitions

* `TauCeti.ComplexProjectiveSpace.projectiveLineLift`: the Hopf lift `G` of the projective line.
* `TauCeti.ComplexProjectiveSpace.projectiveLineDoubleLoop`: the double loop
  `s ↦ (t ↦ [G(s, t)])` at `[v]`.
* `TauCeti.ComplexProjectiveSpace.projectiveLineLoopMap`: the adjoint map `j : S¹ → Ω CPⁿ`.

## Main results

* `TauCeti.ComplexProjectiveSpace.hopfBoundary_congrEquiv_fromDoubleLoop_projectiveLineDoubleLoop`:
  the Hopf boundary of the projective-line class is the class of the counterclockwise loop.
* `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_fromDoubleLoop_projectiveLineDoubleLoop`: the
  projective-line class has degree `1` in `π₂(CPⁿ, [v]) ≃* ℤ`.
* `TauCeti.ComplexProjectiveSpace.zpowers_fromDoubleLoop_projectiveLineDoubleLoop_eq_top`: the
  projective-line class generates `π₂(CPⁿ, [v])`.
* `pi2MulEquivInt_fundamentalGroupLoopSpaceMulEquiv_mapOfEq_projectiveLineLoopMap`:
  `j_*`, read in the integer coordinates of `π₁(S¹)` and `π₂(CPⁿ)`, is the identity of `ℤ`.
* `TauCeti.ComplexProjectiveSpace.bijective_mapOfEq_projectiveLineLoopMap`: `j` induces a
  bijection `π₁(S¹, 1) → π₁(Ω CPⁿ, refl)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Example 4.45 (the Hopf fibration and `π₂(CPⁿ) ≅ ℤ`).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4 (the loop spaces of `CPⁿ` and the
  classes of Proposition 6.38).
-/

public section

noncomputable section

open Metric Set unitInterval
open scoped ComplexInnerProductSpace Real Topology Topology.Homotopy

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} {v w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1}

/-! ### The Hopf lift of the projective line -/

/-- The vector `κ v` for the chord point `κ = κ(s, t)`, a point of the closed unit ball of the
real orthogonal complement of `w`. -/
private def chordVector (hvw : ⟪(v : EuclideanSpace ℂ (Fin (n + 1))), w⟫ = 0) (p : I × I) :
    closedBall (0 : (ℝ ∙ (w : EuclideanSpace ℂ (Fin (n + 1))))ᗮ) 1 :=
  ⟨⟨AffineMap.lineMap (1 : ℂ) (Circle.exp (2 * π * p.2) : ℂ) (p.1 : ℝ) •
      (v : EuclideanSpace ℂ (Fin (n + 1))),
    Submodule.mem_orthogonal_singleton_iff_inner_left.2 <| by
      rw [EuclideanSpace.real_inner_eq_re_inner, inner_smul_left, hvw, mul_zero,
        Complex.zero_re]⟩,
    -- The chord lies in the closed unit disc, as a convex combination of `1` and `e^{2πit}`.
    mem_closedBall_zero_iff.2 <| by
      simpa [norm_smul] using (convex_closedBall (0 : ℂ) 1).lineMap_mem (by simp)
        (mem_closedBall_zero_iff.2 (Circle.norm_coe (Circle.exp (2 * π * p.2))).le) p.1.property⟩

variable (hvw : ⟪(v : EuclideanSpace ℂ (Fin (n + 1))), w⟫ = 0)

private theorem continuous_chordVector : Continuous (chordVector hvw) := by
  refine Continuous.subtype_mk (Continuous.subtype_mk ?_ _) _
  fun_prop

variable (v w) in
/-- The **Hopf lift of the projective line** through `[v]` and `[w]`: the map
`(s, t) ↦ κ v + √(1 - |κ|²) w` from the square to the unit sphere, where
`κ = (1 - s) + s e^{2πit}`. It is `v` on the face `s = 0` and on the sides `t = 0`, `t = 1`, and
`e^{2πit} v` on the face `s = 1`; its projection to `CPⁿ` is the projective line through `[v]` and
`[w]`, with the boundary of the square collapsed to `[v]`. It is `κ v` lifted to the hemisphere
around `w` by `TauCeti.hemisphereHomeomorph`. -/
def projectiveLineLift : C(I × I, sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) where
  toFun p := (hemisphereHomeomorph w).symm (chordVector hvw p)
  continuous_toFun := continuous_subtypeVal.comp
    ((hemisphereHomeomorph w).symm.continuous.comp (continuous_chordVector hvw))

/-- The Hopf lift at `(s, t)` is `κ v + √(1 - |κ|²) w`, with the chord point `κ` written as
`AffineMap.lineMap 1 e^{2πit} s`. -/
private theorem coe_projectiveLineLift_apply_lineMap (s t : I) :
    (projectiveLineLift v w hvw (s, t) : EuclideanSpace ℂ (Fin (n + 1))) =
      AffineMap.lineMap (1 : ℂ) (Circle.exp (2 * π * t) : ℂ) (s : ℝ) •
          (v : EuclideanSpace ℂ (Fin (n + 1))) +
        ((√(1 - ‖AffineMap.lineMap (1 : ℂ) (Circle.exp (2 * π * t) : ℂ) (s : ℝ)‖ ^ 2) : ℝ) : ℂ) •
          (w : EuclideanSpace ℂ (Fin (n + 1))) := by
  simp only [projectiveLineLift, ContinuousMap.coe_mk, coe_hemisphereHomeomorph_symm_apply,
    chordVector, ← Submodule.norm_coe, norm_smul, norm_eq_of_mem_sphere, mul_one,
    Complex.coe_smul]

/-- The Hopf lift at `(s, t)` is `κ v + √(1 - |κ|²) w`, for `κ = (1 - s) + s e^{2πit}`. -/
theorem coe_projectiveLineLift_apply (s t : I) :
    (projectiveLineLift v w hvw (s, t) : EuclideanSpace ℂ (Fin (n + 1))) =
      (((1 - (s : ℝ) : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (Circle.exp (2 * π * t) : ℂ)) •
          (v : EuclideanSpace ℂ (Fin (n + 1))) +
        ((√(1 - ‖((1 - (s : ℝ) : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (Circle.exp (2 * π * t) : ℂ)‖ ^ 2)
          : ℝ) : ℂ) • (w : EuclideanSpace ℂ (Fin (n + 1))) := by
  simp only [coe_projectiveLineLift_apply_lineMap, AffineMap.lineMap_apply_module,
    Complex.real_smul, mul_one]

/-- The value of the Hopf lift at a point where the chord is a unit complex number `u` is
`u v`. -/
private theorem coe_projectiveLineLift_of_lineMap_eq {s t : I} {u : ℂ} (hu : ‖u‖ = 1)
    (h : AffineMap.lineMap (1 : ℂ) (Circle.exp (2 * π * t) : ℂ) (s : ℝ) = u) :
    (projectiveLineLift v w hvw (s, t) : EuclideanSpace ℂ (Fin (n + 1))) =
      u • (v : EuclideanSpace ℂ (Fin (n + 1))) := by
  rw [coe_projectiveLineLift_apply_lineMap, h, hu, one_pow, sub_self, Real.sqrt_zero,
    Complex.ofReal_zero, zero_smul, add_zero]

@[simp]
theorem projectiveLineLift_zero_left (t : I) : projectiveLineLift v w hvw (0, t) = v :=
  Subtype.ext ((coe_projectiveLineLift_of_lineMap_eq hvw norm_one
    (by rw [Icc.coe_zero, AffineMap.lineMap_apply_zero])).trans (one_smul _ _))

@[simp]
theorem projectiveLineLift_zero_right (s : I) : projectiveLineLift v w hvw (s, 0) = v :=
  Subtype.ext ((coe_projectiveLineLift_of_lineMap_eq hvw norm_one
    (by simp)).trans (one_smul _ _))

@[simp]
theorem projectiveLineLift_one_right (s : I) : projectiveLineLift v w hvw (s, 1) = v :=
  Subtype.ext ((coe_projectiveLineLift_of_lineMap_eq hvw norm_one
    (by simp)).trans (one_smul _ _))

/-- On the face `s = 1` the Hopf lift runs once around the Hopf fibre over `[v]`:
`G(1, t) = e^{2πit} v`. -/
@[simp]
theorem projectiveLineLift_one_left (t : I) :
    projectiveLineLift v w hvw (1, t) = Circle.homeomorphSphere (Circle.exp (2 * π * t)) • v :=
  Subtype.ext <|
    (coe_projectiveLineLift_of_lineMap_eq hvw (Circle.norm_coe _)
      (by rw [Icc.coe_one, AffineMap.lineMap_apply_one])).trans
      (by rw [Sphere.coe_sphere_smul, Circle.coe_homeomorphSphere_apply])

/-! ### The double loop -/

variable (v w) in
/-- The **projective line as a double loop** at `[v]` in `CPⁿ`: the loop
`s ↦ (t ↦ [G(s, t)])` of loops, where `G` is the Hopf lift `projectiveLineLift`. -/
def projectiveLineDoubleLoop :
    Ω (Ω (ComplexProjectiveSpace n) (mk n v)) (Path.refl (mk n v)) where
  toFun s :=
    { toFun t := mk n (projectiveLineLift v w hvw (s, t))
      continuous_toFun := (continuous_mk n).comp ((projectiveLineLift v w hvw).continuous.comp
        (continuous_const.prodMk continuous_id))
      source' := by rw [projectiveLineLift_zero_right]
      target' := by rw [projectiveLineLift_one_right] }
  continuous_toFun := Path.continuous_uncurry_iff.1 <|
    (continuous_mk n).comp (projectiveLineLift v w hvw).continuous
  source' := by
    ext t
    simp
  target' := by
    ext t
    simp [projectiveLineLift_one_left, mk_smul]

@[simp]
theorem projectiveLineDoubleLoop_apply (s t : I) :
    projectiveLineDoubleLoop v w hvw s t = mk n (projectiveLineLift v w hvw (s, t)) :=
  (rfl)

/-! ### The Hopf boundary of the projective line -/

/-- The Hopf lift, as a boundary lift of the projective-line square indexed by
`I^(Option (Fin 1))`. -/
private theorem isBoundaryLift_projectiveLineLift :
    TopCat.IsBoundaryLift (hopfHom n) (b := mk n v) ⟨v, rfl⟩
      (GenLoop.congr _ (finSuccEquiv 1)
        (GenLoop.fromDoubleLoop (projectiveLineDoubleLoop v w hvw)))
      ((projectiveLineLift v w hvw).comp
        ⟨fun y : I × (Fin 1 → I) ↦ (y.1, y.2 0), by fun_prop⟩) where
  proj_apply y := by
    have h : finSuccEquiv 1 1 = some 0 := by rw [← Fin.succ_zero_eq_one, finSuccEquiv_succ]
    simp [GenLoop.congr_apply, h, piOptionEquivProdHomeomorph_symm_apply_some, -mk_eq_mk_iff]
  apply_zero t := projectiveLineLift_zero_left hvw _
  apply_of_mem_boundary s t ht := by
    obtain ⟨i, hi | hi⟩ := ht <;> obtain rfl : i = 0 := Subsingleton.elim _ _ <;>
      simp [hi]

/-- **The Hopf boundary of the projective line is the counterclockwise loop.** The boundary map
`π₂(CPⁿ, [v]) → π₁(S¹, 1)` of the Hopf fibration sends the class of the projective-line double
loop to the class of `Circle.expLoop`, `t ↦ e^{2πit}`, carried to the unit sphere of `ℂ`. The
square of the double loop is reindexed by `finSuccEquiv 1`, so that its loop parameter becomes the
lifting direction of the boundary map. -/
theorem hopfBoundary_congrEquiv_fromDoubleLoop_projectiveLineDoubleLoop :
    hopfBoundary v (Fin 1) (HomotopyGroup.congrEquiv (finSuccEquiv 1)
        ⟦GenLoop.fromDoubleLoop (projectiveLineDoubleLoop v w hvw)⟧) =
      ⟦GenLoop.map ⟨Circle.homeomorphSphere, Circle.homeomorphSphere.continuous⟩
        Circle.homeomorphSphere_one ((genLoopEquivOfUnique (Fin 1)).symm Circle.expLoop)⟧ := by
  rw [hopfBoundary_apply, HomotopyGroup.congrEquiv_mk,
    TopCat.fibrationBoundary_mk _ (isBoundaryLift_projectiveLineLift hvw)]
  refine (HomotopyGroup.map_mk _ _ _).trans (congrArg _ (GenLoop.ext _ _ fun t ↦ ?_))
  simp only [GenLoop.map_apply, ContinuousMap.coe_mk, Homeomorph.symm_apply_eq]
  refine Subtype.ext (Subtype.ext ?_)
  rw [coe_hopfFiberHomeomorph_apply, TopCat.IsBoundaryLift.endLoop_apply_coe,
    GenLoop.genLoopEquivOfUnique_symm_apply, Circle.expLoop_apply]
  exact congrArg Subtype.val (projectiveLineLift_one_left hvw (t 0))

/-! ### The degree of the projective line -/

/-- **The projective line has degree one.** The identification `π₂(CPⁿ, [v]) ≃* ℤ` of
`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`, through the Hopf boundary and the degree of loops
of the circle, sends the class of the projective-line double loop to the generator `1`. -/
theorem pi2MulEquivInt_fromDoubleLoop_projectiveLineDoubleLoop :
    pi2MulEquivInt v (ne_zero_of_inner_eq_zero_euclideanSpace (ne_zero_of_mem_unit_sphere v)
        (ne_zero_of_mem_unit_sphere w) hvw)
        ⟦GenLoop.fromDoubleLoop (projectiveLineDoubleLoop v w hvw)⟧ =
      Multiplicative.ofAdd 1 := by
  refine (pi2MulEquivInt_apply v _ _).trans ?_
  rw [hopfBoundary_congrEquiv_fromDoubleLoop_projectiveLineDoubleLoop, ← HomotopyGroup.map_mk]
  -- The Hopf boundary lands in the unit sphere of `ℂ`; carried back to the circle, it is the class
  -- of the counterclockwise loop.
  refine (congrArg (fun a ↦ Circle.fundamentalGroupMulEquiv 1
    (HomotopyGroup.pi1MulEquivFundamentalGroup a))
      (HomotopyGroup.map_map_of_comp_eq_id _ _ _ _ (by ext; simp) _)).trans ?_
  rw [← HomotopyGroup.pi1MulEquivFundamentalGroup_symm_fromPath_mk, MulEquiv.apply_symm_apply,
    Circle.fundamentalGroupMulEquiv_expLoop]

/-- **The projective line generates `π₂(CPⁿ)`.** The class of the projective-line double loop,
read as a square, generates `π₂(CPⁿ, [v]) ≅ ℤ`. -/
theorem zpowers_fromDoubleLoop_projectiveLineDoubleLoop_eq_top :
    Subgroup.zpowers (G := π_ 2 (ComplexProjectiveSpace n) (mk n v))
      ⟦GenLoop.fromDoubleLoop (projectiveLineDoubleLoop v w hvw)⟧ = ⊤ :=
  MulEquiv.zpowers_eq_top_of_apply_eq_ofAdd_one _
    (pi2MulEquivInt_fromDoubleLoop_projectiveLineDoubleLoop hvw)

/-! ### The adjoint map -/

variable (v w) in
/-- The map `j : S¹ → Ω CPⁿ` **adjoint to the projective line**: the double loop
`projectiveLineDoubleLoop` read as a map from the circle, so that `e^{2πis}` goes to the loop
`t ↦ [G(s, t)]`. -/
def projectiveLineLoopMap : C(Circle, Ω (ComplexProjectiveSpace n) (mk n v)) :=
  (projectiveLineDoubleLoop v w hvw).toCircle

/-- `j` is the projective-line double loop read as a map from the circle by `Path.toCircle`. -/
theorem projectiveLineLoopMap_def :
    projectiveLineLoopMap v w hvw = (projectiveLineDoubleLoop v w hvw).toCircle :=
  (rfl)

@[simp]
theorem projectiveLineLoopMap_one : projectiveLineLoopMap v w hvw 1 = Path.refl (mk n v) :=
  Path.toCircle_one _

@[simp]
theorem projectiveLineLoopMap_unitToCircle (s : I) :
    projectiveLineLoopMap v w hvw (TauCeti.unitToCircle s) = projectiveLineDoubleLoop v w hvw s :=
  Path.toCircle_unitToCircle _ s

theorem projectiveLineLoopMap_exp (s : I) :
    projectiveLineLoopMap v w hvw (Circle.exp (2 * π * s)) = projectiveLineDoubleLoop v w hvw s :=
  Path.toCircle_exp _ s

/-- The projective-line double loop, as a class of `π₁(Ω CPⁿ)`, has degree one in `ℤ`. -/
private theorem pi2MulEquivInt_fundamentalGroupLoopSpaceMulEquiv_fromPath_projectiveLineDoubleLoop :
    (HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv.trans (pi2MulEquivInt v
        (ne_zero_of_inner_eq_zero_euclideanSpace (ne_zero_of_mem_unit_sphere v)
          (ne_zero_of_mem_unit_sphere w) hvw)))
        (FundamentalGroup.fromPath (.mk (projectiveLineDoubleLoop v w hvw))) =
      Multiplicative.ofAdd 1 := by
  rw [MulEquiv.trans_apply, HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_fromPath_mk,
    pi2MulEquivInt_fromDoubleLoop_projectiveLineDoubleLoop]

/-- **The adjoint map `j : S¹ → Ω CPⁿ` has degree one.** Composed with the loop-space shift
`π₁(Ω CPⁿ) ≅ π₂(CPⁿ)` and the identification `π₂(CPⁿ) ≃* ℤ` of
`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`, the map `j_*` on fundamental groups is the degree
`π₁(S¹, 1) ≃* ℤ` of `Circle.fundamentalGroupMulEquiv`. -/
theorem pi2MulEquivInt_fundamentalGroupLoopSpaceMulEquiv_mapOfEq_projectiveLineLoopMap
    (δ : FundamentalGroup Circle 1) :
    pi2MulEquivInt v (ne_zero_of_inner_eq_zero_euclideanSpace (ne_zero_of_mem_unit_sphere v)
        (ne_zero_of_mem_unit_sphere w) hvw) (HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv
        (FundamentalGroup.mapOfEq (projectiveLineLoopMap v w hvw)
          (projectiveLineLoopMap_one hvw) δ)) =
      Circle.fundamentalGroupMulEquiv 1 δ :=
  Circle.apply_mapOfEq_toCircle_of_apply_eq_ofAdd_one _ _
    (pi2MulEquivInt_fundamentalGroupLoopSpaceMulEquiv_fromPath_projectiveLineDoubleLoop hvw) δ

/-- **The adjoint map `j : S¹ → Ω CPⁿ` is bijective on fundamental groups**: it induces a
bijection `π₁(S¹, 1) → π₁(Ω CPⁿ, refl)`. Bijectivity does not see the sign of `j`, which is
fixed by the degree computation
`pi2MulEquivInt_fundamentalGroupLoopSpaceMulEquiv_mapOfEq_projectiveLineLoopMap`. -/
theorem bijective_mapOfEq_projectiveLineLoopMap :
    Function.Bijective (FundamentalGroup.mapOfEq (projectiveLineLoopMap v w hvw)
      (projectiveLineLoopMap_one hvw)) :=
  Circle.bijective_mapOfEq_toCircle_of_apply_eq_ofAdd_one _ _
    (pi2MulEquivInt_fundamentalGroupLoopSpaceMulEquiv_fromPath_projectiveLineDoubleLoop hvw)

end TauCeti.ComplexProjectiveSpace
