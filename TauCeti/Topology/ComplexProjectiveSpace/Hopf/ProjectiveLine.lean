/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.Circle.Loop
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
public import TauCeti.Topology.Homotopy.GenLoop.Homeomorph
public import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
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
`[v]`. Its projection `(s, t) ↦ [G(s, t)]` lies in the line `P(span(v, w))` and sends the boundary
of the square to `[v]`. In the affine coordinate of the line centred at `[w]` it is
`κ / √(1 - |κ|²)`, which carries the open disc homeomorphically onto `ℂ`; this is why it
represents the projective line, although the results below use only its Hopf boundary. Read as a
loop of loops, this projection is the double loop
`TauCeti.ComplexProjectiveSpace.projectiveLineDoubleLoop`.

The Hopf boundary of its class is computed from the lift alone: `G` is a boundary lift in the
sense of `TauCeti.TopCat.IsBoundaryLift`, whose end `e^{2πit} v` is the counterclockwise loop of
the fibre. So the Hopf boundary of the class of the projective line is the class of
`Circle.expLoop`, the loop `t ↦ e^{2πit}` that `Circle.fundamentalGroupMulEquiv` sends to the
generator `1` of `ℤ`
(`TauCeti.ComplexProjectiveSpace.hopfBoundary_congrEquiv_fromDoubleLoop_projectiveLineDoubleLoop`).
This fixes the sign of the generator. As the boundary is an isomorphism `π₂(CPⁿ) ≅ π₁(S¹)`,
the class of the projective line generates `π₂(CPⁿ, [v])`
(`TauCeti.ComplexProjectiveSpace.zpowers_fromDoubleLoop_projectiveLineDoubleLoop_eq_top`).

The map `j : S¹ → Ω CPⁿ` adjoint to the projective line
(`TauCeti.ComplexProjectiveSpace.projectiveLineLoopMap`) is the double loop read as a map from the
circle, `e^{2πis} ↦ (t ↦ [G(s, t)])`. It sends `1` to the constant loop and is bijective on
fundamental groups (`TauCeti.ComplexProjectiveSpace.bijective_mapOfEq_projectiveLineLoopMap`): the
composite `π₁(S¹) → π₁(Ω CPⁿ) ≅ π₂(CPⁿ) → π₁(S¹)` through the loop-space shift and the Hopf
boundary is the identity on `Circle.expLoop`. This is the degree-one condition under which the
based Hopf product `S¹ × Ω S²ⁿ⁺¹ → Ω CPⁿ`, `(z, γ) ↦ j z · [γ]`, is a weak homotopy equivalence.

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
* `TauCeti.ComplexProjectiveSpace.zpowers_fromDoubleLoop_projectiveLineDoubleLoop_eq_top`: the
  projective-line class generates `π₂(CPⁿ, [v])`.
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

/-! ### The chord parametrization of the disc -/

/-- The point `(1 - s) + s e^{2πit}` of the closed unit disc, on the chord from `1` to
`e^{2πit}`. -/
private def chord (s t : I) : ℂ :=
  ((1 - (s : ℝ) : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (Circle.exp (2 * π * t) : ℂ)

private theorem continuous_chord : Continuous fun p : I × I ↦ chord p.1 p.2 := by
  unfold chord
  fun_prop

@[simp]
private theorem chord_zero_left (t : I) : chord 0 t = 1 := by
  simp [chord]

@[simp]
private theorem chord_one_left (t : I) : chord 1 t = Circle.exp (2 * π * t) := by
  simp [chord]

@[simp]
private theorem chord_zero_right (s : I) : chord s 0 = 1 := by
  simp [chord]

@[simp]
private theorem chord_one_right (s : I) : chord s 1 = 1 := by
  simp [chord]

/-- The chord lies in the closed unit disc, as a convex combination of `1` and `e^{2πit}`. -/
private theorem norm_chord_le (s t : I) : ‖chord s t‖ ≤ 1 := by
  have h₁ : 0 ≤ 1 - (s : ℝ) := sub_nonneg.2 s.2.2
  calc ‖chord s t‖
      ≤ ‖((1 - (s : ℝ) : ℝ) : ℂ)‖ + ‖((s : ℝ) : ℂ) * (Circle.exp (2 * π * t) : ℂ)‖ :=
        norm_add_le _ _
    _ = (1 - s) + s := by
        simp [-Complex.ofReal_sub, -Circle.coe_exp, abs_of_nonneg h₁, abs_of_nonneg s.2.1]
    _ = 1 := by ring

/-! ### The Hopf lift of the projective line -/

/-- The vector `κ v + √(1 - |κ|²) w` of the Hopf lift, for the chord point `κ = κ(s, t)`. -/
private def liftVector (v w : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) (s t : I) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  chord s t • (v : EuclideanSpace ℂ (Fin (n + 1))) +
    ((√(1 - ‖chord s t‖ ^ 2) : ℝ) : ℂ) • (w : EuclideanSpace ℂ (Fin (n + 1)))

private theorem liftVector_mem_sphere (hvw : ⟪(v : EuclideanSpace ℂ (Fin (n + 1))), w⟫ = 0)
    (s t : I) : liftVector v w s t ∈ sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 := by
  have h₁ : 0 ≤ 1 - ‖chord s t‖ ^ 2 := by
    nlinarith [norm_chord_le s t, norm_nonneg (chord s t)]
  -- Pythagoras for the orthogonal vectors `κ v` and `√(1 - |κ|²) w`.
  have h : ‖liftVector v w s t‖ ^ 2 = 1 := by
    have h₂ := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
      (chord s t • (v : EuclideanSpace ℂ (Fin (n + 1))))
      (((√(1 - ‖chord s t‖ ^ 2) : ℝ) : ℂ) • (w : EuclideanSpace ℂ (Fin (n + 1))))
      (by rw [inner_smul_left, inner_smul_right, hvw, mul_zero, mul_zero])
    rw [liftVector, sq, h₂]
    simp [norm_smul, Real.mul_self_sqrt h₁]
    ring
  rw [mem_sphere_zero_iff_norm]
  nlinarith [norm_nonneg (liftVector v w s t)]

variable (v w) in
/-- The **Hopf lift of the projective line** through `[v]` and `[w]`: the map
`(s, t) ↦ κ v + √(1 - |κ|²) w` from the square to the unit sphere, where
`κ = (1 - s) + s e^{2πit}`. It is `v` on the face `s = 0` and on the sides `t = 0`, `t = 1`, and
`e^{2πit} v` on the face `s = 1`; its projection to `CPⁿ` is the projective line through `[v]` and
`[w]`, with the boundary of the square collapsed to `[v]`. -/
def projectiveLineLift (hvw : ⟪(v : EuclideanSpace ℂ (Fin (n + 1))), w⟫ = 0) :
    C(I × I, sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) where
  toFun p := ⟨liftVector v w p.1 p.2, liftVector_mem_sphere hvw p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    unfold liftVector
    have := continuous_chord
    fun_prop

variable (hvw : ⟪(v : EuclideanSpace ℂ (Fin (n + 1))), w⟫ = 0)

/-- The Hopf lift at `(s, t)` is `κ v + √(1 - |κ|²) w`, for `κ = (1 - s) + s e^{2πit}`. -/
theorem coe_projectiveLineLift_apply (s t : I) :
    (projectiveLineLift v w hvw (s, t) : EuclideanSpace ℂ (Fin (n + 1))) =
      (((1 - (s : ℝ) : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (Circle.exp (2 * π * t) : ℂ)) •
          (v : EuclideanSpace ℂ (Fin (n + 1))) +
        ((√(1 - ‖((1 - (s : ℝ) : ℝ) : ℂ) + ((s : ℝ) : ℂ) * (Circle.exp (2 * π * t) : ℂ)‖ ^ 2)
          : ℝ) : ℂ) • (w : EuclideanSpace ℂ (Fin (n + 1))) :=
  (rfl)

/-- The value of the Hopf lift at a point where the chord is a unit complex number `u` is
`u v`. -/
private theorem coe_projectiveLineLift_of_chord_eq {s t : I} {u : ℂ} (hu : ‖u‖ = 1)
    (h : chord s t = u) :
    (projectiveLineLift v w hvw (s, t) : EuclideanSpace ℂ (Fin (n + 1))) =
      u • (v : EuclideanSpace ℂ (Fin (n + 1))) := by
  simp only [projectiveLineLift, ContinuousMap.coe_mk, liftVector, h, hu]
  simp

@[simp]
theorem projectiveLineLift_zero_left (t : I) : projectiveLineLift v w hvw (0, t) = v :=
  Subtype.ext ((coe_projectiveLineLift_of_chord_eq hvw norm_one (chord_zero_left t)).trans
    (one_smul _ _))

@[simp]
theorem projectiveLineLift_zero_right (s : I) : projectiveLineLift v w hvw (s, 0) = v :=
  Subtype.ext ((coe_projectiveLineLift_of_chord_eq hvw norm_one (chord_zero_right s)).trans
    (one_smul _ _))

@[simp]
theorem projectiveLineLift_one_right (s : I) : projectiveLineLift v w hvw (s, 1) = v :=
  Subtype.ext ((coe_projectiveLineLift_of_chord_eq hvw norm_one (chord_one_right s)).trans
    (one_smul _ _))

/-- On the face `s = 1` the Hopf lift runs once around the Hopf fibre over `[v]`:
`G(1, t) = e^{2πit} v`. -/
@[simp]
theorem projectiveLineLift_one_left (t : I) :
    projectiveLineLift v w hvw (1, t) = Circle.homeomorphSphere (Circle.exp (2 * π * t)) • v :=
  Subtype.ext <|
    (coe_projectiveLineLift_of_chord_eq hvw (Circle.norm_coe _) (chord_one_left t)).trans
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
    have h : finSuccEquiv 1 1 = some 0 := rfl
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

/-! ### Generation and the adjoint map -/

variable (v w) in
/-- The map `j : S¹ → Ω CPⁿ` **adjoint to the projective line**: the double loop
`projectiveLineDoubleLoop` read as a map from the circle, so that `e^{2πis}` goes to the loop
`t ↦ [G(s, t)]`. -/
def projectiveLineLoopMap : C(Circle, Ω (ComplexProjectiveSpace n) (mk n v)) :=
  (projectiveLineDoubleLoop v w hvw).toCircle

@[simp]
theorem projectiveLineLoopMap_one : projectiveLineLoopMap v w hvw 1 = Path.refl (mk n v) :=
  Path.toCircle_one _

theorem projectiveLineLoopMap_exp (s : I) :
    projectiveLineLoopMap v w hvw (Circle.exp (2 * π * s)) = projectiveLineDoubleLoop v w hvw s :=
  Path.toCircle_exp _ s

/-- `j` sends the class of the counterclockwise loop to the class of the double loop. -/
private theorem mapOfEq_projectiveLineLoopMap_expLoop :
    FundamentalGroup.mapOfEq (projectiveLineLoopMap v w hvw) (projectiveLineLoopMap_one hvw)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk Circle.expLoop)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (projectiveLineDoubleLoop v w hvw)) :=
  Circle.mapOfEq_toCircle_expLoop _

/-- The loop-space shift of `j_*` sends the generator of `π₁(S¹)` to the class of the
projective-line double loop in `π₂(CPⁿ)`. -/
private theorem fundamentalGroupLoopSpaceMulEquiv_mapOfEq_projectiveLineLoopMap_ofAdd_one :
    HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv
        (FundamentalGroup.mapOfEq (projectiveLineLoopMap v w hvw) (projectiveLineLoopMap_one hvw)
          ((Circle.fundamentalGroupMulEquiv 1).symm (Multiplicative.ofAdd 1))) =
      (⟦GenLoop.fromDoubleLoop (projectiveLineDoubleLoop v w hvw)⟧ :
        π_ 2 (ComplexProjectiveSpace n) (mk n v)) := by
  -- The final `rfl` of `rw` identifies the two sides, the same class typed once as an element of
  -- `π_ 2` and once as an element of the underlying quotient.
  rw [(Circle.fundamentalGroupMulEquiv 1).symm_apply_eq.2
      Circle.fundamentalGroupMulEquiv_expLoop.symm,
    mapOfEq_projectiveLineLoopMap_expLoop,
    HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv_fromPath_mk]

/-- **The adjoint map `j : S¹ → Ω CPⁿ` has degree one**: it induces a bijection
`π₁(S¹, 1) → π₁(Ω CPⁿ, refl)`. Composed with the loop-space shift `π₁(Ω CPⁿ) ≅ π₂(CPⁿ)` and the
Hopf boundary `π₂(CPⁿ) ≅ π₁(S¹)`, it sends the counterclockwise loop to the counterclockwise
loop. -/
theorem bijective_mapOfEq_projectiveLineLoopMap :
    Function.Bijective (FundamentalGroup.mapOfEq (projectiveLineLoopMap v w hvw)
      (projectiveLineLoopMap_one hvw)) := by
  -- Two orthogonal unit vectors exist only in `ℂⁿ⁺¹` with `n ≥ 1`, where the Hopf boundary
  -- `π₂(CPⁿ) → π₁(S¹)` is an isomorphism.
  have hN : Nat.card (Fin 1) < 2 * n := by
    have h := (linearIndependent_of_ne_zero_of_inner_eq_zero (𝕜 := ℂ)
      (v := ![(v : EuclideanSpace ℂ (Fin (n + 1))), w])
      (by simp [Fin.forall_fin_two, ne_zero_of_mem_unit_sphere])
      (fun i j hij ↦ by
        fin_cases i <;> fin_cases j <;> simp_all [inner_eq_zero_symm])).fintype_card_le_finrank
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, finrank_euclideanSpace_fin] at h ⊢
    omega
  -- The loop-space shift followed by the Hopf boundary, `π₁(Ω CPⁿ) ≃* π₁(S¹)`.
  let Φ := HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv.trans
    ((HomotopyGroup.congrMulEquiv (finSuccEquiv 1)).trans (hopfBoundaryMulEquiv v hN))
  -- The identification of the fundamental group of `Circle` with the first homotopy group of the
  -- unit sphere of `ℂ`, the target of the Hopf boundary.
  let Ψ : FundamentalGroup Circle 1 ≃* HomotopyGroup (Fin 1) (sphere (0 : ℂ) 1) 1 :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
      (HomotopyGroup.homeomorphMulEquivOfEq Circle.homeomorphSphere Circle.homeomorphSphere_one)
  let F := Circle.fundamentalGroupMulEquiv 1
  -- Both `Φ ∘ j_*` and `Ψ` send the counterclockwise loop to the counterclockwise loop, and this
  -- loop generates `π₁(S¹)`.
  have key :
      (Φ.toMonoidHom.comp (FundamentalGroup.mapOfEq _ (projectiveLineLoopMap_one hvw))).comp
        F.symm.toMonoidHom = Ψ.toMonoidHom.comp F.symm.toMonoidHom := by
    refine MonoidHom.ext_mint ?_
    have hΦ : Φ (FundamentalGroup.mapOfEq _ (projectiveLineLoopMap_one hvw)
        (F.symm (Multiplicative.ofAdd 1))) =
          ⟦GenLoop.map ⟨Circle.homeomorphSphere, Circle.homeomorphSphere.continuous⟩
            Circle.homeomorphSphere_one ((genLoopEquivOfUnique (Fin 1)).symm Circle.expLoop)⟧ := by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, HomotopyGroup.congrMulEquiv_apply,
        hopfBoundaryMulEquiv_apply,
        fundamentalGroupLoopSpaceMulEquiv_mapOfEq_projectiveLineLoopMap_ofAdd_one]
      exact hopfBoundary_congrEquiv_fromDoubleLoop_projectiveLineDoubleLoop hvw
    have hΨ : Ψ (F.symm (Multiplicative.ofAdd 1)) =
        ⟦GenLoop.map ⟨Circle.homeomorphSphere, Circle.homeomorphSphere.continuous⟩
          Circle.homeomorphSphere_one ((genLoopEquivOfUnique (Fin 1)).symm Circle.expLoop)⟧ := by
      rw [F.symm_apply_eq.2 Circle.fundamentalGroupMulEquiv_expLoop.symm]
      -- Mathlib's `pi1MulEquivFundamentalGroup.symm` sends the class of a loop to the class of the
      -- corresponding one-dimensional generalized loop by definition, and
      -- `homeomorphMulEquivOfEq` is `HomotopyGroup.map`.
      exact HomotopyGroup.map_mk _ _ _
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact hΦ.trans hΨ.symm
  have hj : ⇑(FundamentalGroup.mapOfEq (projectiveLineLoopMap v w hvw)
      (projectiveLineLoopMap_one hvw)) = Φ.symm ∘ Ψ := by
    funext x
    rw [Function.comp_apply, Φ.eq_symm_apply, ← F.symm_apply_apply x]
    exact DFunLike.congr_fun key (F x)
  rw [hj]
  exact Φ.symm.bijective.comp Ψ.bijective

/-- **The projective line generates `π₂(CPⁿ)`.** The class of the projective-line double loop,
read as a square, generates `π₂(CPⁿ, [v]) ≅ ℤ`. -/
theorem zpowers_fromDoubleLoop_projectiveLineDoubleLoop_eq_top :
    Subgroup.zpowers (G := π_ 2 (ComplexProjectiveSpace n) (mk n v))
      ⟦GenLoop.fromDoubleLoop (projectiveLineDoubleLoop v w hvw)⟧ = ⊤ := by
  let e : Multiplicative ℤ ≃* π_ 2 (ComplexProjectiveSpace n) (mk n v) :=
    (Circle.fundamentalGroupMulEquiv 1).symm.trans
      ((MulEquiv.ofBijective _ (bijective_mapOfEq_projectiveLineLoopMap hvw)).trans
        HomotopyGroup.fundamentalGroupLoopSpaceMulEquiv)
  exact e.symm.zpowers_eq_top_of_apply_eq_ofAdd_one (e.symm_apply_eq.2
    (fundamentalGroupLoopSpaceMulEquiv_mapOfEq_projectiveLineLoopMap_ofAdd_one hvw).symm)

end TauCeti.ComplexProjectiveSpace
