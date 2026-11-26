/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Clutching
public import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact
import TauCeti.Analysis.Normed.Module.Normalize
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Topology.Circle.Degree.Square

/-!
# The coordinate line generates `π₂(CPⁿ⁺¹)`

The boundary map of the Hopf fibration `S¹ → S²ⁿ⁺³ → CPⁿ⁺¹` identifies `π₂(CPⁿ⁺¹)` with
`π₁(S¹) ≅ ℤ` (`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`). This file evaluates that
identification on the coordinate line `[1 : z : 0 : ⋯ : 0]`, read as a sphere through the standard
sphere of the Riemann sphere (`TauCeti.ComplexProjectiveSpace.lineSquare`) and based at `[e₁]`
(`TauCeti.ComplexProjectiveSpace.lineClass`): its value is `1`
(`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_lineClass`). So the generator of `π₂(CPⁿ⁺¹)`
is the class of a projective line with its complex orientation
(`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_symm_ofAdd_one`), the line class `L` of the
quantum relation `x^(n+2) = q^L` and of the period group of `CPⁿ⁺¹`.

**The lift.** At a point of the square with sup-radius `r` (`TauCeti.cubeRadius`) and offset `c`
from the centre (`TauCeti.squareCenterOffset`), the line is `[1 : z]` with `z = 2 c / √(1 - r²)`.
It is the class of the unit vector `u`, the normalization of `(√(1 - r²), 2 c, 0, …, 0)`, which is
continuous on the closed square and equals `(c / |c|) e₁` on its boundary. The boundary map is read
off a lift that starts at `e₁` and stays there over the boundary of the cube
(`TauCeti.TopCat.fibrationBoundary_mk`). So `u` is rotated by the phase
`λ = exp (-i χ (arg (-c) + π))`, where the weight `χ` is `1` on the bottom, top and left edges of
the square and `0` on the segment from the centre to the midpoint of the right edge, the cut of
`arg (-c)`. The phase is continuous on the whole square, and `λ c / |c| = 1` on those three edges,
so `λ u` is a boundary lift. Its end is the loop `t ↦ λ(1, t) c / |c|` of the fibre circle over
`[e₁]`, read along the right edge.

**The degree.** Since `λ` is continuous on the whole square, `λ c / |c|` has the degree of the
direction `c / |c|` from the centre around the boundary of the square
(`TauCeti.squareBoundaryDegree_mul_of_continuous`), which is one
(`TauCeti.squareBoundaryDegree_squareCenterDirection`). Being constant on three edges, it turns
once along the right edge (`TauCeti.squareBoundaryDegree_mul_two_pi_eq_of_edges`), and that is
the degree of the end loop.

**Base points.** The line is based at `affineParam 1 0`, and `pi2MulEquivInt` at the class
`mk (n + 1) e₁` of the unit vector `e₁ = affineUnitVector 1 0`. These points are equal
(`TauCeti.ComplexProjectiveSpace.affineParam_def`), and the class of the line is carried from one
to the other by `HomotopyGroup.map` of the identity (`TauCeti.ComplexProjectiveSpace.lineClass`).

## Main results

* `TauCeti.ComplexProjectiveSpace.lineClass`: the class of the coordinate line in `π₂(CPⁿ⁺¹)`
  at the base point `[e₁]`.
* `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_lineClass`: the coordinate line is sent to
  `1` by `π₂(CPⁿ⁺¹) ≃* ℤ`.
* `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt_symm_ofAdd_one`: the generator of `π₂(CPⁿ⁺¹)`
  is the class of the coordinate line.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Theorem 4.41 (the exact homotopy sequence of a fibration) and Example 4.45 (the Hopf
  fibration and `π₂(CPⁿ) ≅ ℤ`).
-/

public section

noncomputable section

open Metric unitInterval

namespace TauCeti.ComplexProjectiveSpace

/-! ### A phase on the square -/

/-- The weight `χ = min 1 (2 |t - 1/2| + max 0 (1 - 2 s))` at a point `(s, t)` of the square: it
is `1` on the bottom, top and left edges, and `0` on the segment from the centre to the midpoint of
the right edge. -/
private def squarePhaseWeight (y : Fin 2 → I) : ℝ :=
  min 1 (2 * |(y 1 : ℝ) - 1 / 2| + max 0 (1 - 2 * (y 0 : ℝ)))

private theorem continuous_squarePhaseWeight : Continuous squarePhaseWeight := by
  unfold squarePhaseWeight
  fun_prop

private theorem squarePhaseWeight_nonneg (y : Fin 2 → I) : 0 ≤ squarePhaseWeight y :=
  le_min zero_le_one (add_nonneg (by positivity) (le_max_left _ _))

/-- The weight vanishes where the offset from the centre is a nonnegative real number. -/
private theorem squarePhaseWeight_eq_zero {y : Fin 2 → I}
    (hy : -squareCenterOffset y ∉ Complex.slitPlane) : squarePhaseWeight y = 0 := by
  rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_not] at hy
  simp only [Complex.neg_re, Complex.neg_im, re_squareCenterOffset, im_squareCenterOffset,
    neg_eq_zero, neg_nonpos, sub_nonneg, sub_eq_zero] at hy
  obtain ⟨h0, h1⟩ := hy
  rw [squarePhaseWeight, h1, sub_self, abs_zero, mul_zero, zero_add,
    max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

/-- The bottom, top and left edges of the square. -/
private def IsPhaseEdge (y : Fin 2 → I) : Prop :=
  y 0 = 0 ∨ y 1 = 0 ∨ y 1 = 1

private theorem IsPhaseEdge.mem_boundary {y : Fin 2 → I} (hy : IsPhaseEdge y) :
    y ∈ Cube.boundary (Fin 2) := by
  rcases hy with h | h | h
  exacts [⟨0, .inl h⟩, ⟨1, .inl h⟩, ⟨1, .inr h⟩]

private theorem squarePhaseWeight_eq_one {y : Fin 2 → I} (hy : IsPhaseEdge y) :
    squarePhaseWeight y = 1 := by
  refine min_eq_left ?_
  rcases hy with h | h | h <;> simp only [h, Set.Icc.coe_zero, Set.Icc.coe_one]
  · rw [mul_zero, sub_zero, max_eq_right zero_le_one]
    linarith [abs_nonneg ((y 1 : ℝ) - 1 / 2)]
  · rw [show |(0 : ℝ) - 1 / 2| = 1 / 2 by norm_num [abs_of_neg]]
    linarith [le_max_left (0 : ℝ) (1 - 2 * (y 0 : ℝ))]
  · rw [show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num [abs_of_pos]]
    linarith [le_max_left (0 : ℝ) (1 - 2 * (y 0 : ℝ))]

/-- The angle `χ (arg (-c) + π)` of the phase, for the offset `c` from the centre. -/
private def squarePhaseAngle (y : Fin 2 → I) : ℝ :=
  squarePhaseWeight y * (Complex.arg (-squareCenterOffset y) + Real.pi)

private theorem continuous_squarePhaseAngle : Continuous squarePhaseAngle := by
  refine continuous_iff_continuousAt.2 fun y ↦ ?_
  by_cases hy : -squareCenterOffset y ∈ Complex.slitPlane
  · exact continuous_squarePhaseWeight.continuousAt.mul
      (((Complex.continuousAt_arg hy).comp (f := fun z ↦ -squareCenterOffset z)
        (by fun_prop)).add continuousAt_const)
  · -- The weight vanishes at `y`, and the second factor is bounded by `2π`.
    have h0 : squarePhaseAngle y = 0 := by
      rw [squarePhaseAngle, squarePhaseWeight_eq_zero hy, zero_mul]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (a := fun z ↦ 2 * Real.pi * squarePhaseWeight z) (fun z ↦ ?_) ?_
    · rw [squarePhaseAngle, norm_mul, Real.norm_of_nonneg (squarePhaseWeight_nonneg z),
        mul_comm (2 * Real.pi)]
      refine mul_le_mul_of_nonneg_left ?_ (squarePhaseWeight_nonneg z)
      rw [Real.norm_of_nonneg (by linarith [Complex.neg_pi_lt_arg (-squareCenterOffset z)])]
      linarith [Complex.arg_le_pi (-squareCenterOffset z)]
    · simpa [squarePhaseWeight_eq_zero hy] using
        (continuous_squarePhaseWeight.tendsto y).const_mul (2 * Real.pi)

/-- The phase `exp (-i χ (arg (-c) + π))`, a circle-valued map continuous on the whole square. -/
private def squarePhase (y : Fin 2 → I) : Circle :=
  Circle.exp (-squarePhaseAngle y)

private theorem continuous_squarePhase : Continuous squarePhase :=
  (map_continuous Circle.exp).comp continuous_squarePhaseAngle.neg

/-- The direction from the centre, twisted by the phase. -/
private def squareTwist : (Fin 2 → I) → Circle :=
  squareCenterDirection * squarePhase

/-- On the bottom, top and left edges the twisted direction is `1`. -/
private theorem squareTwist_eq_one {y : Fin 2 → I} (hy : IsPhaseEdge y) : squareTwist y = 1 := by
  have hc := squareCenterOffset_ne_zero_of_mem hy.mem_boundary
  -- The direction `c / ‖c‖` is `exp (i (arg (-c) + π))`.
  have key : squareCenterDirection y =
      Circle.exp (Complex.arg (-squareCenterOffset y) + Real.pi) := by
    refine Circle.ext ?_
    simp [coe_squareCenterDirection hc, Complex.exp_arg_mul_I (neg_ne_zero.2 hc)]
    ring
  rw [squareTwist, Pi.mul_apply, squarePhase, squarePhaseAngle, squarePhaseWeight_eq_one hy,
    one_mul, key, ← Circle.exp_add, add_neg_cancel, Circle.exp_zero]

/-- The twisted direction turns once around the circle along the boundary of the square. -/
private theorem squareBoundaryDegree_squareTwist : squareBoundaryDegree squareTwist = 1 := by
  rw [squareTwist, squareBoundaryDegree_mul_of_continuous continuous_squarePhase,
    squareBoundaryDegree_squareCenterDirection]

/-! ### A lift of the coordinate line to the sphere -/

variable (n : ℕ)

/-- The vector `(√(1 - r²), 2 c, 0, …, 0)` of `ℂⁿ⁺²` at a point of the square with sup-radius `r`
and offset `c` from the centre. -/
private def lineLiftVector (y : Fin 2 → I) : EuclideanSpace ℂ (Fin (n + 2)) :=
  ((√(1 - cubeRadius y ^ 2) : ℝ) : ℂ) • EuclideanSpace.single 0 1 +
    (2 * squareCenterOffset y) • EuclideanSpace.single 1 1

private theorem continuous_lineLiftVector : Continuous (lineLiftVector n) := by
  have := continuous_cubeRadius (N := Fin 2)
  unfold lineLiftVector
  fun_prop

private theorem lineLiftVector_apply_zero (y : Fin 2 → I) :
    lineLiftVector n y 0 = ((√(1 - cubeRadius y ^ 2) : ℝ) : ℂ) := by
  simp [lineLiftVector]

private theorem lineLiftVector_apply_one (y : Fin 2 → I) :
    lineLiftVector n y 1 = 2 * squareCenterOffset y := by
  simp [lineLiftVector]

private theorem lineLiftVector_ne_zero (y : Fin 2 → I) : lineLiftVector n y ≠ 0 := by
  intro h
  have h0 := lineLiftVector_apply_zero n y
  have h1 := lineLiftVector_apply_one n y
  rw [h] at h0 h1
  simp only [PiLp.zero_apply, zero_eq_mul, OfNat.ofNat_ne_zero, false_or] at h0 h1
  have hr0 := cubeRadius_nonneg y
  have hr1 := cubeRadius_le_one y
  have hs : √(1 - cubeRadius y ^ 2) = 0 := by exact_mod_cast h0.symm
  rw [Real.sqrt_eq_zero'] at hs
  have hr : cubeRadius y = 1 := by nlinarith
  exact squareCenterOffset_ne_zero_of_mem ((cubeRadius_eq_one_iff y).1 hr) h1

/-- The normalization of `lineLiftVector`, a lift of the coordinate line to the unit sphere of
`ℂⁿ⁺²` (`mk_lineLiftUnit`). -/
private def lineLiftUnit : C(Fin 2 → I, sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) :=
  normalizeToSphere (lineLiftVector n) (continuous_lineLiftVector n) (lineLiftVector_ne_zero n)

/-- On the boundary of the square the lift is `c / ‖c‖ e₁`. -/
private theorem coe_lineLiftUnit_of_mem {y : Fin 2 → I} (hy : y ∈ Cube.boundary (Fin 2)) :
    (lineLiftUnit n y : EuclideanSpace ℂ (Fin (n + 2))) =
      (squareCenterDirection y : ℂ) • EuclideanSpace.single 1 1 := by
  have hc := squareCenterOffset_ne_zero_of_mem hy
  simp [lineLiftUnit, lineLiftVector, (cubeRadius_eq_one_iff y).2 hy, NormedSpace.normalize,
    norm_smul, ← Complex.coe_smul, smul_smul, coe_squareCenterDirection hc]
  field_simp

/-- Away from the boundary of the square the lift is the unit representative of
`[1 : z : 0 : ⋯ : 0]`, for `z = 2 c / √(1 - r²)`. -/
private theorem lineLiftUnit_of_notMem {y : Fin 2 → I} (hy : y ∉ Cube.boundary (Fin 2)) :
    lineLiftUnit n y = affineUnitVector 0
      (Pi.single 0 (2 * squareCenterOffset y / (√(1 - cubeRadius y ^ 2) : ℝ))) := by
  have hr : cubeRadius y < 1 :=
    (cubeRadius_le_one y).lt_of_ne fun h ↦ hy ((cubeRadius_eq_one_iff y).1 h)
  have ha : 0 < √(1 - cubeRadius y ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [cubeRadius_nonneg y])
  have hv : lineLiftVector n y = √(1 - cubeRadius y ^ 2) •
      affineVector 0 (Pi.single 0 (2 * squareCenterOffset y / (√(1 - cubeRadius y ^ 2) : ℝ))) := by
    ext i
    induction i using Fin.succAboveCases 0 with
    | x => simp [lineLiftVector]
    | p j =>
      rw [PiLp.smul_apply, affineVector_apply_succAbove]
      refine Fin.cases ?_ (fun k ↦ ?_) j
      · simp [lineLiftVector, mul_div_cancel₀ _ (Complex.ofReal_ne_zero.2 ha.ne')]
      · simp [lineLiftVector, Fin.ext_iff]
  refine Subtype.ext ?_
  rw [lineLiftUnit, coe_normalizeToSphere_apply, hv, NormedSpace.normalize_smul_of_pos ha,
    coe_affineUnitVector_apply, NormedSpace.normalize]

/-- **The lift covers the coordinate line**: `[lineLiftUnit y] = lineSquare n y`. -/
private theorem mk_lineLiftUnit (y : Fin 2 → I) :
    mk (n + 1) (lineLiftUnit n y) = lineSquare n y := by
  by_cases hy : y ∈ Cube.boundary (Fin 2)
  · rw [lineSquare_apply_of_mem hy, affineParam_def, mk_eq_mk_iff_exists_circle_smul]
    refine ⟨squareCenterDirection y, Subtype.ext ?_⟩
    rw [Circle.coe_smul_sphere, coe_lineLiftUnit_of_mem n hy, coe_affineUnitVector_zero]
  · rw [lineSquare_apply_of_notMem hy, affineParam_def, lineLiftUnit_of_notMem n hy]

/-! ### The class of the coordinate line -/

/-- The base point `affineParam 1 0` of the coordinate line is the base point `[e₁]` of
`TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`. -/
private theorem id_affineParam_one_zero :
    ContinuousMap.id (ComplexProjectiveSpace (n + 1)) (affineParam 1 0) =
      mk (n + 1) (affineUnitVector 1 0) :=
  (ContinuousMap.id_apply _).trans (affineParam_def 1 0)

/-- The class of the coordinate line `lineSquare n` in `π₂(CPⁿ⁺¹)` at the base point
`[e₁] = mk (n + 1) (affineUnitVector 1 0)` of `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt`,
carried there by `HomotopyGroup.map` of the identity from its own base point `affineParam 1 0`,
which is the same point (`affineParam_def`). -/
def lineClass :
    HomotopyGroup (Fin 2) (ComplexProjectiveSpace (n + 1)) (mk (n + 1) (affineUnitVector 1 0)) :=
  HomotopyGroup.map (ContinuousMap.id _) (id_affineParam_one_zero n) ⟦lineSquare n⟧

/-- `lineClass n` is the class of `lineSquare n` carried to `[e₁]` by `HomotopyGroup.map` of the
identity. -/
theorem lineClass_def :
    lineClass n = HomotopyGroup.map (ContinuousMap.id _)
      ((ContinuousMap.id_apply _).trans (affineParam_def 1 0)) ⟦lineSquare n⟧ :=
  (rfl)

/-- The coordinate line carried to `[e₁]`, with its cube reindexed along `finSuccEquiv 1` so that
the homotopy parameter of the boundary map comes first. -/
private def lineGenLoop :
    GenLoop (Option (Fin 1)) (ComplexProjectiveSpace (n + 1)) (mk (n + 1) (affineUnitVector 1 0)) :=
  GenLoop.congr (mk (n + 1) (affineUnitVector 1 0)) (finSuccEquiv 1)
    (GenLoop.map (ContinuousMap.id _) (id_affineParam_one_zero n) (lineSquare n))

/-- Reindexing the cube along `finSuccEquiv 1` sends `lineClass n` to the class of
`lineGenLoop n`. -/
private theorem congrEquiv_lineClass :
    HomotopyGroup.congrEquiv (finSuccEquiv 1) (lineClass n) = ⟦lineGenLoop n⟧ := by
  rw [lineClass_def, HomotopyGroup.map_mk, HomotopyGroup.congrEquiv_mk, lineGenLoop]

/-! ### The boundary of the coordinate line -/

/-- The point `(s, t)` of the square for the homotopy parameter `s` and the cube point `t` of
`I^(Fin 1)`. -/
private def squarePoint (p : I × (Fin 1 → I)) : Fin 2 → I :=
  ![p.1, p.2 0]

private theorem continuous_squarePoint : Continuous squarePoint :=
  continuous_fst.matrixVecCons
    (((continuous_apply 0).comp continuous_snd).matrixVecCons continuous_const)

/-- Reindexing a point of `I^(Option (Fin 1))` along `finSuccEquiv 1` gives the point `(s, t)` of
the square. -/
private theorem comp_finSuccEquiv_piOptionEquivProdHomeomorph_symm (p : I × (Fin 1 → I)) :
    (fun m ↦ (piOptionEquivProdHomeomorph fun _ ↦ I).symm p (finSuccEquiv 1 m)) =
      squarePoint p := by
  funext m
  refine Fin.cases ?_ (fun j ↦ ?_) m
  · rw [finSuccEquiv_zero, piOptionEquivProdHomeomorph_symm_apply_none, squarePoint,
      Matrix.cons_val_zero]
  · rw [finSuccEquiv_succ, Subsingleton.elim j 0, piOptionEquivProdHomeomorph_symm_apply_some,
      squarePoint, Matrix.cons_val_succ, Matrix.cons_val_zero]

/-- **The lift of the coordinate line through the Hopf fibration**: the lift `lineLiftUnit`
rotated by the phase, so that it starts at `e₁` and stays there over the boundary of the cube. -/
private def lineLift :
    C(I × (Fin 1 → I), TopCat.of (sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1)) where
  toFun p := squarePhase (squarePoint p) • lineLiftUnit n (squarePoint p)
  continuous_toFun :=
    (continuous_squarePhase.comp continuous_squarePoint).smul
      ((lineLiftUnit n).continuous.comp continuous_squarePoint)

/-- The lift is the phase times `lineLiftUnit`, as vectors of `ℂⁿ⁺²`. -/
private theorem coe_lineLift_apply (p : I × (Fin 1 → I)) :
    ((lineLift n p : sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) :
        EuclideanSpace ℂ (Fin (n + 2))) =
      (squarePhase (squarePoint p) : ℂ) •
        (lineLiftUnit n (squarePoint p) : EuclideanSpace ℂ (Fin (n + 2))) :=
  (rfl)

/-- Over the boundary of the square the lift is the twisted direction times `e₁`. -/
private theorem coe_lineLift_of_mem {p : I × (Fin 1 → I)}
    (hp : squarePoint p ∈ Cube.boundary (Fin 2)) :
    ((lineLift n p : sphere (0 : EuclideanSpace ℂ (Fin (n + 2))) 1) :
        EuclideanSpace ℂ (Fin (n + 2))) =
      (squareTwist (squarePoint p) : ℂ) • EuclideanSpace.single 1 1 := by
  rw [coe_lineLift_apply, coe_lineLiftUnit_of_mem n hp, smul_smul, squareTwist, Pi.mul_apply,
    Circle.coe_mul, mul_comm]

/-- On the bottom, top and left edges the lift is the base point `e₁`. -/
private theorem lineLift_of_isPhaseEdge {p : I × (Fin 1 → I)} (hp : IsPhaseEdge (squarePoint p)) :
    lineLift n p = affineUnitVector 1 0 :=
  Subtype.ext <| by
    rw [coe_lineLift_of_mem n hp.mem_boundary, squareTwist_eq_one hp, Circle.coe_one, one_smul,
      coe_affineUnitVector_zero]

/-- `lineLift` is a boundary lift of the coordinate line, read in `I^(Option (Fin 1))`. -/
private theorem isBoundaryLift_lineLift :
    TopCat.IsBoundaryLift (hopfHom (n + 1)) ⟨affineUnitVector 1 0, rfl⟩
      (lineGenLoop n) (lineLift n) where
  proj_apply p := by
    rw [lineGenLoop, GenLoop.congr_apply, GenLoop.map_apply, ContinuousMap.id_apply,
      comp_finSuccEquiv_piOptionEquivProdHomeomorph_symm]
    exact (mk_circle_smul _ _ _).trans (mk_lineLiftUnit n _)
  apply_zero t := lineLift_of_isPhaseEdge n (.inl rfl)
  apply_of_mem_boundary s t ht := by
    obtain ⟨i, hi⟩ := ht
    rw [Subsingleton.elim i 0] at hi
    exact lineLift_of_isPhaseEdge n (.inr hi)

/-- The angle along the right edge `t ↦ (1, t)`. -/
private def rightEdgeAngle (t : I) : ℝ :=
  Complex.arg (squareCenterOffset ![1, t]) - squarePhaseAngle ![1, t]

private theorem continuous_rightEdgeAngle : Continuous rightEdgeAngle := by
  have hc : Continuous fun t : I ↦ (![1, t] : Fin 2 → I) :=
    continuous_const.matrixVecCons (continuous_id.matrixVecCons continuous_const)
  refine (continuous_iff_continuousAt.2 fun t ↦ ?_).sub (continuous_squarePhaseAngle.comp hc)
  refine (Complex.continuousAt_arg ?_).comp (f := fun t : I ↦ squareCenterOffset ![1, t])
    (continuous_squareCenterOffset.comp hc).continuousAt
  exact Complex.mem_slitPlane_iff.2 (.inl (by norm_num))

/-- `rightEdgeAngle` is an angle function of the twisted direction along the right edge. -/
private theorem exp_rightEdgeAngle (t : I) :
    Circle.exp (rightEdgeAngle t) = squareTwist ![1, t] := by
  have hc : squareCenterOffset ![1, t] ≠ 0 :=
    squareCenterOffset_ne_zero_of_mem ⟨0, .inr rfl⟩
  refine Circle.ext ?_
  simp [squareTwist, squarePhase, rightEdgeAngle, coe_squareCenterDirection hc,
    Complex.exp_arg_mul_I hc, div_eq_mul_inv]

/-- Along the right edge the angle increases by one full turn. -/
private theorem rightEdgeAngle_one_sub_rightEdgeAngle_zero :
    rightEdgeAngle 1 - rightEdgeAngle 0 = (1 : ℤ) * (2 * Real.pi) := by
  have h := squareBoundaryDegree_mul_two_pi_eq_of_edges (Γ := squareTwist) (c := 1)
    (continuousOn_squareCenterDirection.mul continuous_squarePhase.continuousOn)
    (fun s ↦ squareTwist_eq_one (.inr (.inl rfl))) (fun s ↦ squareTwist_eq_one (.inr (.inr rfl)))
    (fun t ↦ squareTwist_eq_one (.inl rfl)) (fun t ↦ rfl) continuous_rightEdgeAngle
    exp_rightEdgeAngle
  rw [← h, squareBoundaryDegree_squareTwist]

/-- The twisted direction along the right edge, a loop in the circle at `1`. -/
private def rightEdgeLoop : Path (1 : Circle) 1 where
  toFun t := squareTwist ![1, t]
  continuous_toFun :=
    ((map_continuous Circle.exp).comp continuous_rightEdgeAngle).congr exp_rightEdgeAngle
  source' := squareTwist_eq_one (.inr (.inl rfl))
  target' := squareTwist_eq_one (.inr (.inr rfl))

private theorem rightEdgeLoop_apply (t : I) : rightEdgeLoop t = squareTwist ![1, t] :=
  (rfl)

/-- The twisted direction turns once around the circle along the right edge. -/
private theorem degree_rightEdgeLoop : Circle.degree rightEdgeLoop = 1 :=
  Circle.degree_eq_of_sub_eq rightEdgeLoop continuous_rightEdgeAngle exp_rightEdgeAngle
    rightEdgeAngle_one_sub_rightEdgeAngle_zero

/-- **The boundary map of the Hopf fibration on the coordinate line**: it is the class of the loop
`rightEdgeLoop` of the fibre circle over `[e₁]`. -/
private theorem hopfBoundary_lineSquare :
    hopfBoundary (affineUnitVector 1 0) (Fin 1)
        (HomotopyGroup.congrEquiv (finSuccEquiv 1) (lineClass n)) =
      HomotopyGroup.map ⟨Circle.homeomorphSphere, Homeomorph.continuous _⟩ (by ext; simp)
        ⟦(genLoopEquivOfUnique (Fin 1)).symm rightEdgeLoop⟧ := by
  -- Reindexing the cube puts the homotopy parameter of `lineLift` first; the boundary is the
  -- class of the end of the boundary lift `lineLift`.
  refine (congrArg _ (congrEquiv_lineClass n)).trans <| (hopfBoundary_apply _ _).trans <|
    (congrArg _ (TopCat.fibrationBoundary_mk (mk_mem_serreFibrations (n + 1))
      (isBoundaryLift_lineLift n))).trans <|
    (HomotopyGroup.homeomorphEquivOfEq_apply _ _ _).trans <|
    (HomotopyGroup.map_mk _ _ _).trans <| Eq.trans ?_ (HomotopyGroup.map_mk _ _ _).symm
  refine congrArg _ (GenLoop.ext _ _ fun t ↦ ?_)
  rw [GenLoop.map_apply, GenLoop.map_apply]
  refine (hopfFiberHomeomorph _).symm_apply_eq.2 (Subtype.ext (Subtype.ext ?_))
  rw [TopCat.IsBoundaryLift.endLoop_apply_coe, coe_hopfFiberHomeomorph_apply,
    coe_lineLift_of_mem n (p := (1, t)) ⟨0, .inr rfl⟩, ContinuousMap.coe_mk,
    GenLoop.genLoopEquivOfUnique_symm_apply, rightEdgeLoop_apply, Sphere.coe_sphere_smul,
    Circle.coe_homeomorphSphere_apply, coe_affineUnitVector_zero, squarePoint,
    Subsingleton.elim (default : Fin 1) 0]

/-- **The coordinate line generates `π₂(CPⁿ⁺¹)`.** The isomorphism `π₂(CPⁿ⁺¹) ≃* ℤ` of the Hopf
fibration sends the class `lineClass n` of the coordinate line `[1 : z : 0 : ⋯ : 0]`, read as a
sphere through the standard sphere of the Riemann sphere, to `1`. -/
theorem pi2MulEquivInt_lineClass :
    pi2MulEquivInt (affineUnitVector 1 0) n.add_one_ne_zero (lineClass n) =
      Multiplicative.ofAdd 1 := by
  have h1 : Circle.homeomorphSphere (1 : Circle) = 1 := by ext; simp
  -- The circle reads the boundary loop as `rightEdgeLoop`, of degree one.
  have hc : HomotopyGroup.map ⟨Circle.homeomorphSphere.symm, Homeomorph.continuous _⟩
      (by ext; simp)
      (HomotopyGroup.map ⟨Circle.homeomorphSphere, Homeomorph.continuous _⟩ h1
        ⟦(genLoopEquivOfUnique (Fin 1)).symm rightEdgeLoop⟧) =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (FundamentalGroup.fromPath (.mk rightEdgeLoop)) := by
    rw [HomotopyGroup.pi1MulEquivFundamentalGroup_symm_fromPath_mk, HomotopyGroup.map_mk,
      HomotopyGroup.map_mk]
    refine congrArg _ (GenLoop.ext _ _ fun t ↦ ?_)
    rw [GenLoop.map_apply, GenLoop.map_apply]
    exact Circle.homeomorphSphere.symm_apply_apply _
  rw [pi2MulEquivInt_apply]
  refine (congrArg (fun a ↦ Circle.fundamentalGroupMulEquiv 1
    (HomotopyGroup.pi1MulEquivFundamentalGroup (HomotopyGroup.map _ _ a)))
    (hopfBoundary_lineSquare n)).trans ?_
  refine (congrArg (fun a ↦ Circle.fundamentalGroupMulEquiv 1
    (HomotopyGroup.pi1MulEquivFundamentalGroup a)) hc).trans ?_
  rw [MulEquiv.apply_symm_apply, Circle.fundamentalGroupMulEquiv_fromPath, degree_rightEdgeLoop]

/-- **The generator of `π₂(CPⁿ⁺¹)` is the coordinate line**: the element of `π₂(CPⁿ⁺¹)` sent to `1`
by `TauCeti.ComplexProjectiveSpace.pi2MulEquivInt` is the class `lineClass n` of `lineSquare n`,
carried to the base point `[e₁]` along `affineParam 1 0 = [e₁]`. -/
theorem pi2MulEquivInt_symm_ofAdd_one :
    (pi2MulEquivInt (affineUnitVector 1 0) n.add_one_ne_zero).symm (Multiplicative.ofAdd 1) =
      lineClass n :=
  (MulEquiv.symm_apply_eq _).2 (pi2MulEquivInt_lineClass n).symm

end TauCeti.ComplexProjectiveSpace
