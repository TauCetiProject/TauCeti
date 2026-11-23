/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Exact
public import TauCeti.Dynamics.Billiard.Smooth
public import TauCeti.Geometry.Symplectic.Liouville.Plane
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The billiard map is exact symplectic

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the strip `ℝ × (-1, 1)` (`TauCeti.StrictConvexBilliardTable.nextCollision`).
On the strip take the Liouville form `λ = v ds` (`Prod.realPlaneYDx`) and the area form
`ω = -dλ = ds ∧ dv`. This file proves that `B` is an exact symplectic map:

`B^*λ - λ = dℓ`,  hence  `B^*ω = ω`,

where `ℓ(s, v) = ‖χ(t) - χ(s)‖` is the length of the chord travelled from the state `(s, v)` to
the next collision (`TauCeti.StrictConvexBilliardTable.chordLength`).

The chord length is minus the generating function `S(s, t) = -‖χ(t) - χ(s)‖` evaluated at the
next collision parameter, `ℓ(s, v) = -S(s, t(s, v))`. The generating function recovers the
tangential components, `∂_s S(s, t) = v` and `∂_t S(s, t) = -w`, so differentiating gives
`dℓ = w dt - v ds` (`TauCeti.StrictConvexBilliardTable.hasFDerivAt_chordLength`), which is the
exactness identity. It is proved for `C²` parametrizations `χ`, which make `B` differentiable.
Applying `d` to it, `d(dℓ) = 0` and `d(B^*λ) = B^*(dλ)` give `B^*ω = ω`; this step is proved for
`C³` parametrizations, which make `B` and `ℓ` `C²`. Equivalently, the Jacobian determinant of
`B` is one at every state of the strip
(`TauCeti.StrictConvexBilliardTable.det_fderiv_nextCollision`).

The chord length is invariant under the deck translation `(s, v) ↦ (s + L, v)`
(`TauCeti.StrictConvexBilliardTable.chordLength_add_period`), like `λ` and `B`, so it is a function
on the space of collision states `AddCircle L × (-1, 1)`.

## Main definitions

* `TauCeti.StrictConvexBilliardTable.chordLength`: the length of the chord from a collision state
  to the next collision.

## Main results

* `TauCeti.StrictConvexBilliardTable.hasFDerivAt_chordLength`: `dℓ = w dt - v ds`.
* `TauCeti.StrictConvexBilliardTable.realPlaneYDx_compContinuousLinearMap_fderiv_nextCollision_sub`:
  `B^*λ - λ = dℓ`.
* `TauCeti.StrictConvexBilliardTable.wedge_compContinuousLinearMap_fderiv_nextCollision`:
  `B^*(ds ∧ dv) = ds ∧ dv`.
* `TauCeti.StrictConvexBilliardTable.det_fderiv_nextCollision`: the Jacobian determinant of `B`
  is one.

## References

* Ana Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 5.2 (the billiard map of a convex table).
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Module Prod
open scoped RealInnerProductSpace ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o) {n : WithTop ℕ∞}
  {x : ℝ × ℝ}

/-! ### The chord length -/

/-- The length `ℓ(s, v) = ‖χ(t) - χ(s)‖` of the chord from the collision state `(s, v)` to the next
collision point `χ(t)`, where `t` is the next collision parameter. It is the primitive of the
exact symplectic billiard map. Its values outside the strip `ℝ × (-1, 1)` carry no meaning. -/
def chordLength (x : ℝ × ℝ) : ℝ :=
  ‖χ (χ.nextParam x.1 x.2) - χ x.1‖

theorem chordLength_def (x : ℝ × ℝ) :
    χ.chordLength x = ‖χ (χ.nextParam x.1 x.2) - χ x.1‖ :=
  (rfl)

/-- The chord length is minus the generating function at the next collision parameter. -/
theorem chordLength_eq_neg_generatingFunction (x : ℝ × ℝ) :
    χ.chordLength x = -χ.generatingFunction x.1 (χ.nextParam x.1 x.2) := by
  rw [chordLength_def, generatingFunction_def, neg_neg]

/-- The chord of a state of the strip has positive length. -/
theorem chordLength_pos (hx : x.2 ∈ Ioo (-1) 1) : 0 < χ.chordLength x :=
  norm_pos_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hx))

/-- The chord length is invariant under the deck translation `(s, v) ↦ (s + L, v)`. -/
theorem chordLength_add_period (hx : x.2 ∈ Ioo (-1) 1) :
    χ.chordLength (x.1 + χ.period, x.2) = χ.chordLength x := by
  rw [chordLength_def, chordLength_def, χ.nextParam_add_period hx, χ.periodic, χ.periodic]

/-- **Smoothness of the chord length.** If `χ` is `C^(n+1)` with `n ≠ 0`, the chord length is `C^n`
on the strip `ℝ × (-1, 1)`. -/
theorem contDiffAt_chordLength (hn : n ≠ 0) (hχ : ContDiff ℝ (n + 1) χ)
    (hx : x.2 ∈ Ioo (-1) 1) : ContDiffAt ℝ n χ.chordLength x := by
  have hχn : ContDiff ℝ n χ := hχ.of_le le_self_add
  have hd : ContDiffAt ℝ n (fun y : ℝ × ℝ ↦ χ (χ.nextParam y.1 y.2) - χ y.1) x :=
    (hχn.contDiffAt.comp x (χ.contDiffAt_nextParam hn hχ.contDiffAt hχn.contDiffAt hx)).sub
      (hχn.contDiffAt.comp x contDiffAt_fst)
  exact (contDiffAt_norm ℝ (sub_ne_zero.2 (χ.apply_nextParam_ne hx))).comp x hd

/-! ### Exactness -/

/-- **The differential of the chord length** is `dℓ = w dt - v ds`, where `(t, w)` is the next
collision state of `(s, v)`: moving the initial point along the boundary shortens the chord at the
rate `v`, and moving the final point lengthens it at the rate `w`. Here `χ` is `C²`. -/
theorem hasFDerivAt_chordLength (hχ : ContDiff ℝ 2 χ) (hx : x.2 ∈ Ioo (-1) 1) :
    HasFDerivAt χ.chordLength
      ((χ.nextCollision x).2 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (fderiv ℝ χ.nextCollision x) -
        x.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) x := by
  set B' := fderiv ℝ χ.nextCollision x
  set t := χ.nextParam x.1 x.2
  have hB : HasFDerivAt χ.nextCollision B' x :=
    ((χ.contDiffAt_nextCollision one_ne_zero hχ.contDiffAt hχ.contDiffAt hx).differentiableAt
      one_ne_zero).hasFDerivAt
  -- The next collision parameter is the first component of `B`.
  have ht : HasFDerivAt (fun y : ℝ × ℝ ↦ χ.nextParam y.1 y.2)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp B') x := by
    simpa [Function.comp_def] using hasFDerivAt_fst.comp x hB
  have hd := ((χ.differentiableAt t).hasDerivAt.hasFDerivAt.comp x ht).sub
    ((χ.differentiableAt x.1).hasDerivAt.hasFDerivAt.comp x hasFDerivAt_fst)
  have hℓ := (hasFDerivAt_norm_of_ne (sub_ne_zero.2 (χ.apply_nextParam_ne hx))).comp x hd
  convert hℓ using 1
  · funext y
    simp [chordLength_def]
  -- The chord is `ℓ u` for the unit outgoing velocity `u`, which has tangential components `v` at
  -- the initial point and `w` at the final point.
  have hu : ‖χ (χ.nextParam x.1 x.2) - χ x.1‖⁻¹ • innerSL ℝ (χ (χ.nextParam x.1 x.2) - χ x.1) =
      innerSL ℝ (χ.outgoingDir x.1 x.2) := by
    nth_rw 2 [χ.sub_eq_norm_smul_outgoingDir hx]
    rw [map_smul, inv_smul_smul₀ (norm_ne_zero_iff.2 (sub_ne_zero.2 (χ.apply_nextParam_ne hx)))]
  rw [hu]
  refine ContinuousLinearMap.ext fun δ ↦ ?_
  simp [t, nextTangential_def, real_inner_comm (deriv χ x.1), mul_comm]

/-- **The billiard map is exact symplectic**: `B^*λ - λ = dℓ` at every state of the strip, for the
Liouville form `λ = v ds` and the chord length `ℓ`, for a `C²` parametrization `χ`. -/
theorem realPlaneYDx_compContinuousLinearMap_fderiv_nextCollision_sub (hχ : ContDiff ℝ 2 χ)
    (hx : x.2 ∈ Ioo (-1) 1) :
    (realPlaneYDx (χ.nextCollision x)).compContinuousLinearMap (fderiv ℝ χ.nextCollision x) -
        realPlaneYDx x =
      differentialOneForm ℝ χ.chordLength x := by
  ext v
  simp [differentialOneForm_apply, (χ.hasFDerivAt_chordLength hχ hx).fderiv]

/-! ### Area preservation -/

/-- **The billiard map preserves the area form**: `B^*(ds ∧ dv) = ds ∧ dv` at every state of the
strip. It follows from the exactness `B^*λ - λ = dℓ` by applying `d`, since `ds ∧ dv = -dλ`. The
hypothesis that `χ` is `C³` makes `B` and `ℓ` `C²`, the regularity at which `d` commutes with
pullback and `d(dℓ) = 0`. -/
theorem wedge_compContinuousLinearMap_fderiv_nextCollision (hχ : ContDiff ℝ 3 χ)
    (hx : x.2 ∈ Ioo (-1) 1) :
    ((realPlaneDx (χ.nextCollision x)).wedge
        (realPlaneDy (χ.nextCollision x))).compContinuousLinearMap (fderiv ℝ χ.nextCollision x) =
      (realPlaneDx x).wedge (realPlaneDy x) := by
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by norm_num)
  have hB : ContDiffAt ℝ 2 χ.nextCollision x :=
    χ.contDiffAt_nextCollision two_ne_zero hχ.contDiffAt hχ.contDiffAt hx
  have hℓ : ContDiffAt ℝ 2 χ.chordLength x := χ.contDiffAt_chordLength two_ne_zero hχ hx
  -- Near `x` the exactness identity reads `B^*λ = λ + dℓ`.
  have hEq : (fun y ↦ (realPlaneYDx (χ.nextCollision y)).compContinuousLinearMap
      (fderiv ℝ χ.nextCollision y)) =ᶠ[𝓝 x]
        fun y ↦ realPlaneYDx y + differentialOneForm ℝ χ.chordLength y := by
    filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds hx] with y hy
    rw [← χ.realPlaneYDx_compContinuousLinearMap_fderiv_nextCollision_sub hχ2 hy,
      add_sub_cancel]
  -- Apply `d` to both sides: `d(B^*λ) = B^*(dλ)` and `d(dℓ) = 0`.
  have hYDx : ∀ p, DifferentiableAt ℝ realPlaneYDx p := fun _ ↦
    (contDiff_realPlaneYDx (n := 1)).differentiable_one.differentiableAt
  have hd := hEq.extDeriv_eq
  rw [extDeriv_pullback (hYDx _) hB (by simp),
    extDeriv_fun_add (hYDx x) (differentiableAt_differentialOneForm_iff.2
        ((hℓ.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero)),
    extDeriv_differentialOneForm_apply_eq_zero (hℓ.isSymmSndFDerivAt (by simp)), add_zero,
    extDeriv_realPlaneYDx, extDeriv_realPlaneYDx] at hd
  ext v
  simpa using congr(-$hd v)

/-- **The billiard map is area preserving**: the Jacobian determinant of `B` is one at every state
of the strip, for a `C³` parametrization `χ`. -/
theorem det_fderiv_nextCollision (hχ : ContDiff ℝ 3 χ) (hx : x.2 ∈ Ioo (-1) 1) :
    (fderiv ℝ χ.nextCollision x).det = 1 := by
  set A := fderiv ℝ χ.nextCollision x
  have h := congr($(χ.wedge_compContinuousLinearMap_fderiv_nextCollision hχ hx) ![(1, 0), (0, 1)])
  -- Evaluate both sides on the standard basis, where `ds ∧ dv` is the `2 × 2` determinant.
  have hv : ⇑A ∘ ![((1 : ℝ), (0 : ℝ)), (0, 1)] = ![A (1, 0), A (0, 1)] := by
    funext i
    fin_cases i <;> rfl
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hv,
    ContinuousAlternatingMap.wedge_apply_one_one,
    ContinuousAlternatingMap.wedge_apply_one_one] at h
  rw [ContinuousLinearMap.det, LinearMap.det_finTwoProd]
  simpa [mul_comm] using h

end StrictConvexBilliardTable

end TauCeti
