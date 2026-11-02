/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Analysis.InnerProductSpace.BallChord
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.Instances.Icc
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# Smooth chord coordinates on a closed ball

For a unit vector `p`, the closed unit ball minus its equator is analytically diffeomorphic to
its positive open hemisphere times `[-1, 1]`. The map follows the chords parallel to `p`:
`(x, t) ↦ x - (1 - t) ⟪x, p⟫ p`. This upgrades `TauCeti.hemisphereChord`, including at both
ends of each chord, using the manifold-with-boundary structure of the closed ball.

The inverse sends a point to the upper end of its chord and its normalized height. Its square
root has strictly positive argument off the equator, so these coordinates are analytic there.
They allow a smooth arc in the open hemisphere to sweep out a smooth strip in the closed ball;
in particular they are the product coordinates for the slice disc of a knot summed with its
reverse mirror image.

## Main definitions

* `TauCeti.hemisphereOpens`: the positive open hemisphere centered at a unit vector.
* `TauCeti.chordBallOpens`: the closed ball with the equator perpendicular to that vector removed.
* `TauCeti.hemisphereChordDiffeomorph`: the analytic chord parametrization of that open subset.

## References

* C. Livingston, *A survey of classical knot concordance*, Section 2, for the slice disc bounded
  by a knot summed with its reverse mirror image.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 8, for knot cobordism.

The underlying homeomorphism and its coordinate formulas are `TauCeti.hemisphereChord`.
-/

public noncomputable section

open Metric Module Set TopologicalSpace Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- The positive open hemisphere centered at the unit vector `p`.
An abbreviation so its carrier agrees with the domain of `hemisphereChord`. -/
abbrev hemisphereOpens : Opens (sphere (0 : E) 1) :=
  ⟨{x | 0 < ⟪(x : E), (p : E)⟫}, isOpen_lt continuous_const (by fun_prop)⟩

/-- The open subset of the closed unit ball obtained by removing its equator perpendicular to
`p`. It consists of points on nondegenerate chords parallel to `p`.
An abbreviation so its carrier agrees with the codomain of `hemisphereChord`. -/
abbrev chordBallOpens : Opens (closedBall (0 : E) 1) :=
  ⟨{y | ‖(y : E)‖ ^ 2 - ⟪(y : E), (p : E)⟫ ^ 2 < 1},
    isOpen_setOf_norm_sq_sub_inner_sq_lt_one p⟩

local instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The chord parametrization is analytic, including at both ends of each chord. -/
theorem contMDiff_hemisphereChord :
    ContMDiff (M := hemisphereOpens p × Icc (-1 : ℝ) 1) (M' := chordBallOpens p)
      ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ω (hemisphereChord p) := by
  suffices h : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) (𝓡∂ (n + 1)) ω
      (fun q : hemisphereOpens p × Icc (-1 : ℝ) 1 =>
        (hemisphereChord p q : closedBall (0 : E) 1)) by
    exact (TauCeti.ContMDiff.subtypeVal_comp_iff (chordBallOpens p) _).mp h
  apply contMDiff_iff_comp_subtypeVal_closedBall.mpr
  have hx : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ, E) ω
      (fun q : hemisphereOpens p × Icc (-1 : ℝ) 1 => (q.1 : E)) :=
    contMDiff_coe_sphere.comp (contMDiff_subtype_val.comp contMDiff_fst)
  have ht : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ) ω
      (fun q : hemisphereOpens p × Icc (-1 : ℝ) 1 => (q.2 : ℝ)) :=
    (contMDiff_subtypeVal_Icc (x := -1) (y := 1)).comp contMDiff_snd
  have hi : ContMDiff ((𝓡 n).prod (𝓡∂ 1)) 𝓘(ℝ) ω
      (fun q : hemisphereOpens p × Icc (-1 : ℝ) 1 => ⟪(q.1 : E), (p : E)⟫) :=
    contDiff_inner.contMDiff.comp (hx.prodMk_space contMDiff_const)
  convert hx.sub (((contMDiff_const (c := (1 : ℝ)).sub ht).mul hi).smul
    (contMDiff_const (c := (p : E)))) using 1
  funext q
  exact (coe_hemisphereChord_apply p q).trans (chordPoint_def p q.1.1 q.2)

/-- The upper chord endpoint and normalized height depend analytically on the point off the
equator. -/
theorem contMDiff_hemisphereChord_symm :
    ContMDiff (M := chordBallOpens p) (M' := hemisphereOpens p × Icc (-1 : ℝ) 1)
      (𝓡∂ (n + 1)) ((𝓡 n).prod (𝓡∂ 1)) ω (hemisphereChord p).symm := by
  have hy : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, E) ω
      (fun y : chordBallOpens p => (y : E)) :=
    contMDiff_subtypeVal_closedBall.comp contMDiff_subtype_val
  have hi : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω
      (fun y : chordBallOpens p => ⟪(y : E), (p : E)⟫) :=
    contDiff_inner.contMDiff.comp (hy.prodMk_space contMDiff_const)
  -- Off the equator, the positive square root gives the half-length of the chord.
  have hpos (y : chordBallOpens p) :
      0 < 1 - ‖(y : E)‖ ^ 2 + ⟪(y : E), (p : E)⟫ ^ 2 := by
    have : ‖(y : E)‖ ^ 2 - ⟪(y : E), (p : E)⟫ ^ 2 < 1 := y.property
    linarith
  have hr : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ) ω
      (fun y : chordBallOpens p => √(1 - ‖(y : E)‖ ^ 2 + ⟪(y : E), (p : E)⟫ ^ 2)) := by
    intro y
    exact (Real.contDiffAt_sqrt (hpos y).ne').comp_contMDiffAt
      (f := fun y : chordBallOpens p => 1 - ‖(y : E)‖ ^ 2 + ⟪(y : E), (p : E)⟫ ^ 2)
      ((contMDiff_const (c := (1 : ℝ)).sub ((contDiff_norm_sq ℝ).contMDiff.comp hy)).add
        (hi.pow 2)).contMDiffAt
  have hx : ContMDiff (𝓡∂ (n + 1)) (𝓡 n) ω
      (fun y : chordBallOpens p => ((hemisphereChord p).symm y).1.1) := by
    apply ContMDiff.codRestrict_sphere
    convert hy.add ((hr.sub hi).smul (contMDiff_const (c := (p : E)))) using 1
    funext y
    exact coe_hemisphereChord_symm_apply_fst p y
  have hx' : ContMDiff (M' := hemisphereOpens p) (𝓡∂ (n + 1)) (𝓡 n) ω
      (fun y : chordBallOpens p => ((hemisphereChord p).symm y).1) :=
    (TauCeti.ContMDiff.subtypeVal_comp_iff (hemisphereOpens p) _).mp hx
  have ht : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ 1) ω
      (fun y : chordBallOpens p => ((hemisphereChord p).symm y).2) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    refine ⟨(hemisphereChord p).symm.continuous.snd, ?_⟩
    convert hi.div₀ hr (fun y => (Real.sqrt_pos.mpr (hpos y)).ne') using 1
    funext y
    exact coe_hemisphereChord_symm_apply_snd p y
  exact hx'.prodMk ht

/-- The closed unit ball off the equator is analytically diffeomorphic to the positive open
hemisphere times `[-1, 1]`, by following the chords parallel to `p`. The parameter values `±1`
are included, so this is a diffeomorphism of manifolds with boundary. -/
def hemisphereChordDiffeomorph :
    (hemisphereOpens p × Icc (-1 : ℝ) 1) ≃ₘ^ω⟮(𝓡 n).prod (𝓡∂ 1), 𝓡∂ (n + 1)⟯
      chordBallOpens p where
  toEquiv := (hemisphereChord p).toEquiv
  contMDiff_toFun := contMDiff_hemisphereChord p
  contMDiff_invFun := contMDiff_hemisphereChord_symm p

@[simp]
theorem toHomeomorph_hemisphereChordDiffeomorph :
    (hemisphereChordDiffeomorph (n := n) p).toHomeomorph = hemisphereChord p := (rfl)

@[simp]
theorem coe_hemisphereChordDiffeomorph :
    ⇑(hemisphereChordDiffeomorph (n := n) p) = hemisphereChord p := (rfl)

@[simp]
theorem coe_hemisphereChordDiffeomorph_symm :
    ⇑(hemisphereChordDiffeomorph (n := n) p).symm = (hemisphereChord p).symm := (rfl)

end TauCeti
