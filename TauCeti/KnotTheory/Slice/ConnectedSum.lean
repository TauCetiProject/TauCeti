/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BallChord
public import TauCeti.KnotTheory.ConnectedSum.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.Boundary.Collar.Basic
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.Immersion.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Immersion.ModelChange
import TauCeti.Geometry.Manifold.Instances.ClosedBall.Chord
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# A knot plus its reverse mirror image is slice

The inverse of a knot `K` in the knot concordance group is its reverse mirror image `-K`: the
connected sum `K # -K` is slice. This file proves that it is smoothly slice, by an explicit smooth
slice disc; in particular it is topologically slice.

The knot is a smooth circle embedding `K : S¹ → Sⁿ` in connected-sum position for a great circle
`ι` (`TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition ι K`): its knotted arc `A`, the image of
the open upper half of the circle, lies in the open hemisphere `⟪x, u⟫ > 0`, `u = ι i`, and the
rest of `K` is the great circle. Its reverse mirror image in connected-sum position is
`TauCeti.SmoothCircleEmbedding.reverseMirror ι K`, and the connected sum `K # -K` is `K` over the
closed upper half of the circle and `z ↦ σ (K z⁻¹)` over the lower half, for `σ` the reflection in
the great sphere `⟪x, u⟫ = 0`. So `K # -K` is the arc `A` followed by its mirror image `σ A`.

The slice disc is the union of the chords of the closed unit ball parallel to `u` through the
points of `A`, together with its two endpoints `ι (±1)` on the equator, where the chords
degenerate to points: the chord through `a ∈ A` joins `a` to `σ a`. In the chord coordinates of
the ball off its equator (`TauCeti.hemisphereChordDiffeomorph`), a diffeomorphism of manifolds
with boundary from the open hemisphere times `[-1, 1]`, this disc minus its two endpoints is the
product `A × [-1, 1]`, and in the same coordinates for the closed unit disc of `ℂ` minus `±1` it is
the parametrization `(z, t) ↦ (K z, t)` of that product. Near the two points `±1` of the circle the
knot is the great circle, so the disc is the flat disc `ι D²` there. It is an immersion of
manifolds with boundary for a different reason in each of the two regions:

* near `±1` it is the flat disc `ι D²`, the restriction of the linear isometry `ι` to the closed
  unit balls (`LinearIsometry.isImmersionAt_unitClosedBallMap`);
* off the equator of the disc it is the product of the arc `A`, an immersion into the open
  hemisphere because `K` is a smooth embedding, with the identity of `[-1, 1]`, read in chord
  coordinates. The product model of the open hemisphere times `[-1, 1]` is linearly the half-space
  model of the ball (`TauCeti.EuclideanHalfSpace.exists_continuousLinearEquiv_image_range_prod`),
  so the chord coordinates carry this normal form to the half-space charts
  (`TauCeti.isImmersionAt_diffeomorph_comp_of_image_range_eq`).

The disc is injective, meets the boundary sphere exactly along the boundary circle, and is compact,
so it is a smooth embedding. The identification of slice knots with the knots concordant to the
unknot, which turns this into the inverse law of the concordance group, is not proved here.

## Main results

* `TauCeti.SmoothCircleEmbedding.isSmoothlySlice_connectedSum_reverseMirror`: for a knot `K` in
  connected-sum position, `K # -K` is smoothly slice.
* `TauCeti.SmoothCircleEmbedding.isTopologicallySlice_connectedSum_reverseMirror`: in particular
  it is topologically slice.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8, for
  slice knots and the concordance (cobordism) group, whose inverse is the reverse mirror image.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for `K # -K` being slice.
-/

public section

noncomputable section

open Manifold Metric Module Set Topology Filter
open scoped Manifold ContDiff RealInnerProductSpace ComplexConjugate

namespace TauCeti

namespace SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}
  {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-! ### Chord coordinates of the disc and of the ball -/

/-- The unit vector `i`, the direction of the chords of the closed unit disc. -/
private def axisC : sphere (0 : ℂ) 1 :=
  ⟨Complex.I, by simp⟩

variable (ι) in
/-- The unit vector `ι i`, the direction of the chords of the closed unit ball of `E`. -/
private def axis : sphere (0 : E) 1 :=
  ⟨ι Complex.I, by simp⟩

private theorem inner_axisC (z : ℂ) : ⟪z, ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ = z.im := by
  simp [axisC, Complex.inner]

/-- The closed unit disc off its equator `{±1}`, the domain of the chord coordinates of the
disc. -/
private abbrev OffEquator : Type :=
  {z : closedBall (0 : ℂ) 1 // ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1}

/-- The arc of `K` over the open upper half of the circle, as a map into the open upper
hemisphere. -/
private def upperArc (h : IsConnectedSumPosition ι K)
    (x : {x : sphere (0 : ℂ) 1 // 0 < ⟪(x : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫}) :
    {y : sphere (0 : E) 1 // 0 < ⟪(y : E), ((axis ι : sphere (0 : E) 1) : E)⟫} :=
  ⟨K x.1, h.inner_pos (by have hx := x.2; rwa [inner_axisC] at hx)⟩

private theorem coe_upperArc (h : IsConnectedSumPosition ι K)
    (x : {x : sphere (0 : ℂ) 1 // 0 < ⟪(x : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫}) :
    ((upperArc h x : sphere (0 : E) 1) : E) = K x.1 :=
  (rfl)

/-! ### The disc of chords -/

open scoped Classical in
/-- The disc swept out by the chords parallel to `ι i` through the arc of `K`: off the equator of
the closed unit disc it is the arc times `[-1, 1]` in chord coordinates, and at the two points `±1`
of the equator it is `ι`. -/
private def chordDisc (h : IsConnectedSumPosition ι K) (z : closedBall (0 : ℂ) 1) :
    closedBall (0 : E) 1 :=
  if hz : ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1 then
    (hemisphereChord (axis ι) (Prod.map (upperArc h) id ((hemisphereChord axisC).symm ⟨z, hz⟩))).1
  else ι.unitClosedBallMap z

private theorem chordDisc_of_mem (h : IsConnectedSumPosition ι K) {z : closedBall (0 : ℂ) 1}
    (hz : ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1) :
    chordDisc h z = (hemisphereChord (axis ι)
      (Prod.map (upperArc h) id ((hemisphereChord axisC).symm ⟨z, hz⟩))).1 := by
  rw [chordDisc, dite_eq_left hz]

private theorem chordDisc_of_not_mem (h : IsConnectedSumPosition ι K) {z : closedBall (0 : ℂ) 1}
    (hz : ¬‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1) :
    chordDisc h z = ι.unitClosedBallMap z := by
  rw [chordDisc, dite_eq_right hz]

/-- Off the equator, the disc of chords is the point at the chord height of `z` on the chord
through the image under `K` of the upper end of the chord of `z`. -/
private theorem coe_chordDisc_of_mem (h : IsConnectedSumPosition ι K)
    {z : closedBall (0 : ℂ) 1}
    (hz : ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1) :
    (chordDisc h z : E) = chordPoint (axis ι) (K ((hemisphereChord axisC).symm ⟨z, hz⟩).1.1)
      ((hemisphereChord axisC).symm ⟨z, hz⟩).2 := by
  rw [chordDisc_of_mem h hz, coe_hemisphereChord_apply, Prod.map_fst, Prod.map_snd, id_eq,
    coe_upperArc]

/-- A point of the disc off its equator is the point at its chord height on the chord through the
upper end of its chord. -/
private theorem coe_eq_chordPoint
    (z : OffEquator) :
    ((z : closedBall (0 : ℂ) 1) : ℂ) = chordPoint axisC ((hemisphereChord axisC).symm z).1.1
      ((hemisphereChord axisC).symm z).2 := by
  rw [← coe_hemisphereChord_apply, Homeomorph.apply_symm_apply]

/-- The upper end `Re z + √(1 - (Re z)²) i` of the chord of the closed unit disc through `z`, as a
point of the circle; it is continuous on the whole disc. -/
private def chordTop (z : closedBall (0 : ℂ) 1) : Circle :=
  ⟨(z : ℂ).re + √(1 - (z : ℂ).re ^ 2) * Complex.I, mem_sphere_zero_iff_norm.2 <| by
    have hre : (z : ℂ).re ^ 2 ≤ 1 := by
      have := (Complex.abs_re_le_norm (z : ℂ)).trans (mem_closedBall_zero_iff.1 z.2)
      nlinarith [abs_nonneg (z : ℂ).re, sq_abs (z : ℂ).re]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by linarith), add_sub_cancel, Real.sqrt_one]⟩

private theorem continuous_chordTop : Continuous chordTop :=
  .subtype_mk (by fun_prop) _

/-- Off the equator, the first chord coordinate of a point of the disc is the upper end of its
chord. -/
private theorem hemisphereChord_symm_fst_eq_chordTop
    (z : OffEquator) :
    (((hemisphereChord axisC).symm z).1.1 : ℂ) = chordTop z := by
  have hr : 1 - ‖((z : closedBall (0 : ℂ) 1) : ℂ)‖ ^ 2 + ((z : closedBall (0 : ℂ) 1) : ℂ).im ^ 2 =
      1 - ((z : closedBall (0 : ℂ) 1) : ℂ).re ^ 2 := by
    rw [← Complex.sq_norm_sub_sq_im]
    ring
  rw [coe_hemisphereChord_symm_apply_fst, inner_axisC, chordTop, hr]
  apply Complex.ext <;> simp [axisC]

/-- The set of points of the circle near which `K` is the great circle. -/
private def greatCircleLocus (ι : ℂ →ₗᵢ[ℝ] E) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    Set Circle :=
  {ζ | ⇑K =ᶠ[𝓝 ζ] ⇑(greatCircle (n := n) ι)}

private theorem isOpen_chordTop_preimage_greatCircleLocus :
    IsOpen (chordTop ⁻¹' greatCircleLocus (n := n) ι K) :=
  isOpen_setOfPred_eventually_nhds.preimage continuous_chordTop

/-- Near the points `±1`, where `K` is the great circle, the disc of chords is the flat disc. -/
private theorem chordDisc_eq_of_mem (h : IsConnectedSumPosition ι K) {z : closedBall (0 : ℂ) 1}
    (hz : chordTop z ∈ greatCircleLocus ι K) : chordDisc h z = ι.unitClosedBallMap z := by
  by_cases hU : ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1
  · set z' : OffEquator := ⟨z, hU⟩
    have hx : ((hemisphereChord axisC).symm z').1.1 = (chordTop z : sphere (0 : ℂ) 1) :=
      Subtype.ext (hemisphereChord_symm_fst_eq_chordTop z')
    -- The upper end of the chord of `z` is a point where `K` is the great circle.
    have hK : (K ((hemisphereChord axisC).symm z').1.1 : E) =
        ι ((hemisphereChord axisC).symm z').1.1 := by
      rw [hx]
      exact congrArg Subtype.val hz.eq_of_nhds |>.trans (coe_greatCircle_apply ι _)
    refine Subtype.ext ?_
    rw [coe_chordDisc_of_mem h hU, hK, LinearIsometry.coe_unitClosedBallMap_apply,
      coe_eq_chordPoint z']
    simpa only [axis, axisC, z'] using (ι.map_chordPoint axisC
      ((hemisphereChord axisC).symm z').1.1 ((hemisphereChord axisC).symm z').2).symm
  · exact chordDisc_of_not_mem h hU

/-- Every point of the disc is off the equator, or near `±1` where `K` is the great circle. -/
private theorem mem_or_chordTop_mem (h : IsConnectedSumPosition ι K) (z : closedBall (0 : ℂ) 1) :
    ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1 ∨
      chordTop z ∈ greatCircleLocus ι K := by
  by_contra! hz
  refine hz.2 (h.eventuallyEq_greatCircle ?_)
  have hre : 1 ≤ (z : ℂ).re ^ 2 := by
    simpa only [inner_axisC, Complex.sq_norm_sub_sq_im] using hz.1
  have hsqrt : √(1 - (z : ℂ).re ^ 2) = 0 := Real.sqrt_eq_zero'.2 (by linarith)
  simp [chordTop, hsqrt]

/-! ### The disc of chords is a smooth immersion -/

local instance : Fact ((-1 : ℝ) < 1) := ⟨by norm_num⟩

/-- The arc of `K` over the open upper half of the circle is an immersion into the open upper
hemisphere. -/
private theorem isImmersionAt_upperArc (h : IsConnectedSumPosition ι K)
    (x : hemisphereOpens axisC) :
    IsImmersionAt (𝓡 1) (𝓡 n) ∞ (M := hemisphereOpens axisC) (N := hemisphereOpens (axis ι))
      (upperArc h) x := by
  have hK : IsImmersionAt (𝓡 1) (𝓡 n) ∞ (fun y : hemisphereOpens axisC ↦ K y.1) x :=
    isImmersionAt_comp_subtypeVal_iff.2 (K.isSmoothEmbedding.isImmersion.isImmersionAt _)
  exact (isImmersionAt_codRestrict_opens_iff (U := hemisphereOpens (axis ι))
    (f := fun y : hemisphereOpens axisC ↦ K y.1) (fun y ↦ (upperArc h y).2)).2 hK

/-- Off the equator, the disc of chords is the product of the arc of `K` with `[-1, 1]`, read in
the chord coordinates of the disc and of the ball. -/
private theorem chordDisc_comp_coe (h : IsConnectedSumPosition ι K) :
    chordDisc h ∘ ((↑) : chordBallOpens axisC → closedBall (0 : ℂ) 1) =
      ((↑) : chordBallOpens (axis ι) → closedBall (0 : E) 1) ∘
        hemisphereChordDiffeomorph (n := n) (axis ι) ∘ Prod.map (upperArc h) id ∘
          (hemisphereChordDiffeomorph (n := 1) axisC).symm := by
  funext z
  rw [Function.comp_apply, chordDisc_of_mem h z.2]
  simp only [Function.comp_apply, coe_hemisphereChordDiffeomorph,
    coe_hemisphereChordDiffeomorph_symm]
  -- `⟨↑z, _⟩` is `z` itself, read in the subtype `OffEquator` underlying `chordBallOpens axisC`.
  rfl

/-- Off the equator, the disc of chords is an immersion: in the chord coordinates it is the
product of the immersed arc of `K` with the identity of `[-1, 1]`. -/
private theorem isImmersionAt_chordDisc_of_mem (h : IsConnectedSumPosition ι K)
    {z : closedBall (0 : ℂ) 1} (hz : z ∈ chordBallOpens axisC) :
    IsImmersionAt (𝓡∂ 2) (𝓡∂ (n + 1)) ∞ (chordDisc h) z := by
  -- The product models of the chord coordinates are linearly the half-space models.
  obtain ⟨A, hA⟩ := EuclideanHalfSpace.exists_continuousLinearEquiv_image_range_prod 1
  obtain ⟨B, hB⟩ := EuclideanHalfSpace.exists_continuousLinearEquiv_image_range_prod n
  have hA' : A.symm '' range (𝓡∂ (1 + 1)) = range ((𝓡 1).prod (𝓡∂ 1)) := by
    rw [← hA, ← image_comp]
    simp
  -- The product of the arc with the identity is an immersion.
  set q := (hemisphereChordDiffeomorph (n := 1) axisC).symm ⟨z, hz⟩
  have h₁ := (isImmersionAt_upperArc h q.1).prodMap
    ((IsImmersion.id (I := 𝓡∂ 1) (n := ∞) (M := Icc (-1 : ℝ) 1)).isImmersionAt q.2)
  -- Read it in the chord coordinates of the disc and of the ball.
  have h₂ := isImmersionAt_diffeomorph_comp_of_image_range_eq B hB
    (hemisphereChordDiffeomorph (n := n) (axis ι)) le_top
    (isImmersionAt_comp_diffeomorph_of_image_range_eq A.symm hA'
      (hemisphereChordDiffeomorph (n := 1) axisC).symm le_top (x := ⟨z, hz⟩) h₁)
  have h₃ := isImmersionAt_isLocalDiffeomorphAt_comp
    (isLocalDiffeomorph_subtype_val (I := 𝓡∂ (n + 1)) (n := ∞) _) h₂
  rw [← chordDisc_comp_coe h] at h₃
  exact isImmersionAt_comp_subtypeVal_iff.1 h₃

/-- Near `±1`, where `K` is the great circle, the disc of chords is the flat disc, which is an
immersion. -/
private theorem isImmersionAt_chordDisc_of_chordTop_mem (h : IsConnectedSumPosition ι K)
    {z : closedBall (0 : ℂ) 1} (hz : chordTop z ∈ greatCircleLocus ι K) :
    IsImmersionAt (𝓡∂ 2) (𝓡∂ (n + 1)) ∞ (chordDisc h) z :=
  (ι.isImmersionAt_unitClosedBallMap z).congr_of_eventuallyEq <|
    Filter.eventually_of_mem (isOpen_chordTop_preimage_greatCircleLocus.mem_nhds hz)
      fun _ hw ↦ (chordDisc_eq_of_mem h hw).symm

private theorem isImmersion_chordDisc (h : IsConnectedSumPosition ι K) :
    IsImmersion (𝓡∂ 2) (𝓡∂ (n + 1)) ∞ (chordDisc h) :=
  isImmersion_iff_forall_isImmersionAt.2 fun z ↦ (mem_or_chordTop_mem h z).elim
    (isImmersionAt_chordDisc_of_mem h) (isImmersionAt_chordDisc_of_chordTop_mem h)

/-! ### The disc of chords is a slice disc for `K # -K` -/

/-- Off the equator of the disc, the disc of chords stays off the equator of the ball, and at
`±1` it is on it: the quantity `‖y‖² - ⟪y, ι i⟫²` detects the first region. -/
private theorem norm_sq_sub_inner_sq_chordDisc_lt_one_iff (h : IsConnectedSumPosition ι K)
    (z : closedBall (0 : ℂ) 1) :
    ‖(chordDisc h z : E)‖ ^ 2 - ⟪(chordDisc h z : E), ((axis ι : sphere (0 : E) 1) : E)⟫ ^ 2 < 1 ↔
      ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1 := by
  by_cases hz : ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1
  · simp only [hz, iff_true]
    rw [chordDisc_of_mem h hz]
    exact (hemisphereChord (axis ι) _).2
  · simp only [hz, iff_false, not_lt]
    rw [chordDisc_of_not_mem h hz, LinearIsometry.coe_unitClosedBallMap_apply, ι.norm_map]
    simpa [axis, axisC, ι.inner_map_map] using not_lt.1 hz

private theorem injective_chordDisc (h : IsConnectedSumPosition ι K) :
    Function.Injective (chordDisc h) := by
  intro z w hzw
  have hiff := (norm_sq_sub_inner_sq_chordDisc_lt_one_iff h z).symm.trans
    ((congrArg (fun y : closedBall (0 : E) 1 ↦
      ‖(y : E)‖ ^ 2 - ⟪(y : E), ((axis ι : sphere (0 : E) 1) : E)⟫ ^ 2 < 1) hzw).to_iff.trans
      (norm_sq_sub_inner_sq_chordDisc_lt_one_iff h w))
  by_cases hz : ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1
  · have hw := hiff.1 hz
    have h' := hzw
    rw [chordDisc_of_mem h hz, chordDisc_of_mem h hw] at h'
    have hinj : Function.Injective (upperArc h) := fun x x' hx ↦
      Subtype.ext (K.isEmbedding.injective (congrArg Subtype.val hx))
    exact congrArg Subtype.val ((hemisphereChord axisC).symm.injective
      ((hinj.prodMap Function.injective_id) ((hemisphereChord (axis ι)).injective
        (Subtype.ext h'))))
  · have hw : ¬‖(w : ℂ)‖ ^ 2 - ⟪(w : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1 :=
      fun hw ↦ hz (hiff.2 hw)
    rw [chordDisc_of_not_mem h hz, chordDisc_of_not_mem h hw] at hzw
    exact ι.isEmbedding_unitClosedBallMap.injective hzw

/-- The disc of chords meets the unit sphere exactly over the unit circle. -/
private theorem norm_chordDisc_eq_one_iff (h : IsConnectedSumPosition ι K)
    (z : closedBall (0 : ℂ) 1) : ‖(chordDisc h z : E)‖ = 1 ↔ ‖(z : ℂ)‖ = 1 := by
  by_cases hz : ‖(z : ℂ)‖ ^ 2 - ⟪(z : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1
  · let z' : OffEquator := ⟨z, hz⟩
    have h₁ := coe_chordDisc_of_mem h hz
    have h₂ := coe_eq_chordPoint z'
    have hKx := (upperArc h ((hemisphereChord axisC).symm z').1).2
    generalize (hemisphereChord axisC).symm z' = q at h₁ h₂ hKx
    rw [h₁, h₂]
    exact (norm_chordPoint_eq_one_iff _ (norm_eq_of_mem_sphere _) hKx.ne' _).trans
      (norm_chordPoint_eq_one_iff _ (norm_eq_of_mem_sphere _) q.1.2.ne' _).symm
  · rw [chordDisc_of_not_mem h hz, LinearIsometry.coe_unitClosedBallMap_apply, ι.norm_map]

/-- On the boundary circle the disc of chords is `K # -K`: the arc of `K` over the upper half, and
its mirror image `σ (K z⁻¹)` over the lower half. -/
private theorem chordDisc_inclusion (h : IsConnectedSumPosition ι K) (z : Circle) :
    (chordDisc h (Set.inclusion sphere_subset_closedBall z) : E) =
      connectedSum K (reverseMirror ι K) h h.reverseMirror z := by
  set ζ : closedBall (0 : ℂ) 1 := Set.inclusion sphere_subset_closedBall z
  have hζ : (ζ : ℂ) = z := rfl
  have hn : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
  by_cases hU : ‖(ζ : ℂ)‖ ^ 2 - ⟪(ζ : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ ^ 2 < 1
  · let z' : OffEquator := ⟨ζ, hU⟩
    have hdisc := coe_chordDisc_of_mem h hU
    have hxz := coe_eq_chordPoint z'
    generalize (hemisphereChord axisC).symm z' = q at hdisc hxz
    obtain ⟨⟨x, hx⟩, ⟨t, ht'⟩⟩ := q
    dsimp only at hdisc hxz
    -- On the circle the chord height is `±1`, with the sign of `Im z`.
    have ht : t ^ 2 = 1 := by
      rw [← norm_chordPoint_eq_one_iff axisC (norm_eq_of_mem_sphere _) hx.ne', ← hxz, hn]
    have him : (z : ℂ).im = t * ⟪(x : ℂ), ((axisC : sphere (0 : ℂ) 1) : ℂ)⟫ := by
      rw [← inner_axisC, hxz, inner_chordPoint]
    rcases sq_eq_one_iff.1 ht with rfl | rfl
    · -- Over the upper half, the chord height is `1` and the disc is `K`.
      have hxz' : (x : Circle) = z := Subtype.ext (by rw [hxz, chordPoint_one])
      rw [hdisc, chordPoint_one, connectedSum_apply_of_im_nonneg _ _ (by rw [him]; positivity),
        hxz']
    · -- Over the lower half, the chord height is `-1` and the disc is the mirror image of `K`.
      have hzneg : (z : ℂ).im < 0 := by
        rw [him]
        linarith
      have hxz' : (x : Circle) = z⁻¹ := by
        refine Subtype.ext ?_
        rw [Circle.coe_inv_eq_conj, hxz, chordPoint_neg_one,
          reflection_orthogonal_singleton_apply (norm_eq_of_mem_sphere _)]
        apply Complex.ext <;> simp [axisC, Complex.inner]
        ring
      rw [hdisc, chordPoint_neg_one, coe_connectedSum_apply_of_im_neg _ _ hzneg,
        coe_reverseMirror_apply, Submodule.reflection_reflection, neg_neg, hxz']
      rfl
  · -- At `±1` both are the great circle.
    have him : (z : ℂ).im = 0 := by
      rw [hζ, inner_axisC, Complex.sq_norm_sub_sq_im, not_lt] at hU
      have h1 := Complex.sq_norm_sub_sq_re (z : ℂ)
      rw [hn] at h1
      nlinarith [sq_nonneg (z : ℂ).im]
    rw [chordDisc_of_not_mem h hU, LinearIsometry.coe_unitClosedBallMap_apply,
      connectedSum_apply_of_im_nonneg _ _ him.ge, h.apply_eq him.le, coe_greatCircle_apply]

private theorem isSmoothSliceDisc_chordDisc (h : IsConnectedSumPosition ι K) :
    IsSmoothSliceDisc (connectedSum K (reverseMirror ι K) h h.reverseMirror) (chordDisc h) := by
  have himm := isImmersion_chordDisc h
  have hcont : Continuous (chordDisc h) :=
    continuous_iff_continuousAt.2 fun z ↦ (himm.isImmersionAt z).continuousAt
  have : CompactSpace (closedBall (0 : ℂ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  refine ⟨⟨himm, (hcont.isClosedEmbedding (injective_chordDisc h)).isEmbedding⟩, ?_,
    chordDisc_inclusion h⟩
  ext z
  simp [boundary_closedBall, norm_chordDisc_eq_one_iff h]

/-- **A knot plus its reverse mirror image is smoothly slice.** For a knot `K : S¹ → Sⁿ` in
connected-sum position for the great circle `ι`, the connected sum `K # -K` of `K` with its reverse
mirror image `TauCeti.SmoothCircleEmbedding.reverseMirror ι K` bounds a smooth slice disc in
`Dⁿ⁺¹`: the union of the chords parallel to `ι i` through the knotted arc of `K`. -/
theorem isSmoothlySlice_connectedSum_reverseMirror (h : IsConnectedSumPosition ι K) :
    IsSmoothlySlice (connectedSum K (reverseMirror ι K) h h.reverseMirror) :=
  (isSmoothSliceDisc_chordDisc h).isSmoothlySlice

/-- **A knot plus its reverse mirror image is topologically slice.** This follows from the smooth
statement `TauCeti.SmoothCircleEmbedding.isSmoothlySlice_connectedSum_reverseMirror`. -/
theorem isTopologicallySlice_connectedSum_reverseMirror (h : IsConnectedSumPosition ι K) :
    IsTopologicallySlice (connectedSum K (reverseMirror ι K) h h.reverseMirror) :=
  (isSmoothlySlice_connectedSum_reverseMirror h).isTopologicallySlice

end SmoothCircleEmbedding

end TauCeti
