/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Reflection
public import TauCeti.KnotTheory.Mirror
import TauCeti.Analysis.InnerProductSpace.LinearIsometry

/-!
# The connected sum of knots

The **connected sum** `K₁ # K₂` of two oriented knots is obtained by cutting each of them at a
point and joining the two resulting arcs: a `2`-sphere meeting `K₁ # K₂` in two points cuts it
into the two knotted arcs, and closing either arc by an unknotted arc gives back the summand. It is
the group operation of the knot concordance group.

Here a knot is a smooth circle embedding `K : S¹ → Sⁿ` into the unit sphere of a real inner product
space `E` of dimension `n + 1` (`TauCeti.SmoothCircleEmbedding`), with `S³ ⊆ ℝ⁴` the case `n = 3`.
The construction fixes a great circle, given by a linear isometry `ι : ℂ →ₗᵢ[ℝ] E` as
`TauCeti.SmoothCircleEmbedding.greatCircle ι`, and the great sphere `{x | ⟪x, ι i⟫ = 0}`, which
meets that circle in the two points `ι 1` and `ι (-1)`. A knot `K` is in **connected-sum
position** (`TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition ι K`) when

* near every point `z` of the closed lower half `Im z ≤ 0` of the standard circle, `K` agrees with
  the great circle, so that the lower half is an unknotted arc in the closed lower hemisphere;
* the open upper half `Im z > 0` is carried into the open upper hemisphere `⟪x, ι i⟫ > 0`.

So all the knotting of `K` happens in the upper hemisphere. The great circle itself is in
connected-sum position (`TauCeti.SmoothCircleEmbedding.isConnectedSumPosition_greatCircle`).

For `K₁`, `K₂` in connected-sum position, `TauCeti.SmoothCircleEmbedding.connectedSum` keeps the
upper half of `K₁` and replaces its lower half by the upper half of `K₂` turned over into the lower
hemisphere by the half-turn `ρ` of `E` in the plane `ι ℂ`, the rotation by `π` in that plane
fixing its orthogonal complement:

`(K₁ # K₂) z = K₁ z` if `Im z ≥ 0`, and `(K₁ # K₂) z = ρ (K₂ (-z))` if `Im z < 0`.

Near the two points `±1` of the circle both halves are the great circle (`ρ (ι (-z)) = ι z`), so the
result is again a smooth embedding. Since `ρ` is a rotation and `z ↦ -z` is a rotation of the
circle, the lower half of `K₁ # K₂` is the knotted arc of `K₂` moved by an orientation-preserving
isometry, with its orientation kept; so this is the connected sum of the oriented knots `K₁` and
`K₂`, not of `K₁` and the reverse or the mirror image of `K₂`. The great sphere `⟪x, ι i⟫ = 0`
splits it into the two knotted arcs: the sign of `⟪(K₁ # K₂) z, ι i⟫` is the sign of `Im z`
(`TauCeti.SmoothCircleEmbedding.sign_inner_connectedSum`).

The great circle is a right unit on the nose
(`TauCeti.SmoothCircleEmbedding.connectedSum_greatCircle`), and a left unit up to replacing the
knot by `TauCeti.SmoothCircleEmbedding.turnOver`, which moves it by the half-turn and rotates its
parametrization by `-1` (`TauCeti.SmoothCircleEmbedding.greatCircle_connectedSum`). Any linear
isometry `e : E ≃ₗᵢ[ℝ] E'` intertwining `ι` and `ι'` transports connected-sum position and commutes
with the connected sum (`TauCeti.SmoothCircleEmbedding.transDiffeomorph_connectedSum`); in
particular the mirror image of a connected sum of knots in `S³ ⊆ ℝ⁴`, in position for the unknot, is
the connected sum of the mirror images (`TauCeti.SmoothCircleEmbedding.mirror_connectedSum`).

The reverse mirror image `TauCeti.SmoothCircleEmbedding.reverseMirror ι K`, the candidate inverse
of `K` in the concordance group, is an involution fixing `greatCircle ι` and distributing on the
nose over `connectedSum` (`reverseMirror_reverseMirror`, `reverseMirror_greatCircle`,
`reverseMirror_connectedSum`). It is a turned-over copy of the reverse of `K` moved by a reflection
(`TauCeti.SmoothCircleEmbedding.reverseMirror_eq_turnOver`), so it is smoothly concordant to
`K.reverse` moved by any reflection (`concordant_reverseMirror_of_det_eq_neg_one`), and in `ℝⁿ⁺¹`
to `K.reverse.mirror` (`TauCeti.SmoothCircleEmbedding.concordant_reverseMirror_reverse_mirror`).

Concordances in connected-sum position can themselves be summed, giving a concordance between
the connected sums (`TauCeti.KnotTheory.ConnectedSum.Concordance`), and in a sphere of dimension
at least two every knot is concordant to one in connected-sum position
(`TauCeti.KnotTheory.ConnectedSum.Position`). In fact every knot in a sphere of dimension at
least two is smoothly ambient isotopic to one in that position
(`TauCeti.KnotTheory.ConnectedSum.Isotopy`). Independence of the positioned representatives and of
the great circle up to smooth concordance is proved in
`TauCeti.KnotTheory.ConnectedSum.Congruence`.

## Main definitions

* `TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition ι K`: the knot `K` is standard on the lower
  half of the circle and knotted only in the upper hemisphere determined by `ι`.
* `TauCeti.SmoothCircleEmbedding.turnOver ι K`: the knot `K` moved by the half-turn `ρ` and
  reparametrized by `z ↦ -z`, the second summand of a connected sum.
* `TauCeti.SmoothCircleEmbedding.connectedSum`: the connected sum of two knots in connected-sum
  position.
* `TauCeti.SmoothCircleEmbedding.reverseMirror`: the reverse mirror image of a knot, in
  connected-sum position whenever the knot is.

## Main results

* `TauCeti.SmoothCircleEmbedding.smoothIsotopic_turnOver`,
  `TauCeti.SmoothCircleEmbedding.concordant_turnOver`: turning a knot over preserves its smooth
  isotopy and concordance classes.
* `TauCeti.SmoothCircleEmbedding.connectedSum_apply_of_im_nonneg`,
  `TauCeti.SmoothCircleEmbedding.coe_connectedSum_apply_of_im_neg`: the two halves of the connected
  sum.
* `TauCeti.SmoothCircleEmbedding.sign_inner_connectedSum`: the great sphere `⟪x, ι i⟫ = 0` meets
  the connected sum exactly at `ι (±1)` and separates the two summands.
* `TauCeti.SmoothCircleEmbedding.connectedSum_greatCircle`,
  `TauCeti.SmoothCircleEmbedding.greatCircle_connectedSum`: the great circle is a unit.
* `TauCeti.SmoothCircleEmbedding.transDiffeomorph_connectedSum`,
  `TauCeti.SmoothCircleEmbedding.transDiffeomorph_reverse_rotate_connectedSum`,
  `TauCeti.SmoothCircleEmbedding.mirror_connectedSum`: compatibility with linear isometries
  intertwining great circles (or negating `ι 1` and preserving `ι i`), and with mirroring.
* `TauCeti.SmoothCircleEmbedding.reverseMirror_reverseMirror`,
  `TauCeti.SmoothCircleEmbedding.reverseMirror_greatCircle`,
  `TauCeti.SmoothCircleEmbedding.reverseMirror_connectedSum`: involutivity, unit preservation, and
  distributivity of `reverseMirror`.
* `TauCeti.SmoothCircleEmbedding.concordant_reverseMirror_of_det_eq_neg_one`,
  `TauCeti.SmoothCircleEmbedding.concordant_reverseMirror_reverse_mirror`: the reverse mirror image
  is smoothly concordant to the reversed knot moved by any reflection.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 (the sum
  of two knots).
* G. Burde, H. Zieschang, *Knots*, 2nd ed., de Gruyter (2003), Chapter 2 (the product, or
  connected sum, of knots).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the concordance group).
-/

public section

noncomputable section

open Metric Module Set Filter Topology Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

namespace SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}

/-! ### Connected-sum position -/

variable (ι) in
/-- A knot `K` in the unit sphere of `E` is in **connected-sum position** with respect to the great
circle `ι` when it agrees with the great circle `TauCeti.SmoothCircleEmbedding.greatCircle ι` near
every point `z` of the closed lower half `Im z ≤ 0` of the standard circle, and carries the open
upper half `Im z > 0` into the open hemisphere `⟪x, ι i⟫ > 0`. All the knotting of `K` then
happens in that hemisphere. -/
structure IsConnectedSumPosition (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) : Prop where
  /-- Near the closed lower half of the circle the knot is the great circle. -/
  eventuallyEq_greatCircle {z : Circle} (hz : (z : ℂ).im ≤ 0) : ⇑K =ᶠ[𝓝 z] ⇑(greatCircle (n := n) ι)
  /-- The open upper half of the circle goes into the open hemisphere `⟪x, ι i⟫ > 0`. -/
  inner_pos {z : Circle} (hz : 0 < (z : ℂ).im) : 0 < ⟪(K z : E), ι Complex.I⟫

variable {K K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- On the closed lower half of the circle, a knot in connected-sum position is the great
circle. -/
theorem IsConnectedSumPosition.apply_eq (h : IsConnectedSumPosition ι K) {z : Circle}
    (hz : (z : ℂ).im ≤ 0) : K z = greatCircle (n := n) ι z :=
  (h.eventuallyEq_greatCircle hz).eq_of_nhds

/-- A knot in connected-sum position meets the great sphere `⟪x, ι i⟫ = 0` only at `ι (±1)`: the
height `⟪K z, ι i⟫` has the sign of `Im z`. -/
theorem IsConnectedSumPosition.sign_inner (h : IsConnectedSumPosition ι K) (z : Circle) :
    SignType.sign ⟪(K z : E), ι Complex.I⟫ = SignType.sign (z : ℂ).im := by
  rcases lt_or_ge 0 (z : ℂ).im with hz | hz
  · rw [sign_pos hz, sign_pos (h.inner_pos hz)]
  · rw [h.apply_eq hz, coe_greatCircle_apply, ι.inner_map_map, Complex.inner]
    simp

variable (ι) in
/-- The great circle is in connected-sum position with respect to itself. -/
theorem isConnectedSumPosition_greatCircle :
    IsConnectedSumPosition ι (greatCircle (n := n) ι) where
  eventuallyEq_greatCircle _ := EventuallyEq.rfl
  inner_pos {z} hz := by simpa [ι.inner_map_map, Complex.inner] using hz

/-- A linear isometry equivalence intertwining `ι` and `ι'` transports `greatCircle ι` to
`greatCircle ι'`. -/
theorem transDiffeomorph_unitSphereDiffeomorph_greatCircle
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E' = n + 1)]
    {ι' : ℂ →ₗᵢ[ℝ] E'} {e : E ≃ₗᵢ[ℝ] E'} (he : ∀ w, e (ι w) = ι' w) :
    (greatCircle (n := n) ι).transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) =
      greatCircle (n := n) ι' :=
  SmoothEmbedding.ext fun z => Subtype.ext <| by simp [he]

/-- A linear isometry equivalence intertwining `ι` and `ι'` transports connected-sum position for
`ι` to connected-sum position for `ι'`. -/
theorem IsConnectedSumPosition.transDiffeomorph
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E' = n + 1)]
    {ι' : ℂ →ₗᵢ[ℝ] E'} (h : IsConnectedSumPosition ι K)
    {e : E ≃ₗᵢ[ℝ] E'} (he : ∀ w, e (ι w) = ι' w) :
    IsConnectedSumPosition ι'
      (K.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) where
  eventuallyEq_greatCircle {z} hz := by
    filter_upwards [h.eventuallyEq_greatCircle hz] with w hw
    exact Subtype.ext (by simp [hw, he])
  inner_pos {z} hz := by
    rw [SmoothEmbedding.transDiffeomorph_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      ← he Complex.I, LinearIsometryEquiv.inner_map_map]
    exact h.inner_pos hz

/-! ### The turned-over second summand -/

/-- The second summand of a connected sum: the knot moved into the lower hemisphere by the
half-turn in the plane `ι ℂ`, and reparametrized by the rotation `z ↦ -z` of the circle, so that
its knotted arc lies over the lower half of the circle. -/
def turnOver (ι : ℂ →ₗᵢ[ℝ] E) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  rotate (K.transDiffeomorph
    ((LinearMap.range ι.toLinearMap)ᗮ.reflection.unitSphereDiffeomorph (n := n) (k := n) ∞)) (-1)

/-- The turned-over embedding reflects the knot at the antipodal circle parameter. -/
@[simp]
theorem coe_turnOver_apply (ι : ℂ →ₗᵢ[ℝ] E)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) (z : Circle) :
    (turnOver ι K z : E) = (LinearMap.range ι.toLinearMap)ᗮ.reflection (K (-z)) := by
  simp [turnOver]

variable (ι) in
/-- **A knot is smoothly isotopic to its turned-over copy**: `K` and `turnOver ι K`, the knot moved
by the half-turn in the plane `ι ℂ` and reparametrized by `z ↦ -z`, are joined by a jointly smooth
isotopy through parametrized embeddings. -/
theorem smoothIsotopic_turnOver (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothIsotopic K.toContMDiffMap (turnOver ι K).toContMDiffMap := by
  apply smoothIsotopic_def.mpr
  obtain ⟨R, hR, hR0, hR1⟩ := ι.exists_contDiff_path_reflection_orthogonal_range
  let a : unitInterval → Circle := fun t => Circle.exp (Real.pi * t)
  have ha : ContMDiff (𝓡∂ 1) (𝓡 1) ∞ a :=
    contMDiff_circleExp.comp
      (contMDiff_const.mul (contMDiff_subtypeVal_Icc (x := 0) (y := 1)))
  have ha0 : a 0 = 1 := by simp [a]
  have ha1 : a 1 = -1 := by
    apply Subtype.ext
    simp [a, Circle.coe_exp, Complex.exp_pi_mul_I]
  let F : unitInterval × Circle → sphere (0 : E) 1 := fun p =>
    (R p.1).unitSphereDiffeomorph (n := n) (k := n) ∞ (K (a p.1 * p.2))
  have hs : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) (𝓡 n) ∞ F := by
    have hK : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ, E) ∞
        (fun p : unitInterval × Circle => (K (a p.1 * p.2) : E)) :=
      contMDiff_coe_sphere.comp
        (K.contMDiff.comp ((ha.comp contMDiff_fst).mul contMDiff_snd))
    have ht : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ) ∞
        (fun p : unitInterval × Circle => (p.1 : ℝ)) :=
      (contMDiff_subtypeVal_Icc (x := 0) (y := 1)).comp contMDiff_fst
    have hambient := hR.comp_contMDiff (ht.prodMk_space hK)
    have hcoe : (fun p => (F p : E)) =
        (fun p => R (p.1 : ℝ) (K (a p.1 * p.2))) := by
      funext p
      exact LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply _ _
    have hmem (p : unitInterval × Circle) : (F p : E) ∈ sphere (0 : E) 1 := (F p).property
    simp only [Function.comp_def] at hambient
    rw [← hcoe] at hambient
    exact hambient.codRestrict_sphere hmem
  refine ⟨{ toContMDiffMap := ⟨F, hs⟩
            map_zero_left := ?_
            map_one_left := ?_
            isSmoothEmbedding := ?_ }⟩
  · intro z
    apply Subtype.ext
    simp [F, ha0, hR0]
  · intro z
    apply Subtype.ext
    simp [F, ha1, hR1]
  · intro t
    have hslice := (K.rotate (a t)).transDiffeomorph
      ((R t).unitSphereDiffeomorph (n := n) (k := n) ∞) |>.isSmoothEmbedding
    simpa only [SmoothEmbedding.coe_transDiffeomorph, Function.comp_def,
      rotate_apply, F, ContMDiffMap.coeFn_mk] using hslice

variable (ι) in
/-- **Turning a knot over does not change its concordance class.** -/
theorem concordant_turnOver (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothEmbedding.Concordant K (turnOver ι K) :=
  SmoothEmbedding.Concordant.of_smoothIsotopic (smoothIsotopic_turnOver ι K) (by simp) le_rfl

/-- The half-turn and the antipodal parametrization together fix the great circle. -/
theorem reflection_greatCircle_neg (z : Circle) :
    (LinearMap.range ι.toLinearMap)ᗮ.reflection (greatCircle (n := n) ι (-z)) = ι z := by
  rw [coe_greatCircle_apply, Circle.coe_neg, map_neg, map_neg,
    ι.reflection_orthogonal_range_apply, neg_neg]

/-- Near the closed upper half of the circle, the turned-over knot is the great circle. -/
private theorem IsConnectedSumPosition.eventuallyEq_turnOver (h : IsConnectedSumPosition ι K)
    {z : Circle} (hz : 0 ≤ (z : ℂ).im) : ⇑(turnOver ι K) =ᶠ[𝓝 z] ⇑(greatCircle (n := n) ι) := by
  have hneg : ((-z : Circle) : ℂ).im ≤ 0 := by simpa using hz
  filter_upwards [(continuous_neg.tendsto z).eventually (h.eventuallyEq_greatCircle hneg)]
    with w hw
  ext
  rw [coe_turnOver_apply, hw, reflection_greatCircle_neg, coe_greatCircle_apply]

/-! ### The connected sum -/

/-- The underlying map of the connected sum: `K₁` on the closed upper half of the circle, and the
turned-over `K₂` on the open lower half. -/
private def connectedSumFun (ι : ℂ →ₗᵢ[ℝ] E)
    (K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) (z : Circle) : sphere (0 : E) 1 :=
  if 0 ≤ (z : ℂ).im then K₁ z else turnOver ι K₂ z

/-- Near every point the connected sum agrees with one of three smooth embeddings: `K₁` over the
open upper half, the turned-over `K₂` over the open lower half, and the great circle near `±1`. -/
private theorem exists_eventuallyEq_connectedSumFun (h₁ : IsConnectedSumPosition ι K₁)
    (h₂ : IsConnectedSumPosition ι K₂) (z : Circle) :
    ∃ G : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1), connectedSumFun ι K₁ K₂ =ᶠ[𝓝 z] ⇑G := by
  rcases lt_trichotomy (z : ℂ).im 0 with hz | hz | hz
  · refine ⟨turnOver ι K₂, ?_⟩
    filter_upwards [(isOpen_lt (Complex.continuous_im.comp continuous_subtypeVal)
      continuous_const).mem_nhds hz] with w (hw : (w : ℂ).im < 0)
    simp [connectedSumFun, hw.not_ge]
  · refine ⟨greatCircle ι, ?_⟩
    filter_upwards [h₁.eventuallyEq_greatCircle hz.le, h₂.eventuallyEq_turnOver hz.ge]
      with w hw₁ hw₂
    unfold connectedSumFun
    split_ifs <;> assumption
  · refine ⟨K₁, ?_⟩
    filter_upwards [(isOpen_lt continuous_const
      (Complex.continuous_im.comp continuous_subtypeVal)).mem_nhds hz] with w (hw : 0 < (w : ℂ).im)
    simp [connectedSumFun, hw.le]

/-- The height of the connected sum has the sign of `Im z`. -/
private theorem sign_inner_connectedSumFun (h₁ : IsConnectedSumPosition ι K₁)
    (h₂ : IsConnectedSumPosition ι K₂) (z : Circle) :
    SignType.sign ⟪(connectedSumFun ι K₁ K₂ z : E), ι Complex.I⟫ = SignType.sign (z : ℂ).im := by
  unfold connectedSumFun
  split_ifs with hz
  · exact h₁.sign_inner z
  · rw [coe_turnOver_apply,
      Submodule.inner_reflection_orthogonal_of_mem (LinearMap.range ι.toLinearMap) _
      (v := ι Complex.I) (LinearMap.mem_range_self _ Complex.I), Left.sign_neg,
      h₂.sign_inner, Circle.coe_neg, Complex.neg_im, Left.sign_neg, neg_neg]

private theorem injective_connectedSumFun (h₁ : IsConnectedSumPosition ι K₁)
    (h₂ : IsConnectedSumPosition ι K₂) : Function.Injective (connectedSumFun ι K₁ K₂) := by
  intro z w hzw
  have hsign : SignType.sign (z : ℂ).im = SignType.sign (w : ℂ).im := by
    rw [← sign_inner_connectedSumFun h₁ h₂, ← sign_inner_connectedSumFun h₁ h₂, hzw]
  rcases lt_trichotomy (z : ℂ).im 0 with hz | hz | hz
  · have hw : (w : ℂ).im < 0 := by rwa [sign_neg hz, eq_comm, sign_eq_neg_one_iff] at hsign
    simp only [connectedSumFun, hz.not_ge, hw.not_ge, ↓reduceIte] at hzw
    exact (turnOver ι K₂).isEmbedding.injective hzw
  · have hw : (w : ℂ).im = 0 := by rwa [hz, sign_zero, eq_comm, sign_eq_zero_iff] at hsign
    simp only [connectedSumFun, hz.ge, hw.ge, ↓reduceIte] at hzw
    rw [h₁.apply_eq hz.le, h₁.apply_eq hw.le] at hzw
    exact (greatCircle ι).isEmbedding.injective hzw
  · have hw : 0 < (w : ℂ).im := by rwa [sign_pos hz, eq_comm, sign_eq_one_iff] at hsign
    simp only [connectedSumFun, hz.le, hw.le, ↓reduceIte] at hzw
    exact K₁.isEmbedding.injective hzw

private theorem isSmoothEmbedding_connectedSumFun (h₁ : IsConnectedSumPosition ι K₁)
    (h₂ : IsConnectedSumPosition ι K₂) :
    IsSmoothEmbedding (𝓡 1) (𝓡 n) ∞ (connectedSumFun ι K₁ K₂) := by
  have hsmooth : ContMDiff (𝓡 1) (𝓡 n) ∞ (connectedSumFun ι K₁ K₂) := fun z ↦ by
    obtain ⟨G, hG⟩ := exists_eventuallyEq_connectedSumFun h₁ h₂ z
    exact G.contMDiff.contMDiffAt.congr_of_eventuallyEq hG
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun z ↦ ?_,
    (hsmooth.continuous.isClosedEmbedding (injective_connectedSumFun h₁ h₂)).isEmbedding⟩
  obtain ⟨G, hG⟩ := exists_eventuallyEq_connectedSumFun h₁ h₂ z
  exact (G.isImmersion.isImmersionAt z).congr_of_eventuallyEq hG.symm

/-- The **connected sum** `K₁ # K₂` of two knots in connected-sum position with respect to the
great circle `ι`: it is `K₁` over the closed upper half of the circle, and over the open lower half
it is `z ↦ ρ (K₂ (-z))`, the knotted arc of `K₂` turned over into the lower hemisphere by the
half-turn `ρ` of `E` in the plane `ι ℂ`. -/
def connectedSum (K₁ K₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
    (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  SmoothEmbedding.ofIsSmoothEmbedding _ (isSmoothEmbedding_connectedSumFun h₁ h₂)

variable (h₁ : IsConnectedSumPosition ι K₁) (h₂ : IsConnectedSumPosition ι K₂)

/-- Over the closed upper half of the circle the connected sum is the first summand. -/
theorem connectedSum_apply_of_im_nonneg {z : Circle} (hz : 0 ≤ (z : ℂ).im) :
    connectedSum K₁ K₂ h₁ h₂ z = K₁ z := by
  simp [connectedSum, connectedSumFun, hz]

/-- Over the open lower half of the circle the connected sum is the second summand, turned over
by the half-turn in the plane `ι ℂ`: `(K₁ # K₂) z = ρ (K₂ (-z))`. -/
theorem coe_connectedSum_apply_of_im_neg {z : Circle} (hz : (z : ℂ).im < 0) :
    (connectedSum K₁ K₂ h₁ h₂ z : E) = (LinearMap.range ι.toLinearMap)ᗮ.reflection (K₂ (-z)) := by
  simp [connectedSum, connectedSumFun, hz.not_ge, coe_turnOver_apply]

/-- **The great sphere splits the connected sum into its two summands**: the height
`⟪(K₁ # K₂) z, ι i⟫` has the sign of `Im z`, so the connected sum meets the great sphere
`⟪x, ι i⟫ = 0` exactly at `ι (±1)`, with the knotted arc of `K₁` above it and that of `K₂` below. -/
theorem sign_inner_connectedSum (z : Circle) :
    SignType.sign ⟪(connectedSum K₁ K₂ h₁ h₂ z : E), ι Complex.I⟫ = SignType.sign (z : ℂ).im := by
  rw [connectedSum, SmoothEmbedding.ofIsSmoothEmbedding_apply]
  exact sign_inner_connectedSumFun h₁ h₂ z

/-! ### The great circle is a unit -/

/-- **The great circle is a right unit** for the connected sum. -/
@[simp]
theorem connectedSum_greatCircle (h₀ : IsConnectedSumPosition ι (greatCircle ι)) :
    connectedSum K₁ (greatCircle ι) h₁ h₀ = K₁ := by
  ext z : 1
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ hz]
  · ext
    rw [coe_connectedSum_apply_of_im_neg _ _ hz, h₁.apply_eq hz.le,
      reflection_greatCircle_neg, coe_greatCircle_apply]

/-- **The great circle is a left unit** for the connected sum, up to moving the knot by the
half-turn `ρ` in the plane `ι ℂ` and rotating its parametrization by `-1`; as `ρ` is a rotation,
the result is ambient isotopic to the knot. -/
theorem greatCircle_connectedSum (h₀ : IsConnectedSumPosition ι (greatCircle ι)) :
    connectedSum (greatCircle ι) K₂ h₀ h₂ =
      rotate (K₂.transDiffeomorph ((LinearMap.range ι.toLinearMap)ᗮ.reflection.unitSphereDiffeomorph
        (n := n) (k := n) ∞)) (-1) := by
  ext z : 2
  rw [← turnOver, coe_turnOver_apply]
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ hz, ← coe_turnOver_apply,
      (h₂.eventuallyEq_turnOver hz).eq_of_nhds]
  · rw [coe_connectedSum_apply_of_im_neg _ _ hz]

/-! ### Isometries intertwining great circles, and mirroring -/

/-- A linear isometry equivalence intertwining `ι` and `ι'` commutes with the connected sum. -/
theorem transDiffeomorph_connectedSum
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E' = n + 1)]
    {ι' : ℂ →ₗᵢ[ℝ] E'} {e : E ≃ₗᵢ[ℝ] E'} (he : ∀ w, e (ι w) = ι' w) :
    (connectedSum K₁ K₂ h₁ h₂).transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞) =
      connectedSum (K₁.transDiffeomorph (e.unitSphereDiffeomorph ∞))
        (K₂.transDiffeomorph (e.unitSphereDiffeomorph ∞)) (h₁.transDiffeomorph he)
        (h₂.transDiffeomorph he) := by
  ext z : 1
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ hz, SmoothEmbedding.transDiffeomorph_apply,
      SmoothEmbedding.transDiffeomorph_apply, connectedSum_apply_of_im_nonneg _ _ hz]
  · ext
    have hrange : (LinearMap.range ι.toLinearMap).map (e.toLinearEquiv : E →ₗ[ℝ] E') =
        LinearMap.range ι'.toLinearMap :=
      LinearMap.map_range_eq_of_forall_map_eq (f := ι.toLinearMap) (g := ι'.toLinearMap)
        (l := (e.toLinearEquiv : E →ₗ[ℝ] E')) he
    rw [coe_connectedSum_apply_of_im_neg _ _ hz, SmoothEmbedding.transDiffeomorph_apply,
      LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, coe_connectedSum_apply_of_im_neg _ _ hz,
      SmoothEmbedding.transDiffeomorph_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
      Submodule.reflection_orthogonal_apply_of_map_eq _ hrange]

/-- A linear isometry equivalence sending `ι 1` to `-ι' 1` and `ι i` to `ι' i` transports
`(greatCircle ι).reverse.rotate (-1)` to `greatCircle ι'`. -/
theorem transDiffeomorph_reverse_rotate_greatCircle
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E' = n + 1)]
    {ι' : ℂ →ₗᵢ[ℝ] E'} {e : E ≃ₗᵢ[ℝ] E'}
    (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) :
    ((greatCircle (n := n) ι).reverse.rotate (-1)).transDiffeomorph
        (e.unitSphereDiffeomorph (n := n) (k := n) ∞) =
      greatCircle (n := n) ι' := by
  ext z : 2
  rw [SmoothEmbedding.transDiffeomorph_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
    rotate_apply, neg_one_mul, reverse_apply, coe_greatCircle_apply, coe_greatCircle_apply]
  refine (LinearMap.map_eq_neg_conj_of_map_one_eq_neg_of_map_I
    (f := ι.toLinearMap) (g := ι'.toLinearMap) (l := (e.toLinearEquiv : E →ₗ[ℝ] E')) h1 hI _).trans
    (congrArg ι' ?_)
  rw [Circle.coe_inv_eq_conj, Circle.coe_neg, map_neg, map_neg, Complex.conj_conj, neg_neg]

/-- A linear isometry equivalence sending `ι 1` to `-ι' 1` and `ι i` to `ι' i` carries a knot `K`
in connected-sum position for `ι` to
`(K.reverse.rotate (-1)).transDiffeomorph (e.unitSphereDiffeomorph ∞)` in connected-sum position
for `ι'`. -/
theorem IsConnectedSumPosition.transDiffeomorph_reverse_rotate
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E' = n + 1)]
    {ι' : ℂ →ₗᵢ[ℝ] E'} (h : IsConnectedSumPosition ι K) {e : E ≃ₗᵢ[ℝ] E'}
    (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) :
    IsConnectedSumPosition ι'
      ((K.reverse.rotate (-1)).transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) where
  eventuallyEq_greatCircle {z} hz := by
    have hneg : (((-z)⁻¹ : Circle) : ℂ).im ≤ 0 := by
      simpa [Circle.coe_inv_eq_conj] using hz
    rw [← transDiffeomorph_reverse_rotate_greatCircle (n := n) h1 hI]
    filter_upwards [((continuous_inv.comp continuous_neg).tendsto z).eventually
      (h.eventuallyEq_greatCircle hneg)] with w hw
    -- `filter_upwards` states `hw` through a composite of functions.
    have hw : K (-w)⁻¹ = greatCircle ι (-w)⁻¹ := hw
    simp only [SmoothEmbedding.transDiffeomorph_apply, rotate_apply, neg_one_mul, reverse_apply, hw]
  inner_pos {z} hz := by
    simp only [SmoothEmbedding.transDiffeomorph_apply,
      LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, rotate_apply, neg_one_mul, reverse_apply,
      ← hI, LinearIsometryEquiv.inner_map_map]
    exact h.inner_pos (by simpa [Circle.coe_inv_eq_conj] using hz)

/-- A linear isometry equivalence sending `ι 1` to `-ι' 1` and `ι i` to `ι' i` distributes
`.reverse.rotate (-1)` moved along `e` over the connected sum. -/
theorem transDiffeomorph_reverse_rotate_connectedSum
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [Fact (finrank ℝ E' = n + 1)]
    {ι' : ℂ →ₗᵢ[ℝ] E'} {e : E ≃ₗᵢ[ℝ] E'}
    (h1 : e (ι 1) = -ι' 1) (hI : e (ι Complex.I) = ι' Complex.I) :
    ((connectedSum K₁ K₂ h₁ h₂).reverse.rotate (-1)).transDiffeomorph
        (e.unitSphereDiffeomorph (n := n) (k := n) ∞) =
      connectedSum
        ((K₁.reverse.rotate (-1)).transDiffeomorph (e.unitSphereDiffeomorph ∞))
        ((K₂.reverse.rotate (-1)).transDiffeomorph (e.unitSphereDiffeomorph ∞))
        (h₁.transDiffeomorph_reverse_rotate h1 hI)
        (h₂.transDiffeomorph_reverse_rotate h1 hI) := by
  ext z : 1
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · have hz' : 0 ≤ (((-z)⁻¹ : Circle) : ℂ).im := by
      simpa [Circle.coe_inv_eq_conj] using hz
    simp only [SmoothEmbedding.transDiffeomorph_apply, rotate_apply, neg_one_mul, reverse_apply,
      connectedSum_apply_of_im_nonneg _ _ hz, connectedSum_apply_of_im_nonneg _ _ hz']
  · ext
    have hz' : (((-z)⁻¹ : Circle) : ℂ).im < 0 := by
      simpa [Circle.coe_inv_eq_conj] using hz
    have hrange : (LinearMap.range ι.toLinearMap).map (e.toLinearEquiv : E →ₗ[ℝ] E') =
        LinearMap.range ι'.toLinearMap :=
      LinearMap.map_range_eq_of_map_one_eq_neg_of_map_I
        (f := ι.toLinearMap) (g := ι'.toLinearMap) (l := (e.toLinearEquiv : E →ₗ[ℝ] E')) h1 hI
    have hneg : -((-z)⁻¹) = (-(-z))⁻¹ := Subtype.ext (by simp [inv_neg])
    simp only [SmoothEmbedding.transDiffeomorph_apply,
      LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, rotate_apply, neg_one_mul, reverse_apply,
      coe_connectedSum_apply_of_im_neg _ _ hz, coe_connectedSum_apply_of_im_neg _ _ hz', hneg,
      Submodule.reflection_orthogonal_apply_of_map_eq _ hrange]

/-! ### The reverse mirror image -/

variable (ι) in
/-- The **reverse mirror image** `-K` of a knot `K`, placed in connected-sum position whenever `K`
is (`TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition.reverseMirror`): `z ↦ ρ (σ (K (-z)⁻¹))`,
where `σ` is the reflection of `E` in the great sphere `⟪x, ι i⟫ = 0`
and `ρ` is the half-turn in the plane `ι ℂ`. The isometry `ρ ∘ σ` negates `ι 1` and fixes `ι i`
and the orthogonal complement of `ι ℂ`, so it is the reflection in the great sphere
`⟪x, ι 1⟫ = 0` and reverses the orientation of `E`; the reparametrization `z ↦ (-z)⁻¹` reverses the
orientation of the circle. This is the knot whose connected sum with `K` is smoothly slice
(`TauCeti.SmoothCircleEmbedding.isSmoothlySlice_connectedSum_reverseMirror`). -/
def reverseMirror (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  (K.reverse.rotate (-1)).transDiffeomorph
    (((ℝ ∙ ι Complex.I)ᗮ.reflection.trans
      (LinearMap.range ι.toLinearMap)ᗮ.reflection).unitSphereDiffeomorph (n := n) (k := n) ∞)

/-- The reverse mirror image sends `z` to `ρ (σ (K (-z)⁻¹))`, for `σ` the reflection in the great
sphere `⟪x, ι i⟫ = 0` and `ρ` the half-turn in the plane `ι ℂ`. -/
@[simp]
theorem coe_reverseMirror_apply (z : Circle) :
    (reverseMirror ι K z : E) =
      (LinearMap.range ι.toLinearMap)ᗮ.reflection ((ℝ ∙ ι Complex.I)ᗮ.reflection (K (-z)⁻¹)) := by
  simp [reverseMirror]

private theorem reverseMirror_reflection_map_one :
    ((ℝ ∙ ι Complex.I)ᗮ.reflection.trans (LinearMap.range ι.toLinearMap)ᗮ.reflection) (ι 1) =
      -ι 1 := by
  rw [LinearIsometryEquiv.trans_apply, ι.reflection_orthogonal_singleton_map_I, map_one,
    ι.reflection_orthogonal_range_apply]

private theorem reverseMirror_reflection_map_I :
    ((ℝ ∙ ι Complex.I)ᗮ.reflection.trans (LinearMap.range ι.toLinearMap)ᗮ.reflection)
        (ι Complex.I) = ι Complex.I := by
  rw [LinearIsometryEquiv.trans_apply, ι.reflection_orthogonal_singleton_map_I,
    Complex.conj_I, map_neg, map_neg, ι.reflection_orthogonal_range_apply, neg_neg]

/-- The reverse mirror image of a knot in connected-sum position is in connected-sum position. -/
theorem IsConnectedSumPosition.reverseMirror (h : IsConnectedSumPosition ι K) :
    IsConnectedSumPosition ι (reverseMirror ι K) :=
  h.transDiffeomorph_reverse_rotate
    reverseMirror_reflection_map_one reverseMirror_reflection_map_I

variable (ι) in
/-- The reverse mirror image is the turned-over copy of the reversed knot reflected in the great
sphere `⟪x, ι i⟫ = 0`. -/
theorem reverseMirror_eq_turnOver (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirror ι K = turnOver ι (K.reverse.transDiffeomorph
      ((ℝ ∙ ι Complex.I)ᗮ.reflection.unitSphereDiffeomorph (n := n) (k := n) ∞)) :=
  SmoothEmbedding.ext fun z => Subtype.ext <| by simp

variable (ι) in
/-- Applying `reverseMirror` twice returns the original knot. -/
@[simp]
theorem reverseMirror_reverseMirror (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    reverseMirror ι (reverseMirror ι K) = K := by
  have hsub : (ℝ ∙ ι Complex.I).map
      (((LinearMap.range ι.toLinearMap)ᗮ.reflection).toLinearEquiv : E →ₗ[ℝ] E) =
      ℝ ∙ ι Complex.I := by
    rw [Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, ι.reflection_orthogonal_range_apply,
      show -ι Complex.I = (-1 : ℝ) • ι Complex.I from (neg_one_smul ℝ _).symm,
      Submodule.span_singleton_smul_eq isUnit_one.neg]
  ext z : 2
  have hzz : (-((-z)⁻¹))⁻¹ = z := Subtype.ext (by simp)
  rw [coe_reverseMirror_apply, coe_reverseMirror_apply, hzz,
    ← Submodule.reflection_orthogonal_apply_of_map_eq (ℝ ∙ ι Complex.I) hsub,
    Submodule.reflection_reflection, Submodule.reflection_reflection]

variable (ι) in
/-- The reverse mirror image of the great circle `ι` is `greatCircle ι` itself. -/
@[simp]
theorem reverseMirror_greatCircle :
    reverseMirror ι (greatCircle (n := n) ι) = greatCircle (n := n) ι :=
  transDiffeomorph_reverse_rotate_greatCircle
    reverseMirror_reflection_map_one reverseMirror_reflection_map_I

/-- The reverse mirror image distributes over the connected sum. -/
@[simp]
theorem reverseMirror_connectedSum :
    reverseMirror ι (connectedSum K₁ K₂ h₁ h₂) =
      connectedSum (reverseMirror ι K₁) (reverseMirror ι K₂)
        h₁.reverseMirror h₂.reverseMirror :=
  transDiffeomorph_reverse_rotate_connectedSum h₁ h₂
    reverseMirror_reflection_map_one reverseMirror_reflection_map_I

variable (ι) in
/-- **The reverse mirror image is smoothly concordant to the reversed knot moved by any
orientation-reversing linear isometry.** For any `e : E ≃ₗᵢ[ℝ] E` of determinant `-1`,
`reverseMirror ι K` is smoothly concordant to `K.reverse` transported along `e`. -/
theorem concordant_reverseMirror_of_det_eq_neg_one {e : E ≃ₗᵢ[ℝ] E}
    (he : (LinearEquiv.det e.toLinearEquiv : ℝ) = -1)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothEmbedding.Concordant (reverseMirror ι K)
      (K.reverse.transDiffeomorph (e.unitSphereDiffeomorph (n := n) (k := n) ∞)) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  rw [reverseMirror_eq_turnOver]
  refine (concordant_turnOver ι _).symm.trans
    ((SmoothEmbedding.smoothAmbientIsotopic_transDiffeomorph_unitSphereDiffeomorph
      K.reverse ?_).concordant le_rfl)
  rw [linearEquiv_det_reflection_orthogonal_singleton
    ((map_ne_zero_iff ι ι.injective).2 Complex.I_ne_zero), he]

end General

/-! ### The reverse mirror image is the mirror image of the reverse -/

section ReverseMirror

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

variable {n : ℕ} (ι : ℂ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))

/-- **The reverse mirror image is concordant to the mirror image of the reverse.** For a knot `K`
in the unit sphere of `ℝⁿ⁺¹` and any great circle `ι`, the reverse mirror image `reverseMirror ι K`
is smoothly concordant to `K.reverse.mirror`: it is a turned-over copy of `K.reverse` moved by a
reflection, and the mirror image does not depend on the reflection up to ambient isotopy. -/
theorem concordant_reverseMirror_reverse_mirror
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :
    SmoothEmbedding.Concordant (reverseMirror ι K) K.reverse.mirror := by
  rw [K.reverse.mirror_def]
  exact concordant_reverseMirror_of_det_eq_neg_one ι
    (linearEquiv_det_reflection_orthogonal_singleton (by simp)) K

end ReverseMirror

/-! ### Mirroring knots in `S³` -/

section Mirror

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

variable {K K₁ K₂ : SmoothCircleEmbedding (𝓡 3) (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)}

/-- The mirror image of a knot in `S³` in connected-sum position for the unknot is again in
connected-sum position. -/
theorem IsConnectedSumPosition.mirror (h : IsConnectedSumPosition complexToEuclideanFour K) :
    IsConnectedSumPosition complexToEuclideanFour K.mirror := by
  rw [mirror_def]
  exact h.transDiffeomorph mirror_reflection_complexToEuclideanFour

/-- **The mirror image of a connected sum** of knots in `S³` is the connected sum of the mirror
images. -/
@[simp]
theorem mirror_connectedSum (h₁ : IsConnectedSumPosition complexToEuclideanFour K₁)
    (h₂ : IsConnectedSumPosition complexToEuclideanFour K₂) :
    (connectedSum K₁ K₂ h₁ h₂).mirror = connectedSum K₁.mirror K₂.mirror h₁.mirror h₂.mirror := by
  convert transDiffeomorph_connectedSum h₁ h₂ mirror_reflection_complexToEuclideanFour using 2 <;>
    exact mirror_def _

end Mirror

end SmoothCircleEmbedding

end TauCeti
