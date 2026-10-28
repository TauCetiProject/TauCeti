/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.KnotTheory.ConnectedSum.Basic

/-!
# The connected sum of concordances

The knot concordance group has the connected sum as its operation, so the connected sum has to be
compatible with concordance: if `K₁` is concordant to `K₁'` and `K₂` to `K₂'`, then `K₁ # K₂` is
concordant to `K₁' # K₂'`. The classical argument first arranges both concordance annuli to be
standard near an arc running from one end to the other, then cuts them along those arcs and glues
the two cut annuli together, exactly as the connected sum of knots glues two cut circles. This
file carries out the gluing, for concordances already in that standard form.

Fix, as in `TauCeti.KnotTheory.ConnectedSum.Basic`, a great circle `ι : ℂ →ₗᵢ[ℝ] E` in the unit
sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1`. A smooth concordance
`F : S¹ × ℝ → Sⁿ × ℝ` (`TauCeti.SmoothEmbedding.Concordance`) is in **connected-sum position**
(`TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition ι F`) when

* near every point `(z, t)` with `Im z ≤ 0` it agrees with the product of the great circle with the
  identity of the time line, so the lower half of the annulus is the standard strip;
* every point `(z, t)` with `Im z > 0` goes into the open upper hemisphere `⟪x, ι i⟫ > 0`, times
  the line.

Its two ends are then knots in connected-sum position
(`TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.initial`, `.final`), and the constant
concordance of a knot in connected-sum position is in connected-sum position. For two such
concordances `F₁` from `K₁` to `K₁'` and `F₂` from `K₂` to `K₂'`,
`TauCeti.SmoothEmbedding.Concordance.connectedSum` is the concordance

`(F₁ # F₂) (z, t) = F₁ (z, t)` if `Im z ≥ 0`, and `(F₁ # F₂) (z, t) = (ρ × id) (F₂ (-z, t))` if
`Im z < 0`,

from `K₁ # K₂` to `K₁' # K₂'`, where `ρ` is the half-turn of `E` in the plane `ι ℂ`. Near the seam
`Im z = 0` both halves are the standard strip, so the result is again smooth and an immersion;
the height `⟪x, ι i⟫` separates the two halves, so it is injective; and since it is a collared
track with compact source, it is a closed embedding (`TauCeti.IsCollaredTrack.isClosedEmbedding`).

Not formalized here: that any two concordant knots in connected-sum position are joined by a
concordance in connected-sum position, an isotopy-extension argument moving a standard arc of the
annulus onto the strip. That is the step from this construction to the connected sum being well
defined on concordance classes.

## Main definitions

* `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition ι F`: the concordance `F` is the
  standard strip over the lower half of the circle, and lies over the upper hemisphere elsewhere.
* `TauCeti.SmoothEmbedding.Concordance.connectedSum`: the connected sum of two concordances in
  connected-sum position.

## Main results

* `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.initial`,
  `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.final`: the ends of a concordance in
  connected-sum position are knots in connected-sum position.
* `TauCeti.SmoothEmbedding.Concordance.isConnectedSumPosition_refl`,
  `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.symm`: the constant and the reversed
  concordance are in connected-sum position.
* `TauCeti.SmoothEmbedding.Concordance.connectedSum_refl`,
  `TauCeti.SmoothEmbedding.Concordance.symm_connectedSum`: the connected sum of constant
  concordances is constant, and reversal distributes over the connected sum.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum`: the connected sums of the ends of two
  concordances in connected-sum position are concordant.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_left`,
  `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_right`: the same, varying one summand.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the concordance group, with the connected sum as its operation).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8 (knot
  cobordism and the cobordism group of knots).
-/

public section

noncomputable section

open Metric Module Set Filter Topology Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}

namespace SmoothEmbedding

namespace Concordance

open SmoothCircleEmbedding

/-! ### Concordances in connected-sum position -/

variable (ι) in
/-- A concordance `F` between knots in the unit sphere of `E` is in **connected-sum position** with
respect to the great circle `ι` when it agrees with the product of the great circle
`TauCeti.SmoothCircleEmbedding.greatCircle ι` and the identity of the time line near every point
`(z, t)` with `Im z ≤ 0`, and carries every point `(z, t)` with `Im z > 0` over the open hemisphere
`⟪x, ι i⟫ > 0`. All the knotting of the annulus then happens over that hemisphere. -/
structure IsConnectedSumPosition {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (F : Concordance K K') : Prop where
  /-- Over the closed lower half of the circle the concordance is the standard strip. -/
  eventuallyEq_prodMap {p : Circle × ℝ} (hp : (p.1 : ℂ).im ≤ 0) :
    ⇑F =ᶠ[𝓝 p] Prod.map (greatCircle (n := n) ι) _root_.id
  /-- Over the open upper half of the circle the concordance lies over the open hemisphere
  `⟪x, ι i⟫ > 0`. -/
  inner_pos {p : Circle × ℝ} (hp : 0 < (p.1 : ℂ).im) : 0 < ⟪((F p).1 : E), ι Complex.I⟫

variable {K K' K₁ K₁' K₂ K₂' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  {F : Concordance K K'}

/-- Over the closed lower half of the circle, a concordance in connected-sum position is the
standard strip. -/
theorem IsConnectedSumPosition.apply_eq (hF : F.IsConnectedSumPosition ι) {p : Circle × ℝ}
    (hp : (p.1 : ℂ).im ≤ 0) : F p = (greatCircle (n := n) ι p.1, p.2) :=
  (hF.eventuallyEq_prodMap hp).eq_of_nhds

/-- The height `⟪x, ι i⟫` of a concordance in connected-sum position has the sign of `Im z`. -/
theorem IsConnectedSumPosition.sign_inner (hF : F.IsConnectedSumPosition ι) (p : Circle × ℝ) :
    SignType.sign ⟪((F p).1 : E), ι Complex.I⟫ = SignType.sign (p.1 : ℂ).im := by
  rcases lt_or_ge 0 (p.1 : ℂ).im with hp | hp
  · rw [sign_pos hp, sign_pos (hF.inner_pos hp)]
  · simp [hF.apply_eq hp, ι.inner_map_map, Complex.inner]

/-- A knot which is the time-`c` slice of a concordance in connected-sum position is in
connected-sum position. -/
private theorem IsConnectedSumPosition.of_apply_eq (hF : F.IsConnectedSumPosition ι)
    {L : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {c : ℝ} (hL : ∀ w, F (w, c) = (L w, c)) :
    SmoothCircleEmbedding.IsConnectedSumPosition ι L where
  eventuallyEq_greatCircle {z} hz := by
    have hcont : Continuous fun w : Circle => (w, c) := by fun_prop
    filter_upwards [(hcont.tendsto z).eventually (hF.eventuallyEq_prodMap (p := (z, c)) hz)]
      with w hw
    simpa [hL] using congrArg Prod.fst hw
  inner_pos {z} hz := by simpa [hL] using hF.inner_pos (p := (z, c)) hz

/-- The initial knot of a concordance in connected-sum position is in connected-sum position. -/
theorem IsConnectedSumPosition.initial (hF : F.IsConnectedSumPosition ι) :
    SmoothCircleEmbedding.IsConnectedSumPosition ι K :=
  hF.of_apply_eq F.apply_zero

/-- The final knot of a concordance in connected-sum position is in connected-sum position. -/
theorem IsConnectedSumPosition.final (hF : F.IsConnectedSumPosition ι) :
    SmoothCircleEmbedding.IsConnectedSumPosition ι K' :=
  hF.of_apply_eq F.apply_one

/-- The constant concordance of a knot in connected-sum position is in connected-sum position. -/
theorem isConnectedSumPosition_refl (hK : SmoothCircleEmbedding.IsConnectedSumPosition ι K) :
    (Concordance.refl K).IsConnectedSumPosition ι where
  eventuallyEq_prodMap {p} hp := by
    filter_upwards [(continuous_fst.tendsto p).eventually (hK.eventuallyEq_greatCircle hp)]
      with q hq
    simp [Prod.map_apply', hq]
  inner_pos {p} hp := by simpa using hK.inner_pos hp

/-- The reversed concordance of a concordance in connected-sum position is in connected-sum
position. -/
theorem IsConnectedSumPosition.symm (hF : F.IsConnectedSumPosition ι) :
    F.symm.IsConnectedSumPosition ι where
  eventuallyEq_prodMap {p} hp := by
    have hcont : Continuous fun q : Circle × ℝ => (q.1, 1 - q.2) := by fun_prop
    filter_upwards [(hcont.tendsto p).eventually
      (hF.eventuallyEq_prodMap (p := (p.1, 1 - p.2)) hp)] with q hq
    obtain ⟨z, t⟩ := q
    simp only [Prod.map_apply, id_eq] at hq
    simp [hq]
  inner_pos {p} hp := by
    obtain ⟨z, t⟩ := p
    simpa using hF.inner_pos (p := (z, 1 - t)) hp

/-! ### The turned-over second concordance -/

/-- The half-turn of the unit sphere of `E` in the plane `ι ℂ`, which fixes the great circle
`ι` up to the antipodal map and exchanges the two hemispheres `⟪x, ι i⟫ > 0` and `⟪x, ι i⟫ < 0`. -/
private abbrev halfTurn (ι : ℂ →ₗᵢ[ℝ] E) :
    sphere (0 : E) 1 ≃ₘ^∞⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 :=
  (LinearMap.range ι.toLinearMap)ᗮ.reflection.unitSphereDiffeomorph (n := n) (k := n) ∞

/-- The second summand of a connected sum of concordances: the concordance moved over the lower
hemisphere by the half-turn in the plane `ι ℂ`, and reparametrized by the rotation `z ↦ -z` of the
circle, so that its knotted half lies over the lower half of the circle. -/
private def turnOver (ι : ℂ →ₗᵢ[ℝ] E) (F : Concordance K K') :
    Concordance (((K.transDiffeomorph (halfTurn ι))).compDiffeomorph (circleRotationHom (-1)))
      (((K'.transDiffeomorph (halfTurn ι))).compDiffeomorph (circleRotationHom (-1))) :=
  (F.transDiffeomorph (halfTurn ι)).compDiffeomorph (circleRotationHom (-1))

private theorem turnOver_apply (ι : ℂ →ₗᵢ[ℝ] E) (F : Concordance K K') (p : Circle × ℝ) :
    turnOver ι F p = Prod.map (halfTurn (n := n) ι) _root_.id (F (-p.1, p.2)) := by
  simp [turnOver, circleRotationHom_apply_apply, Prod.map_apply']

/-- Near the closed upper half of the circle, the turned-over concordance is the standard
strip. -/
private theorem IsConnectedSumPosition.eventuallyEq_turnOver (hF : F.IsConnectedSumPosition ι)
    {p : Circle × ℝ} (hp : 0 ≤ (p.1 : ℂ).im) :
    ⇑(turnOver ι F) =ᶠ[𝓝 p] Prod.map (greatCircle (n := n) ι) _root_.id := by
  have hneg : ((-p.1 : Circle) : ℂ).im ≤ 0 := by simpa using hp
  have hcont : Continuous fun q : Circle × ℝ => (-q.1, q.2) := by fun_prop
  filter_upwards [(hcont.tendsto p).eventually (hF.eventuallyEq_prodMap (p := (-p.1, p.2)) hneg)]
    with q hq
  rw [turnOver_apply, hq, Prod.map_apply', Prod.map_apply', Prod.map_apply']
  ext
  · dsimp only
    rw [LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply, reflection_greatCircle_neg,
      coe_greatCircle_apply]
  · rfl

/-- The height of the turned-over concordance has the sign of `Im z`. -/
private theorem IsConnectedSumPosition.sign_inner_turnOver (hF : F.IsConnectedSumPosition ι)
    (p : Circle × ℝ) :
    SignType.sign ⟪((turnOver ι F p).1 : E), ι Complex.I⟫ = SignType.sign (p.1 : ℂ).im := by
  rw [turnOver_apply, Prod.map_fst, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply,
    Submodule.inner_reflection_orthogonal_of_mem (LinearMap.range ι.toLinearMap) _
      (v := ι Complex.I) (LinearMap.mem_range_self _ Complex.I), Left.sign_neg,
    hF.sign_inner (-p.1, p.2), Circle.coe_neg, Complex.neg_im, Left.sign_neg, neg_neg]

/-! ### The connected sum of concordances -/

/-- The track of the connected sum of two concordances: the first concordance over the closed
upper half of the circle, and the turned-over second concordance over the open lower half. -/
private def connectedSumTrack (ι : ℂ →ₗᵢ[ℝ] E) (F₁ : Concordance K₁ K₁')
    (F₂ : Concordance K₂ K₂') (p : Circle × ℝ) : sphere (0 : E) 1 × ℝ :=
  if 0 ≤ (p.1 : ℂ).im then F₁ p else turnOver ι F₂ p

variable {F₁ : Concordance K₁ K₁'} {F₂ : Concordance K₂ K₂'}

/-- Near every point the track agrees with one of three smooth embeddings: the first concordance
over the open upper half, the turned-over second concordance over the open lower half, and the
standard strip near the seam `Im z = 0`. -/
private theorem exists_eventuallyEq_connectedSumTrack (hF₁ : F₁.IsConnectedSumPosition ι)
    (hF₂ : F₂.IsConnectedSumPosition ι) (p : Circle × ℝ) :
    ∃ G : SmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (Circle × ℝ)
      (sphere (0 : E) 1 × ℝ), connectedSumTrack ι F₁ F₂ =ᶠ[𝓝 p] ⇑G := by
  have him : Continuous fun q : Circle × ℝ => ((q.1 : ℂ)).im := by fun_prop
  rcases lt_trichotomy (p.1 : ℂ).im 0 with hp | hp | hp
  · refine ⟨(turnOver ι F₂).toSmoothEmbedding, ?_⟩
    filter_upwards [(isOpen_lt him continuous_const).mem_nhds hp] with q (hq : (q.1 : ℂ).im < 0)
    simp [connectedSumTrack, hq.not_ge]
  · refine ⟨(greatCircle ι).prodMap SmoothEmbedding.id, ?_⟩
    filter_upwards [hF₁.eventuallyEq_prodMap hp.le, hF₂.eventuallyEq_turnOver hp.ge]
      with q hq₁ hq₂
    rw [coe_prodMap, coe_id]
    unfold connectedSumTrack
    split_ifs <;> assumption
  · refine ⟨F₁.toSmoothEmbedding, ?_⟩
    filter_upwards [(isOpen_lt continuous_const him).mem_nhds hp] with q (hq : 0 < (q.1 : ℂ).im)
    simp [connectedSumTrack, hq.le]

/-- The height of the track has the sign of `Im z`. -/
private theorem sign_inner_connectedSumTrack (hF₁ : F₁.IsConnectedSumPosition ι)
    (hF₂ : F₂.IsConnectedSumPosition ι) (p : Circle × ℝ) :
    SignType.sign ⟪((connectedSumTrack ι F₁ F₂ p).1 : E), ι Complex.I⟫ =
      SignType.sign (p.1 : ℂ).im := by
  unfold connectedSumTrack
  split_ifs
  · exact hF₁.sign_inner p
  · exact hF₂.sign_inner_turnOver p

private theorem injective_connectedSumTrack (hF₁ : F₁.IsConnectedSumPosition ι)
    (hF₂ : F₂.IsConnectedSumPosition ι) : Function.Injective (connectedSumTrack ι F₁ F₂) := by
  intro p q hpq
  have hsign : SignType.sign (p.1 : ℂ).im = SignType.sign (q.1 : ℂ).im := by
    rw [← sign_inner_connectedSumTrack hF₁ hF₂, ← sign_inner_connectedSumTrack hF₁ hF₂, hpq]
  rcases lt_or_ge (p.1 : ℂ).im 0 with hp | hp
  · have hq : (q.1 : ℂ).im < 0 := by rwa [sign_neg hp, eq_comm, sign_eq_neg_one_iff] at hsign
    simp only [connectedSumTrack, hp.not_ge, hq.not_ge, ↓reduceIte] at hpq
    exact (turnOver ι F₂).toSmoothEmbedding.isEmbedding.injective hpq
  · have hq : 0 ≤ (q.1 : ℂ).im := by
      rw [← sign_nonneg_iff, ← hsign, sign_nonneg_iff]
      exact hp
    simp only [connectedSumTrack, hp, hq, ↓reduceIte] at hpq
    exact F₁.toSmoothEmbedding.isEmbedding.injective hpq

/-- The track is a collared track from `K₁ # K₂` to `K₁' # K₂'`. -/
private theorem isCollaredTrack_connectedSumTrack (hF₁ : F₁.IsConnectedSumPosition ι)
    (hF₂ : F₂.IsConnectedSumPosition ι) :
    IsCollaredTrack (SmoothCircleEmbedding.connectedSum K₁ K₂ hF₁.initial hF₂.initial)
      (SmoothCircleEmbedding.connectedSum K₁' K₂' hF₁.final hF₂.final)
      (connectedSumTrack ι F₁ F₂) := by
  -- Over the open lower half of the circle, the ends of the turned-over concordance are those of
  -- the connected sums.
  have hend {L₁ L₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
      (h₁ : SmoothCircleEmbedding.IsConnectedSumPosition ι L₁)
      (h₂ : SmoothCircleEmbedding.IsConnectedSumPosition ι L₂) {z : Circle} (hz : (z : ℂ).im < 0) :
      ((L₂.transDiffeomorph (halfTurn ι)).compDiffeomorph (circleRotationHom (-1))) z =
        SmoothCircleEmbedding.connectedSum L₁ L₂ h₁ h₂ z := by
    ext
    simp [coe_connectedSum_apply_of_im_neg _ _ hz, circleRotationHom_apply_apply]
  refine
    { exists_pos_apply_eq_left := ?_
      exists_pos_apply_eq_right := ?_
      snd_apply_mem_Ioo := fun z t ht => ?_ }
  · obtain ⟨ε₁, hε₁, h₁⟩ := F₁.isCollaredTrack.exists_pos_apply_eq_left
    obtain ⟨ε₂, hε₂, h₂⟩ := (turnOver ι F₂).isCollaredTrack.exists_pos_apply_eq_left
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z t ht => ?_⟩
    unfold connectedSumTrack
    split_ifs with hz
    · rw [h₁ z t (ht.trans (min_le_left _ _)), connectedSum_apply_of_im_nonneg _ _ hz]
    · rw [h₂ z t (ht.trans (min_le_right _ _)), hend _ _ (not_le.1 hz)]
  · obtain ⟨ε₁, hε₁, h₁⟩ := F₁.isCollaredTrack.exists_pos_apply_eq_right
    obtain ⟨ε₂, hε₂, h₂⟩ := (turnOver ι F₂).isCollaredTrack.exists_pos_apply_eq_right
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z t ht => ?_⟩
    unfold connectedSumTrack
    split_ifs with hz
    · rw [h₁ z t ((sub_le_sub_left (min_le_left _ _) 1).trans ht),
        connectedSum_apply_of_im_nonneg _ _ hz]
    · rw [h₂ z t ((sub_le_sub_left (min_le_right _ _) 1).trans ht), hend _ _ (not_le.1 hz)]
  · unfold connectedSumTrack
    split_ifs
    · exact F₁.isCollaredTrack.snd_apply_mem_Ioo z t ht
    · exact (turnOver ι F₂).isCollaredTrack.snd_apply_mem_Ioo z t ht

private theorem isSmoothEmbedding_connectedSumTrack (hF₁ : F₁.IsConnectedSumPosition ι)
    (hF₂ : F₂.IsConnectedSumPosition ι) :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (connectedSumTrack ι F₁ F₂) := by
  have hsmooth : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (connectedSumTrack ι F₁ F₂) :=
    fun p ↦ by
      obtain ⟨G, hG⟩ := exists_eventuallyEq_connectedSumTrack hF₁ hF₂ p
      exact G.contMDiff.contMDiffAt.congr_of_eventuallyEq hG
  have := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1)
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun p ↦ ?_,
    ((isCollaredTrack_connectedSumTrack hF₁ hF₂).isClosedEmbedding hsmooth.continuous
      (injective_connectedSumTrack hF₁ hF₂)).isEmbedding⟩
  obtain ⟨G, hG⟩ := exists_eventuallyEq_connectedSumTrack hF₁ hF₂ p
  exact (G.isImmersion.isImmersionAt p).congr_of_eventuallyEq hG.symm

/-- The **connected sum** `F₁ # F₂` of a concordance `F₁` from `K₁` to `K₁'` and a concordance
`F₂` from `K₂` to `K₂'`, both in connected-sum position with respect to the great circle `ι`: a
concordance from `K₁ # K₂` to `K₁' # K₂'`. It is `F₁` over the closed upper half of the circle,
and over the open lower half it is `(z, t) ↦ (ρ × id) (F₂ (-z, t))`, the knotted half of `F₂`
turned over the lower hemisphere by the half-turn `ρ` of `E` in the plane `ι ℂ`. -/
def connectedSum (F₁ : Concordance K₁ K₁') (F₂ : Concordance K₂ K₂')
    (hF₁ : F₁.IsConnectedSumPosition ι) (hF₂ : F₂.IsConnectedSumPosition ι) :
    Concordance (SmoothCircleEmbedding.connectedSum K₁ K₂ hF₁.initial hF₂.initial)
      (SmoothCircleEmbedding.connectedSum K₁' K₂' hF₁.final hF₂.final) where
  toSmoothEmbedding := .ofIsSmoothEmbedding _ (isSmoothEmbedding_connectedSumTrack hF₁ hF₂)
  isCollaredTrack_toSmoothEmbedding := by
    rw [coe_ofIsSmoothEmbedding]
    exact isCollaredTrack_connectedSumTrack hF₁ hF₂

variable (hF₁ : F₁.IsConnectedSumPosition ι) (hF₂ : F₂.IsConnectedSumPosition ι)

/-- Over the closed upper half of the circle the connected sum of concordances is the first
concordance. -/
theorem connectedSum_apply_of_im_nonneg {p : Circle × ℝ} (hp : 0 ≤ (p.1 : ℂ).im) :
    F₁.connectedSum F₂ hF₁ hF₂ p = F₁ p := by
  rw [← coe_toSmoothEmbedding, Concordance.connectedSum, coe_ofIsSmoothEmbedding]
  simp [connectedSumTrack, hp]

/-- Over the open lower half of the circle the connected sum of concordances is the second
concordance, turned over by the half-turn `ρ` in the plane `ι ℂ`:
`(F₁ # F₂) (z, t) = (ρ (F₂ (-z, t)).1, (F₂ (-z, t)).2)`. -/
theorem connectedSum_apply_of_im_neg {p : Circle × ℝ} (hp : (p.1 : ℂ).im < 0) :
    F₁.connectedSum F₂ hF₁ hF₂ p =
      Prod.map ((LinearMap.range ι.toLinearMap)ᗮ.reflection.unitSphereDiffeomorph (n := n) (k := n)
        ∞) _root_.id (F₂ (-p.1, p.2)) := by
  rw [← coe_toSmoothEmbedding, Concordance.connectedSum, coe_ofIsSmoothEmbedding]
  simp only [connectedSumTrack, hp.not_ge, ↓reduceIte]
  exact turnOver_apply ι F₂ p

/-- The connected sum of the constant concordances of two knots is the constant concordance of
their connected sum. -/
@[simp]
theorem connectedSum_refl (h₁ : SmoothCircleEmbedding.IsConnectedSumPosition ι K₁)
    (h₂ : SmoothCircleEmbedding.IsConnectedSumPosition ι K₂) :
    (Concordance.refl K₁).connectedSum (Concordance.refl K₂) (isConnectedSumPosition_refl h₁)
      (isConnectedSumPosition_refl h₂) =
      Concordance.refl (SmoothCircleEmbedding.connectedSum K₁ K₂ h₁ h₂) := by
  refine Concordance.ext fun ⟨z, t⟩ => ?_
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ (p := (z, t)) hz, refl_apply, refl_apply,
      SmoothCircleEmbedding.connectedSum_apply_of_im_nonneg _ _ hz]
  · rw [connectedSum_apply_of_im_neg _ _ (p := (z, t)) hz, refl_apply, refl_apply]
    ext
    · simp [coe_connectedSum_apply_of_im_neg _ _ hz]
    · rfl

/-- Reversing the connected sum of two concordances gives the connected sum of the reversed
concordances. -/
theorem symm_connectedSum :
    (F₁.connectedSum F₂ hF₁ hF₂).symm = F₁.symm.connectedSum F₂.symm hF₁.symm hF₂.symm := by
  refine Concordance.ext fun ⟨z, t⟩ => ?_
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [symm_apply, connectedSum_apply_of_im_nonneg hF₁ hF₂ (p := (z, 1 - t)) hz,
      connectedSum_apply_of_im_nonneg hF₁.symm hF₂.symm (p := (z, t)) hz, symm_apply]
  · rw [symm_apply, connectedSum_apply_of_im_neg hF₁ hF₂ (p := (z, 1 - t)) hz,
      connectedSum_apply_of_im_neg hF₁.symm hF₂.symm (p := (z, t)) hz, symm_apply]
    simp [Prod.map_apply']

end Concordance

end SmoothEmbedding

namespace SmoothCircleEmbedding

open SmoothEmbedding

variable {K₁ K₁' K₂ K₂' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
  {F₁ : Concordance K₁ K₁'} {F₂ : Concordance K₂ K₂'}

/-- **The connected sum respects concordance in connected-sum position**: if `K₁` is concordant to
`K₁'` and `K₂` to `K₂'` through concordances in connected-sum position with respect to `ι`, then
`K₁ # K₂` is concordant to `K₁' # K₂'`. -/
theorem concordant_connectedSum (hF₁ : F₁.IsConnectedSumPosition ι)
    (hF₂ : F₂.IsConnectedSumPosition ι) :
    Concordant (connectedSum K₁ K₂ hF₁.initial hF₂.initial)
      (connectedSum K₁' K₂' hF₁.final hF₂.final) :=
  Concordant.of_concordance (F₁.connectedSum F₂ hF₁ hF₂)

/-- Varying the first summand of a connected sum through a concordance in connected-sum position
gives concordant connected sums. -/
theorem concordant_connectedSum_left (hF₁ : F₁.IsConnectedSumPosition ι)
    (h₂ : IsConnectedSumPosition ι K₂) :
    Concordant (connectedSum K₁ K₂ hF₁.initial h₂) (connectedSum K₁' K₂ hF₁.final h₂) :=
  concordant_connectedSum hF₁ (Concordance.isConnectedSumPosition_refl h₂)

/-- Varying the second summand of a connected sum through a concordance in connected-sum position
gives concordant connected sums. -/
theorem concordant_connectedSum_right (h₁ : IsConnectedSumPosition ι K₁)
    (hF₂ : F₂.IsConnectedSumPosition ι) :
    Concordant (connectedSum K₁ K₂ h₁ hF₂.initial) (connectedSum K₁ K₂' h₁ hF₂.final) :=
  concordant_connectedSum (Concordance.isConnectedSumPosition_refl h₁) hF₂

end SmoothCircleEmbedding

end TauCeti
