/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.KnotTheory.ConnectedSum.Basic
public import TauCeti.Topology.Maps.ClosedCover

/-!
# The connected sum of concordances

Concordance classes of knots form a group under the connected sum. This file supplies the
operation on concordances that this rests on: two concordances, each standard on the lower half of
the circle, have a connected sum, which is a concordance between the connected sums of their ends.

Here a knot is a smooth circle embedding `K : S¹ → Sⁿ` into the unit sphere of a real inner
product space `E` of dimension `n + 1`, and a concordance `F` from `K` to `K'` is a smooth
concordance in collared form (`TauCeti.SmoothEmbedding.Concordance`): a smooth embedding
`F : S¹ × ℝ → Sⁿ × ℝ` which is `K × id` near the initial end and `K' × id` near the final end, so
that its track over `S¹ × [0, 1]` is an annulus in `Sⁿ × [0, 1]`. Fix a great circle, given by a
linear isometry `ι : ℂ →ₗᵢ[ℝ] E`. The concordance `F` is in **connected-sum position**
(`TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition ι F`) when

* near every point `(z, t)` with `Im z ≤ 0`, the track `F` agrees with the product of the great
  circle with the identity, so that the lower half of the annulus is the unknotted strip
  `(lower half of the great circle) × ℝ`;
* the open upper half `Im z > 0` of every level is carried into the open upper hemisphere
  `⟪x, ι i⟫ > 0`.

This is the knot notion `TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition` holding uniformly
along the concordance; in particular both ends of a concordance in connected-sum position are in
connected-sum position. The constant concordance of a knot in connected-sum position, the reversed
concordance and the stacked concordance stay in connected-sum position.

For `F₁` from `K₁` to `K₁'` and `F₂` from `K₂` to `K₂'`, both in connected-sum position,
`TauCeti.SmoothEmbedding.Concordance.connectedSum F₁ F₂` keeps `F₁` over the closed upper half of
the circle and replaces its lower half by `F₂` turned over into the lower hemisphere by the
half-turn `ρ` of `E` in the plane `ι ℂ`, levelwise as for knots:

`(F₁ # F₂) (z, t) = F₁ (z, t)` if `Im z ≥ 0`, and `(F₁ # F₂) (z, t) = (ρ y, s)` if `Im z < 0`,
where `F₂ (-z, t) = (y, s)`.

It is a concordance from `K₁ # K₂` to `K₁' # K₂'`. The track is a smooth embedding since near every
point it is one of three smooth embeddings (`F₁`, the turned-over `F₂`, and the product of the
great circle with the identity), and the great sphere `⟪x, ι i⟫ = 0` splits it into those two
tracks; the source `S¹ × ℝ` is not compact, so the embedding property is glued over the two closed
hemispheres with `Topology.IsEmbedding.of_isClosed_cover`. The connected sum of the constant
concordances is the constant concordance of the connected sum, and it commutes with reversing
concordances.

Not formalized here: that a concordance between knots in connected-sum position can always be
moved into connected-sum position. That is what makes the connected sum of knots in connected-sum
position well defined on their concordance classes.

## Main definitions

* `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition ι F`: the concordance `F` is the
  standard strip over the lower half of the circle, and knotted only in the upper hemisphere.
* `TauCeti.SmoothEmbedding.Concordance.connectedSum`: the connected sum of two concordances in
  connected-sum position.

## Main results

* `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.initial`,
  `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.final`: the ends of a concordance in
  connected-sum position are in connected-sum position.
* `TauCeti.SmoothEmbedding.Concordance.isConnectedSumPosition_refl`,
  `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.symm`,
  `TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.trans`: connected-sum position is
  preserved by the constant, reversed and stacked concordances.
* `TauCeti.SmoothEmbedding.Concordance.sign_inner_connectedSum`: the great sphere `⟪x, ι i⟫ = 0`
  separates the two summands of the connected sum of concordances.
* `TauCeti.SmoothEmbedding.Concordance.refl_connectedSum_refl`,
  `TauCeti.SmoothEmbedding.Concordance.connectedSum_symm`: the connected sum of constant
  concordances is the constant concordance of the connected sum, and reversing a connected sum of
  concordances reverses both summands.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the concordance group, and the connected sum of concordances).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8 (knot
  cobordism, and the group of cobordism classes under the sum of knots).
-/

public section

noncomputable section

open Metric Module Set Filter Topology Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

namespace SmoothEmbedding

namespace Concordance

open SmoothCircleEmbedding (greatCircle coe_greatCircle_apply reflection_greatCircle_neg)

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}
  {K K' K'' K₁ K₁' K₂ K₂' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-! ### Connected-sum position -/

variable (ι) in
/-- A concordance `F` of knots in the unit sphere of `E` is in **connected-sum position** with
respect to the great circle `ι` when, near every point `(z, t)` with `Im z ≤ 0`, it agrees with the
product of the great circle `TauCeti.SmoothCircleEmbedding.greatCircle ι` with the identity, and
it carries every point `(z, t)` with `Im z > 0` into the open hemisphere `⟪x, ι i⟫ > 0`. All the
knotting of the annulus then happens over that hemisphere. -/
structure IsConnectedSumPosition (F : Concordance K K') : Prop where
  /-- Near the closed lower half of the circle the track is the great circle times the line. -/
  eventuallyEq_greatCircle {z : Circle} (hz : (z : ℂ).im ≤ 0) (t : ℝ) :
    ⇑F =ᶠ[𝓝 (z, t)] fun p ↦ (greatCircle (n := n) ι p.1, p.2)
  /-- The open upper half of the circle goes into the open hemisphere `⟪x, ι i⟫ > 0`. -/
  inner_pos {z : Circle} (hz : 0 < (z : ℂ).im) (t : ℝ) : 0 < ⟪((F (z, t)).1 : E), ι Complex.I⟫

variable {F : Concordance K K'} {G : Concordance K' K''}

/-- Over the closed lower half of the circle, a concordance in connected-sum position is the
great circle times the line. -/
theorem IsConnectedSumPosition.apply_eq (h : IsConnectedSumPosition ι F) {z : Circle}
    (hz : (z : ℂ).im ≤ 0) (t : ℝ) : F (z, t) = (greatCircle (n := n) ι z, t) :=
  (h.eventuallyEq_greatCircle hz t).eq_of_nhds

/-- The track of a concordance in connected-sum position meets the great sphere `⟪x, ι i⟫ = 0`
only over `±1`: the height `⟪(F (z, t)).1, ι i⟫` has the sign of `Im z`. -/
theorem IsConnectedSumPosition.sign_inner (h : IsConnectedSumPosition ι F) (z : Circle) (t : ℝ) :
    SignType.sign ⟪((F (z, t)).1 : E), ι Complex.I⟫ = SignType.sign (z : ℂ).im := by
  rcases lt_or_ge 0 (z : ℂ).im with hz | hz
  · rw [sign_pos hz, sign_pos (h.inner_pos hz t)]
  · rw [h.apply_eq hz, coe_greatCircle_apply, ι.inner_map_map, Complex.inner]
    simp

/-- The knot at a fixed level of a concordance in connected-sum position, when that level is a
product level, is in connected-sum position. -/
private theorem IsConnectedSumPosition.isConnectedSumPosition_of_apply
    (h : IsConnectedSumPosition ι F) {L : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} {t : ℝ}
    (hL : ∀ z, F (z, t) = (L z, t)) : SmoothCircleEmbedding.IsConnectedSumPosition ι L where
  eventuallyEq_greatCircle {z} hz := by
    filter_upwards [(Continuous.prodMk_left t).tendsto z |>.eventually
      (h.eventuallyEq_greatCircle hz t)] with w hw
    simpa [hL] using congrArg Prod.fst hw
  inner_pos {z} hz := by simpa [hL] using h.inner_pos hz t

/-- The initial knot of a concordance in connected-sum position is in connected-sum position. -/
theorem IsConnectedSumPosition.initial (h : IsConnectedSumPosition ι F) :
    SmoothCircleEmbedding.IsConnectedSumPosition ι K :=
  h.isConnectedSumPosition_of_apply F.apply_zero

/-- The final knot of a concordance in connected-sum position is in connected-sum position. -/
theorem IsConnectedSumPosition.final (h : IsConnectedSumPosition ι F) :
    SmoothCircleEmbedding.IsConnectedSumPosition ι K' :=
  h.isConnectedSumPosition_of_apply F.apply_one

/-- The constant concordance of a knot in connected-sum position is in connected-sum position. -/
theorem isConnectedSumPosition_refl (h : SmoothCircleEmbedding.IsConnectedSumPosition ι K) :
    IsConnectedSumPosition ι (refl K) where
  eventuallyEq_greatCircle {z} hz t := by
    filter_upwards [continuous_fst.tendsto (z, t) |>.eventually (h.eventuallyEq_greatCircle hz)]
      with p hp
    simp [hp]
  inner_pos {z} hz t := by simpa using h.inner_pos hz

/-- The reversed concordance of a concordance in connected-sum position is in connected-sum
position. -/
theorem IsConnectedSumPosition.symm (h : IsConnectedSumPosition ι F) :
    IsConnectedSumPosition ι F.symm where
  eventuallyEq_greatCircle {z} hz t := by
    have hc : Continuous fun p : Circle × ℝ => (p.1, 1 - p.2) := by fun_prop
    filter_upwards [hc.tendsto (z, t) |>.eventually (h.eventuallyEq_greatCircle hz (1 - t))]
      with ⟨w, s⟩ hp
    simp_all
  inner_pos {z} hz t := by simpa using h.inner_pos hz (1 - t)

/-- The stacked concordance of two concordances in connected-sum position is in connected-sum
position. -/
theorem IsConnectedSumPosition.trans (hF : IsConnectedSumPosition ι F)
    (hG : IsConnectedSumPosition ι G) : IsConnectedSumPosition ι (F.trans G) where
  eventuallyEq_greatCircle {z} hz t := by
    rcases lt_or_ge t (2 / 3) with ht | ht
    · -- Below time `2 / 3` the stacked track is `F` at triple speed.
      have hc : Continuous fun p : Circle × ℝ => (p.1, 3 * p.2) := by fun_prop
      have hlow : IsOpen {p : Circle × ℝ | p.2 < 2 / 3} := isOpen_lt continuous_snd continuous_const
      filter_upwards [hlow.mem_nhds ht, hc.tendsto (z, t) |>.eventually
        (hF.eventuallyEq_greatCircle hz (3 * t))] with p hp hFp
      rw [coe_trans, F.isCollaredTrack.stack_eqOn_lower G.isCollaredTrack hp, conjTime_apply]
      simp only [add_zero] at hFp ⊢
      rw [hFp]
      simp
    · -- From time `1 / 3` on the stacked track is `G` at triple speed.
      have hc : Continuous fun p : Circle × ℝ => (p.1, 3 * p.2 + -2) := by fun_prop
      have hup : IsOpen {p : Circle × ℝ | 1 / 3 < p.2} := isOpen_lt continuous_const continuous_snd
      filter_upwards [hup.mem_nhds (lt_of_lt_of_le (by norm_num) ht),
        hc.tendsto (z, t) |>.eventually (hG.eventuallyEq_greatCircle hz (3 * t + -2))]
        with p hp hGp
      rw [coe_trans, F.isCollaredTrack.stack_eqOn_upper G.isCollaredTrack hp, conjTime_apply]
      rw [hGp]
      ext <;> simp
  inner_pos {z} hz t := by
    rcases le_or_gt t (1 / 2) with ht | ht
    · simpa [trans_apply_of_le F G z ht] using hF.inner_pos hz (3 * t)
    · simpa [trans_apply_of_lt F G z ht] using hG.inner_pos hz (3 * t - 2)

/-! ### The turned-over second summand -/

/-- The half-turn of `E` in the plane `ι ℂ`, as a diffeomorphism of the unit sphere. -/
private abbrev halfTurn (ι : ℂ →ₗᵢ[ℝ] E) : sphere (0 : E) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1 :=
  (LinearMap.range ι.toLinearMap)ᗮ.reflection.unitSphereDiffeomorph (n := n) (k := n) ∞

/-- The track of the second summand of a connected sum of concordances: the track moved into the
lower hemisphere by the half-turn in the plane `ι ℂ`, and reparametrized by the rotation `z ↦ -z`
of the circle, so that its knotted half lies over the lower half of the circle. -/
private def turnOverTrack (ι : ℂ →ₗᵢ[ℝ] E) (F : Concordance K K') :
    SmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (Circle × ℝ) (sphere (0 : E) 1 × ℝ) :=
  ((F.transDiffeomorph (halfTurn (n := n) ι)).compDiffeomorph
    (circleRotationHom (-1))).toSmoothEmbedding

private theorem turnOverTrack_apply (ι : ℂ →ₗᵢ[ℝ] E) (F : Concordance K K') (z : Circle)
    (t : ℝ) : turnOverTrack ι F (z, t) = (halfTurn (n := n) ι (F (-z, t)).1, (F (-z, t)).2) := by
  simp [turnOverTrack]

private theorem coe_fst_turnOverTrack_apply (ι : ℂ →ₗᵢ[ℝ] E) (F : Concordance K K') (z : Circle)
    (t : ℝ) :
    ((turnOverTrack ι F (z, t)).1 : E) =
      (LinearMap.range ι.toLinearMap)ᗮ.reflection ((F (-z, t)).1) := by
  simp [turnOverTrack_apply]

/-- Near the closed upper half of the circle, the turned-over track of a concordance in
connected-sum position is the great circle times the line. -/
private theorem IsConnectedSumPosition.eventuallyEq_turnOverTrack (h : IsConnectedSumPosition ι F)
    {z : Circle} (hz : 0 ≤ (z : ℂ).im) (t : ℝ) :
    ⇑(turnOverTrack ι F) =ᶠ[𝓝 (z, t)] fun p ↦ (greatCircle (n := n) ι p.1, p.2) := by
  have hneg : ((-z : Circle) : ℂ).im ≤ 0 := by simpa using hz
  have hc : Continuous fun p : Circle × ℝ => (-p.1, p.2) := by fun_prop
  filter_upwards [hc.tendsto (z, t) |>.eventually (h.eventuallyEq_greatCircle hneg t)] with p hp
  ext
  · rw [coe_fst_turnOverTrack_apply, hp]
    dsimp only
    rw [reflection_greatCircle_neg, coe_greatCircle_apply]
  · rw [turnOverTrack_apply, hp]

/-! ### The connected sum -/

/-- The underlying map of the connected sum of concordances: `F₁` over the closed upper half of
the circle, and the turned-over `F₂` over the open lower half. -/
private def connectedSumFun (ι : ℂ →ₗᵢ[ℝ] E) (F₁ : Concordance K₁ K₁') (F₂ : Concordance K₂ K₂')
    (p : Circle × ℝ) : sphere (0 : E) 1 × ℝ :=
  if 0 ≤ (p.1 : ℂ).im then F₁ p else turnOverTrack ι F₂ p

variable {F₁ : Concordance K₁ K₁'} {F₂ : Concordance K₂ K₂'}

/-- Over the closed lower half of the circle the connected sum is the turned-over second track. -/
private theorem connectedSumFun_eq_turnOverTrack (h₁ : IsConnectedSumPosition ι F₁)
    (h₂ : IsConnectedSumPosition ι F₂) {p : Circle × ℝ} (hp : (p.1 : ℂ).im ≤ 0) :
    connectedSumFun ι F₁ F₂ p = turnOverTrack ι F₂ p := by
  unfold connectedSumFun
  split_ifs with hp'
  · have h0 : (p.1 : ℂ).im = 0 := le_antisymm hp hp'
    rw [h₁.apply_eq h0.le, (h₂.eventuallyEq_turnOverTrack h0.ge p.2).eq_of_nhds]
  · rfl

/-- Near every point the connected sum of concordances agrees with one of three smooth embeddings:
`F₁` over the open upper half, the turned-over `F₂` over the open lower half, and the great circle
times the line over `±1`. -/
private theorem exists_eventuallyEq_connectedSumFun (h₁ : IsConnectedSumPosition ι F₁)
    (h₂ : IsConnectedSumPosition ι F₂) (p : Circle × ℝ) :
    ∃ G : SmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (Circle × ℝ)
      (sphere (0 : E) 1 × ℝ), connectedSumFun ι F₁ F₂ =ᶠ[𝓝 p] ⇑G := by
  have him : Continuous fun q : Circle × ℝ => (q.1 : ℂ).im := by fun_prop
  rcases lt_trichotomy (p.1 : ℂ).im 0 with hp | hp | hp
  · refine ⟨turnOverTrack ι F₂, ?_⟩
    filter_upwards [(isOpen_lt him continuous_const).mem_nhds hp] with q (hq : (q.1 : ℂ).im < 0)
    simp [connectedSumFun, hq.not_ge]
  · refine ⟨(greatCircle ι).prodMap SmoothEmbedding.id, ?_⟩
    filter_upwards [h₁.eventuallyEq_greatCircle (z := p.1) hp.le p.2,
      h₂.eventuallyEq_turnOverTrack (z := p.1) hp.ge p.2] with q hq₁ hq₂
    rw [coe_prodMap, coe_id]
    unfold connectedSumFun
    split_ifs <;> assumption
  · refine ⟨F₁.toSmoothEmbedding, ?_⟩
    filter_upwards [(isOpen_lt continuous_const him).mem_nhds hp] with q (hq : 0 < (q.1 : ℂ).im)
    simp [connectedSumFun, hq.le]

/-- The height of the connected sum of concordances has the sign of `Im z`. -/
private theorem sign_inner_connectedSumFun (h₁ : IsConnectedSumPosition ι F₁)
    (h₂ : IsConnectedSumPosition ι F₂) (p : Circle × ℝ) :
    SignType.sign ⟪((connectedSumFun ι F₁ F₂ p).1 : E), ι Complex.I⟫ =
      SignType.sign (p.1 : ℂ).im := by
  unfold connectedSumFun
  split_ifs with hp
  · exact h₁.sign_inner p.1 p.2
  · rw [coe_fst_turnOverTrack_apply,
      Submodule.inner_reflection_orthogonal_of_mem (LinearMap.range ι.toLinearMap) _
      (v := ι Complex.I) (LinearMap.mem_range_self _ Complex.I), Left.sign_neg,
      h₂.sign_inner, Circle.coe_neg, Complex.neg_im, Left.sign_neg, neg_neg]

private theorem injective_connectedSumFun (h₁ : IsConnectedSumPosition ι F₁)
    (h₂ : IsConnectedSumPosition ι F₂) : Function.Injective (connectedSumFun ι F₁ F₂) := by
  intro p q hpq
  have hsign : SignType.sign (p.1 : ℂ).im = SignType.sign (q.1 : ℂ).im := by
    rw [← sign_inner_connectedSumFun h₁ h₂, ← sign_inner_connectedSumFun h₁ h₂, hpq]
  rcases le_or_gt (p.1 : ℂ).im 0 with hp | hp
  · have hq : (q.1 : ℂ).im ≤ 0 := by
      rcases hp.lt_or_eq with hp | hp
      · rw [sign_neg hp, eq_comm, sign_eq_neg_one_iff] at hsign
        exact hsign.le
      · rw [hp, sign_zero, eq_comm, sign_eq_zero_iff] at hsign
        exact hsign.le
    rw [connectedSumFun_eq_turnOverTrack h₁ h₂ hp,
      connectedSumFun_eq_turnOverTrack h₁ h₂ hq] at hpq
    exact (turnOverTrack ι F₂).isEmbedding.injective hpq
  · have hq : 0 < (q.1 : ℂ).im := by rwa [sign_pos hp, eq_comm, sign_eq_one_iff] at hsign
    simp only [connectedSumFun, hp.le, hq.le, ↓reduceIte] at hpq
    exact F₁.toSmoothEmbedding.isEmbedding.injective hpq

private theorem isSmoothEmbedding_connectedSumFun (h₁ : IsConnectedSumPosition ι F₁)
    (h₂ : IsConnectedSumPosition ι F₂) :
    IsSmoothEmbedding ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (connectedSumFun ι F₁ F₂) := by
  have hsmooth : ContMDiff ((𝓡 1).prod 𝓘(ℝ)) ((𝓡 n).prod 𝓘(ℝ)) ∞ (connectedSumFun ι F₁ F₂) :=
    fun p ↦ by
      obtain ⟨G, hG⟩ := exists_eventuallyEq_connectedSumFun h₁ h₂ p
      exact G.contMDiff.contMDiffAt.congr_of_eventuallyEq hG
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun p ↦ ?_, ?_⟩
  · obtain ⟨G, hG⟩ := exists_eventuallyEq_connectedSumFun h₁ h₂ p
    exact (G.isImmersion.isImmersionAt p).congr_of_eventuallyEq hG.symm
  -- The closed hemispheres `⟪x, ι i⟫ ≥ 0` and `⟪x, ι i⟫ ≤ 0` cover the target; over the first the
  -- connected sum is `F₁`, over the second it is the turned-over `F₂`.
  have hheight : Continuous fun y : sphere (0 : E) 1 × ℝ => ⟪(y.1 : E), ι Complex.I⟫ := by
    fun_prop
  have hsign := sign_inner_connectedSumFun h₁ h₂
  refine IsEmbedding.of_isClosed_cover hsmooth.continuous (injective_connectedSumFun h₁ h₂)
    (isClosed_le continuous_const hheight) (isClosed_le hheight continuous_const)
    (fun y _ => le_total 0 _) ?_ ?_
  · have heq : connectedSumFun ι F₁ F₂ ∘ ((↑) : connectedSumFun ι F₁ F₂ ⁻¹'
        {y | 0 ≤ ⟪(y.1 : E), ι Complex.I⟫} → Circle × ℝ) = F₁ ∘ (↑) := by
      funext ⟨p, hp⟩
      have hp' : 0 ≤ (p.1 : ℂ).im := by
        rw [← sign_nonneg_iff, ← hsign]
        exact sign_nonneg_iff.2 hp
      simp [connectedSumFun, hp']
    rw [heq]
    exact F₁.toSmoothEmbedding.isEmbedding.isInducing.comp IsInducing.subtypeVal
  · have heq : connectedSumFun ι F₁ F₂ ∘ ((↑) : connectedSumFun ι F₁ F₂ ⁻¹'
        {y | ⟪(y.1 : E), ι Complex.I⟫ ≤ 0} → Circle × ℝ) = turnOverTrack ι F₂ ∘ (↑) := by
      funext ⟨p, hp⟩
      have hp' : (p.1 : ℂ).im ≤ 0 := by
        rw [← sign_nonpos_iff, ← hsign]
        exact sign_nonpos_iff.2 hp
      exact connectedSumFun_eq_turnOverTrack h₁ h₂ hp'
    rw [heq]
    exact (turnOverTrack ι F₂).isEmbedding.isInducing.comp IsInducing.subtypeVal

/-- At a product level of both concordances, the connected sum of concordances is the connected
sum of the two level knots. -/
private theorem connectedSumFun_apply_of_apply (h₁ : IsConnectedSumPosition ι F₁)
    (h₂ : IsConnectedSumPosition ι F₂) {L₁ L₂ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    {t : ℝ} (hL₁ : ∀ z, F₁ (z, t) = (L₁ z, t)) (hL₂ : ∀ z, F₂ (z, t) = (L₂ z, t)) (z : Circle) :
    connectedSumFun ι F₁ F₂ (z, t) =
      (SmoothCircleEmbedding.connectedSum L₁ L₂ (h₁.isConnectedSumPosition_of_apply hL₁)
        (h₂.isConnectedSumPosition_of_apply hL₂) z, t) := by
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · simp [connectedSumFun, hz, hL₁, SmoothCircleEmbedding.connectedSum_apply_of_im_nonneg _ _ hz]
  · simp only [connectedSumFun, hz.not_ge, ↓reduceIte]
    ext
    · rw [coe_fst_turnOverTrack_apply,
        SmoothCircleEmbedding.coe_connectedSum_apply_of_im_neg _ _ hz, hL₂]
    · rw [turnOverTrack_apply, hL₂]

/-- The connected sum of two concordances in connected-sum position is a collared track from the
connected sum of their initial knots to the connected sum of their final knots. -/
private theorem isCollaredTrack_connectedSumFun (h₁ : IsConnectedSumPosition ι F₁)
    (h₂ : IsConnectedSumPosition ι F₂) :
    IsCollaredTrack (SmoothCircleEmbedding.connectedSum K₁ K₂ h₁.initial h₂.initial)
      (SmoothCircleEmbedding.connectedSum K₁' K₂' h₁.final h₂.final)
      (connectedSumFun ι F₁ F₂) where
  exists_pos_apply_eq_left := by
    obtain ⟨ε₁, hε₁, hF₁⟩ := F₁.isCollaredTrack.exists_pos_apply_eq_left
    obtain ⟨ε₂, hε₂, hF₂⟩ := F₂.isCollaredTrack.exists_pos_apply_eq_left
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z t ht => ?_⟩
    exact connectedSumFun_apply_of_apply h₁ h₂ (fun w => hF₁ w t (ht.trans (min_le_left _ _)))
      (fun w => hF₂ w t (ht.trans (min_le_right _ _))) z
  exists_pos_apply_eq_right := by
    obtain ⟨ε₁, hε₁, hF₁⟩ := F₁.isCollaredTrack.exists_pos_apply_eq_right
    obtain ⟨ε₂, hε₂, hF₂⟩ := F₂.isCollaredTrack.exists_pos_apply_eq_right
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z t ht => ?_⟩
    exact connectedSumFun_apply_of_apply h₁ h₂
      (fun w => hF₁ w t ((sub_le_sub_left (min_le_left _ _) 1).trans ht))
      (fun w => hF₂ w t ((sub_le_sub_left (min_le_right _ _) 1).trans ht)) z
  snd_apply_mem_Ioo z t ht := by
    unfold connectedSumFun
    split_ifs
    · exact F₁.isCollaredTrack.snd_apply_mem_Ioo z t ht
    · rw [turnOverTrack_apply]
      exact F₂.isCollaredTrack.snd_apply_mem_Ioo (-z) t ht

/-- The **connected sum** `F₁ # F₂` of two concordances in connected-sum position with respect to
the great circle `ι`, a concordance from `K₁ # K₂` to `K₁' # K₂'`. Over the closed upper half of
the circle it is `F₁`, and over the open lower half it is `F₂` turned over levelwise into the lower
hemisphere: `(F₁ # F₂) (z, t) = (ρ y, s)` where `F₂ (-z, t) = (y, s)` and `ρ` is the half-turn of
`E` in the plane `ι ℂ`. -/
def connectedSum (F₁ : Concordance K₁ K₁') (F₂ : Concordance K₂ K₂')
    (h₁ : IsConnectedSumPosition ι F₁) (h₂ : IsConnectedSumPosition ι F₂) :
    Concordance (SmoothCircleEmbedding.connectedSum K₁ K₂ h₁.initial h₂.initial)
      (SmoothCircleEmbedding.connectedSum K₁' K₂' h₁.final h₂.final) where
  toSmoothEmbedding := .ofIsSmoothEmbedding _ (isSmoothEmbedding_connectedSumFun h₁ h₂)
  isCollaredTrack_toSmoothEmbedding := by
    rw [coe_ofIsSmoothEmbedding]
    exact isCollaredTrack_connectedSumFun h₁ h₂

variable (h₁ : IsConnectedSumPosition ι F₁) (h₂ : IsConnectedSumPosition ι F₂)

private theorem coe_connectedSum : ⇑(connectedSum F₁ F₂ h₁ h₂) = connectedSumFun ι F₁ F₂ :=
  coe_ofIsSmoothEmbedding _ _

/-- Over the closed upper half of the circle the connected sum of concordances is the first
concordance. -/
theorem connectedSum_apply_of_im_nonneg {z : Circle} (hz : 0 ≤ (z : ℂ).im) (t : ℝ) :
    connectedSum F₁ F₂ h₁ h₂ (z, t) = F₁ (z, t) := by
  simp [coe_connectedSum, connectedSumFun, hz]

/-- Over the open lower half of the circle the knot component of the connected sum of
concordances is that of the second concordance, turned over by the half-turn in the plane
`ι ℂ`. -/
theorem coe_fst_connectedSum_apply_of_im_neg {z : Circle} (hz : (z : ℂ).im < 0) (t : ℝ) :
    ((connectedSum F₁ F₂ h₁ h₂ (z, t)).1 : E) =
      (LinearMap.range ι.toLinearMap)ᗮ.reflection ((F₂ (-z, t)).1) := by
  simp [coe_connectedSum, connectedSumFun, hz.not_ge, coe_fst_turnOverTrack_apply]

/-- Over the open lower half of the circle the time component of the connected sum of
concordances is that of the second concordance. -/
theorem snd_connectedSum_apply_of_im_neg {z : Circle} (hz : (z : ℂ).im < 0) (t : ℝ) :
    (connectedSum F₁ F₂ h₁ h₂ (z, t)).2 = (F₂ (-z, t)).2 := by
  simp [coe_connectedSum, connectedSumFun, hz.not_ge, turnOverTrack_apply]

/-- **The great sphere splits the connected sum of concordances into its two summands**: the
height `⟪((F₁ # F₂) (z, t)).1, ι i⟫` has the sign of `Im z`, so the annulus meets the great sphere
`⟪x, ι i⟫ = 0` times the line exactly over `±1`, with `F₁` above it and `F₂` below. -/
theorem sign_inner_connectedSum (z : Circle) (t : ℝ) :
    SignType.sign ⟪((connectedSum F₁ F₂ h₁ h₂ (z, t)).1 : E), ι Complex.I⟫ =
      SignType.sign (z : ℂ).im := by
  rw [coe_connectedSum]
  exact sign_inner_connectedSumFun h₁ h₂ (z, t)

/-- Reversing the connected sum of two concordances reverses both summands. -/
@[simp]
theorem connectedSum_symm :
    (connectedSum F₁ F₂ h₁ h₂).symm = connectedSum F₁.symm F₂.symm h₁.symm h₂.symm := by
  ext ⟨z, t⟩ : 1
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [symm_apply, connectedSum_apply_of_im_nonneg _ _ hz, connectedSum_apply_of_im_nonneg _ _ hz,
      symm_apply]
  · refine Prod.ext (Subtype.ext ?_) ?_
    · rw [symm_apply, coe_fst_connectedSum_apply_of_im_neg _ _ hz,
        coe_fst_connectedSum_apply_of_im_neg _ _ hz, symm_apply]
    · rw [symm_apply, snd_connectedSum_apply_of_im_neg _ _ hz,
        snd_connectedSum_apply_of_im_neg _ _ hz, symm_apply]

/-- **The connected sum of constant concordances** is the constant concordance of the connected
sum. -/
@[simp]
theorem refl_connectedSum_refl (hK₁ : SmoothCircleEmbedding.IsConnectedSumPosition ι K₁)
    (hK₂ : SmoothCircleEmbedding.IsConnectedSumPosition ι K₂) :
    connectedSum (refl K₁) (refl K₂) (isConnectedSumPosition_refl hK₁)
      (isConnectedSumPosition_refl hK₂) = refl (SmoothCircleEmbedding.connectedSum K₁ K₂ hK₁ hK₂) :=
  ext fun ⟨z, t⟩ => by
    rw [coe_connectedSum, connectedSumFun_apply_of_apply (isConnectedSumPosition_refl hK₁)
      (isConnectedSumPosition_refl hK₂) (refl_apply K₁ ⟨·, t⟩) (refl_apply K₂ ⟨·, t⟩), refl_apply]

end Concordance

end SmoothEmbedding

end TauCeti
