/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.ConnectedSum.Concordance
public import TauCeti.KnotTheory.ConnectedSum.Position

/-!
# Boosting concordances into connected-sum position

The connected sum of two concordances (`TauCeti.SmoothEmbedding.Concordance.connectedSum`) is
defined for concordances in connected-sum position for a great circle `ι`
(`TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition`): the standard strip
`(z, t) ↦ (ι z, t)` near the closed lower half of the circle, and knotted only over the open upper
hemisphere `⟪x, ι i⟫ > 0`. For the connected sum to be well defined on concordance classes, any
two concordant knots in connected-sum position must be joined by a concordance in connected-sum
position. This file reduces that to a condition near a single arc of the annulus: a concordance
which is the standard strip near the arc `{-i} × ℝ` can be replaced by one in connected-sum
position.

The tool is the conformal boost of the sphere toward `v = ι i` (`TauCeti.sphereBoost`), as for
knots in `TauCeti.KnotTheory.ConnectedSum.Position`.

* **Boosting a concordance.** The boosted concordance
  `TauCeti.SmoothEmbedding.Concordance.boost ι a F` boosts `F` by rapidity `a` in the sphere factor
  and undoes the boost on the parameter circle; it is a concordance from the boosted knot
  `TauCeti.SmoothCircleEmbedding.boost ι a K` to `boost ι a K'`. If `F` is the standard strip on
  `U × ℝ` for a neighbourhood `U` of `-i`, then off `U × ℝ` it avoids the line `{-v} × ℝ`. Being a
  product beyond the times `0` and `1`, its sphere component off `U × ℝ` ranges over the image of
  the compact set `Uᶜ × [0, 1]`. So a large boost carries it into the upper hemisphere, while the
  boost of the parameters blows `U` up over the lower half of the circle
  (`TauCeti.SmoothEmbedding.Concordance.eventually_isConnectedSumPosition_boost`).
* **The boost of a knot in connected-sum position.** For `a ≥ 0` the boosted knot is joined to the
  knot by the concordance `TauCeti.SmoothCircleEmbedding.boostConcordance ι a K`, the joint trace
  of the boost diffeotopies of the sphere and of the circle
  (`TauCeti.SmoothEmbedding.Concordance.ofDiffeotopies`). At every time it is a boost of rapidity
  `b ∈ [0, a]` of the knot, undone on the parameters. Boosting the parameters toward `-i` keeps
  the lower half of the circle in place, where the knot is the great circle and the two boosts
  cancel, and boosting toward `v` raises heights
  (`TauCeti.monotone_inner_sphereBoost`). So this concordance is in connected-sum position as soon
  as the knot is
  (`TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition.boostConcordance`).

Stacking these concordances with the boosted one
(`TauCeti.SmoothEmbedding.Concordance.IsConnectedSumPosition.trans`) joins two knots in
connected-sum position, concordant through a concordance standard near the arc `{-i} × ℝ`, by a
concordance in connected-sum position
(`TauCeti.SmoothCircleEmbedding.exists_concordance_isConnectedSumPosition`). Their connected sums
with any third knot in connected-sum position are then concordant
(`TauCeti.SmoothCircleEmbedding.concordant_connectedSum_left_of_eventually_apply_eq` and its right
version).

Not formalized here: that every concordance between knots in connected-sum position can be
replaced by one which is the standard strip near the arc `{-i} × ℝ`. In `Sⁿ × ℝ` with `n ≥ 3` this
moves the image of that arc onto the straight line `{-v} × ℝ` and the tangent direction of the
annulus along it onto that of the strip, by isotopy extension.

## Main definitions

* `TauCeti.SmoothCircleEmbedding.boostConcordance ι a K`: the concordance from `K` to its boost,
  boosting the sphere and the circle simultaneously.
* `TauCeti.SmoothEmbedding.Concordance.boost ι a F`: a concordance boosted by rapidity `a` toward
  `ι i`, with the boost undone on the parameter circle.

## Main results

* `TauCeti.SmoothCircleEmbedding.IsConnectedSumPosition.boostConcordance`:
  for `a ≥ 0`, the concordance from a knot in connected-sum position to its boost is in
  connected-sum position.
* `TauCeti.SmoothEmbedding.Concordance.eventually_isConnectedSumPosition_boost`: a concordance
  which is the standard strip near the arc `{-i} × ℝ` is in connected-sum position once boosted far
  enough.
* `TauCeti.SmoothCircleEmbedding.exists_concordance_isConnectedSumPosition`: two knots in
  connected-sum position joined by a concordance standard near that arc are joined by a
  concordance in connected-sum position.
* `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_left_of_eventually_apply_eq`,
  `TauCeti.SmoothCircleEmbedding.concordant_connectedSum_right_of_eventually_apply_eq`: varying one
  summand of a connected sum through such a concordance gives concordant connected sums.

## References

* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the concordance group, whose operation is the connected sum).
* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, Graduate Texts in Mathematics 149,
  3rd ed., Springer (2019), Section 4.5 (Möbius transformations of the sphere).
-/

public section

noncomputable section

open Metric Module Set Filter Topology
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}

namespace SmoothCircleEmbedding

/-- **The boost concordance of a knot in connected-sum position is in connected-sum position**, for
a nonnegative rapidity. Boosting the parameters toward `-i` keeps the closed lower half of the
circle, where the knot is the great circle and the two boosts cancel; and boosting the sphere
toward `ι i` keeps the open upper hemisphere. -/
theorem IsConnectedSumPosition.boostConcordance
    {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)} (hK : IsConnectedSumPosition ι K)
    {a : ℝ} (ha : 0 ≤ a) :
    (SmoothCircleEmbedding.boostConcordance ι a K).IsConnectedSumPosition ι := by
  set τ := SmoothEmbedding.Concordance.collaredSmoothTransitionUnit
  set Ψ := circleBoostDiffeotopy (m := ∞) (-a)
  set g : Circle × ℝ → Circle := fun q => Ψ (τ q.2, q.1)
  have hg : Continuous g := Ψ.contMDiff.continuous.comp (by fun_prop)
  have happly (q : Circle × ℝ) : SmoothCircleEmbedding.boostConcordance ι a K q =
      (sphereBoostDiffeotopy (n := n) (m := ∞) ι.norm_map_I a (τ q.2, K (g q)), q.2) :=
    boostConcordance_apply ι a K q
  -- The knot is the great circle on the open set `U`, which contains the closed lower half.
  set U := {z : Circle | ⇑K =ᶠ[𝓝 z] ⇑(greatCircle (n := n) ι)}
  have hUo : IsOpen U := isOpen_setOfPred_eventually_nhds
  have hKU {z : Circle} (hz : z ∈ U) : K z = greatCircle ι z := hz.eq_of_nhds
  -- Boosting the parameters toward `-i` keeps the closed lower half of the circle.
  have him (q : Circle × ℝ) (hq : (q.1 : ℂ).im ≤ 0) : ((g q : Circle) : ℂ).im ≤ 0 := by
    have h := monotone_inner_sphereBoost (v := Complex.I) (x := (q.1 : ℂ)) (by simp)
      (Circle.norm_coe q.1) (by nlinarith [(τ q.2).2.1] : -a * (τ q.2 : ℝ) ≤ 0)
    have hgq : ((g q : Circle) : ℂ) = sphereBoost Complex.I (-a * (τ q.2 : ℝ)) q.1 :=
      coe_circleBoostDiffeotopy_apply _ _
    simp only [sphereBoost_zero, id, Complex.real_inner_I_right] at h
    rw [hgq]
    linarith
  -- Where the knot is the great circle, the boost concordance is the standard strip.
  have hstrip (q : Circle × ℝ) (hq : g q ∈ U) :
      SmoothCircleEmbedding.boostConcordance ι a K q = (greatCircle (n := n) ι q.1, q.2) := by
    rw [happly, hKU hq, sphereBoostDiffeotopy_greatCircle_circleBoostDiffeotopy]
  refine ⟨fun {p} hp => ?_, fun {p} hp => ?_⟩
  · filter_upwards [(hUo.preimage hg).mem_nhds (hK.eventuallyEq_greatCircle (him p hp))]
      with q hq
    exact hstrip q hq
  · by_cases hgp : g p ∈ U
    · rw [hstrip p hgp, coe_greatCircle_apply, ι.inner_map_map, Complex.real_inner_I_right]
      exact hp
    · -- Off `U` the parameter `g p` lies in the open upper half, where the knot is over the upper
      -- hemisphere, which boosting toward `ι i` keeps.
      have hpos : 0 < ⟪(K (g p) : E), ι Complex.I⟫ :=
        hK.inner_pos (not_le.1 fun h => hgp (hK.eventuallyEq_greatCircle h))
      have h := monotone_inner_sphereBoost ι.norm_map_I (norm_eq_of_mem_sphere (K (g p)))
        (mul_nonneg ha (τ p.2).2.1 : (0 : ℝ) ≤ a * (τ p.2 : ℝ))
      simp only [sphereBoost_zero, id] at h
      rw [happly, coe_sphereBoostDiffeotopy_apply]
      exact hpos.trans_le h

end SmoothCircleEmbedding

namespace SmoothEmbedding

namespace Concordance

open SmoothCircleEmbedding

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-! ### Boosting a concordance -/

/-- The **boosted concordance**: a concordance `F` from `K` to `K'` moved by the boost of rapidity
`a` toward `ι i` in the sphere factor, and reparametrized by the boost of rapidity `-a` toward `i`
of the circle. It is a concordance between the boosted knots
`TauCeti.SmoothCircleEmbedding.boost ι a K` and `boost ι a K'`. -/
def boost (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) (F : Concordance K K') :
    Concordance (K.boost ι a) (K'.boost ι a) :=
  (F.transDiffeomorph (sphereBoostDiffeotopy ι.norm_map_I a).final).compDiffeomorph
    (circleBoostDiffeotopy (-a)).final

/-- The boosted concordance boosts `F` after undoing the boost on the parameter circle. -/
theorem boost_apply (ι : ℂ →ₗᵢ[ℝ] E) (a : ℝ) (F : Concordance K K') (p : Circle × ℝ) :
    F.boost ι a p =
      ((sphereBoostDiffeotopy (n := n) (m := ∞) ι.norm_map_I a).final
          (F ((circleBoostDiffeotopy (m := ∞) (-a)).final p.1, p.2)).1,
        (F ((circleBoostDiffeotopy (m := ∞) (-a)).final p.1, p.2)).2) :=
  (compDiffeomorph_apply _ _ p).trans (transDiffeomorph_apply _ _ _)

/-- **Boosting a concordance into connected-sum position.** A concordance which is the standard
strip `(z, t) ↦ (ι z, t)` for all times `t` and all parameters `z` near the bottom point `-i` of
the circle is in connected-sum position for `ι` once boosted far enough toward `ι i`. -/
theorem eventually_isConnectedSumPosition_boost {F : Concordance K K'} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I)
    (hF : ∀ᶠ z in 𝓝 z₀, ∀ t, F (z, t) = (greatCircle (n := n) ι z, t)) :
    ∀ᶠ a in atTop, (F.boost ι a).IsConnectedSumPosition ι := by
  obtain ⟨U, hU, hUo, hz₀U⟩ := _root_.eventually_nhds_iff.1 hF
  -- Off `U × ℝ`, the sphere component of `F` ranges over the image `C` of the compact set
  -- `Uᶜ × [0, 1]`, since `F` is a product beyond the times `0` and `1`.
  set C := (fun p => ((F p).1 : E)) '' (Uᶜ ×ˢ Icc 0 1)
  have hC : IsCompact C := (hUo.isClosed_compl.isCompact.prod isCompact_Icc).image
    (continuous_subtype_val.comp (continuous_fst.comp F.toSmoothEmbedding.contMDiff.continuous))
  have hmemC {z : Circle} (hz : z ∉ U) (t : ℝ) : ((F (z, t)).1 : E) ∈ C := by
    rcases le_or_gt t 0 with ht | ht
    · exact ⟨(z, 0), ⟨hz, le_rfl, zero_le_one⟩, by
        simp [F.isCollaredTrack.apply_of_nonpos z ht, F.apply_zero]⟩
    rcases le_or_gt 1 t with ht' | ht'
    · exact ⟨(z, 1), ⟨hz, zero_le_one, le_rfl⟩, by
        simp [F.isCollaredTrack.apply_of_one_le z ht', F.apply_one]⟩
    · exact ⟨(z, t), ⟨hz, ht.le, ht'.le⟩, rfl⟩
  -- `C` avoids `-ι i`: over `z₀` the concordance is the line `{-ι i} × ℝ`, and `F` is injective.
  have hCv : -ι Complex.I ∉ C := by
    rintro ⟨⟨z, t⟩, ⟨hz, -⟩, hzt⟩
    have heq : F (z₀, (F (z, t)).2) = F (z, t) := by
      rw [hU z₀ hz₀U]
      refine Prod.ext (Subtype.ext ?_) rfl
      rw [coe_greatCircle_apply, hz₀, map_neg]
      exact hzt.symm
    exact hz (congrArg Prod.fst (F.toSmoothEmbedding.isEmbedding.injective heq) ▸ hz₀U)
  have h₁ := hC.eventually_forall_inner_sphereBoost_pos ι.norm_map_I
    (by rintro _ ⟨p, -, rfl⟩; exact norm_eq_of_mem_sphere (F p).1) hCv
  -- Boosting back a parameter `w` with `m w ∉ U` lands in the open upper half of the circle.
  filter_upwards [h₁, eventually_forall_im_pos_of_circleBoostDiffeotopy_final_notMem (m := ∞)
    (hUo.mem_nhds hz₀U) hz₀] with a ha₁ him
  set m := (circleBoostDiffeotopy (m := ∞) (-a)).final
  -- Where the boosted-back parameter lies in `U`, the boosted concordance is the standard strip.
  have hstrip (q : Circle × ℝ) (hq : m q.1 ∈ U) :
      F.boost ι a q = (greatCircle (n := n) ι q.1, q.2) := by
    rw [boost_apply, hU _ hq, Diffeotopy.final_apply, Diffeotopy.final_apply,
      sphereBoostDiffeotopy_greatCircle_circleBoostDiffeotopy]
  refine ⟨fun {p} hp => ?_, fun {p} hp => ?_⟩
  · have hmU : (fun q : Circle × ℝ => m q.1) ⁻¹' U ∈ 𝓝 p :=
      (hUo.preimage (m.continuous.comp continuous_fst)).mem_nhds
        (not_not.1 fun h => (not_le.2 (him p.1 h)) hp)
    filter_upwards [hmU] with q hq
    exact hstrip q hq
  · by_cases hmp : m p.1 ∈ U
    · rw [hstrip p hmp, coe_greatCircle_apply, ι.inner_map_map, Complex.real_inner_I_right]
      exact hp
    · rw [boost_apply, coe_sphereBoostDiffeotopy_final_apply]
      exact ha₁ _ (hmemC hmp p.2)

end Concordance

end SmoothEmbedding

namespace SmoothCircleEmbedding

open SmoothEmbedding

variable {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-! ### Concordances in connected-sum position -/

/-- **Concordances in connected-sum position from concordances standard near an arc.** Two knots
in connected-sum position for `ι`, joined by a concordance which is the standard strip
`(z, t) ↦ (ι z, t)` for all times and all parameters `z` near the bottom point `-i` of the circle,
are joined by a concordance in connected-sum position: boost both knots, through their boost
concordances, and the concordance between them. -/
theorem exists_concordance_isConnectedSumPosition (hK : IsConnectedSumPosition ι K)
    (hK' : IsConnectedSumPosition ι K') {F : Concordance K K'} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I)
    (hF : ∀ᶠ z in 𝓝 z₀, ∀ t, F (z, t) = (greatCircle (n := n) ι z, t)) :
    ∃ G : Concordance K K', G.IsConnectedSumPosition ι := by
  obtain ⟨a, hpos, ha⟩ :=
    ((Concordance.eventually_isConnectedSumPosition_boost hz₀ hF).and
      (eventually_ge_atTop 0)).exists
  exact ⟨(boostConcordance ι a K).trans ((F.boost ι a).trans (boostConcordance ι a K').symm),
    (hK.boostConcordance ha).trans
      (hpos.trans (hK'.boostConcordance ha).symm)⟩

/-- Varying the first summand of a connected sum through a concordance which is the standard strip
near the arc `{-i} × ℝ` gives concordant connected sums. -/
theorem concordant_connectedSum_left_of_eventually_apply_eq {L : SmoothCircleEmbedding (𝓡 n)
    (sphere (0 : E) 1)} (hK : IsConnectedSumPosition ι K) (hK' : IsConnectedSumPosition ι K')
    (hL : IsConnectedSumPosition ι L) {F : Concordance K K'} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I)
    (hF : ∀ᶠ z in 𝓝 z₀, ∀ t, F (z, t) = (greatCircle (n := n) ι z, t)) :
    Concordant (connectedSum K L hK hL) (connectedSum K' L hK' hL) :=
  (exists_concordance_isConnectedSumPosition hK hK' hz₀ hF).elim fun _ hG =>
    concordant_connectedSum_left hG hL

/-- Varying the second summand of a connected sum through a concordance which is the standard
strip near the arc `{-i} × ℝ` gives concordant connected sums. -/
theorem concordant_connectedSum_right_of_eventually_apply_eq {L : SmoothCircleEmbedding (𝓡 n)
    (sphere (0 : E) 1)} (hL : IsConnectedSumPosition ι L) (hK : IsConnectedSumPosition ι K)
    (hK' : IsConnectedSumPosition ι K') {F : Concordance K K'} {z₀ : Circle}
    (hz₀ : (z₀ : ℂ) = -Complex.I)
    (hF : ∀ᶠ z in 𝓝 z₀, ∀ t, F (z, t) = (greatCircle (n := n) ι z, t)) :
    Concordant (connectedSum L K hL hK) (connectedSum L K' hL hK') :=
  (exists_concordance_isConnectedSumPosition hK hK' hz₀ hF).elim fun _ hG =>
    concordant_connectedSum_right hL hG

end SmoothCircleEmbedding

end TauCeti
