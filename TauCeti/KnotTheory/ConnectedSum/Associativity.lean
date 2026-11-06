/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Inner
public import TauCeti.KnotTheory.ConnectedSum.BoostConcordance

/-!
# Associativity of the connected sum of knots up to concordance

The connected sum `TauCeti.SmoothCircleEmbedding.connectedSum` of two knots `K₁`, `K₂` in the unit
sphere of `E`, in connected-sum position for a great circle `ι`, keeps `K₁` over the upper half of
the circle and puts `K₂`, turned over by the half-turn of the plane `ι ℂ`, over the lower half. The
result is not in connected-sum position again, so `(K₁ # K₂) # K₃` only makes sense after `K₁ # K₂`
is replaced by a concordant knot in connected-sum position. This file proves that such
replacements can be chosen so that the two bracketings agree up to concordance
(`TauCeti.SmoothCircleEmbedding.exists_concordant_connectedSum_assoc`): there are knots `P` and
`Q` in connected-sum position, concordant to `K₁ # K₂` and to `K₂ # K₃`, with `P # K₃` concordant
to `K₁ # Q`. Together with the independence of the connected sum from the representatives in
connected-sum position, this is the associativity of the knot concordance group.

The proof slides knotted arcs along the great circle.

* **Small caps.** Boosting a knot in connected-sum position toward `ι i`
  (`TauCeti.SmoothCircleEmbedding.boost`) concentrates its knotting: for large rapidity the boosted
  knot is the great circle outside the arc `Im z > r` around `i`, and carries that arc into the cap
  `⟪x, ι i⟫ > r` around `ι i`, for any `r < 1`. The boost concordance is in connected-sum position,
  so this changes connected sums only up to concordance.
* **Sliding.** The rotation of `E` by `c ∈ S¹` in the plane `ι ℂ`
  (`LinearIsometry.planeRotation`), with the parameter rotated back by `c⁻¹`, slides such a knot
  along the great circle, moving its arc and its cap to the arc and the cap around `c i`.
* **Cap sums.** Knots `K_j` slid by `c_j` whose caps are pairwise disjoint, which happens when
  `⟪c_j, c_k⟫ < 2 r² - 1`, superpose to a single knot `ι + ∑_j (c_j • K_j - ι)`: near each of the
  arcs it is the slid knot `c_j • K_j`, and elsewhere it is the great circle. Moving the points
  `c_j` along paths that keep the caps disjoint is a smooth isotopy of cap sums.

The connected sum of two small-cap knots is their cap sum at `1` and `-1`. Sliding the second cap
from `-1` to `ω = exp (7πi/4)` puts it into the upper hemisphere next to the first, which gives the
knot `P` in connected-sum position; likewise `Q`. Then `P # K₃` is the cap sum of `K₁`, `K₂`, `K₃`
at `1`, `ω`, `-1`, and `K₁ # Q` is their cap sum at `1`, `-1`, `-ω`. The three caps come in the
same cyclic order, so sliding the second cap from `-1` to `ω` and the third from `-ω` to `-1`,
which keeps the caps disjoint throughout, is a smooth isotopy from one to the other.

## Main results

* `TauCeti.SmoothCircleEmbedding.exists_concordant_connectedSum_assoc`: the connected sum of knots
  in connected-sum position is associative up to concordance and the choice of representatives in
  connected-sum position.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 (the
  sum of knots is associative) and Chapter 8 (the concordance group).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the concordance group, whose operation is the connected sum).
-/

public section

noncomputable section

open Metric Module Set Filter Topology Real Manifold
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

namespace SmoothCircleEmbedding

attribute [local instance] finrank_real_complex_fact'

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {ι : ℂ →ₗᵢ[ℝ] E}

/-! ### Sliding a knot along the great circle -/

variable (ι) in
/-- The knot `K` slid along the great circle `ι` by `c`: moved by the rotation by `c` of the plane
`ι ℂ`, and reparametrized by the rotation by `c⁻¹` of the circle. -/
private def slide (c : Circle) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  (K.rotate c⁻¹).transDiffeomorph ((ι.planeRotation c).unitSphereDiffeomorph (n := n) (k := n) ∞)

private theorem coe_slide_apply (c : Circle) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
    (z : Circle) : (slide ι c K z : E) = ι.planeRotation c (K (c⁻¹ * z)) := by
  simp [slide]

/-- Sliding by `1` does not move the knot. -/
private theorem slide_one_apply (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
    (z : Circle) : slide ι 1 K z = K z := by
  ext
  simp [coe_slide_apply]

/-- Turning a slid knot over, at the antipodal parameter, slides it by `-c`. -/
private theorem reflection_slide_neg (c : Circle)
    (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) (z : Circle) :
    ι.rangeᗮ.reflection (slide ι c K (-z) : E) = slide ι (-c) K z := by
  have hz : c⁻¹ * -z = (-c)⁻¹ * z := by
    apply Subtype.ext
    simp only [Circle.coe_mul, Circle.coe_inv, Circle.coe_neg, inv_neg, neg_mul, mul_neg]
  have hR : ι.planeRotation (-c) = ι.planeRotation (-1) * ι.planeRotation c := by
    rw [← map_mul, neg_one_mul]
  rw [coe_slide_apply, coe_slide_apply, ← ι.planeRotation_neg_one, hz, hR,
    LinearIsometryEquiv.coe_mul, Function.comp_apply]

/-! ### Knots knotted in a small cap -/

variable (ι) in
/-- A knot is in **`r`-cap position** for the great circle `ι` when it is the great circle outside
the arc `Im z > r` of the circle, and carries that arc into the cap `⟪x, ι i⟫ > r`. -/
private structure IsCapPosition (r : ℝ) (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) :
    Prop where
  apply_eq {z : Circle} (hz : (z : ℂ).im ≤ r) : K z = greatCircle (n := n) ι z
  lt_inner {z : Circle} (hz : r < (z : ℂ).im) : r < ⟪(K z : E), ι Complex.I⟫

variable {r : ℝ} {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- Outside its arc around `c i`, a slid knot in cap position is the great circle. -/
private theorem IsCapPosition.coe_slide_apply_of_le (hK : IsCapPosition ι r K) {c z : Circle}
    (hz : ⟪(z : ℂ), (c : ℂ) * Complex.I⟫ ≤ r) : (slide ι c K z : E) = ι z := by
  rw [coe_slide_apply, hK.apply_eq (by rwa [Circle.im_inv_mul_eq_inner]), coe_greatCircle_apply,
    LinearIsometry.planeRotation_apply_map, ← Circle.coe_mul, mul_inv_cancel_left]

/-- A slid knot in cap position is in the cap around `ι (c i)` exactly over the arc around `c i`. -/
private theorem IsCapPosition.lt_inner_slide_iff (hK : IsCapPosition ι r K) (c z : Circle) :
    r < ⟪(slide ι c K z : E), ι ((c : ℂ) * Complex.I)⟫ ↔ r < ⟪(z : ℂ), (c : ℂ) * Complex.I⟫ := by
  have hinner : ⟪(slide ι c K z : E), ι ((c : ℂ) * Complex.I)⟫ =
      ⟪(K (c⁻¹ * z) : E), ι Complex.I⟫ := by
    rw [coe_slide_apply, ← LinearIsometry.planeRotation_apply_map,
      LinearIsometryEquiv.inner_map_map]
  rw [hinner, ← Circle.im_inv_mul_eq_inner]
  refine ⟨fun h => not_le.1 fun h' => h.not_ge ?_, hK.lt_inner⟩
  rw [hK.apply_eq h', coe_greatCircle_apply, ι.inner_map_map, Complex.real_inner_I_right]
  exact h'

/-- A knot in cap position for some `r > 0` is in connected-sum position. -/
private theorem IsCapPosition.isConnectedSumPosition (hK : IsCapPosition ι r K) (hr : 0 < r) :
    IsConnectedSumPosition ι K where
  eventuallyEq_greatCircle {z} hz := by
    filter_upwards [(Complex.continuous_im.comp continuous_subtype_val).continuousAt.eventually
      (gt_mem_nhds (hz.trans_lt hr))] with w hw using hK.apply_eq hw.le
  inner_pos {z} hz := by
    rcases le_or_gt (z : ℂ).im r with h | h
    · rwa [hK.apply_eq h, coe_greatCircle_apply, ι.inner_map_map, Complex.real_inner_I_right]
    · exact hr.trans (hK.lt_inner h)

/-! ### Boosting a knot into a small cap -/

/-- **Boosting a knot into a small cap.** For `r < 1`, a large enough boost toward `ι i` puts a
knot in connected-sum position into `r`-cap position. -/
private theorem IsConnectedSumPosition.eventually_isCapPosition_boost
    (hK : IsConnectedSumPosition ι K) (hr : r < 1) :
    ∀ᶠ a in atTop, IsCapPosition ι r (boost ι a K) := by
  -- The knot is the great circle on the open set `U`, which contains the closed lower half.
  set U := {z : Circle | ⇑K =ᶠ[𝓝 z] ⇑(greatCircle (n := n) ι)}
  have hUo : IsOpen U := isOpen_setOfPred_eventually_nhds
  have hKU {z : Circle} (hz : z ∈ U) : K z = greatCircle ι z := hz.eq_of_nhds
  have hUc {z : Circle} (hz : z ∉ U) : 0 < (z : ℂ).im :=
    not_le.1 fun h => hz (hK.eventuallyEq_greatCircle h)
  set z₀ : Circle := ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩
  have hz₀ : (z₀ : ℂ) = -Complex.I := rfl
  have hz₀U : z₀ ∈ U := hK.eventuallyEq_greatCircle (by simp [hz₀])
  -- The knotted part `K (Uᶜ)` is compact and lies in the open upper hemisphere.
  set C := (fun z => (K z : E)) '' Uᶜ
  have hC : IsCompact C :=
    hUo.isClosed_compl.isCompact.image (continuous_subtype_val.comp K.contMDiff.continuous)
  have hCv : -ι Complex.I ∉ C := by
    rintro ⟨z, hz, hzv⟩
    have h := hK.inner_pos (hUc hz)
    simp only at hzv
    rw [hzv, inner_neg_left, real_inner_self_eq_norm_sq, ι.norm_map_I] at h
    norm_num at h
  filter_upwards [hC.eventually_forall_lt_inner_sphereBoost ι.norm_map_I
      (by rintro _ ⟨z, -, rfl⟩; exact norm_eq_of_mem_sphere (K z)) hCv hr,
    eventually_forall_lt_im_of_circleBoostDiffeotopy_final_notMem (m := ∞)
      (hUo.mem_nhds hz₀U) hz₀ hr] with a ha hparam
  set ψ := (circleBoostDiffeotopy (m := ∞) (-a)).final
  -- Where the boosted-back parameter lies in `U`, the boosted knot is the great circle.
  have hstd {w : Circle} (hw : ψ w ∈ U) : boost ι a K w = greatCircle (n := n) ι w := by
    ext
    rw [coe_boost_apply, hKU hw, coe_greatCircle_apply, coe_greatCircle_apply,
      LinearIsometry.sphereBoost_map, sphereBoost_circleBoostDiffeotopy_final_neg]
  refine ⟨fun {w} hw => hstd (not_not.1 fun h => (hparam w h).not_ge hw), fun {w} hw => ?_⟩
  by_cases hψ : ψ w ∈ U
  · rwa [hstd hψ, coe_greatCircle_apply, ι.inner_map_map, Complex.real_inner_I_right]
  · rw [coe_boost_apply]
    exact ha _ ⟨_, hψ, rfl⟩

/-! ### Cap sums -/

variable {m : ℕ}

variable (ι) in
/-- The superposition of the knots `K j` slid by `c j`: the great circle, plus the displacement of
each slid knot from the great circle. -/
private def capSumFun (c : Fin m → Circle) (K : Fin m → SmoothCircleEmbedding (𝓡 n)
    (sphere (0 : E) 1)) (z : Circle) : E :=
  ι z + ∑ j, ((slide ι (c j) (K j) z : E) - ι z)

variable (ι) in
/-- A **cap configuration**: the knots `K j` are in `r`-cap position, `r > 0`, and the caps around
the points `ι (c j i)` are pairwise disjoint. -/
private structure IsCapConfig (r : ℝ) (c : Fin m → Circle)
    (K : Fin m → SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) : Prop where
  pos : 0 < r
  isCapPosition (j : Fin m) : IsCapPosition ι r (K j)
  inner_lt {j k : Fin m} (hjk : j ≠ k) : ⟪(c j : ℂ), (c k : ℂ)⟫ < 2 * r ^ 2 - 1

variable {c : Fin m → Circle} {Ks : Fin m → SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The closed arcs around the points `c j i` of a cap configuration are disjoint. -/
private theorem IsCapConfig.inner_lt_of_le (h : IsCapConfig ι r c Ks) {j k : Fin m} (hjk : j ≠ k)
    {z : Circle} (hz : r ≤ ⟪(z : ℂ), (c j : ℂ) * Complex.I⟫) :
    ⟪(z : ℂ), (c k : ℂ) * Complex.I⟫ < r :=
  inner_lt_of_le_inner (Circle.norm_coe z) (by simp) (by simp) h.pos
    (by rw [mul_comm _ Complex.I, mul_comm _ Complex.I,
      Complex.inner_mul_mul_of_norm_eq_one Complex.norm_I]; exact h.inner_lt hjk) hz

/-- The closed caps around the points `ι (c j i)` of a cap configuration are disjoint. -/
private theorem IsCapConfig.inner_lt_of_le' (h : IsCapConfig ι r c Ks) {j k : Fin m} (hjk : j ≠ k)
    {x : E} (hx : ‖x‖ = 1) (hxj : r ≤ ⟪x, ι ((c j : ℂ) * Complex.I)⟫) :
    ⟪x, ι ((c k : ℂ) * Complex.I)⟫ < r :=
  inner_lt_of_le_inner hx (by simp) (by simp) h.pos
    (by rw [ι.inner_map_map, mul_comm _ Complex.I, mul_comm _ Complex.I,
      Complex.inner_mul_mul_of_norm_eq_one Complex.norm_I]; exact h.inner_lt hjk) hxj

/-- Off the closed arcs around the points `c k i`, `k ≠ j`, the cap sum is the `j`-th slid
knot. -/
private theorem IsCapConfig.capSumFun_eq_slide (h : IsCapConfig ι r c Ks) (j : Fin m) {z : Circle}
    (hz : ∀ k, k ≠ j → ⟪(z : ℂ), (c k : ℂ) * Complex.I⟫ ≤ r) :
    capSumFun ι c Ks z = slide ι (c j) (Ks j) z := by
  rw [capSumFun, Finset.sum_eq_single j (fun k _ hk => by
    rw [(h.isCapPosition k).coe_slide_apply_of_le (hz k hk), sub_self]) (by simp)]
  abel

/-- Off all the closed arcs, the cap sum is the great circle. -/
private theorem IsCapConfig.capSumFun_eq (h : IsCapConfig ι r c Ks) {z : Circle}
    (hz : ∀ k, ⟪(z : ℂ), (c k : ℂ) * Complex.I⟫ ≤ r) : capSumFun ι c Ks z = ι z := by
  rw [capSumFun, Finset.sum_eq_zero (fun k _ => by
    rw [(h.isCapPosition k).coe_slide_apply_of_le (hz k), sub_self]), add_zero]

/-- Near a point off all the closed arcs, the cap sum is the great circle. -/
private theorem IsCapConfig.eventually_capSumFun_eq (h : IsCapConfig ι r c Ks) {z : Circle}
    (hz : ∀ k, ⟪(z : ℂ), (c k : ℂ) * Complex.I⟫ < r) :
    ∀ᶠ w in 𝓝 z, capSumFun ι c Ks w = greatCircle (n := n) ι w := by
  filter_upwards [eventually_all.2 fun k =>
    (continuous_subtype_val.inner continuous_const).continuousAt.eventually
      (gt_mem_nhds (hz k))] with w hw
  rw [h.capSumFun_eq fun k => (hw k).le, coe_greatCircle_apply]

/-- Near every point, the cap sum is either one of the slid knots or the great circle. -/
private theorem IsCapConfig.exists_eventually_capSumFun_eq (h : IsCapConfig ι r c Ks)
    (z : Circle) : ∃ G : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1),
      ∀ᶠ w in 𝓝 z, capSumFun ι c Ks w = G w := by
  by_cases hj : ∃ j, r ≤ ⟪(z : ℂ), (c j : ℂ) * Complex.I⟫
  · obtain ⟨j, hj⟩ := hj
    refine ⟨slide ι (c j) (Ks j), ?_⟩
    filter_upwards [eventually_all.2 fun k : Fin m => eventually_imp_distrib_left.2 fun hkj =>
      (continuous_subtype_val.inner continuous_const).continuousAt.eventually
        (gt_mem_nhds (h.inner_lt_of_le (Ne.symm hkj) hj))] with w hw
    exact h.capSumFun_eq_slide j fun k hk => (hw k hk).le
  · push Not at hj
    exact ⟨greatCircle ι, h.eventually_capSumFun_eq hj⟩

private theorem IsCapConfig.capSumFun_mem_sphere (h : IsCapConfig ι r c Ks) (z : Circle) :
    capSumFun ι c Ks z ∈ sphere (0 : E) 1 := by
  obtain ⟨G, hG⟩ := h.exists_eventually_capSumFun_eq z
  rw [hG.self_of_nhds]
  exact (G z).2

/-- The cap sum is in the cap around `ι (c j i)` exactly over the arc around `c j i`. -/
private theorem IsCapConfig.lt_inner_capSumFun_iff (h : IsCapConfig ι r c Ks) (j : Fin m)
    (z : Circle) :
    r < ⟪capSumFun ι c Ks z, ι ((c j : ℂ) * Complex.I)⟫ ↔
      r < ⟪(z : ℂ), (c j : ℂ) * Complex.I⟫ := by
  by_cases hk : ∃ k, r ≤ ⟪(z : ℂ), (c k : ℂ) * Complex.I⟫
  · obtain ⟨k, hk⟩ := hk
    rw [h.capSumFun_eq_slide k fun l hl => (h.inner_lt_of_le (Ne.symm hl) hk).le]
    rcases eq_or_ne j k with rfl | hjk
    · exact (h.isCapPosition j).lt_inner_slide_iff _ _
    refine iff_of_false (fun hlt => ?_) (h.inner_lt_of_le (Ne.symm hjk) hk).not_gt
    by_cases hs : r ≤ ⟪(slide ι (c k) (Ks k) z : E), ι ((c k : ℂ) * Complex.I)⟫
    · exact (h.inner_lt_of_le' (Ne.symm hjk) (norm_eq_of_mem_sphere _) hs).not_gt hlt
    · have hzk : ⟪(z : ℂ), (c k : ℂ) * Complex.I⟫ ≤ r :=
        not_lt.1 fun h' => hs ((h.isCapPosition k).lt_inner_slide_iff _ _ |>.2 h').le
      rw [(h.isCapPosition k).coe_slide_apply_of_le hzk, ι.inner_map_map] at hlt
      exact (h.inner_lt_of_le (Ne.symm hjk) hk).not_gt hlt
  · push Not at hk
    rw [h.capSumFun_eq fun k => (hk k).le, ι.inner_map_map]

private theorem IsCapConfig.injective_capSumFun (h : IsCapConfig ι r c Ks) :
    Function.Injective (capSumFun ι c Ks) := by
  intro z w hzw
  by_cases hj : ∃ j, r < ⟪(z : ℂ), (c j : ℂ) * Complex.I⟫
  · obtain ⟨j, hj⟩ := hj
    have hj' : r < ⟪(w : ℂ), (c j : ℂ) * Complex.I⟫ :=
      (h.lt_inner_capSumFun_iff j w).1 (hzw ▸ (h.lt_inner_capSumFun_iff j z).2 hj)
    rw [h.capSumFun_eq_slide j fun k hk => (h.inner_lt_of_le (Ne.symm hk) hj.le).le,
      h.capSumFun_eq_slide j fun k hk => (h.inner_lt_of_le (Ne.symm hk) hj'.le).le] at hzw
    exact (slide ι (c j) (Ks j)).isEmbedding.injective (Subtype.ext hzw)
  · push Not at hj
    have hj' : ∀ k, ⟪(w : ℂ), (c k : ℂ) * Complex.I⟫ ≤ r := fun k => not_lt.1 fun h' =>
      (hj k).not_gt ((h.lt_inner_capSumFun_iff k z).1 (hzw ▸ (h.lt_inner_capSumFun_iff k w).2 h'))
    rw [h.capSumFun_eq hj, h.capSumFun_eq hj'] at hzw
    exact Subtype.ext (ι.injective hzw)

/-- The cap sum as a map into the sphere. -/
private def capSumSphere (h : IsCapConfig ι r c Ks) (z : Circle) : sphere (0 : E) 1 :=
  ⟨capSumFun ι c Ks z, h.capSumFun_mem_sphere z⟩

private theorem isSmoothEmbedding_capSumSphere (h : IsCapConfig ι r c Ks) :
    IsSmoothEmbedding (𝓡 1) (𝓡 n) ∞ (capSumSphere h) := by
  have hloc (z : Circle) : ∃ G : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1),
      capSumSphere h =ᶠ[𝓝 z] ⇑G := by
    obtain ⟨G, hG⟩ := h.exists_eventually_capSumFun_eq z
    exact ⟨G, hG.mono fun w hw => Subtype.ext hw⟩
  have hsmooth : ContMDiff (𝓡 1) (𝓡 n) ∞ (capSumSphere h) := fun z ↦ by
    obtain ⟨G, hG⟩ := hloc z
    exact G.contMDiff.contMDiffAt.congr_of_eventuallyEq hG
  refine ⟨isImmersion_iff_forall_isImmersionAt.2 fun z ↦ ?_,
    (hsmooth.continuous.isClosedEmbedding fun z w hzw =>
      h.injective_capSumFun (congrArg Subtype.val hzw)).isEmbedding⟩
  obtain ⟨G, hG⟩ := hloc z
  exact (G.isImmersion.isImmersionAt z).congr_of_eventuallyEq hG.symm

/-- The **cap sum** of a cap configuration. -/
private def capSum (h : IsCapConfig ι r c Ks) : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1) :=
  SmoothEmbedding.ofIsSmoothEmbedding _ (isSmoothEmbedding_capSumSphere h)

private theorem coe_capSum_apply (h : IsCapConfig ι r c Ks) (z : Circle) :
    (capSum h z : E) = capSumFun ι c Ks z := by
  rw [capSum, SmoothEmbedding.ofIsSmoothEmbedding_apply]
  rfl

/-- A cap sum whose caps lie in the upper hemisphere is in connected-sum position. -/
private theorem IsCapConfig.isConnectedSumPosition_capSum (h : IsCapConfig ι r c Ks)
    (hc : ∀ j, 0 ≤ (c j : ℂ).re) (hc' : ∀ j, 1 - (c j : ℂ).re ^ 2 < r ^ 2) :
    IsConnectedSumPosition ι (capSum h) := by
  have hcu (j : Fin m) : ⟪ι ((c j : ℂ) * Complex.I), ι Complex.I⟫ = (c j : ℂ).re := by
    rw [ι.inner_map_map, Complex.real_inner_I_right]
    simp
  -- Every closed arc lies in the open upper half of the circle.
  have harc {z : Circle} (j : Fin m) (hz : r ≤ ⟪(z : ℂ), (c j : ℂ) * Complex.I⟫) :
      0 < (z : ℂ).im :=
    Circle.im_pos_of_le_inner h.pos (hc j) (hc' j) hz
  refine ⟨fun {z} hz => ?_, fun {z} hz => ?_⟩
  · have hz' : ∀ k, ⟪(z : ℂ), (c k : ℂ) * Complex.I⟫ < r := fun k =>
      not_le.1 fun h' => (harc k h').not_ge hz
    filter_upwards [h.eventually_capSumFun_eq hz'] with w hw
    exact Subtype.ext ((coe_capSum_apply h w).trans hw)
  · by_cases hj : ∃ j, r < ⟪(z : ℂ), (c j : ℂ) * Complex.I⟫
    · obtain ⟨j, hj⟩ := hj
      rw [coe_capSum_apply]
      exact inner_pos_of_le_inner (u := ι Complex.I)
        (mem_sphere_zero_iff_norm.1 (h.capSumFun_mem_sphere z)) (by simp)
        (by simp) h.pos (by rw [hcu]; exact hc j) (by rw [hcu]; exact hc' j)
        ((h.lt_inner_capSumFun_iff j z).2 hj).le
    · push Not at hj
      rwa [coe_capSum_apply, h.capSumFun_eq hj, ι.inner_map_map, Complex.real_inner_I_right]

/-! ### Sliding caps is an isotopy -/

/-- **Moving the caps is a smooth isotopy.** Moving the points of a cap configuration along smooth
paths which keep the caps disjoint is a smooth isotopy of cap sums. -/
private theorem smoothIsotopic_capSum {c : unitInterval → Fin m → Circle}
    (hc : ∀ j, ContMDiff (𝓡∂ 1) (𝓡 1) ∞ fun t => c t j) (h : ∀ t, IsCapConfig ι r (c t) Ks) :
    SmoothIsotopic (capSum (h 0)).toContMDiffMap (capSum (h 1)).toContMDiffMap := by
  apply smoothIsotopic_def.mpr
  let F : unitInterval × Circle → sphere (0 : E) 1 := fun p => capSumSphere (h p.1) p.2
  have hs : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) (𝓡 n) ∞ F := by
    have hι : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ, E) ∞
        fun p : unitInterval × Circle => ι (p.2 : ℂ) :=
      ι.toContinuousLinearMap.contDiff.contMDiff.comp (contMDiff_coe_sphere.comp contMDiff_snd)
    have hslide (j : Fin m) : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ, E) ∞
        fun p : unitInterval × Circle => (slide ι (c p.1 j) (Ks j) p.2 : E) := by
      simp_rw [coe_slide_apply]
      have hcj : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) (𝓡 1) ∞
          fun p : unitInterval × Circle => c p.1 j := (hc j).comp contMDiff_fst
      exact ι.contMDiff_planeRotation.comp (hcj.prodMk (contMDiff_coe_sphere.comp
        ((Ks j).contMDiff.comp (hcj.inv.mul contMDiff_snd))))
    have hsum : ContMDiff ((𝓡∂ 1).prod (𝓡 1)) 𝓘(ℝ, E) ∞
        fun p : unitInterval × Circle => capSumFun ι (c p.1) Ks p.2 :=
      hι.add (ContMDiff.sum fun j _ => (hslide j).sub hι)
    exact hsum.codRestrict_sphere fun p => (h p.1).capSumFun_mem_sphere p.2
  refine ⟨{ toContMDiffMap := ⟨F, hs⟩
            map_zero_left := fun z => Subtype.ext (coe_capSum_apply (h 0) z).symm
            map_one_left := fun z => Subtype.ext (coe_capSum_apply (h 1) z).symm
            isSmoothEmbedding := fun t => isSmoothEmbedding_capSumSphere (h t) }⟩

/-! ### Connected sums as cap sums -/

/-- The height of a point toward the cap at `-1` is minus its imaginary part. -/
private theorem inner_neg_one_mul_I (z : ℂ) : ⟪z, ((-1 : Circle) : ℂ) * Complex.I⟫ = -z.im := by
  simp

variable {K₁ K₂ K₃ : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

/-- The connected sum of two knots in cap position is their cap sum at `1` and `-1`. -/
private theorem connectedSum_eq_capSum {c : Fin 2 → Circle} (h : IsCapConfig ι r c ![K₁, K₂])
    (hc₀ : c 0 = 1) (hc₁ : c 1 = -1) (h₁ : IsConnectedSumPosition ι K₁)
    (h₂ : IsConnectedSumPosition ι K₂) : connectedSum K₁ K₂ h₁ h₂ = capSum h := by
  ext z : 2
  rw [coe_capSum_apply]
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ hz, h.capSumFun_eq_slide 0 fun k hk => ?_]
    · simp [hc₀, slide_one_apply]
    · obtain rfl : k = 1 := by omega
      rw [hc₁, inner_neg_one_mul_I]
      linarith [h.pos]
  · rw [coe_connectedSum_apply_of_im_neg _ _ hz, h.capSumFun_eq_slide 1 fun k hk => ?_]
    · rw [hc₁, ← reflection_slide_neg, slide_one_apply]
      simp
    · obtain rfl : k = 0 := by omega
      rw [hc₀]
      simpa [Complex.real_inner_I_right] using hz.le.trans h.pos.le

/-- The connected sum of a cap sum of two knots, with its caps in the upper hemisphere, and a
third knot is their cap sum with the third cap at `-1`. -/
private theorem connectedSum_capSum_eq {c : Fin 2 → Circle} {c' : Fin 3 → Circle}
    (h : IsCapConfig ι r c ![K₁, K₂]) (h' : IsCapConfig ι r c' ![K₁, K₂, K₃])
    (hc₀ : c' 0 = c 0) (hc₁ : c' 1 = c 1) (hc₂ : c' 2 = -1)
    (hc : ∀ j, 0 ≤ (c j : ℂ).re) (hc' : ∀ j, 1 - (c j : ℂ).re ^ 2 < r ^ 2)
    (hP : IsConnectedSumPosition ι (capSum h)) (h₃ : IsConnectedSumPosition ι K₃) :
    connectedSum (capSum h) K₃ hP h₃ = capSum h' := by
  ext z : 2
  rw [coe_capSum_apply]
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ hz, coe_capSum_apply, capSumFun, capSumFun,
      Fin.sum_univ_two, Fin.sum_univ_three, hc₀, hc₁, hc₂]
    have h₃' := (h'.isCapPosition 2).coe_slide_apply_of_le (c := -1) (z := z) (by
      rw [inner_neg_one_mul_I]; linarith [h.pos])
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h₃' ⊢
    rw [h₃', sub_self, add_zero]
  · rw [coe_connectedSum_apply_of_im_neg _ _ hz, h'.capSumFun_eq_slide 2 fun k hk => ?_]
    · rw [hc₂, ← reflection_slide_neg, slide_one_apply]
      simp
    · have hk' : c' k = c 0 ∨ c' k = c 1 := by
        fin_cases k
        · exact Or.inl hc₀
        · exact Or.inr hc₁
        · exact absurd rfl hk
      rcases hk' with hk' | hk' <;> rw [hk'] <;>
        exact not_lt.1 fun h'' =>
          hz.not_ge (Circle.im_pos_of_le_inner h.pos (hc _) (hc' _) h''.le).le

/-- The connected sum of a knot and a cap sum of two knots, with its caps in the upper
hemisphere, is their cap sum with the first cap at `1` and the other two turned over. -/
private theorem connectedSum_capSum_eq' {c : Fin 2 → Circle} {c' : Fin 3 → Circle}
    (h : IsCapConfig ι r c ![K₂, K₃]) (h' : IsCapConfig ι r c' ![K₁, K₂, K₃])
    (hc₀ : c' 0 = 1) (hc₁ : c' 1 = -c 0) (hc₂ : c' 2 = -c 1)
    (hc : ∀ j, 0 ≤ (c j : ℂ).re) (hc' : ∀ j, 1 - (c j : ℂ).re ^ 2 < r ^ 2)
    (h₁ : IsConnectedSumPosition ι K₁) (hQ : IsConnectedSumPosition ι (capSum h)) :
    connectedSum K₁ (capSum h) h₁ hQ = capSum h' := by
  ext z : 2
  rw [coe_capSum_apply]
  -- The heights of `-z` along the caps of `c` are the heights of `z` along the turned-over caps.
  have hneg (j : Fin 2) : ⟪(z : ℂ), (-(c j : ℂ)) * Complex.I⟫ =
      ⟪((-z : Circle) : ℂ), (c j : ℂ) * Complex.I⟫ := by
    rw [Circle.coe_neg, neg_mul, inner_neg_right, inner_neg_left]
  rcases le_or_gt 0 (z : ℂ).im with hz | hz
  · rw [connectedSum_apply_of_im_nonneg _ _ hz, h'.capSumFun_eq_slide 0 fun k hk => ?_]
    · simp [hc₀, slide_one_apply]
    · have hk' : c' k = -c 0 ∨ c' k = -c 1 := by
        fin_cases k
        · exact absurd rfl hk
        · exact Or.inl hc₁
        · exact Or.inr hc₂
      have himz : ((-z : Circle) : ℂ).im ≤ 0 := by simpa using hz
      rcases hk' with hk' | hk' <;> rw [hk', Circle.coe_neg, hneg] <;>
        exact not_lt.1 fun h'' =>
          himz.not_gt (Circle.im_pos_of_le_inner h.pos (hc _) (hc' _) h''.le)
  · rw [coe_connectedSum_apply_of_im_neg _ _ hz, coe_capSum_apply, capSumFun, capSumFun,
      Fin.sum_univ_two, Fin.sum_univ_three, hc₀, hc₁, hc₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have h₁' : (slide ι 1 K₁ z : E) = ι z := by
      have hK₁ := (h'.isCapPosition 0).apply_eq (z := z) (by simpa using hz.le.trans h.pos.le)
      simp only [Matrix.cons_val_zero] at hK₁
      rw [slide_one_apply, hK₁, coe_greatCircle_apply]
    rw [h₁', map_add, map_add, map_sub, map_sub, reflection_slide_neg, reflection_slide_neg,
      ← coe_greatCircle_apply (n := n) ι (-z), ← reflection_greatCircle_neg (ι := ι) (n := n) z]
    abel

/-! ### The configurations of the proof -/

/-- The threshold `r = 19 / 20` of the caps, whose angular radius is a little over `18°`. -/
private abbrev capRadius : ℝ := 19 / 20

/-- Two points of the circle at an angle between `π / 4` and `7 π / 4` have disjoint caps of
height `19 / 20`: their inner product is at most `cos (π / 4) < 2 r² - 1`. -/
private theorem cos_lt_of_mem_Icc {x : ℝ} (hx : π / 4 ≤ x) (hx' : x ≤ 7 * π / 4) :
    cos x < 2 * capRadius ^ 2 - 1 := by
  have hle : cos x ≤ cos (π / 4) := by
    rcases le_or_gt x π with h | h
    · exact cos_le_cos_of_nonneg_of_le_pi (by positivity) h hx
    · rw [← cos_two_pi_sub]
      exact cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith) (by linarith)
  rw [cos_pi_div_four] at hle
  have hsqrt : √2 < 161 / 100 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  norm_num [capRadius]
  linarith

/-- The point `ω = exp (7 π i / 4)` of the circle, where the second cap of the summands in
connected-sum position sits. -/
private abbrev capPoint : Circle := Circle.exp (7 * π / 4)

/-- Turning `-1` through `3 π / 4` reaches `capPoint`; this is the end of the second cap's
path. -/
private theorem circleExp_pi_add_three_pi_div_four : Circle.exp (π + 3 * π / 4) = capPoint := by
  rw [capPoint]
  congr 1
  ring

private theorem circleExp_three_pi_div_four : Circle.exp (3 * π / 4) = -capPoint := by
  rw [← circleExp_pi_add_three_pi_div_four, Circle.exp_add, Circle.exp_pi, neg_mul, one_mul,
    neg_neg]

private theorem re_capPoint :
    (0 : ℝ) ≤ (capPoint : ℂ).re ∧ 1 - (capPoint : ℂ).re ^ 2 < capRadius ^ 2 := by
  have hcos : cos (7 * π / 4) = √2 / 2 := by
    have hangle : 7 * π / 4 = -(π / 4) + 2 * π := by ring
    rw [hangle, cos_add_two_pi, cos_neg, cos_pi_div_four]
  rw [capPoint, Circle.coe_exp, Complex.exp_ofReal_mul_I_re, hcos]
  refine ⟨by positivity, ?_⟩
  rw [div_pow, sq_sqrt (by norm_num)]
  norm_num [capRadius]

/-- The path of the second cap, from `-1` to `capPoint`. -/
private def pathTwo (t : unitInterval) : Fin 2 → Circle :=
  ![Circle.exp 0, Circle.exp (π + 3 * π / 4 * t)]

/-- The path of the second and third caps, from `-1` and `-capPoint` to `capPoint` and `-1`. -/
private def pathThree (t : unitInterval) : Fin 3 → Circle :=
  ![Circle.exp 0, Circle.exp (π + 3 * π / 4 * t), Circle.exp (3 * π / 4 + π / 4 * t)]

private theorem contMDiff_pathTwo (j : Fin 2) :
    ContMDiff (𝓡∂ 1) (𝓡 1) ∞ fun t => pathTwo t j := by
  fin_cases j <;> first
    | exact contMDiff_const
    | exact contMDiff_circleExp.comp (contMDiff_const.add
        (contMDiff_const.mul (contMDiff_subtypeVal_Icc (x := 0) (y := 1))))

private theorem contMDiff_pathThree (j : Fin 3) :
    ContMDiff (𝓡∂ 1) (𝓡 1) ∞ fun t => pathThree t j := by
  fin_cases j <;> first
    | exact contMDiff_const
    | exact contMDiff_circleExp.comp (contMDiff_const.add
        (contMDiff_const.mul (contMDiff_subtypeVal_Icc (x := 0) (y := 1))))

/-- Points `exp (a i)` and `exp (b i)` at an angle `a - b` or `b - a` between `π / 4` and
`7 π / 4` are separated. -/
private theorem inner_circleExp_lt {a b : ℝ}
    (h : π / 4 ≤ a - b ∧ a - b ≤ 7 * π / 4 ∨ π / 4 ≤ b - a ∧ b - a ≤ 7 * π / 4) :
    ⟪(Circle.exp a : ℂ), (Circle.exp b : ℂ)⟫ < 2 * capRadius ^ 2 - 1 := by
  rw [Circle.inner_exp_exp]
  rcases h with h | h
  · exact cos_lt_of_mem_Icc h.1 h.2
  · rw [← cos_neg, neg_sub]
    exact cos_lt_of_mem_Icc h.1 h.2

private theorem inner_pathTwo_lt (t : unitInterval) {j k : Fin 2} (hjk : j ≠ k) :
    ⟪(pathTwo t j : ℂ), (pathTwo t k : ℂ)⟫ < 2 * capRadius ^ 2 - 1 := by
  obtain ⟨t, ht₀, ht₁⟩ := t
  fin_cases j <;> fin_cases k <;> simp only [ne_eq, not_true_eq_false] at hjk <;>
    simp only [pathTwo, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    exact inner_circleExp_lt (by
      first
      | exact Or.inl ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
      | exact Or.inr ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩)

private theorem inner_pathThree_lt (t : unitInterval) {j k : Fin 3} (hjk : j ≠ k) :
    ⟪(pathThree t j : ℂ), (pathThree t k : ℂ)⟫ < 2 * capRadius ^ 2 - 1 := by
  obtain ⟨t, ht₀, ht₁⟩ := t
  fin_cases j <;> fin_cases k <;> simp only [ne_eq, not_true_eq_false] at hjk <;>
    simp only [pathThree, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    exact inner_circleExp_lt (by
      first
      | exact Or.inl ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩
      | exact Or.inr ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩)

/-! ### Associativity -/

/-- **The connected sum is associative up to concordance.** For knots `K₁`, `K₂`, `K₃` in
connected-sum position for the great circle `ι`, there are knots `P` and `Q` in connected-sum
position, concordant to `K₁ # K₂` and to `K₂ # K₃`, such that `P # K₃` is concordant to `K₁ # Q`.
Once the connected sum is known not to depend on the representatives in connected-sum position,
this is the associativity of the connected sum of concordance classes. -/
theorem exists_concordant_connectedSum_assoc (h₁ : IsConnectedSumPosition ι K₁)
    (h₂ : IsConnectedSumPosition ι K₂) (h₃ : IsConnectedSumPosition ι K₃) :
    ∃ (P Q : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
      (hP : IsConnectedSumPosition ι P) (hQ : IsConnectedSumPosition ι Q),
      SmoothEmbedding.Concordant (connectedSum K₁ K₂ h₁ h₂) P ∧
        SmoothEmbedding.Concordant (connectedSum K₂ K₃ h₂ h₃) Q ∧
        SmoothEmbedding.Concordant (connectedSum P K₃ hP h₃) (connectedSum K₁ Q h₁ hQ) := by
  have hr : (0 : ℝ) < capRadius := by norm_num [capRadius]
  have hr₁ : capRadius < 1 := by norm_num [capRadius]
  -- Boost the three knots into small caps, through concordances in connected-sum position.
  obtain ⟨a, ha₁, ha₂, ha₃, ha⟩ := ((h₁.eventually_isCapPosition_boost hr₁).and
    ((h₂.eventually_isCapPosition_boost hr₁).and ((h₃.eventually_isCapPosition_boost hr₁).and
      (eventually_ge_atTop 0)))).exists
  set L₁ := boost ι a K₁
  set L₂ := boost ι a K₂
  set L₃ := boost ι a K₃
  have hF₁ := h₁.boostConcordance ha
  have hF₂ := h₂.boostConcordance ha
  have hF₃ := h₃.boostConcordance ha
  -- The cap configurations along the two paths.
  have hcap₂ (L L' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
      (hL : IsCapPosition ι capRadius L) (hL' : IsCapPosition ι capRadius L') (t : unitInterval) :
      IsCapConfig ι capRadius (pathTwo t) ![L, L'] :=
    ⟨hr, fun j => by fin_cases j <;> assumption, inner_pathTwo_lt t⟩
  have hcap₃ (t : unitInterval) : IsCapConfig ι capRadius (pathThree t) ![L₁, L₂, L₃] :=
    ⟨hr, fun j => by fin_cases j <;> assumption, inner_pathThree_lt t⟩
  have hpos₂ (j : Fin 2) :
      0 ≤ (pathTwo 1 j : ℂ).re ∧ 1 - (pathTwo 1 j : ℂ).re ^ 2 < capRadius ^ 2 := by
    fin_cases j
    · simp [pathTwo, capRadius]
    · simp only [pathTwo, Fin.mk_one, Matrix.cons_val_one, Set.Icc.coe_one, mul_one]
      rw [circleExp_pi_add_three_pi_div_four]
      exact re_capPoint
  -- Evaluating the paths at their ends.
  have hp₂₀ : pathTwo 0 0 = 1 := by simp [pathTwo]
  have hp₂₁ : pathTwo 0 1 = -1 := by simp [pathTwo, Circle.exp_pi]
  have hq₂₀ : pathTwo 1 0 = 1 := by simp [pathTwo]
  have hq₂₁ : pathTwo 1 1 = capPoint := by
    simp only [pathTwo, Matrix.cons_val_one, Matrix.cons_val_zero, Set.Icc.coe_one, mul_one]
    exact circleExp_pi_add_three_pi_div_four
  have hp₃₀ : pathThree 0 0 = 1 := by simp [pathThree]
  have hp₃₁ : pathThree 0 1 = -1 := by simp [pathThree, Circle.exp_pi]
  have hp₃₂ : pathThree 0 2 = -capPoint := by simp [pathThree, circleExp_three_pi_div_four]
  have hq₃₀ : pathThree 1 0 = 1 := by simp [pathThree]
  have hq₃₁ : pathThree 1 1 = capPoint := by
    simp only [pathThree, Matrix.cons_val_one, Matrix.cons_val_zero, Set.Icc.coe_one, mul_one]
    exact circleExp_pi_add_three_pi_div_four
  have hq₃₂ : pathThree 1 2 = -1 := by
    simp only [pathThree, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Set.Icc.coe_one, mul_one]
    have hangle : 3 * π / 4 + π / 4 = π := by ring
    rw [hangle, Circle.exp_pi]
  set P := capSum (hcap₂ L₁ L₂ ha₁ ha₂ 1)
  set Q := capSum (hcap₂ L₂ L₃ ha₂ ha₃ 1)
  have hP : IsConnectedSumPosition ι P :=
    (hcap₂ L₁ L₂ ha₁ ha₂ 1).isConnectedSumPosition_capSum (fun j => (hpos₂ j).1)
      fun j => (hpos₂ j).2
  have hQ : IsConnectedSumPosition ι Q :=
    (hcap₂ L₂ L₃ ha₂ ha₃ 1).isConnectedSumPosition_capSum (fun j => (hpos₂ j).1)
      fun j => (hpos₂ j).2
  -- A connected sum of two boosted knots slides to a cap sum in connected-sum position.
  have hslide₂ (L L' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
      (hL : IsCapPosition ι capRadius L) (hL' : IsCapPosition ι capRadius L') :
      SmoothEmbedding.Concordant (connectedSum L L' (hL.isConnectedSumPosition hr)
        (hL'.isConnectedSumPosition hr)) (capSum (hcap₂ L L' hL hL' 1)) := by
    rw [connectedSum_eq_capSum (hcap₂ L L' hL hL' 0) hp₂₀ hp₂₁]
    exact SmoothEmbedding.Concordant.of_smoothIsotopic
      (smoothIsotopic_capSum contMDiff_pathTwo (hcap₂ L L' hL hL')) (by simp) le_rfl
  refine ⟨P, Q, hP, hQ, ?_, ?_, ?_⟩
  · exact (concordant_connectedSum hF₁ hF₂).trans (hslide₂ L₁ L₂ ha₁ ha₂)
  · exact (concordant_connectedSum hF₂ hF₃).trans (hslide₂ L₂ L₃ ha₂ ha₃)
  · -- `P # K₃ ∼ P # L₃`, the cap sum at `1, capPoint, -1`; and `K₁ # Q ∼ L₁ # Q`, the cap sum at
    -- `1, -1, -capPoint`. The second slides to the first.
    have hA : connectedSum P L₃ hP (ha₃.isConnectedSumPosition hr) = capSum (hcap₃ 1) :=
      connectedSum_capSum_eq (hcap₂ L₁ L₂ ha₁ ha₂ 1) (hcap₃ 1) (hq₃₀.trans hq₂₀.symm)
        (hq₃₁.trans hq₂₁.symm) hq₃₂ (fun j => (hpos₂ j).1) (fun j => (hpos₂ j).2) hP _
    have hB : connectedSum L₁ Q (ha₁.isConnectedSumPosition hr) hQ = capSum (hcap₃ 0) :=
      connectedSum_capSum_eq' (hcap₂ L₂ L₃ ha₂ ha₃ 1) (hcap₃ 0) hp₃₀ (hp₃₁.trans (by rw [hq₂₀]))
        (hp₃₂.trans (by rw [hq₂₁])) (fun j => (hpos₂ j).1) (fun j => (hpos₂ j).2) _ hQ
    have hBA : SmoothEmbedding.Concordant (capSum (hcap₃ 0)) (capSum (hcap₃ 1)) :=
      SmoothEmbedding.Concordant.of_smoothIsotopic
        (smoothIsotopic_capSum contMDiff_pathThree hcap₃) (by simp) le_rfl
    refine ((concordant_connectedSum_right hP hF₃).trans ?_).trans
      (concordant_connectedSum_left hF₁ hQ).symm
    rw [hA, hB]
    exact hBA.symm

end SmoothCircleEmbedding

end TauCeti
