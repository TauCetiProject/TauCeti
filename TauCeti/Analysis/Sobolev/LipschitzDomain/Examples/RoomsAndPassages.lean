/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.BoundaryPart
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Rooms and passages: Poincaré–Friedrichs fails without the Lipschitz hypothesis

The Poincaré–Friedrichs inequality
`TauCeti.W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule` bounds
`‖u‖_{Lᵖ(Ω)}` by `C ‖∇u‖_{Lᵖ(Ω)}` on `W^{1,p}_Γ(Ω)` for a bounded connected Lipschitz domain `Ω`
and a boundary part `Γ` of positive surface measure. This file shows that the Lipschitz hypothesis
cannot be dropped, by the classical domain of rooms and passages.

The plane domain `TauCeti.roomsAndPassages` is a row of square rooms
`R_k = (4 - 4 · 2⁻ᵏ, 4 - 3 · 2⁻ᵏ) × (0, 2⁻ᵏ)` of side `2⁻ᵏ`, the room `R_{k+1}` starting at
distance `2⁻ᵏ` to the right of `R_k`, joined by passages
`P_k = (4 - 4 · 2⁻ᵏ, 4 - 3 · 2⁻⁽ᵏ⁺¹⁾) × (0, w_k)` along the bottom edge, of width
`w_k = 2^(-(k + 1)²)`. It is open, bounded and connected, and the far side
`Γ = {0} × (0, 1)` of the first room (`TauCeti.roomsAndPassagesWall`) is a part of its frontier of
one-dimensional Hausdorff measure one. Yet for every finite `p ≥ 1` no inequality
`‖u‖_p ≤ C ‖∇u‖_p` holds on `W^{1,p}_Γ`
(`TauCeti.not_exists_norm_value_le_mul_norm_gradient_roomsAndPassages`). Comparing with the
Poincaré–Friedrichs inequality, the domain is not a Lipschitz domain
(`TauCeti.not_isLipschitzDomain_roomsAndPassages`). The rooms accumulate at the corner `(4, 0)`.

The witnesses are smooth steps `u_k` in the first coordinate, equal to `0` up to the right side of
`R_k` and to `1` from the left side of `R_{k+1}` on, rising across the stretch of `P_k` of length
`2⁻ᵏ` between them. On the domain, `∇u_k` is supported in that stretch, of area at most
`2⁻ᵏ w_k`, and bounded by a constant multiple of `2ᵏ`, while `u_k = 1` on `R_{k+1}`, of area
`4^(-(k + 1))`. So `‖∇u_k‖_p ≲ 2ᵏ (2⁻ᵏ w_k)^(1/p)` and `‖u_k‖_p ≥ 2^(-2(k + 1)/p)`, and the ratio
`‖u_k‖_p / ‖∇u_k‖_p` tends to infinity: the passage widths decay faster than any power of `2⁻ᵏ`,
so one domain serves every exponent `p`. Each `u_k` is a smooth compactly supported function on
the plane, cut off far from the domain, whose support misses `closure Γ`, so it is a generator of
`W^{1,p}_Γ`.

## Main declarations

* `TauCeti.roomsAndPassages`: the domain, with `TauCeti.mem_roomsAndPassages`.
* `TauCeti.isBounded_roomsAndPassages`, `TauCeti.isConnected_roomsAndPassages`: it is bounded and
  connected.
* `TauCeti.roomsAndPassagesWall_subset_frontier` and
  `TauCeti.euclideanHausdorffMeasure_roomsAndPassagesWall`: `Γ` lies in the frontier and has
  one-dimensional Hausdorff measure one.
* `TauCeti.not_exists_norm_value_le_mul_norm_gradient_roomsAndPassages`: the Poincaré–Friedrichs
  inequality fails on `W^{1,p}_Γ`, for every finite `p`.
* `TauCeti.not_isLipschitzDomainWith_roomsAndPassages` and
  `TauCeti.not_isLipschitzDomain_roomsAndPassages`: the domain is not a Lipschitz domain.

## References

* C. J. Amick, *Some remarks on Rellich's theorem and the Poincaré inequality*, J. London Math.
  Soc. (2) **18** (1978), 81–93 (rooms and passages domains).
* D. E. Edmunds, W. D. Evans, *Spectral Theory and Differential Operators*, Oxford University
  Press, 1987, Chapter V (rooms and passages).
-/

public section

noncomputable section

open Filter MeasureTheory Metric Module Set TopologicalSpace WithLp
open scoped ENNReal NNReal Gradient Distributions Topology ContDiff

namespace TauCeti

/-! ### The domain -/

/-- The side `2⁻ᵏ` of the `k`-th room. -/
private def roomSide (k : ℕ) : ℝ := (1 / 2) ^ k

/-- The width `2^(-(k + 1)²)` of the `k`-th passage. -/
private def passageWidth (k : ℕ) : ℝ := ((1 / 2) ^ (k + 1)) ^ (k + 1)

/-- The `k`-th room `(4 - 4 · 2⁻ᵏ, 4 - 3 · 2⁻ᵏ) × (0, 2⁻ᵏ)`. -/
private def room (k : ℕ) : Set (WithLp 2 (ℝ × ℝ)) :=
  ofLp ⁻¹' (Ioo (4 - 4 * roomSide k) (4 - 3 * roomSide k) ×ˢ Ioo 0 (roomSide k))

/-- The `k`-th passage, from the left side of the `k`-th room to the right side of the next one,
of width `2^(-(k + 1)²)`. -/
private def passage (k : ℕ) : Set (WithLp 2 (ℝ × ℝ)) :=
  ofLp ⁻¹' (Ioo (4 - 4 * roomSide k) (4 - 3 * roomSide (k + 1)) ×ˢ Ioo 0 (passageWidth k))

/-- **Rooms and passages.** The open set in the plane made of the square rooms
`R_k = (4 - 4 · 2⁻ᵏ, 4 - 3 · 2⁻ᵏ) × (0, 2⁻ᵏ)`, `k ∈ ℕ`, and the passages
`P_k = (4 - 4 · 2⁻ᵏ, 4 - 3 · 2⁻⁽ᵏ⁺¹⁾) × (0, 2^(-(k + 1)²))` joining `R_k` to `R_{k+1}` along the
bottom edge. It is bounded and connected, but not a Lipschitz domain, and the Poincaré–Friedrichs
inequality fails on it. -/
def roomsAndPassages : Opens (WithLp 2 (ℝ × ℝ)) where
  carrier := ⋃ k, room k ∪ passage k
  is_open' := isOpen_iUnion fun _ =>
    ((isOpen_Ioo.prod isOpen_Ioo).preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ)).union
      ((isOpen_Ioo.prod isOpen_Ioo).preimage (WithLp.prod_continuous_ofLp 2 ℝ ℝ))

private theorem coe_roomsAndPassages :
    (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))) = ⋃ k, room k ∪ passage k :=
  rfl

/-- Membership in the domain of rooms and passages: a point lies in a room or in a passage. -/
theorem mem_roomsAndPassages {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ roomsAndPassages ↔ ∃ k : ℕ,
      (x.fst ∈ Ioo (4 - 4 * (1 / 2) ^ k) (4 - 3 * (1 / 2) ^ k) ∧ x.snd ∈ Ioo 0 ((1 / 2) ^ k)) ∨
      (x.fst ∈ Ioo (4 - 4 * (1 / 2) ^ k) (4 - 3 * (1 / 2) ^ (k + 1)) ∧
        x.snd ∈ Ioo 0 (((1 / 2) ^ (k + 1)) ^ (k + 1))) := by
  simp [← SetLike.mem_coe, coe_roomsAndPassages, room, passage, roomSide, passageWidth]

/-- The far side `Γ = {0} × (0, 1)` of the first room, a part of the frontier of
`TauCeti.roomsAndPassages`. -/
def roomsAndPassagesWall : Set (WithLp 2 (ℝ × ℝ)) :=
  ofLp ⁻¹' ({0} ×ˢ Ioo 0 1)

/-- Membership in the far side of the first room. -/
@[simp]
theorem mem_roomsAndPassagesWall {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ roomsAndPassagesWall ↔ x.fst = 0 ∧ x.snd ∈ Ioo 0 1 := by
  simp [roomsAndPassagesWall]

/-! ### Elementary geometry -/

private theorem roomSide_pos (k : ℕ) : 0 < roomSide k := by
  unfold roomSide; positivity

private theorem roomSide_le_one (k : ℕ) : roomSide k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

private theorem roomSide_succ (k : ℕ) : roomSide (k + 1) = roomSide k / 2 := by
  simp [roomSide, pow_succ, div_eq_mul_inv]

private theorem roomSide_anti {j k : ℕ} (h : j ≤ k) : roomSide k ≤ roomSide j :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

private theorem passageWidth_pos (k : ℕ) : 0 < passageWidth k := by
  unfold passageWidth; positivity

/-- A passage is no wider than the next room. -/
private theorem passageWidth_le (k : ℕ) : passageWidth k ≤ roomSide (k + 1) := by
  unfold passageWidth
  exact pow_le_of_le_one (by positivity) (roomSide_le_one (k + 1)) (by omega)

private theorem mem_room {k : ℕ} {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ room k ↔ x.fst ∈ Ioo (4 - 4 * roomSide k) (4 - 3 * roomSide k) ∧
      x.snd ∈ Ioo 0 (roomSide k) := by
  simp [room]

private theorem mem_passage {k : ℕ} {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ passage k ↔ x.fst ∈ Ioo (4 - 4 * roomSide k) (4 - 3 * roomSide (k + 1)) ∧
      x.snd ∈ Ioo 0 (passageWidth k) := by
  simp [passage]

private theorem mem_roomsAndPassages_iff {x : WithLp 2 (ℝ × ℝ)} :
    x ∈ roomsAndPassages ↔ ∃ k, x ∈ room k ∨ x ∈ passage k := by
  simp [← SetLike.mem_coe, coe_roomsAndPassages]

private theorem room_subset (k : ℕ) : room k ⊆ roomsAndPassages := fun _ hx =>
  mem_roomsAndPassages_iff.2 ⟨k, Or.inl hx⟩

/-- The domain lies in the rectangle `(0, 4) × (0, 1)`. -/
private theorem mem_Ioo_of_mem {x : WithLp 2 (ℝ × ℝ)} (hx : x ∈ roomsAndPassages) :
    x.fst ∈ Ioo 0 4 ∧ x.snd ∈ Ioo 0 1 := by
  obtain ⟨k, hk | hk⟩ := mem_roomsAndPassages_iff.1 hx
  · rw [mem_room] at hk
    have := roomSide_pos k
    have := roomSide_le_one k
    exact ⟨⟨by linarith [hk.1.1], by linarith [hk.1.2]⟩, ⟨hk.2.1, by linarith [hk.2.2]⟩⟩
  · rw [mem_passage] at hk
    have := roomSide_pos (k + 1)
    have := roomSide_le_one k
    have := passageWidth_le k
    have := roomSide_le_one (k + 1)
    exact ⟨⟨by linarith [hk.1.1], by linarith [hk.1.2]⟩, ⟨hk.2.1, by linarith [hk.2.2]⟩⟩

/-- The centre `(2, 1 / 2)` of the rectangle containing the domain. -/
private def center : WithLp 2 (ℝ × ℝ) := toLp 2 ((2 : ℝ), (1 / 2 : ℝ))

/-- The domain lies in the open ball of radius `3` about `(2, 1 / 2)`. -/
private theorem subset_ball : (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))) ⊆ ball center 3 := by
  intro x hx
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_Ioo_of_mem hx
  rw [mem_ball, prod_dist_eq_of_L2, Real.sqrt_lt' (by norm_num)]
  simp only [center, Real.dist_eq, toLp_fst, toLp_snd, sq_abs]
  nlinarith

/-- **The domain of rooms and passages is bounded.** -/
theorem isBounded_roomsAndPassages :
    Bornology.IsBounded (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))) :=
  isBounded_ball.subset subset_ball

/-- **The domain of rooms and passages is connected**: each room meets its outgoing passage, and
each passage meets the next room. -/
theorem isConnected_roomsAndPassages :
    IsConnected (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))) := by
  -- Rooms and passages are open rectangles, hence convex.
  have hconv (a b h : ℝ) :
      IsPreconnected (ofLp ⁻¹' (Ioo a b ×ˢ Ioo 0 h) : Set (WithLp 2 (ℝ × ℝ))) :=
    (((convex_Ioo a b).prod (convex_Ioo 0 h)).linear_preimage
      (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).toLinearMap).isPreconnected
  -- A point of the `k`-th passage inside the `j`-th room, for `j = k` and `j = k + 1`.
  have hmeet (k j : ℕ) (hj : j = k ∨ j = k + 1) :
      toLp 2 (4 - 7 / 2 * roomSide j, passageWidth k / 2) ∈ room j ∩ passage k := by
    have := roomSide_pos k
    have := passageWidth_pos k
    have := passageWidth_le k
    have := roomSide_succ k
    rw [mem_inter_iff, mem_room, mem_passage]
    simp only [toLp_fst, toLp_snd]
    rcases hj with rfl | rfl <;>
      refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  rw [coe_roomsAndPassages]
  refine IsConnected.iUnion_of_chain (fun k => ?_) (fun k => ?_)
  · have h := hmeet k k (Or.inl rfl)
    exact ⟨⟨_, Or.inl h.1⟩, IsPreconnected.union _ h.1 h.2 (hconv _ _ _) (hconv _ _ _)⟩
  · have h := hmeet k (k + 1) (Or.inr rfl)
    exact ⟨_, Or.inr h.2, Or.inl h.1⟩

/-! ### The wall `Γ` -/

/-- The far side `Γ = {0} × (0, 1)` of the first room lies in the frontier of the domain: it is
the limit of points of the first room, and misses the domain, which lies in `{0 < x.fst}`. -/
theorem roomsAndPassagesWall_subset_frontier :
    roomsAndPassagesWall ⊆ frontier (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))) := by
  intro x hx
  rw [mem_roomsAndPassagesWall] at hx
  rw [roomsAndPassages.isOpen.frontier_eq]
  refine ⟨?_, fun h => (mem_Ioo_of_mem h).1.1.ne' hx.1⟩
  -- `x` is the limit of the points `(s, x.snd)` of the first room as `s → 0⁺`.
  have hx' : toLp 2 ((0 : ℝ), x.snd) = x :=
    ofLp_injective 2 (Prod.ext (by simp [hx.1]) (by simp))
  have h0 : (0 : ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have hcont : Continuous fun s : ℝ => toLp 2 (s, x.snd) :=
    (prod_continuous_toLp 2 ℝ ℝ).comp (continuous_id.prodMk continuous_const)
  rw [← hx']
  refine closure_mono (room_subset 0)
    (map_mem_closure (f := fun s : ℝ => toLp 2 (s, x.snd)) hcont h0 fun s hs => ?_)
  rw [mem_room]
  simp only [roomSide, pow_zero, mul_one, toLp_fst, toLp_snd]
  exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, hx.2⟩

/-- The far side `Γ = {0} × (0, 1)` of the first room has one-dimensional Hausdorff measure one:
it is an isometric copy of the unit interval. -/
theorem euclideanHausdorffMeasure_roomsAndPassagesWall :
    (μHE[1] : Measure (WithLp 2 (ℝ × ℝ))) roomsAndPassagesWall = 1 := by
  have hiso := WithLp.isometry_toLp_prodMk_left 2 (β := ℝ) (0 : ℝ)
  have himage : roomsAndPassagesWall = (fun t : ℝ => toLp 2 ((0 : ℝ), t)) '' Ioo 0 1 := by
    ext x
    rw [mem_roomsAndPassagesWall]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨x.snd, h1, ofLp_injective 2 (Prod.ext (by simp [h0]) (by simp))⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨rfl, ht⟩
  have hvol := InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ)
  rw [finrank_self] at hvol
  rw [himage, hiso.euclideanHausdorffMeasure_image, hvol, Real.volume_Ioo, sub_zero,
    ENNReal.ofReal_one]

/-! ### The witnesses -/

/-- A smooth cutoff equal to one on the ball of radius `3` about `(2, 1 / 2)`, hence on a
neighbourhood of the domain. -/
private def cutoff : ContDiffBump center := ⟨3, 4, by norm_num, by norm_num⟩

/-- The smooth step `σ(2ᵏ (x.fst - (4 - 3 · 2⁻ᵏ)))` in the first coordinate, `σ` the smooth
transition: it is `0` up to the right side of the `k`-th room and `1` from the left side of the
next room on. -/
private def step (k : ℕ) (x : WithLp 2 (ℝ × ℝ)) : ℝ :=
  Real.smoothTransition ((roomSide k)⁻¹ * (x.fst - (4 - 3 * roomSide k)))

private theorem contDiff_step (k : ℕ) : ContDiff ℝ ∞ (step k) :=
  Real.smoothTransition.contDiff.comp
    (contDiff_const.mul ((fstL 2 ℝ ℝ ℝ).contDiff.sub contDiff_const))

private theorem hasFDerivAt_step (k : ℕ) (x : WithLp 2 (ℝ × ℝ)) :
    HasFDerivAt (step k) (deriv Real.smoothTransition
      ((roomSide k)⁻¹ * (x.fst - (4 - 3 * roomSide k))) •
        ((roomSide k)⁻¹ • fstL 2 ℝ ℝ ℝ)) x :=
  (((fstL 2 ℝ ℝ ℝ).hasFDerivAt.sub_const _).const_mul _).smoothTransition

/-- The `k`-th witness, the smooth step `step k` cut off far from the domain: a test function on
the plane. -/
private def witness (k : ℕ) : 𝓓((⊤ : Opens (WithLp 2 (ℝ × ℝ))), ℝ) :=
  ⟨fun x => step k x * cutoff x, (contDiff_step k).mul cutoff.contDiff,
    cutoff.hasCompactSupport.mul_left, subset_univ _⟩

private theorem witness_apply (k : ℕ) (x : WithLp 2 (ℝ × ℝ)) :
    witness k x = step k x * cutoff x := by
  rw [witness, TestFunction.coe_mk]

/-- Near the domain the witness is the step itself. -/
private theorem witness_eventuallyEq {k : ℕ} {x : WithLp 2 (ℝ × ℝ)}
    (hx : x ∈ roomsAndPassages) : (witness k : WithLp 2 (ℝ × ℝ) → ℝ) =ᶠ[𝓝 x] step k := by
  filter_upwards [isOpen_ball.mem_nhds (subset_ball hx)] with y hy
  rw [witness_apply, cutoff.one_of_mem_closedBall (ball_subset_closedBall hy), mul_one]

/-- On the domain the gradient of the `k`-th witness is at most `L 2ᵏ`, for a bound `L` on the
derivative of the smooth transition. -/
private theorem norm_gradient_witness_le {L : ℝ}
    (hL : ∀ τ, ‖deriv Real.smoothTransition τ‖ ≤ L) {k : ℕ} {x : WithLp 2 (ℝ × ℝ)}
    (hx : x ∈ roomsAndPassages) : ‖∇ (witness k : WithLp 2 (ℝ × ℝ) → ℝ) x‖ ≤
      L * (roomSide k)⁻¹ := by
  rw [norm_gradient_eq_norm_fderiv, (witness_eventuallyEq hx).fderiv_eq,
    (hasFDerivAt_step k x).fderiv, norm_smul, norm_smul, ← mul_assoc]
  have hs := (inv_pos.2 (roomSide_pos k)).le
  refine (mul_le_of_le_one_right (by positivity) (norm_fstL_le_one 2 ℝ ℝ ℝ)).trans ?_
  rw [Real.norm_of_nonneg hs]
  exact mul_le_mul_of_nonneg_right (hL _) hs

/-- On the domain the gradient of the `k`-th witness vanishes off the stretch
`4 - 3 · 2⁻ᵏ < x.fst < 4 - 2 · 2⁻ᵏ` of the `k`-th passage between the rooms. -/
private theorem gradient_witness_eq_zero {k : ℕ} {x : WithLp 2 (ℝ × ℝ)}
    (hx : x ∈ roomsAndPassages)
    (hxk : x.fst ∉ Ioo (4 - 3 * roomSide k) (4 - 4 * roomSide (k + 1))) :
    ∇ (witness k : WithLp 2 (ℝ × ℝ) → ℝ) x = 0 := by
  rw [gradient_eq_zero_iff, (witness_eventuallyEq hx).fderiv_eq, (hasFDerivAt_step k x).fderiv]
  have hs := roomSide_pos k
  rw [roomSide_succ, mem_Ioo, not_and_or, not_lt, not_lt] at hxk
  rcases hxk with h | h
  · rw [Real.smoothTransition.deriv_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 hs).le (by linarith)), zero_smul]
  · rw [Real.smoothTransition.deriv_of_one_le, zero_smul]
    rw [le_inv_mul_iff₀ hs]
    linarith

/-- The `k`-th witness is `1` on the next room. -/
private theorem witness_eq_one {k : ℕ} {x : WithLp 2 (ℝ × ℝ)} (hx : x ∈ room (k + 1)) :
    witness k x = 1 := by
  rw [witness_apply, cutoff.one_of_mem_closedBall
    (ball_subset_closedBall (subset_ball (room_subset _ hx))), mul_one, step,
    Real.smoothTransition.one_of_one_le]
  have hs := roomSide_pos k
  rw [mem_room, roomSide_succ] at hx
  rw [le_inv_mul_iff₀ hs]
  linarith [hx.1.1]

/-- The support of every witness misses the closure of `Γ`: the witnesses vanish on
`{x.fst ≤ 4 - 3 · 2⁻ᵏ}`, a neighbourhood of `{x.fst = 0}`. -/
private theorem disjoint_tsupport_witness (k : ℕ) :
    Disjoint (tsupport (witness k : WithLp 2 (ℝ × ℝ) → ℝ)) (closure roomsAndPassagesWall) := by
  have hs := roomSide_pos k
  have hs1 := roomSide_le_one k
  have hclosed : IsClosed {x : WithLp 2 (ℝ × ℝ) | 4 - 3 * roomSide k ≤ x.fst} :=
    isClosed_le continuous_const (prod_continuous_ofLp 2 ℝ ℝ).fst
  have hsupp : tsupport (witness k : WithLp 2 (ℝ × ℝ) → ℝ) ⊆
      {x | 4 - 3 * roomSide k ≤ x.fst} := by
    refine closure_minimal (fun x hx => ?_) hclosed
    by_contra h
    refine hx ?_
    rw [witness_apply, step, Real.smoothTransition.zero_of_nonpos, zero_mul]
    simp only [mem_ofPred_eq, not_le] at h
    exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.2 hs).le (by linarith)
  have hwall : closure roomsAndPassagesWall ⊆ {x : WithLp 2 (ℝ × ℝ) | x.fst = 0} :=
    closure_minimal (fun x hx => (mem_roomsAndPassagesWall.1 hx).1)
      (isClosed_eq (prod_continuous_ofLp 2 ℝ ℝ).fst continuous_const)
  refine Set.disjoint_left.2 fun x hx hx' => ?_
  have h1 := hsupp hx
  have h2 := hwall hx'
  simp only [mem_ofPred_eq] at h1 h2
  linarith

/-! ### The estimates -/

/-- The stretch `(4 - 3 · 2⁻ᵏ, 4 - 2 · 2⁻ᵏ) × (0, w_k)` of the `k`-th passage between the `k`-th
room and the next. -/
private def stretch (k : ℕ) : Set (WithLp 2 (ℝ × ℝ)) :=
  ofLp ⁻¹' (Ioo (4 - 3 * roomSide k) (4 - 4 * roomSide (k + 1)) ×ˢ Ioo 0 (passageWidth k))

private theorem measurableSet_stretch (k : ℕ) : MeasurableSet (stretch k) :=
  ((isOpen_Ioo.prod isOpen_Ioo).preimage (prod_continuous_ofLp 2 ℝ ℝ)).measurableSet

/-- The only part of the domain between the `k`-th room and the next is the stretch of the `k`-th
passage. -/
private theorem mem_stretch {k : ℕ} {x : WithLp 2 (ℝ × ℝ)} (hx : x ∈ roomsAndPassages)
    (hxk : x.fst ∈ Ioo (4 - 3 * roomSide k) (4 - 4 * roomSide (k + 1))) : x ∈ stretch k := by
  obtain ⟨j, hj | hj⟩ := mem_roomsAndPassages_iff.1 hx
  · rw [mem_room] at hj
    exfalso
    rcases le_or_gt j k with hjk | hjk
    · linarith [roomSide_anti hjk, hj.1.2, hxk.1]
    · linarith [roomSide_anti (Nat.succ_le_of_lt hjk), hj.1.1, hxk.2]
  · rw [mem_passage] at hj
    rcases lt_trichotomy j k with hjk | rfl | hjk
    · linarith [roomSide_anti (Nat.succ_le_of_lt hjk), hj.1.2, hxk.1]
    · simpa [stretch] using ⟨hxk, hj.2⟩
    · linarith [roomSide_anti (Nat.succ_le_of_lt hjk), hj.1.1, hxk.2]

private theorem volume_room (k : ℕ) :
    volume (room k) = ENNReal.ofReal (roomSide k * roomSide k) := by
  rw [room, (volume_preserving_ofLp ℝ ℝ).measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, sub_zero,
    ← ENNReal.ofReal_mul (by linarith [roomSide_pos k])]
  congr 1
  ring

private theorem volume_stretch (k : ℕ) :
    volume (stretch k) = ENNReal.ofReal (roomSide k * passageWidth k) := by
  rw [stretch, (volume_preserving_ofLp ℝ ℝ).measure_preimage
    (measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, sub_zero, roomSide_succ,
    ← ENNReal.ofReal_mul (by linarith [roomSide_pos k])]
  congr 1
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The witness is `1` on the next room, so its `Lᵖ` norm on the domain is at least the
`p`-th root of the area of that room. -/
private theorem le_eLpNorm_value (hp : p ≠ (∞ : ℝ≥0∞)) (k : ℕ) :
    ENNReal.ofReal ((roomSide (k + 1) * roomSide (k + 1)) ^ p.toReal⁻¹) ≤
      eLpNorm (W1p.value (W1p.restrictL
        (le_top : roomsAndPassages ≤ ⊤) (W1p.ofTestFunctionₗ volume ⊤ p (witness k)))) p
      (volume.restrict (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ)))) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hroom : MeasurableSet (room (k + 1)) :=
    ((isOpen_Ioo.prod isOpen_Ioo).preimage (prod_continuous_ofLp 2 ℝ ℝ)).measurableSet
  rw [eLpNorm_congr_ae (W1p.value_restrictL_ofTestFunctionₗ_ae le_top (witness k)),
    ← ENNReal.ofReal_rpow_of_nonneg (mul_pos (roomSide_pos _) (roomSide_pos _)).le
      (inv_nonneg.2 ENNReal.toReal_nonneg), ← volume_room]
  calc volume (room (k + 1)) ^ p.toReal⁻¹
      = eLpNorm (fun _ => (1 : ℝ)) p (volume.restrict (room (k + 1))) := by
        rw [eLpNorm_const' _ hp0 hp, eNorm_one, one_mul, Measure.restrict_apply_univ, one_div]
    _ = eLpNorm (witness k) p (volume.restrict (room (k + 1))) :=
        eLpNorm_congr_ae (ae_restrict_of_forall_mem hroom fun x hx => (witness_eq_one hx).symm)
    _ ≤ _ := eLpNorm_mono_measure _ (Measure.restrict_mono (room_subset _) le_rfl)

/-- On the domain the gradient of the witness is supported in the stretch of the passage, where it
is at most `L 2ᵏ`. -/
private theorem eLpNorm_gradient_le {L : ℝ} (hL : ∀ τ, ‖deriv Real.smoothTransition τ‖ ≤ L)
    (k : ℕ) :
    eLpNorm (W1p.gradient (W1p.restrictL (le_top : roomsAndPassages ≤ ⊤)
      (W1p.ofTestFunctionₗ volume ⊤ p (witness k)))) p
      (volume.restrict (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ)))) ≤
      ENNReal.ofReal ((roomSide k * passageWidth k) ^ p.toReal⁻¹ * (L * (roomSide k)⁻¹)) := by
  have hst := mul_pos (roomSide_pos k) (passageWidth_pos k)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hst.le _),
    ← ENNReal.ofReal_rpow_of_nonneg hst.le (inv_nonneg.2 ENNReal.toReal_nonneg), ← volume_stretch]
  set g := W1p.gradient (W1p.restrictL (le_top : roomsAndPassages ≤ ⊤)
    (W1p.ofTestFunctionₗ volume ⊤ p (witness k)))
  have hg : ∀ᵐ x ∂volume.restrict (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))),
      x ∈ roomsAndPassages ∧ g x = ∇ (witness k : WithLp 2 (ℝ × ℝ) → ℝ) x := by
    filter_upwards [ae_restrict_mem roomsAndPassages.isOpen.measurableSet,
      W1p.gradient_restrictL_ae le_top (W1p.ofTestFunctionₗ volume ⊤ p (witness k)),
      ae_restrict_of_ae (W1p.gradient_ofTestFunctionₗ_top_ae (p := p) (witness k))]
      with x hx h1 h2
    exact ⟨hx, h1.trans h2⟩
  -- The gradient vanishes on the domain off the stretch.
  have hgT : (g : WithLp 2 (ℝ × ℝ) → WithLp 2 (ℝ × ℝ)) =ᵐ[volume.restrict
      (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ)))] (stretch k).indicator g := by
    filter_upwards [hg] with x ⟨hx, hgx⟩
    by_cases hxT : x ∈ stretch k
    · rw [indicator_of_mem hxT]
    · rw [indicator_of_notMem hxT, hgx,
        gradient_witness_eq_zero hx fun h => hxT (mem_stretch hx h)]
  rw [eLpNorm_congr_ae hgT,
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_stretch k).nullMeasurableSet]
  refine (eLpNorm_le_of_ae_bound (Lp.aestronglyMeasurable g).restrict
    (ae_restrict_of_ae (hg.mono fun x ⟨hx, hgx⟩ => hgx ▸ norm_gradient_witness_le hL hx))).trans
    (mul_le_mul_left (ENNReal.rpow_le_rpow ?_ (by positivity)) _)
  rw [Measure.restrict_apply_univ, Measure.restrict_apply (measurableSet_stretch k)]
  exact measure_mono inter_subset_left

/-- The decay of the passage widths beats every power: for `0 < q ≤ 1` and `M ≥ 0`, some `k` has
`M (2 t^k)^q < 2 t`, with `t = 2^(-(k + 1))`. -/
private theorem exists_mul_rpow_lt {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) {M : ℝ} (hM : 0 ≤ M) :
    ∃ k : ℕ, M * (2 * roomSide (k + 1) ^ k) ^ q < 2 * roomSide (k + 1) := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (by linarith : (0 : ℝ) < M + 1))
    (by norm_num : (1 / 2 : ℝ) < 1)
  obtain ⟨N, hN⟩ := exists_nat_ge (2 / q)
  refine ⟨max K N, ?_⟩
  set k := max K N
  set t := roomSide (k + 1)
  have ht0 : 0 < t := roomSide_pos _
  have ht1 : t ≤ 1 := roomSide_le_one _
  have hkq : 2 ≤ (k : ℝ) * q := by
    have : (2 / q) * q = 2 := div_mul_cancel₀ _ hq.ne'
    nlinarith [(Nat.cast_le (α := ℝ)).2 (le_max_right K N)]
  -- `(2 t^k)^q ≤ 2 t²`, since `k q ≥ 2` and `t ≤ 1`.
  have h1 : (2 * t ^ k) ^ q ≤ 2 * t ^ 2 := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast t k,
      ← Real.rpow_mul ht0.le]
    refine mul_le_mul ?_ ?_ (by positivity) (by norm_num)
    · simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hq1
    · simpa using Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hkq
  -- `(M + 1) t < 1`, since `t ≤ 2^(-K)`.
  have h2 : (M + 1) * t < 1 := by
    have : t ≤ (1 / 2) ^ K := roomSide_anti (by omega)
    calc (M + 1) * t ≤ (M + 1) * (1 / 2) ^ K := by gcongr
      _ < (M + 1) * (M + 1)⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ (by linarith)
  calc M * (2 * t ^ k) ^ q ≤ M * (2 * t ^ 2) := mul_le_mul_of_nonneg_left h1 hM
    _ = 2 * t * (M * t) := by ring
    _ < 2 * t * 1 := by gcongr; nlinarith
    _ = 2 * t := mul_one _

/-- The real form of the contradiction: with `t = 2^(-(k + 1))`, if `C L (2 t^k)^q < 2 t`, then
the bound `C (2⁻ᵏ w_k)^q L 2ᵏ` on `‖u_k‖_p` is below the lower bound `(t²)^q`. -/
private theorem mul_rpow_mul_lt {q C L : ℝ} {k : ℕ}
    (hk : C * L * (2 * roomSide (k + 1) ^ k) ^ q < 2 * roomSide (k + 1)) :
    C * ((roomSide k * passageWidth k) ^ q * (L * (roomSide k)⁻¹)) <
      (roomSide (k + 1) * roomSide (k + 1)) ^ q := by
  have ht := roomSide_pos (k + 1)
  have hsk : roomSide k = 2 * roomSide (k + 1) := by rw [roomSide_succ]; ring
  have hw : roomSide k * passageWidth k =
      roomSide (k + 1) * roomSide (k + 1) * (2 * roomSide (k + 1) ^ k) := by
    rw [hsk, passageWidth, roomSide]
    ring
  rw [hw, Real.mul_rpow (by positivity) (by positivity), hsk]
  calc C * ((roomSide (k + 1) * roomSide (k + 1)) ^ q * (2 * roomSide (k + 1) ^ k) ^ q *
        (L * (2 * roomSide (k + 1))⁻¹))
      = (roomSide (k + 1) * roomSide (k + 1)) ^ q *
          (C * L * (2 * roomSide (k + 1) ^ k) ^ q / (2 * roomSide (k + 1))) := by
        ring
    _ < (roomSide (k + 1) * roomSide (k + 1)) ^ q * 1 :=
        mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 hk)
          (Real.rpow_pos_of_pos (mul_pos ht ht) _)
    _ = _ := mul_one _

/-! ### Poincaré–Friedrichs fails -/

/-- **Poincaré–Friedrichs fails on rooms and passages.** For every finite `p ≥ 1` there is no
constant `C` with `‖u‖_{Lᵖ} ≤ C ‖∇u‖_{Lᵖ}` for all `u ∈ W^{1,p}_Γ` on the domain of rooms and
passages, `Γ = {0} × (0, 1)` the far side of the first room. The domain is bounded and connected
and `Γ` is a part of its frontier of positive measure, so it is the Lipschitz hypothesis of
`TauCeti.W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule` that fails. -/
theorem not_exists_norm_value_le_mul_norm_gradient_roomsAndPassages (hp : p ≠ (∞ : ℝ≥0∞)) :
    ¬ ∃ C : ℝ, ∀ u ∈ w1pVanishingOnSubmodule volume roomsAndPassages p roomsAndPassagesWall,
      ‖W1p.value u‖ ≤ C * ‖W1p.gradient u‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hp1 : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hq : 0 < p.toReal⁻¹ := inv_pos.2 (by linarith)
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  obtain ⟨k, hk⟩ := exists_mul_rpow_lt hq (inv_le_one_of_one_le₀ hp1) (mul_nonneg hC0 hL0)
  set u := W1p.restrictL (le_top : roomsAndPassages ≤ ⊤)
    (W1p.ofTestFunctionₗ volume ⊤ p (witness k))
  have hu := hC u (W1p.restrictL_ofTestFunctionₗ_mem_w1pVanishingOnSubmodule
    (disjoint_tsupport_witness k))
  -- The Poincaré–Friedrichs inequality for `u`, in `ℝ≥0∞`.
  have hPF : eLpNorm (W1p.value u) p (volume.restrict (roomsAndPassages : Set _)) ≤
      ENNReal.ofReal (max C 0) *
        eLpNorm (W1p.gradient u) p (volume.restrict (roomsAndPassages : Set _)) := by
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (W1p.value u)),
      ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (W1p.gradient u)), ← ENNReal.ofReal_mul hC0,
      ← Lp.norm_def, ← Lp.norm_def]
    exact ENNReal.ofReal_le_ofReal
      (hu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
  have h := (le_eLpNorm_value hp k).trans
    (hPF.trans (mul_le_mul_right (eLpNorm_gradient_le hL k) _))
  have hY : 0 ≤ (roomSide k * passageWidth k) ^ p.toReal⁻¹ * (L * (roomSide k)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg (mul_pos (roomSide_pos k) (passageWidth_pos k)).le _)
      (mul_nonneg hL0 (inv_pos.2 (roomSide_pos k)).le)
  rw [← ENNReal.ofReal_mul hC0, ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 hY)] at h
  exact (mul_rpow_mul_lt hk).not_ge h

/-- **Rooms and passages is not a Lipschitz domain**, with any constant: otherwise the
Poincaré–Friedrichs inequality would hold on it. -/
theorem not_isLipschitzDomainWith_roomsAndPassages (L : ℝ≥0) :
    ¬ (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomainWith L := fun hΩ => by
  have hΓ : (μHE[finrank ℝ ℝ] : Measure (WithLp 2 (ℝ × ℝ)))
      (roomsAndPassagesWall ∩ frontier (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ)))) ≠ 0 := by
    rw [finrank_self, inter_eq_left.2 roomsAndPassagesWall_subset_frontier,
      euclideanHausdorffMeasure_roomsAndPassagesWall]
    exact one_ne_zero
  obtain ⟨C, -, hC⟩ :=
    W1p.exists_norm_value_le_mul_norm_gradient_of_mem_w1pVanishingOnSubmodule (p := 2)
      ENNReal.ofNat_ne_top hΩ isBounded_roomsAndPassages
      isConnected_roomsAndPassages.isPreconnected hΓ
  exact not_exists_norm_value_le_mul_norm_gradient_roomsAndPassages ENNReal.ofNat_ne_top ⟨C, hC⟩

/-- **Rooms and passages is not a Lipschitz domain**: its frontier is compact, so a Lipschitz
domain structure would have a uniform Lipschitz constant. -/
theorem not_isLipschitzDomain_roomsAndPassages :
    ¬ (roomsAndPassages : Set (WithLp 2 (ℝ × ℝ))).IsLipschitzDomain ℝ := fun h => by
  obtain ⟨L, hL⟩ := h.exists_isLipschitzDomainWith
    (isBounded_roomsAndPassages.isCompact_closure.of_isClosed_subset isClosed_frontier
      frontier_subset_closure)
  exact not_isLipschitzDomainWith_roomsAndPassages L hL

end TauCeti
