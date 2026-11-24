/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Inverse
import Mathlib.Algebra.Order.Interval.Set.Group
import TauCeti.Dynamics.Billiard.Continuous
import TauCeti.Dynamics.Billiard.GeneratingFunction
import TauCeti.Topology.Constructions.SumProd
import TauCeti.Topology.Instances.AddCircle.Coe

/-!
# The billiard map on the closed cylinder

Let `χ` be an arclength parametrization of the boundary of a strictly convex billiard table
(`TauCeti.StrictConvexBilliardTable`), with period `L`, and let `B(s, v) = (t, w)` be its
next-collision map on the open strip `ℝ × (-1, 1)`. The tangential component `v = cos δ` of a state
is the cosine of the angle `δ` between the outgoing velocity and the tangent, so the open strip is
the phase space `δ ∈ (0, π)` read in the coordinate `cos δ`.

As `v → 1` the ball leaves almost along the tangent `χ'(s)` and lands almost at once: the next
collision parameter tends to `s` and the next tangential component to `1`. As `v → -1` it leaves
almost along `-χ'(s)` and lands just short of `χ(s + L)`, with tangential component tending to `-1`.
So `B` extends to the closed strip `ℝ × [-1, 1]` by the identity on the line `v = 1` and by the
deck translation `(s, -1) ↦ (s + L, -1)` on the line `v = -1`
(`TauCeti.StrictConvexBilliardTable.closedNextParam`,
`TauCeti.StrictConvexBilliardTable.closedNextTangential`). For fixed `s` the extended collision
parameter is strictly decreasing on `[-1, 1]`
(`TauCeti.StrictConvexBilliardTable.strictAntiOn_closedNextParam`), and the extension still
satisfies the time reversal `B'(t, -w) = (s + L, -v)`, so it is a bijection of the closed strip
with inverse `τ⁻¹ ∘ ι ∘ B' ∘ ι` (`TauCeti.StrictConvexBilliardTable.closedNextCollisionEquiv`),
where `ι(s, v) = (s, -v)` and `τ(s, v) = (s + L, v)`.

The extension is continuous, for every table without further smoothness
(`TauCeti.StrictConvexBilliardTable.continuousOn_closedNextParam`,
`TauCeti.StrictConvexBilliardTable.continuousOn_closedNextTangential`). At the boundary this rests
on the monotonicity in `v`: the collision parameter of `(s, v)` lies between `s` and the collision
parameter of `(s, v₀)` for `v₀ < v`, and the latter is close to `s` uniformly for `s` near `s₀`
once `v₀` is close to `1`. The tangential component is `⟪u, χ'(t)⟫` on the whole closed strip,
where `u` is the outgoing velocity, so it is continuous as soon as the collision parameter is.

The extension descends to a homeomorphism `T'` of the closed cylinder `AddCircle L × [-1, 1]`
(`TauCeti.StrictConvexBilliardTable.closedBilliardHomeomorph`) that fixes both boundary circles
pointwise (`TauCeti.StrictConvexBilliardTable.closedBilliardMap_one`,
`TauCeti.StrictConvexBilliardTable.closedBilliardMap_neg_one`) and restricts to the billiard map on
the open cylinder (`TauCeti.StrictConvexBilliardTable.closedBilliardMap_inclusion`). In the angle
coordinate `δ`, the circle `v = 1` is `δ = 0` and `v = -1` is `δ = π`.

## Main definitions

* `TauCeti.StrictConvexBilliardTable.closedNextParam`,
  `TauCeti.StrictConvexBilliardTable.closedNextTangential`: the next-collision map extended to the
  closed strip `ℝ × [-1, 1]`.
* `TauCeti.StrictConvexBilliardTable.closedNextCollisionEquiv`: the extension as a bijection of
  `ℝ × [-1, 1]`, and `TauCeti.StrictConvexBilliardTable.closedNextCollisionHomeomorph`, as a
  homeomorphism.
* `TauCeti.StrictConvexBilliardTable.closedBilliardMap`: the billiard map extended to the closed
  cylinder `AddCircle L × [-1, 1]`, and
  `TauCeti.StrictConvexBilliardTable.closedBilliardHomeomorph`, as a homeomorphism.

## References

* Anatole Katok and Boris Hasselblatt, *Introduction to the Modern Theory of Dynamical Systems*,
  Cambridge University Press, 1995, Section 9.2.
* Serge Tabachnikov, *Geometry and Billiards*, Student Mathematical Library 30, American
  Mathematical Society, 2005, Chapter 3.
-/

public section

noncomputable section

open Function Set Filter Topology Module
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} (χ : StrictConvexBilliardTable o)

/-! ### The extension to the closed strip -/

/-- The next collision parameter extended to the closed strip `ℝ × [-1, 1]`: it is `s` on the line
`v = 1`, `s + L` on the line `v = -1`, and the next collision parameter `nextParam s v` on the open
strip. Its values for `v ∉ [-1, 1]` carry no meaning. -/
def closedNextParam (s v : ℝ) : ℝ :=
  if v ≤ -1 then s + χ.period else if 1 ≤ v then s else χ.nextParam s v

/-- The next tangential component extended to the closed strip `ℝ × [-1, 1]`: it is `v` on the two
boundary lines `v = ±1`, and `nextTangential s v` on the open strip. -/
def closedNextTangential (s v : ℝ) : ℝ :=
  if v ≤ -1 then v else if 1 ≤ v then v else χ.nextTangential s v

theorem closedNextParam_of_mem_Ioo {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.closedNextParam s v = χ.nextParam s v := by
  simp [closedNextParam, not_le.2 hv.1, not_le.2 hv.2]

theorem closedNextTangential_of_mem_Ioo {s v : ℝ} (hv : v ∈ Ioo (-1) 1) :
    χ.closedNextTangential s v = χ.nextTangential s v := by
  simp [closedNextTangential, not_le.2 hv.1, not_le.2 hv.2]

@[simp]
theorem closedNextParam_one (s : ℝ) : χ.closedNextParam s 1 = s := by
  norm_num [closedNextParam]

@[simp]
theorem closedNextParam_neg_one (s : ℝ) : χ.closedNextParam s (-1) = s + χ.period := by
  simp [closedNextParam]

@[simp]
theorem closedNextTangential_one (s : ℝ) : χ.closedNextTangential s 1 = 1 := by
  simp [closedNextTangential]

@[simp]
theorem closedNextTangential_neg_one (s : ℝ) : χ.closedNextTangential s (-1) = -1 := by
  simp [closedNextTangential]

/-- The extended next-collision map commutes with the deck translation `τ(s, v) = (s + L, v)`. -/
@[simp]
theorem closedNextParam_add_period (s v : ℝ) :
    χ.closedNextParam (s + χ.period) v = χ.closedNextParam s v + χ.period := by
  unfold closedNextParam
  split_ifs with h₁ h₂
  · rfl
  · rfl
  · exact χ.nextParam_add_period ⟨not_le.1 h₁, not_le.1 h₂⟩

@[simp]
theorem closedNextTangential_add_period (s v : ℝ) :
    χ.closedNextTangential (s + χ.period) v = χ.closedNextTangential s v := by
  unfold closedNextTangential
  split_ifs with h₁ h₂
  · rfl
  · rfl
  · exact χ.nextTangential_add_period ⟨not_le.1 h₁, not_le.1 h₂⟩

theorem closedNextParam_of_le_neg_one (s : ℝ) {v : ℝ} (hv : v ≤ -1) :
    χ.closedNextParam s v = s + χ.period := by
  simp [closedNextParam, hv]

theorem closedNextParam_of_one_le (s : ℝ) {v : ℝ} (hv : 1 ≤ v) : χ.closedNextParam s v = s := by
  simp [closedNextParam, hv, show ¬v ≤ -1 by linarith]

theorem closedNextTangential_of_notMem_Ioo (s : ℝ) {v : ℝ} (hv : v ∉ Ioo (-1) 1) :
    χ.closedNextTangential s v = v := by
  unfold closedNextTangential
  split_ifs with h₁ h₂
  · rfl
  · rfl
  · exact absurd ⟨not_le.1 h₁, not_le.1 h₂⟩ hv

/-- The extended next collision parameter lies in `[s, s + L]`. -/
theorem closedNextParam_mem_Icc (s v : ℝ) : χ.closedNextParam s v ∈ Icc s (s + χ.period) := by
  by_cases hv : v ∈ Ioo (-1) 1
  · rw [χ.closedNextParam_of_mem_Ioo hv]
    exact Ioo_subset_Icc_self (χ.nextParam_mem_Ioo hv)
  rcases le_or_gt v (-1) with h | h
  · simp [χ.closedNextParam_of_le_neg_one s h, χ.period_pos.le]
  · simp [χ.closedNextParam_of_one_le s (not_lt.1 fun h' ↦ hv ⟨h, h'⟩), χ.period_pos.le]

/-- The extended next tangential component maps `[-1, 1]` into itself. -/
theorem closedNextTangential_mem_Icc (s : ℝ) {v : ℝ} (hv : v ∈ Icc (-1) 1) :
    χ.closedNextTangential s v ∈ Icc (-1) 1 := by
  rcases hv.1.eq_or_lt with rfl | h₁
  · simp
  rcases hv.2.eq_or_lt with rfl | h₂
  · simp
  rw [χ.closedNextTangential_of_mem_Ioo ⟨h₁, h₂⟩]
  exact Ioo_subset_Icc_self (χ.nextTangential_mem_Ioo ⟨h₁, h₂⟩)

/-- For fixed `s`, the extended next collision parameter is strictly decreasing on `[-1, 1]`, from
`s + L` at `v = -1` to `s` at `v = 1`. -/
theorem strictAntiOn_closedNextParam (s : ℝ) :
    StrictAntiOn (χ.closedNextParam s) (Icc (-1) 1) := by
  intro v hv w hw hvw
  have hw₁ : -1 < w := hv.1.trans_lt hvw
  have hv₂ : v < 1 := hvw.trans_le hw.2
  rcases hv.1.eq_or_lt with rfl | h₁
  · rcases hw.2.eq_or_lt with rfl | h₂
    · simp [χ.period_pos]
    simpa [χ.closedNextParam_of_mem_Ioo ⟨hw₁, h₂⟩] using (χ.nextParam_mem_Ioo ⟨hw₁, h₂⟩).2
  rw [χ.closedNextParam_of_mem_Ioo ⟨h₁, hv₂⟩]
  rcases hw.2.eq_or_lt with rfl | h₂
  · simpa using (χ.nextParam_mem_Ioo ⟨h₁, hv₂⟩).1
  rw [χ.closedNextParam_of_mem_Ioo ⟨hw₁, h₂⟩]
  exact χ.strictAntiOn_nextParam s ⟨h₁, hv₂⟩ ⟨hw₁, h₂⟩ hvw

/-- The extended next tangential component is the tangential component `⟪u, χ'(t)⟫` of the
outgoing velocity `u` at the extended next collision point `χ(t)`. -/
theorem closedNextTangential_eq_inner (s v : ℝ) :
    χ.closedNextTangential s v = ⟪χ.outgoingDir s v, deriv χ (χ.closedNextParam s v)⟫ := by
  by_cases hv : v ∈ Ioo (-1) 1
  · rw [χ.closedNextTangential_of_mem_Ioo hv, χ.closedNextParam_of_mem_Ioo hv, nextTangential_def]
  rw [χ.closedNextTangential_of_notMem_Ioo s hv]
  rcases le_or_gt v (-1) with h | h
  · rw [χ.closedNextParam_of_le_neg_one s h, deriv_add_period, real_inner_comm,
      inner_deriv_outgoingDir]
  · rw [χ.closedNextParam_of_one_le s (not_lt.1 fun h' ↦ hv ⟨h, h'⟩), real_inner_comm,
      inner_deriv_outgoingDir]

/-! ### Time reversal and bijectivity -/

/-- Time reversal of the extended collision parameter: `B'(t, -w)` has parameter `s + L`, where
`(t, w) = B'(s, v)`. -/
theorem closedNextParam_closedNextParam_neg_closedNextTangential (s v : ℝ) :
    χ.closedNextParam (χ.closedNextParam s v) (-χ.closedNextTangential s v) = s + χ.period := by
  by_cases hv : v ∈ Ioo (-1) 1
  · have hw := χ.nextTangential_mem_Ioo (s := s) hv
    rw [χ.closedNextTangential_of_mem_Ioo hv, χ.closedNextParam_of_mem_Ioo hv,
      χ.closedNextParam_of_mem_Ioo ⟨by linarith [hw.2], by linarith [hw.1]⟩]
    exact χ.nextParam_nextParam_neg_nextTangential hv
  rw [χ.closedNextTangential_of_notMem_Ioo s hv]
  rcases le_or_gt v (-1) with h | h
  · rw [χ.closedNextParam_of_le_neg_one s h, χ.closedNextParam_of_one_le _ (by linarith)]
  · have h' : 1 ≤ v := not_lt.1 fun h' ↦ hv ⟨h, h'⟩
    rw [χ.closedNextParam_of_one_le s h', χ.closedNextParam_of_le_neg_one _ (by linarith)]

/-- Time reversal of the extended tangential component: `B'(t, -w)` has tangential component `-v`,
where `(t, w) = B'(s, v)`. -/
theorem closedNextTangential_closedNextParam_neg_closedNextTangential (s v : ℝ) :
    χ.closedNextTangential (χ.closedNextParam s v) (-χ.closedNextTangential s v) = -v := by
  by_cases hv : v ∈ Ioo (-1) 1
  · have hw := χ.nextTangential_mem_Ioo (s := s) hv
    rw [χ.closedNextTangential_of_mem_Ioo hv, χ.closedNextParam_of_mem_Ioo hv,
      χ.closedNextTangential_of_mem_Ioo ⟨by linarith [hw.2], by linarith [hw.1]⟩]
    exact χ.nextTangential_nextParam_neg_nextTangential hv
  rw [χ.closedNextTangential_of_notMem_Ioo s hv,
    χ.closedNextTangential_of_notMem_Ioo _ fun h ↦ hv (by simpa using Set.neg_mem_Ioo_iff.1 h)]

/-- The tangential component `-w` of the extended next collision of `(s, -v)` lies in `[-1, 1]`: it
is the tangential component of the state that the inverse of the extended map assigns to
`(s, v)`. -/
theorem neg_closedNextTangential_neg_mem_Icc (s : ℝ) (v : Icc (-1 : ℝ) 1) :
    -χ.closedNextTangential s (-v) ∈ Icc (-1 : ℝ) 1 :=
  Set.neg_mem_Icc_iff.2 <| by
    simpa using χ.closedNextTangential_mem_Icc s (Set.neg_mem_Icc_iff.2 (by simp))

/-- The next-collision map extended to the closed strip `ℝ × [-1, 1]`, as a bijection. It is the
identity on the line `v = 1` and the deck translation on the line `v = -1`; its inverse is
`τ⁻¹ ∘ ι ∘ B' ∘ ι`. -/
def closedNextCollisionEquiv : ℝ × Icc (-1 : ℝ) 1 ≃ ℝ × Icc (-1 : ℝ) 1 where
  toFun x := (χ.closedNextParam x.1 x.2, ⟨χ.closedNextTangential x.1 x.2,
      χ.closedNextTangential_mem_Icc x.1 x.2.property⟩)
  invFun x := (χ.closedNextParam x.1 (-x.2) - χ.period,
    ⟨-χ.closedNextTangential x.1 (-x.2), χ.neg_closedNextTangential_neg_mem_Icc x.1 x.2⟩)
  left_inv x := by
    ext
    · simp [χ.closedNextParam_closedNextParam_neg_closedNextTangential]
    · simp [χ.closedNextTangential_closedNextParam_neg_closedNextTangential]
  right_inv x := by
    -- The inverse moves the parameter back by one period; undo this by the deck translation.
    have hp := χ.closedNextParam_add_period (χ.closedNextParam x.1 (-x.2) - χ.period)
      (-χ.closedNextTangential x.1 (-x.2))
    have ht := χ.closedNextTangential_add_period (χ.closedNextParam x.1 (-x.2) - χ.period)
      (-χ.closedNextTangential x.1 (-x.2))
    rw [sub_add_cancel] at hp ht
    ext
    · simp only
      linarith [χ.closedNextParam_closedNextParam_neg_closedNextTangential x.1 (-x.2)]
    · simp [← ht, χ.closedNextTangential_closedNextParam_neg_closedNextTangential]

@[simp]
theorem closedNextCollisionEquiv_apply (x : ℝ × Icc (-1 : ℝ) 1) :
    χ.closedNextCollisionEquiv x = (χ.closedNextParam x.1 x.2, ⟨χ.closedNextTangential x.1 x.2,
      χ.closedNextTangential_mem_Icc x.1 x.2.property⟩) := by
  rfl

@[simp]
theorem closedNextCollisionEquiv_symm_apply (x : ℝ × Icc (-1 : ℝ) 1) :
    χ.closedNextCollisionEquiv.symm x = (χ.closedNextParam x.1 (-x.2) - χ.period,
      ⟨-χ.closedNextTangential x.1 (-x.2), χ.neg_closedNextTangential_neg_mem_Icc x.1 x.2⟩) := by
  rfl

/-! ### Continuity -/

/-- Near a state `(s₀, v₀)` of the open strip, the displacement `nextParam s v₀ - s` of the
collision parameter at the fixed tangential component `v₀` stays in any neighbourhood of its value
at `s₀`. -/
private theorem eventually_nextParam_sub_mem {s₀ v₀ : ℝ}
    (hv₀ : v₀ ∈ Ioo (-1) 1) {U : Set ℝ} (hU : U ∈ 𝓝 (χ.nextParam s₀ v₀ - s₀)) (w : ℝ) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (s₀, w), χ.nextParam p.1 v₀ - p.1 ∈ U := by
  have hB : ContinuousAt (fun s ↦ χ.nextParam s v₀) s₀ :=
    (χ.continuousAt_nextParam hv₀).comp (f := fun s : ℝ ↦ (s, v₀))
      (continuous_id.prodMk continuous_const).continuousAt
  exact (continuous_fst.tendsto (s₀, w)).eventually ((hB.sub continuousAt_id).eventually_mem hU)

/-- As `v → 1` on the closed strip, the extended next collision parameter approaches `s`
uniformly. -/
private theorem tendsto_closedNextParam_sub_one (s₀ : ℝ) :
    Tendsto (fun p : ℝ × ℝ ↦ χ.closedNextParam p.1 p.2 - p.1)
      (𝓝[univ ×ˢ Icc (-1) 1] (s₀, 1)) (𝓝 0) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · exact Eventually.of_forall fun p ↦ by linarith [(χ.closedNextParam_mem_Icc p.1 p.2).1]
  set c := min a χ.period / 2 with hcdef
  have hc : 0 < c := by have := χ.period_pos; positivity
  have hca : c < a := by linarith [min_le_left a χ.period, hcdef]
  have hcL : c < χ.period := by linarith [min_le_right a χ.period, χ.period_pos, hcdef]
  obtain ⟨v₀, hv₀, hv₀c⟩ : s₀ + c ∈ χ.nextParam s₀ '' Ioo (-1) 1 := by
    rw [image_nextParam_Ioo]
    exact ⟨by linarith, by linarith⟩
  have h₁ := χ.eventually_nextParam_sub_mem hv₀ (U := Iio a)
    (Iio_mem_nhds (by rw [hv₀c]; linarith)) 1
  have h₂ : ∀ᶠ p : ℝ × ℝ in 𝓝 (s₀, 1), v₀ < p.2 :=
    (continuous_snd.tendsto (s₀, (1 : ℝ))).eventually (lt_mem_nhds hv₀.2)
  filter_upwards [nhdsWithin_le_nhds h₁, nhdsWithin_le_nhds h₂, self_mem_nhdsWithin]
    with p hp₁ hp₂ hp
  rcases hp.2.2.eq_or_lt with h | h
  · rw [h, closedNextParam_one, sub_self]
    exact ha
  have hpI : p.2 ∈ Ioo (-1) 1 := ⟨by linarith [hv₀.1], h⟩
  rw [χ.closedNextParam_of_mem_Ioo hpI]
  linarith [χ.strictAntiOn_nextParam p.1 hv₀ hpI hp₂, mem_Iio.1 hp₁]

/-- As `v → -1` on the closed strip, the extended next collision parameter approaches `s + L`
uniformly. -/
private theorem tendsto_closedNextParam_sub_neg_one (s₀ : ℝ) :
    Tendsto (fun p : ℝ × ℝ ↦ χ.closedNextParam p.1 p.2 - p.1)
      (𝓝[univ ×ˢ Icc (-1) 1] (s₀, -1)) (𝓝 χ.period) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  swap
  · exact Eventually.of_forall fun p ↦ by linarith [(χ.closedNextParam_mem_Icc p.1 p.2).2]
  set c := min (χ.period - a) χ.period / 2 with hcdef
  have hc : 0 < c := by have := χ.period_pos; have : 0 < χ.period - a := by linarith
                        positivity
  have hca : a < χ.period - c := by linarith [min_le_left (χ.period - a) χ.period, hcdef]
  have hcL : c < χ.period := by linarith [min_le_right (χ.period - a) χ.period, χ.period_pos, hcdef]
  obtain ⟨v₀, hv₀, hv₀c⟩ : s₀ + (χ.period - c) ∈ χ.nextParam s₀ '' Ioo (-1) 1 := by
    rw [image_nextParam_Ioo]
    exact ⟨by linarith, by linarith⟩
  have h₁ := χ.eventually_nextParam_sub_mem hv₀ (U := Ioi a)
    (Ioi_mem_nhds (by rw [hv₀c]; linarith)) (-1)
  have h₂ : ∀ᶠ p : ℝ × ℝ in 𝓝 (s₀, -1), p.2 < v₀ :=
    (continuous_snd.tendsto (s₀, (-1 : ℝ))).eventually (gt_mem_nhds hv₀.1)
  filter_upwards [nhdsWithin_le_nhds h₁, nhdsWithin_le_nhds h₂, self_mem_nhdsWithin]
    with p hp₁ hp₂ hp
  rcases hp.2.1.eq_or_lt with h | h
  · rw [← h, closedNextParam_neg_one, add_sub_cancel_left]
    exact ha
  have hpI : p.2 ∈ Ioo (-1) 1 := ⟨h, by linarith [hv₀.2]⟩
  rw [χ.closedNextParam_of_mem_Ioo hpI]
  linarith [χ.strictAntiOn_nextParam p.1 hpI hv₀ hp₂, mem_Ioi.1 hp₁]

/-- **Continuity of the extended collision parameter.** The next collision
parameter, extended by `s` on `v = 1` and by `s + L` on `v = -1`, is continuous on the closed
strip `ℝ × [-1, 1]`. -/
theorem continuousOn_closedNextParam :
    ContinuousOn (fun p : ℝ × ℝ ↦ χ.closedNextParam p.1 p.2) (univ ×ˢ Icc (-1) 1) := by
  rintro ⟨s, v⟩ ⟨-, hv⟩
  have hsub : ∀ {l : ℝ}, Tendsto (fun p : ℝ × ℝ ↦ χ.closedNextParam p.1 p.2 - p.1)
      (𝓝[univ ×ˢ Icc (-1) 1] (s, v)) (𝓝 l) → χ.closedNextParam s v = l + s →
      ContinuousWithinAt (fun p : ℝ × ℝ ↦ χ.closedNextParam p.1 p.2) (univ ×ˢ Icc (-1) 1)
        (s, v) := fun h hl ↦ by
    have := h.add (continuous_fst.continuousWithinAt (s := univ ×ˢ Icc (-1 : ℝ) 1)
      (x := (s, v))).tendsto
    simpa [ContinuousWithinAt, hl] using this
  rcases hv.1.eq_or_lt with rfl | h₁
  · exact hsub (χ.tendsto_closedNextParam_sub_neg_one s) (by simp [add_comm])
  rcases hv.2.eq_or_lt with rfl | h₂
  · exact hsub (χ.tendsto_closedNextParam_sub_one s) (by simp)
  refine ContinuousAt.continuousWithinAt ?_
  have hev : (fun p : ℝ × ℝ ↦ χ.nextParam p.1 p.2) =ᶠ[𝓝 (s, v)]
      fun p ↦ χ.closedNextParam p.1 p.2 := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds (⟨mem_univ s, ⟨h₁, h₂⟩⟩ :
      (s, v) ∈ univ ×ˢ Ioo (-1 : ℝ) 1)] with p hp
    exact (χ.closedNextParam_of_mem_Ioo hp.2).symm
  exact (χ.continuousAt_nextParam ⟨h₁, h₂⟩).congr hev

/-- **Continuity of the extended tangential component.** The next tangential
component, extended by `v` on the lines `v = ±1`, is continuous on the closed strip
`ℝ × [-1, 1]`. -/
theorem continuousOn_closedNextTangential :
    ContinuousOn (fun p : ℝ × ℝ ↦ χ.closedNextTangential p.1 p.2) (univ ×ˢ Icc (-1) 1) := by
  have hd : Continuous (deriv χ) := χ.continuous_deriv
  have hu : Continuous fun p : ℝ × ℝ ↦ χ.outgoingDir p.1 p.2 := by
    simp only [outgoingDir_def]
    exact (continuous_snd.smul (hd.comp continuous_fst)).add
      ((continuous_const.sub (continuous_snd.pow 2)).sqrt.smul
        (o.rightAngleRotation.continuous.comp (hd.comp continuous_fst)))
  exact (hu.continuousOn.inner (hd.comp_continuousOn χ.continuousOn_closedNextParam)).congr
    fun p _ ↦ χ.closedNextTangential_eq_inner p.1 p.2

/-- The extended next-collision bijection of `ℝ × [-1, 1]` is continuous. -/
theorem continuous_closedNextCollisionEquiv :
    Continuous χ.closedNextCollisionEquiv :=
  ((χ.continuousOn_closedNextParam.prodMk
    χ.continuousOn_closedNextTangential).continuous_restrict_univ_prod
      fun x ↦ χ.closedNextTangential_mem_Icc x.1 x.2.property).congr fun x ↦ by simp

/-- The inverse of the extended next-collision bijection of `ℝ × [-1, 1]` is continuous. -/
theorem continuous_closedNextCollisionEquiv_symm :
    Continuous χ.closedNextCollisionEquiv.symm := by
  have hι : ContinuousOn (fun p : ℝ × ℝ ↦ (p.1, -p.2)) (univ ×ˢ Icc (-1 : ℝ) 1) :=
    (continuous_fst.prodMk continuous_snd.neg).continuousOn
  have hmaps : MapsTo (fun p : ℝ × ℝ ↦ (p.1, -p.2)) (univ ×ˢ Icc (-1 : ℝ) 1)
      (univ ×ˢ Icc (-1 : ℝ) 1) :=
    fun p hp ↦ ⟨mem_univ _, Set.neg_mem_Icc_iff.2 (by simpa using hp.2)⟩
  exact ((((χ.continuousOn_closedNextParam.comp hι hmaps).sub
    (continuousOn_const (c := χ.period))).prodMk
    (χ.continuousOn_closedNextTangential.comp hι hmaps).neg).continuous_restrict_univ_prod
      fun x ↦ χ.neg_closedNextTangential_neg_mem_Icc x.1 x.2).congr fun x ↦ by simp

/-- **The closed strip.** The next-collision map extends to a homeomorphism of the
closed strip `ℝ × [-1, 1]`, equal to the identity on `v = 1` and to the deck translation
`(s, -1) ↦ (s + L, -1)` on `v = -1`. -/
def closedNextCollisionHomeomorph :
    ℝ × Icc (-1 : ℝ) 1 ≃ₜ ℝ × Icc (-1 : ℝ) 1 where
  toEquiv := χ.closedNextCollisionEquiv
  continuous_toFun := χ.continuous_closedNextCollisionEquiv
  continuous_invFun := χ.continuous_closedNextCollisionEquiv_symm

@[simp]
theorem coe_closedNextCollisionHomeomorph :
    ⇑χ.closedNextCollisionHomeomorph = χ.closedNextCollisionEquiv :=
  (rfl)

@[simp]
theorem coe_closedNextCollisionHomeomorph_symm :
    ⇑χ.closedNextCollisionHomeomorph.symm = χ.closedNextCollisionEquiv.symm :=
  (rfl)

/-! ### The closed cylinder -/

/-- The billiard map extended to the closed cylinder `AddCircle L × [-1, 1]`, induced by the
extended next-collision map of the closed strip. It fixes both boundary circles pointwise and
restricts to the billiard map on the open cylinder. -/
def closedBilliardMap :
    AddCircle χ.period × Icc (-1 : ℝ) 1 ≃ AddCircle χ.period × Icc (-1 : ℝ) 1 :=
  AddCircle.prodEquivOfLift χ.closedNextCollisionEquiv fun s v ↦ by simp

/-- The extended billiard map sends the class of a state `(s, v)` of the closed strip to the class
of its extended next collision. -/
@[simp]
theorem closedBilliardMap_coe (s : ℝ) (v : Icc (-1 : ℝ) 1) :
    χ.closedBilliardMap ((s : AddCircle χ.period), v) =
      ((χ.closedNextParam s v : AddCircle χ.period),
        ⟨χ.closedNextTangential s v, χ.closedNextTangential_mem_Icc s v.property⟩) := by
  simp [closedBilliardMap]

/-- The inverse of the extended billiard map sends the class of a state `(s, v)` of the closed
strip to the class of `(t, -w)`, where `(t, w)` is the extended next collision of `(s, -v)`. -/
@[simp]
theorem closedBilliardMap_symm_coe (s : ℝ) (v : Icc (-1 : ℝ) 1) :
    χ.closedBilliardMap.symm ((s : AddCircle χ.period), v) =
      ((χ.closedNextParam s (-v) : AddCircle χ.period),
        ⟨-χ.closedNextTangential s (-v), χ.neg_closedNextTangential_neg_mem_Icc s v⟩) := by
  simp only [closedBilliardMap, AddCircle.prodEquivOfLift_symm_coe,
    closedNextCollisionEquiv_symm_apply]
  rw [← AddCircle.coe_add_period, sub_add_cancel]

/-- The extended billiard map fixes the boundary circle `v = 1` pointwise. -/
@[simp]
theorem closedBilliardMap_one (θ : AddCircle χ.period) :
    χ.closedBilliardMap (θ, ⟨1, by norm_num, le_rfl⟩) = (θ, ⟨1, by norm_num, le_rfl⟩) := by
  induction θ using QuotientAddGroup.induction_on with | H s => ?_
  simp

/-- The extended billiard map fixes the boundary circle `v = -1` pointwise. -/
@[simp]
theorem closedBilliardMap_neg_one (θ : AddCircle χ.period) :
    χ.closedBilliardMap (θ, ⟨-1, le_rfl, by norm_num⟩) = (θ, ⟨-1, le_rfl, by norm_num⟩) := by
  induction θ using QuotientAddGroup.induction_on with | H s => ?_
  ext <;> simp

/-- On the open cylinder `AddCircle L × (-1, 1)` the extended billiard map is the billiard map. -/
theorem closedBilliardMap_inclusion (x : AddCircle χ.period × Ioo (-1 : ℝ) 1) :
    χ.closedBilliardMap (x.1, inclusion Ioo_subset_Icc_self x.2) =
      Prod.map id (inclusion Ioo_subset_Icc_self) (χ.billiardMap x) := by
  obtain ⟨θ, v⟩ := x
  induction θ using QuotientAddGroup.induction_on with | H s => ?_
  ext
  · simp [χ.closedNextParam_of_mem_Ioo v.property]
  · simp [χ.closedNextTangential_of_mem_Ioo v.property]

/-- **The closed cylinder.** The billiard map extends to a homeomorphism `T'` of
the closed cylinder `AddCircle L × [-1, 1]` that fixes both boundary circles pointwise
(`TauCeti.StrictConvexBilliardTable.closedBilliardMap_one`,
`TauCeti.StrictConvexBilliardTable.closedBilliardMap_neg_one`) and restricts to the billiard map on
the open cylinder (`TauCeti.StrictConvexBilliardTable.closedBilliardMap_inclusion`). -/
def closedBilliardHomeomorph :
    AddCircle χ.period × Icc (-1 : ℝ) 1 ≃ₜ AddCircle χ.period × Icc (-1 : ℝ) 1 where
  toEquiv := χ.closedBilliardMap
  continuous_toFun := AddCircle.continuous_prod_of_lift χ.continuous_closedNextCollisionEquiv
    fun s v ↦ by simp
  continuous_invFun :=
    AddCircle.continuous_prod_of_lift χ.continuous_closedNextCollisionEquiv_symm
      fun s v ↦ by simp [closedBilliardMap]

@[simp]
theorem coe_closedBilliardHomeomorph :
    ⇑χ.closedBilliardHomeomorph = χ.closedBilliardMap :=
  (rfl)

@[simp]
theorem coe_closedBilliardHomeomorph_symm :
    ⇑χ.closedBilliardHomeomorph.symm = χ.closedBilliardMap.symm :=
  (rfl)

end StrictConvexBilliardTable

end TauCeti
