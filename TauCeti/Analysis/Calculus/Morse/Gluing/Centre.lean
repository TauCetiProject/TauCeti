/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Passage
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.DenselyOrdered
import TauCeti.Analysis.Calculus.Morse.Gluing.TransverseDisc
import TauCeti.Analysis.Calculus.RadialRescaleGraph
import TauCeti.Topology.Homeomorph.CompactQuotient

/-!
# Gluing into a disc through the centre of the split hyperbolic box

The gluing theorems for the split hyperbolic flow `φ t (x, y) = (e^{-t} x, e^t y)`
(`TauCeti.splitQuadraticFlow`) on the box `‖x‖ ≤ ε, ‖y‖ ≤ ε` join a Lipschitz graph
`y ↦ (g y, y)` in the entrance face `‖x‖ = ε` to a Lipschitz graph `x ↦ (x, k x)` in the exit face
`‖y‖ = ε`. This file treats the case where the second disc passes through the centre `(0, 0)`
instead: `x ↦ (x, k x)` with `k 0 = 0`, a disc transverse at the rest point to the unstable set
`x = 0`.

The orbit through the entrance point `(g y, y)` reaches the graph of `k` at time `T` exactly when
`e^T y = k (e^{-T} g y)`, that is, when `y` is a fixed point of `y ↦ e^{-T} k (e^{-T} g y)`. For
large `T` this map is a contraction of a closed ball, with Lipschitz constant
`e^{-2T} Kk Kg`, so it has a fixed point
(`TauCeti.eventually_exists_splitQuadraticFlow_snd_eq`). The orbit then stays in the box up to time
`T`, and the point where it meets the graph of `k` tends to the centre as `T → ∞`. So, for every
large `T`, some orbit from the entrance disc reaches the disc through the centre at time `T`, close
to the centre.

The image of a disc through the centre which is strictly differentiable at `0`, with the
derivative of its contracting component `x` invertible, contains such a graph near the centre
(`TauCeti.exists_lipschitzOnWith_graph_of_hasStrictFDerivAt`), by the inverse function theorem.

**The compactified gluing arc.** Write `l = e^{-T}` for the gluing parameter. The orbit through
`(g y, y)` meets the graph of `k` at time `T` exactly when `y` is a fixed point of the contraction
`y ↦ l • k (l • g y)`, so for each small `l` there is exactly one such orbit, and its entrance point
depends continuously on `l`. At `l = 0` the fixed point is `0`, which gives the broken orbit
entering along the stable set at `(g 0, 0)` and resting at the centre. Recording a glued orbit by
the pair of its entrance point and the point where it meets the graph of `k`
(`TauCeti.splitCenterGluingPairs`), these pairs form a half-open arc, whose closure adds exactly
the broken pair `((g 0, 0), 0)` and is homeomorphic to a closed interval, with the parameter
`l = ‖x‖ / ε` read off the glued point `(x, k x)`
(`TauCeti.eventually_exists_homeomorph_closure_splitCenterGluingPairs`). For discs given by
strictly differentiable maps transverse to the stable set and to the unstable set, this arc
consists of exactly the orbits from the first disc to the second near the broken orbit
(`TauCeti.exists_homeomorph_closure_splitCenterGluingPairs_of_hasStrictFDerivAt`). Unlike the
gluing arc between the entrance and exit faces
(`TauCeti.exists_homeomorph_closure_splitGluingPairs`), the second disc passes through the rest
point, so the broken orbit does not leave the box.

In Morse theory, the entrance disc is a piece of the unstable manifold of a critical point `p`
which flows into the critical point `a` at the centre of the box, and the disc through the centre is
a piece of a submanifold through `a` transverse to the unstable manifold of `a`, such as the stable
manifold of a second pseudo-gradient. The glued orbits are then points of `W^u(p)` on that
submanifold converging to `a`.

## Main results

* `TauCeti.exists_lipschitzOnWith_graph_of_hasStrictFDerivAt`: near the centre, the image of a disc
  through the centre transverse to the unstable set contains a Lipschitz graph `x ↦ (x, k x)` with
  `k 0 = 0`.
* `TauCeti.eventually_exists_splitQuadraticFlow_snd_eq`: for all large `T`, the orbit through some
  point of the entrance graph stays in the box up to time `T` and meets the graph of `k` at time
  `T`, in a prescribed neighbourhood of the centre.
* `TauCeti.splitCenterGluingPairs`: the entrance points and glued points of the orbits from the
  entrance graph to the graph through the centre.
* `TauCeti.eventually_exists_homeomorph_closure_splitCenterGluingPairs`: their closure is a closed
  interval, adding only the broken pair.
* `TauCeti.exists_homeomorph_closure_splitCenterGluingPairs_of_hasStrictFDerivAt`: the same for
  transverse discs, together with the identification of the glued orbits as all orbits from the
  first disc to the second near the broken orbit.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 3 (gluing with a pseudo-gradient linear near the critical points).
-/

public section

open Filter Metric Set Topology
open scoped NNReal

namespace TauCeti

variable {G Eₛ Eᵤ : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup Eₛ] [NormedSpace ℝ Eₛ] [NormedAddCommGroup Eᵤ] [NormedSpace ℝ Eᵤ]

/-- **A disc through the centre transverse to the unstable set contains a graph.** Let `χ` be a
disc through the centre `(0, 0)` of the split model, strictly differentiable at `0` with the
derivative of its contracting component `x` invertible. There is a Lipschitz graph `x ↦ (x, k x)`
over a closed ball of the contracting factor, with `k 0 = 0`, every point of which is `χ z` for
some `z` in a prescribed neighbourhood `V` of `0`; conversely, for `z` near `0`, the point `χ z`
lies on this graph. -/
theorem exists_lipschitzOnWith_graph_of_hasStrictFDerivAt [CompleteSpace G]
    {χ : G → WithLp 2 (Eₛ × Eᵤ)} {χ' : G →L[ℝ] WithLp 2 (Eₛ × Eᵤ)}
    (hχ : HasStrictFDerivAt χ χ' 0) (hχ' : (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L χ').IsInvertible)
    (hχ₀ : χ 0 = 0) {V : Set G} (hV : V ∈ 𝓝 0) :
    ∃ η > 0, ∃ (K : ℝ≥0) (k : Eₛ → Eᵤ), LipschitzOnWith K k (closedBall 0 η) ∧ k 0 = 0 ∧
      (∀ x ∈ closedBall 0 η, ∃ z ∈ V, χ z = WithLp.toLp 2 (x, k x)) ∧
      ∀ᶠ z in 𝓝 0, (χ z).fst ∈ closedBall 0 η ∧ (χ z).snd = k (χ z).fst := by
  obtain ⟨L, hL⟩ := hχ'
  -- The contracting component of `χ` is a local diffeomorphism at `0`; invert it.
  set a : G → Eₛ := fun z ↦ (χ z).fst with ha_def
  have ha : HasStrictFDerivAt a (L : G →L[ℝ] Eₛ) 0 := by
    rw [hL]
    exact (WithLp.fstL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp 0 hχ
  have ha₀ : a 0 = 0 := by simp [ha_def, hχ₀]
  have hσ := ha.to_localInverse
  have hσ₀ := ha.localInverse_apply_image
  have hright := ha.eventually_right_inverse
  have hleft := ha.eventually_left_inverse
  have hσt := ha.localInverse_tendsto
  rw [ha₀] at hσ hσ₀ hright hσt
  set σ := ha.localInverse a L 0
  -- The expanding component of `χ`, read over the contracting one.
  set k : Eₛ → Eᵤ := fun x ↦ (χ (σ x)).snd
  have hk : HasStrictFDerivAt k
      ((WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L χ') ∘L (L.symm : Eₛ →L[ℝ] G)) 0 := by
    have hχσ : HasStrictFDerivAt χ χ' (σ 0) := by rwa [hσ₀]
    exact ((WithLp.sndL 2 ℝ Eₛ Eᵤ).hasStrictFDerivAt.comp (σ 0) hχσ).comp 0 hσ
  obtain ⟨K, s, hs, hks⟩ := hk.exists_lipschitzOnWith
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hs (inter_mem (hσt hV) hright))
  refine ⟨η, hη, K, k, hks.mono fun x hx ↦ (hηs hx).1, by simp [k, hσ₀, hχ₀], fun x hx ↦ ?_, ?_⟩
  · obtain ⟨-, hxV, hxa⟩ := hηs hx
    exact ⟨σ x, hxV, WithLp.ofLp_injective 2 (Prod.ext (by simpa [ha_def] using hxa) (by simp [k]))⟩
  · -- Near `0`, the local inverse recovers `z` from the contracting component of `χ z`.
    have hη' : closedBall (0 : Eₛ) η ∈ 𝓝 (a 0) := by rw [ha₀]; exact closedBall_mem_nhds _ hη
    filter_upwards [ha.continuousAt.preimage_mem_nhds hη', hleft] with z hzη hz
    exact ⟨hzη, (congrArg (fun w ↦ (χ w).snd) hz).symm⟩

omit [NormedSpace ℝ Eᵤ] in
/-- Along the entrance graph `y ↦ (g y, y)` in the face `‖x‖ = ε`, scaled by a rate `l` with
`l ε ≤ η`, the contracting component stays over the ball of radius `η` on which the graph `k`
through the centre is defined, and `k` there has norm at most `Kk l ε`. -/
private theorem smul_mem_closedBall_and_norm_le {ε δ η l : ℝ} {Kk : ℝ≥0} {g : Eᵤ → Eₛ}
    {k : Eₛ → Eᵤ} (hη : 0 < η) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) (hl : 0 ≤ l) (h : l * ε ≤ η)
    {y : Eᵤ} (hy : y ∈ closedBall 0 δ) :
    l • g y ∈ closedBall (0 : Eₛ) η ∧ ‖k (l • g y)‖ ≤ Kk * (l * ε) := by
  have hn : ‖l • g y‖ = l * ε := by rw [norm_smul, Real.norm_of_nonneg hl, hgε y hy]
  have hmem : l • g y ∈ closedBall (0 : Eₛ) η := by rwa [mem_closedBall_zero_iff, hn]
  refine ⟨hmem, ?_⟩
  simpa [hk₀, hn] using hk.norm_sub_le hmem (mem_closedBall_self hη.le)

/-- For `l ∈ [0, l₀]` with `l₀ ≤ 1`, `l₀ ε ≤ η` and `l₀ Kk ε ≤ δ`, the map
`y ↦ l • k (l • g y)` sends the closed ball of radius `δ` into itself, and is Lipschitz there with
constant `l₀ Kk Kg`. -/
private theorem smul_comp_smul_mem_closedBall_and_dist_le {ε δ η l₀ : ℝ} {Kg Kk : ℝ≥0}
    {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hη : 0 < η) (hg : LipschitzOnWith Kg g (closedBall 0 δ))
    (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) {l : ℝ} (hl : l ∈ Icc 0 l₀)
    (hl₀₁ : l₀ ≤ 1) (h₁ : l₀ * ε ≤ η) (h₂ : l₀ * (Kk * ε) ≤ δ) {y y' : Eᵤ}
    (hy : y ∈ closedBall 0 δ) (hy' : y' ∈ closedBall 0 δ) :
    l • k (l • g y) ∈ closedBall (0 : Eᵤ) δ ∧
      dist (l • k (l • g y)) (l • k (l • g y')) ≤ l₀ * (Kk * Kg) * dist y y' := by
  obtain ⟨hl0, hll₀⟩ := hl
  have hε : 0 ≤ ε := hgε y hy ▸ norm_nonneg _
  have hlε : l * ε ≤ η := (mul_le_mul_of_nonneg_right hll₀ hε).trans h₁
  obtain ⟨hgy, hky⟩ := smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl0 hlε hy
  have hgy' := (smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl0 hlε hy').1
  have hl₁ : l ≤ 1 := hll₀.trans hl₀₁
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hl0]
    calc l * ‖k (l • g y)‖ ≤ 1 * (Kk * (l₀ * ε)) := by
          gcongr
          exact hky.trans (by gcongr)
      _ ≤ δ := by linarith
  · rw [dist_smul₀, Real.norm_of_nonneg hl0]
    calc l * dist (k (l • g y)) (k (l • g y')) ≤ l * (Kk * dist (l • g y) (l • g y')) := by
          gcongr
          exact hk.dist_le_mul _ hgy _ hgy'
      _ = l * (Kk * (l * dist (g y) (g y'))) := by rw [dist_smul₀, Real.norm_of_nonneg hl0]
      _ ≤ l * (Kk * (l * (Kg * dist y y'))) := by
          gcongr
          exact hg.dist_le_mul _ hy _ hy'
      _ = (l * l) * (Kk * Kg * dist y y') := by ring
      _ ≤ l₀ * (Kk * Kg * dist y y') := by
          gcongr
          nlinarith
      _ = l₀ * (Kk * Kg) * dist y y' := by ring

/-- **The contraction of gluing at the centre.** Under the conditions of
`smul_comp_smul_mem_closedBall_and_dist_le` and `l₀ Kk Kg < 1`, for `l ∈ [0, l₀]` the map
`y ↦ l • k (l • g y)` restricts to a contraction of the closed ball of radius `δ`, with constant
`l₀ Kk Kg`. -/
private theorem contractingWith_smul_comp_smul {ε δ η l₀ l : ℝ} {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ}
    {k : Eₛ → Eᵤ} (hη : 0 < η) (hg : LipschitzOnWith Kg g (closedBall 0 δ))
    (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε) (hk : LipschitzOnWith Kk k (closedBall 0 η))
    (hk₀ : k 0 = 0) (hl : l ∈ Icc 0 l₀) (hl₀₁ : l₀ ≤ 1) (h₁ : l₀ * ε ≤ η)
    (h₂ : l₀ * (Kk * ε) ≤ δ) (h₃ : l₀ * (Kk * Kg) < 1) :
    ∃ hmaps : MapsTo (fun y ↦ l • k (l • g y)) (closedBall (0 : Eᵤ) δ) (closedBall 0 δ),
      ContractingWith (l₀ * (Kk * Kg)).toNNReal (hmaps.restrict _ _ _) := by
  have hF {y y' : Eᵤ} (hy : y ∈ closedBall 0 δ) (hy' : y' ∈ closedBall 0 δ) :=
    smul_comp_smul_mem_closedBall_and_dist_le hη hg hgε hk hk₀ hl hl₀₁ h₁ h₂ hy hy'
  have hc : 0 ≤ l₀ * (Kk * Kg) := mul_nonneg (hl.1.trans hl.2) (by positivity)
  have hmaps : MapsTo (fun y ↦ l • k (l • g y)) (closedBall (0 : Eᵤ) δ) (closedBall 0 δ) :=
    fun y hy ↦ (hF hy hy).1
  refine ⟨hmaps, by rw [← NNReal.coe_lt_coe]; push_cast [Real.coe_toNNReal _ hc]; exact h₃,
    LipschitzWith.of_dist_le_mul fun y y' ↦ ?_⟩
  rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply,
    Real.coe_toNNReal _ hc]
  exact (hF y.property y'.property).2

/-- **The fixed-point equation of gluing at the centre.** Under the conditions of
`contractingWith_smul_comp_smul`, the map `y ↦ l • k (l • g y)` has a fixed point in the closed
ball of radius `δ`. -/
private theorem exists_smul_comp_smul_eq_self [CompleteSpace Eᵤ] {ε δ η l₀ l : ℝ} {Kg Kk : ℝ≥0}
    {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hδ : 0 < δ) (hη : 0 < η)
    (hg : LipschitzOnWith Kg g (closedBall 0 δ)) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) (hl : l ∈ Icc 0 l₀)
    (hl₀₁ : l₀ ≤ 1) (h₁ : l₀ * ε ≤ η) (h₂ : l₀ * (Kk * ε) ≤ δ) (h₃ : l₀ * (Kk * Kg) < 1) :
    ∃ y ∈ closedBall (0 : Eᵤ) δ, l • k (l • g y) = y := by
  obtain ⟨hmaps, hcontr⟩ := contractingWith_smul_comp_smul hη hg hgε hk hk₀ hl hl₀₁ h₁ h₂ h₃
  obtain ⟨y, hy, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps hcontr (mem_closedBall_self hδ.le) (edist_ne_top _ _)
  exact ⟨y, hy, hfix⟩

/-- **The fixed points of gluing at the centre.** Under the conditions of
`smul_comp_smul_mem_closedBall_and_dist_le` and `l₀ Kk Kg < 1`, for each `l ∈ [0, l₀]` the map
`y ↦ l • k (l • g y)` has exactly one fixed point `w l` in the closed ball of radius `δ`. It
vanishes at `l = 0`, and depends continuously on `l`. -/
private theorem exists_continuousOn_smul_comp_smul_eq_self [CompleteSpace Eᵤ] {ε δ η l₀ : ℝ}
    {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hδ : 0 < δ) (hη : 0 < η)
    (hg : LipschitzOnWith Kg g (closedBall 0 δ))
    (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε) (hk : LipschitzOnWith Kk k (closedBall 0 η))
    (hk₀ : k 0 = 0) (hl₀ : 0 ≤ l₀) (hl₀₁ : l₀ ≤ 1) (h₁ : l₀ * ε ≤ η) (h₂ : l₀ * (Kk * ε) ≤ δ)
    (h₃ : l₀ * (Kk * Kg) < 1) :
    ∃ w : ℝ → Eᵤ, ContinuousOn w (Icc 0 l₀) ∧ w 0 = 0 ∧ ∀ l ∈ Icc 0 l₀,
      w l ∈ closedBall (0 : Eᵤ) δ ∧ l • k (l • g (w l)) = w l ∧
        ∀ y ∈ closedBall (0 : Eᵤ) δ, l • k (l • g y) = y → y = w l := by
  set c := l₀ * (Kk * Kg)
  have hc : 0 ≤ c := mul_nonneg hl₀ (by positivity)
  have hcontr {l : ℝ} (hl : l ∈ Icc 0 l₀) :=
    contractingWith_smul_comp_smul hη hg hgε hk hk₀ hl hl₀₁ h₁ h₂ h₃
  -- A fixed point is within `dist (F v) v / (1 - c)` of every point `v` of the ball.
  have hdist : ∀ l ∈ Icc 0 l₀, ∀ y ∈ closedBall (0 : Eᵤ) δ, ∀ v ∈ closedBall (0 : Eᵤ) δ,
      l • k (l • g y) = y → dist y v ≤ dist (l • k (l • g v)) v / (1 - c) := by
    intro l hl y hy v hv hfix
    obtain ⟨_, hf⟩ := hcontr hl
    have h := hf.dist_le_of_fixedPoint ⟨v, hv⟩ (y := ⟨y, hy⟩) (Subtype.ext hfix)
    rw [Subtype.dist_eq, Subtype.dist_eq, Real.coe_toNNReal _ hc] at h
    simpa only [dist_comm, MapsTo.val_restrict_apply] using h
  choose! w hwb hwfix using fun l (hl : l ∈ Icc 0 l₀) ↦
    exists_smul_comp_smul_eq_self hδ hη hg hgε hk hk₀ hl hl₀₁ h₁ h₂ h₃
  have huniq : ∀ l ∈ Icc 0 l₀, ∀ y ∈ closedBall (0 : Eᵤ) δ, l • k (l • g y) = y → y = w l := by
    intro l hl y hy hfix
    obtain ⟨_, hf⟩ := hcontr hl
    exact Subtype.ext_iff.1 (hf.fixedPoint_unique' (x := ⟨y, hy⟩) (y := ⟨w l, hwb l hl⟩)
      (Subtype.ext hfix) (Subtype.ext (hwfix l hl)))
  refine ⟨w, fun l' hl' ↦ ?_,
    (huniq 0 (left_mem_Icc.2 hl₀) 0 (mem_closedBall_self hδ.le) (by simp)).symm,
    fun l hl ↦ ⟨hwb l hl, hwfix l hl, huniq l hl⟩⟩
  -- Continuity: `F_l (w l') → F_{l'} (w l') = w l'` as `l → l'`, and the estimate above.
  have hFc : ContinuousOn (fun l ↦ l • k (l • g (w l'))) (Icc 0 l₀) :=
    continuousOn_id.smul (hk.continuousOn.comp (continuousOn_id.smul continuousOn_const)
      fun l hl ↦ (smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl.1
        ((mul_le_mul_of_nonneg_right hl.2 ((hgε _ (hwb l' hl')) ▸ norm_nonneg _)).trans h₁)
        (hwb l' hl')).1)
  have hF' := hFc l' hl'
  rw [ContinuousWithinAt, hwfix l' hl'] at hF'
  have hlim : Tendsto (fun l ↦ dist (l • k (l • g (w l'))) (w l') / (1 - c))
      (𝓝[Icc 0 l₀] l') (𝓝 0) := by
    simpa using (tendsto_iff_dist_tendsto_zero.1 hF').div_const (1 - c)
  refine tendsto_iff_dist_tendsto_zero.2
    (squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlim)
  filter_upwards [self_mem_nhdsWithin] with l hl
  exact hdist l hl (w l) (hwb l hl) (w l') (hwb l' hl') (hwfix l hl)

/-- **Gluing at the centre of the split hyperbolic box.** Let `y ↦ (g y, y)` be a `Kg`-Lipschitz
graph in the entrance face `‖x‖ = ε` over the closed ball of radius `δ > 0` of the expanding
factor, and `x ↦ (x, k x)` a `Kk`-Lipschitz graph through the centre over the closed ball of
radius `η > 0` of the contracting factor, with `k 0 = 0`. For every neighbourhood `W` of the centre
and all large `T`, there is an entrance point `(g y, y)` whose orbit stays in the box
`‖x‖ ≤ ε, ‖y‖ ≤ ε` for times in `[0, T]` and, at time `T`, lies in `W` on the graph of `k`. -/
theorem eventually_exists_splitQuadraticFlow_snd_eq [CompleteSpace Eᵤ] {ε δ η : ℝ}
    {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hδ : 0 < δ) (hη : 0 < η)
    (hg : LipschitzOnWith Kg g (closedBall 0 δ)) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0)
    {W : Set (WithLp 2 (Eₛ × Eᵤ))} (hW : W ∈ 𝓝 0) :
    ∀ᶠ T in atTop, ∃ y ∈ closedBall (0 : Eᵤ) δ,
      (∀ s ∈ Icc 0 T, ‖(splitQuadraticFlow s (WithLp.toLp 2 (g y, y))).fst‖ ≤ ε ∧
        ‖(splitQuadraticFlow s (WithLp.toLp 2 (g y, y))).snd‖ ≤ ε) ∧
      splitQuadraticFlow T (WithLp.toLp 2 (g y, y)) ∈ W ∧
      (splitQuadraticFlow T (WithLp.toLp 2 (g y, y))).fst ∈ closedBall 0 η ∧
      (splitQuadraticFlow T (WithLp.toLp 2 (g y, y))).snd =
        k (splitQuadraticFlow T (WithLp.toLp 2 (g y, y))).fst := by
  have hε : 0 ≤ ε := hgε 0 (mem_closedBall_self hδ.le) ▸ norm_nonneg _
  -- `W` contains the points whose two components are smaller than some `r`.
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.1 ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).tendsto 0
    (by simpa using hW))
  have hW' (x : Eₛ) (y : Eᵤ) (hx : ‖x‖ < r) (hy : ‖y‖ < r) : WithLp.toLp 2 (x, y) ∈ W :=
    hrW (by
      rw [← ball_prod_same]
      exact mk_mem_prod (mem_ball_zero_iff.2 hx) (mem_ball_zero_iff.2 hy))
  -- The rate `e^{-T}` eventually beats every constant.
  have hsmall (C c : ℝ) (hc : 0 < c) : ∀ᶠ T in atTop, Real.exp (-T) * C < c := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.mul_const C).eventually
      (gt_mem_nhds (by rwa [zero_mul]))
  filter_upwards [eventually_ge_atTop 0, hsmall ε η hη, hsmall (Kk * ε) δ hδ,
    hsmall (Kk * Kg) 1 one_pos, hsmall Kk 1 one_pos, hsmall ε r hr, hsmall (Kk * ε) r hr]
    with T hT h₁ h₂ h₃ h₄ h₅ h₆
  set l := Real.exp (-T) with hldef
  have hl : 0 < l := Real.exp_pos _
  have hl₁ : l ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hexp : Real.exp T * l = 1 := by rw [hldef, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
  -- The orbit through `(g y, y)` meets the graph of `k` at time `T` when `y` is a fixed point of
  -- `y ↦ e^{-T} k (e^{-T} g y)`.
  obtain ⟨y, hy, hyF⟩ := exists_smul_comp_smul_eq_self hδ hη hg hgε hk hk₀
    (right_mem_Icc.2 hl.le) hl₁ h₁.le h₂.le (by linarith)
  obtain ⟨hgη, hkg⟩ := smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl.le h₁.le hy
  have hky : Real.exp T • y = k (l • g y) := by
    calc Real.exp T • y = Real.exp T • (l • k (l • g y)) := by rw [hyF]
      _ = k (l • g y) := by rw [smul_smul, hexp, one_smul]
  -- At time `T` the orbit is at `(e^{-T} g y, k (e^{-T} g y))`.
  have hT' : splitQuadraticFlow T (WithLp.toLp 2 (g y, y)) =
      WithLp.toLp 2 (l • g y, k (l • g y)) := by
    rw [splitQuadraticFlow_apply, WithLp.toLp_fst, WithLp.toLp_snd, hky]
  have hny : Real.exp T * ‖y‖ ≤ Kk * (l * ε) := by
    rw [← Real.norm_of_nonneg (Real.exp_pos T).le, ← norm_smul, hky]
    exact hkg
  refine ⟨y, hy, fun s hs ↦ ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [norm_fst_splitQuadraticFlow, WithLp.toLp_fst, hgε y hy]
    exact mul_le_of_le_one_left hε (Real.exp_le_one_iff.2 (by linarith [hs.1]))
  · rw [norm_snd_splitQuadraticFlow, WithLp.toLp_snd]
    calc Real.exp s * ‖y‖ ≤ Real.exp T * ‖y‖ := by gcongr; exact hs.2
      _ ≤ Kk * (l * ε) := hny
      _ ≤ ε := by nlinarith [mul_nonneg (Kk.coe_nonneg) hε]
  · rw [hT']
    refine hW' _ _ ?_ ?_
    · rw [norm_smul, Real.norm_of_nonneg hl.le, hgε y hy]
      exact h₅
    · exact hkg.trans_lt (by linarith)
  · rw [hT', WithLp.toLp_fst]
    exact hgη
  · rw [hT', WithLp.toLp_snd, WithLp.toLp_fst]

/-! ### The compactified gluing arc at the centre -/

section Arc

variable {ε δ η l₀ : ℝ} {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ}

/-- The **gluing pairs at the centre** of the split hyperbolic box: the pairs `(w, z)` of a point
`w = (g y, y)` of the entrance graph of `g`, with `‖y‖ ≤ δ`, and the point `z` of its orbit, at a
time `T` with `e^{-T} ≤ l₀`, which lies on the graph `x ↦ (x, k x)`. When `k 0 = 0` this graph
passes through the centre `(0, 0)`, the rate `e^{-T}` is the gluing parameter, and the broken orbit,
entering along the stable set at `(g 0, 0)` and resting at the centre, is the limit `e^{-T} → 0`. -/
def splitCenterGluingPairs (δ l₀ : ℝ) (g : Eᵤ → Eₛ) (k : Eₛ → Eᵤ) :
    Set (WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)) :=
  {p | ‖p.1.snd‖ ≤ δ ∧ p.1.fst = g p.1.snd ∧
    (∃ T, Real.exp (-T) ≤ l₀ ∧ splitQuadraticFlow T p.1 = p.2) ∧ p.2.snd = k p.2.fst}

/-- The entrance, flow and graph conditions defining the gluing pairs at the centre. -/
@[simp]
theorem mem_splitCenterGluingPairs {p : WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)} :
    p ∈ splitCenterGluingPairs δ l₀ g k ↔ ‖p.1.snd‖ ≤ δ ∧ p.1.fst = g p.1.snd ∧
      (∃ T, Real.exp (-T) ≤ l₀ ∧ splitQuadraticFlow T p.1 = p.2) ∧ p.2.snd = k p.2.fst :=
  Iff.rfl

/-- The gluing parametrization at the centre, extended continuously to the parameter `0`. Its
values at positive parameters are the gluing pairs, its value at `0` is the broken pair
`((g 0, 0), 0)`, and its parameter is recovered as `‖x‖ / ε` from the glued point `(x, k x)`. -/
private theorem exists_splitCenterGluingPairs_parametrization [CompleteSpace Eᵤ] (hδ : 0 < δ)
    (hη : 0 < η) (hε : 0 < ε) (hg : LipschitzOnWith Kg g (closedBall 0 δ))
    (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε) (hk : LipschitzOnWith Kk k (closedBall 0 η))
    (hk₀ : k 0 = 0) (hl₀ : 0 < l₀) (hl₀₁ : l₀ ≤ 1) (h₁ : l₀ * ε ≤ η) (h₂ : l₀ * (Kk * ε) ≤ δ)
    (h₃ : l₀ * (Kk * Kg) < 1) :
    ∃ c : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ), ContinuousOn c (Icc 0 l₀) ∧
      c '' Ioc 0 l₀ = splitCenterGluingPairs δ l₀ g k ∧
      c 0 = (WithLp.toLp 2 (g 0, 0), 0) ∧ ∀ l ∈ Icc 0 l₀, ‖(c l).2.fst‖ / ε = l := by
  obtain ⟨w, hwc, hw₀, hw⟩ :=
    exists_continuousOn_smul_comp_smul_eq_self hδ hη hg hgε hk hk₀ hl₀.le hl₀₁ h₁ h₂ h₃
  set c : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ) := fun l ↦
    (WithLp.toLp 2 (g (w l), w l), WithLp.toLp 2 (l • g (w l), k (l • g (w l)))) with hc
  have hgw : ContinuousOn (fun l ↦ g (w l)) (Icc 0 l₀) :=
    hg.continuousOn.comp hwc fun l hl ↦ (hw l hl).1
  have hball (l : ℝ) (hl : l ∈ Icc 0 l₀) : l • g (w l) ∈ closedBall (0 : Eₛ) η :=
    (smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl.1
      ((mul_le_mul_of_nonneg_right hl.2 hε.le).trans h₁) (hw l hl).1).1
  refine ⟨c, ?_, ?_, by simp [hc, hw₀, hk₀], fun l hl ↦ ?_⟩
  · have hx : ContinuousOn (fun l ↦ l • g (w l)) (Icc 0 l₀) := continuousOn_id.smul hgw
    exact ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn (hgw.prodMk hwc)).prodMk
      ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn
        (hx.prodMk (hk.continuousOn.comp hx hball)))
  · ext p
    constructor
    · -- A positive parameter `l` gives the pair glued at the time `T = -log l`.
      rintro ⟨l, hl, rfl⟩
      obtain ⟨hwb, hfix, -⟩ := hw l (Ioc_subset_Icc_self hl)
      have hinv : l⁻¹ • w l = k (l • g (w l)) := (inv_smul_eq_iff₀ hl.1.ne').2 hfix.symm
      refine ⟨by simpa [hc] using hwb, by simp [hc], ⟨-Real.log l, ?_, ?_⟩, by simp [hc]⟩
      · rw [neg_neg, Real.exp_log hl.1]
        exact hl.2
      · simp only [hc, splitQuadraticFlow_apply, WithLp.toLp_fst, WithLp.toLp_snd, neg_neg,
          Real.exp_neg, Real.exp_log hl.1, hinv]
    · -- Conversely, the expanding coordinate of a pair glued at time `T` is the fixed point at
      -- the parameter `e^{-T}`.
      rintro ⟨hy, hfst, ⟨T, hT, hTp⟩, hsnd⟩
      have hl : Real.exp (-T) ∈ Ioc 0 l₀ := ⟨Real.exp_pos _, hT⟩
      have hp₂ : p.2 = WithLp.toLp 2 (Real.exp (-T) • g p.1.snd, Real.exp T • p.1.snd) := by
        rw [← hTp, splitQuadraticFlow_apply, hfst]
      have hk' : Real.exp T • p.1.snd = k (Real.exp (-T) • g p.1.snd) := by
        simpa [hp₂] using hsnd
      have hfix : Real.exp (-T) • k (Real.exp (-T) • g p.1.snd) = p.1.snd := by
        rw [← hk', smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]
      have hwl := (hw _ (Ioc_subset_Icc_self hl)).2.2 _ (mem_closedBall_zero_iff.2 hy) hfix
      refine ⟨Real.exp (-T), hl, Prod.ext ?_ ?_⟩
      · simp only [hc]
        rw [← hwl]
        exact WithLp.ofLp_injective 2 (Prod.ext (by simp [hfst]) (by simp))
      · simp only [hc]
        rw [← hwl, hp₂, hk']
  · simp only [hc, WithLp.toLp_fst]
    rw [norm_smul, Real.norm_of_nonneg hl.1, hgε _ (hw l hl).1, mul_div_cancel_right₀ _ hε.ne']

/-- Along the orbit of a gluing pair at the centre, from the entrance point to the glued point, the
flow stays in the box `‖x‖ ≤ ε, ‖y‖ ≤ ε` when `l₀ ≤ 1`, `l₀ ε ≤ η` and `l₀ Kk ≤ 1`. -/
private theorem forall_mem_Icc_norm_splitQuadraticFlow_le (hη : 0 < η) (hε : 0 < ε)
    (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε) (hk : LipschitzOnWith Kk k (closedBall 0 η))
    (hk₀ : k 0 = 0) (hl₀₁ : l₀ ≤ 1) (h₁ : l₀ * ε ≤ η) (h₄ : l₀ * Kk ≤ 1)
    {p : WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)} (hp : p ∈ splitCenterGluingPairs δ l₀ g k)
    {T : ℝ} (hT : splitQuadraticFlow T p.1 = p.2) :
    0 ≤ T ∧ ∀ s ∈ Icc 0 T, ‖(splitQuadraticFlow s p.1).fst‖ ≤ ε ∧
      ‖(splitQuadraticFlow s p.1).snd‖ ≤ ε := by
  obtain ⟨hy, hfst, ⟨T', hT', hT'p⟩, hsnd⟩ := hp
  have hgy : ‖p.1.fst‖ = ε := hfst ▸ hgε _ (mem_closedBall_zero_iff.2 hy)
  -- The glued point determines the time: its contracting coordinate has norm `e^{-T} ε`.
  have hTT : T = T' := by
    have h := congrArg (fun z ↦ ‖z.fst‖) (hT.trans hT'p.symm)
    simp only [norm_fst_splitQuadraticFlow, hgy] at h
    exact neg_inj.1 (Real.exp_injective (mul_right_cancel₀ hε.ne' h))
  subst hTT
  have hT0 : 0 ≤ T := by linarith [Real.exp_le_one_iff.1 (hT'.trans hl₀₁)]
  have hx : ‖p.2.fst‖ = Real.exp (-T) * ε := by rw [← hT, norm_fst_splitQuadraticFlow, hgy]
  have hxη : p.2.fst ∈ closedBall (0 : Eₛ) η := by
    rw [mem_closedBall_zero_iff, hx]
    exact (mul_le_mul_of_nonneg_right hT' hε.le).trans h₁
  have hkx : ‖k p.2.fst‖ ≤ Kk * ‖p.2.fst‖ := by
    simpa [hk₀] using hk.norm_sub_le hxη (mem_closedBall_self hη.le)
  refine ⟨hT0, fun s hs ↦ ⟨?_, ?_⟩⟩
  · rw [norm_fst_splitQuadraticFlow, hgy]
    exact mul_le_of_le_one_left hε.le (Real.exp_le_one_iff.2 (by linarith [hs.1]))
  · rw [norm_snd_splitQuadraticFlow]
    calc Real.exp s * ‖p.1.snd‖ ≤ Real.exp T * ‖p.1.snd‖ := by gcongr; exact hs.2
      _ = ‖k p.2.fst‖ := by rw [← hsnd, ← hT, norm_snd_splitQuadraticFlow]
      _ ≤ Kk * (l₀ * ε) := by
          rw [hx] at hkx
          exact hkx.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hT' hε.le)
            Kk.coe_nonneg)
      _ ≤ ε := by nlinarith

/-- For every `C` and `c > 0`, the product `l * C` is eventually smaller than `c` as `l → 0⁺`. -/
private theorem eventually_mul_lt (C : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ l in 𝓝[>] (0 : ℝ), l * C < c :=
  nhdsWithin_le_nhds (((continuous_mul_const C).tendsto 0).eventually
    (gt_mem_nhds (by rwa [zero_mul])))

/-- **The compactified gluing arc at the centre of the split box.** Let `y ↦ (g y, y)` be a
Lipschitz graph in the entrance face `‖x‖ = ε` over the closed ball of radius `δ` of the expanding
factor, and `x ↦ (x, k x)` a Lipschitz graph through the centre over the closed ball of radius `η`
of the contracting factor, with `k 0 = 0`. For every small gluing parameter `l₀ > 0`:

* the closure of the gluing pairs `splitCenterGluingPairs δ l₀ g k` is homeomorphic to the closed
  interval `[0, l₀]`, with the inverse coordinate `‖x‖ / ε` read off the glued point `(x, k x)`,
  and the broken pair `((g 0, 0), 0)` at the parameter `0`;
* this broken pair is the only point the closure adds;
* along every gluing pair, the orbit runs from the entrance point to the glued point inside the box
  `‖x‖ ≤ ε, ‖y‖ ≤ ε`.

So the orbits from the entrance disc to the disc through the centre form a half-open arc, whose
closure adds exactly the broken orbit resting at the centre. -/
theorem eventually_exists_homeomorph_closure_splitCenterGluingPairs [CompleteSpace Eᵤ]
    (hδ : 0 < δ) (hη : 0 < η) (hε : 0 < ε) (hg : LipschitzOnWith Kg g (closedBall 0 δ))
    (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε) (hk : LipschitzOnWith Kk k (closedBall 0 η))
    (hk₀ : k 0 = 0) :
    ∀ᶠ l₀ in 𝓝[>] 0, ∃ (hl₀ : 0 < l₀)
      (e : Icc (0 : ℝ) l₀ ≃ₜ closure (splitCenterGluingPairs δ l₀ g k)),
      (∀ p, (e.symm p : ℝ) = ‖p.val.2.fst‖ / ε) ∧
      (e ⟨0, left_mem_Icc.2 hl₀.le⟩).val = (WithLp.toLp 2 (g 0, 0), 0) ∧
      closure (splitCenterGluingPairs δ l₀ g k) =
        insert (WithLp.toLp 2 (g 0, 0), 0) (splitCenterGluingPairs δ l₀ g k) ∧
      ∀ p ∈ splitCenterGluingPairs δ l₀ g k, ∀ T, splitQuadraticFlow T p.1 = p.2 →
        0 ≤ T ∧ ∀ s ∈ Icc 0 T, ‖(splitQuadraticFlow s p.1).fst‖ ≤ ε ∧
          ‖(splitQuadraticFlow s p.1).snd‖ ≤ ε := by
  filter_upwards [self_mem_nhdsWithin, eventually_mul_lt 1 one_pos, eventually_mul_lt ε hη,
    eventually_mul_lt (Kk * ε) hδ, eventually_mul_lt (Kk * Kg) one_pos,
    eventually_mul_lt Kk one_pos] with l₀ hl₀ h₀ h₁ h₂ h₃ h₄
  rw [mul_one] at h₀
  obtain ⟨c, hc, himage, hc₀, hnorm⟩ := exists_splitCenterGluingPairs_parametrization hδ hη hε hg
    hgε hk hk₀ hl₀ h₀.le h₁.le h₂.le h₃
  have hclosure : closure (splitCenterGluingPairs δ l₀ g k) = c '' Icc 0 l₀ := by
    rw [← himage]
    refine subset_antisymm (closure_minimal (image_mono Ioc_subset_Icc_self)
      (isCompact_Icc.image_of_continuousOn hc).isClosed) ?_
    have h := ContinuousOn.image_closure (s := Ioc 0 l₀) (f := c) (by rwa [closure_Ioc hl₀.ne])
    simpa only [closure_Ioc hl₀.ne] using h
  -- The parametrization is injective, since its parameter is read off the glued point, so it is
  -- a homeomorphism from the compact interval onto the closure.
  have hinj : InjOn c (Icc 0 l₀) := fun l hl l' hl' hll' ↦
    (hnorm l hl).symm.trans (hll' ▸ hnorm l' hl')
  let e := (isCompact_Icc.imageHomeomorph hc hinj).trans (Homeomorph.setCongr hclosure.symm)
  refine ⟨hl₀, e, fun p ↦ ?_,
    (congrArg Subtype.val (isCompact_Icc.imageHomeomorph_apply hc hinj _)).trans hc₀, ?_,
    fun p hp T hT ↦
    forall_mem_Icc_norm_splitQuadraticFlow_le hη hε hgε hk hk₀ h₀.le h₁.le h₄.le hp hT⟩
  · have h : c (e.symm p) = p.val := isCompact_Icc.apply_imageHomeomorph_symm hc hinj _
    rw [← h, hnorm _ (e.symm p).property]
  · rw [hclosure, ← insert_left_Ioc hl₀.le, image_insert_eq, hc₀, himage]

end Arc

/-! ### Gluing a transverse disc to a disc through the centre -/

/-- **Gluing a transverse disc to a disc through the centre.** Let `ψ` be a disc through the point
`(x₀, 0)` of the stable set on the entrance face `‖x‖ = ε`, strictly differentiable at `0` with
the derivative of its expanding component invertible, and `χ` a disc through the centre, strictly
differentiable at `0` with the derivative of its contracting component invertible. Then there are a
radius `δ > 0`, a graph `y ↦ (g y, y)` in the entrance face with `g 0 = x₀`, and a graph
`x ↦ (x, k x)` through the centre such that:

* for every small gluing parameter `l₀ > 0`, the closure of the gluing pairs
  `splitCenterGluingPairs δ l₀ g k` is homeomorphic to `[0, l₀]`, with the inverse coordinate
  `‖x‖ / ε` read off the glued point `(x, k x)` and the broken pair `((x₀, 0), 0)` at the parameter
  `0`; this broken pair is the only point the closure adds; every gluing pair consists of the entry
  point of the orbit through `ψ z` for some `z ∈ U` and the point `χ z'` for some `z' ∈ V`; and
  along it the orbit runs inside the box;
* conversely, for `z` and `z'` near `0`, if the orbit through the entry point of the orbit through
  `ψ z` reaches `χ z'` at a time `T` with `e^{-T} ≤ l₀`, then this entry point and `χ z'` form a
  gluing pair.

So, near the broken orbit entering along the stable set and resting at the centre, the orbits from
the first disc to the second form a half-open arc whose closure adds exactly the broken orbit. In
Morse theory, `ψ` is the trace of the unstable manifold of a critical point `p` near a trajectory
from `p` into the critical point `a` at the centre, and `χ` a submanifold through `a` transverse to
the unstable manifold of `a`. -/
theorem exists_homeomorph_closure_splitCenterGluingPairs_of_hasStrictFDerivAt
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [CompleteSpace G]
    {ψ : F → WithLp 2 (Eₛ × Eᵤ)} {ψ' : F →L[ℝ] WithLp 2 (Eₛ × Eᵤ)}
    {χ : G → WithLp 2 (Eₛ × Eᵤ)} {χ' : G →L[ℝ] WithLp 2 (Eₛ × Eᵤ)} {U : Set F} {V : Set G}
    {ε : ℝ} {x₀ : Eₛ} (hψ : HasStrictFDerivAt ψ ψ' 0)
    (hψ' : (WithLp.sndL 2 ℝ Eₛ Eᵤ ∘L ψ').IsInvertible) (hψ₀ : ψ 0 = WithLp.toLp 2 (x₀, 0))
    (hx₀ : ‖x₀‖ = ε) (hχ : HasStrictFDerivAt χ χ' 0)
    (hχ' : (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L χ').IsInvertible) (hχ₀ : χ 0 = 0) (hε : 0 < ε)
    (hU : U ∈ 𝓝 0) (hV : V ∈ 𝓝 0) :
    ∃ δ > 0, ∃ (g : Eᵤ → Eₛ) (k : Eₛ → Eᵤ), g 0 = x₀ ∧
      (∀ᶠ l₀ in 𝓝[>] 0, ∃ (hl₀ : 0 < l₀)
        (e : Icc (0 : ℝ) l₀ ≃ₜ closure (splitCenterGluingPairs δ l₀ g k)),
        (∀ p, (e.symm p : ℝ) = ‖p.val.2.fst‖ / ε) ∧
        (e ⟨0, left_mem_Icc.2 hl₀.le⟩).val = (WithLp.toLp 2 (x₀, 0), 0) ∧
        closure (splitCenterGluingPairs δ l₀ g k) =
          insert (WithLp.toLp 2 (x₀, 0), 0) (splitCenterGluingPairs δ l₀ g k) ∧
        ∀ p ∈ splitCenterGluingPairs δ l₀ g k,
          ((∃ z ∈ U, splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z) = p.1) ∧
            ∃ z ∈ V, χ z = p.2) ∧
          ∀ T, splitQuadraticFlow T p.1 = p.2 → 0 ≤ T ∧ ∀ s ∈ Icc 0 T,
            ‖(splitQuadraticFlow s p.1).fst‖ ≤ ε ∧ ‖(splitQuadraticFlow s p.1).snd‖ ≤ ε) ∧
      ∀ᶠ q : F × G in 𝓝 (0, 0), ∀ l₀ T, Real.exp (-T) ≤ l₀ →
        splitQuadraticFlow T (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1)) = χ q.2 →
        (splitQuadraticFlow (splitEntryTime ε (ψ q.1)) (ψ q.1), χ q.2) ∈
          splitCenterGluingPairs δ l₀ g k := by
  -- The expanding factor is isomorphic to the complete space `F`.
  have : CompleteSpace Eᵤ := by
    obtain ⟨L, -⟩ := hψ'
    exact (completeSpace_congr (e := L.toEquiv) L.isUniformEmbedding).1 inferInstance
  obtain ⟨δ, hδ, Kg, g, hg, hg₀, hgpts, hgexh⟩ :=
    exists_splitQuadraticFlow_splitEntryTime_eq_graph hψ hψ' hψ₀ hx₀ hε hU
  obtain ⟨η, hη, Kk, k, hk, hk₀, hkpts, hkexh⟩ :=
    exists_lipschitzOnWith_graph_of_hasStrictFDerivAt hχ hχ' hχ₀ hV
  have hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε := fun y hy ↦ (hgpts y hy).1
  refine ⟨δ, hδ, g, k, hg₀, ?_, ?_⟩
  · filter_upwards [eventually_exists_homeomorph_closure_splitCenterGluingPairs hδ hη hε hg hgε hk
      hk₀, eventually_mul_lt ε hη] with l₀ ⟨hl₀, e, hcoord, he₀, hcl, hbox⟩ hl₀η
    rw [hg₀] at he₀ hcl
    refine ⟨hl₀, e, hcoord, he₀, hcl, fun p hp ↦ ⟨⟨?_, ?_⟩, hbox p hp⟩⟩
    · -- The entrance point lies on the graph of `g`, which consists of entry points of `ψ`.
      obtain ⟨hy, hfst, -⟩ := hp
      obtain ⟨-, z, hzU, hz⟩ := hgpts _ (mem_closedBall_zero_iff.2 hy)
      exact ⟨z, hzU, hz.trans (WithLp.ofLp_injective 2 (Prod.ext (by simp [hfst]) (by simp)))⟩
    · -- The glued point lies on the graph of `k` over the ball of radius `η`, made of points
      -- of `χ`.
      obtain ⟨hy, hfst, ⟨T, hT, hTp⟩, hsnd⟩ := hp
      have hx : p.2.fst ∈ closedBall (0 : Eₛ) η := by
        rw [mem_closedBall_zero_iff, ← hTp, norm_fst_splitQuadraticFlow, hfst,
          hgε _ (mem_closedBall_zero_iff.2 hy)]
        exact (mul_le_mul_of_nonneg_right hT hε.le).trans hl₀η.le
      obtain ⟨z, hzV, hz⟩ := hkpts _ hx
      exact ⟨z, hzV, hz.trans (WithLp.ofLp_injective 2 (Prod.ext (by simp) (by simp [hsnd])))⟩
  · -- Near `0`, entry points of `ψ` lie on the graph of `g` over the ball of radius `δ`, and points
    -- of `χ` on the graph of `k`.
    obtain ⟨hfst₀, hsnd₀⟩ := eventually_ne_zero_and_norm_rescale_smul_le
      ((WithLp.fstL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.comp hψ.continuousAt)
      ((WithLp.sndL 2 ℝ Eₛ Eᵤ).continuous.continuousAt.comp hψ.continuousAt)
      (by simpa [hψ₀] using hx₀) (by simp [hψ₀]) hε (div_pos hδ hε)
    have hentry : ∀ᶠ z in 𝓝 (0 : F),
        (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).fst =
          g (splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).snd ∧
        ‖(splitQuadraticFlow (splitEntryTime ε (ψ z)) (ψ z)).snd‖ ≤ δ := by
      filter_upwards [hgexh, hfst₀, hsnd₀] with z hz hz₀ hzδ
      refine ⟨hz, ?_⟩
      simp only [Function.comp_apply, WithLp.fstL_apply, WithLp.sndL_apply,
        div_mul_cancel₀ _ hε.ne'] at hz₀ hzδ
      rwa [splitQuadraticFlow_splitEntryTime hε hz₀]
    filter_upwards [(continuous_fst.tendsto (0, 0)).eventually hentry,
      (continuous_snd.tendsto (0, 0)).eventually hkexh] with q hq₁ hq₂ l₀ T hT hTq
    exact ⟨hq₁.2, hq₁.1, ⟨T, hT, hTq⟩, hq₂.2⟩

end TauCeti
