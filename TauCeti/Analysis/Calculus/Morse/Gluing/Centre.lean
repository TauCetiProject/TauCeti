/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Passage
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Topology.Algebra.Order.Field
import TauCeti.Topology.MetricSpace.Contracting

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

In Morse theory, the entrance disc is a piece of the unstable manifold of a critical point `p`
which flows into the critical point `a` at the centre of the box, and the disc through the centre is
a piece of a submanifold through `a` transverse to the unstable manifold of `a`, such as the stable
manifold of a second pseudo-gradient. The glued orbits are then points of `W^u(p)` on that
submanifold converging to `a`.

For a whole family of rates the fixed points depend continuously on the rate: for small `l₀`, the
equation `l • k (l • g y) = y` has exactly one solution `v l` in the closed ball for each
`l ∈ [0, l₀]`, with `v` continuous and `v 0 = 0`
(`TauCeti.eventually_exists_continuousOn_smul_comp_smul_eq_iff`). At the rate `l = e^{-T}` this
equation says that the orbit through `(g y, y)` meets the graph of `k` at time `T`
(`TauCeti.splitQuadraticFlow_snd_eq_iff_smul_comp_smul_eq`). So the orbits from the entrance graph
to the graph through the centre form a continuous family parametrized by the rate, ending at the
broken configuration at `l = 0`; this is the local model of the boundary chart of a
one-dimensional moduli space at a configuration breaking at a critical point.

## Main results

* `TauCeti.exists_lipschitzOnWith_graph_of_hasStrictFDerivAt`: near the centre, the image of a disc
  through the centre transverse to the unstable set contains a Lipschitz graph `x ↦ (x, k x)` with
  `k 0 = 0`, which contains the image of a neighbourhood of `0`.
* `TauCeti.eventually_exists_splitQuadraticFlow_snd_eq`: for all large `T`, the orbit through some
  point of the entrance graph stays in the box up to time `T` and meets the graph of `k` at time
  `T`, in a prescribed neighbourhood of the centre.
* `TauCeti.eventually_exists_continuousOn_smul_comp_smul_eq_iff`: the solutions of the gluing
  equation form a continuous family in the rate.
* `TauCeti.splitQuadraticFlow_snd_eq_iff_smul_comp_smul_eq`: meeting the graph through the centre
  at time `T` is the gluing equation at the rate `e^{-T}`.
* `TauCeti.splitQuadraticFlow_eq_and_norm_le_of_smul_comp_smul_eq`: a solution of the gluing
  equation at the rate `l` flows in the box, in time `-log l`, to the graph through the centre.

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
some `z` in a prescribed neighbourhood `V` of `0`; conversely, the points `χ z` for `z` near `0`
lie on the graph. -/
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
  have hσt := ha.localInverse_tendsto
  have hleft := ha.eventually_left_inverse
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
  · -- Near `0`, `σ` inverts the contracting component, so `χ z` is the point of the graph over it.
    have hat : Tendsto a (𝓝 0) (𝓝 0) := by simpa [ha₀] using ha.continuousAt.tendsto
    filter_upwards [hleft, hat (closedBall_mem_nhds 0 hη)] with z hz hzη
    exact ⟨hzη, by simp only [k, ha_def] at hz ⊢; rw [hz]⟩

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

/-- Along the entrance graph `y ↦ (g y, y)`, scaled by a rate `l` with `l ε ≤ η`, the map
`y ↦ l • k (l • g y)` is Lipschitz with constant `l Kk l Kg`. -/
private theorem dist_smul_comp_smul_le {ε δ η l : ℝ} {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ}
    {k : Eₛ → Eᵤ} (hη : 0 < η) (hg : LipschitzOnWith Kg g (closedBall 0 δ))
    (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε) (hk : LipschitzOnWith Kk k (closedBall 0 η))
    (hk₀ : k 0 = 0) (hl : 0 ≤ l) (h : l * ε ≤ η) {y y' : Eᵤ} (hy : y ∈ closedBall 0 δ)
    (hy' : y' ∈ closedBall 0 δ) :
    dist (l • k (l • g y)) (l • k (l • g y')) ≤ l * (Kk * (l * Kg)) * dist y y' := by
  have hkg {y : Eᵤ} (hy : y ∈ closedBall 0 δ) :=
    smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl h hy
  rw [dist_smul₀, Real.norm_of_nonneg hl]
  calc l * dist (k (l • g y)) (k (l • g y')) ≤ l * (Kk * dist (l • g y) (l • g y')) :=
        mul_le_mul_of_nonneg_left (hk.dist_le_mul _ (hkg hy).1 _ (hkg hy').1) hl
    _ = l * (Kk * (l * dist (g y) (g y'))) := by rw [dist_smul₀, Real.norm_of_nonneg hl]
    _ ≤ l * (Kk * (l * (Kg * dist y y'))) := by
        gcongr
        exact hg.dist_le_mul _ hy _ hy'
    _ = l * (Kk * (l * Kg)) * dist y y' := by ring

/-- **The orbits glued at the centre form a continuous family.** Let `y ↦ (g y, y)` be a
`Kg`-Lipschitz graph in the entrance face `‖x‖ = ε` over the closed ball of radius `δ > 0` of the
expanding factor, and `x ↦ (x, k x)` a `Kk`-Lipschitz graph through the centre over the closed
ball of radius `η > 0` of the contracting factor, with `k 0 = 0`. For every small `l₀ > 0` there
is a map `v`, continuous on `[0, l₀]` with `v 0 = 0`, such that for every rate `l ∈ [0, l₀]` the
point `v l` is the only solution `y` in the closed ball of radius `δ` of the gluing equation
`l • k (l • g y) = y`. At the rate `l = e^{-T}`, this equation says that the orbit through the
entrance point `(g y, y)` meets the graph of `k` at time `T`
(`TauCeti.splitQuadraticFlow_snd_eq_iff_smul_comp_smul_eq`). The point `l • g (v l)` lies in the
domain of `k`, and `k` there is at most `Kk l ε`. -/
theorem eventually_exists_continuousOn_smul_comp_smul_eq_iff [CompleteSpace Eᵤ] {ε δ η : ℝ}
    {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hδ : 0 < δ) (hη : 0 < η)
    (hg : LipschitzOnWith Kg g (closedBall 0 δ)) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) :
    ∀ᶠ l₀ in 𝓝[>] 0, ∃ v : ℝ → Eᵤ, ContinuousOn v (Icc 0 l₀) ∧ v 0 = 0 ∧
      ∀ l ∈ Icc 0 l₀, v l ∈ closedBall 0 δ ∧ l • g (v l) ∈ closedBall 0 η ∧
        ‖k (l • g (v l))‖ ≤ Kk * (l * ε) ∧ ∀ y ∈ closedBall 0 δ, l • k (l • g y) = y ↔ y = v l := by
  have hε : 0 ≤ ε := hgε 0 (mem_closedBall_self hδ.le) ▸ norm_nonneg _
  -- The rates `l₀` for which every `l ∈ [0, l₀]` gives a contraction with one constant.
  filter_upwards [self_mem_nhdsWithin,
    (tendsto_mul_const_nhdsGT_zero 1).eventually (gt_mem_nhds one_pos),
    (tendsto_mul_const_nhdsGT_zero ε).eventually (gt_mem_nhds hη),
    (tendsto_mul_const_nhdsGT_zero (Kk * ε)).eventually (gt_mem_nhds hδ),
    (tendsto_mul_const_nhdsGT_zero (Kk * Kg : ℝ)).eventually (gt_mem_nhds one_pos)]
    with l₀ hl₀ h₀ h₁ h₂ h₃
  rw [mem_Ioi] at hl₀
  rw [mul_one] at h₀
  set K : ℝ≥0 := l₀.toNNReal * (Kk * (l₀.toNNReal * Kg)) with hKdef
  have hK : (K : ℝ) = l₀ * (Kk * (l₀ * Kg)) := by
    simp [hKdef, Real.coe_toNNReal _ hl₀.le]
  have hK₁ : (K : ℝ) < 1 := by
    rw [hK]
    nlinarith [mul_nonneg Kk.coe_nonneg Kg.coe_nonneg]
  have hlε {l : ℝ} (hl : l ∈ Icc 0 l₀) : l * ε ≤ η :=
    ((mul_le_mul_of_nonneg_right hl.2 hε).trans h₁.le)
  have hkg {l : ℝ} (hl : l ∈ Icc 0 l₀) {y : Eᵤ} (hy : y ∈ closedBall 0 δ) :=
    smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl.1 (hlε hl) hy
  -- For `l ∈ [0, l₀]`, the gluing map is a contraction of the closed ball of radius `δ`.
  have hmaps {l : ℝ} (hl : l ∈ Icc 0 l₀) :
      MapsTo (fun y ↦ l • k (l • g y)) (closedBall (0 : Eᵤ) δ) (closedBall 0 δ) := fun y hy ↦ by
    have hll : l * l ≤ l₀ := by nlinarith [hl.1, hl.2]
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hl.1]
    calc l * ‖k (l • g y)‖ ≤ l * (Kk * (l * ε)) :=
          mul_le_mul_of_nonneg_left (hkg hl hy).2 hl.1
      _ = l * l * (Kk * ε) := by ring
      _ ≤ l₀ * (Kk * ε) := by gcongr
      _ ≤ δ := h₂.le
  have hlip {l : ℝ} (hl : l ∈ Icc 0 l₀) {y y' : Eᵤ} (hy : y ∈ closedBall 0 δ)
      (hy' : y' ∈ closedBall 0 δ) :
      dist (l • k (l • g y)) (l • k (l • g y')) ≤ K * dist y y' := by
    refine (dist_smul_comp_smul_le hη hg hgε hk hk₀ hl.1 (hlε hl) hy hy').trans ?_
    obtain ⟨hl0, hll₀⟩ := hl
    rw [hK]
    gcongr
  have hcontr {l : ℝ} (hl : l ∈ Icc 0 l₀) : ContractingWith K ((hmaps hl).restrict _ _ _) :=
    ⟨by rw [← NNReal.coe_lt_coe]; simpa using hK₁, LipschitzWith.of_dist_le_mul fun y y' ↦ by
      simpa only [Subtype.dist_eq, MapsTo.val_restrict_apply] using
        hlip hl y.property y'.property⟩
  -- Its fixed point `v l`, the only one in the ball.
  have hfix (l : ℝ) : ∃ y : Eᵤ, l ∈ Icc 0 l₀ → y ∈ closedBall 0 δ ∧ l • k (l • g y) = y := by
    by_cases hl : l ∈ Icc 0 l₀
    · obtain ⟨y, hy, hyfix, -⟩ := ContractingWith.exists_fixedPoint'
        isClosed_closedBall.isComplete (hmaps hl) (hcontr hl) (mem_closedBall_self hδ.le)
        (edist_ne_top _ _)
      exact ⟨y, fun _ ↦ ⟨hy, hyfix⟩⟩
    · exact ⟨0, fun h ↦ absurd h hl⟩
  choose v hv using hfix
  have huniq {l : ℝ} (hl : l ∈ Icc 0 l₀) {y : Eᵤ} (hy : y ∈ closedBall 0 δ)
      (hyfix : l • k (l • g y) = y) : y = v l :=
    congrArg Subtype.val ((hcontr hl).fixedPoint_unique' (x := ⟨y, hy⟩)
      (y := ⟨v l, (hv l hl).1⟩) (Subtype.ext hyfix) (Subtype.ext (hv l hl).2))
  have hv₀ : v 0 = 0 :=
    (huniq (left_mem_Icc.2 hl₀.le) (mem_closedBall_self hδ.le) (by simp)).symm
  -- The fixed points depend continuously on `l`, since the maps do.
  refine ⟨v, continuousOn_of_forall_contractingWith (F := fun l y ↦ l • k (l • g y))
      (fun l hl ↦ hmaps hl) (fun l hl ↦ hcontr hl) hv fun y hy ↦ ?_, hv₀,
    fun l hl ↦ ⟨(hv l hl).1, (hkg hl (hv l hl).1).1, (hkg hl (hv l hl).1).2,
      fun y hy ↦ ⟨huniq hl hy, fun h ↦ h ▸ (hv l hl).2⟩⟩⟩
  exact continuousOn_id.smul (hk.continuousOn.comp (continuousOn_id.smul continuousOn_const)
    fun l hl ↦ (hkg hl hy).1)

/-- **Meeting the graph through the centre at a given time.** The orbit through `(x, y)` meets the
graph of `k` at time `T` exactly when `y` solves the gluing equation `l • k (l • x) = y` at the rate
`l = e^{-T}`. -/
theorem splitQuadraticFlow_snd_eq_iff_smul_comp_smul_eq {k : Eₛ → Eᵤ} (T : ℝ) (x : Eₛ)
    (y : Eᵤ) :
    (splitQuadraticFlow T (WithLp.toLp 2 (x, y))).snd =
        k (splitQuadraticFlow T (WithLp.toLp 2 (x, y))).fst ↔
      Real.exp (-T) • k (Real.exp (-T) • x) = y := by
  simp only [splitQuadraticFlow_apply, WithLp.toLp_fst, WithLp.toLp_snd]
  constructor <;> intro h <;> simp [← h, smul_smul, ← Real.exp_add]

/-- **The glued orbit at a solved rate, in the model.** If `y` solves the gluing equation
`l • k (l • x) = y` at a rate `l > 0`, with `‖x‖ ≤ ε` and `‖k (l • x)‖ ≤ ε`, then in time `-log l`
the orbit through `(x, y)` reaches the point `(l • x, k (l • x))` of the graph of `k`, and it stays
in the box `‖x‖ ≤ ε, ‖y‖ ≤ ε` meanwhile. -/
theorem splitQuadraticFlow_eq_and_norm_le_of_smul_comp_smul_eq {k : Eₛ → Eᵤ} {ε l : ℝ}
    (hl : 0 < l) {x : Eₛ} {y : Eᵤ} (hx : ‖x‖ ≤ ε) (hfix : l • k (l • x) = y)
    (hk : ‖k (l • x)‖ ≤ ε) :
    splitQuadraticFlow (-Real.log l) (WithLp.toLp 2 (x, y)) =
        WithLp.toLp 2 (l • x, k (l • x)) ∧
      ∀ s ∈ Icc 0 (-Real.log l), ‖(splitQuadraticFlow s (WithLp.toLp 2 (x, y))).fst‖ ≤ ε ∧
        ‖(splitQuadraticFlow s (WithLp.toLp 2 (x, y))).snd‖ ≤ ε := by
  have hexpT : Real.exp (-Real.log l) * l = 1 := by
    rw [Real.exp_neg, Real.exp_log hl, inv_mul_cancel₀ hl.ne']
  -- `‖y‖ = l ‖k (l • x)‖`, and `e^s l ≤ 1` for `s ≤ -log l`.
  have hy : ‖y‖ = l * ‖k (l • x)‖ := by rw [← hfix, norm_smul, Real.norm_of_nonneg hl.le]
  refine ⟨?_, fun s hs ↦ ⟨?_, ?_⟩⟩
  · simp [splitQuadraticFlow_apply, Real.exp_log hl, ← hfix, smul_smul, hexpT]
  · rw [norm_fst_splitQuadraticFlow, WithLp.toLp_fst]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.2 (by linarith [hs.1]))).trans hx
  · rw [norm_snd_splitQuadraticFlow, WithLp.toLp_snd, hy]
    calc Real.exp s * (l * ‖k (l • x)‖) ≤ Real.exp (-Real.log l) * (l * ‖k (l • x)‖) := by
          gcongr; exact hs.2
      _ = ‖k (l • x)‖ := by rw [← mul_assoc, hexpT, one_mul]
      _ ≤ ε := hk

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
  obtain ⟨r, hr, hW'⟩ := WithLp.exists_pos_forall_toLp_mem_of_mem_nhds_zero hW
  -- A bound `l₀` on the rates for which the gluing equation has its solutions `v l`, and for
  -- which the glued points lie in `W`.
  have hlin := tendsto_mul_const_nhdsGT_zero (𝕜 := ℝ)
  obtain ⟨l₀, ⟨v, -, -, hv⟩, hl₀, hl₀₁, hl₀r, hl₀k, hl₀Kk⟩ :=
    ((eventually_exists_continuousOn_smul_comp_smul_eq_iff hδ hη hg hgε hk hk₀).and
      (Filter.Eventually.and self_mem_nhdsWithin (((hlin 1).eventually (gt_mem_nhds one_pos)).and
        (((hlin ε).eventually (gt_mem_nhds hr)).and (((hlin (Kk * ε)).eventually
          (gt_mem_nhds hr)).and ((hlin Kk).eventually (gt_mem_nhds one_pos))))))).exists
  rw [mul_one] at hl₀₁
  filter_upwards [Real.tendsto_exp_neg_atTop_nhds_zero.eventually (ge_mem_nhds hl₀)] with T hTl₀
  set l := Real.exp (-T) with hldef
  have hl : l ∈ Icc 0 l₀ := ⟨(Real.exp_pos _).le, hTl₀⟩
  have hlT : -Real.log l = T := by rw [hldef, Real.log_exp, neg_neg]
  -- The orbit through `(g y, y)` meets the graph of `k` at time `T` for the solution `y = v l` of
  -- the gluing equation at the rate `l = e^{-T}`, staying in the box.
  obtain ⟨hy, hgη, hkg, hiff⟩ := hv l hl
  set y := v l
  have hkε : ‖k (l • g y)‖ ≤ ε :=
    hkg.trans (by nlinarith [mul_nonneg (Kk.coe_nonneg) hε, hl.1, hl.2, Kk.coe_nonneg])
  obtain ⟨hT', hbox⟩ := splitQuadraticFlow_eq_and_norm_le_of_smul_comp_smul_eq (Real.exp_pos _)
    (hgε y hy).le ((hiff y hy).2 rfl) hkε
  rw [hlT] at hT' hbox
  refine ⟨y, hy, hbox, ?_, ?_, ?_⟩
  · rw [hT']
    refine hW' _ _ ?_ ?_
    · rw [norm_smul, Real.norm_of_nonneg hl.1, hgε y hy]
      nlinarith [hl.2]
    · exact hkg.trans_lt (by nlinarith [hl.2, mul_nonneg (Kk.coe_nonneg) hε])
  · rw [hT', WithLp.toLp_fst]
    exact hgη
  · rw [hT', WithLp.toLp_snd, WithLp.toLp_fst]


end TauCeti
