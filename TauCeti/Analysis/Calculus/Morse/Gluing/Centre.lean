/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Passage
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.MetricSpace.Contracting

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

## Main results

* `TauCeti.exists_lipschitzOnWith_graph_of_hasStrictFDerivAt`: near the centre, the image of a disc
  through the centre transverse to the unstable set contains a Lipschitz graph `x ↦ (x, k x)` with
  `k 0 = 0`.
* `TauCeti.eventually_exists_splitQuadraticFlow_snd_eq`: for all large `T`, the orbit through some
  point of the entrance graph stays in the box up to time `T` and meets the graph of `k` at time
  `T`, in a prescribed neighbourhood of the centre.

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
some `z` in a prescribed neighbourhood `V` of `0`. -/
theorem exists_lipschitzOnWith_graph_of_hasStrictFDerivAt [CompleteSpace G]
    {χ : G → WithLp 2 (Eₛ × Eᵤ)} {χ' : G →L[ℝ] WithLp 2 (Eₛ × Eᵤ)}
    (hχ : HasStrictFDerivAt χ χ' 0) (hχ' : (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L χ').IsInvertible)
    (hχ₀ : χ 0 = 0) {V : Set G} (hV : V ∈ 𝓝 0) :
    ∃ η > 0, ∃ (K : ℝ≥0) (k : Eₛ → Eᵤ), LipschitzOnWith K k (closedBall 0 η) ∧ k 0 = 0 ∧
      ∀ x ∈ closedBall 0 η, ∃ z ∈ V, χ z = WithLp.toLp 2 (x, k x) := by
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
  refine ⟨η, hη, K, k, hks.mono fun x hx ↦ (hηs hx).1, by simp [k, hσ₀, hχ₀], fun x hx ↦ ?_⟩
  obtain ⟨-, hxV, hxa⟩ := hηs hx
  exact ⟨σ x, hxV, WithLp.ofLp_injective 2 (Prod.ext (by simpa [ha_def] using hxa) (by simp [k]))⟩

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

/-- **The fixed-point equation of gluing at the centre.** For a small rate `l > 0`, the map
`y ↦ l • k (l • g y)` is a contraction of the closed ball of radius `δ`, so it has a fixed point
there. -/
private theorem exists_smul_comp_smul_eq_self [CompleteSpace Eᵤ] {ε δ η l : ℝ} {Kg Kk : ℝ≥0}
    {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hδ : 0 < δ) (hη : 0 < η)
    (hg : LipschitzOnWith Kg g (closedBall 0 δ)) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) (hl : 0 < l) (hl₁ : l ≤ 1)
    (h₁ : l * ε < η) (h₂ : l * (Kk * ε) < δ) (h₃ : l * (Kk * Kg) < 1) :
    ∃ y ∈ closedBall (0 : Eᵤ) δ, l • k (l • g y) = y := by
  have hε : 0 ≤ ε := hgε 0 (mem_closedBall_self hδ.le) ▸ norm_nonneg _
  have hkg {y : Eᵤ} (hy : y ∈ closedBall 0 δ) :=
    smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl.le h₁.le hy
  set F : Eᵤ → Eᵤ := fun y ↦ l • k (l • g y)
  have hmaps : MapsTo F (closedBall 0 δ) (closedBall 0 δ) := fun y hy ↦ by
    rw [mem_closedBall_zero_iff]
    simp only [F, norm_smul, Real.norm_of_nonneg hl.le]
    nlinarith [(hkg hy).2, mul_nonneg (Kk.coe_nonneg) hε]
  have hcontr : ContractingWith (l.toNNReal * (Kk * (l.toNNReal * Kg)))
      (hmaps.restrict F _ _) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun y y' ↦ ?_⟩
    · rw [← NNReal.coe_lt_coe]
      push_cast [Real.coe_toNNReal _ hl.le]
      nlinarith [mul_nonneg Kk.coe_nonneg Kg.coe_nonneg]
    · rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply]
      push_cast [Real.coe_toNNReal _ hl.le]
      simp only [F, dist_smul₀, Real.norm_of_nonneg hl.le]
      calc l * dist (k (l • g y)) (k (l • g y')) ≤ l * (Kk * dist (l • g y) (l • g y')) :=
            mul_le_mul_of_nonneg_left
              (hk.dist_le_mul _ (hkg y.property).1 _ (hkg y'.property).1) hl.le
        _ = l * (Kk * (l * dist (g y) (g y'))) := by
            rw [dist_smul₀, Real.norm_of_nonneg hl.le]
        _ ≤ l * (Kk * (l * (Kg * dist (y : Eᵤ) y'))) := by
            gcongr
            exact hg.dist_le_mul _ y.property _ y'.property
        _ = l * (Kk * (l * Kg)) * dist (y : Eᵤ) y' := by ring
  obtain ⟨y, hy, hfix, -⟩ := ContractingWith.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps hcontr (mem_closedBall_self hδ.le) (edist_ne_top _ _)
  exact ⟨y, hy, hfix⟩

omit [NormedSpace ℝ Eₛ] [NormedSpace ℝ Eᵤ] in
/-- A neighbourhood of the centre of the split model contains the points whose two components
have norm less than some `r > 0`. -/
private theorem exists_pos_forall_toLp_mem {W : Set (WithLp 2 (Eₛ × Eᵤ))} (hW : W ∈ 𝓝 0) :
    ∃ r > 0, ∀ (x : Eₛ) (y : Eᵤ), ‖x‖ < r → ‖y‖ < r → WithLp.toLp 2 (x, y) ∈ W := by
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.1 ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).tendsto 0
    (by simpa using hW))
  refine ⟨r, hr, fun x y hx hy ↦ hrW (?_ : (x, y) ∈ ball ((0 : Eₛ), (0 : Eᵤ)) r)⟩
  rw [← ball_prod_same]
  exact mk_mem_prod (mem_ball_zero_iff.2 hx) (mem_ball_zero_iff.2 hy)

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
  obtain ⟨r, hr, hW'⟩ := exists_pos_forall_toLp_mem hW
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
  obtain ⟨y, hy, hyF⟩ :=
    exists_smul_comp_smul_eq_self hδ hη hg hgε hk hk₀ hl hl₁ h₁ h₂ (by linarith)
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

end TauCeti
