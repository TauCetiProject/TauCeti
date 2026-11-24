/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Passage
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Topology.MetricSpace.Contracting
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
derivative of its contracting component `x` invertible, is such a graph near the centre
(`TauCeti.exists_lipschitzOnWith_graph_of_hasStrictFDerivAt`), by the inverse function theorem.

**The local compactified gluing space at the centre.** Record such an orbit by the pair
`(z, φ_T z)` of its entrance point `z = (g y, y)` and its point on the graph of `k`
(`TauCeti.splitCenterGluingPairs`). Its gluing parameter is `r = e^{-T}`, read off as
`‖x‖ / ε` from the contracting coordinate of the second point, and the matching condition is that
`y` is a fixed point of `y ↦ r • k (r • g y)`. For small `r` this is a contraction of a closed
ball with constant `r² Kk Kg`, whose unique fixed point depends Lipschitz-continuously on `r`
and is `0` at `r = 0`. So the pairs form a single arc, whose closure adds exactly the broken pair
`((g 0, 0), 0)` of the entrance point on the stable set and the centre
(`TauCeti.closure_splitCenterGluingPairs`), and that closure is homeomorphic to a closed interval
(`TauCeti.exists_homeomorph_closure_splitCenterGluingPairs`). This is the analogue at the centre of
`TauCeti.exists_homeomorph_closure_splitGluingPairs`.

In Morse theory, the entrance disc is a piece of the unstable manifold of a critical point `p`
which flows into the critical point `a` at the centre of the box, and the disc through the centre is
a piece of a submanifold through `a` transverse to the unstable manifold of `a`, such as the stable
manifold of a second pseudo-gradient. The glued orbits are then points of `W^u(p)` on that
submanifold converging to `a`.

## Main results

* `TauCeti.exists_lipschitzOnWith_graph_of_hasStrictFDerivAt`: near the centre, the image of a disc
  through the centre transverse to the unstable set is a Lipschitz graph `x ↦ (x, k x)` with
  `k 0 = 0`.
* `TauCeti.eventually_exists_splitQuadraticFlow_snd_eq`: for all large `T`, the orbit through some
  point of the entrance graph stays in the box up to time `T` and meets the graph of `k` at time
  `T`, in a prescribed neighbourhood of the centre.
* `TauCeti.splitCenterGluingPairs`: entrance points paired with the points where their orbits meet
  the graph through the centre.
* `TauCeti.closure_splitCenterGluingPairs`: their closure adds exactly the broken pair.
* `TauCeti.exists_homeomorph_closure_splitCenterGluingPairs`: that closure is a closed interval,
  with the gluing parameter as inverse coordinate.

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
some `z` in a prescribed neighbourhood `V` of `0`. Conversely, near `0` every point `χ z` lies on
the graph of `k`. -/
theorem exists_lipschitzOnWith_graph_of_hasStrictFDerivAt [CompleteSpace G]
    {χ : G → WithLp 2 (Eₛ × Eᵤ)} {χ' : G →L[ℝ] WithLp 2 (Eₛ × Eᵤ)}
    (hχ : HasStrictFDerivAt χ χ' 0) (hχ' : (WithLp.fstL 2 ℝ Eₛ Eᵤ ∘L χ').IsInvertible)
    (hχ₀ : χ 0 = 0) {V : Set G} (hV : V ∈ 𝓝 0) :
    ∃ η > 0, ∃ (K : ℝ≥0) (k : Eₛ → Eᵤ), LipschitzOnWith K k (closedBall 0 η) ∧ k 0 = 0 ∧
      (∀ x ∈ closedBall 0 η, ∃ z ∈ V, χ z = WithLp.toLp 2 (x, k x)) ∧
      ∀ᶠ z in 𝓝 0, (χ z).snd = k (χ z).fst := by
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
  refine ⟨η, hη, K, k, hks.mono fun x hx ↦ (hηs hx).1, by simp [k, hσ₀, hχ₀], fun x hx ↦ ?_,
    ?_⟩
  · obtain ⟨-, hxV, hxa⟩ := hηs hx
    exact ⟨σ x, hxV, WithLp.ofLp_injective 2 (Prod.ext (by simpa [ha_def] using hxa) (by simp [k]))⟩
  · -- Near `0`, `σ` inverts the contracting component on the left, so `k (a z) = (χ z).snd`.
    filter_upwards [ha.eventually_left_inverse] with z hz
    have hk : k (χ z).fst = (χ (σ (a z))).snd := rfl
    rw [hk]
    exact (congrArg (fun w ↦ (χ w).snd) hz).symm

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

/-! ### The local compactified gluing space at the centre -/

section Compactification

variable {ε r₀ : ℝ} {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ}

/-- The pairs `(z, φ_T z)` of a point `z = (g y, y)` of the graph of `g` and the point of its orbit,
at a time `T ≥ 0`, on the graph `x ↦ (x, k x)`, with `‖y‖` and the contracting coordinate of
`φ_T z` at most `r₀ ε`. For `g` with values on the sphere of radius `ε`, the second condition reads
`e^{-T} ≤ r₀`: the number `e^{-T}` is the gluing parameter of the pair. -/
def splitCenterGluingPairs (ε r₀ : ℝ) (g : Eᵤ → Eₛ) (k : Eₛ → Eᵤ) :
    Set (WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)) :=
  {p | ‖p.1.snd‖ ≤ r₀ * ε ∧ p.1.fst = g p.1.snd ∧
    (∃ T, 0 ≤ T ∧ p.2 = splitQuadraticFlow T p.1) ∧ ‖p.2.fst‖ ≤ r₀ * ε ∧ p.2.snd = k p.2.fst}

/-- The conditions defining the gluing pairs at the centre. -/
@[simp]
theorem mem_splitCenterGluingPairs {p : WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)} :
    p ∈ splitCenterGluingPairs ε r₀ g k ↔
      ‖p.1.snd‖ ≤ r₀ * ε ∧ p.1.fst = g p.1.snd ∧
        (∃ T, 0 ≤ T ∧ p.2 = splitQuadraticFlow T p.1) ∧ ‖p.2.fst‖ ≤ r₀ * ε ∧
          p.2.snd = k p.2.fst :=
  Iff.rfl

section Hypotheses

variable (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
  (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
  (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε))) (hk₀ : k 0 = 0)
  (hr₀₁ : r₀ ≤ 1) (hKk : Kk * r₀ ≤ 1)

omit [NormedSpace ℝ Eᵤ] in
include hgε hk hk₀ in
/-- For a gluing parameter `r ∈ [0, r₀]`, the point `r • g y` lies in the domain of `k`, where
`‖k (r • g y)‖ ≤ Kk r ε`. -/
private theorem smul_mem_closedBall_and_norm_k_le {r : ℝ} (hr : r ∈ Icc 0 r₀) {y : Eᵤ}
    (hy : y ∈ closedBall 0 (r₀ * ε)) :
    r • g y ∈ closedBall (0 : Eₛ) (r₀ * ε) ∧ ‖k (r • g y)‖ ≤ Kk * (r * ε) := by
  have hε : 0 ≤ ε := hgε y hy ▸ norm_nonneg _
  have hn : ‖r • g y‖ = r * ε := by rw [norm_smul, Real.norm_of_nonneg hr.1, hgε y hy]
  have hmem : r • g y ∈ closedBall (0 : Eₛ) (r₀ * ε) := by
    rw [mem_closedBall_zero_iff, hn]
    exact mul_le_mul_of_nonneg_right hr.2 hε
  refine ⟨hmem, ?_⟩
  simpa [hk₀, hn] using hk.norm_sub_le hmem (mem_closedBall_self (mul_nonneg (hr.1.trans hr.2) hε))

include hgε hk hk₀ hKk in
/-- The gluing map `y ↦ r • k (r • g y)` at the centre sends the closed ball of radius `r₀ ε` to
itself. -/
private theorem mapsTo_centerGluing {r : ℝ} (hr : r ∈ Icc 0 r₀) :
    MapsTo (fun y ↦ r • k (r • g y)) (closedBall 0 (r₀ * ε)) (closedBall 0 (r₀ * ε)) := by
  intro y hy
  have hε : 0 ≤ ε := hgε y hy ▸ norm_nonneg _
  have hkg := (smul_mem_closedBall_and_norm_k_le hgε hk hk₀ hr hy).2
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg hr.1]
  have hKr : Kk * r ≤ 1 := (mul_le_mul_of_nonneg_left hr.2 Kk.coe_nonneg).trans hKk
  calc r * ‖k (r • g y)‖ ≤ r * (Kk * (r * ε)) := mul_le_mul_of_nonneg_left hkg hr.1
    _ = r * ((Kk * r) * ε) := by ring
    _ ≤ r₀ * (1 * ε) := mul_le_mul hr.2 (mul_le_mul_of_nonneg_right hKr hε)
        (mul_nonneg (mul_nonneg Kk.coe_nonneg hr.1) hε) (hr.1.trans hr.2)
    _ = r₀ * ε := by ring

include hg hgε hk hk₀ in
/-- The gluing map `y ↦ r • k (r • g y)` at the centre is Lipschitz with constant
`Kk * Kg * r₀ ^ 2` on the closed ball of radius `r₀ ε`. -/
private theorem dist_centerGluing_le {r : ℝ} (hr : r ∈ Icc 0 r₀) {y y' : Eᵤ}
    (hy : y ∈ closedBall 0 (r₀ * ε)) (hy' : y' ∈ closedBall 0 (r₀ * ε)) :
    dist (r • k (r • g y)) (r • k (r • g y')) ≤ Kk * Kg * r₀ ^ 2 * dist y y' := by
  have hrr : r * r ≤ r₀ ^ 2 := pow_two r₀ ▸ mul_le_mul hr.2 hr.2 hr.1 (hr.1.trans hr.2)
  calc dist (r • k (r • g y)) (r • k (r • g y'))
      = r * dist (k (r • g y)) (k (r • g y')) := by rw [dist_smul₀, Real.norm_of_nonneg hr.1]
    _ ≤ r * (Kk * dist (r • g y) (r • g y')) := by
        gcongr
        · exact hr.1
        · exact hk.dist_le_mul _ (smul_mem_closedBall_and_norm_k_le hgε hk hk₀ hr hy).1 _
            (smul_mem_closedBall_and_norm_k_le hgε hk hk₀ hr hy').1
    _ = r * (Kk * (r * dist (g y) (g y'))) := by rw [dist_smul₀, Real.norm_of_nonneg hr.1]
    _ ≤ r * (Kk * (r * (Kg * dist y y'))) := by
        gcongr
        · exact hr.1
        · exact hr.1
        · exact hg.dist_le_mul _ hy _ hy'
    _ = Kk * Kg * (r * r) * dist y y' := by ring
    _ ≤ Kk * Kg * r₀ ^ 2 * dist y y' := by gcongr

include hgε hk hk₀ hr₀₁ in
/-- The gluing map `y ↦ r • k (r • g y)` at the centre depends Lipschitz-continuously on the gluing
parameter, uniformly on the closed ball of radius `r₀ ε`. -/
private theorem dist_centerGluing_le_dist {r s : ℝ} (hr : r ∈ Icc 0 r₀) (hs : s ∈ Icc 0 r₀)
    {y : Eᵤ} (hy : y ∈ closedBall 0 (r₀ * ε)) :
    dist (r • k (r • g y)) (s • k (s • g y)) ≤ 2 * Kk * ε * dist r s := by
  have hε : 0 ≤ ε := hgε y hy ▸ norm_nonneg _
  obtain ⟨hr', hkr⟩ := smul_mem_closedBall_and_norm_k_le hgε hk hk₀ hr hy
  obtain ⟨hs', -⟩ := smul_mem_closedBall_and_norm_k_le hgε hk hk₀ hs hy
  have hr1 : r ≤ 1 := hr.2.trans hr₀₁
  have hs1 : s ≤ 1 := hs.2.trans hr₀₁
  have hgy : ‖g y‖ = ε := hgε y hy
  calc dist (r • k (r • g y)) (s • k (s • g y))
      ≤ dist (r • k (r • g y)) (s • k (r • g y)) + dist (s • k (r • g y)) (s • k (s • g y)) :=
        dist_triangle _ _ _
    _ = dist r s * ‖k (r • g y)‖ + s * dist (k (r • g y)) (k (s • g y)) := by
        rw [dist_smul₀, Real.norm_of_nonneg hs.1, dist_eq_norm, dist_eq_norm, ← sub_smul,
          norm_smul, Real.norm_eq_abs, Real.dist_eq]
    _ ≤ dist r s * (Kk * (1 * ε)) + 1 * (Kk * (dist r s * ε)) := by
        gcongr
        · exact hkr.trans (by gcongr)
        · calc dist (k (r • g y)) (k (s • g y)) ≤ Kk * dist (r • g y) (s • g y) :=
                hk.dist_le_mul _ hr' _ hs'
            _ = Kk * (dist r s * ε) := by
                rw [dist_eq_norm, ← sub_smul, norm_smul, hgy, Real.dist_eq, Real.norm_eq_abs]
    _ = 2 * Kk * ε * dist r s := by ring

end Hypotheses

/-- **The gluing parameter of a pair at the centre.** A gluing pair at the centre is
`((g y, y), (r • g y, k (r • g y)))` for its gluing parameter `r ∈ (0, r₀]` and the expanding
coordinate `y` of its entrance point, which solves the gluing equation `r • k (r • g y) = y`. -/
private theorem exists_mem_Ioc_of_mem_splitCenterGluingPairs
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε) (hε : 0 < ε)
    {p : WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ)} (hp : p ∈ splitCenterGluingPairs ε r₀ g k) :
    ∃ r ∈ Ioc 0 r₀, r • k (r • g p.1.snd) = p.1.snd ∧
      (WithLp.toLp 2 (g p.1.snd, p.1.snd),
        WithLp.toLp 2 (r • g p.1.snd, k (r • g p.1.snd))) = p := by
  obtain ⟨hp₁, hpg, ⟨T, -, hpT⟩, hp₂, hpk⟩ := hp
  -- The gluing parameter is `r = e^{-T}`.
  set r := Real.exp (-T) with hrdef
  have hrpos : 0 < r := Real.exp_pos _
  have hp2fst : p.2.fst = r • g p.1.snd := by
    rw [hpT, splitQuadraticFlow_apply, ← hpg, WithLp.toLp_fst]
  have hp2snd : p.2.snd = Real.exp T • p.1.snd := by
    rw [hpT, splitQuadraticFlow_apply, WithLp.toLp_snd]
  have hrr₀ : r ≤ r₀ := by
    rw [hp2fst, norm_smul, Real.norm_of_nonneg hrpos.le,
      hgε _ (mem_closedBall_zero_iff.2 hp₁)] at hp₂
    exact le_of_mul_le_mul_right hp₂ hε
  refine ⟨r, ⟨hrpos, hrr₀⟩, ?_, Prod.ext ?_ ?_⟩
  · rw [← hp2fst, ← hpk, hp2snd, smul_smul, hrdef, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, one_smul]
  · apply WithLp.ofLp_injective
    ext
    · simp [hpg]
    · simp
  · apply WithLp.ofLp_injective
    ext
    · simp [hp2fst]
    · simp [hpk, hp2fst]

/-- **Parametrizing the gluing pairs at the centre.** Under the hypotheses of
`TauCeti.exists_homeomorph_closure_splitCenterGluingPairs`, the gluing pairs at the centre are the
values `F r`, `0 < r ≤ r₀`, of a map `F` continuous on `[0, r₀]`, with `F 0` the broken pair
`((g 0, 0), 0)` and the gluing parameter `r` recovered as `‖(F r).2.fst‖ / ε`. -/
private theorem exists_splitCenterGluingPairs_parametrization [CompleteSpace Eᵤ]
    (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
    (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε))) (hk₀ : k 0 = 0) (hε : 0 < ε)
    (hr₀ : 0 ≤ r₀) (hr₀₁ : r₀ ≤ 1) (hKk : Kk * r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1) :
    ∃ F : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ),
      ContinuousOn F (Icc 0 r₀) ∧ F '' Ioc 0 r₀ = splitCenterGluingPairs ε r₀ g k ∧
      F 0 = (WithLp.toLp 2 (g 0, 0), 0) ∧ ∀ r ∈ Icc 0 r₀, ‖(F r).2.fst‖ / ε = r := by
  -- The gluing maps contract the closed ball of radius `r₀ ε` and depend Lipschitz-continuously on
  -- the gluing parameter, so their fixed points form a Lipschitz family.
  obtain ⟨y, hylip, hy⟩ := exists_lipschitzOnWith_forall_fixedPt (S := Icc 0 r₀)
    (T := fun r v ↦ r • k (r • g v)) isClosed_closedBall.isComplete
    ⟨0, mem_closedBall_self (by positivity)⟩ hK (fun r hr ↦ mapsTo_centerGluing hgε hk hk₀ hKk hr)
    (fun r hr v hv v' hv' ↦ dist_centerGluing_le hg hgε hk hk₀ hr hv hv')
    (fun r hr r' hr' v hv ↦ dist_centerGluing_le_dist hgε hk hk₀ hr₀₁ hr hr' hv)
  have hyc := hylip.continuousOn
  set F : ℝ → WithLp 2 (Eₛ × Eᵤ) × WithLp 2 (Eₛ × Eᵤ) := fun r ↦
    (WithLp.toLp 2 (g (y r), y r), WithLp.toLp 2 (r • g (y r), k (r • g (y r)))) with hFdef
  have hgy (r : ℝ) (hr : r ∈ Icc 0 r₀) := hgε _ (hy r hr).1
  have hnorm (r : ℝ) (hr : r ∈ Icc 0 r₀) : ‖(F r).2.fst‖ = r * ε := by
    simp [hFdef, norm_smul, Real.norm_of_nonneg hr.1, hgy r hr]
  -- Continuity: `g` and `k` are Lipschitz on their domains, into which `y` and `r • g (y r)` map.
  have hgc : ContinuousOn (fun r ↦ g (y r)) (Icc 0 r₀) :=
    hg.continuousOn.comp hyc fun r hr ↦ (hy r hr).1
  have hxc : ContinuousOn (fun r ↦ r • g (y r)) (Icc 0 r₀) := continuousOn_id.smul hgc
  have hkc : ContinuousOn (fun r ↦ k (r • g (y r))) (Icc 0 r₀) :=
    hk.continuousOn.comp hxc fun r hr ↦
      (smul_mem_closedBall_and_norm_k_le hgε hk hk₀ hr (hy r hr).1).1
  have hFc : ContinuousOn F (Icc 0 r₀) :=
    ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn (hgc.prodMk hyc)).prodMk
      ((WithLp.prod_continuous_toLp 2 Eₛ Eᵤ).comp_continuousOn (hxc.prodMk hkc))
  have hy₀ : y 0 = 0 := by
    have h := (hy 0 (left_mem_Icc.2 hr₀)).2.1
    rw [zero_smul] at h
    exact h.symm
  refine ⟨F, hFc, ?_, by simp [hFdef, hy₀, hk₀], fun r hr ↦ by
    rw [hnorm r hr, mul_div_cancel_right₀ _ hε.ne']⟩
  ext p
  constructor
  · -- The pair of gluing parameter `r > 0` is reached at the time `T = -log r ≥ 0`.
    rintro ⟨r, hr, rfl⟩
    have hr' : r ∈ Icc 0 r₀ := Ioc_subset_Icc_self hr
    have hr1 : r ≤ 1 := hr.2.trans hr₀₁
    refine ⟨mem_closedBall_zero_iff.1 (hy r hr').1, rfl, ⟨-Real.log r,
      neg_nonneg.2 (Real.log_nonpos hr.1.le hr1), ?_⟩, ?_, rfl⟩
    · rw [splitQuadraticFlow_apply, neg_neg, Real.exp_log hr.1, Real.exp_neg, Real.exp_log hr.1]
      apply WithLp.ofLp_injective
      ext
      · simp [hFdef]
      · have h := congrArg (fun v ↦ r⁻¹ • v) (hy r hr').2.1
        simp only [smul_smul, inv_mul_cancel₀ hr.1.ne', one_smul] at h
        simp [hFdef, h]
    · rw [hnorm r hr']
      exact mul_le_mul_of_nonneg_right hr.2 hε.le
  · -- Conversely, the expanding entrance coordinate of a pair of gluing parameter `r` is a fixed
    -- point of the gluing map, hence `y r`.
    intro hp
    obtain ⟨r, hr, hfix, hpe⟩ := exists_mem_Ioc_of_mem_splitCenterGluingPairs hgε hε hp
    have hpy := (hy r (Ioc_subset_Icc_self hr)).2.2 _ (mem_closedBall_zero_iff.2 hp.1) hfix
    exact ⟨r, hr, by rw [← hpe, hpy]⟩

section Single

variable [CompleteSpace Eᵤ]
  (hg : LipschitzOnWith Kg g (closedBall 0 (r₀ * ε)))
  (hgε : ∀ y ∈ closedBall 0 (r₀ * ε), ‖g y‖ = ε)
  (hk : LipschitzOnWith Kk k (closedBall 0 (r₀ * ε))) (hk₀ : k 0 = 0) (hε : 0 < ε)
  (hr₀ : 0 < r₀) (hr₀₁ : r₀ ≤ 1) (hKk : Kk * r₀ ≤ 1) (hK : Kk * Kg * r₀ ^ 2 < 1)

include hg hgε hk hk₀ hε hr₀ hr₀₁ hKk hK

/-- **The closure of the gluing pairs at the centre.** The closure adds exactly the broken pair
`((g 0, 0), 0)` of the entrance point on the stable set and the centre. -/
theorem closure_splitCenterGluingPairs :
    closure (splitCenterGluingPairs ε r₀ g k) =
      insert (WithLp.toLp 2 (g 0, 0), 0) (splitCenterGluingPairs ε r₀ g k) := by
  obtain ⟨F, hF, himage, hF₀, -⟩ :=
    exists_splitCenterGluingPairs_parametrization hg hgε hk hk₀ hε hr₀.le hr₀₁ hKk hK
  have hclosure : closure (F '' Ioc 0 r₀) = F '' Icc 0 r₀ := by
    refine subset_antisymm
      (closure_minimal (image_mono Ioc_subset_Icc_self)
        (isCompact_Icc.image_of_continuousOn hF).isClosed) ?_
    simpa only [closure_Ioc hr₀.ne] using
      ContinuousOn.image_closure (s := Ioc 0 r₀) (f := F) (by rwa [closure_Ioc hr₀.ne])
  rw [← himage, hclosure, ← insert_left_Ioc hr₀.le, image_insert_eq, hF₀]

/-- **The local compactified gluing space at the centre is a closed interval.** Let
`y ↦ (g y, y)` be a `Kg`-Lipschitz graph in the entrance face `‖x‖ = ε` and `x ↦ (x, k x)` a
`Kk`-Lipschitz graph through the centre, with `k 0 = 0`, both over closed balls of radius `r₀ ε`.
If `r₀ ≤ 1`, `Kk r₀ ≤ 1` and `Kk Kg r₀ ^ 2 < 1`, the closure of the gluing pairs at the centre is
homeomorphic to `[0, r₀]`, with inverse coordinate the norm of the contracting coordinate of the
second point divided by `ε`, and with the broken pair `((g 0, 0), 0)` at `0`.

For `r > 0` the pair at `r` is `(z, φ_T z)` with `z = (g y, y)` and `r = e^{-T}`, where `y` is the
unique solution of `y = r • k (r • g y)` of norm at most `r₀ ε`; as `r → 0` the entrance point
tends to the point `(g 0, 0)` of the stable set and `φ_T z` to the centre. -/
theorem exists_homeomorph_closure_splitCenterGluingPairs :
    ∃ e : Icc (0 : ℝ) r₀ ≃ₜ closure (splitCenterGluingPairs ε r₀ g k),
      (∀ p, (e.symm p : ℝ) = ‖p.val.2.fst‖ / ε) ∧
      (e ⟨0, left_mem_Icc.2 hr₀.le⟩).val = (WithLp.toLp 2 (g 0, 0), 0) := by
  obtain ⟨F, hF, himage, hF₀, hnorm⟩ :=
    exists_splitCenterGluingPairs_parametrization hg hgε hk hk₀ hε hr₀.le hr₀₁ hKk hK
  have hcl : closure (splitCenterGluingPairs ε r₀ g k) = range ((Icc 0 r₀).domRestrict F) := by
    rw [closure_splitCenterGluingPairs hg hgε hk hk₀ hε hr₀ hr₀₁ hKk hK, range_domRestrict,
      ← himage, ← hF₀, ← image_insert_eq, insert_left_Ioc hr₀.le]
  have hinj : Function.Injective ((Icc 0 r₀).domRestrict F) := fun r s h ↦ Subtype.ext (by
    rw [← hnorm r r.property, ← hnorm s s.property]
    exact congrArg (fun p ↦ ‖p.2.fst‖ / ε) h)
  have hemb := (hF.domRestrict.isClosedEmbedding hinj).isEmbedding
  refine ⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hcl.symm), fun p ↦ ?_, hF₀⟩
  set r := (hemb.toHomeomorph.trans (Homeomorph.setCongr hcl.symm)).symm p
  have hp : F r = p.val := by
    have := (hemb.toHomeomorph.trans (Homeomorph.setCongr hcl.symm)).apply_symm_apply p
    exact congrArg Subtype.val this
  rw [← hp, hnorm r r.property]

end Single

end Compactification

end TauCeti
