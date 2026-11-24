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

**The gluing arc.** Write `l = e^{-T}` for the rate. For `l ∈ [0, l₀]` with `l₀` small, the
contraction `y ↦ l • k (l • g y)` has a unique fixed point `y l`, and the estimate
`‖y l - y l'‖ ≤ 2 (l + l') Kk ε |l - l'|` between the fixed points at two rates shows that `y` is
continuous, with `y 0 = 0` (`TauCeti.exists_continuousOn_smul_comp_smul_eq_self`). For `l > 0` the
orbit of `(g (y l), y l)` stays in the box up to time `-log l`, where it reaches the point
`(l • g (y l), k (l • g (y l)))` of the graph of `k`
(`TauCeti.splitQuadraticFlow_neg_log_of_smul_comp_smul_eq_self`). So these orbits form an arc,
continuous in `l`, which ends at the entrance point `(g 0, 0)` of the stable set and at the
centre for `l = 0`, and every orbit from the entrance graph meeting the graph of `k` at a small rate
is one of them.

The image of a disc through the centre which is strictly differentiable at `0`, with the
derivative of its contracting component `x` invertible, contains such a graph near the centre, and
near `0` the disc lies on it (`TauCeti.exists_lipschitzOnWith_graph_of_hasStrictFDerivAt`), by the
inverse function theorem.

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
* `TauCeti.exists_continuousOn_smul_comp_smul_eq_self`: the fixed point of the gluing at rate
  `l ∈ [0, l₀]` is unique and continuous in `l`.
* `TauCeti.splitQuadraticFlow_neg_log_of_smul_comp_smul_eq_self`: from the entrance point of a fixed
  point at rate `l > 0`, the orbit reaches the graph of `k` in the box at time `-log l`.

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
some `z` in a prescribed neighbourhood `V` of `0`; conversely, near `0` every point of the disc
lies on the graph. -/
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
  refine ⟨η, hη, K, k, hks.mono fun x hx ↦ (hηs hx).1, by simp [k, hσ₀, hχ₀], fun x hx ↦ ?_,
    hleft.mono fun z hz ↦ ?_⟩
  · obtain ⟨-, hxV, hxa⟩ := hηs hx
    exact ⟨σ x, hxV, WithLp.ofLp_injective 2 (Prod.ext (by simpa [ha_def] using hxa) (by simp [k]))⟩
  · -- Near `0`, the local inverse recovers `z` from the contracting component of `χ z`.
    have hz' : σ (χ z).fst = z := hz
    simp only [k, hz']

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

/-- A fixed point `y` of `y ↦ l • k (l • g y)` in the closed ball of radius `δ`, for a rate `l`
with `l ε ≤ η` and `l Kk ≤ 1`, satisfies `‖y‖ ≤ l ε`. -/
private theorem norm_le_of_smul_comp_smul_eq_self {ε δ η l : ℝ} {Kk : ℝ≥0} {g : Eᵤ → Eₛ}
    {k : Eₛ → Eᵤ} (hη : 0 < η) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) (hl : 0 ≤ l) (h : l * ε ≤ η)
    (hKk : l * Kk ≤ 1) {y : Eᵤ} (hy : y ∈ closedBall 0 δ) (hfix : l • k (l • g y) = y) :
    ‖y‖ ≤ l * ε := by
  have hε : 0 ≤ ε := (hgε y hy) ▸ norm_nonneg _
  have hkn := (smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl h hy).2
  rw [← hfix, norm_smul, Real.norm_of_nonneg hl]
  have : (Kk : ℝ) * (l * ε) ≤ ε := by nlinarith
  exact mul_le_mul_of_nonneg_left (hkn.trans this) hl

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

/-- **The glued orbit at the centre.** If `l > 0` and `y` is a fixed point of
`y ↦ l • k (l • g y)` with `‖g y‖ = ε` and `‖y‖ ≤ l ε`, then the orbit of the entrance point
`(g y, y)` stays in the box `‖x‖ ≤ ε, ‖y‖ ≤ ε` up to time `-log l`, at which it reaches the point
`(l • g y, k (l • g y))` of the graph of `k`. -/
theorem splitQuadraticFlow_neg_log_of_smul_comp_smul_eq_self {ε l : ℝ} {g : Eᵤ → Eₛ}
    {k : Eₛ → Eᵤ} {y : Eᵤ} (hl : 0 < l) (hgy : ‖g y‖ = ε) (hy : ‖y‖ ≤ l * ε)
    (hfix : l • k (l • g y) = y) :
    (∀ s ∈ Icc 0 (-Real.log l), ‖(splitQuadraticFlow s (WithLp.toLp 2 (g y, y))).fst‖ ≤ ε ∧
      ‖(splitQuadraticFlow s (WithLp.toLp 2 (g y, y))).snd‖ ≤ ε) ∧
      splitQuadraticFlow (-Real.log l) (WithLp.toLp 2 (g y, y)) =
        WithLp.toLp 2 (l • g y, k (l • g y)) := by
  have hε : 0 ≤ ε := hgy ▸ norm_nonneg _
  refine ⟨fun s hs ↦ ⟨?_, ?_⟩, ?_⟩
  · rw [norm_fst_splitQuadraticFlow, WithLp.toLp_fst, hgy]
    exact mul_le_of_le_one_left hε (Real.exp_le_one_iff.2 (by linarith [hs.1]))
  · rw [norm_snd_splitQuadraticFlow, WithLp.toLp_snd]
    calc Real.exp s * ‖y‖ ≤ Real.exp (-Real.log l) * (l * ε) :=
          mul_le_mul (Real.exp_le_exp.2 hs.2) hy (norm_nonneg _) (Real.exp_pos _).le
      _ = ε := by rw [Real.exp_neg, Real.exp_log hl, ← mul_assoc, inv_mul_cancel₀ hl.ne', one_mul]
  · have hky : k (l • g y) = l⁻¹ • y := by rw [eq_inv_smul_iff₀ hl.ne', hfix]
    rw [splitQuadraticFlow_apply, WithLp.toLp_fst, WithLp.toLp_snd, neg_neg, Real.exp_log hl,
      Real.exp_neg, Real.exp_log hl, hky]

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
  -- The orbit through `(g y, y)` meets the graph of `k` at time `T` when `y` is a fixed point of
  -- `y ↦ e^{-T} k (e^{-T} g y)`.
  obtain ⟨y, hy, hyF⟩ :=
    exists_smul_comp_smul_eq_self hδ hη hg hgε hk hk₀ hl hl₁ h₁ h₂ (by linarith)
  obtain ⟨hgη, hkg⟩ := smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl.le h₁.le hy
  have hny := norm_le_of_smul_comp_smul_eq_self hη hgε hk hk₀ hl.le h₁.le h₄.le hy hyF
  -- At time `T = -log l` the orbit is at `(e^{-T} g y, k (e^{-T} g y))`.
  obtain ⟨hb, hT'⟩ := splitQuadraticFlow_neg_log_of_smul_comp_smul_eq_self hl (hgε y hy) hny hyF
  have hTl : -Real.log l = T := by rw [hldef, Real.log_exp, neg_neg]
  rw [hTl] at hb hT'
  refine ⟨y, hy, hb, ?_, ?_, ?_⟩
  · rw [hT']
    refine hW' _ _ ?_ ?_
    · rw [norm_smul, Real.norm_of_nonneg hl.le, hgε y hy]
      exact h₅
    · exact hkg.trans_lt (by linarith)
  · rw [hT', WithLp.toLp_fst]
    exact hgη
  · rw [hT', WithLp.toLp_snd, WithLp.toLp_fst]

/-! ### The gluing arc at the centre -/

/-- **The fixed point of gluing at the centre depends Lipschitz-continuously on the rate.** For
rates `l, l' ≥ 0` with `l ε, l' ε ≤ η` and `l l' Kk Kg ≤ 1 / 2`, fixed points `y` of
`y ↦ l • k (l • g y)` and `y'` of `y ↦ l' • k (l' • g y)` in the closed ball of radius `δ` satisfy
`‖y - y'‖ ≤ 2 (l + l') Kk ε |l - l'|`. For `l = l'` this is the uniqueness of the fixed point. -/
private theorem norm_sub_le_of_smul_comp_smul_eq_self {ε δ η l l' : ℝ} {Kg Kk : ℝ≥0}
    {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hη : 0 < η)
    (hg : LipschitzOnWith Kg g (closedBall 0 δ)) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) (hl : 0 ≤ l) (hl' : 0 ≤ l')
    (h₁ : l * ε ≤ η) (h₁' : l' * ε ≤ η) (h₃ : l * l' * (Kk * Kg) ≤ 1 / 2)
    {y y' : Eᵤ} (hy : y ∈ closedBall 0 δ) (hy' : y' ∈ closedBall 0 δ)
    (hfix : l • k (l • g y) = y) (hfix' : l' • k (l' • g y') = y') :
    ‖y - y'‖ ≤ 2 * ((l + l') * (Kk * ε)) * |l - l'| := by
  have hmem := (smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl h₁ hy).1
  obtain ⟨hmem', hk'⟩ := smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl' h₁' hy'
  -- The entrance points differ by at most `|l - l'| ε + l' Kg ‖y - y'‖`.
  have hgd : ‖l • g y - l' • g y'‖ ≤ |l - l'| * ε + l' * (Kg * ‖y - y'‖) := by
    have h : l • g y - l' • g y' = (l - l') • g y + l' • (g y - g y') := by
      simp only [sub_smul, smul_sub]
      abel
    rw [h]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, hgε y hy]
    · rw [norm_smul, Real.norm_of_nonneg hl']
      exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hg.dist_le_mul _ hy _ hy') hl'
  have hkd : ‖k (l • g y) - k (l' • g y')‖ ≤ Kk * ‖l • g y - l' • g y'‖ := by
    simpa [dist_eq_norm] using hk.dist_le_mul _ hmem _ hmem'
  have hsplit : y - y' = l • (k (l • g y) - k (l' • g y')) + (l - l') • k (l' • g y') := by
    conv_lhs => rw [← hfix, ← hfix']
    simp only [smul_sub, sub_smul]
    abel
  have hD : ‖y - y'‖ ≤ l * (Kk * (|l - l'| * ε + l' * (Kg * ‖y - y'‖))) +
      |l - l'| * (Kk * (l' * ε)) := by
    conv_lhs => rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg hl]
      exact mul_le_mul_of_nonneg_left (hkd.trans (mul_le_mul_of_nonneg_left hgd Kk.coe_nonneg)) hl
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hk' (abs_nonneg _)
  -- The term `l l' Kk Kg ‖y - y'‖` is at most half of `‖y - y'‖`.
  have hhalf := mul_le_mul_of_nonneg_right h₃ (norm_nonneg (y - y'))
  nlinarith [abs_nonneg (l - l'), Kk.coe_nonneg]

/-- **The gluing arc at the centre.** Let `y ↦ (g y, y)` be a `Kg`-Lipschitz graph in the entrance
face `‖x‖ = ε` over the closed ball of radius `δ > 0` of the expanding factor, and
`x ↦ (x, k x)` a `Kk`-Lipschitz graph through the centre over the closed ball of radius `η > 0` of
the contracting factor, with `k 0 = 0`. There are `l₀ > 0` and a family `y`, continuous on
`[0, l₀]`, such that for every rate `l ∈ [0, l₀]` the point `y l` is the unique fixed point of
`y ↦ l • k (l • g y)` in the closed ball of radius `δ`, with `‖y l‖ ≤ l ε` and `l • g (y l)` in the
closed ball of radius `η`. For `l > 0` the orbit of `(g (y l), y l)` meets the graph of `k` at time
`-log l` (`TauCeti.splitQuadraticFlow_neg_log_of_smul_comp_smul_eq_self`), and `y 0 = 0`, so the
entrance points form an arc ending at the entrance point `(g 0, 0)` of the stable set. -/
theorem exists_continuousOn_smul_comp_smul_eq_self [CompleteSpace Eᵤ] {ε δ η : ℝ}
    {Kg Kk : ℝ≥0} {g : Eᵤ → Eₛ} {k : Eₛ → Eᵤ} (hδ : 0 < δ) (hη : 0 < η)
    (hg : LipschitzOnWith Kg g (closedBall 0 δ)) (hgε : ∀ y ∈ closedBall 0 δ, ‖g y‖ = ε)
    (hk : LipschitzOnWith Kk k (closedBall 0 η)) (hk₀ : k 0 = 0) :
    ∃ l₀ > 0, ∃ y : ℝ → Eᵤ, ContinuousOn y (Icc 0 l₀) ∧ ∀ l ∈ Icc 0 l₀,
      y l ∈ closedBall 0 δ ∧ ‖y l‖ ≤ l * ε ∧ l • g (y l) ∈ closedBall 0 η ∧
        l • k (l • g (y l)) = y l ∧ ∀ y' ∈ closedBall 0 δ, l • k (l • g y') = y' → y' = y l := by
  have hε : 0 ≤ ε := hgε 0 (mem_closedBall_self hδ.le) ▸ norm_nonneg _
  -- A small rate `l₀`, beating every constant in play.
  have hsmall (C c : ℝ) (hc : 0 < c) : ∀ᶠ l in 𝓝[>] (0 : ℝ), l * C < c :=
    nhdsWithin_le_nhds (((continuous_id.mul continuous_const).tendsto' 0 0 (by simp)).eventually
      (gt_mem_nhds hc))
  obtain ⟨l₀, ⟨hl₀, h₀⟩, h₁, h₂, h₃, h₄⟩ := ((eventually_mem_nhdsWithin.and
    (hsmall 1 1 one_pos)).and ((hsmall ε η hη).and ((hsmall (Kk * ε) δ hδ).and
      ((hsmall (Kk * Kg) (1 / 2) (by norm_num)).and (hsmall Kk 1 one_pos))))).exists
  rw [mem_Ioi] at hl₀
  rw [mul_one] at h₀
  -- For each rate in `[0, l₀]`, a fixed point in the closed ball of radius `δ`.
  have hex (l : ℝ) : ∃ y : Eᵤ, l ∈ Icc 0 l₀ → y ∈ closedBall 0 δ ∧ l • k (l • g y) = y := by
    by_cases hl : l ∈ Icc 0 l₀
    · rcases hl.1.eq_or_lt with rfl | hlpos
      · exact ⟨0, fun _ ↦ ⟨mem_closedBall_self hδ.le, by simp⟩⟩
      · obtain ⟨y, hy, hfix⟩ := exists_smul_comp_smul_eq_self hδ hη hg hgε hk hk₀ hlpos
          (hl.2.trans h₀.le) (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hl.2 hε) h₁)
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hl.2 (by positivity)) h₂)
          (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hl.2 (by positivity)) (by linarith))
        exact ⟨y, fun _ ↦ ⟨hy, hfix⟩⟩
    · exact ⟨0, fun h ↦ absurd h hl⟩
  choose y hy using hex
  have hεl {l : ℝ} (hl : l ∈ Icc 0 l₀) : l * ε ≤ η :=
    (mul_le_mul_of_nonneg_right hl.2 hε).trans h₁.le
  have hKl {l l' : ℝ} (hl : l ∈ Icc 0 l₀) (hl' : l' ∈ Icc 0 l₀) : l * l' * (Kk * Kg) ≤ 1 / 2 := by
    have hll' : l * l' ≤ l₀ := by nlinarith [hl.1, hl.2, hl'.1, hl'.2]
    nlinarith [mul_nonneg Kk.coe_nonneg Kg.coe_nonneg]
  have hest {l l' : ℝ} (hl : l ∈ Icc 0 l₀) (hl' : l' ∈ Icc 0 l₀) {y' : Eᵤ}
      (hy' : y' ∈ closedBall 0 δ) (hfix' : l' • k (l' • g y') = y') :
      ‖y l - y'‖ ≤ 2 * ((l + l') * (Kk * ε)) * |l - l'| :=
    norm_sub_le_of_smul_comp_smul_eq_self hη hg hgε hk hk₀ hl.1 hl'.1 (hεl hl) (hεl hl')
      (hKl hl hl') (hy l hl).1 hy' (hy l hl).2 hfix'
  refine ⟨l₀, hl₀, y, ?_, fun l hl ↦ ⟨(hy l hl).1, ?_,
    (smul_mem_closedBall_and_norm_le hη hgε hk hk₀ hl.1 (hεl hl) (hy l hl).1).1, (hy l hl).2,
    fun y' hy' hfix' ↦ ?_⟩⟩
  · -- The fixed point is Lipschitz in the rate, with constant `4 l₀ Kk ε`.
    refine (LipschitzOnWith.of_dist_le_mul (K := (4 * l₀ * (Kk * ε)).toNNReal)
      fun l hl l' hl' ↦ ?_).continuousOn
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    refine (hest hl hl' (hy l' hl').1 (hy l' hl').2).trans ?_
    have : (l + l') * (Kk * ε) ≤ 2 * l₀ * (Kk * ε) :=
      mul_le_mul_of_nonneg_right (by linarith [hl.2, hl'.2]) (by positivity)
    nlinarith [abs_nonneg (l - l')]
  · exact norm_le_of_smul_comp_smul_eq_self hη hgε hk hk₀ hl.1 (hεl hl)
      (by nlinarith [hl.2, Kk.coe_nonneg]) (hy l hl).1 (hy l hl).2
  · have h := hest hl hl hy' hfix'
    rw [sub_self, abs_zero, mul_zero] at h
    exact (sub_eq_zero.1 (norm_le_zero_iff.1 h)).symm

end TauCeti
