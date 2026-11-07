/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Hofer
public import TauCeti.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hofer's lemma on a ball and rescaling where derivatives blow up

Hofer's lemma (`hofer` in Mathlib) moves a point `x` of a complete metric space, by at most `2 ε`,
to a point `x'` at which a continuous nonnegative function `ϕ` controls itself on a whole ball:
`ϕ ≤ 2 ϕ(x')` on the ball of radius `ε' ≤ ε` about `x'`, while `ε ϕ(x) ≤ ε' ϕ(x')`. It is the
device that turns blow-up of the derivatives of a sequence of maps into a rescaled sequence with
uniformly bounded derivatives, the first step in extracting bubbles in Gromov compactness.

The maps arising there are only defined, or only `C¹`, near the point of blow-up, so this file
first localizes the lemma: `ϕ` only needs to be continuous and nonnegative on the closed ball of
radius `3 ε` about `x`, which contains every point the lemma looks at
(`TauCeti.hofer_of_continuousOn_closedBall`).

Applied along a sequence of functions `ϕ i` blowing up at points `x i → x₀`, at radii
`ε i → 0` with `ε i * ϕ i (x i) → ∞`, it gives centres `c i → x₀` and radii `ρ i → 0` with
`ρ i * ϕ i (c i) → ∞` and `ϕ i ≤ 2 ϕ i (c i)` on the ball of radius `ρ i` about `c i`
(`TauCeti.exists_tendsto_hofer`).

For the derivatives `ϕ i = ‖du i‖` of maps `u i` between real normed spaces, rescaling by
`ε i = 1 / ‖du i (c i)‖` gives maps `v i (w) = u i (c i + ε i w)` whose derivatives have norm one
at the origin and norm at most two on balls of radii `R i → ∞`, while the rescaled balls
`c i + ε i • closedBall 0 (R i)` shrink to the point of blow-up
(`TauCeti.exists_tendsto_norm_fderiv_rescale_le`). This is the normalization of
McDuff–Salamon, Section 4.2. Extracting a convergent subsequence of the rescaled maps needs
elliptic estimates for the equation they solve and is not part of this file.

## Main results

* `TauCeti.hofer_of_continuousOn_closedBall`: Hofer's lemma for a function continuous on a closed
  ball.
* `TauCeti.exists_tendsto_hofer`: Hofer's lemma along a sequence of functions blowing up at a
  point.
* `TauCeti.exists_tendsto_norm_fderiv_rescale_le`: rescaling maps whose derivatives blow up at a
  point to maps with derivatives of norm one at the origin and at most two on growing balls.

## References

* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*,
  Comm. Pure Appl. Math. 45 (1992), 583–622.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section 4.2 (rescaling at a point where the derivatives
  blow up) and Section 4.6 (Hofer's lemma).
-/

public section

open Filter Metric Set Topology

namespace TauCeti

section Hofer

variable {X : Type*} [MetricSpace X] [CompleteSpace X]

/-- **Hofer's lemma on a closed ball.** Let `ϕ` be continuous and nonnegative on the closed ball
of radius `3 ε` about `x`. Then there are `0 < ε' ≤ ε` and a point `x'` within `2 ε` of `x` with
`ε ϕ(x) ≤ ε' ϕ(x')` and `ϕ ≤ 2 ϕ(x')` on the closed ball of radius `ε'` about `x'`. -/
theorem hofer_of_continuousOn_closedBall (x : X) {ε : ℝ} (hε : 0 < ε) {ϕ : X → ℝ}
    (hϕ : ContinuousOn ϕ (closedBall x (3 * ε))) (hϕ₀ : ∀ y ∈ closedBall x (3 * ε), 0 ≤ ϕ y) :
    ∃ ε' > 0, ∃ x' : X, ε' ≤ ε ∧ dist x' x ≤ 2 * ε ∧ ε * ϕ x ≤ ε' * ϕ x' ∧
      ∀ y, dist x' y ≤ ε' → ϕ y ≤ 2 * ϕ x' := by
  set S := closedBall x (3 * ε)
  have : CompleteSpace S := isClosed_closedBall.completeSpace_coe
  -- Apply Hofer's lemma in the complete metric space `S`, on which `ϕ` is continuous.
  obtain ⟨ε', hε', x', hε'ε, hx'x, hϕx, hball⟩ := hofer (X := S)
    ⟨x, mem_closedBall_self (by positivity)⟩ ε hε hϕ.domRestrict fun y ↦ hϕ₀ y y.2
  rw [Subtype.dist_eq] at hx'x
  refine ⟨ε', hε', x', hε'ε, hx'x, by simpa using hϕx, fun y hy ↦ ?_⟩
  -- Every point within `ε'` of `x'` lies in `S`, so the conclusion of the lemma applies to it.
  have hyS : y ∈ S := mem_closedBall.2 <| by
    have := dist_triangle y x' x
    rw [dist_comm] at hy
    linarith
  exact hball ⟨y, hyS⟩ (by rwa [Subtype.dist_eq])

variable {ι : Type*} {l : Filter ι}

/-- **Hofer's lemma along a sequence blowing up at a point.** Let the functions `ϕ i` be continuous
and nonnegative on a closed ball about `x₀`, and let `ϕ i (x i) → ∞` along points `x i → x₀`.
Then there are centres `c i → x₀` and radii `ρ i > 0` with `ρ i → 0` and `ρ i * ϕ i (c i) → ∞`,
such that eventually `ϕ i (x i) ≤ ϕ i (c i)` and `ϕ i ≤ 2 ϕ i (c i)` on the closed ball of radius
`ρ i` about `c i`. -/
theorem exists_tendsto_hofer {ϕ : ι → X → ℝ} {x : ι → X} {x₀ : X} {r : ℝ} (hr : 0 < r)
    (hϕ : ∀ i, ContinuousOn (ϕ i) (closedBall x₀ r)) (hϕ₀ : ∀ i, ∀ y ∈ closedBall x₀ r, 0 ≤ ϕ i y)
    (hx : Tendsto x l (𝓝 x₀)) (hϕx : Tendsto (fun i ↦ ϕ i (x i)) l atTop) :
    ∃ (c : ι → X) (ρ : ι → ℝ), (∀ i, 0 < ρ i) ∧ Tendsto c l (𝓝 x₀) ∧ Tendsto ρ l (𝓝 0) ∧
      Tendsto (fun i ↦ ρ i * ϕ i (c i)) l atTop ∧
      ∀ᶠ i in l, ϕ i (x i) ≤ ϕ i (c i) ∧ ∀ y, dist (c i) y ≤ ρ i → ϕ i y ≤ 2 * ϕ i (c i) := by
  -- Apply Hofer's lemma at `x i` with the radius `ε i = ϕ i (x i) ^ (-1/2)`, so that `ε i → 0`
  -- while `ε i * ϕ i (x i) = √(ϕ i (x i)) → ∞`.
  set ε : ι → ℝ := fun i ↦ (√(max 1 (ϕ i (x i))))⁻¹
  have hε (i : ι) : 0 < ε i := inv_pos.2 <| Real.sqrt_pos.2 <| lt_max_of_lt_left one_pos
  have hmax : Tendsto (fun i ↦ max 1 (ϕ i (x i))) l atTop :=
    tendsto_atTop_mono (fun i ↦ le_max_right _ _) hϕx
  have hε0 : Tendsto ε l (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hmax)
  have hεϕ : Tendsto (fun i ↦ ε i * ϕ i (x i)) l atTop := by
    refine (Real.tendsto_sqrt_atTop.comp hϕx).congr' ?_
    filter_upwards [hϕx.eventually_ge_atTop 1] with i hi
    simp only [ε, Function.comp_apply, max_eq_right hi, ← div_eq_inv_mul, Real.div_sqrt]
  have hdx : Tendsto (fun i ↦ dist (x i) x₀) l (𝓝 0) := tendsto_iff_dist_tendsto_zero.1 hx
  -- Eventually the ball of radius `3 ε i` about `x i`, where Hofer's lemma looks, lies in the
  -- ball where the functions are continuous.
  have hP : ∀ᶠ i in l, dist (x i) x₀ + 3 * ε i ≤ r := by
    have h := hdx.add (hε0.const_mul 3)
    rw [mul_zero, add_zero] at h
    exact (h.eventually (gt_mem_nhds hr)).mono fun i hi ↦ hi.le
  have hsub (i : ι) (hi : dist (x i) x₀ + 3 * ε i ≤ r) :
      closedBall (x i) (3 * ε i) ⊆ closedBall x₀ r :=
    closedBall_subset_closedBall' (by linarith)
  have key (i : ι) : ∃ c ρ, 0 < ρ ∧ ρ ≤ ε i ∧ dist c (x i) ≤ 2 * ε i ∧
      (dist (x i) x₀ + 3 * ε i ≤ r →
        ε i * ϕ i (x i) ≤ ρ * ϕ i c ∧ ∀ y, dist c y ≤ ρ → ϕ i y ≤ 2 * ϕ i c) := by
    by_cases hi : dist (x i) x₀ + 3 * ε i ≤ r
    · obtain ⟨ρ, hρ, c, hρε, hcx, hϕc, hball⟩ := hofer_of_continuousOn_closedBall (x i) (hε i)
        ((hϕ i).mono (hsub i hi)) fun y hy ↦ hϕ₀ i y (hsub i hi hy)
      exact ⟨c, ρ, hρ, hρε, hcx, fun _ ↦ ⟨hϕc, hball⟩⟩
    · exact ⟨x i, ε i, hε i, le_rfl, by simpa using (hε i).le, fun h ↦ absurd h hi⟩
  choose c ρ hρ hρε hcx hc using key
  have hcx₀ (i : ι) : dist (c i) x₀ ≤ 2 * ε i + dist (x i) x₀ := by
    linarith [dist_triangle (c i) (x i) x₀, hcx i]
  refine ⟨c, ρ, hρ, ?_, squeeze_zero (fun i ↦ (hρ i).le) hρε hε0, ?_, ?_⟩
  · refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) hcx₀ ?_)
    simpa using (hε0.const_mul 2).add hdx
  · exact tendsto_atTop_mono' l (hP.mono fun i hi ↦ (hc i hi).1) hεϕ
  · filter_upwards [hP] with i hi
    refine ⟨?_, (hc i hi).2⟩
    -- From `ε ϕ(x) ≤ ρ ϕ(c) ≤ ε ϕ(c)`, using that `c` stays in the ball where `ϕ ≥ 0`.
    have hc₀ : 0 ≤ ϕ i (c i) := hϕ₀ i _ <| hsub i hi <| mem_closedBall.2 <| by
      linarith [hcx i, hε i]
    exact le_of_mul_le_mul_left ((hc i hi).1.trans
      (mul_le_mul_of_nonneg_right (hρε i) hc₀)) (hε i)

end Hofer

section Rescale

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type*} {l : Filter ι}

/-- **Rescaling where derivatives blow up.** Let the derivatives of maps `u i` be continuous on a
closed ball about `z₀`, and let `‖du i (z i)‖ → ∞` along points `z i → z₀`. Then there are centres
`c i → z₀`, scales `ε i > 0` with `ε i → 0` and radii `R i → ∞` with `ε i * R i → 0`, such that
eventually the rescaled maps `w ↦ u i (c i + ε i • w)` have derivative of norm one at the origin
and derivatives of norm at most two on the closed ball of radius `R i`. -/
theorem exists_tendsto_norm_fderiv_rescale_le {u : ι → E → F} {z : ι → E} {z₀ : E} {r : ℝ}
    (hr : 0 < r) (hu : ∀ i, ContinuousOn (fderiv ℝ (u i)) (closedBall z₀ r))
    (hz : Tendsto z l (𝓝 z₀)) (hblow : Tendsto (fun i ↦ ‖fderiv ℝ (u i) (z i)‖) l atTop) :
    ∃ (c : ι → E) (ε R : ι → ℝ), (∀ i, 0 < ε i) ∧ Tendsto c l (𝓝 z₀) ∧ Tendsto ε l (𝓝 0) ∧
      Tendsto R l atTop ∧ Tendsto (fun i ↦ ε i * R i) l (𝓝 0) ∧
      ∀ᶠ i in l, ‖fderiv ℝ (fun w ↦ u i (c i + ε i • w)) 0‖ = 1 ∧
        ∀ w, ‖w‖ ≤ R i → ‖fderiv ℝ (fun w ↦ u i (c i + ε i • w)) w‖ ≤ 2 := by
  obtain ⟨c, ρ, hρ, hc, hρ0, hρN, hball⟩ := exists_tendsto_hofer hr
    (fun i ↦ (hu i).norm) (fun _ _ _ ↦ norm_nonneg _) hz hblow
  -- Rescale by the inverse of `N i = ‖du i (c i)‖`, which tends to infinity, over the radius
  -- `R i = ρ i * N i`.
  set N : ι → ℝ := fun i ↦ max 1 ‖fderiv ℝ (u i) (c i)‖
  have hN (i : ι) : 0 < N i := lt_max_of_lt_left one_pos
  have hNc : Tendsto (fun i ↦ ‖fderiv ℝ (u i) (c i)‖) l atTop :=
    tendsto_atTop_mono' l (hball.mono fun i hi ↦ hi.1) hblow
  have hNtop : Tendsto N l atTop := tendsto_atTop_mono (fun i ↦ le_max_right _ _) hNc
  refine ⟨c, fun i ↦ (N i)⁻¹, fun i ↦ ρ i * N i, fun i ↦ inv_pos.2 (hN i), hc,
    tendsto_inv_atTop_zero.comp hNtop,
    tendsto_atTop_mono (fun i ↦ mul_le_mul_of_nonneg_left (le_max_right _ _) (hρ i).le) hρN,
    hρ0.congr fun i ↦ by field_simp [(hN i).ne'], ?_⟩
  filter_upwards [hball, hNc.eventually_ge_atTop 1] with i hi hNi
  have hNeq : N i = ‖fderiv ℝ (u i) (c i)‖ := max_eq_right hNi
  have hNinv : ‖(N i)⁻¹‖ = (N i)⁻¹ := Real.norm_of_nonneg (inv_pos.2 (hN i)).le
  refine ⟨?_, fun w hw ↦ ?_⟩
  · rw [fderiv_comp_add_smul, smul_zero, add_zero, norm_smul, hNinv, ← hNeq,
      inv_mul_cancel₀ (hN i).ne']
  · -- The point `c i + (N i)⁻¹ • w` lies within `ρ i` of `c i`, where `‖du i‖ ≤ 2 N i`.
    have hy : dist (c i) (c i + (N i)⁻¹ • w) ≤ ρ i := by
      rw [dist_self_add_right, norm_smul, hNinv, inv_mul_le_iff₀ (hN i)]
      linarith
    rw [fderiv_comp_add_smul, norm_smul, hNinv, inv_mul_le_iff₀ (hN i)]
    linarith [hi.2 _ hy]

end Rescale

end TauCeti
