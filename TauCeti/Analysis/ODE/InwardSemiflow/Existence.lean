/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.ODE.InwardSemiflow.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.Positivity

/-!
# Local existence, joint continuity, and completeness of inward forward semiflows

Building on `TauCeti/Analysis/ODE/InwardSemiflow/Basic.lean`, this file constructs local forward
integral curves of a locally Lipschitz vector field `X` on `U ∩ C` that is strictly inward to a
closed convex subset `C` of a Banach space, and establishes the topological and global properties of
`TauCeti.forwardSemiflow`:

* `TauCeti.exists_local_forwardSemiflow_continuousOn`: constrained Picard iteration on the closed
  subset of `C(Icc 0 b, E)` lying in the inward cone tube
  `closedBall (x + t • X x) (ε / 2 * t) ⊆ C`, giving uniform short-time existence, integral fixed
  points, spatial Lipschitz dependence, and joint continuity.
* `TauCeti.exists_isOpen_forwardSemiflowDomain`, `TauCeti.continuousOn_forwardSemiflow`: relative
  openness of `forwardSemiflowDomain X (U ∩ C)` in `Ici 0 ×ˢ (U ∩ C)` and joint continuity of
  `uncurry (forwardSemiflow X (U ∩ C))` via cocycle propagation.
* `TauCeti.not_mapClusterPt_nhdsLT_forwardSemiflow`,
  `TauCeti.eventually_notMem_nhdsLT_forwardSemiflow`,
  `TauCeti.forwardSemiflowInterval_eq_Ici_of_isCompact`,
  `TauCeti.forwardSemiflowInterval_eq_Ici_of_isCompact_sublevel`: forward compact escape at finite
  endpoints and global forward completeness under compactness or a proper Lyapunov function.
* `TauCeti.forwardSemiflow_const_one_Ici`, `TauCeti.forwardSemiflow_half_sub_Icc`: closed-form
  model checks on `Ici 0` and `Icc 0 1`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12, 9.16, and 9.24–9.26.
-/

public section

open Filter Function Metric Set intervalIntegral
open scoped NNReal Topology

namespace TauCeti

/-! ### Constrained Picard contraction, openness of domain, and joint continuity -/

section LocalExistenceAndContinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Every continuous path on `[0, b]` lying in the inward cone tube
`closedBall (x + t • X x) (ε / 2 * t)` stays in `ball x₀ (2 * r) ∩ C` and within distance
`(‖X x‖ + ε / 2) * b` of `x`. -/
private theorem mem_ball_and_norm_sub_le_of_mem_inwardTube {C : Set E} {X : E → E}
    {x₀ x : E} {r b ε : ℝ} (hx : x ∈ ball x₀ r ∩ C) (hε : 0 < ε)
    (hin : ∀ t ∈ Ioc 0 b, closedBall (x + t • X x) (ε / 2 * t) ⊆ C)
    (hrad : (‖X x‖ + ε / 2) * b < r) {γ : C(Icc 0 b, E)}
    (hγ : ∀ t : Icc 0 b, γ t ∈ closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ)))
    (t : Icc 0 b) :
    γ t ∈ ball x₀ (2 * r) ∩ C ∧ ‖γ t - x‖ ≤ (‖X x‖ + ε / 2) * b := by
  have ht_cb := hγ t
  have hnorm : ‖γ t - x‖ ≤ (‖X x‖ + ε / 2) * b := by
    have hcb := mem_closedBall_iff_norm.mp ht_cb
    calc ‖γ t - x‖ = ‖(γ t - (x + (t : ℝ) • X x)) + (t : ℝ) • X x‖ := by congr 1; abel
      _ ≤ ε / 2 * (t : ℝ) + (t : ℝ) * ‖X x‖ :=
          (norm_add_le _ _).trans (by rw [norm_smul, Real.norm_of_nonneg t.2.1]; linarith)
      _ = (‖X x‖ + ε / 2) * (t : ℝ) := by ring
      _ ≤ (‖X x‖ + ε / 2) * b := mul_le_mul_of_nonneg_left t.2.2 (by positivity)
  have hC_t : γ t ∈ C := by
    rcases t.2.1.eq_or_lt with ht0 | ht_pos
    · have h0 : γ t ∈ closedBall x 0 := by simpa [← ht0] using ht_cb
      exact (mem_closedBall.mp h0 |> dist_le_zero.mp) ▸ hx.2
    · exact hin t ⟨ht_pos, t.2.2⟩ ht_cb
  refine ⟨⟨mem_ball.mpr ?_, hC_t⟩, hnorm⟩
  have hd_lt : dist (γ t) x < r := by simpa [dist_eq_norm] using hnorm.trans_lt hrad
  linarith [dist_triangle (γ t) x x₀, mem_ball.mp hx.1]

/-- Constrained Picard contraction for a single initial point `x ∈ ball x₀ r ∩ C`, on the closed
subset of `C(Icc 0 b, E)` consisting of paths in `closedBall (x + t • X x) (ε / 2 * t) ⊆ C`. -/
private theorem exists_Icc_trajectory_of_ball_subset {C : Set E} (hC_closed : IsClosed C)
    {X : E → E} {x₀ x : E} {r b ε : ℝ} {K : ℝ≥0} (hx : x ∈ ball x₀ r ∩ C) (hb : 0 < b)
    (hε : 0 < ε) (hK : LipschitzOnWith K X (ball x₀ (2 * r) ∩ C))
    (hin : ∀ t ∈ Ioc 0 b, closedBall (x + t • X x) (ε / 2 * t) ⊆ C)
    (hrad : (‖X x‖ + ε / 2) * b < r)
    (hself : (K : ℝ) * ((‖X x‖ + ε / 2) * b) ≤ ε / 2)
    (hcontr : (K : ℝ) * b ≤ 1 / 2) :
    ∃ γ : ℝ → E, γ 0 = x ∧ MapsTo γ (Icc 0 b) (ball x₀ (2 * r) ∩ C) ∧
      (∀ t ∈ Icc 0 b, γ t = x + ∫ s in (0 : ℝ)..t, X (γ s)) ∧
      ∀ t ∈ Icc 0 b, HasDerivWithinAt γ (X (γ t)) (Icc 0 b) t := by
  let _ := hC_closed
  let S : Set C(Icc 0 b, E) :=
    {γ | ∀ t : Icc 0 b, γ t ∈ closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ))}
  have hS_closed : IsClosed S := by
    rw [show S = ⋂ t : Icc 0 b, (fun γ : C(Icc 0 b, E) ↦ γ t) ⁻¹'
      closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ)) by ext; simp [S]]
    exact isClosed_iInter fun t ↦ isClosed_closedBall.preimage (by fun_prop)
  have : CompleteSpace S := hS_closed.completeSpace_coe
  have : Nonempty S := ⟨⟨⟨fun t ↦ x + (t : ℝ) • X x, by fun_prop⟩,
    fun t ↦ mem_closedBall_self (mul_nonneg (half_pos hε).le t.2.1)⟩⟩
  have hS_mem (γ : S) (t : Icc 0 b) :=
    mem_ball_and_norm_sub_le_of_mem_inwardTube hx hε hin hrad γ.2 t
  let f : S → ℝ → E := fun γ s ↦ X (γ.1 (projIcc 0 b hb.le s))
  have hf_cont (γ : S) : Continuous (f γ) :=
    hK.continuousOn.comp_continuous (γ.1.continuous.comp continuous_projIcc)
      fun _ ↦ (hS_mem γ _).1
  let P₀ : S → C(Icc 0 b, E) := fun γ ↦ ⟨fun t ↦ x + ∫ s in (0 : ℝ)..(t : ℝ), f γ s,
    ((continuous_primitive (fun _ _ ↦ (hf_cont γ).intervalIntegrable _ _) 0).const_add x).comp
      continuous_subtype_val⟩
  have hr_pos : 0 < r := dist_nonneg.trans_lt hx.1
  let P : S → S := fun γ ↦ ⟨P₀ γ, fun t ↦ by
    simp only [P₀, ContinuousMap.coe_mk, mem_closedBall, dist_eq_norm]
    rw [show x + (t : ℝ) • X x = x + ∫ _ in (0 : ℝ)..(t : ℝ), X x by simp,
      add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub ((hf_cont γ).intervalIntegrable _ _) intervalIntegrable_const]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2)
      fun s _ ↦ ?_).trans (by rw [sub_zero, abs_of_nonneg t.2.1])
    rw [← dist_eq_norm]
    refine (hK.dist_le_mul _ (hS_mem γ _).1 x
      ⟨ball_subset_ball (by linarith) hx.1, hx.2⟩).trans ?_
    rw [dist_eq_norm]
    exact (mul_le_mul_of_nonneg_left (hS_mem γ _).2 K.coe_nonneg).trans hself⟩
  have hP : ContractingWith (1 / 2) P := by
    refine ⟨by norm_num, lipschitzWith_iff_dist_le_mul.mpr fun γ₁ γ₂ ↦ ?_⟩
    rw [Subtype.dist_eq, ContinuousMap.dist_le (by positivity)]
    intro t
    simp only [P, P₀, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub]
    rw [← intervalIntegral.integral_sub ((hf_cont γ₁).intervalIntegrable _ _)
      ((hf_cont γ₂).intervalIntegrable _ _)]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (K : ℝ) * dist γ₁ γ₂)
      fun s _ ↦ ?_).trans ?_
    · rw [← dist_eq_norm]
      exact (hK.dist_le_mul _ (hS_mem γ₁ _).1 _ (hS_mem γ₂ _).1).trans
        (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist _) K.coe_nonneg)
    · rw [sub_zero, abs_of_nonneg t.2.1]
      calc (K : ℝ) * dist γ₁ γ₂ * (t : ℝ) = ((K : ℝ) * (t : ℝ)) * dist γ₁ γ₂ := by ring
        _ ≤ ↑(1 / 2 : ℝ≥0) * dist γ₁ γ₂ := by
            rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_two]
            exact mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_left t.2.2 K.coe_nonneg).trans hcontr) dist_nonneg
  set γstar : S := hP.fixedPoint
  let γ : ℝ → E := fun t ↦ x + ∫ s in (0 : ℝ)..t, f γstar s
  have hγ_eq (t : ℝ) (ht : t ∈ Icc 0 b) : γ t = γstar.1 ⟨t, ht⟩ :=
    congr_arg (fun z : S ↦ z.1 ⟨t, ht⟩) hP.fixedPoint_isFixedPt
  have hf_eq (t : ℝ) (ht : t ∈ Icc 0 b) : f γstar t = X (γ t) := by
    simp only [f, projIcc_of_mem hb.le ht, hγ_eq t ht]
  refine ⟨γ, by simp [γ], fun t ht ↦ hγ_eq t ht ▸ (hS_mem γstar ⟨t, ht⟩).1,
    fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · simp only [γ, add_right_inj]
    exact intervalIntegral.integral_congr fun s hs ↦
      hf_eq s ⟨(uIcc_of_le ht.1 ▸ hs).1, (uIcc_of_le ht.1 ▸ hs).2.trans ht.2⟩
  · exact (hf_eq t ht ▸
      ((hf_cont γstar).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x).hasDerivWithinAt

/-- **Uniform local forward existence, spatial Lipschitz dependence, and joint continuity** of
`forwardSemiflow` around a point `x₀ ∈ U ∩ C` where `X x₀ ∈ strictInwardCone C x₀`. -/
theorem exists_local_forwardSemiflow_continuousOn {C U : Set E} (hC : Convex ℝ C)
    (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) {x₀ : E} (hx₀ : x₀ ∈ U ∩ C)
    (hX_in : X x₀ ∈ strictInwardCone C x₀) :
    ∃ r > 0, ∃ τ > 0, ∃ K KΦ : ℝ≥0,
      ball x₀ (2 * r) ⊆ U ∧
      LipschitzOnWith K X (ball x₀ (2 * r) ∩ C) ∧
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        forwardSemiflow X (U ∩ C) t y = y + ∫ s in (0 : ℝ)..t,
          X (forwardSemiflow X (U ∩ C) s y)) ∧
      (∀ t ∈ Icc 0 τ,
        LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C)) ∧
      ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 τ ×ˢ (ball x₀ r ∩ C)) := by
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀.1
  obtain ⟨K, V, hV, hKLipV⟩ := hX hx₀
  obtain ⟨rL, hrL, hballV⟩ := Metric.mem_nhdsWithin_iff.mp hV
  obtain ⟨ε, hε, δ, hδ, hev⟩ := hC.exists_uniform_ball_subset_of_mem_strictInwardCone hX_in
  obtain ⟨rI, hrI, hballI⟩ := Metric.mem_nhdsWithin_iff.mp
    ((continuousWithinAt_id.prodMk (hX.continuousOn x₀ hx₀)).eventually hev)
  set r := min (min rU rL) rI / 3 with hr_def
  have hr : 0 < r := by positivity
  have h2rU : ball x₀ (2 * r) ⊆ U :=
    (ball_subset_ball (by linarith [hr_def, min_le_left (min rU rL) rI, min_le_left rU rL])).trans
      hballU
  have hKLip : LipschitzOnWith K X (ball x₀ (2 * r) ∩ C) := hKLipV.mono fun y hy ↦ hballV
    ⟨ball_subset_ball (by linarith [hr_def, min_le_left (min rU rL) rI, min_le_right rU rL]) hy.1,
      h2rU hy.1, hy.2⟩
  set M : ℝ := ‖X x₀‖ + (K : ℝ) * r + ε / 2 + 1 with hM_def
  have hM : 0 < M := by positivity
  set L : ℝ := (K : ℝ) + 1 with hL_def
  have hL : 0 < L := by positivity
  set τ : ℝ := min (min (δ / 4) (r / (4 * M))) (min (ε / (8 * L * M)) (1 / (8 * L)))
  have hτ : 0 < τ := by positivity
  have hKL : (K : ℝ) ≤ L := by linarith [hL_def]
  have htraj (y : E) (hy : y ∈ ball x₀ r ∩ C) :
      Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y ∧
      (∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C) ∧
      (∀ t ∈ Icc 0 τ, forwardSemiflow X (U ∩ C) t y =
        y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y)) := by
    have hyX : ‖X y‖ + ε / 2 < M := by
      have hdist : dist (X y) (X x₀) ≤ (K : ℝ) * r :=
        (hKLip.dist_le_mul y ⟨ball_subset_ball (by linarith) hy.1, hy.2⟩ x₀
          ⟨mem_ball_self (by positivity), hx₀.2⟩).trans
          (mul_le_mul_of_nonneg_left hy.1.le K.coe_nonneg)
      rw [dist_eq_norm] at hdist
      linarith [hM_def, norm_sub_norm_le (X y) (X x₀)]
    have hin (t : ℝ) (ht : t ∈ Ioc 0 (2 * τ)) :
        closedBall (y + t • X y) (ε / 2 * t) ⊆ C := by
      have hτ_δ : τ ≤ δ / 4 := (min_le_left _ _).trans (min_le_left _ _)
      exact (closedBall_subset_ball (mul_lt_mul_of_pos_right (half_lt_self hε) ht.1)).trans
        (hballI ⟨ball_subset_ball (by linarith [hr_def, min_le_right (min rU rL) rI]) hy.1,
          h2rU (ball_subset_ball (by linarith) hy.1), hy.2⟩ hy.2 t
          ⟨ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩)
    have hb_rad : (‖X y‖ + ε / 2) * (2 * τ) < r := by
      have hτ_r : τ ≤ r / (4 * M) := (min_le_left _ _).trans (min_le_right _ _)
      calc (‖X y‖ + ε / 2) * (2 * τ) < M * (2 * (r / (4 * M))) :=
            (mul_lt_mul_of_pos_right hyX (by positivity)).trans_le (by gcongr)
        _ = r / 2 := by have := hM.ne'; field_simp; ring
        _ < r := half_lt_self hr
    have hb_self : (K : ℝ) * ((‖X y‖ + ε / 2) * (2 * τ)) ≤ ε / 2 := by
      have hτ_e : τ ≤ ε / (8 * L * M) := (min_le_right _ _).trans (min_le_left _ _)
      have hle : (K : ℝ) * ((‖X y‖ + ε / 2) * (2 * τ)) ≤ L * (M * (2 * (ε / (8 * L * M)))) := by
        gcongr
      exact hle.trans (by have := hL.ne'; have := hM.ne'; field_simp; linarith)
    have hb_contr : (K : ℝ) * (2 * τ) ≤ 1 / 2 := by
      have hτ_c : τ ≤ 1 / (8 * L) := (min_le_right _ _).trans (min_le_right _ _)
      have hle : (K : ℝ) * (2 * τ) ≤ L * (2 * (1 / (8 * L))) := by gcongr
      exact hle.trans (by have := hL.ne'; field_simp; norm_num)
    obtain ⟨γ, hγ0, hγmem, hγint, hγ'⟩ := exists_Icc_trajectory_of_ball_subset hC_closed hy
      (by positivity : 0 < 2 * τ) hε hKLip hin hb_rad hb_self hb_contr
    have hγU : MapsTo γ (Ico 0 (2 * τ)) (U ∩ C) :=
      fun _ hs ↦ ⟨h2rU (hγmem (Ico_subset_Icc_self hs)).1, (hγmem (Ico_subset_Icc_self hs)).2⟩
    have hγ'_Ico : ∀ s ∈ Ico 0 (2 * τ), HasDerivWithinAt γ (X (γ s)) (Ico 0 (2 * τ)) s :=
      fun s hs ↦ (hγ' s (Ico_subset_Icc_self hs)).mono Ico_subset_Icc_self
    have heq (s : ℝ) (hs : s ∈ Ico 0 (2 * τ)) : γ s = forwardSemiflow X (U ∩ C) s y :=
      eqOn_forwardSemiflow hX (by positivity) hγ0 hγU hγ'_Ico hs
    refine ⟨Ico_subset_forwardSemiflowInterval (by positivity) hγ0 hγU hγ'_Ico,
      fun t ht ↦ heq t ⟨ht.1, by linarith [ht.2]⟩ ▸ hγmem ⟨ht.1, by linarith [ht.2]⟩,
      fun t ht ↦ ?_⟩
    rw [← heq t ⟨ht.1, by linarith [ht.2]⟩, hγint t ⟨ht.1, by linarith [ht.2]⟩]
    exact congr_arg (y + ·) (intervalIntegral.integral_congr fun s hs ↦
      congr_arg X (heq s ⟨(uIcc_of_le ht.1 ▸ hs).1, by linarith [(uIcc_of_le ht.1 ▸ hs).2, ht.2]⟩))
  set KΦ : ℝ≥0 := ⟨Real.exp ((K : ℝ) * τ), (Real.exp_pos _).le⟩
  have hcont {y : E} (hy : y ∈ ball x₀ r ∩ C) :
      ContinuousOn (fun u ↦ forwardSemiflow X (U ∩ C) u y) (Icc 0 τ) :=
    fun s hs ↦ ((hasDerivWithinAt_forwardSemiflow_Ico hX (htraj y hy).1
      ⟨hs.1, by linarith [hs.2]⟩).continuousWithinAt).mono fun _ hu ↦ ⟨hu.1, by linarith [hu.2]⟩
  have hLipΦ (t : ℝ) (ht : t ∈ Icc 0 τ) :
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X (U ∩ C) t y) (ball x₀ r ∩ C) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr fun y₁ hy₁ y₂ hy₂ ↦ ?_
    have hIci {y : E} (hy : y ∈ ball x₀ r ∩ C) (s : ℝ) (hs : s ∈ Ico 0 τ) :
        HasDerivWithinAt (fun u ↦ forwardSemiflow X (U ∩ C) u y)
          (X (forwardSemiflow X (U ∩ C) s y)) (Ici s) s :=
      (hasDerivWithinAt_forwardSemiflow_Ico hX (htraj y hy).1
        ⟨hs.1, by linarith [hs.2]⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
          ⟨Iio (2 * τ), isOpen_Iio, mem_Iio.mpr (by linarith [hs.2]),
            fun _ hu ↦ ⟨hs.1.trans hu.2, hu.1⟩⟩
    refine (dist_le_of_trajectories_ODE_of_mem (v := fun _ ↦ X)
      (s := fun _ ↦ ball x₀ (2 * r) ∩ C) (fun _ _ ↦ hKLip)
      (hcont hy₁) (hIci hy₁) (fun s hs ↦ (htraj y₁ hy₁).2.1 s (Ico_subset_Icc_self hs))
      (hcont hy₂) (hIci hy₂) (fun s hs ↦ (htraj y₂ hy₂).2.1 s (Ico_subset_Icc_self hs))
      (by simp only [forwardSemiflow_zero]; exact le_rfl) t ht).trans ?_
    rw [sub_zero, mul_comm (dist y₁ y₂)]
    change Real.exp ((K : ℝ) * t) * dist y₁ y₂ ≤ Real.exp ((K : ℝ) * τ) * dist y₁ y₂
    gcongr
    exact ht.2
  exact ⟨r, hr, τ, hτ, K, KΦ, h2rU, hKLip, fun y hy ↦ (htraj y hy).1,
    fun y hy ↦ (htraj y hy).2.1, fun y hy ↦ (htraj y hy).2.2, hLipΦ,
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ KΦ hLipΦ fun _ hy ↦ hcont hy⟩

/-- At any point `x ∈ U ∩ C` where a locally Lipschitz field `X` is strictly inward to the closed
convex set `C`, `0` belongs to `forwardSemiflowInterval X (U ∩ C) x`. -/
theorem zero_mem_forwardSemiflowInterval {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X) {x : E} (hx : x ∈ U ∩ C)
    (hX_in : X x ∈ strictInwardCone C x) :
    (0 : ℝ) ∈ forwardSemiflowInterval X (U ∩ C) x := by
  obtain ⟨r, hr, τ, hτ, _, _, _, _, hsub, -⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hx hX_in
  exact hsub x ⟨mem_ball_self hr, hx.2⟩ ⟨le_rfl, by positivity⟩

/-- Propagation of local existence and joint continuity of `forwardSemiflow` up to any time
`T ∈ forwardSemiflowInterval X (U ∩ C) x₀`. -/
theorem exists_continuousOn_Icc_of_mem_forwardSemiflowInterval {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) {x₀ : E} {T : ℝ}
    (hx₀ : x₀ ∈ U ∩ C) (hT : T ∈ forwardSemiflowInterval X (U ∩ C) x₀) :
    ∃ r > 0, ∃ δ > 0, ball x₀ r ⊆ U ∧
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (T + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      ContinuousOn (uncurry (forwardSemiflow X (U ∩ C)))
        (Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ C)) := by
  let Φ := forwardSemiflow X (U ∩ C)
  let P : ℝ → Prop := fun t ↦ ∃ r > 0, ∃ δ > 0, ball x₀ r ⊆ U ∧
    (∀ y ∈ ball x₀ r ∩ C, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
    ContinuousOn (uncurry Φ) (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C))
  have hP_ext {t r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hrU : ball x₀ r ⊆ U)
      (hsub : ∀ y ∈ ball x₀ r ∩ C, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y)
      (hcont : ContinuousOn (uncurry Φ) (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C)))
      {u : ℝ} (hu : u ≤ t + δ / 2) : P u :=
    ⟨r, hr, δ / 4, by positivity, hrU, fun y hy ↦
      (Ico_subset_Ico_right (by linarith)).trans (hsub y hy),
      hcont.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)⟩
  by_contra hnotPT
  let B : Set ℝ := {t ∈ Icc 0 T | ¬ P t}
  have hBne : B.Nonempty := ⟨T, ⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  have hBbdd : BddBelow B := ⟨0, fun _ ht ↦ ht.1.1⟩
  set b := sInf B
  have hb0 : 0 ≤ b := le_csInf hBne fun _ ht ↦ ht.1.1
  have hbT : b ≤ T := csInf_le hBbdd ⟨⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  obtain ⟨r₀, hr₀, τ₀, hτ₀, _, _, h2r₀U, _, hsub₀, _, _, _, hcont₀⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hx₀ (hX_in x₀ hx₀)
  have hb_pos : 0 < b := lt_of_lt_of_le (by positivity : 0 < τ₀ / 4) <|
    le_csInf hBne fun t ht ↦ le_of_not_gt fun hlt ↦ ht.2 <|
      hP_ext (t := 0) hr₀ (half_pos hτ₀) ((ball_subset_ball (by linarith)).trans h2r₀U)
        (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub₀ y hy))
        (hcont₀.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)) (by linarith)
  have hbJ : b ∈ forwardSemiflowInterval X (U ∩ C) x₀ :=
    Icc_subset_of_mem_forwardSemiflowInterval hT ⟨hb0, hbT⟩
  have hzU : Φ b x₀ ∈ U ∩ C := forwardSemiflow_mem hX hbJ
  obtain ⟨rz, hrz, τz, hτz, _, _, _, _, hsubz, _, _, _, hcontz⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hzU (hX_in _ hzU)
  obtain ⟨η₀, hη₀, hclose_b⟩ := Metric.continuousAt_iff.mp
    ((hasDerivAt_forwardSemiflow hX hbJ hb_pos).continuousAt) rz hrz
  set η := min (b / 2) (min (η₀ / 2) (τz / 3))
  have hη : 0 < η := by positivity
  set s := b - η
  have hs_pos : 0 < s := by linarith [min_le_left (b / 2) (min (η₀ / 2) (τz / 3))]
  have hs_lt_b : s < b := sub_lt_self b hη
  have hbs_le : b - s ≤ τz / 3 := by
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_right (η₀ / 2) (τz / 3)]
  have hΦs_mem : Φ s x₀ ∈ ball (Φ b x₀) rz := hclose_b <| by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt_b)]
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_left (η₀ / 2) (τz / 3)]
  have hPs : P s := by_contra fun hnotPs ↦
    not_lt_of_ge (csInf_le hBbdd ⟨⟨hs_pos.le, hs_lt_b.le.trans hbT⟩, hnotPs⟩) hs_lt_b
  obtain ⟨rs, hrs, δs, hδs, hrsU, hsubs, hconts⟩ := hPs
  have hΦs_cont : ContinuousOn (fun y ↦ Φ s y) (ball x₀ rs ∩ C) :=
    hconts.comp (continuousOn_const.prodMk continuousOn_id)
      fun _ hy ↦ ⟨⟨hs_pos.le, by linarith⟩, hy⟩
  obtain ⟨rc, hrc, hballc⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hΦs_cont x₀ ⟨mem_ball_self hrs, hx₀.2⟩).eventually (isOpen_ball.mem_nhds hΦs_mem))
  set r' := min rs rc
  have hΦs_ball (y : E) (hy : y ∈ ball x₀ r' ∩ C) : Φ s y ∈ ball (Φ b x₀) rz ∩ C := by
    have hy_rs : y ∈ ball x₀ rs ∩ C := ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    exact ⟨hballc ⟨ball_subset_ball (min_le_right _ _) hy.1, hy_rs⟩,
      (forwardSemiflow_mem hX (hsubs y hy_rs ⟨hs_pos.le, by linarith⟩)).2⟩
  have hsub_all (y : E) (hy : y ∈ ball x₀ r' ∩ C) :
      Ico 0 (s + 2 * τz) ⊆ forwardSemiflowInterval X (U ∩ C) y := fun t ht ↦ by
    have hsJ := hsubs y ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩ ⟨hs_pos.le, by linarith⟩
    rcases le_or_gt t s with hts | hst
    · exact Icc_subset_of_mem_forwardSemiflowInterval hsJ ⟨ht.1, hts⟩
    · rw [← sub_add_cancel t s]
      exact (add_mem_forwardSemiflowInterval_iff hX hsJ (by linarith)).mpr
        (hsubz (Φ s y) (hΦs_ball y hy) ⟨by linarith, by linarith [ht.2]⟩)
  have hstep_cont : ContinuousOn (uncurry Φ) (Icc s (s + τz) ×ˢ (ball x₀ r' ∩ C)) := by
    have hΦs_c : ContinuousOn (fun p : ℝ × E ↦ Φ s p.2) (Icc s (s + τz) ×ˢ (ball x₀ r' ∩ C)) :=
      (hΦs_cont.mono (inter_subset_inter_left C (ball_subset_ball (min_le_left _ _)))).comp
        continuousOn_snd fun _ hp ↦ hp.2
    have hmap : ContinuousOn (fun p : ℝ × E ↦ (p.1 - s, Φ s p.2))
        (Icc s (s + τz) ×ˢ (ball x₀ r' ∩ C)) :=
      (continuousOn_fst.sub continuousOn_const).prodMk hΦs_c
    refine (hcontz.comp hmap fun p hp ↦
      ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, hΦs_ball p.2 hp.2⟩).congr fun p hp ↦ ?_
    have htJ : p.1 - s ∈ forwardSemiflowInterval X (U ∩ C) (Φ s p.2) :=
      hsubz (Φ s p.2) (hΦs_ball p.2 hp.2) ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    simpa [Φ, uncurry, sub_add_cancel] using
      forwardSemiflow_add hX (hsub_all p.2 hp.2 ⟨hs_pos.le, by linarith⟩) htJ
  have hglue : ContinuousOn (uncurry Φ) (Icc 0 (s + τz) ×ˢ (ball x₀ r' ∩ C)) := by
    set T₁ := min (s + δs) (s + τz)
    intro p hp
    rcases lt_or_ge p.1 T₁ with hlt | hge
    · refine (hconts p ⟨⟨hp.1.1, hlt.le.trans (min_le_left _ _)⟩,
        ball_subset_ball (min_le_left _ _) hp.2.1, hp.2.2⟩).mono_of_mem_nhdsWithin <|
        mem_nhdsWithin.mpr ⟨Iio T₁ ×ˢ ball x₀ rs, isOpen_Iio.prod isOpen_ball,
          ⟨hlt, ball_subset_ball (min_le_left _ _) hp.2.1⟩,
          fun _ hq ↦ ⟨⟨hq.2.1.1, hq.1.1.le.trans (min_le_left _ _)⟩, hq.1.2, hq.2.2.2⟩⟩
    · have hgt : s < p.1 := (lt_min (by linarith) (by linarith)).trans_le hge
      exact (hstep_cont p ⟨⟨hgt.le, hp.1.2⟩, hp.2⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
        ⟨Ioi s ×ˢ univ, isOpen_Ioi.prod isOpen_univ, ⟨hgt, trivial⟩,
          fun _ hq ↦ ⟨⟨hq.1.1.le, hq.2.1.2⟩, hq.2.2⟩⟩
  have hb_contra : b + τz / 6 ≤ b := le_csInf hBne fun t ht ↦ le_of_not_gt fun hlt ↦
    ht.2 <| hP_ext (t := b) (lt_min hrs hrc) (by positivity : 0 < τz / 3)
      ((ball_subset_ball (min_le_left _ _)).trans hrsU)
      (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub_all y hy))
      (hglue.mono (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)) (by linarith)
  linarith

/-- **Relative openness of the maximal forward semiflow domain.** If `X` is locally Lipschitz on
`U ∩ C` and strictly inward to the closed convex set `C` at every point of `U ∩ C`, then
`forwardSemiflowDomain X (U ∩ C)` is open in the subspace topology of `Ici 0 ×ˢ (U ∩ C)`. -/
theorem exists_isOpen_forwardSemiflowDomain {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ∃ Ω : Set (ℝ × E), IsOpen Ω ∧
      forwardSemiflowDomain X (U ∩ C) = Ω ∩ (Ici 0 ×ˢ (U ∩ C)) := by
  have hloc (p : forwardSemiflowDomain X (U ∩ C)) :
      ∃ W : Set (ℝ × E), IsOpen W ∧ p.1 ∈ W ∧
        W ∩ (Ici 0 ×ˢ (U ∩ C)) ⊆ forwardSemiflowDomain X (U ∩ C) := by
    obtain ⟨hpU, hpJ⟩ := mem_forwardSemiflowDomain_iff.mp p.2
    obtain ⟨r, hr, δ, hδ, _, hsub, _⟩ :=
      exists_continuousOn_Icc_of_mem_forwardSemiflowInterval hC hC_closed hU hX hX_in hpU hpJ
    exact ⟨Iio (p.1.1 + 2 * δ) ×ˢ ball p.1.2 r, isOpen_Iio.prod isOpen_ball,
      ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩, fun q hq ↦
        mem_forwardSemiflowDomain_iff.mpr ⟨hq.2.2, hsub q.2 ⟨hq.1.2, hq.2.2.2⟩ ⟨hq.2.1, hq.1.1⟩⟩⟩
  choose W hW_open hpW hW_sub using hloc
  refine ⟨⋃ p, W p, isOpen_iUnion hW_open, Subset.antisymm (fun q hq ↦ ?_) (fun q hq ↦ ?_)⟩
  · obtain ⟨hqU, hqJ⟩ := mem_forwardSemiflowDomain_iff.mp hq
    exact ⟨mem_iUnion.mpr ⟨⟨q, hq⟩, hpW ⟨q, hq⟩⟩, nonneg_of_mem_forwardSemiflowInterval hqJ, hqU⟩
  · obtain ⟨p, hqp⟩ := mem_iUnion.mp hq.1
    exact hW_sub p ⟨hqp, hq.2⟩

/-- **Joint continuity of the maximal forward semiflow.** If `X` is locally Lipschitz on `U ∩ C`
and strictly inward to the closed convex set `C` on `U ∩ C`, then
`uncurry (forwardSemiflow X (U ∩ C))` is continuous on `forwardSemiflowDomain X (U ∩ C)`. -/
theorem continuousOn_forwardSemiflow {C U : Set E} (hC : Convex ℝ C) (hC_closed : IsClosed C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (forwardSemiflowDomain X (U ∩ C)) := by
  intro p hp
  obtain ⟨hpU, hpJ⟩ := mem_forwardSemiflowDomain_iff.mp hp
  obtain ⟨r, hr, δ, hδ, _, _, hcont⟩ :=
    exists_continuousOn_Icc_of_mem_forwardSemiflowInterval hC hC_closed hU hX hX_in hpU hpJ
  exact (hcont p ⟨⟨nonneg_of_mem_forwardSemiflowInterval hpJ, by linarith⟩,
    mem_ball_self hr, hpU.2⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Iio (p.1 + δ) ×ˢ ball p.2 r, isOpen_Iio.prod isOpen_ball,
        ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩, fun _ hq ↦
          ⟨⟨nonneg_of_mem_forwardSemiflowInterval (mem_forwardSemiflowDomain_iff.mp hq.2).2,
            hq.1.1.le⟩, hq.1.2, (mem_forwardSemiflowDomain_iff.mp hq.2).1.2⟩⟩

end LocalExistenceAndContinuity

/-! ### Forward compact escape and global forward completeness -/

section EscapeAndGlobal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Any finite least upper bound of a `forwardSemiflowInterval` containing `0` is strictly
positive. -/
theorem pos_of_isLUB_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {b : ℝ}
    (h0 : (0 : ℝ) ∈ forwardSemiflowInterval X S x)
    (hb : IsLUB (forwardSemiflowInterval X S x) b) : 0 < b := by
  obtain ⟨c, hc, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval h0
  exact (half_pos hc).trans_le (hb.1 (hsub ⟨by linarith, by linarith⟩))

/-- If `forwardSemiflowInterval X S x` has a finite least upper bound `b`, then it equals
`Ico 0 b`. -/
theorem eq_Ico_of_isLUB_forwardSemiflowInterval {X : E → E} {S : Set E} {x : E} {b : ℝ}
    (hb : IsLUB (forwardSemiflowInterval X S x) b) :
    forwardSemiflowInterval X S x = Ico 0 b := by
  refine Subset.antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨c, htc, hsub⟩ := exists_Ico_subset_of_mem_forwardSemiflowInterval ht
    have hmid : (t + c) / 2 ∈ forwardSemiflowInterval X S x :=
      hsub ⟨by linarith [nonneg_of_mem_forwardSemiflowInterval ht], by linarith⟩
    exact ⟨nonneg_of_mem_forwardSemiflowInterval ht, lt_of_lt_of_le (by linarith) (hb.1 hmid)⟩
  · obtain ⟨s, hs, hts, _⟩ := hb.exists_between ht.2
    exact Icc_subset_of_mem_forwardSemiflowInterval hs ⟨ht.1, hts.le⟩

/-- An unbounded-above `forwardSemiflowInterval` equals `Ici 0`. -/
private theorem eq_Ici_of_not_bddAbove {X : E → E} {S : Set E} {x : E}
    (h : ¬ BddAbove (forwardSemiflowInterval X S x)) :
    forwardSemiflowInterval X S x = Ici 0 :=
  Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) fun t ht ↦
    let ⟨_, hs, hts⟩ := not_bddAbove_iff.mp h t
    Icc_subset_of_mem_forwardSemiflowInterval hs ⟨ht, hts.le⟩

/-- **No cluster point in `U ∩ C` at a finite forward endpoint.** If `b` is the least upper bound
of `forwardSemiflowInterval X (U ∩ C) x`, then `forwardSemiflow X (U ∩ C) · x` cannot accumulate
at any point `z ∈ U ∩ C` as `t → b⁻`. -/
theorem not_mapClusterPt_nhdsLT_forwardSemiflow [CompleteSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) (hX_in : ∀ y ∈ U ∩ C, X y ∈ strictInwardCone C y)
    {x z : E} {b : ℝ} (hx : x ∈ U ∩ C)
    (hb : IsLUB (forwardSemiflowInterval X (U ∩ C) x) b) (hz : z ∈ U ∩ C) :
    ¬ MapClusterPt z (𝓝[<] b) (fun t ↦ forwardSemiflow X (U ∩ C) t x) := by
  intro hcl
  have hb_pos := pos_of_isLUB_forwardSemiflowInterval
    (zero_mem_forwardSemiflowInterval hC hC_closed hU hX hx (hX_in x hx)) hb
  obtain ⟨r, hr, τ, hτ, _, _, _, _, hsub, -⟩ :=
    exists_local_forwardSemiflow_continuousOn hC hC_closed hU hX hz (hX_in z hz)
  obtain ⟨s, hs_ball, hs_Ioo⟩ := ((hcl.frequently (Metric.ball_mem_nhds z hr)).and_eventually
    (Ioo_mem_nhdsLT (max_lt hb_pos (sub_lt_self b hτ)))).exists
  have hsJ : s ∈ forwardSemiflowInterval X (U ∩ C) x :=
    eq_Ico_of_isLUB_forwardSemiflowInterval hb ▸
      ⟨(le_max_left 0 (b - τ)).trans hs_Ioo.1.le, hs_Ioo.2⟩
  have huJ : τ ∈ forwardSemiflowInterval X (U ∩ C) (forwardSemiflow X (U ∩ C) s x) :=
    hsub _ ⟨hs_ball, (forwardSemiflow_mem hX hsJ).2⟩ ⟨hτ.le, by linarith⟩
  linarith [hb.1 ((add_mem_forwardSemiflowInterval_iff hX hsJ hτ.le).mpr huJ),
    (le_max_right 0 (b - τ)).trans_lt hs_Ioo.1]

/-- **Forward compact-escape lemma.** At a finite least upper bound `b` of
`forwardSemiflowInterval X (U ∩ C) x`, the trajectory leaves every compact subset `K ⊆ U ∩ C`
as `t → b⁻`. -/
theorem eventually_notMem_nhdsLT_forwardSemiflow [CompleteSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) (hX_in : ∀ y ∈ U ∩ C, X y ∈ strictInwardCone C y)
    {x : E} {b : ℝ} (hx : x ∈ U ∩ C)
    (hb : IsLUB (forwardSemiflowInterval X (U ∩ C) x) b) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U ∩ C) :
    ∀ᶠ t in 𝓝[<] b, forwardSemiflow X (U ∩ C) t x ∉ K := by
  by_contra h
  obtain ⟨z, hzK, hz⟩ := hK.exists_mapClusterPt_of_frequently (by simpa [not_eventually] using h)
  exact not_mapClusterPt_nhdsLT_forwardSemiflow hC hC_closed hU hX hX_in hx hb (hKU hzK) hz

/-- **Global forward existence under compact trapping.** If a trajectory of `forwardSemiflow` stays
inside a compact subset `K ⊆ U ∩ C`, then it is defined on all of `[0, ∞)`. -/
theorem forwardSemiflowInterval_eq_Ici_of_isCompact_of_mapsTo [CompleteSpace E] {C U : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) (hU : IsOpen U) {X : E → E}
    (hX : LocallyLipschitzOn (U ∩ C) X) (hX_in : ∀ y ∈ U ∩ C, X y ∈ strictInwardCone C y)
    {x : E} (hx : x ∈ U ∩ C) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U ∩ C)
    (hmem : MapsTo (fun t ↦ forwardSemiflow X (U ∩ C) t x)
      (forwardSemiflowInterval X (U ∩ C) x) K) :
    forwardSemiflowInterval X (U ∩ C) x = Ici 0 := by
  refine eq_Ici_of_not_bddAbove fun hbdd ↦ ?_
  have h0 := zero_mem_forwardSemiflowInterval hC hC_closed hU hX hx (hX_in x hx)
  have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
  obtain ⟨t, ht, htK⟩ := ((eventually_mem_set.mpr
    (Ioo_mem_nhdsLT (pos_of_isLUB_forwardSemiflowInterval h0 hlub))).and
      (eventually_notMem_nhdsLT_forwardSemiflow hC hC_closed hU hX hX_in hx hlub hK hKU)).exists
  exact htK (hmem (eq_Ico_of_isLUB_forwardSemiflowInterval hlub ▸ ⟨ht.1.le, ht.2⟩))

/-- **Global forward completeness on a compact convex set.** Every locally Lipschitz strictly inward
vector field on a compact convex set `C` generates a forward semiflow defined for all `t ≥ 0`. -/
theorem forwardSemiflowInterval_eq_Ici_of_isCompact [CompleteSpace E] {C : Set E}
    (hC : Convex ℝ C) (hC_compact : IsCompact C) {X : E → E} (hX : LocallyLipschitzOn C X)
    (hX_in : ∀ y ∈ C, X y ∈ strictInwardCone C y) {x : E} (hx : x ∈ C) :
    forwardSemiflowInterval X C x = Ici 0 := by
  simpa only [univ_inter] using forwardSemiflowInterval_eq_Ici_of_isCompact_of_mapsTo hC
    hC_compact.isClosed isOpen_univ (by simpa only [univ_inter] using hX)
    (fun y hy ↦ hX_in y hy.2) ⟨trivial, hx⟩ hC_compact (fun y hy ↦ ⟨trivial, hy⟩)
    fun _ ht ↦ (forwardSemiflow_mem (by simpa only [univ_inter] using hX) ht).2

/-- **Global forward completeness via a proper Lyapunov / exhaustion function.** If `C` is closed
and convex, `f : E → ℝ` is continuous on `C` with compact sublevel sets `{y ∈ C | f y ≤ R}`, and
`f` is differentiable on `interior C` with `df y (X y) ≤ c`, then every forward trajectory of a
locally Lipschitz strictly inward field `X` on `C` is defined on all of `[0, ∞)`. -/
theorem forwardSemiflowInterval_eq_Ici_of_isCompact_sublevel [CompleteSpace E] {C : Set E}
    (hC : Convex ℝ C) (hC_closed : IsClosed C) {X : E → E} (hX : LocallyLipschitzOn C X)
    (hX_in : ∀ y ∈ C, X y ∈ strictInwardCone C y) {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {c : ℝ}
    (hf_cont : ContinuousOn f C) (hf_deriv : ∀ y ∈ interior C, HasFDerivAt f (df y) y)
    (hf_le : ∀ y ∈ interior C, df y (X y) ≤ c)
    (hf_compact : ∀ R : ℝ, IsCompact {y ∈ C | f y ≤ R}) {x : E} (hx : x ∈ C) :
    forwardSemiflowInterval X C x = Ici 0 := by
  refine eq_Ici_of_not_bddAbove fun hbdd ↦ ?_
  have hX' : LocallyLipschitzOn (univ ∩ C) X := by simpa only [univ_inter] using hX
  have h0 : (0 : ℝ) ∈ forwardSemiflowInterval X C x := by
    simpa only [univ_inter] using
      zero_mem_forwardSemiflowInterval hC hC_closed isOpen_univ hX' ⟨trivial, hx⟩ (hX_in x hx)
  set b := sSup (forwardSemiflowInterval X C x)
  have hlub : IsLUB (forwardSemiflowInterval X C x) b := isLUB_csSup ⟨0, h0⟩ hbdd
  set c' := max c 0
  set R := f x + c' * b
  have htrap (T : ℝ) (hT : T ∈ Ioo 0 b) : forwardSemiflow X C T x ∈ {y ∈ C | f y ≤ R} := by
    have hTJ : T ∈ forwardSemiflowInterval X C x :=
      eq_Ico_of_isLUB_forwardSemiflowInterval hlub ▸ ⟨hT.1.le, hT.2⟩
    refine ⟨forwardSemiflow_mem hX hTJ, ?_⟩
    let g : ℝ → ℝ := fun s ↦ f (forwardSemiflow X C s x) - c' * s
    have hsubT := Icc_subset_of_mem_forwardSemiflowInterval hTJ
    have hg_cont : ContinuousOn g (Icc 0 T) :=
      (hf_cont.comp (fun s hs ↦
        ((hasDerivWithinAt_forwardSemiflow hX (hsubT hs)).continuousWithinAt).mono hsubT)
        fun _ hs ↦ forwardSemiflow_mem hX (hsubT hs)).sub
        (continuousOn_const.mul continuousOn_id)
    have hint (s : ℝ) (hs : s ∈ interior (Icc 0 T)) :
        0 < s ∧ s ∈ forwardSemiflowInterval X C x ∧ forwardSemiflow X C s x ∈ interior C := by
      rw [interior_Icc] at hs
      exact ⟨hs.1, hsubT (Ioo_subset_Icc_self hs),
        forwardSemiflow_mem_interior hC Subset.rfl hX hX_in (hsubT (Ioo_subset_Icc_self hs)) hs.1⟩
    have hg_anti : AntitoneOn g (Icc 0 T) := antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun s ↦ df (forwardSemiflow X C s x) (X (forwardSemiflow X C s x)) - c')
      (convex_Icc 0 T) hg_cont
      (fun s hs ↦ (((hf_deriv _ (hint s hs).2.2).comp_hasDerivAt s
        (hasDerivAt_forwardSemiflow hX (hint s hs).2.1 (hint s hs).1)).sub
          ((hasDerivAt_id' s).const_mul c') |>.congr_deriv (by ring)).hasDerivWithinAt)
      (fun s hs ↦ by linarith [hf_le _ (hint s hs).2.2, le_max_left c 0])
    have hle0T := hg_anti ⟨le_rfl, hT.1.le⟩ ⟨hT.1.le, le_rfl⟩ hT.1.le
    simp only [g, forwardSemiflow_zero, mul_zero, sub_zero] at hle0T
    linarith [mul_le_mul_of_nonneg_left hT.2.le (le_max_right c 0)]
  have hesc : ∀ᶠ t in 𝓝[<] b, forwardSemiflow X C t x ∉ {y ∈ C | f y ≤ R} := by
    simpa only [univ_inter] using eventually_notMem_nhdsLT_forwardSemiflow hC hC_closed
      isOpen_univ hX' (fun y hy ↦ hX_in y hy.2) ⟨trivial, hx⟩
      (by simpa only [univ_inter] using hlub) (hf_compact R) (fun y hy ↦ ⟨trivial, hy.1⟩)
  obtain ⟨t, ht, htK⟩ := ((eventually_mem_set.mpr
    (Ioo_mem_nhdsLT (pos_of_isLUB_forwardSemiflowInterval h0 hlub))).and hesc).exists
  exact htK (htrap t ht)

end EscapeAndGlobal

/-! ### Closed-form model checks -/

section ModelExamples

/-- Closed-form check on the closed half-line `Ici (0 : ℝ)`: the constant inward field `X = 1`
has maximal forward interval `Ici 0`. -/
theorem forwardSemiflowInterval_const_one_Ici {x : ℝ} (hx : x ∈ Ici (0 : ℝ)) :
    forwardSemiflowInterval (fun _ : ℝ ↦ (1 : ℝ)) (Ici (0 : ℝ)) x = Ici 0 :=
  Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) fun t ht ↦
    Ico_subset_forwardSemiflowInterval (b := t + 1) (by linarith [mem_Ici.mp ht]) (add_zero x)
      (fun _ hs ↦ mem_Ici.mpr (by linarith [mem_Ici.mp hx, hs.1]))
      (fun s _ ↦ ((hasDerivAt_id' s).const_add x).hasDerivWithinAt) ⟨ht, lt_add_one t⟩

/-- Closed-form check on the closed half-line `Ici (0 : ℝ)`: the forward semiflow of the constant
inward field `X = 1` is `forwardSemiflow (fun _ ↦ 1) (Ici 0) t x = x + t`. -/
theorem forwardSemiflow_const_one_Ici {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ici (0 : ℝ)) :
    forwardSemiflow (fun _ : ℝ ↦ (1 : ℝ)) (Ici (0 : ℝ)) t x = x + t :=
  (eqOn_forwardSemiflow ((LipschitzWith.const (1 : ℝ)).locallyLipschitz.locallyLipschitzOn)
    (γ := fun s ↦ x + s) (b := t + 1) (by linarith) (add_zero x)
    (fun _ hs ↦ mem_Ici.mpr (by linarith [mem_Ici.mp hx, hs.1]))
    (fun s _ ↦ ((hasDerivAt_id' s).const_add x).hasDerivWithinAt) ⟨ht, lt_add_one t⟩).symm

/-- Explicit trajectory for the affine inward field `y ↦ 1 / 2 - y` on `Icc 0 1`. -/
private theorem mapsTo_and_deriv_half_sub_Icc {x b : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    let γ : ℝ → ℝ := fun s ↦ 1 / 2 + (x - 1 / 2) * Real.exp (-s)
    MapsTo γ (Ico 0 b) (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Ico 0 b, HasDerivWithinAt γ (1 / 2 - γ s) (Ico 0 b) s :=
  ⟨fun s hs ↦ by
      have := Real.exp_pos (-s)
      have := Real.exp_le_one_iff.mpr (by linarith [hs.1] : -s ≤ 0)
      exact ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1, hx.2]⟩,
    fun s _ ↦ ((((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id' s).neg).const_mul
      (x - 1 / 2)).const_add (1 / 2 : ℝ) |>.congr_deriv (by simp)).hasDerivWithinAt⟩

/-- Closed-form check on the unit interval `Icc (0 : ℝ) 1`: the affine inward field
`X y = 1 / 2 - y` has maximal forward interval `Ici 0`. -/
theorem forwardSemiflowInterval_half_sub_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    forwardSemiflowInterval (fun y : ℝ ↦ 1 / 2 - y) (Icc (0 : ℝ) 1) x = Ici 0 :=
  Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) fun t ht ↦ by
    obtain ⟨hmaps, hderiv⟩ := mapsTo_and_deriv_half_sub_Icc (b := t + 1) hx
    exact Ico_subset_forwardSemiflowInterval (by linarith [mem_Ici.mp ht]) (by simp)
      hmaps hderiv ⟨ht, lt_add_one t⟩

/-- Closed-form check on the unit interval `Icc (0 : ℝ) 1`: the forward semiflow of the affine
inward field `X y = 1 / 2 - y` is `1 / 2 + (x - 1 / 2) * exp (-t)`. -/
theorem forwardSemiflow_half_sub_Icc {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Icc (0 : ℝ) 1) :
    forwardSemiflow (fun y : ℝ ↦ 1 / 2 - y) (Icc (0 : ℝ) 1) t x =
      1 / 2 + (x - 1 / 2) * Real.exp (-t) := by
  obtain ⟨hmaps, hderiv⟩ := mapsTo_and_deriv_half_sub_Icc (b := t + 1) hx
  exact (eqOn_forwardSemiflow
    (((LipschitzWith.const (1 / 2 : ℝ)).sub LipschitzWith.id).locallyLipschitz.locallyLipschitzOn)
    (b := t + 1) (by linarith) (by simp) hmaps hderiv ⟨ht, lt_add_one t⟩).symm

end ModelExamples

end TauCeti
