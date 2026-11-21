/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.ODE.InwardSemiflow.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic.Positivity

/-!
# Local existence, joint continuity, and completeness of inward forward semiflows

Constructs local forward integral curves of a locally Lipschitz vector field `X` on `U ∩ C` that
is strictly inward to a convex subset `C` of a Banach space, and proves relative openness of the
maximal domain, joint continuity, forward compact escape, and global forward completeness criteria
for `TauCeti.forwardSemiflow`.

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
  have hnorm : ‖γ t - x‖ ≤ (‖X x‖ + ε / 2) * b := by
    have hcb := mem_closedBall_iff_norm.mp (hγ t)
    calc ‖γ t - x‖ = ‖(γ t - (x + (t : ℝ) • X x)) + (t : ℝ) • X x‖ := by congr 1; abel
      _ ≤ ε / 2 * (t : ℝ) + (t : ℝ) * ‖X x‖ :=
          (norm_add_le _ _).trans (by rw [norm_smul, Real.norm_of_nonneg t.property.1]; linarith)
      _ ≤ (‖X x‖ + ε / 2) * b := by nlinarith [t.property.2, half_pos hε, norm_nonneg (X x)]
  have hC_t : γ t ∈ C := by
    rcases t.property.1.eq_or_lt with ht0 | ht_pos
    · exact (dist_le_zero.mp (mem_closedBall.mp (by simpa [← ht0] using hγ t))) ▸ hx.2
    · exact hin t ⟨ht_pos, t.property.2⟩ (hγ t)
  exact ⟨⟨mem_ball.mpr (by
    rw [← dist_eq_norm] at hnorm
    linarith [dist_triangle (γ t) x x₀, mem_ball.mp hx.1, hnorm.trans_lt hrad]), hC_t⟩, hnorm⟩

/-- Constrained Picard contraction for a single initial point `x ∈ ball x₀ r ∩ C`, on the closed
subset of `C(Icc 0 b, E)` consisting of paths in `closedBall (x + t • X x) (ε / 2 * t) ⊆ C`. -/
private theorem exists_Icc_trajectory_of_ball_subset {C : Set E} {X : E → E} {x₀ x : E}
    {r b ε : ℝ} {K : ℝ≥0} (hx : x ∈ ball x₀ r ∩ C) (hb : 0 < b) (hε : 0 < ε)
    (hK : LipschitzOnWith K X (ball x₀ (2 * r) ∩ C))
    (hin : ∀ t ∈ Ioc 0 b, closedBall (x + t • X x) (ε / 2 * t) ⊆ C)
    (hrad : (‖X x‖ + ε / 2) * b < r) (hself : (K : ℝ) * ((‖X x‖ + ε / 2) * b) ≤ ε / 2)
    (hcontr : (K : ℝ) * b ≤ 1 / 2) :
    ∃ γ : ℝ → E, γ 0 = x ∧ MapsTo γ (Icc 0 b) (ball x₀ (2 * r) ∩ C) ∧
      (∀ t ∈ Icc 0 b, γ t = x + ∫ s in (0 : ℝ)..t, X (γ s)) ∧
      ∀ t ∈ Icc 0 b, HasDerivWithinAt γ (X (γ t)) (Icc 0 b) t := by
  let S : Set C(Icc 0 b, E) :=
    {γ | ∀ t : Icc 0 b, γ t ∈ closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ))}
  have hS_closed : IsClosed S := by
    rw [show S = ⋂ t : Icc 0 b, (fun γ : C(Icc 0 b, E) ↦ γ t) ⁻¹'
      closedBall (x + (t : ℝ) • X x) (ε / 2 * (t : ℝ)) by ext; simp [S]]
    exact isClosed_iInter fun t ↦ isClosed_closedBall.preimage (by fun_prop)
  have : CompleteSpace S := hS_closed.completeSpace_coe
  have : Nonempty S := ⟨⟨⟨fun t ↦ x + (t : ℝ) • X x, by fun_prop⟩,
    fun t ↦ mem_closedBall_self (mul_nonneg (half_pos hε).le t.property.1)⟩⟩
  have hS_mem (γ : S) (t : Icc 0 b) :=
    mem_ball_and_norm_sub_le_of_mem_inwardTube hx hε hin hrad γ.property t
  let f : S → ℝ → E := fun γ s ↦ X (γ.val (projIcc 0 b hb.le s))
  have hf_cont (γ : S) : Continuous (f γ) :=
    hK.continuousOn.comp_continuous (γ.val.continuous.comp continuous_projIcc)
      fun _ ↦ (hS_mem γ _).1
  let P₀ : S → C(Icc 0 b, E) := fun γ ↦ ⟨fun t ↦ x + ∫ s in (0 : ℝ)..(t : ℝ), f γ s,
    ((continuous_primitive (fun _ _ ↦ (hf_cont γ).intervalIntegrable _ _) 0).const_add x).comp
      continuous_subtypeVal⟩
  have hr_pos : 0 < r := dist_nonneg.trans_lt hx.1
  let P : S → S := fun γ ↦ ⟨P₀ γ, fun t ↦ by
    simp only [P₀, ContinuousMap.coe_mk, mem_closedBall, dist_eq_norm]
    rw [show x + (t : ℝ) • X x = x + ∫ _ in (0 : ℝ)..(t : ℝ), X x by simp, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub ((hf_cont γ).intervalIntegrable _ _) intervalIntegrable_const]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2) fun s _ ↦ ?_).trans
      (by rw [sub_zero, abs_of_nonneg t.property.1])
    rw [← dist_eq_norm]
    refine (hK.dist_le_mul _ (hS_mem γ _).1 x
      ⟨ball_subset_ball (by linarith) hx.1, hx.2⟩).trans ?_
    rw [dist_eq_norm]; exact (mul_le_mul_of_nonneg_left (hS_mem γ _).2 K.coe_nonneg).trans hself⟩
  have hP : ContractingWith (1 / 2) P := by
    refine ⟨by norm_num, lipschitzWith_iff_dist_le_mul.mpr fun γ₁ γ₂ ↦ ?_⟩
    rw [Subtype.dist_eq, ContinuousMap.dist_le (by positivity)]; intro t
    simp only [P, P₀, ContinuousMap.coe_mk, dist_eq_norm, add_sub_add_left_eq_sub]
    rw [← intervalIntegral.integral_sub ((hf_cont γ₁).intervalIntegrable _ _)
      ((hf_cont γ₂).intervalIntegrable _ _)]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := (K : ℝ) * dist γ₁ γ₂)
      fun s _ ↦ ?_).trans ?_
    · rw [← dist_eq_norm]
      exact (hK.dist_le_mul _ (hS_mem γ₁ _).1 _ (hS_mem γ₂ _).1).trans
        (mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist _) K.coe_nonneg)
    · rw [sub_zero, abs_of_nonneg t.property.1, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two]
      calc (K : ℝ) * dist γ₁ γ₂ * (t : ℝ) = (K : ℝ) * (t : ℝ) * dist γ₁ γ₂ := by ring
        _ ≤ (K : ℝ) * b * dist γ₁ γ₂ := by gcongr; exact t.property.2
        _ ≤ (1 / 2 : ℝ) * dist γ₁ γ₂ := by gcongr
  set γstar : S := hP.fixedPoint
  let γ : ℝ → E := fun t ↦ x + ∫ s in (0 : ℝ)..t, f γstar s
  have hγ_eq (t : ℝ) (ht : t ∈ Icc 0 b) : γ t = γstar.val ⟨t, ht⟩ :=
    congr_arg (fun z : S ↦ z.val ⟨t, ht⟩) hP.fixedPoint_isFixedPt
  have hf_eq (t : ℝ) (ht : t ∈ Icc 0 b) : f γstar t = X (γ t) := by
    simp only [f, projIcc_of_mem hb.le ht, hγ_eq t ht]
  refine ⟨γ, by simp [γ], fun t ht ↦ hγ_eq t ht ▸ (hS_mem γstar ⟨t, ht⟩).1, fun t ht ↦ ?_,
    fun t ht ↦ (hf_eq t ht ▸
      ((hf_cont γstar).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add x).hasDerivWithinAt⟩
  simp only [γ, add_right_inj]
  exact intervalIntegral.integral_congr fun s hs ↦
    hf_eq s ⟨(uIcc_of_le ht.1 ▸ hs).1, (uIcc_of_le ht.1 ▸ hs).2.trans ht.2⟩

/-- Uniform short-time step size `τ > 0` on `ball x₀ r ∩ C` from uniform inward balls and a
local Lipschitz bound on `ball x₀ (2 * r) ∩ C`. -/
private theorem exists_Ico_and_Icc_forwardSemiflow_of_ball_subset {C U : Set E}
    {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X) {x₀ : E} (hx₀ : x₀ ∈ U ∩ C)
    {r ε δ : ℝ} {K : ℝ≥0} (hr : 0 < r) (hε : 0 < ε) (hδ : 0 < δ)
    (h2rU : ball x₀ (2 * r) ⊆ U) (hKLip : LipschitzOnWith K X (ball x₀ (2 * r) ∩ C))
    (hin_ball : ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Ioo 0 δ, ball (y + t • X y) (ε * t) ⊆ C) :
    ∃ τ > 0,
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      (∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        forwardSemiflow X (U ∩ C) t y ∈ ball x₀ (2 * r) ∩ C) ∧
      ∀ y ∈ ball x₀ r ∩ C, ∀ t ∈ Icc 0 τ,
        forwardSemiflow X (U ∩ C) t y =
          y + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X (U ∩ C) s y) := by
  set M : ℝ := ‖X x₀‖ + (K : ℝ) * r + ε / 2 + 1 with hM_def
  set L : ℝ := (K : ℝ) + 1 with hL_def
  have hM : 0 < M := by positivity
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
      have hdist := (hKLip.dist_le_mul y ⟨ball_subset_ball (by linarith) hy.1, hy.2⟩ x₀
        ⟨mem_ball_self (by positivity), hx₀.2⟩).trans
        (mul_le_mul_of_nonneg_left hy.1.le K.coe_nonneg)
      rw [dist_eq_norm] at hdist; linarith [hM_def, norm_sub_norm_le (X y) (X x₀)]
    have hin (t : ℝ) (ht : t ∈ Ioc 0 (2 * τ)) : closedBall (y + t • X y) (ε / 2 * t) ⊆ C :=
      (closedBall_subset_ball (mul_lt_mul_of_pos_right (half_lt_self hε) ht.1)).trans
        (hin_ball y hy t ⟨ht.1, lt_of_le_of_lt ht.2 <| by
          have hτ_δ : τ ≤ δ / 4 := (min_le_left _ _).trans (min_le_left _ _)
          linarith⟩)
    have hb_rad : (‖X y‖ + ε / 2) * (2 * τ) < r :=
      calc (‖X y‖ + ε / 2) * (2 * τ) < M * (2 * (r / (4 * M))) :=
            (mul_lt_mul_of_pos_right hyX (by positivity)).trans_le
              (by gcongr; exact (min_le_left _ _).trans (min_le_right _ _))
        _ = r / 2 := by field_simp; ring
        _ < r := half_lt_self hr
    have hb_self : (K : ℝ) * ((‖X y‖ + ε / 2) * (2 * τ)) ≤ ε / 2 :=
      calc (K : ℝ) * ((‖X y‖ + ε / 2) * (2 * τ)) ≤ L * (M * (2 * (ε / (8 * L * M)))) := by
            gcongr; exact (min_le_right _ _).trans (min_le_left _ _)
        _ = ε / 4 := by field_simp; ring
        _ ≤ ε / 2 := by linarith
    have hb_contr : (K : ℝ) * (2 * τ) ≤ 1 / 2 :=
      calc (K : ℝ) * (2 * τ) ≤ L * (2 * (1 / (8 * L))) := by
            gcongr; exact (min_le_right _ _).trans (min_le_right _ _)
        _ ≤ 1 / 2 := by field_simp; norm_num
    obtain ⟨γ, hγ0, hγmem, hγint, hγ'⟩ := exists_Icc_trajectory_of_ball_subset hy
      (by positivity : 0 < 2 * τ) hε hKLip hin hb_rad hb_self hb_contr
    have hγU : MapsTo γ (Ico 0 (2 * τ)) (U ∩ C) :=
      fun _ hs ↦ ⟨h2rU (hγmem (Ico_subset_Icc_self hs)).1, (hγmem (Ico_subset_Icc_self hs)).2⟩
    have hγ'_Ico : ∀ s ∈ Ico 0 (2 * τ), HasDerivWithinAt γ (X (γ s)) (Ico 0 (2 * τ)) s :=
      fun s hs ↦ (hγ' s (Ico_subset_Icc_self hs)).mono Ico_subset_Icc_self
    have heq (s : ℝ) (hs : s ∈ Ico 0 (2 * τ)) : γ s = forwardSemiflow X (U ∩ C) s y :=
      hX.eqOn_forwardSemiflow (by positivity) hγ0 hγU hγ'_Ico hs
    refine ⟨Ico_subset_forwardSemiflowInterval (by positivity) hγ0 hγU hγ'_Ico,
      fun t ht ↦ heq t ⟨ht.1, by linarith [ht.2]⟩ ▸ hγmem ⟨ht.1, by linarith [ht.2]⟩,
      fun t ht ↦ ?_⟩
    rw [← heq t ⟨ht.1, by linarith [ht.2]⟩, hγint t ⟨ht.1, by linarith [ht.2]⟩]
    exact congr_arg (y + ·) (intervalIntegral.integral_congr fun s hs ↦
      congr_arg X (heq s ⟨(uIcc_of_le ht.1 ▸ hs).1, by linarith [(uIcc_of_le ht.1 ▸ hs).2, ht.2]⟩))
  exact ⟨τ, hτ, fun y hy ↦ (htraj y hy).1, fun y hy ↦ (htraj y hy).2.1, fun y hy ↦ (htraj y hy).2.2⟩

omit [CompleteSpace E] in
/-- Spatial Grönwall Lipschitz bound and joint continuity of `forwardSemiflow` on `Icc 0 τ ×ˢ B`
from a Lipschitz bound on `X` over a trapping region `B'`. -/
private theorem lipschitzOnWith_and_continuousOn_forwardSemiflow_Icc {S B B' : Set E}
    {X : E → E} (hX : LocallyLipschitzOn S X) {τ : ℝ} {K : ℝ≥0} (hτ : 0 < τ)
    (hKLip : LipschitzOnWith K X B')
    (hsub : ∀ y ∈ B, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X S y)
    (hmem : ∀ y ∈ B, ∀ t ∈ Icc 0 τ, forwardSemiflow X S t y ∈ B') :
    ∃ KΦ : ℝ≥0,
      (∀ t ∈ Icc 0 τ, LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X S t y) B) ∧
      ContinuousOn (uncurry (forwardSemiflow X S)) (Icc 0 τ ×ˢ B) := by
  set KΦ : ℝ≥0 := ⟨Real.exp ((K : ℝ) * τ), (Real.exp_pos _).le⟩
  have hcont {y : E} (hy : y ∈ B) : ContinuousOn (fun u ↦ forwardSemiflow X S u y) (Icc 0 τ) :=
    fun s hs ↦ ((hX.hasDerivWithinAt_forwardSemiflow_Ico (hsub y hy)
      ⟨hs.1, by linarith [hs.2]⟩).continuousWithinAt).mono fun _ hu ↦ ⟨hu.1, by linarith [hu.2]⟩
  have hLipΦ (t : ℝ) (ht : t ∈ Icc 0 τ) :
      LipschitzOnWith KΦ (fun y ↦ forwardSemiflow X S t y) B := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr fun y₁ hy₁ y₂ hy₂ ↦ ?_
    have hIci {y : E} (hy : y ∈ B) (s : ℝ) (hs : s ∈ Ico 0 τ) : HasDerivWithinAt
        (fun u ↦ forwardSemiflow X S u y) (X (forwardSemiflow X S s y)) (Ici s) s :=
      (hX.hasDerivWithinAt_forwardSemiflow_Ico (hsub y hy)
        ⟨hs.1, by linarith [hs.2]⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
          ⟨Iio (2 * τ), isOpen_Iio, mem_Iio.mpr (by linarith [hs.2]),
            fun _ hu ↦ ⟨hs.1.trans hu.2, hu.1⟩⟩
    refine (dist_le_of_trajectories_ODE_of_mem (v := fun _ ↦ X) (s := fun _ ↦ B')
      (fun _ _ ↦ hKLip) (hcont hy₁) (hIci hy₁) (fun s hs ↦ hmem y₁ hy₁ s (Ico_subset_Icc_self hs))
      (hcont hy₂) (hIci hy₂) (fun s hs ↦ hmem y₂ hy₂ s (Ico_subset_Icc_self hs))
      (by simp only [forwardSemiflow_zero]; exact le_rfl) t ht).trans ?_
    rw [sub_zero, mul_comm (dist y₁ y₂)]; change Real.exp ((K : ℝ) * t) * dist y₁ y₂ ≤
      Real.exp ((K : ℝ) * τ) * dist y₁ y₂
    gcongr; exact ht.2
  exact ⟨KΦ, hLipΦ,
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ KΦ hLipΦ fun _ hy ↦ hcont hy⟩

end LocalExistenceAndContinuity

end TauCeti

section LocalExistenceAndContinuity

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Uniform local forward existence, spatial Lipschitz dependence, and joint continuity** of
`forwardSemiflow` around a point `x₀ ∈ U ∩ C` where `X x₀ ∈ strictInwardCone C x₀`. -/
theorem Convex.exists_local_forwardSemiflow_continuousOn {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {X : E → E}
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
  -- Step 1: Choose `r > 0` on which `U`, local Lipschitzness of `X`, and uniform inward balls hold.
  obtain ⟨rU, hrU, hballU⟩ := Metric.isOpen_iff.mp hU x₀ hx₀.1
  obtain ⟨K, V, hV, hKLipV⟩ := hX hx₀
  obtain ⟨rL, hrL, hballV⟩ := Metric.mem_nhdsWithin_iff.mp hV
  obtain ⟨ε, hε, δ, hδ, hev⟩ :=
    hC.exists_uniform_ball_subset_of_continuousWithinAt hX_in (hX.continuousOn x₀ hx₀)
  obtain ⟨rI, hrI, hballI⟩ := Metric.mem_nhdsWithin_iff.mp hev
  set r := min (min rU rL) rI / 3 with hr_def
  have hr : 0 < r := by positivity
  have h2rU : ball x₀ (2 * r) ⊆ U :=
    (ball_subset_ball (by linarith [hr_def, min_le_left (min rU rL) rI, min_le_left rU rL])).trans
      hballU
  have hKLip : LipschitzOnWith K X (ball x₀ (2 * r) ∩ C) := hKLipV.mono fun y hy ↦ hballV
    ⟨ball_subset_ball (by linarith [hr_def, min_le_left (min rU rL) rI, min_le_right rU rL]) hy.1,
      h2rU hy.1, hy.2⟩
  have hin_ball (y : E) (hy : y ∈ ball x₀ r ∩ C) :
      ∀ t ∈ Ioo 0 δ, ball (y + t • X y) (ε * t) ⊆ C :=
    hballI ⟨ball_subset_ball (by linarith [hr_def, min_le_right (min rU rL) rI]) hy.1,
      h2rU (ball_subset_ball (by linarith) hy.1), hy.2⟩ hy.2
  -- Step 2: Uniform constrained Picard existence on `ball x₀ r ∩ C`.
  obtain ⟨τ, hτ, hsub, hmem, hint⟩ := exists_Ico_and_Icc_forwardSemiflow_of_ball_subset hX hx₀
    hr hε hδ h2rU hKLip hin_ball
  -- Step 3: Spatial Grönwall Lipschitz bound and joint continuity on `Icc 0 τ ×ˢ (ball x₀ r ∩ C)`.
  obtain ⟨KΦ, hLipΦ, hcontΦ⟩ := lipschitzOnWith_and_continuousOn_forwardSemiflow_Icc hX hτ
    hKLip hsub hmem
  exact ⟨r, hr, τ, hτ, K, KΦ, h2rU, hKLip, hsub, hmem, hint, hLipΦ, hcontΦ⟩

/-- At any point `x ∈ U ∩ C` where a locally Lipschitz field `X` is strictly inward to the convex
set `C`, `0` belongs to `forwardSemiflowInterval X (U ∩ C) x`. -/
theorem Convex.zero_mem_forwardSemiflowInterval {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X) {x : E} (hx : x ∈ U ∩ C)
    (hX_in : X x ∈ strictInwardCone C x) :
    (0 : ℝ) ∈ forwardSemiflowInterval X (U ∩ C) x := by
  obtain ⟨r, hr, τ, hτ, _, _, _, _, hsub, -⟩ :=
    hC.exists_local_forwardSemiflow_continuousOn hU hX hx hX_in
  exact hsub x ⟨mem_ball_self hr, hx.2⟩ ⟨le_rfl, by positivity⟩

omit [CompleteSpace E] in
/-- **Cocycle continuation along `forwardSemiflowInterval`.** Any local product-neighborhood
property `Q : Set (ℝ × E) → Prop` of `forwardSemiflow X (U ∩ C)` that implies joint continuity, is
closed under restriction, open-cover gluing, and cocycle time-shifting, and holds locally around
every point of `U ∩ C`, propagates to `Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ C)` for every
`T ∈ forwardSemiflowInterval X (U ∩ C) x₀`. -/
theorem LocallyLipschitzOn.exists_Icc_prod_of_mem_forwardSemiflowInterval {C U : Set E}
    {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X) {Q : Set (ℝ × E) → Prop}
    (hQ_mono : ∀ ⦃S₁ S₂⦄, Q S₂ → S₁ ⊆ S₂ → Q S₁)
    (hQ_cont : ∀ ⦃S⦄, Q S → ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) S)
    (hQ_local : ∀ ⦃S⦄, (∀ p ∈ S, ∃ W, IsOpen W ∧ p ∈ W ∧ Q (S ∩ W)) → Q S)
    (hQ_shift : ∀ {s δ τ : ℝ} {B₁ B₂ : Set E},
      Q (Icc 0 (s + δ) ×ˢ B₁) → Q (Icc 0 τ ×ˢ B₂) → 0 ≤ s → 0 < δ →
      (∀ y ∈ B₁, forwardSemiflow X (U ∩ C) s y ∈ B₂) →
      (∀ p ∈ Icc s (s + τ) ×ˢ B₁, uncurry (forwardSemiflow X (U ∩ C)) p =
        uncurry (forwardSemiflow X (U ∩ C)) (p.1 - s, forwardSemiflow X (U ∩ C) s p.2)) →
      Q (Icc s (s + τ) ×ˢ B₁))
    (hQ_loc : ∀ x ∈ U ∩ C, ∃ r > 0, ∃ τ > 0, ball x r ⊆ U ∧
      (∀ y ∈ ball x r ∩ C, Ico 0 (2 * τ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      Q (Icc 0 τ ×ˢ (ball x r ∩ C)))
    {x₀ : E} {T : ℝ} (hx₀ : x₀ ∈ U ∩ C) (hT : T ∈ forwardSemiflowInterval X (U ∩ C) x₀) :
    ∃ r > 0, ∃ δ > 0, ball x₀ r ⊆ U ∧
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (T + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      Q (Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ C)) := by
  let Φ := forwardSemiflow X (U ∩ C)
  let P : ℝ → Prop := fun t ↦ ∃ r > 0, ∃ δ > 0, ball x₀ r ⊆ U ∧
    (∀ y ∈ ball x₀ r ∩ C, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
    Q (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C))
  have hP_ext {t r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hrU : ball x₀ r ⊆ U)
      (hsub : ∀ y ∈ ball x₀ r ∩ C, Ico 0 (t + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y)
      (hQ : Q (Icc 0 (t + δ) ×ˢ (ball x₀ r ∩ C))) {u : ℝ} (hu : u ≤ t + δ / 2) : P u :=
    ⟨r, hr, δ / 4, by positivity, hrU,
      fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub y hy),
      hQ_mono hQ (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)⟩
  by_contra hnotPT
  let B : Set ℝ := {t ∈ Icc 0 T | ¬ P t}
  have hBne : B.Nonempty := ⟨T, ⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  have hBbdd : BddBelow B := ⟨0, fun _ ht ↦ ht.1.1⟩
  set b := sInf B
  have hb0 : 0 ≤ b := le_csInf hBne fun _ ht ↦ ht.1.1
  have hbT : b ≤ T := csInf_le hBbdd ⟨⟨nonneg_of_mem_forwardSemiflowInterval hT, le_rfl⟩, hnotPT⟩
  obtain ⟨r₀, hr₀, τ₀, hτ₀, hr₀U, hsub₀, hQ₀⟩ := hQ_loc x₀ hx₀
  have hb_pos : 0 < b := lt_of_lt_of_le (by positivity : 0 < τ₀ / 4) <|
    le_csInf hBne fun t ht ↦ le_of_not_gt fun hlt ↦ ht.2 <|
      hP_ext (t := 0) hr₀ (half_pos hτ₀) hr₀U
        (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub₀ y hy))
        (hQ_mono hQ₀ (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)) (by linarith)
  have hbJ : b ∈ forwardSemiflowInterval X (U ∩ C) x₀ :=
    Icc_subset_forwardSemiflowInterval_of_mem hT ⟨hb0, hbT⟩
  obtain ⟨rz, hrz, τz, hτz, _, hsubz, hQz⟩ := hQ_loc (Φ b x₀) (forwardSemiflow_mem hbJ)
  obtain ⟨η₀, hη₀, hclose_b⟩ := Metric.continuousAt_iff.mp
    ((hX.hasDerivAt_forwardSemiflow hbJ hb_pos).continuousAt) rz hrz
  set η := min (b / 2) (min (η₀ / 2) (τz / 3))
  have hη : 0 < η := by positivity
  set s := b - η
  have hs_pos : 0 < s := by linarith [min_le_left (b / 2) (min (η₀ / 2) (τz / 3))]
  have hs_lt_b : s < b := sub_lt_self b hη
  have hΦs_mem : Φ s x₀ ∈ ball (Φ b x₀) rz := hclose_b <| by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hs_lt_b)]
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_left (η₀ / 2) (τz / 3)]
  have hPs : P s := by_contra fun hnotPs ↦
    not_lt_of_ge (csInf_le hBbdd ⟨⟨hs_pos.le, hs_lt_b.le.trans hbT⟩, hnotPs⟩) hs_lt_b
  obtain ⟨rs, hrs, δs, hδs, hrsU, hsubs, hQs⟩ := hPs
  have hΦs_cont : ContinuousOn (fun y ↦ Φ s y) (ball x₀ rs ∩ C) := (hQ_cont hQs).comp
    (continuousOn_const.prodMk continuousOn_id) fun _ hy ↦ ⟨⟨hs_pos.le, by linarith⟩, hy⟩
  obtain ⟨rc, hrc, hballc⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hΦs_cont x₀ ⟨mem_ball_self hrs, hx₀.2⟩).eventually (isOpen_ball.mem_nhds hΦs_mem))
  set r' := min rs rc
  have hΦs_ball (y : E) (hy : y ∈ ball x₀ r' ∩ C) : Φ s y ∈ ball (Φ b x₀) rz ∩ C := by
    have hy_rs : y ∈ ball x₀ rs ∩ C := ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    exact ⟨hballc ⟨ball_subset_ball (min_le_right _ _) hy.1, hy_rs⟩,
      (forwardSemiflow_mem (hsubs y hy_rs ⟨hs_pos.le, by linarith⟩)).2⟩
  have hsub_all (y : E) (hy : y ∈ ball x₀ r' ∩ C) :
      Ico 0 (s + 2 * τz) ⊆ forwardSemiflowInterval X (U ∩ C) y := fun t ht ↦ by
    have hsJ := hsubs y ⟨ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩ ⟨hs_pos.le, by linarith⟩
    rcases le_or_gt t s with hts | hst
    · exact Icc_subset_forwardSemiflowInterval_of_mem hsJ ⟨ht.1, hts⟩
    · rw [← sub_add_cancel t s]
      exact (hX.add_mem_forwardSemiflowInterval_iff hsJ (by linarith)).mpr
        (hsubz (Φ s y) (hΦs_ball y hy) ⟨by linarith, by linarith [ht.2]⟩)
  have hstep_Q : Q (Icc s (s + τz) ×ˢ (ball x₀ r' ∩ C)) :=
    hQ_shift (hQ_mono hQs
        (prod_mono Subset.rfl (inter_subset_inter_left C (ball_subset_ball (min_le_left _ _)))))
      hQz hs_pos.le hδs hΦs_ball fun p hp ↦ by
        have htJ : p.1 - s ∈ forwardSemiflowInterval X (U ∩ C) (Φ s p.2) :=
          hsubz (Φ s p.2) (hΦs_ball p.2 hp.2) ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
        simpa [Φ, uncurry, sub_add_cancel] using
          hX.forwardSemiflow_add (hsub_all p.2 hp.2 ⟨hs_pos.le, by linarith⟩) htJ
  have hglue : Q (Icc 0 (s + τz) ×ˢ (ball x₀ r' ∩ C)) := by
    set T₁ := min (s + δs) (s + τz)
    refine hQ_local fun p _ ↦ ?_
    rcases lt_or_ge p.1 T₁ with hlt | hge
    · exact ⟨Iio T₁ ×ˢ univ, isOpen_Iio.prod isOpen_univ, ⟨hlt, trivial⟩,
        hQ_mono hQs fun _ hq ↦ ⟨⟨hq.1.1.1, hq.2.1.le.trans (min_le_left _ _)⟩,
          ball_subset_ball (min_le_left _ _) hq.1.2.1, hq.1.2.2⟩⟩
    · exact ⟨Ioi s ×ˢ univ, isOpen_Ioi.prod isOpen_univ,
        ⟨(lt_min (by linarith) (by linarith)).trans_le hge, trivial⟩,
        hQ_mono hstep_Q fun _ hq ↦ ⟨⟨hq.2.1.le, hq.1.1.2⟩, hq.1.2⟩⟩
  have hbs_le : b - s ≤ τz / 3 := by
    linarith [min_le_right (b / 2) (min (η₀ / 2) (τz / 3)), min_le_right (η₀ / 2) (τz / 3)]
  have hb_contra : b + τz / 6 ≤ b := le_csInf hBne fun t ht ↦ le_of_not_gt fun hlt ↦
    ht.2 <| hP_ext (t := b) (lt_min hrs hrc) (by positivity : 0 < τz / 3)
      ((ball_subset_ball (min_le_left _ _)).trans hrsU)
      (fun y hy ↦ (Ico_subset_Ico_right (by linarith)).trans (hsub_all y hy))
      (hQ_mono hglue (prod_mono (Icc_subset_Icc_right (by linarith)) Subset.rfl)) (by linarith)
  linarith

/-- Propagation of local existence and joint continuity of `forwardSemiflow` up to any time
`T ∈ forwardSemiflowInterval X (U ∩ C) x₀`. -/
theorem Convex.exists_continuousOn_Icc_of_mem_forwardSemiflowInterval {C U : Set E}
    (hC : Convex ℝ C) (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) {x₀ : E} {T : ℝ}
    (hx₀ : x₀ ∈ U ∩ C) (hT : T ∈ forwardSemiflowInterval X (U ∩ C) x₀) :
    ∃ r > 0, ∃ δ > 0, ball x₀ r ⊆ U ∧
      (∀ y ∈ ball x₀ r ∩ C, Ico 0 (T + 2 * δ) ⊆ forwardSemiflowInterval X (U ∩ C) y) ∧
      ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (Icc 0 (T + δ) ×ˢ (ball x₀ r ∩ C)) := by
  refine hX.exists_Icc_prod_of_mem_forwardSemiflowInterval
    (fun _ _ h hsub ↦ h.mono hsub) (fun _ h ↦ h)
    (fun _ h p hp ↦ let ⟨W, hW, hpW, hfW⟩ := h p hp
      (hfW p ⟨hp, hpW⟩).mono_of_mem_nhdsWithin
        (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (hW.mem_nhds hpW))))
    (fun {s δ τ B₁ B₂} hQ₁ hQ₂ hs0 hδ hmaps hcocycle ↦ ?_) (fun x hx ↦ ?_) hx₀ hT
  · have hΦs : ContinuousOn (fun p : ℝ × E ↦ forwardSemiflow X (U ∩ C) s p.2)
        (Icc s (s + τ) ×ˢ B₁) :=
      hQ₁.comp (continuousOn_const.prodMk continuousOn_snd) fun _ hp ↦ ⟨⟨hs0, by linarith⟩, hp.2⟩
    exact (hQ₂.comp ((continuousOn_fst.sub continuousOn_const).prodMk hΦs)
      fun p hp ↦ ⟨⟨by dsimp; linarith [hp.1.1], by dsimp; linarith [hp.1.2]⟩,
        hmaps p.2 hp.2⟩).congr hcocycle
  · obtain ⟨r, hr, τ, hτ, _, _, h2rU, _, hsub, _, _, _, hcont⟩ :=
      hC.exists_local_forwardSemiflow_continuousOn hU hX hx (hX_in x hx)
    exact ⟨r, hr, τ, hτ, (ball_subset_ball (by linarith)).trans h2rU, hsub, hcont⟩

/-- **Relative openness of the maximal forward semiflow domain.** If `X` is locally Lipschitz on
`U ∩ C` and strictly inward to the convex set `C` at every point of `U ∩ C`, then
`forwardSemiflowDomain X (U ∩ C)` is open in the subspace topology of `Ici 0 ×ˢ (U ∩ C)`. -/
theorem Convex.exists_isOpen_inter_eq_forwardSemiflowDomain {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ∃ Ω : Set (ℝ × E), IsOpen Ω ∧ Ω ∩ (Ici 0 ×ˢ (U ∩ C)) = forwardSemiflowDomain X (U ∩ C) := by
  have hloc (p : forwardSemiflowDomain X (U ∩ C)) : ∃ W : Set (ℝ × E), IsOpen W ∧ p.val ∈ W ∧
      W ∩ (Ici 0 ×ˢ (U ∩ C)) ⊆ forwardSemiflowDomain X (U ∩ C) := by
    obtain ⟨hpU, hpJ⟩ := mem_forwardSemiflowDomain_iff.mp p.property
    obtain ⟨r, hr, δ, hδ, _, hsub, _⟩ :=
      hC.exists_continuousOn_Icc_of_mem_forwardSemiflowInterval hU hX hX_in hpU hpJ
    exact ⟨Iio (p.val.1 + 2 * δ) ×ˢ ball p.val.2 r, isOpen_Iio.prod isOpen_ball,
      ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩, fun q hq ↦
        mem_forwardSemiflowDomain_iff.mpr ⟨hq.2.2, hsub q.2 ⟨hq.1.2, hq.2.2.2⟩ ⟨hq.2.1, hq.1.1⟩⟩⟩
  choose W hW_open hpW hW_sub using hloc
  refine ⟨⋃ p, W p, isOpen_iUnion hW_open, Subset.antisymm (fun q hq ↦ ?_) (fun q hq ↦ ?_)⟩
  · obtain ⟨p, hqp⟩ := mem_iUnion.mp hq.1; exact hW_sub p ⟨hqp, hq.2⟩
  · obtain ⟨hqU, hqJ⟩ := mem_forwardSemiflowDomain_iff.mp hq
    exact ⟨mem_iUnion.mpr ⟨⟨q, hq⟩, hpW ⟨q, hq⟩⟩, nonneg_of_mem_forwardSemiflowInterval hqJ, hqU⟩

/-- **Joint continuity of the maximal forward semiflow.** If `X` is locally Lipschitz on `U ∩ C`
and strictly inward to the convex set `C` on `U ∩ C`, then
`uncurry (forwardSemiflow X (U ∩ C))` is continuous on `forwardSemiflowDomain X (U ∩ C)`. -/
theorem Convex.continuousOn_forwardSemiflow {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X)
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) :
    ContinuousOn (uncurry (forwardSemiflow X (U ∩ C))) (forwardSemiflowDomain X (U ∩ C)) := by
  intro p hp
  obtain ⟨hpU, hpJ⟩ := mem_forwardSemiflowDomain_iff.mp hp
  obtain ⟨r, hr, δ, hδ, _, _, hcont⟩ :=
    hC.exists_continuousOn_Icc_of_mem_forwardSemiflowInterval hU hX hX_in hpU hpJ
  exact (hcont p ⟨⟨nonneg_of_mem_forwardSemiflowInterval hpJ, by linarith⟩,
    mem_ball_self hr, hpU.2⟩).mono_of_mem_nhdsWithin <| mem_nhdsWithin.mpr
      ⟨Iio (p.1 + δ) ×ˢ ball p.2 r, isOpen_Iio.prod isOpen_ball,
        ⟨mem_Iio.mpr (by linarith), mem_ball_self hr⟩, fun _ hq ↦
          ⟨⟨nonneg_of_mem_forwardSemiflowInterval (mem_forwardSemiflowDomain_iff.mp hq.2).2,
            hq.1.1.le⟩, hq.1.2, (mem_forwardSemiflowDomain_iff.mp hq.2).1.2⟩⟩

end LocalExistenceAndContinuity

/-! ### Forward compact escape and global forward completeness -/

section EscapeAndGlobal

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **No cluster point with uniform local restart.** If `X` is locally Lipschitz on `S`,
`forwardSemiflowInterval X S x` is nonempty with least upper bound `b`, and every point of `S`
near `z` admits a uniform positive forward existence time `τ > 0`, then
`forwardSemiflow X S · x` cannot accumulate at `z` as `t → b⁻`. -/
theorem LocallyLipschitzOn.not_mapClusterPt_nhdsLT_forwardSemiflow {S : Set E} {X : E → E}
    (hX : LocallyLipschitzOn S X) {x z : E} {b : ℝ}
    (hne : (forwardSemiflowInterval X S x).Nonempty)
    (hb : IsLUB (forwardSemiflowInterval X S x) b)
    (hrest : ∃ V ∈ 𝓝 z, ∃ τ > 0, ∀ y ∈ V ∩ S, τ ∈ forwardSemiflowInterval X S y) :
    ¬ MapClusterPt z (𝓝[<] b) (fun t ↦ forwardSemiflow X S t x) := by
  intro hcl
  obtain ⟨t₀, ht₀⟩ := hne
  have h0 : (0 : ℝ) ∈ forwardSemiflowInterval X S x :=
    Icc_subset_forwardSemiflowInterval_of_mem ht₀
      ⟨le_rfl, nonneg_of_mem_forwardSemiflowInterval ht₀⟩
  have hb_pos := pos_of_isLUB_forwardSemiflowInterval h0 hb
  obtain ⟨V, hV, τ, hτ, hsub⟩ := hrest
  obtain ⟨s, hs_V, hs_Ioo⟩ := ((hcl.frequently hV).and_eventually
    (Ioo_mem_nhdsLT (max_lt hb_pos (sub_lt_self b hτ)))).exists
  have hsJ : s ∈ forwardSemiflowInterval X S x :=
    hb.forwardSemiflowInterval_eq_Ico ▸ ⟨(le_max_left 0 (b - τ)).trans hs_Ioo.1.le, hs_Ioo.2⟩
  have huJ : τ ∈ forwardSemiflowInterval X S (forwardSemiflow X S s x) :=
    hsub _ ⟨hs_V, forwardSemiflow_mem hsJ⟩
  linarith [hb.1 ((hX.add_mem_forwardSemiflowInterval_iff hsJ hτ.le).mpr huJ),
    (le_max_right 0 (b - τ)).trans_lt hs_Ioo.1]

variable [CompleteSpace E]

/-- **Forward compact-escape lemma.** At a finite least upper bound `b` of
`forwardSemiflowInterval X (U ∩ C) x`, if `X` is strictly inward to `C` on a compact subset
`K ⊆ U ∩ C`, then the trajectory leaves `K` as `t → b⁻`. -/
theorem Convex.eventually_notMem_nhdsLT_forwardSemiflow {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X) {x : E} {b : ℝ}
    (h0 : (0 : ℝ) ∈ forwardSemiflowInterval X (U ∩ C) x)
    (hb : IsLUB (forwardSemiflowInterval X (U ∩ C) x) b) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U ∩ C) (hX_in : ∀ y ∈ K, X y ∈ strictInwardCone C y) :
    ∀ᶠ t in 𝓝[<] b, forwardSemiflow X (U ∩ C) t x ∉ K := by
  by_contra h
  obtain ⟨z, hzK, hz⟩ := hK.exists_mapClusterPt_of_frequently (by simpa [not_eventually] using h)
  obtain ⟨r, hr, τ, hτ, _, _, _, _, hsub, -⟩ :=
    hC.exists_local_forwardSemiflow_continuousOn hU hX (hKU hzK) (hX_in z hzK)
  exact hX.not_mapClusterPt_nhdsLT_forwardSemiflow ⟨0, h0⟩ hb
    ⟨ball z r, Metric.ball_mem_nhds z hr, τ, hτ, fun y hy ↦
      hsub y ⟨hy.1, hy.2.2⟩ ⟨hτ.le, by linarith⟩⟩ hz

/-- **Global forward existence under compact trapping.** If a trajectory of `forwardSemiflow` stays
inside a compact subset `K ⊆ U ∩ C` on which `X` is strictly inward to `C`, then it is defined on
all of `[0, ∞)`. -/
theorem Convex.forwardSemiflowInterval_eq_Ici_of_isCompact_of_mapsTo {C U : Set E}
    (hC : Convex ℝ C) (hU : IsOpen U) {X : E → E} (hX : LocallyLipschitzOn (U ∩ C) X) {x : E}
    (h0 : (0 : ℝ) ∈ forwardSemiflowInterval X (U ∩ C) x) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ U ∩ C) (hX_in : ∀ y ∈ K, X y ∈ strictInwardCone C y)
    (hmem : MapsTo (fun t ↦ forwardSemiflow X (U ∩ C) t x)
      (forwardSemiflowInterval X (U ∩ C) x) K) :
    forwardSemiflowInterval X (U ∩ C) x = Ici 0 := by
  refine forwardSemiflowInterval_eq_Ici_of_not_bddAbove fun hbdd ↦ ?_
  have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
  obtain ⟨t, ht, htK⟩ := ((eventually_mem_set.mpr
    (Ioo_mem_nhdsLT (pos_of_isLUB_forwardSemiflowInterval h0 hlub))).and
      (hC.eventually_notMem_nhdsLT_forwardSemiflow hU hX h0 hlub hK hKU hX_in)).exists
  exact htK (hmem (hlub.forwardSemiflowInterval_eq_Ico ▸ ⟨ht.1.le, ht.2⟩))

/-- **Global forward completeness on a compact convex set.** Every locally Lipschitz strictly inward
vector field on a compact convex set `C` generates a forward semiflow defined for all `t ≥ 0`. -/
theorem Convex.forwardSemiflowInterval_eq_Ici_of_isCompact {C : Set E} (hC : Convex ℝ C)
    (hC_compact : IsCompact C) {X : E → E} (hX : LocallyLipschitzOn C X)
    (hX_in : ∀ y ∈ C, X y ∈ strictInwardCone C y) {x : E} (hx : x ∈ C) :
    forwardSemiflowInterval X C x = Ici 0 := by
  have hX' : LocallyLipschitzOn (univ ∩ C) X := by simpa only [univ_inter] using hX
  have h0 : (0 : ℝ) ∈ forwardSemiflowInterval X (univ ∩ C) x :=
    hC.zero_mem_forwardSemiflowInterval isOpen_univ hX' ⟨trivial, hx⟩ (hX_in x hx)
  simpa only [univ_inter] using hC.forwardSemiflowInterval_eq_Ici_of_isCompact_of_mapsTo
    isOpen_univ hX' h0 hC_compact (fun y hy ↦ ⟨trivial, hy⟩) hX_in
    fun _ ht ↦ (forwardSemiflow_mem ht).2

/-- **Global forward completeness via a proper Lyapunov / exhaustion function.** If `C` is convex,
`f : E → ℝ` is continuous on `C` with compact sublevel sets `{y ∈ C | f y ≤ R}`, and `f` is
differentiable on `interior C` with `df y (X y) ≤ c`, then every forward trajectory of a locally
Lipschitz strictly inward field `X` on `C` is defined on all of `[0, ∞)`. -/
theorem Convex.forwardSemiflowInterval_eq_Ici_of_isCompact_sublevel {C : Set E} (hC : Convex ℝ C)
    {X : E → E} (hX : LocallyLipschitzOn C X) (hX_in : ∀ y ∈ C, X y ∈ strictInwardCone C y)
    {f : E → ℝ} {df : E → E →L[ℝ] ℝ} {c : ℝ} (hf_cont : ContinuousOn f C)
    (hf_deriv : ∀ y ∈ interior C, HasFDerivAt f (df y) y) (hf_le : ∀ y ∈ interior C, df y (X y) ≤ c)
    (hf_compact : ∀ R : ℝ, IsCompact {y ∈ C | f y ≤ R}) {x : E} (hx : x ∈ C) :
    forwardSemiflowInterval X C x = Ici 0 := by
  refine forwardSemiflowInterval_eq_Ici_of_not_bddAbove fun hbdd ↦ ?_
  have hX' : LocallyLipschitzOn (univ ∩ C) X := by simpa only [univ_inter] using hX
  have h0 : (0 : ℝ) ∈ forwardSemiflowInterval X C x := by
    simpa only [univ_inter] using
      hC.zero_mem_forwardSemiflowInterval isOpen_univ hX' ⟨trivial, hx⟩ (hX_in x hx)
  set b := sSup (forwardSemiflowInterval X C x)
  have hlub : IsLUB (forwardSemiflowInterval X C x) b := isLUB_csSup ⟨0, h0⟩ hbdd
  set c' := max c 0; set R := f x + c' * b
  have htrap (T : ℝ) (hT : T ∈ Ioo 0 b) : forwardSemiflow X C T x ∈ {y ∈ C | f y ≤ R} := by
    have hTJ : T ∈ forwardSemiflowInterval X C x :=
      hlub.forwardSemiflowInterval_eq_Ico ▸ ⟨hT.1.le, hT.2⟩
    refine ⟨forwardSemiflow_mem hTJ, ?_⟩
    have hsubT := Icc_subset_forwardSemiflowInterval_of_mem hTJ
    have hint (s : ℝ) (hs : s ∈ interior (Icc 0 T)) :
        0 < s ∧ s ∈ forwardSemiflowInterval X C x ∧ forwardSemiflow X C s x ∈ interior C := by
      rw [interior_Icc] at hs
      exact ⟨hs.1, hsubT (Ioo_subset_Icc_self hs),
        hC.forwardSemiflow_mem_interior Subset.rfl hX_in (hsubT (Ioo_subset_Icc_self hs)) hs.1⟩
    have hle0T := (antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun s ↦ df (forwardSemiflow X C s x) (X (forwardSemiflow X C s x)) - c')
      (convex_Icc 0 T) ((hf_cont.comp (fun s hs ↦ ((hX.hasDerivWithinAt_forwardSemiflow
        (hsubT hs)).continuousWithinAt).mono hsubT) fun _ hs ↦ forwardSemiflow_mem (hsubT hs)).sub
        (continuousOn_const.mul continuousOn_id))
      (fun s hs ↦ (((hf_deriv _ (hint s hs).2.2).comp_hasDerivAt s
        (hX.hasDerivAt_forwardSemiflow (hint s hs).2.1 (hint s hs).1)).sub
          ((hasDerivAt_id' s).const_mul c') |>.congr_deriv (by ring)).hasDerivWithinAt)
      (fun s hs ↦ by linarith [hf_le _ (hint s hs).2.2, le_max_left c 0]))
      ⟨le_rfl, hT.1.le⟩ ⟨hT.1.le, le_rfl⟩ hT.1.le
    simp only [Pi.sub_apply, Pi.mul_apply, Function.comp_apply, id_eq, forwardSemiflow_zero,
      mul_zero, sub_zero] at hle0T
    linarith [mul_le_mul_of_nonneg_left hT.2.le (le_max_right c 0)]
  have hesc : ∀ᶠ t in 𝓝[<] b, forwardSemiflow X C t x ∉ {y ∈ C | f y ≤ R} := by
    simpa only [univ_inter] using hC.eventually_notMem_nhdsLT_forwardSemiflow isOpen_univ hX'
      (by simpa only [univ_inter] using h0) (by simpa only [univ_inter] using hlub)
      (hf_compact R) (fun y hy ↦ ⟨trivial, hy.1⟩) (fun y hy ↦ hX_in y hy.1)
  obtain ⟨t, ht, htK⟩ := ((eventually_mem_set.mpr
    (Ioo_mem_nhdsLT (pos_of_isLUB_forwardSemiflowInterval h0 hlub))).and hesc).exists
  exact htK (htrap t ht)

end EscapeAndGlobal
