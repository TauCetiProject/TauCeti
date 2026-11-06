/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.Cutoff

/-!
# Peetre's theorem: local operators have locally finite order

Let `E` be a finite-dimensional real normed space and `P` a linear map from the smooth functions
`E → F` to functions `E → G`. Suppose that on an open set `U` the operator `P` is *local*, that is
`(P u) x = 0` whenever `u` vanishes on a neighbourhood of `x ∈ U`, and that every `P u` is
continuous on `U`. No continuity of `P` itself is assumed. Peetre's theorem says that `P` then has
locally finite order: for every compact `K ⊆ U` there is `r` such that `(P u) x = (P v) x`
whenever `x ∈ K` and `u`, `v` have the same derivatives of order at most `r` at `x`
(`LinearMap.exists_apply_eq_apply_of_iteratedFDeriv_eq`). The order need not be bounded on all
of `U`: an operator `∑ₖ φₖ • u⁽ᵏ⁾` with smooth bumps `φₖ` supported near the integers `k` has
order `k` near `k`.

The proof has three steps.

* `LinearMap.exists_norm_apply_le_of_tsupport_subset`: near each `x₀ ∈ U` there are a radius `ρ`,
  an order `r` and a constant `C` with `‖(P φ) y‖ ≤ C * M` for every smooth `φ` supported in the
  punctured ball `ball x₀ ρ \ {x₀}` whose derivatives of order at most `r` are bounded by `M`.
  Otherwise there are functions `ψₖ` supported in disjoint annuli shrinking to `x₀`, with
  derivatives of order at most `k` bounded by `2⁻ᵏ` and `‖(P ψₖ) yₖ‖ > 2ᵏ`. Their sum `ψ` is smooth
  and agrees with `ψₖ` near `yₖ`, so locality gives `‖(P ψ) yₖ‖ > 2ᵏ` while `yₖ → x₀`, contradicting
  the continuity of `P ψ` at `x₀`.
* `LinearMap.exists_forall_mem_ball_apply_eq_zero`: if the derivatives of `u` of order at most `r`
  vanish at `y`, then `(P u) y` is unchanged by cutting `u` off to `closedBall y ε`, and these
  cut-offs are `O(ε)` in `C^r` (`TauCeti.exists_norm_iteratedFDeriv_smul_le_mul`). By the first
  step `(P u) y = 0` at every `y ≠ x₀` of the ball. At the centre `x₀` the same bound holds at
  nearby points `y ≠ x₀`, and continuity at `x₀` gives `(P u) x₀ = 0`.
* A finite cover of `K` by such balls gives the uniform order
  (`LinearMap.exists_apply_eq_zero_of_iteratedFDeriv_eq_zero`).

For operators between sections of vector bundles the hypotheses and the conclusion are local, so
in charts and trivializations they reduce to this Euclidean form.

## Main declarations

* `LinearMap.exists_apply_eq_zero_of_iteratedFDeriv_eq_zero`,
  `LinearMap.exists_apply_eq_apply_of_iteratedFDeriv_eq`: **Peetre's theorem**.
* `LinearMap.exists_forall_mem_ball_apply_eq_zero`: its local form near a point.
* `LinearMap.exists_norm_apply_le_of_tsupport_subset`: the estimate on punctured balls.

## References

* J. Peetre, *Réctification à l'article « Une caractérisation abstraite des opérateurs
  différentiels »*, Math. Scand. 8 (1960), 116–120.
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Theorem 19.1.
* R. Narasimhan, *Analysis on Real and Complex Manifolds*, Theorem 3.3.3.
-/

public section

open Set Filter Metric Function
open scoped ContDiff Manifold Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

namespace LinearMap

variable {U : Set E}

/-! ### The estimate on punctured balls -/

/-- If the estimate fails on `ball x₀ ρ \ {x₀}`, then for every `k` there is a smooth `ψ` of size
`2⁻ᵏ` in `C^k`, supported in an annulus `ball x₀ ρ \ closedBall x₀ ρ'`, with `‖(P ψ) y‖ > 2ᵏ` at a
point `y ∈ U` of that annulus. -/
private theorem exists_tsupport_subset_annulus (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    {x₀ : E} {ρ : ℝ} (hρ : 0 < ρ)
    (H : ∀ (r : ℕ) (C : ℝ), ∃ φ : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯,
      tsupport (φ : E → F) ⊆ ball x₀ ρ \ {x₀} ∧ ∃ M : ℝ,
        (∀ i ≤ r, ∀ z, ‖iteratedFDeriv ℝ i φ z‖ ≤ M) ∧ ∃ y ∈ U, C * M < ‖P φ y‖)
    (k : ℕ) :
    ∃ ψ : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ / 2 ∧
      tsupport (ψ : E → F) ⊆ ball x₀ ρ \ closedBall x₀ ρ' ∧
      (∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i ψ z‖ ≤ 2⁻¹ ^ k) ∧
      ∃ y ∈ ball x₀ ρ \ closedBall x₀ ρ', y ∈ U ∧ 2 ^ k < ‖P ψ y‖ := by
  obtain ⟨φ, hφs, M, hM, y, hyU, hy⟩ := H k (4 ^ k)
  have hM0 : 0 < M := by
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (by simpa using hM 0 (Nat.zero_le k) x₀)
    refine hM0.lt_of_ne fun hM0 ↦ ?_
    have hφ : φ = 0 := ContMDiffMap.ext fun z ↦ by
      simpa [← hM0] using hM 0 (Nat.zero_le k) z
    simp [hφ, ← hM0] at hy
  -- Rescale `φ` by `c = (2ᵏ M)⁻¹`.
  set c : ℝ := (2 ^ k * M)⁻¹
  have hc0 : 0 < c := by positivity
  set ψ := c • φ
  have hψs : tsupport (ψ : E → F) ⊆ tsupport (φ : E → F) := by
    rw [ContMDiffMap.coe_smul]
    exact tsupport_smul_subset_right (fun _ ↦ c) φ
  have hx₀ψ : x₀ ∉ tsupport (ψ : E → F) := fun h ↦ (hφs (hψs h)).2 rfl
  obtain ⟨ε, hε, hεψ⟩ :=
    Metric.mem_nhds_iff.mp ((isClosed_tsupport _).isOpen_compl.mem_nhds hx₀ψ)
  have hsub : tsupport (ψ : E → F) ⊆ ball x₀ ρ \ closedBall x₀ (min (ρ / 2) (ε / 2)) := by
    intro z hz
    refine ⟨(hφs (hψs hz)).1, fun hz' ↦ hεψ ?_ hz⟩
    exact closedBall_subset_ball (by linarith [min_le_right (ρ / 2) (ε / 2)]) hz'
  have hyψ : 2 ^ k < ‖P ψ y‖ := by
    rw [map_smul, Pi.smul_apply, norm_smul, Real.norm_of_nonneg hc0.le]
    have hcM : c * (2 ^ k * M) = 1 := inv_mul_cancel₀ (by positivity)
    calc (2 : ℝ) ^ k = c * (2 ^ k * M) * 2 ^ k := by rw [hcM, one_mul]
      _ = c * (4 ^ k * M) := by
          rw [show (4 : ℝ) ^ k = 2 ^ k * 2 ^ k by rw [← mul_pow]; norm_num]
          ring
      _ < c * ‖P φ y‖ := by gcongr
  refine ⟨ψ, min (ρ / 2) (ε / 2), by positivity, min_le_left _ _, hsub, fun i hi z ↦ ?_,
    y, hsub ?_, hyU, hyψ⟩
  · rw [ContMDiffMap.coe_smul, iteratedFDeriv_const_smul_apply
      (φ.contMDiff.contDiff.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
      Real.norm_of_nonneg hc0.le]
    calc c * ‖iteratedFDeriv ℝ i φ z‖ ≤ c * M := by gcongr; exact hM i hi z
      _ = 2⁻¹ ^ k := by
          rw [show c = (2 ^ k)⁻¹ * M⁻¹ from mul_inv _ _, mul_assoc, inv_mul_cancel₀ hM0.ne',
            mul_one, inv_pow]
  · -- `y` lies in the support of `ψ`, since otherwise locality would give `(P ψ) y = 0`.
    by_contra hyn
    rw [hloc ψ y hyU (notMem_tsupport_iff_eventuallyEq.mp hyn), norm_zero] at hyψ
    exact (pow_pos two_pos k).not_gt hyψ

/-- Smooth functions `Ψ k` supported in pairwise disjoint open sets `A k ⊆ U`, of size `2⁻ᵏ` in
`C^k`, cannot satisfy `‖(P (Ψ k)) (Y k)‖ > 2ᵏ` at points `Y k ∈ A k` converging to `x₀ ∈ U`:
their sum `Ψs` is smooth and agrees with `Ψ k` near `Y k`, so `P Ψs` would be unbounded near
`x₀`. -/
private theorem false_of_tendsto [CompleteSpace F]
    (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G) (hU : IsOpen U)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    (hcont : ∀ u, ContinuousOn (P u) U) {x₀ : E} (hx₀ : x₀ ∈ U) {A : ℕ → Set E}
    (hA : ∀ k, IsOpen (A k)) (hAU : ∀ k, A k ⊆ U) (hdisj : Pairwise (Disjoint on A))
    {Ψ : ℕ → C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯} (hΨs : ∀ k, tsupport (Ψ k : E → F) ⊆ A k)
    (hΨb : ∀ k, ∀ i ≤ k, ∀ z, ‖iteratedFDeriv ℝ i (Ψ k) z‖ ≤ 2⁻¹ ^ k) {Y : ℕ → E}
    (hYA : ∀ k, Y k ∈ A k) (hY : Tendsto Y atTop (𝓝 x₀))
    (hPY : ∀ k, 2 ^ k < ‖P (Ψ k) (Y k)‖) : False := by
  have hsmooth : ContDiff ℝ ∞ fun z ↦ ∑' k, Ψ k z := by
    refine contDiff_tsum_of_eventually (N := ⊤) (v := fun _ k ↦ 2⁻¹ ^ k)
      (fun k ↦ (Ψ k).contMDiff.contDiff)
      (fun _ _ ↦ summable_geometric_of_lt_one (by norm_num) (by norm_num)) fun i _ ↦ ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop i] with k hik
    exact hΨb k i hik
  let Ψs : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ := ⟨fun z ↦ ∑' k, Ψ k z, hsmooth.contMDiff⟩
  -- Near `Y k` the sum agrees with `Ψ k`, so locality gives `‖(P Ψs) (Y k)‖ > 2ᵏ`.
  have hPY' : ∀ k, 2 ^ k < ‖P Ψs (Y k)‖ := by
    intro k
    have hloc' : ((Ψs - Ψ k : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) : E → F) =ᶠ[𝓝 (Y k)] 0 := by
      filter_upwards [(hA k).mem_nhds (hYA k)] with z hz
      rw [ContMDiffMap.coe_sub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
      exact tsum_eq_single k fun j hj ↦ image_eq_zero_of_notMem_tsupport fun hz' ↦
        Set.disjoint_left.1 (hdisj hj) (hΨs j hz') hz
    have h := hloc _ (Y k) (hAU k (hYA k)) hloc'
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h
    rw [h]
    exact hPY k
  -- But `P Ψs` is continuous at `x₀`, so it is bounded near `x₀`.
  have hcontx : Tendsto (fun k ↦ ‖P Ψs (Y k)‖) atTop (𝓝 ‖P Ψs x₀‖) :=
    (((hcont Ψs).continuousAt (hU.mem_nhds hx₀)).tendsto.comp hY).norm
  obtain ⟨k, hk₁, hk₂⟩ :=
    ((hcontx.eventually (gt_mem_nhds (lt_add_one ‖P Ψs x₀‖))).and
      ((tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_gt_atTop
        (‖P Ψs x₀‖ + 1))).exists
  linarith [hPY' k]

/-- **Peetre's estimate** on punctured balls. Let `P` be local on the open set `U` with `P u`
continuous on `U` for every `u`. Then near each `x₀ ∈ U` there are `ρ > 0`, an order `r` and a
constant `C` such that `‖(P φ) y‖ ≤ C * M` at every `y ∈ U`, for every smooth `φ` supported in
`ball x₀ ρ \ {x₀}` whose derivatives of order at most `r` are bounded by `M`. -/
theorem exists_norm_apply_le_of_tsupport_subset [CompleteSpace F]
    (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G) (hU : IsOpen U)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    (hcont : ∀ u, ContinuousOn (P u) U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧ ∃ (r : ℕ) (C : ℝ), ∀ φ : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯,
      tsupport (φ : E → F) ⊆ ball x₀ ρ \ {x₀} → ∀ M : ℝ,
        (∀ i ≤ r, ∀ z, ‖iteratedFDeriv ℝ i φ z‖ ≤ M) → ∀ y ∈ U, ‖P φ y‖ ≤ C * M := by
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.isOpen_iff.mp hU x₀ hx₀
  by_contra! H
  choose! ψ ρ' hρ'0 hρ'le hψs hψb y hy hyU hyP using fun ρ (hρ : 0 < ρ) (hρρ₀ : ρ ≤ ρ₀) ↦
    exists_tsupport_subset_annulus P hloc hρ (H ρ hρ ((ball_subset_ball hρρ₀).trans hρ₀U))
  -- The radii `s k ≤ ρ₀ / 2ᵏ` of nested annuli, with a counterexample `ψ (s k) k` in the `k`-th.
  let s : ℕ → ℝ := fun k ↦ Nat.rec ρ₀ (fun k ρ ↦ ρ' ρ k) k
  have hs_succ : ∀ k, s (k + 1) = ρ' (s k) k := fun k ↦ rfl
  have hs : ∀ k, 0 < s k ∧ s k ≤ ρ₀ / 2 ^ k := by
    intro k
    induction k with
    | zero => exact ⟨hρ₀, by simp [s]⟩
    | succ k ih =>
      have hle : s k ≤ ρ₀ := ih.2.trans (div_le_self hρ₀.le (one_le_pow₀ one_le_two))
      rw [hs_succ]
      refine ⟨hρ'0 _ ih.1 hle k, (hρ'le _ ih.1 hle k).trans ?_⟩
      rw [pow_succ, ← div_div]
      gcongr
      exact ih.2
  have hs0 : ∀ k, 0 < s k := fun k ↦ (hs k).1
  have hsρ₀ : ∀ k, s k ≤ ρ₀ := fun k ↦
    (hs k).2.trans (div_le_self hρ₀.le (one_le_pow₀ one_le_two))
  have hanti : Antitone s := antitone_nat_of_succ_le fun k ↦ by
    rw [hs_succ]
    linarith [hρ'le _ (hs0 k) (hsρ₀ k) k, hs0 k]
  -- The annuli are pairwise disjoint.
  have hdisj : Pairwise (Disjoint on fun k ↦ ball x₀ (s k) \ closedBall x₀ (s (k + 1))) := by
    have hlt : ∀ j k, j < k → Disjoint (ball x₀ (s j) \ closedBall x₀ (s (j + 1)))
        (ball x₀ (s k) \ closedBall x₀ (s (k + 1))) := fun j k hjk ↦
      Set.disjoint_left.2 fun z hzj hzk ↦ hzj.2 <|
        ball_subset_closedBall (ball_subset_ball (hanti (Nat.succ_le_of_lt hjk)) hzk.1)
    intro j k hjk
    rcases lt_or_gt_of_ne hjk with h | h
    exacts [hlt j k h, (hlt k j h).symm]
  -- The points `y (s k) k` converge to `x₀`.
  have hY : Tendsto (fun k ↦ y (s k) k) atTop (𝓝 x₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Tendsto (fun k : ℕ ↦ ρ₀ / 2 ^ k) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv, inv_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num)).const_mul ρ₀
    refine squeeze_zero (fun k ↦ dist_nonneg) (fun k ↦ ?_) hlim
    exact (mem_ball.mp (hy _ (hs0 k) (hsρ₀ k) k).1).le.trans (hs k).2
  exact false_of_tendsto P hU hloc hcont hx₀ (fun k ↦ isOpen_ball.sdiff isClosed_closedBall)
    (fun k ↦ sdiff_subset.trans ((ball_subset_ball (hsρ₀ k)).trans hρ₀U)) hdisj
    (fun k ↦ hψs _ (hs0 k) (hsρ₀ k) k) (fun k ↦ hψb _ (hs0 k) (hsρ₀ k) k)
    (fun k ↦ hy _ (hs0 k) (hsρ₀ k) k) hY (fun k ↦ hyP _ (hs0 k) (hsρ₀ k) k)

/-! ### Cut-offs and the local order -/

section Cutoff

variable [FiniteDimensional ℝ E]

/-- A smooth bump equal to `1` on the closed ball of radius `1 / 2` and supported in the closed unit
ball. -/
private noncomputable def unitBump : ContDiffBump (0 : E) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem unitBump_rIn : (unitBump : ContDiffBump (0 : E)).rIn = 1 / 2 := rfl

/-- The smooth function `z ↦ χ (ε⁻¹ • (z - y)) • u z` localizing `u` to `closedBall y ε`, for the
bump `χ = unitBump`. -/
private noncomputable def cutoff (y : E) (ε : ℝ) (u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :
    C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ :=
  ⟨fun z ↦ (unitBump : ContDiffBump (0 : E)) (ε⁻¹ • (z - y)) • u z,
    ((unitBump.contDiff.comp (by fun_prop)).smul u.contMDiff.contDiff).contMDiff⟩

private theorem coe_cutoff (y : E) (ε : ℝ) (u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :
    (cutoff y ε u : E → F) = fun z ↦ (unitBump : ContDiffBump (0 : E)) (ε⁻¹ • (z - y)) • u z :=
  rfl

private theorem tsupport_cutoff_subset_closedBall {y : E} {ε : ℝ} (hε : 0 < ε)
    (u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) : tsupport (cutoff y ε u : E → F) ⊆ closedBall y ε := by
  rw [coe_cutoff]
  exact (tsupport_smul_subset_left _ _).trans
    (TauCeti.tsupport_comp_inv_smul_sub_subset_closedBall unitBump.tsupport_eq.subset hε y)

private theorem tsupport_cutoff_subset (y : E) (ε : ℝ) (u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :
    tsupport (cutoff y ε u : E → F) ⊆ tsupport (u : E → F) := by
  rw [coe_cutoff]
  exact tsupport_smul_subset_right _ _

private theorem cutoff_eventuallyEq {y : E} {ε : ℝ} (hε : 0 < ε)
    (u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) : (cutoff y ε u : E → F) =ᶠ[𝓝 y] u := by
  filter_upwards [ball_mem_nhds y (half_pos hε)] with z hz
  rw [coe_cutoff]
  dsimp only
  rw [unitBump.one_of_mem_closedBall, one_smul]
  rw [mem_ball, dist_eq_norm] at hz
  rw [unitBump_rIn, mem_closedBall, dist_zero_right, norm_smul, norm_inv,
    Real.norm_of_nonneg hε.le, inv_mul_le_iff₀ hε]
  linarith

/-- Letting `δ → 0⁺`: if `a ≤ c * δ` for every `δ ∈ Ioc 0 δ₀`, then `a ≤ 0`. -/
private theorem le_zero_of_forall_mem_Ioc_le_mul {a c δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (h : ∀ δ ∈ Ioc 0 δ₀, a ≤ c * δ) : a ≤ 0 :=
  ge_of_tendsto (((continuous_const_mul c).tendsto' 0 0 (mul_zero _)).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))) (eventually_of_mem (Ioc_mem_nhdsGT hδ₀) h)

/-- The cut-offs of a function that is flat to order `r` at `y` are `O(ε)` in `C^r`. -/
private theorem exists_norm_iteratedFDeriv_cutoff_le {u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯} {y : E}
    {r : ℕ} (hflat : ∀ i ≤ r, iteratedFDeriv ℝ i u y = 0) :
    ∃ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ i ≤ r, ∀ z,
      ‖iteratedFDeriv ℝ i (cutoff y ε u) z‖ ≤ K * ε :=
  TauCeti.exists_norm_iteratedFDeriv_smul_le_mul unitBump.contDiff unitBump.tsupport_eq.subset
    (u.contMDiff.contDiff.of_le (by exact_mod_cast le_top)) hflat

/-- Localizing `u` at `y ∈ U` does not change `(P u) y`. -/
private theorem apply_cutoff (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    {y : E} (hy : y ∈ U) {ε : ℝ} (hε : 0 < ε) (u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯) :
    P (cutoff y ε u) y = P u y := by
  have h := hloc (u - cutoff y ε u) y hy (by
    filter_upwards [cutoff_eventuallyEq hε u] with z hz
    rw [ContMDiffMap.coe_sub, Pi.sub_apply, hz, sub_self, Pi.zero_apply])
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h
  exact h.symm

/-- Given the estimate of `LinearMap.exists_norm_apply_le_of_tsupport_subset` on
`ball x₀ ρ \ {x₀}`, it also holds at the points `y' ≠ x₀` of the ball for functions `w` supported in
`ball x₀ ρ` that are flat to order `r` at `x₀`: cutting `w` off near `x₀` costs arbitrarily little
in `C^r`. -/
private theorem norm_apply_le_of_iteratedFDeriv_eq_zero
    (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    {x₀ : E} {ρ : ℝ} (hρU : ball x₀ ρ ⊆ U) {r : ℕ} {C : ℝ}
    (hC : ∀ φ : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, tsupport (φ : E → F) ⊆ ball x₀ ρ \ {x₀} →
      ∀ M : ℝ, (∀ i ≤ r, ∀ z, ‖iteratedFDeriv ℝ i φ z‖ ≤ M) → ∀ y ∈ U, ‖P φ y‖ ≤ C * M)
    {w : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯} {M : ℝ} (hws : tsupport (w : E → F) ⊆ ball x₀ ρ)
    (hwflat : ∀ i ≤ r, iteratedFDeriv ℝ i w x₀ = 0)
    (hwM : ∀ i ≤ r, ∀ z, ‖iteratedFDeriv ℝ i w z‖ ≤ M) {y' : E} (hy' : y' ∈ ball x₀ ρ)
    (hne : y' ≠ x₀) : ‖P w y'‖ ≤ C * M := by
  obtain ⟨Kw, hKw⟩ := exists_norm_iteratedFDeriv_cutoff_le hwflat
  have hd : 0 < dist y' x₀ := dist_pos.mpr hne
  suffices ‖P w y'‖ - C * M ≤ 0 by linarith
  -- Let `δ → 0⁺` in `‖P w y'‖ - C * M ≤ C * Kw * δ`.
  refine le_zero_of_forall_mem_Ioc_le_mul (c := C * Kw)
    (show (0 : ℝ) < min 1 (dist y' x₀ / 2) by positivity) fun δ ⟨hδ, hδle⟩ ↦ ?_
  have hδ1 : δ ≤ 1 := hδle.trans (min_le_left _ _)
  have hδd : δ < dist y' x₀ := by linarith [min_le_right 1 (dist y' x₀ / 2)]
  set v := w - cutoff x₀ δ w
  -- Removing the cut-off near `x₀` does not change the value at `y'`.
  have hPv : P v y' = P w y' := by
    have h := hloc (cutoff x₀ δ w) y' (hρU hy') (notMem_tsupport_iff_eventuallyEq.mp
      fun h ↦ (mem_closedBall.mp (tsupport_cutoff_subset_closedBall hδ w h)).not_gt hδd)
    rw [map_sub, Pi.sub_apply, h, sub_zero]
  have hvs : tsupport (v : E → F) ⊆ ball x₀ ρ \ {x₀} := by
    intro z hz
    refine ⟨?_, fun hzx ↦ ?_⟩
    · rw [ContMDiffMap.coe_sub] at hz
      rcases tsupport_sub _ _ hz with hz | hz
      exacts [hws hz, hws (tsupport_cutoff_subset x₀ δ w hz)]
    · rw [mem_singleton_iff] at hzx
      subst hzx
      refine notMem_tsupport_iff_eventuallyEq.mpr ?_ hz
      filter_upwards [cutoff_eventuallyEq hδ w] with z hz
      rw [ContMDiffMap.coe_sub, Pi.sub_apply, hz, sub_self, Pi.zero_apply]
  have hvM : ∀ i ≤ r, ∀ z, ‖iteratedFDeriv ℝ i v z‖ ≤ M + Kw * δ := by
    intro i hi z
    rw [ContMDiffMap.coe_sub, iteratedFDeriv_sub_apply
      (w.contMDiff.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
      ((cutoff x₀ δ w).contMDiff.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))]
    exact (norm_sub_le _ _).trans (add_le_add (hwM i hi z) (hKw δ hδ hδ1 i hi z))
  have := hC v hvs (M + Kw * δ) hvM y' (hρU hy')
  rw [hPv] at this
  linarith

variable [CompleteSpace F]

/-- **Peetre's theorem**, local form. Let `P` be local on the open set `U` with `P u` continuous on
`U` for every `u`. Then each `x₀ ∈ U` has a ball `ball x₀ ρ ⊆ U` and an order `r` such that
`(P u) y = 0` for every `y` in the ball and every smooth `u` whose derivatives of order at most `r`
vanish at `y`. -/
theorem exists_forall_mem_ball_apply_eq_zero (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G)
    (hU : IsOpen U)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    (hcont : ∀ u, ContinuousOn (P u) U) {x₀ : E} (hx₀ : x₀ ∈ U) :
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧ ∃ r : ℕ, ∀ y ∈ ball x₀ ρ, ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯,
      (∀ i ≤ r, iteratedFDeriv ℝ i u y = 0) → P u y = 0 := by
  obtain ⟨ρ, hρ, hρU, r, C, hC⟩ := exists_norm_apply_le_of_tsupport_subset P hU hloc hcont hx₀
  refine ⟨ρ, hρ, hρU, r, fun y hy u hflat ↦ ?_⟩
  obtain ⟨K, hK⟩ := exists_norm_iteratedFDeriv_cutoff_le hflat
  rcases eq_or_ne y x₀ with rfl | hne
  · -- At the centre, bound `P` of the cut-offs at nearby points and use continuity.
    -- A trivial `E` forces `u = 0`; otherwise `(𝓝[≠] y).NeBot`, needed for `le_of_tendsto` below.
    rcases subsingleton_or_nontrivial E with hE | hE
    · have h0 : u y = 0 := by
        simpa [norm_iteratedFDeriv_zero] using congrArg norm (hflat 0 (Nat.zero_le r))
      have hu : u = 0 := ContMDiffMap.ext fun z ↦ by simpa [Subsingleton.elim z y] using h0
      simp [hu]
    -- Let `ε → 0⁺` in `‖(P u) y‖ ≤ C * K * ε`.
    refine norm_le_zero_iff.mp (le_zero_of_forall_mem_Ioc_le_mul (c := C * K)
      (show (0 : ℝ) < min 1 (ρ / 2) by positivity) fun ε ⟨hε, hεle⟩ ↦ ?_)
    have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
    have hερ : ε < ρ := by linarith [min_le_right 1 (ρ / 2)]
    have hws : tsupport (cutoff y ε u : E → F) ⊆ ball y ρ :=
      (tsupport_cutoff_subset_closedBall hε u).trans (closedBall_subset_ball hερ)
    have hwflat : ∀ i ≤ r, iteratedFDeriv ℝ i (cutoff y ε u) y = 0 := fun i hi ↦ by
      rw [((cutoff_eventuallyEq hε u).iteratedFDeriv ℝ i).eq_of_nhds, hflat i hi]
    rw [← apply_cutoff P hloc hx₀ hε u]
    have hcontw : Tendsto (fun y' ↦ ‖P (cutoff y ε u) y'‖) (𝓝[≠] y)
        (𝓝 ‖P (cutoff y ε u) y‖) :=
      (((hcont _).continuousAt (hU.mem_nhds hx₀)).tendsto.mono_left nhdsWithin_le_nhds).norm
    refine le_of_tendsto hcontw ?_
    filter_upwards [inter_mem_nhdsWithin _ (ball_mem_nhds y hρ), self_mem_nhdsWithin]
      with y' hy' hne'
    calc ‖P (cutoff y ε u) y'‖ ≤ C * (K * ε) :=
          norm_apply_le_of_iteratedFDeriv_eq_zero P hloc hρU hC hws hwflat (hK ε hε hε1)
            hy'.2 hne'
      _ = C * K * ε := by ring
  · -- Away from the centre, the cut-offs themselves are supported in the punctured ball.
    have hd : 0 < dist y x₀ := dist_pos.mpr hne
    have hd' : 0 < ρ - dist y x₀ := sub_pos.mpr (mem_ball.mp hy)
    -- Let `ε → 0⁺` in `‖(P u) y‖ ≤ C * K * ε`.
    refine norm_le_zero_iff.mp (le_zero_of_forall_mem_Ioc_le_mul (c := C * K)
      (show (0 : ℝ) < min 1 (min (dist y x₀) (ρ - dist y x₀) / 2) by positivity)
      fun ε ⟨hε, hεle⟩ ↦ ?_)
    have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
    have hεd : ε < dist y x₀ := by
      linarith [min_le_right 1 (min (dist y x₀) (ρ - dist y x₀) / 2),
        min_le_left (dist y x₀) (ρ - dist y x₀)]
    have hερ : ε < ρ - dist y x₀ := by
      linarith [min_le_right 1 (min (dist y x₀) (ρ - dist y x₀) / 2),
        min_le_right (dist y x₀) (ρ - dist y x₀)]
    have hws : tsupport (cutoff y ε u : E → F) ⊆ ball x₀ ρ \ {x₀} := by
      intro z hz
      have hz' := mem_closedBall.mp (tsupport_cutoff_subset_closedBall hε u hz)
      refine ⟨mem_ball.mpr ?_, fun hzx ↦ ?_⟩
      · linarith [dist_triangle z y x₀]
      · rw [mem_singleton_iff] at hzx
        subst hzx
        rw [dist_comm] at hz'
        linarith
    rw [← apply_cutoff P hloc (hρU hy) hε u]
    calc ‖P (cutoff y ε u) y‖ ≤ C * (K * ε) := hC _ hws _ (hK ε hε hε1) y (hρU hy)
      _ = C * K * ε := by ring

/-- **Peetre's theorem.** Let `P` be a linear map from smooth functions `E → F` to functions
`E → G`, local on the open set `U` (`(P u) x = 0` whenever `u` vanishes near `x ∈ U`) and with
`P u` continuous on `U` for every `u`. Then `P` has locally finite order: for every compact
`K ⊆ U` there is `r` such that `(P u) x = 0` whenever `x ∈ K` and the derivatives of `u` of order at
most `r` vanish at `x`. No continuity of `P` is assumed. -/
theorem exists_apply_eq_zero_of_iteratedFDeriv_eq_zero
    (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G) (hU : IsOpen U)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    (hcont : ∀ u, ContinuousOn (P u) U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯,
      (∀ i ≤ r, iteratedFDeriv ℝ i u x = 0) → P u x = 0 := by
  choose! ρ hρ _ r hr using fun x (hx : x ∈ U) ↦
    exists_forall_mem_ball_apply_eq_zero P hU hloc hcont hx
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun x ↦ ball x (ρ x))
    fun x hx ↦ ball_mem_nhds x (hρ x (hKU hx))
  refine ⟨t.sup r, fun x hx u hu ↦ ?_⟩
  obtain ⟨c, hct, hxc⟩ := mem_iUnion₂.mp (hKt hx)
  exact hr c (hKU (htK c hct)) x hxc u fun i hi ↦ hu i (hi.trans (Finset.le_sup hct))

/-- **Peetre's theorem**, in jet form: for every compact `K ⊆ U` there is `r` such that
`(P u) x = (P v) x` whenever `x ∈ K` and `u`, `v` have the same derivatives of order at most `r`
at `x`. -/
theorem exists_apply_eq_apply_of_iteratedFDeriv_eq
    (P : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯ →ₗ[ℝ] E → G) (hU : IsOpen U)
    (hloc : ∀ u : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯, ∀ x ∈ U, (u : E → F) =ᶠ[𝓝 x] 0 → P u x = 0)
    (hcont : ∀ u, ContinuousOn (P u) U) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ r : ℕ, ∀ x ∈ K, ∀ u v : C^∞⟮𝓘(ℝ, E), E; 𝓘(ℝ, F), F⟯,
      (∀ i ≤ r, iteratedFDeriv ℝ i u x = iteratedFDeriv ℝ i v x) → P u x = P v x := by
  obtain ⟨r, hr⟩ := exists_apply_eq_zero_of_iteratedFDeriv_eq_zero P hU hloc hcont hK hKU
  refine ⟨r, fun x hx u v huv ↦ ?_⟩
  have h := hr x hx (u - v) fun i hi ↦ by
    rw [ContMDiffMap.coe_sub, iteratedFDeriv_sub_apply
      (u.contMDiff.contDiff.contDiffAt.of_le (by exact_mod_cast le_top))
      (v.contMDiff.contDiff.contDiffAt.of_le (by exact_mod_cast le_top)), huv i hi, sub_self]
  rwa [map_sub, Pi.sub_apply, sub_eq_zero] at h

end Cutoff

end LinearMap
