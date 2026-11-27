/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.ZerothOrderMaximumPrinciple
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential decay of subsolutions of `-Δ + V` inside a ball

Let `u` be a function on a ball `B(x, R)` of a finite-dimensional real inner product space `E`
of dimension `n`, and suppose that it is a subsolution of the screened operator `-Δ + V` with a
constant forcing `K ≥ 0`,

`V u - K ≤ Δ u`  on `B(x, R)`,  with `V ≥ c² > 0`,

and that `u ≤ M` with `M ≥ 0`. Then `u` is exponentially small at the centre, up to the forcing
level `K / c²`:

`u x ≤ K / c² + exp (n / 8) M exp (-c R / 4)`

(`TauCeti.le_div_sq_add_exp_mul_mul_exp_of_mul_sub_le_laplacian`). The forcing level is attained
by the constant `K / c²`, which solves `c² u - K = Δ u`, and the factor `exp (-c R / 4)` records
how far `x` is from the part of the boundary where `u` may be as large as `M`. Unlike the exterior
decay of `TauCeti.Analysis.InnerProductSpace.Laplacian.ExponentialDecay`, nothing is assumed at
infinity: the estimate is local, and the constants depend only on `n`.

The proof compares `u - K / c²` with the Gaussian barrier

`g y = M exp (μ (‖y - x‖² - R²))`,  `μ = c² / (4 c R + 2 n)`,

which equals `M` on the sphere `‖y - x‖ = R` and satisfies
`Δ g = (4 μ² ‖y - x‖² + 2 n μ) g ≤ c² g` on the ball, by the choice of `μ`
(`ContDiffAt.laplacian_comp_norm_sq`). So `g` is a supersolution of `-Δ + V`, and the comparison
principle for `-Δ + V` (`TauCeti.le_of_mul_le_laplacian_le_of_le_frontier`) gives
`u x - K / c² ≤ g x = M exp (-c² R² / (4 c R + 2 n))`
(`TauCeti.le_div_sq_add_mul_exp_of_mul_sub_le_laplacian`), and
`c² R² / (4 c R + 2 n) ≥ c R / 4 - n / 8`.

Estimates of the form `C / r + C exp (-c √r d)`, with `d` the distance to the zero set of the
spinor component `α`, run through Taubes's analysis of the Seiberg–Witten equations at large
parameter `r`. This file is their comparison step: if a quantity bounded by `M` satisfies the
screened inequality with `c²` proportional to `r` and `K` bounded on every ball avoiding the zero
set, then the estimate on the ball of radius `R = d` gives exactly the two terms `K / c²`, of
order `1 / r`, and `M exp (-c d / 4)`.

## Main declarations

* `TauCeti.le_div_sq_add_mul_exp_of_mul_sub_le_laplacian`: the estimate with the barrier exponent
  `c² R² / (4 c R + 2 n)`, for `u` continuous on the closed ball with `u ≤ M` on the sphere.
* `TauCeti.le_div_sq_add_exp_mul_mul_exp_of_mul_sub_le_laplacian`: the estimate
  `u x ≤ K / c² + exp (n / 8) M exp (-c R / 4)` for `u` bounded by `M` on the open ball.

## References

* D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Springer, Chapter 3 (the maximum principle and comparison with barriers).
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set Filter Topology InnerProductSpace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The exponent `μ = c² / (4 c R s + 2 T)` of the Gaussian barrier satisfies
`4 s² R² μ² + 2 T μ ≤ c²`. -/
theorem four_mul_sq_mul_sq_mul_sq_add_two_mul_mul_le {c R s T : ℝ} (hc : 0 < c)
    (hR : 0 ≤ R) (hs : 0 ≤ s) (hT : 0 ≤ T) :
    4 * s ^ 2 * R ^ 2 * (c ^ 2 / (4 * c * R * s + 2 * T)) ^ 2 +
      2 * T * (c ^ 2 / (4 * c * R * s + 2 * T)) ≤ c ^ 2 := by
  set D := 4 * c * R * s + 2 * T
  set μ := c ^ 2 / D
  rcases (show 0 ≤ D by positivity).eq_or_lt with hD | hD
  · simp [μ, ← hD, sq_nonneg]
  have hμ : 0 ≤ μ := by positivity
  have hμD : μ * D = c ^ 2 := div_mul_cancel₀ _ hD.ne'
  have hsRμ : 0 ≤ s * R * μ := by positivity
  -- From `μ D = c²` and `D ≥ 4 c R s`: `4 s R μ ≤ c`, so `4 s² R² μ² ≤ 4 c s R μ = μ D - 2 T μ`.
  have hle : 4 * (s * R * μ) ≤ c := by
    have : c * (4 * (s * R * μ)) ≤ c * c := by nlinarith [mul_nonneg hT hμ]
    exact le_of_mul_le_mul_left this hc
  nlinarith [mul_le_mul_of_nonneg_left hle hsRμ]

/-- The barrier exponent `c² s² / (4 c s σ + 2 (P + β s))` of the decay estimate on the ball of
radius `s` is at least `c² s / (4 c σ + 2 β) - n / 8` when `0 ≤ P ≤ n σ²`. -/
theorem neg_div_le_div_eight_add_neg_div {c s σ β P n : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hσ : 0 ≤ σ) (hβ : 0 ≤ β) (hn : 0 ≤ n) (hP : 0 ≤ P) (hPn : P ≤ n * σ ^ 2) :
    -(c ^ 2 * s ^ 2 / (4 * c * s * σ + 2 * (P + β * s))) ≤
      n / 8 + -(c ^ 2 * s / (4 * c * σ + 2 * β)) := by
  set A := 4 * c * σ + 2 * β
  have hDA : 4 * c * s * σ + 2 * (P + β * s) = s * A + 2 * P := by ring
  rw [hDA]
  rcases (show 0 ≤ A by positivity).eq_or_lt with hA | hA
  · -- Then `σ = β = 0`, so `P = 0` and both exponents vanish.
    have hσ0 : σ = 0 := by nlinarith
    have hP0 : P = 0 := le_antisymm (by simpa [hσ0] using hPn) hP
    simp only [← hA, hP0, mul_zero, add_zero, div_zero, neg_zero]
    positivity
  -- The difference of the exponents is `2 c² s P / (A (s A + 2 P)) ≤ 2 c² P / A² ≤ n / 8`.
  have h1 : c ^ 2 * s / A - c ^ 2 * s ^ 2 / (s * A + 2 * P) =
      2 * c ^ 2 * s * P / (A * (s * A + 2 * P)) := by
    field_simp
    ring
  have h2 : 2 * c ^ 2 * s * P / (A * (s * A + 2 * P)) ≤ 2 * c ^ 2 * P / A ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg c) hP) (mul_nonneg hA.le hP)]
  have h3 : 2 * c ^ 2 * P / A ^ 2 ≤ n / 8 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hA2 : 16 * c ^ 2 * σ ^ 2 ≤ A ^ 2 := by nlinarith [mul_nonneg hc.le hσ]
    nlinarith [mul_le_mul_of_nonneg_left hPn (sq_nonneg c), mul_le_mul_of_nonneg_left hA2 hn]
  linarith

/-- The Gaussian barrier `M exp (μ (‖y - x‖² - R²))`, `μ = c² / (4 c R + 2 n)`, is a supersolution
of `-Δ + c²` on the closed ball of radius `R` about `x`, for `M ≥ 0`. -/
private theorem laplacian_gaussian_barrier_le {x y : E} {c R M : ℝ} (hc : 0 < c) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hy : ‖y - x‖ ≤ R) :
    Δ (fun z : E ↦ M * Real.exp (c ^ 2 / (4 * c * R + 2 * Module.finrank ℝ E) *
        (‖z - x‖ ^ 2 - R ^ 2))) y ≤
      c ^ 2 * (M * Real.exp (c ^ 2 / (4 * c * R + 2 * Module.finrank ℝ E) *
        (‖y - x‖ ^ 2 - R ^ 2))) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  set μ := c ^ 2 / (4 * c * R + 2 * n)
  set ρ : ℝ → ℝ := fun s ↦ M * Real.exp (μ * (s - R ^ 2))
  have hρ : ContDiff ℝ 2 ρ := by fun_prop
  have hd : deriv ρ = fun s ↦ μ * ρ s := by
    funext s
    simp (disch := fun_prop) [ρ]
    ring
  have hdd : deriv (deriv ρ) = fun s ↦ μ ^ 2 * ρ s := by
    rw [hd]
    funext s
    rw [deriv_const_mul _ (hρ.differentiable (by norm_num) s), hd]
    ring
  -- Translate the barrier to the origin, where it is a function of `‖·‖²`.
  have htr : (fun z : E ↦ M * Real.exp (μ * (‖z - x‖ ^ 2 - R ^ 2))) =
      fun z ↦ (fun w : E ↦ ρ (‖w‖ ^ 2)) (z + -x) := by
    funext z
    simp [ρ, sub_eq_add_neg]
  rw [htr, laplacian_comp_add_right (fun w : E ↦ ρ (‖w‖ ^ 2)) (-x)]
  beta_reduce
  rw [← sub_eq_add_neg, hρ.contDiffAt.laplacian_comp_norm_sq, hdd, hd]
  have hρy : 0 ≤ ρ (‖y - x‖ ^ 2) := by positivity
  have hyR : ‖y - x‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have hμ : 4 * R ^ 2 * μ ^ 2 + 2 * n * μ ≤ c ^ 2 := by
    simpa using four_mul_sq_mul_sq_mul_sq_add_two_mul_mul_le hc hR zero_le_one
      (Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ E))
  calc 4 * ‖y - x‖ ^ 2 * (μ ^ 2 * ρ (‖y - x‖ ^ 2)) + 2 * n * (μ * ρ (‖y - x‖ ^ 2))
      ≤ (4 * R ^ 2 * μ ^ 2 + 2 * n * μ) * ρ (‖y - x‖ ^ 2) := by
        nlinarith [mul_nonneg (sq_nonneg μ) hρy]
    _ ≤ c ^ 2 * ρ (‖y - x‖ ^ 2) := mul_le_mul_of_nonneg_right hμ hρy

/-- In a zero-dimensional space, a subsolution of `-Δ + V` with `V ≥ c² > 0` and forcing `K ≥ 0`
is at most `K / c²`, since its Laplacian vanishes. -/
private theorem le_div_sq_of_subsingleton [Subsingleton E] {u V : E → ℝ} {x : E} {c K : ℝ}
    (hc : 0 < c) (hK : 0 ≤ K) (hV : c ^ 2 ≤ V x) (hsub : V x * u x - K ≤ Δ u x) :
    u x ≤ K / c ^ 2 := by
  have hΔ : Δ u x = 0 := by
    rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis (f := u)) x]
    simp [Module.finrank_zero_of_subsingleton]
  rw [hΔ] at hsub
  rw [le_div_iff₀ (by positivity)]
  rcases le_or_gt (u x) 0 with hu | hu
  · nlinarith [sq_nonneg c]
  · nlinarith

/-- **Exponential decay of subsolutions of `-Δ + V` inside a ball, barrier form.** Let `u` be
continuous on the closed ball of radius `R > 0` about `x` and `C²` on the open ball, where it
satisfies `V u - K ≤ Δ u` for a potential `V ≥ c²`, `c > 0`, and a forcing `K ≥ 0`. If `u ≤ M` on
the sphere, with `M ≥ 0`, then at the centre, with `n = dim E`,

`u x ≤ K / c² + M exp (-c² R² / (4 c R + 2 n))`. -/
theorem le_div_sq_add_mul_exp_of_mul_sub_le_laplacian {u V : E → ℝ} {x : E} {c R K M : ℝ}
    (hc : 0 < c) (hR : 0 < R) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hcont : ContinuousOn u (closedBall x R)) (hcd : ∀ y ∈ ball x R, ContDiffAt ℝ 2 u y)
    (hV : ∀ y ∈ ball x R, c ^ 2 ≤ V y) (hsub : ∀ y ∈ ball x R, V y * u y - K ≤ Δ u y)
    (hbdry : ∀ y ∈ sphere x R, u y ≤ M) :
    u x ≤ K / c ^ 2 +
      M * Real.exp (-(c ^ 2 * R ^ 2 / (4 * c * R + 2 * Module.finrank ℝ E))) := by
  have hx : x ∈ ball x R := mem_ball_self hR
  have hexp : 0 ≤ M * Real.exp (-(c ^ 2 * R ^ 2 / (4 * c * R + 2 * Module.finrank ℝ E))) := by
    positivity
  rcases subsingleton_or_nontrivial E with hE | hE
  · linarith [le_div_sq_of_subsingleton hc hK (hV x hx) (hsub x hx)]
  set μ := c ^ 2 / (4 * c * R + 2 * Module.finrank ℝ E)
  set g : E → ℝ := fun z ↦ M * Real.exp (μ * (‖z - x‖ ^ 2 - R ^ 2))
  have hg : ContDiff ℝ 2 g := by
    have : ContDiff ℝ 2 fun z : E ↦ ‖z - x‖ ^ 2 := (contDiff_id.sub contDiff_const).norm_sq ℝ
    fun_prop
  have hint : interior (closedBall x R) = ball x R := interior_closedBall x hR.ne'
  have hfr : frontier (closedBall x R) = sphere x R := frontier_closedBall x hR.ne'
  -- Compare `u - K / c²` with the barrier `g` by the comparison principle for `-Δ + V`.
  have key := le_of_mul_le_laplacian_le_of_le_frontier (isCompact_closedBall x R) (c := V)
    (f := u - fun _ ↦ K / c ^ 2) (g := g) (hcont.sub continuousOn_const) hg.continuous.continuousOn
    (fun y hy ↦ (hcd y (hint ▸ hy)).sub contDiffAt_const) (fun y _ ↦ hg.contDiffAt)
    (fun y hy ↦ (sq_pos_of_pos hc).le.trans (hV y (hint ▸ hy)))
    (fun y hy ↦ by
      rw [hint] at hy
      rw [(hcd y hy).laplacian_sub contDiffAt_const, laplacian_const, Pi.sub_apply, Pi.zero_apply,
        sub_zero]
      -- `V ≥ c²` and `K ≥ 0` give `K ≤ V K / c²`.
      have hKV : K ≤ V y * (K / c ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity)]
        nlinarith [hV y hy]
      nlinarith [hsub y hy])
    (fun y hy ↦ by
      rw [hint] at hy
      have hgy : 0 ≤ g y := by positivity
      exact (laplacian_gaussian_barrier_le hc hR.le hM (mem_ball_iff_norm.1 hy).le).trans
        (mul_le_mul_of_nonneg_right (hV y hy) hgy))
    (fun y hy ↦ by
      rw [hfr] at hy
      have hyx : ‖y - x‖ = R := mem_sphere_iff_norm.1 hy
      simp only [g, Pi.sub_apply, hyx, sub_self, mul_zero, Real.exp_zero, mul_one]
      linarith [hbdry y hy, div_nonneg hK (sq_nonneg c)])
    (mem_closedBall_self hR.le)
  simp only [g, Pi.sub_apply, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_sub] at key
  have hμR : μ * -R ^ 2 = -(c ^ 2 * R ^ 2 / (4 * c * R + 2 * Module.finrank ℝ E)) := by
    simp only [μ]
    ring
  rw [hμR] at key
  linarith

/-- **Exponential decay of subsolutions of `-Δ + V` inside a ball.** Let `u` be `C²` on the ball
of radius `R > 0` about `x`, where it satisfies `V u - K ≤ Δ u` for a potential `V ≥ c²`, `c > 0`,
and a forcing `K ≥ 0`, and is bounded by `M ≥ 0`. Then at the centre, with `n = dim E`,

`u x ≤ K / c² + exp (n / 8) M exp (-c R / 4)`. -/
theorem le_div_sq_add_exp_mul_mul_exp_of_mul_sub_le_laplacian {u V : E → ℝ} {x : E}
    {c R K M : ℝ} (hc : 0 < c) (hR : 0 < R) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hcd : ∀ y ∈ ball x R, ContDiffAt ℝ 2 u y) (hV : ∀ y ∈ ball x R, c ^ 2 ≤ V y)
    (hsub : ∀ y ∈ ball x R, V y * u y - K ≤ Δ u y) (hle : ∀ y ∈ ball x R, u y ≤ M) :
    u x ≤ K / c ^ 2 +
      Real.exp ((Module.finrank ℝ E : ℝ) / 8) * M * Real.exp (-(c * R / 4)) := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  set F : ℝ → ℝ := fun s ↦ K / c ^ 2 + Real.exp (n / 8) * M * Real.exp (-(c * s / 4))
  -- The bound holds on every smaller closed ball, and `F` is continuous in the radius.
  have hsmall : ∀ s ∈ Ioo 0 R, u x ≤ F s := by
    rintro s ⟨hs, hsR⟩
    have hsub' : closedBall x s ⊆ ball x R := closedBall_subset_ball hsR
    have h := le_div_sq_add_mul_exp_of_mul_sub_le_laplacian hc hs hK hM
      (fun y hy ↦ (hcd y (hsub' hy)).continuousAt.continuousWithinAt)
      (fun y hy ↦ hcd y (ball_subset_ball hsR.le hy)) (fun y hy ↦ hV y (ball_subset_ball hsR.le hy))
      (fun y hy ↦ hsub y (ball_subset_ball hsR.le hy))
      (fun y hy ↦ hle y (hsub' (sphere_subset_closedBall hy)))
    have hexp : -(c ^ 2 * s ^ 2 / (4 * c * s + 2 * n)) ≤ n / 8 + -(c * s / 4) := by
      have hn : 0 ≤ n := Nat.cast_nonneg _
      have h := neg_div_le_div_eight_add_neg_div hc hs zero_le_one le_rfl hn hn (by simp)
      simp only [mul_one, zero_mul, mul_zero, add_zero] at h
      rwa [show c ^ 2 * s / (4 * c) = c * s / 4 by field_simp] at h
    calc u x ≤ K / c ^ 2 + M * Real.exp (-(c ^ 2 * s ^ 2 / (4 * c * s + 2 * n))) := h
      _ ≤ K / c ^ 2 + M * Real.exp (n / 8 + -(c * s / 4)) := by gcongr
      _ = F s := by
        simp only [F, Real.exp_add]
        ring
  have hF : Continuous F := by fun_prop
  exact ge_of_tendsto (hF.tendsto R |>.mono_left nhdsWithin_le_nhds)
    (eventually_of_mem (Ioo_mem_nhdsLT hR) hsmall)

end TauCeti
