/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Calculus.IteratedFDeriv.FDerivApply
import TauCeti.Analysis.InnerProductSpace.Harmonic.Analytic
import TauCeti.Analysis.InnerProductSpace.Harmonic.Deriv
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Interior derivative estimates of every order

Let `E` be a real inner product space of finite dimension `n`, and let `u : E → F` be harmonic on
the ball `ball x R`, with values in a finite-dimensional real normed space `F`. This file proves
the interior estimates for derivatives of every order `k`:

* if `‖u‖ ≤ M` on `ball x R`, then
  `‖D^k u(x)‖ ≤ (2ⁿ⁺¹ n k / R)^k M`
  (`InnerProductSpace.HarmonicOnNhd.norm_iteratedFDeriv_le_of_norm_le`);
* with the `L¹` norm on `ball x r` for an additive Haar measure `μ`,
  `‖D^k u(x)‖ ≤ 2ⁿ (2ⁿ⁺² n k)^k / (μ(B₁) r^(n+k)) ∫_{B(x,r)} ‖u‖ dμ`
  (`InnerProductSpace.HarmonicOnNhd.norm_iteratedFDeriv_le_integral_norm`), where `μ(B₁)` is the
  measure of the unit ball.

Consequently, if harmonic functions converge locally uniformly to a harmonic function on an open
set, so do their derivatives of every order
(`TendstoLocallyUniformlyOn.iteratedFDeriv_of_harmonicOnNhd`).

Here `D^k u(x)` is the iterated Fréchet derivative `iteratedFDeriv ℝ k u x`, whose operator norm
bounds every partial derivative `∂^α u(x)` with `|α| = k`. The constants depend only on `n` and
`k`, and the estimates are scale-invariant: they carry the factor `R^{-k}`, respectively
`r^{-n-k}`.

## The argument

The gradient bound `‖Du(y)‖ ≤ 2ⁿ n M / ρ` for a harmonic function bounded by `M` on `ball y (2ρ)`
(`InnerProductSpace.HarmonicOnNhd.norm_fderiv_le_of_norm_le`), in its translated form
`InnerProductSpace.HarmonicOnNhd.norm_fderiv_le_of_norm_le_of_mem_ball`, is iterated, as in Evans.
Peel off the innermost derivative: `D^(k+1) u(x)(m₀, …, m_k) = D^k (∂_{m_k} u)(x)(m₀, …, m_{k-1})`,
the directional derivative `∂_v u` is again harmonic
(`InnerProductSpace.HarmonicOnNhd.fderiv_apply`), and on `ball x (R k / (k + 1))` it is bounded by
`2ⁿ⁺¹ n (k + 1) M ‖v‖ / R`, by the gradient bound on balls of radius `R / (k + 1)`. Splitting
`ball x R` into `k + 1` shells of equal width gives the constant `(2ⁿ⁺¹ n (k + 1) / R)^(k+1)`.
Vector-valued functions are reduced to scalar ones by the continuous linear functionals on `F`; this
uses that a harmonic function with values in a finite-dimensional space is smooth
(`InnerProductSpace.HarmonicAt.analyticAt`). The `L¹` estimate follows from the supremum estimate on
`ball x (r / 2)` and the mean-value bound
`InnerProductSpace.HarmonicOnNhd.norm_le_inv_measureReal_mul_integral_norm`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §2.2.3, Theorem 7 (estimates on
  derivatives).
-/

public section

noncomputable section

open Filter Metric Set Module MeasureTheory Topology

namespace InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The supremum estimate for real-valued harmonic functions, by induction on the order. -/
private theorem HarmonicOnNhd.norm_iteratedFDeriv_le_of_norm_le_real (k : ℕ) :
    ∀ {u : E → ℝ} {x : E} {R M : ℝ}, HarmonicOnNhd u (ball x R) →
      (∀ y ∈ ball x R, ‖u y‖ ≤ M) → 0 < R →
      ‖iteratedFDeriv ℝ k u x‖ ≤ (2 ^ (finrank ℝ E + 1) * finrank ℝ E * k / R) ^ k * M := by
  induction k with
  | zero =>
    intro u x R M _ hM hR
    simpa using hM x (mem_ball_self hR)
  | succ k ih =>
    intro u x R M hu hM hR
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_ball_self hR))
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- The first derivative is the gradient bound on `ball x (2 * (R / 2))`.
      have h2 : 2 * (R / 2) = R := by ring
      rw [norm_iteratedFDeriv_one]
      refine (HarmonicOnNhd.norm_fderiv_le_of_norm_le (ρ := R / 2) (by rwa [h2])
        (by rwa [h2]) (half_pos hR)).trans_eq ?_
      push_cast
      field_simp
      ring
    -- The directional derivatives are bounded by `c M` on `ball x R'`, by the gradient bound on
    -- balls of radius `2 ρ`, where `R' + 2 ρ = R`.
    set n := finrank ℝ E
    set c : ℝ := 2 ^ (n + 1) * n * (k + 1 : ℕ) / R
    set R' : ℝ := R * k / (k + 1)
    set ρ : ℝ := R / (2 * (k + 1))
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have hR' : 0 < R' := by positivity
    have hρ : 0 < ρ := by positivity
    have hRρ : R - 2 * ρ = R' := by simp only [R', ρ]; field_simp; ring
    have hcρ : 2 ^ n * n / ρ = c := by simp only [c, ρ]; push_cast; field_simp; ring
    have hcR' : 2 ^ (n + 1) * n * k / R' = c := by
      simp only [c, R']; push_cast; field_simp
    have hD (y : E) (hy : y ∈ ball x R') : ‖fderiv ℝ u y‖ ≤ c * M := by
      rw [← hcρ]
      exact hu.norm_fderiv_le_of_norm_le_of_mem_ball hM hρ (by rwa [hRρ])
    have : 0 ≤ c := by positivity
    have hcd : ContDiffAt ℝ (k + 1) u x := (hu x (mem_ball_self hR)).analyticAt.contDiffAt
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
    -- Peel off the innermost derivative, in the direction `v = m (Fin.last k)`.
    set v := m (Fin.last k)
    have hih := ih ((hu.fderiv_apply v).mono (ball_subset_ball (by linarith)))
      (M := c * M * ‖v‖) (fun y hy ↦ ((fderiv ℝ u y).le_opNorm v).trans (by gcongr; exact hD y hy))
      hR'
    rw [hcR'] at hih
    rw [← Fin.snoc_init_self m, ← hcd.iteratedFDeriv_fderiv_apply_eq_iteratedFDeriv_snoc,
      Fin.prod_univ_castSucc]
    calc ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ u y v) x (Fin.init m)‖
        ≤ ‖iteratedFDeriv ℝ k (fun y ↦ fderiv ℝ u y v) x‖ * ∏ i, ‖Fin.init m i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ c ^ k * (c * M * ‖v‖) * ∏ i, ‖Fin.init m i‖ := by gcongr
      _ = _ := by simp [v, Fin.init]; ring

/-- **Interior derivative estimates of every order.** Let `u` be harmonic on `ball x R`, with
values in a finite-dimensional real normed space, and bounded by `M` there. Then the `k`-th
iterated Fréchet derivative of `u` at the centre satisfies
`‖D^k u(x)‖ ≤ (2ⁿ⁺¹ n k / R)^k M`, where `n` is the dimension of `E`. -/
theorem HarmonicOnNhd.norm_iteratedFDeriv_le_of_norm_le [FiniteDimensional ℝ F] {u : E → F}
    {x : E} {R M : ℝ} (hu : HarmonicOnNhd u (ball x R)) (hM : ∀ y ∈ ball x R, ‖u y‖ ≤ M)
    (hR : 0 < R) (k : ℕ) :
    ‖iteratedFDeriv ℝ k u x‖ ≤ (2 ^ (finrank ℝ E + 1) * finrank ℝ E * k / R) ^ k * M := by
  set C : ℝ := (2 ^ (finrank ℝ E + 1) * finrank ℝ E * k / R) ^ k
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_ball_self hR))
  have : 0 ≤ C := by positivity
  have hcd : ContDiffAt ℝ k u x := (hu x (mem_ball_self hR)).analyticAt.contDiffAt
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m ↦ ?_
  -- Test against every continuous linear functional `ℓ`, for which `ℓ ∘ u` is real-valued.
  refine NormedSpace.norm_le_dual_bound ℝ _ (by positivity) fun ℓ ↦ ?_
  have hℓ := HarmonicOnNhd.norm_iteratedFDeriv_le_of_norm_le_real k (hu.comp_CLM ℓ)
    (M := ‖ℓ‖ * M) (fun y hy ↦ (ℓ.le_opNorm _).trans (by gcongr; exact hM y hy)) hR
  calc ‖ℓ (iteratedFDeriv ℝ k u x m)‖ = ‖iteratedFDeriv ℝ k (ℓ ∘ u) x m‖ := by
        simp [ℓ.iteratedFDeriv_comp_left hcd le_rfl]
    _ ≤ ‖iteratedFDeriv ℝ k (ℓ ∘ u) x‖ * ∏ i, ‖m i‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C * (‖ℓ‖ * M) * ∏ i, ‖m i‖ := by gcongr
    _ = C * M * (∏ i, ‖m i‖) * ‖ℓ‖ := by ring

/-- **Interior derivative estimates of every order, in the `L¹` norm.** Let `u` be harmonic on
`ball x r` and integrable there for an additive Haar measure `μ`, with values in a
finite-dimensional real normed space. Then the `k`-th iterated Fréchet derivative of `u` at the
centre satisfies
`‖D^k u(x)‖ ≤ 2ⁿ (2ⁿ⁺² n k)^k / (μ(B₁) r^(n+k)) ∫_{B(x,r)} ‖u‖ dμ`,
where `n` is the dimension of `E` and `μ(B₁)` is the measure of the unit ball. -/
theorem HarmonicOnNhd.norm_iteratedFDeriv_le_integral_norm [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {x : E}
    {r : ℝ} (hu : HarmonicOnNhd u (ball x r)) (hi : IntegrableOn u (ball x r) μ) (hr : 0 < r)
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k u x‖ ≤
      2 ^ finrank ℝ E * (2 ^ (finrank ℝ E + 2) * finrank ℝ E * k) ^ k /
        (μ.real (ball (0 : E) 1) * r ^ (finrank ℝ E + k)) * ∫ y in ball x r, ‖u y‖ ∂μ := by
  set I := ∫ y in ball x r, ‖u y‖ ∂μ
  have hr2 : 0 < r / 2 := half_pos hr
  have hω : 0 < μ.real (ball (0 : E) 1) := measureReal_ball_pos μ 0 one_pos
  -- By the mean-value bound, `‖u‖ ≤ I / μ(B_{r/2})` on `ball x (r / 2)`.
  have hM (y : E) (hy : y ∈ ball x (r / 2)) : ‖u y‖ ≤ (μ.real (ball (0 : E) (r / 2)))⁻¹ * I := by
    refine hu.norm_le_inv_measureReal_mul_integral_norm hi hr2 fun z hz ↦ ?_
    rw [mem_ball]
    linarith [mem_ball.mp hy, mem_closedBall.mp hz, dist_triangle z y x]
  have h := (hu.mono (ball_subset_ball (half_le_self hr.le))).norm_iteratedFDeriv_le_of_norm_le
    hM hr2 k
  refine h.trans_eq ?_
  have hc : 2 ^ (finrank ℝ E + 1) * finrank ℝ E * k / (r / 2) =
      2 ^ (finrank ℝ E + 2) * finrank ℝ E * k / r := by
    field_simp
    ring
  rw [hc, μ.addHaar_real_ball_of_pos 0 hr2, div_pow r, div_pow]
  field_simp
  ring

/-- **Locally uniform convergence of harmonic functions upgrades to all derivatives.** If,
eventually along `l`, the functions `u i` are harmonic on an open set `U` and converge locally
uniformly on `U` to a function `f` harmonic on `U`, then for every `k` their `k`-th iterated
Fréchet derivatives converge locally uniformly on `U` to that of `f`. -/
theorem _root_.TendstoLocallyUniformlyOn.iteratedFDeriv_of_harmonicOnNhd [FiniteDimensional ℝ F]
    {ι : Type*} {l : Filter ι} {u : ι → E → F} {f : E → F} {U : Set E}
    (hlim : TendstoLocallyUniformlyOn u f l U) (hu : ∀ᶠ i in l, HarmonicOnNhd (u i) U)
    (hf : HarmonicOnNhd f U) (hU : IsOpen U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i ↦ iteratedFDeriv ℝ k (u i)) (iteratedFDeriv ℝ k f) l U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  obtain ⟨r, hr, hrU⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds hx)
  have hr2 : 0 < r / 2 := half_pos hr
  set C : ℝ := (2 ^ (finrank ℝ E + 1) * finrank ℝ E * k / (r / 2)) ^ k
  have : 0 ≤ C := by positivity
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hrU
    (isCompact_closedBall x r)
  refine ⟨ball x (r / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr2), ?_⟩
  filter_upwards [hu, Metric.tendstoUniformlyOn_iff.1 hunif (ε / (C + 1)) (by positivity)]
    with i hi hδ y hy
  have hball : ball y (r / 2) ⊆ closedBall x r := fun z hz ↦ by
    rw [mem_closedBall]
    rw [mem_ball] at hz hy
    linarith [dist_triangle z y x]
  have hyU : y ∈ U := hrU (hball (mem_ball_self hr2))
  -- The interior estimate for `u i - f`, which is bounded by `ε / (C + 1)` on `ball y (r / 2)`.
  have hb := ((hi.sub hf).mono (hball.trans hrU)).norm_iteratedFDeriv_le_of_norm_le
    (M := ε / (C + 1)) (fun z hz ↦ by
      rw [Pi.sub_apply, ← dist_eq_norm, dist_comm]
      exact (hδ z (hball hz)).le) hr2 k
  rw [iteratedFDeriv_sub_apply (hi y hyU).analyticAt.contDiffAt
    (hf y hyU).analyticAt.contDiffAt] at hb
  rw [dist_comm, dist_eq_norm]
  calc _ ≤ C * (ε / (C + 1)) := hb
    _ < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith

end InnerProductSpace
