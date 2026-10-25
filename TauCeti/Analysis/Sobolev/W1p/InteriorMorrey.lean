/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.DirichletGrowth
public import TauCeti.Analysis.Sobolev.W1p.Morrey
import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.Topology.MetricSpace.Holder.Basic

/-!
# Morrey's embedding for `W^{1,p}(Ω)` in the interior of a domain

Let `Ω` be an open subset of a finite-dimensional real inner product space of dimension `n`, with
an additive Haar measure `μ`, and let `n < p ≤ ∞`. This file proves that every `u ∈ W^{1,p}(Ω)` is
locally Hölder continuous in `Ω` with exponent `α = 1 - n / p`, in the form of the local Morrey
inequality

`|u*(x) - u*(y)| ≤ C ‖∇u‖_{Lᵖ(B(x, 2|x - y|))} |x - y|^α` whenever `closedBall x (2|x - y|) ⊆ Ω`,

where `u*` is the precise representative of `u` (the limit of its averages over shrinking balls,
which agrees with `u` almost everywhere on `Ω` by `TauCeti.W1p.ae_eq_preciseRepresentative`) and
`C` depends only on `n`, `p` and `μ`. No regularity of `∂Ω` is needed, and the endpoint `p = ∞`
is included: there `α = 1`, so a function of `W^{1,∞}(Ω)` is locally Lipschitz in `Ω`.

Morrey's embedding on the whole space, `TauCeti.W1p.exists_holderWith_ae_eq_value`, is proved by
approximation with test functions, which are dense in `W^{1,p}(ℝⁿ)` but not in `W^{1,p}(Ω)`. Here
the estimate is instead a consequence of Morrey's Dirichlet growth theorem
(`TauCeti.W1p.dist_preciseRepresentative_le_of_setIntegral_norm_gradient_le`): by Hölder's
inequality on a ball `B(z, r)`,

`∫_{B(z, r)} ‖∇u‖ ≤ μ(B(z, r))^(1 - 1/p) ‖∇u‖_{Lᵖ(B(z, r))} = ω^(1 - 1/p) r^(n - 1 + α) ‖∇u‖_{Lᵖ}`,

with `ω = μ(B(0, 1))`, which is exactly the growth condition of that theorem.

## Main declarations

* `TauCeti.W1p.setIntegral_ball_norm_gradient_le`: Hölder's inequality on a ball, which gives
  the growth condition.
* `TauCeti.W1p.exists_dist_preciseRepresentative_le`: the local Morrey inequality.
* `TauCeti.W1p.exists_holderOnWith_preciseRepresentative`: the precise representative is
  `α`-Hölder continuous, with constant `C ‖∇u‖_{Lᵖ(Ω)}`, on every set of diameter at most `R` whose
  closed `2R`-thickening lies in `Ω`.
* `TauCeti.W1p.continuousOn_preciseRepresentative`: the precise representative is continuous
  on `Ω`.
* `TauCeti.W1p.exists_holderOnWith_preciseRepresentative_of_isCompact`: it is `α`-Hölder
  continuous on every compact subset of `Ω`.
* `TauCeti.W1p.exists_lipschitzOnWith_preciseRepresentative_of_isCompact`: a function of
  `W^{1,∞}(Ω)` is Lipschitz on every compact subset of `Ω`.
* `TauCeti.W1p.preciseRepresentative_eq_morreyRepresentative`: on the whole space, for finite
  `p > n`, the precise representative is the canonical representative
  `TauCeti.W1p.morreyRepresentative` of the whole-space embedding.

## References

* C. B. Morrey, *Multiple Integrals in the Calculus of Variations*, Theorem 3.5.2.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorems 7.17 and 7.19.
* L. C. Evans, *Partial Differential Equations*, §5.6.2, Theorem 4, and §5.8.2, Theorem 4.
-/

public section

noncomputable section

open Metric Set MeasureTheory Module TopologicalSpace TauCeti.MeasureTheory
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The gradient of a `W^{1,p}` function grows like a power of the radius.** If `B(z, r) ⊆ Ω`,
then by Hölder's inequality

`∫_{B(z, r)} ‖∇u‖ ≤ ω^(1 - 1/p) r^(n (1 - 1/p)) ‖∇u‖_{Lᵖ(B(z, r))}`,

where `n` is the dimension and `ω` is the measure of the unit ball. For `p > n` the exponent
`n (1 - 1/p)` is `n - 1 + α` with `α = 1 - n / p`, which is the growth condition of Morrey's
Dirichlet growth theorem. -/
theorem W1p.setIntegral_ball_norm_gradient_le {Omega : Opens E} (u : W1p mu Omega p) {z : E}
    {r : ℝ} (hr : 0 < r) (hball : ball z r ⊆ (Omega : Set E)) :
    ∫ w in ball z r, ‖W1p.gradient u w‖ ∂mu ≤
      mu.real (ball (0 : E) 1) ^ (1 - 1 / p.toReal) *
        r ^ ((finrank ℝ E : ℝ) * (1 - 1 / p.toReal)) *
          (eLpNorm (W1p.gradient u) p (mu.restrict (ball z r))).toReal := by
  set q : ℝ := 1 - 1 / p.toReal
  have hq : 0 ≤ q := by
    have h1 : (1 : ℝ≥0∞) ≤ p := Fact.out
    rcases eq_or_ne p ∞ with rfl | hptop
    · simp [q]
    · have : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hptop h1
      simp only [q, sub_nonneg]
      exact (div_le_one (by linarith)).2 this
  have hf : AEStronglyMeasurable (W1p.gradient u) (mu.restrict (ball z r)) :=
    (Lp.aestronglyMeasurable _).mono_measure (Measure.restrict_mono hball le_rfl)
  have hfin : eLpNorm (W1p.gradient u) p (mu.restrict (ball z r)) ≠ ∞ :=
    ((eLpNorm_mono_measure _ (Measure.restrict_mono hball le_rfl)).trans_lt
      (Lp.eLpNorm_lt_top _)).ne
  -- Hölder's inequality: `‖f‖_{L¹(B(z, r))} ≤ ‖f‖_{Lᵖ(B(z, r))} μ(B(z, r))^(1 - 1/p)`.
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : (1 : ℝ≥0∞) ≤ p) hf
  rw [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one] at hholder
  calc ∫ w in ball z r, ‖W1p.gradient u w‖ ∂mu
      = (eLpNorm (W1p.gradient u) 1 (mu.restrict (ball z r))).toReal := by
        rw [integral_norm_eq_lintegral_enorm hf, eLpNorm_one_eq_lintegral_enorm hf]
    _ ≤ (eLpNorm (W1p.gradient u) p (mu.restrict (ball z r)) * mu (ball z r) ^ q).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top hfin
          (ENNReal.rpow_ne_top_of_nonneg hq measure_ball_lt_top.ne)) hholder
    _ = (eLpNorm (W1p.gradient u) p (mu.restrict (ball z r))).toReal *
          (r ^ finrank ℝ E * mu.real (ball (0 : E) 1)) ^ q := by
        rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← measureReal_def,
          mu.addHaar_real_ball_of_pos z hr]
    _ = _ := by
        rw [Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast,
          ← Real.rpow_mul hr.le]
        ring

/-- **The local Morrey inequality.** Let `n < p ≤ ∞`, where `n` is the dimension, and let
`α = 1 - n / p`. There is a constant `C > 0`, depending only on `n`, `p` and the Haar measure `μ`,
such that the following holds. Let `u ∈ W^{1,p}(Ω)` and let `x, y` be points with
`closedBall x (2 |x - y|) ⊆ Ω`. Then the precise representative `u*` of `u` satisfies

`|u*(x) - u*(y)| ≤ C ‖∇u‖_{Lᵖ(B(x, 2 |x - y|))} |x - y|^α`. -/
theorem W1p.exists_dist_preciseRepresentative_le (hp : (finrank ℝ E : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens E} (u : W1p mu Omega p) {x y : E},
      closedBall x (2 * dist x y) ⊆ (Omega : Set E) →
        dist (preciseRepresentative mu (W1p.value u) x)
            (preciseRepresentative mu (W1p.value u) y) ≤
          C * (eLpNorm (W1p.gradient u) p (mu.restrict (ball x (2 * dist x y)))).toReal *
            dist x y ^ (((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal : ℝ) := by
  set n := finrank ℝ E
  set α : ℝ≥0 := ((1 : ℝ≥0∞) - n / p).toNNReal
  set q : ℝ := 1 - 1 / p.toReal
  set ω := mu.real (ball (0 : E) 1)
  have hα : 0 < α := ENNReal.toNNReal_one_sub_div_pos hp
  have hexp : (n : ℝ) * q = n - 1 + α := by
    rw [ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_one_sub_div hp.le, ENNReal.toReal_natCast]
    ring
  have hω : 0 < ω :=
    ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne' measure_ball_lt_top.ne
  set K₀ : ℝ := 2 * 2 ^ (α : ℝ) * (2 ^ n / (1 - 2 ^ (-(α : ℝ))))
  have hK₀ : 0 < K₀ := by
    have : (2 : ℝ) ^ (-(α : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 (NNReal.coe_pos.2 hα))
    have : 0 < 1 - (2 : ℝ) ^ (-(α : ℝ)) := by linarith
    positivity
  refine ⟨K₀ * (2 ^ (n + 1) / ω * ω ^ q), by positivity, ?_⟩
  intro Omega u x y hxy
  set B := ball x (2 * dist x y)
  set N := (eLpNorm (W1p.gradient u) p (mu.restrict B)).toReal
  -- On every ball inside `B` the gradient satisfies the growth condition of Morrey's Dirichlet
  -- growth theorem, with `M = ω^(1 - 1/p) N`.
  have hgrowth : ∀ z r, 0 < r → ball z r ⊆ B →
      ∫ w in ball z r, ‖W1p.gradient u w‖ ∂mu ≤ ω ^ q * N * r ^ ((n : ℝ) - 1 + α) := by
    intro z r hr hzr
    have hBΩ : B ⊆ (Omega : Set E) := ball_subset_closedBall.trans hxy
    refine (W1p.setIntegral_ball_norm_gradient_le u hr (hzr.trans hBΩ)).trans ?_
    rw [hexp, mul_right_comm]
    gcongr
    exact W1p.toReal_eLpNorm_gradient_mono u hzr hBΩ
  have hx : ∀ r, 0 < r → r ≤ 2 * dist x y →
      ∫ w in ball x r, ‖W1p.gradient u w‖ ∂mu ≤ ω ^ q * N * r ^ ((n : ℝ) - 1 + α) :=
    fun r hr hr' => hgrowth x r hr (ball_subset_ball hr')
  have hy : ∀ r, 0 < r → r ≤ dist x y →
      ∫ w in ball y r, ‖W1p.gradient u w‖ ∂mu ≤ ω ^ q * N * r ^ ((n : ℝ) - 1 + α) := by
    intro r hr hr'
    refine hgrowth y r hr fun w hw => ?_
    rw [mem_ball] at hw ⊢
    linarith [dist_triangle w y x, dist_comm x y]
  refine (W1p.dist_preciseRepresentative_le_of_setIntegral_norm_gradient_le
    (NNReal.coe_pos.2 hα) u hxy hx hy).trans_eq ?_
  ring

/-- **Morrey's embedding in the interior of a domain.** Let `n < p ≤ ∞`, where `n` is the
dimension, and let `α = 1 - n / p`. There is a constant `C > 0`, depending only on `n`, `p` and the
Haar measure `μ`, such that the following holds. Let `u ∈ W^{1,p}(Ω)`, and let `K` be a set of
diameter at most `R` whose closed `2R`-thickening lies in `Ω`. Then the precise representative of
`u` is `α`-Hölder continuous on `K` with constant `C ‖∇u‖_{Lᵖ(Ω)}`. -/
theorem W1p.exists_holderOnWith_preciseRepresentative (hp : (finrank ℝ E : ℝ≥0∞) < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Omega : Opens E} (u : W1p mu Omega p) {K : Set E} {R : ℝ},
      (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ R) → cthickening (2 * R) K ⊆ (Omega : Set E) →
        HolderOnWith (C * ‖W1p.gradient u‖).toNNReal ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
          (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨C, hC, hdist⟩ := W1p.exists_dist_preciseRepresentative_le (mu := mu) hp
  refine ⟨C, hC, fun {Omega} u K R hKR hK => HolderOnWith.of_dist_le fun x hx y hy => ?_⟩
  have hxy : closedBall x (2 * dist x y) ⊆ (Omega : Set E) :=
    ((closedBall_subset_closedBall (by linarith [hKR x hx y hy])).trans
      (closedBall_subset_cthickening hx _)).trans hK
  refine (hdist u hxy).trans ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  gcongr
  exact (W1p.toReal_eLpNorm_gradient_mono u (ball_subset_closedBall.trans hxy)
    subset_rfl).trans_eq (Lp.norm_def _).symm

/-- **Continuity of `W^{1,p}` functions for `p` above the dimension.** If `n < p ≤ ∞`, where `n`
is the dimension, the precise representative of any `u ∈ W^{1,p}(Ω)`, which agrees with `u` almost
everywhere on `Ω`, is continuous on `Ω`. -/
theorem W1p.continuousOn_preciseRepresentative (hp : (finrank ℝ E : ℝ≥0∞) < p)
    {Omega : Opens E} (u : W1p mu Omega p) :
    ContinuousOn (preciseRepresentative mu (W1p.value u)) Omega := by
  obtain ⟨C, -, hhol⟩ := W1p.exists_holderOnWith_preciseRepresentative (mu := mu) hp
  intro x hx
  obtain ⟨ε, hε, hsub⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  have hε5 : 0 < ε / 5 := by positivity
  -- On `closedBall x (ε / 5)`, of diameter at most `2ε / 5`, whose closed `4ε / 5`-thickening
  -- is `closedBall x ε ⊆ Ω`, the precise representative is Hölder continuous.
  have hK := hhol u (K := closedBall x (ε / 5)) (R := 2 * (ε / 5))
    (fun a ha b hb => by
      rw [mem_closedBall] at ha hb
      linarith [dist_triangle a x b, dist_comm b x])
    (by
      rw [cthickening_closedBall (by positivity) hε5.le]
      exact (closedBall_subset_closedBall (by linarith)).trans hsub)
  exact ((hK.continuousOn (ENNReal.toNNReal_one_sub_div_pos hp)).continuousAt
    (closedBall_mem_nhds x hε5)).continuousWithinAt

/-- **Morrey's embedding on compact subsets.** If `n < p ≤ ∞`, where `n` is the dimension, the
precise representative of any `u ∈ W^{1,p}(Ω)` is Hölder continuous with exponent `1 - n / p` on
every compact subset of `Ω`. -/
theorem W1p.exists_holderOnWith_preciseRepresentative_of_isCompact
    (hp : (finrank ℝ E : ℝ≥0∞) < p) {Omega : Opens E} (u : W1p mu Omega p) {K : Set E}
    (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set E)) :
    ∃ C : ℝ≥0, HolderOnWith C ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
      (preciseRepresentative mu (W1p.value u)) K := by
  set α := ((1 : ℝ≥0∞) - finrank ℝ E / p).toNNReal
  set f := preciseRepresentative mu (W1p.value u)
  obtain ⟨C, hC, hdist⟩ := W1p.exists_dist_preciseRepresentative_le (mu := mu) hp
  obtain ⟨R, hR, hRK⟩ := hK.exists_cthickening_subset_open Omega.isOpen hKΩ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((W1p.continuousOn_preciseRepresentative hp u).mono hKΩ)
  set L := max (C * ‖W1p.gradient u‖) (2 * M * (2 / R) ^ (α : ℝ))
  refine ⟨L.toNNReal, HolderOnWith.of_dist_le fun x hx y hy => ?_⟩
  rw [Real.coe_toNNReal _ ((mul_nonneg hC.le (norm_nonneg _)).trans (le_max_left _ _))]
  rcases le_or_gt (dist x y) (R / 2) with hd | hd
  · -- Nearby points: the local Morrey inequality on `closedBall x (2 |x - y|) ⊆ Ω`.
    have hxy : closedBall x (2 * dist x y) ⊆ (Omega : Set E) :=
      ((closedBall_subset_cthickening hx _).trans (cthickening_mono (by linarith) K)).trans hRK
    refine (hdist u hxy).trans ?_
    gcongr
    refine le_trans ?_ (le_max_left _ _)
    gcongr
    exact (W1p.toReal_eLpNorm_gradient_mono u (ball_subset_closedBall.trans hxy)
      subset_rfl).trans_eq (Lp.norm_def _).symm
  · -- Distant points: `|f x - f y| ≤ 2M ≤ 2M (2 |x - y| / R)^α`.
    have hone : 1 ≤ (2 / R * dist x y) ^ (α : ℝ) :=
      Real.one_le_rpow (by rw [div_mul_eq_mul_div, le_div_iff₀ hR]; linarith) α.coe_nonneg
    calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * M * 1 := by linarith [hM x hx, hM y hy]
      _ ≤ 2 * M * (2 / R * dist x y) ^ (α : ℝ) := by
          gcongr
          linarith [(norm_nonneg (f x)).trans (hM x hx)]
      _ = 2 * M * (2 / R) ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
          rw [Real.mul_rpow (by positivity) dist_nonneg]
          ring
      _ ≤ L * dist x y ^ (α : ℝ) := by gcongr; exact le_max_right _ _

/-- **`W^{1,∞}` functions are locally Lipschitz.** The precise representative of any
`u ∈ W^{1,∞}(Ω)` is Lipschitz on every compact subset of `Ω`. -/
theorem W1p.exists_lipschitzOnWith_preciseRepresentative_of_isCompact {Omega : Opens E}
    (u : W1p mu Omega ∞) {K : Set E} (hK : IsCompact K) (hKΩ : K ⊆ (Omega : Set E)) :
    ∃ C : ℝ≥0, LipschitzOnWith C (preciseRepresentative mu (W1p.value u)) K := by
  obtain ⟨C, hC⟩ := W1p.exists_holderOnWith_preciseRepresentative_of_isCompact
    (ENNReal.natCast_lt_top _) u hK hKΩ
  simp only [ENNReal.div_top, tsub_zero, ENNReal.toNNReal_one] at hC
  exact ⟨C, holderOnWith_one.1 hC⟩

/-- On the whole space, for finite `p` above the dimension, the precise representative of
`u ∈ W^{1,p}(ℝⁿ)` is the canonical Morrey representative `TauCeti.W1p.morreyRepresentative`: both
are continuous and agree with `u` almost everywhere. -/
theorem W1p.preciseRepresentative_eq_morreyRepresentative {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (u : W1p mu ⊤ (p : ℝ≥0∞)) (hp : (finrank ℝ E : ℝ≥0) < p) :
    preciseRepresentative mu (W1p.value u) = W1p.morreyRepresentative u hp := by
  have hcont : Continuous (preciseRepresentative mu (W1p.value u)) := by
    rw [← continuousOn_univ]
    simpa using W1p.continuousOn_preciseRepresentative (by exact_mod_cast hp) u
  refine (hcont.ae_eq_iff_eq mu (W1p.continuous_morreyRepresentative u hp)).1 ?_
  have hae : W1p.value u =ᵐ[mu.restrict univ] preciseRepresentative mu (W1p.value u) :=
    W1p.ae_eq_preciseRepresentative u
  rw [Measure.restrict_univ] at hae
  exact hae.symm.trans (W1p.value_ae_eq_morreyRepresentative u hp)

end TauCeti
