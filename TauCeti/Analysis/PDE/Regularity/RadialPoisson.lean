/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.PDE.WeakLaplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.NormRpow
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# Poisson's equation with a radial power datum

On a bounded open set `Ω ⊆ ℝᵈ`, `d ≥ 1`, the radial function

`w(x) = -‖x‖ ^ (2 - γ) / ((2 - γ) (d - γ))`

is a weak solution of Poisson's equation `-Δw = ‖x‖ ^ (-γ)` across the origin, for `γ < 1`, and
for `γ = 1` when `d ≥ 2`. Its gradient `∇w(x) = -‖x‖ ^ (-γ) x / (d - γ)` has size
`‖x‖ ^ (1 - γ) / (d - γ)`. These solutions show that the interior Schauder estimate for
divergence-form equations with a scalar datum,
`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`,
is sharp in its datum: for `f ∈ Lᵠ` with `q > d` and `q ≥ 2` (automatic from `q > d` when `d ≥ 2`),
it makes `∇u` Hölder continuous with every exponent `β < 1` with `β ≤ 1 - d / q` (and `β ≤ α`, the
coefficient exponent, which for the Laplacian is arbitrary).

* **The exponent `1 - d / q` cannot be raised.** The datum `‖x‖ ^ (-γ)` lies in `Lᵠ(Ω)` when
  `γ q < d`, while `∇w` vanishes at the origin and has length `t ^ (1 - γ) / (d - γ)` at distance
  `t`, so it is not Hölder at the origin with any exponent larger than `1 - γ`.
  Letting `γ ↑ d / q` shows that every exponent `β > 1 - d / q` fails for some datum in `Lᵠ`
  (`TauCeti.PDE.exists_memLp_forall_energyFormH1_eq_and_not_holderOnWith_gradient`).
* **Integrability below `q = d` does not even give continuity.** For `γ = 1` and `d ≥ 2`, the
  datum `‖x‖⁻¹` lies in `Lᵠ(Ω)` for every `q < d`
  (`Bornology.IsBounded.memLp_norm_inv_restrict`), though, when `Ω` contains the origin, not for
  `q = d` (`TauCeti.not_memLp_norm_inv_closedBall`), and the
  gradient `-x / ((d - 1) ‖x‖)` of the solution `-‖x‖ / (d - 1)` has no representative continuous
  at the origin (`TauCeti.PDE.exists_forall_energyFormH1_eq_and_not_continuousAt_gradient`).

The weak equation is the divergence identity `∫ Δφ w = ∫ φ div ∇w` for the radial field
`x ↦ ‖x‖ ^ (-γ) • x`, whose weak derivative is its classical one across the origin
(`TauCeti.hasWeakFDerivOn_norm_rpow_smul_self`,
`TauCeti.hasWeakFDerivOn_norm_rpow_neg_one_smul_self`) and whose divergence is
`(d - γ) ‖x‖ ^ (-γ)` (`TauCeti.trace_rpow_smul_id_add_smulRight`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Theorem 8.32 (the interior `C^{1,α}` estimate in divergence form).
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5 (Schauder estimates for equations in
  divergence form with data in Morrey spaces).
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open InnerProductSpace MeasureTheory Metric Set Filter Topology TopologicalSpace
open scoped ENNReal NNReal Distributions Gradient RealInnerProductSpace

variable {ι : Type*} [Fintype ι] {γ : ℝ}

/-! ### The radial solutions -/

/-- The radial solution `-‖x‖ ^ (2 - γ) / ((2 - γ) (d - γ))` of `-Δw = ‖x‖ ^ (-γ)`. -/
private def radialSolution (γ : ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  -(‖x‖ ^ (2 - γ)) / ((2 - γ) * (Fintype.card ι - γ))

/-- The gradient `-‖x‖ ^ (-γ) x / (d - γ)` of the radial solution. -/
private def radialGradient (γ : ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (-(Fintype.card ι - γ)⁻¹) • (‖x‖ ^ (-γ) • x)

private theorem radialSolution_continuous (hγ : γ < 2) :
    Continuous (radialSolution (ι := ι) γ) :=
  ((continuous_norm.rpow_const fun _ ↦ Or.inr (by linarith)).neg).div_const _

/-- Away from the origin, the radial gradient has length `‖x‖ ^ (1 - γ) / |d - γ|`. -/
private theorem norm_radialGradient {x : EuclideanSpace ℝ ι} (hx : x ≠ 0) :
    ‖radialGradient γ x‖ = |Fintype.card ι - γ|⁻¹ * ‖x‖ ^ (1 - γ) := by
  have h : ‖x‖ ^ (-γ) * ‖x‖ = ‖x‖ ^ (1 - γ) := by
    rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hx), neg_add_eq_sub]
  simp [radialGradient, norm_smul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _), h]

private theorem norm_radialGradient_le (x : EuclideanSpace ℝ ι) :
    ‖radialGradient γ x‖ ≤ |Fintype.card ι - γ|⁻¹ * ‖x‖ ^ (1 - γ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [radialGradient, smul_zero, norm_zero]
    positivity
  exact (norm_radialGradient hx).le

/-- The radial solution has the radial gradient as weak gradient on every open set. -/
private theorem hasWeakFDerivOn_radialSolution [Nonempty ι] (hγ : γ < 2)
    (Ω : Opens (EuclideanSpace ℝ ι)) :
    HasWeakFDerivOn volume Ω (radialSolution (ι := ι) γ)
      (fun x ↦ innerSL ℝ (radialGradient γ x)) := by
  have hd : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := (hasWeakFDerivOn_norm_rpow (μ := volume) (E := EuclideanSpace ℝ ι) (s := 2 - γ)
    (by rw [finrank_euclideanSpace]; linarith) Ω).const_smul
      (-((2 - γ) * (Fintype.card ι - γ))⁻¹)
  have h2 : 2 - γ ≠ 0 := by linarith
  refine (h.congr_ae (Eventually.of_forall fun x ↦ ?_)).congr_ae_deriv
    (Eventually.of_forall fun x ↦ ?_)
  · simp only [Pi.smul_apply, smul_eq_mul, radialSolution]
    ring
  · ext v
    simp only [Pi.smul_apply, smul_apply, innerSL_apply_apply, smul_eq_mul,
      radialGradient, inner_smul_left, RCLike.conj_to_real]
    rw [show 2 - γ - 2 = -γ by ring, mul_inv]
    linear_combination (-(Fintype.card ι - γ)⁻¹ * ‖x‖ ^ (-γ) * ⟪x, v⟫) *
      inv_mul_cancel₀ h2

/-- **The weak equation.** If the radial field `‖x‖ ^ (-γ) • x` has its classical derivative as
weak derivative, then an element of `H¹(Ω)` equal to the radial solution is a weak solution of
`-Δw = ‖x‖ ^ (-γ)`. -/
private theorem energyFormH1_eq_of_value_ae_eq [DecidableEq ι] [Nonempty ι] (hγ : γ < 2)
    (hγd : γ ≠ Fintype.card ι) {Ω : Opens (EuclideanSpace ℝ ι)}
    (hD : HasWeakFDerivOn volume Ω (fun x : EuclideanSpace ℝ ι ↦ ‖x‖ ^ (-γ) • x)
      (fun x ↦ ‖x‖ ^ (-γ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι) +
        ((-γ * ‖x‖ ^ (-γ - 2)) • innerSL ℝ x).smulRight x))
    {u : W1p volume Ω 2} (hu : W1p.value u =ᵐ[volume.restrict Ω] radialSolution γ)
    (φ : 𝓓(Ω, ℝ)) :
    energyFormH1 (fun _ ↦ 1) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
      ∫ x in Ω, ‖x‖ ^ (-γ) * φ x := by
  have hg : HasWeakFDerivOn volume Ω (radialGradient (ι := ι) γ) _ :=
    (hD.const_smul (-(Fintype.card ι - γ)⁻¹)).congr_ae
      (Eventually.of_forall fun _ ↦ by simp only [radialGradient, Pi.smul_apply])
  rw [energyFormH1_one_zero_zero_ofTestFunctionₗ_eq_neg_integral_laplacian_smul hu,
    (hasWeakFDerivOn_radialSolution hγ Ω).integral_laplacian_smul_eq_integral_smul_trace hg φ,
    ← integral_neg, ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp [φ.zero_on_compl hx]]
  refine setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦ ?_
  have hdγ : (Fintype.card ι : ℝ) - γ ≠ 0 := sub_ne_zero.2 hγd.symm
  simp only [Pi.smul_apply, ContinuousLinearMap.toLinearMap_smul, map_smul,
    trace_rpow_smul_id_add_smulRight, finrank_euclideanSpace, smul_eq_mul]
  field_simp
  ring

/-- On a bounded open set, the radial solution with `γ ≤ 1` lies in `H¹(Ω)`. -/
private theorem exists_w1p_radialSolution [Nonempty ι] (hγ : γ ≤ 1)
    {Ω : Opens (EuclideanSpace ℝ ι)} (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) :
    ∃ u : W1p volume Ω 2, W1p.value u =ᵐ[volume.restrict Ω] radialSolution γ ∧
      W1p.gradient u =ᵐ[volume.restrict Ω] radialGradient γ := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : EuclideanSpace ℝ ι)
  have : IsFiniteMeasure (volume.restrict (Ω : Set (EuclideanSpace ℝ ι))) :=
    isFiniteMeasure_restrict.2 hb.measure_lt_top.ne
  -- The solution is continuous, hence bounded on the compact closed ball.
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ ι) R).exists_bound_of_continuousOn
    (radialSolution_continuous (ι := ι) (by linarith)).continuousOn
  have hw : MemLp (radialSolution (ι := ι) γ) 2 (volume.restrict Ω) :=
    MemLp.of_bound (radialSolution_continuous (by linarith)).aestronglyMeasurable M
      ((ae_restrict_mem Ω.isOpen.measurableSet).mono fun x hx ↦ hM x (hR hx))
  -- The gradient is bounded by `|d - γ|⁻¹ R ^ (1 - γ)` on the ball.
  have hmeas : Measurable (radialGradient (ι := ι) γ) := by
    unfold radialGradient
    fun_prop
  have hg : MemLp (radialGradient (ι := ι) γ) 2 (volume.restrict Ω) := by
    refine MemLp.of_bound hmeas.aestronglyMeasurable
      (|Fintype.card ι - γ|⁻¹ * R ^ (1 - γ)) ((ae_restrict_mem Ω.isOpen.measurableSet).mono
        fun x hx ↦ (norm_radialGradient_le x).trans ?_)
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg x) (by simpa using hR hx) (by linarith)) (by positivity)
  refine ⟨W1p.mk hw.toLp hg.toLp
    (((hasWeakFDerivOn_radialSolution (by linarith) Ω).congr_ae
      hw.coeFn_toLp.symm).congr_ae_deriv (hg.coeFn_toLp.mono fun x hx ↦ by simp only [hx])),
    ?_, ?_⟩
  · rw [W1p.value_mk]
    exact hw.coeFn_toLp
  · rw [W1p.gradient_mk]
    exact hg.coeFn_toLp

/-- For `γ < 1` the radial gradient is continuous, also at the origin. -/
private theorem radialGradient_continuous (hγ : γ < 1) :
    Continuous (radialGradient (ι := ι) γ) := by
  unfold radialGradient
  exact (continuous_norm_rpow_smul_self (E := EuclideanSpace ℝ ι)
    (by linarith : -1 < -γ)).const_smul (-((Fintype.card ι : ℝ) - γ)⁻¹)

/-- For `β > 1 - γ`, the radial gradient is not `β`-Hölder on any ball about the origin: it
vanishes at the origin and has length `t ^ (1 - γ) / (d - γ)` at distance `t`. -/
private theorem not_holderOnWith_radialGradient [Nonempty ι] (hγ : γ < 1) {β : ℝ≥0}
    (hβ : 1 - γ < β) {r : ℝ} (hr : 0 < r) (C : ℝ≥0) :
    ¬ HolderOnWith C β (radialGradient (ι := ι) γ) (ball 0 r) := by
  classical
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have hd : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hdγ : 0 < (Fintype.card ι : ℝ) - γ := by linarith
  set c : ℝ := ((Fintype.card ι : ℝ) - γ)⁻¹
  have hc0 : 0 < c := inv_pos.2 hdγ
  set ε : ℝ := β - (1 - γ) with hε
  have hε0 : 0 < ε := by linarith
  -- `C t ^ ε → 0` as `t → 0⁺`, so for small `t > 0` it is below `c`.
  have hlim : Tendsto (fun t : ℝ ↦ (C : ℝ) * t ^ ε) (𝓝[>] 0) (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 ε (Or.inr hε0.le)).tendsto).const_mul (C : ℝ)
    rw [Real.zero_rpow hε0.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨t, ht, htr⟩ := ((hlim.eventually (gt_mem_nhds hc0)).and (Ioo_mem_nhdsGT hr)).exists
  have ht0 : 0 < t := htr.1
  have hnorm : ‖t • e‖ = t := by rw [norm_smul, he, mul_one, Real.norm_of_nonneg ht0.le]
  have hmem : t • e ∈ ball (0 : EuclideanSpace ℝ ι) r := by
    rw [mem_ball_zero_iff, hnorm]
    exact htr.2
  have hdist := h.dist_le hmem (mem_ball_self hr)
  have hg0 : radialGradient (ι := ι) γ 0 = 0 := by simp [radialGradient]
  have hgt : ‖radialGradient γ (t • e)‖ = c * t ^ (1 - γ) := by
    rw [norm_radialGradient (by rw [← norm_ne_zero_iff, hnorm]; exact ht0.ne'), abs_of_pos hdγ,
      hnorm]
  have htβ : t ^ (β : ℝ) = t ^ ε * t ^ (1 - γ) := by
    rw [← Real.rpow_add ht0, hε]
    congr 1
    ring
  simp only [hg0, dist_zero_right, hgt, hnorm, htβ] at hdist
  have hpos : 0 < t ^ (1 - γ) := Real.rpow_pos_of_pos ht0 _
  nlinarith [mul_lt_mul_of_pos_right ht hpos]

/-- **The Morrey gain `1 - d / q` in the divergence-form Schauder estimate is sharp.** Let
`Ω ⊆ ℝᵈ`, `d ≥ 1`, be a bounded open set, let `0 < q < ∞`, and let `β > 0` with `β > 1 - d / q`.
Then there are a datum `f ∈ Lᵠ(Ω)` and a weak solution `u ∈ H¹(Ω)` of Poisson's equation
`-Δu = f`, that is `∫_Ω ∇φ · ∇u = ∫_Ω f φ` for every test function `φ`, such that no
representative of `∇u` is `β`-Hölder on any ball about the origin contained in `Ω`.

For `q > d` with `q ≥ 2`, the Schauder estimate
`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`
gives a `β`-Hölder representative of `∇u` for every `β < 1` with `β ≤ 1 - d / q` (the coefficient
`a = 1` being `α`-Hölder for every `α`); this theorem shows that `1 - d / q` cannot be replaced by
a larger exponent. The proof takes the datum `‖x‖ ^ (-γ)` and the radial solution
`-‖x‖ ^ (2 - γ) / ((2 - γ) (d - γ))`, for a `γ < d / q` with `1 - γ < β`. -/
theorem exists_memLp_forall_energyFormH1_eq_and_not_holderOnWith_gradient [DecidableEq ι]
    [Nonempty ι] {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞) {β : ℝ≥0} (hβ0 : 0 < β)
    (hβ : 1 - Fintype.card ι / q.toReal < β) {Ω : Opens (EuclideanSpace ℝ ι)}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι))) :
    ∃ f : EuclideanSpace ℝ ι → ℝ, MemLp f q (volume.restrict Ω) ∧
      ∃ u : W1p volume Ω 2,
        (∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun _ ↦ 1) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
          ∫ x in Ω, f x * φ x) ∧
        ∀ r : ℝ, 0 < r → ball (0 : EuclideanSpace ℝ ι) r ⊆ (Ω : Set (EuclideanSpace ℝ ι)) →
          ∀ (C : ℝ≥0) (g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι),
            g =ᵐ[volume.restrict (ball 0 r)] W1p.gradient u → ¬ HolderOnWith C β g (ball 0 r) := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hdq : 0 < (Fintype.card ι : ℝ) / q.toReal := div_pos (by exact_mod_cast Fintype.card_pos) hqr
  have hβ0' : (0 : ℝ) < β := hβ0
  -- Choose `γ` strictly between `max 0 (1 - β)` and `min 1 (d / q)`.
  obtain ⟨γ, hγ0, hγ1, hγβ, hγq⟩ : ∃ γ : ℝ, 0 < γ ∧ γ < 1 ∧ 1 - γ < β ∧
      γ < (Fintype.card ι : ℝ) / q.toReal := by
    obtain ⟨γ, hlo, hhi⟩ := exists_between
      (max_lt (lt_min one_pos hdq) (lt_min (by linarith) (by linarith)) :
        max 0 (1 - (β : ℝ)) < min 1 ((Fintype.card ι : ℝ) / q.toReal))
    exact ⟨γ, (le_max_left _ _).trans_lt hlo, hhi.trans_le (min_le_left _ _),
      by linarith [le_max_right 0 (1 - (β : ℝ))], hhi.trans_le (min_le_right _ _)⟩
  -- `‖x‖ ^ (-γ) ∈ Lᵠ(Ω)` since `γ q < d`.
  refine ⟨fun x ↦ ‖x‖ ^ (-γ), hb.memLp_norm_rpow_restrict hq ?_, ?_⟩
  · rw [finrank_euclideanSpace]
    linarith [(lt_div_iff₀ hqr).1 hγq]
  obtain ⟨u, hu, hgu⟩ := exists_w1p_radialSolution hγ1.le hb
  have hγd : γ ≠ Fintype.card ι := by
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    linarith
  refine ⟨u, fun φ ↦ energyFormH1_eq_of_value_ae_eq (by linarith) hγd
    (hasWeakFDerivOn_norm_rpow_smul_self (by linarith) Ω) hu φ, ?_⟩
  intro r hr hball C g hg hH
  -- On the ball, `g` agrees almost everywhere with the continuous radial gradient, hence
  -- everywhere, and the radial gradient is not `β`-Hölder.
  have hae : g =ᵐ[volume.restrict (ball 0 r)] radialGradient γ :=
    hg.trans (ae_restrict_of_ae_restrict_of_subset hball hgu)
  have heq : EqOn g (radialGradient γ) (ball 0 r) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_ball (hH.continuousOn hβ0)
      (radialGradient_continuous hγ1).continuousOn
  exact not_holderOnWith_radialGradient hγ1 hγβ hr C fun x hx y hy ↦ by
    rw [← heq hx, ← heq hy]
    exact hH x hx y hy

/-- A point of the ball `B(σ s e, s / 2)`, for a unit vector `e` and `|σ| = 1`, has norm less than
`3 s / 2` and component `σ ⟪x, e⟫` greater than `s / 2`. -/
private theorem norm_lt_and_lt_mul_inner_of_mem_ball {e x : EuclideanSpace ℝ ι} (he : ‖e‖ = 1)
    {σ s : ℝ} (hσ : |σ| = 1) (hs : 0 < s) (hx : x ∈ ball (σ • s • e) (s / 2)) :
    ‖x‖ < 3 * s / 2 ∧ s / 2 < σ * ⟪x, e⟫ := by
  rw [mem_ball, dist_eq_norm] at hx
  have hσe : ‖σ • s • e‖ = s := by
    rw [norm_smul, norm_smul, he, Real.norm_eq_abs, hσ, Real.norm_of_nonneg hs.le]
    ring
  have hinner : σ * ⟪x, e⟫ = s + σ * ⟪x - σ • s • e, e⟫ := by
    rw [inner_sub_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq, he]
    simp only [RCLike.conj_to_real]
    have : σ * σ = 1 := by rw [← abs_mul_abs_self, hσ, one_mul]
    linear_combination (s : ℝ) * this
  have hbound : |σ * ⟪x - σ • s • e, e⟫| ≤ ‖x - σ • s • e‖ := by
    rw [abs_mul, hσ, one_mul]
    simpa [he] using abs_real_inner_le_norm (x - σ • s • e) e
  refine ⟨?_, ?_⟩
  · calc ‖x‖ = ‖σ • s • e + (x - σ • s • e)‖ := by rw [add_sub_cancel]
      _ ≤ ‖σ • s • e‖ + ‖x - σ • s • e‖ := norm_add_le _ _
      _ < 3 * s / 2 := by rw [hσe]; linarith
  · rw [hinner]
    linarith [neg_abs_le (σ * ⟪x - σ • s • e, e⟫)]

/-- Where `σ ⟪x, e⟫ > ‖x‖ / 3`, the component `-σ ⟪∇w(x), e⟫ = σ ⟪x, e⟫ / ((d - 1) ‖x‖)` of the
unit radial gradient exceeds `1 / (3 (d - 1))`. -/
private theorem lt_mul_neg_inner_radialGradient_one (hd : 1 < Fintype.card ι)
    {e x : EuclideanSpace ℝ ι} {σ : ℝ} (h : ‖x‖ < 3 * σ * ⟪x, e⟫) :
    ((Fintype.card ι : ℝ) - 1)⁻¹ / 3 < σ * -⟪radialGradient 1 x, e⟫ := by
  have hd' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hc0 : 0 < ((Fintype.card ι : ℝ) - 1)⁻¹ := inv_pos.2 (by linarith)
  have hxpos : 0 < ‖x‖ := by
    rcases (norm_nonneg x).lt_or_eq with h' | h'
    · exact h'
    · rw [eq_comm, norm_eq_zero] at h'
      simp [h'] at h
  have h3 : 1 / 3 < σ * ⟪x, e⟫ / ‖x‖ := by
    rw [lt_div_iff₀ hxpos]
    linarith
  rw [radialGradient, inner_smul_left, inner_smul_left, Real.rpow_neg_one]
  simp only [RCLike.conj_to_real]
  have heq : σ * -(-((Fintype.card ι : ℝ) - 1)⁻¹ * (‖x‖⁻¹ * ⟪x, e⟫)) =
      ((Fintype.card ι : ℝ) - 1)⁻¹ * (σ * ⟪x, e⟫ / ‖x‖) := by
    ring
  rw [heq]
  nlinarith [mul_lt_mul_of_pos_left h3 hc0]

/-- The unit radial gradient `-x / ((d - 1) ‖x‖)` has no representative continuous at the origin:
on the balls `B(±s e, s / 2)` its component along `e` stays beyond `1 / (3 (d - 1))` in absolute
value, with opposite signs. -/
private theorem not_continuousAt_of_ae_eq_radialGradient_one [Nonempty ι]
    (hd : 1 < Fintype.card ι) {Ω : Opens (EuclideanSpace ℝ ι)}
    (h0 : (0 : EuclideanSpace ℝ ι) ∈ Ω) {g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hg : g =ᵐ[volume.restrict Ω] radialGradient 1) : ¬ ContinuousAt g 0 := by
  classical
  intro hc
  obtain ⟨i⟩ := ‹Nonempty ι›
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have hd' : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  set c : ℝ := ((Fintype.card ι : ℝ) - 1)⁻¹
  have hc0 : 0 < c := inv_pos.2 (by linarith)
  obtain ⟨δ, hδ, hδg⟩ := Metric.continuousAt_iff.1 hc (c / 3) (div_pos hc0 three_pos)
  obtain ⟨ρ, hρ, hρΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen 0 h0
  set s : ℝ := min δ ρ / 2 with hs_def
  have hs : 0 < s := by positivity
  have hsδ : 3 * s / 2 ≤ δ := by have := min_le_left δ ρ; linarith
  have hsρ : 3 * s / 2 ≤ ρ := by have := min_le_right δ ρ; linarith
  -- On `B(σ s e, s / 2)` with `|σ| = 1`, which lies in `Ω` and within `δ` of the origin, almost
  -- every point has `g = ∇w`; the ball has positive measure, so some point does.
  have key : ∀ σ : ℝ, |σ| = 1 → ∃ x, g x = radialGradient 1 x ∧ dist (g x) (g 0) < c / 3 ∧
      c / 3 < σ * -⟪radialGradient 1 x, e⟫ := by
    intro σ hσ
    have hsub : ball (σ • s • e) (s / 2) ⊆ (Ω : Set (EuclideanSpace ℝ ι)) := fun x hx ↦
      hρΩ (mem_ball_zero_iff.2
        ((norm_lt_and_lt_mul_inner_of_mem_ball he hσ hs hx).1.trans_le hsρ))
    have : (ae (volume.restrict (ball (σ • s • e) (s / 2)))).NeBot :=
      ae_restrict_neBot.2 (measure_ball_pos volume _ (by positivity)).ne'
    obtain ⟨x, hxg, hx⟩ := ((ae_restrict_of_ae_restrict_of_subset hsub hg).and
      (ae_restrict_mem measurableSet_ball)).exists
    obtain ⟨hxn, hxe⟩ := norm_lt_and_lt_mul_inner_of_mem_ball he hσ hs hx
    exact ⟨x, hxg, hδg (by rw [dist_zero_right]; linarith),
      lt_mul_neg_inner_radialGradient_one hd (by linarith)⟩
  -- At the two points the components along `e` differ by more than `2 c / 3`, while `g` moves
  -- them by less than `c / 3` each from `g 0`.
  obtain ⟨x₁, hx₁g, hx₁d, hx₁⟩ := key 1 (by norm_num)
  obtain ⟨x₂, hx₂g, hx₂d, hx₂⟩ := key (-1) (by norm_num)
  have hdist : dist (radialGradient 1 x₂) (radialGradient 1 x₁) < 2 * c / 3 := by
    rw [← hx₁g, ← hx₂g]
    linarith [dist_triangle_right (g x₂) (g x₁) (g 0)]
  have hinner : ⟪radialGradient 1 x₂ - radialGradient 1 x₁, e⟫ ≤
      dist (radialGradient 1 x₂) (radialGradient 1 x₁) := by
    rw [dist_eq_norm]
    simpa [he] using real_inner_le_norm (radialGradient 1 x₂ - radialGradient 1 x₁) e
  rw [inner_sub_left] at hinner
  linarith

/-- **Integrability of the datum below `q = d` does not give a continuous gradient.** Let `d ≥ 2`
and let `Ω ⊆ ℝᵈ` be a bounded open set containing the origin. There is a weak solution
`u ∈ H¹(Ω)` of `-Δu = ‖x‖⁻¹`, that is `∫_Ω ∇φ · ∇u = ∫_Ω ‖x‖⁻¹ φ` for every test function `φ`,
whose gradient has no representative continuous at the origin. The proof takes the radial solution
`-‖x‖ / (d - 1)`, whose gradient is `-x / ((d - 1) ‖x‖)`.

The datum `‖x‖⁻¹` lies in `Lᵠ(Ω)` for every `q < d`
(`Bornology.IsBounded.memLp_norm_inv_restrict`), though it just misses `Lᵈ(Ω)`
(`TauCeti.not_memLp_norm_inv_closedBall`). So a datum in every `Lᵠ` with `q < d` can give a
solution whose gradient is not even continuous, let alone Hölder as in the Schauder estimate
`exists_holderOnWith_preciseRepresentative_gradient_of_holderOnWith_matrixBilinearForm_of_memLp`
for `q > d`. -/
theorem exists_forall_energyFormH1_eq_and_not_continuousAt_gradient [DecidableEq ι]
    (hd : 1 < Fintype.card ι) {Ω : Opens (EuclideanSpace ℝ ι)}
    (hb : Bornology.IsBounded (Ω : Set (EuclideanSpace ℝ ι)))
    (h0 : (0 : EuclideanSpace ℝ ι) ∈ Ω) :
    ∃ u : W1p volume Ω 2,
      (∀ φ : 𝓓(Ω, ℝ), energyFormH1 (fun _ ↦ 1) 0 0 u (W1p.ofTestFunctionₗ volume Ω 2 φ) =
          ∫ x in Ω, ‖x‖⁻¹ * φ x) ∧
      ∀ g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι,
        g =ᵐ[volume.restrict Ω] W1p.gradient u → ¬ ContinuousAt g 0 := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨u, hu, hgu⟩ := exists_w1p_radialSolution (ι := ι) (γ := 1) le_rfl hb
  have hγd : (1 : ℝ) ≠ Fintype.card ι := by
    have : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    exact this.ne
  refine ⟨u, fun φ ↦ ?_, fun g hg ↦
    not_continuousAt_of_ae_eq_radialGradient_one hd h0 (hg.trans hgu)⟩
  rw [energyFormH1_eq_of_value_ae_eq (by norm_num) hγd
    (hasWeakFDerivOn_norm_rpow_neg_one_smul_self (by rwa [finrank_euclideanSpace]) Ω) hu φ]
  simp only [Real.rpow_neg_one]

end PDE

end TauCeti
