/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
public import TauCeti.MeasureTheory.Function.Campanato
import Mathlib.Analysis.Convex.Integral
import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
import TauCeti.Analysis.SpecificLimits.DecayIteration
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos
import TauCeti.Topology.MetricSpace.Holder

/-!
# Hölder continuity of the gradient for `-Δu = -div G`

Let `u ∈ H¹(Ω)` be a weak solution of `-Δu = -div G` in an open set `Ω ⊆ ℝ^{n+1}`, that is

`∫_Ω ⟨∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ` on `Ω`,

and let `0 < α < 1`. This file proves that `∇u` is as regular as `G` in the interior: if the closed
`R`-thickening `S_R` of a set `S` lies in `Ω` and `G` is `α`-Hölder on `S_R` with constant `K`,
then the precise representative of `∇u` is `α`-Hölder on `S` with constant
`C (K + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`, where `C` depends only on `n` and `α`. This is the
interior Schauder estimate for the Laplacian in divergence form,
`[∇u]_{α, S} ≤ C ([G]_{α, S_R} + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`, and its proof is Campanato's.

## The argument

Fix a ball `B_r = ball x₀ r ⊆ Ω`. Since constants have zero divergence, `u` also solves
`-Δu = -div (G - G(x₀))` on `B_r`, now against all of `H¹₀(B_r)`, and `‖G - G(x₀)‖ ≤ K r^α` there.
Let `w` be the harmonic replacement of `u` on `B_r`
(`TauCeti.PDE.exists_sub_mem_w1p0Submodule_harmonicOnNhd_ae_eq_of_subset_ball`). The energy
estimate bounds `∫_{B_r} ‖∇u - ∇w‖²` by `∫_{B_r} ‖G - G(x₀)‖² ≤ |B_r| K² r^{2α}`, while `∇w` is
harmonic (`TauCeti.PDE.W1p.exists_harmonicOnNhd_ae_eq_gradient`), so its square mean oscillation
decays like `(ρ / r)^{n+3}`
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le`).
Together, the square mean oscillation `ψ(ρ) = ∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖²` satisfies

`ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + B K² r^{n+1+2α}` for `0 < ρ ≤ r`.

Since `n + 1 + 2α < n + 3`, the iteration lemma
`TauCeti.exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add` improves this to
`ψ(ρ) ≤ C ρ^{n+1+2α} (R^{-(n+1+2α)} ‖∇u‖² + K²)`. By Jensen's inequality the mean oscillation of
`∇u` on balls of radius `ρ` is then `O(ρ^α)`, and Campanato's theorem
(`TauCeti.MeasureTheory.dist_preciseRepresentative_le_of_setAverage_norm_sub_le`) turns this into
the Hölder estimate. Points farther apart than `R / 2` are compared through the averages of `∇u`
over balls of radius `R`.

## Main declarations

* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient`: the interior Hölder estimate
  for `∇u`, with explicit dependence on `K`, `R` and `‖∇u‖_{L²(Ω)}`.
* `TauCeti.PDE.exists_holderOnWith_preciseRepresentative_gradient_of_isCompact`: `∇u` is
  `α`-Hölder on compact subsets of `Ω`.

## References

* S. Campanato, *Equazioni ellittiche del II ordine e spazi `𝓛^{(2,λ)}`*, Ann. Mat. Pura Appl.
  69 (1965), 321–381.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, 2nd ed., Chapter 5.
* Q. Han, F. Lin, *Elliptic Partial Differential Equations*, Chapter 3.
-/

public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Module Set TopologicalSpace TauCeti.MeasureTheory
open scoped Distributions Gradient InnerProductSpace NNReal

namespace TauCeti

namespace PDE

section Transfer

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure]

omit [DecidableEq ι] [mu.IsAddHaarMeasure] in
/-- Pairing a field with the gradient of a test function only sees the support of the test
function. -/
private theorem setIntegral_inner_gradient_eq_integral {Omega : Opens (EuclideanSpace ℝ ι)}
    (φ : 𝓓(Omega, ℝ)) (g : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    {s : Set (EuclideanSpace ℝ ι)} (hs : tsupport (φ : EuclideanSpace ℝ ι → ℝ) ⊆ s) :
    ∫ x in s, ⟪g x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu =
      ∫ x, ⟪g x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu :=
  setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    simp [gradient, fderiv_of_notMem_tsupport ℝ fun h => hx (hs h)]

omit [DecidableEq ι] in
/-- Subtracting a constant `c` from a square-integrable field `G` on `B` does not change its
pairing with gradients of test functions on `B`. -/
private theorem inner_toLp_gradient_ofTestFunctionₗ {B : Opens (EuclideanSpace ℝ ι)}
    {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {c : EuclideanSpace ℝ ι}
    (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B)) (φ : 𝓓(B, ℝ)) :
    ⟪hGc.toLp, W1p.gradient (W1p.ofTestFunctionₗ mu B 2 φ)⟫_ℝ =
      ∫ x in B, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
  -- The constant `c` integrates to zero against `∇φ`.
  have hpt : ∀ x, ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ = lineDeriv ℝ (φ : _ → ℝ) x c :=
    fun x => by
      rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply,
        (φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  have hcint : IntegrableOn (fun x => ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) B mu := by
    simpa [hpt] using (integrable_lineDeriv_smul_of_locallyIntegrableOn
      (locallyIntegrableOn_const (1 : ℝ) (μ := mu) (s := B)) φ c).integrableOn
  have hc : ∫ x in B, ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu = 0 := by
    rw [setIntegral_inner_gradient_eq_integral φ _ φ.tsupport_subset]
    simpa only [hpt] using TestFunction.integral_lineDeriv_eq_zero (μ := mu) φ c
  have hGint : IntegrableOn (fun x => ⟪G x - c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) B mu := by
    refine (L2.integrable_inner hGc.toLp
      (gradientTestFunctionLp (mu := mu) (Omega := B) 2 φ)).congr ?_
    filter_upwards [hGc.coeFn_toLp,
      gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
    rw [hx, hφx]
  rw [L2.inner_def]
  calc ∫ x in B, ⟪MemLp.toLp _ hGc x, W1p.gradient (W1p.ofTestFunctionₗ mu B 2 φ) x⟫_ℝ ∂mu
      = ∫ x in B, (⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ -
          ⟪c, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ) ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [hGc.coeFn_toLp,
          gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
        rw [W1p.gradient_ofTestFunctionₗ, hx, hφx, inner_sub_left]
    _ = ∫ x in B, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
        rw [integral_sub ((hGint.add hcint).congr (ae_of_all _ fun x => by simp)) hcint, hc,
          sub_zero]

/-- The weak equation `-Δu = -div G` on `Ω`, tested against test functions, holds on every open
`B ⊆ Ω` against all of `H¹₀(B)` once `G` is replaced by `G - c` for a constant `c`, provided
`G - c` is square integrable on `B`: constants have zero divergence. -/
private theorem forall_energyFormH1_restrictL_eq_inner {Omega B : Opens (EuclideanSpace ℝ ι)}
    (hB : B ≤ Omega) {u : W1p mu Omega 2} {G : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
    (hu : ∀ φ : 𝓓(Omega, ℝ), energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ) =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu)
    {c : EuclideanSpace ℝ ι} (hGc : MemLp (fun x => G x - c) 2 (mu.restrict B))
    (v : W1p0 mu B 2) :
    energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL hB u) (v : W1p mu B 2) =
      ⟪hGc.toLp, W1p.gradient (v : W1p mu B 2)⟫_ℝ := by
  set L : W1p mu B 2 →L[ℝ] ℝ :=
    (innerSL ℝ (W1p.gradient (W1p.restrictL hB u) - hGc.toLp)).comp W1p.gradientL
  have hL : ∀ w, L w = energyFormH1 (fun _ => 1) 0 0 (W1p.restrictL hB u) w -
      ⟪hGc.toLp, W1p.gradient w⟫_ℝ := fun w => by
    simp only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply, W1p.gradientL_apply,
      inner_sub_left, energyFormH1_one_zero_zero_eq_inner]
  -- The functional `L` is continuous, so it suffices that it vanishes on test functions.
  suffices hzero : (w1p0Submodule mu B 2 : Set (W1p mu B 2)) ⊆ {w | L w = 0} by
    have := hzero v.2
    simp only [mem_ofPred_eq, hL] at this
    linarith
  refine w1p0Submodule_subset_of_isClosed (isClosed_eq L.continuous continuous_const) fun φ => ?_
  simp only [mem_ofPred_eq, hL, inner_toLp_gradient_ofTestFunctionₗ hGc φ, sub_eq_zero]
  -- The test function `φ` on `B` is also a test function `φ'` on `Ω`, and
  -- `∫_B ⟪∇u, ∇φ⟫ = ∫_Ω ⟪∇u, ∇φ'⟫ = ∫_Ω ⟪G, ∇φ'⟫ = ∫_B ⟪G, ∇φ⟫`.
  set φ' : 𝓓(Omega, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hB⟩
  have hφB : tsupport (φ : EuclideanSpace ℝ ι → ℝ) ⊆ B := φ.tsupport_subset
  have hφΩ : tsupport (φ : EuclideanSpace ℝ ι → ℝ) ⊆ Omega := hφB.trans hB
  have hΩ : energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ mu Omega 2 φ') =
      ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := hu φ'
  rw [energyFormH1_one_zero_zero_eq_inner, L2.inner_def] at hΩ ⊢
  rw [setIntegral_inner_gradient_eq_integral φ G hφB,
    ← setIntegral_inner_gradient_eq_integral φ G hφΩ, ← hΩ]
  calc ∫ x in B, ⟪W1p.gradient (W1p.restrictL hB u) x,
        W1p.gradient (W1p.ofTestFunctionₗ mu B 2 φ) x⟫_ℝ ∂mu
      = ∫ x in B, ⟪W1p.gradient u x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [W1p.gradient_restrictL_ae hB u,
          gradientTestFunctionLp_apply_ae (mu := mu) (Omega := B) 2 φ] with x hx hφx
        rw [W1p.gradient_ofTestFunctionₗ, hx, hφx]
    _ = ∫ x in Omega, ⟪W1p.gradient u x, ∇ (φ : EuclideanSpace ℝ ι → ℝ) x⟫_ℝ ∂mu := by
        rw [setIntegral_inner_gradient_eq_integral φ _ hφB,
          setIntegral_inner_gradient_eq_integral φ _ hφΩ]
    _ = ∫ x in Omega, ⟪W1p.gradient u x,
          W1p.gradient (W1p.ofTestFunctionₗ mu Omega 2 φ') x⟫_ℝ ∂mu := by
        refine integral_congr_ae ?_
        filter_upwards [gradientTestFunctionLp_apply_ae (mu := mu) (Omega := Omega) 2 φ']
          with x hφx
        rw [W1p.gradient_ofTestFunctionₗ, hφx]
        -- `φ'` is `φ` regarded as a test function on `Ω`: the same underlying function.
        rfl

end Transfer

variable {n : ℕ}

section Comparison

/-- A function square integrable on `t` is integrable on every subset `s ⊆ t` of finite measure,
and so is its squared distance to any constant. -/
private theorem integrableOn_and_integrableOn_norm_sub_sq {X F : Type*} [MeasurableSpace X]
    {μ : Measure X} [NormedAddCommGroup F] {g : X → F} {s t : Set X}
    (hg : MemLp g 2 (μ.restrict t)) (hst : s ⊆ t) (hs : μ s ≠ ⊤) :
    IntegrableOn g s μ ∧ ∀ c, IntegrableOn (fun x => ‖g x - c‖ ^ 2) s μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hgs : MemLp g 2 (μ.restrict s) := by
    simpa [Measure.restrict_restrict_of_subset hst] using hg.restrict s
  exact ⟨hgs.integrable one_le_two, fun c =>
    (hgs.sub (memLp_const c)).integrable_norm_pow (p := 2) two_ne_zero⟩

/-- The constant `2^{3d+8} (d + 1)²` of the Campanato decay estimate for harmonic functions on
`ℝ^d`, `d = n + 1`. -/
private def decayConst (n : ℕ) : ℝ := 2 ^ (3 * (n + 1) + 8) * (((n + 1 : ℕ) : ℝ) + 1) ^ 2

private theorem decayConst_nonneg (n : ℕ) : 0 ≤ decayConst n := by
  unfold decayConst
  positivity

/-- **Comparison with a harmonic function.** Let `H` be harmonic on `B_r = ball x₀ r` in a space
of dimension `d`, and let `f` and `H` be square integrable on `B_r`. For `0 < ρ ≤ r`, the square
mean oscillation `ψ(t) = ∫_{B_t} ‖f - f_{B_t}‖²` of `f` decays like that of `H`, up to the
distance `∫_{B_r} ‖f - H‖²` between them:
`ψ(ρ) ≤ 4D (ρ / r)^{d+2} ψ(r) + (4D + 2) ∫_{B_r} ‖f - H‖²`, where `D = 2^{3d+8} (d + 1)²`. -/
private theorem setIntegral_norm_sub_setAverage_sq_le_of_harmonicOnNhd {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {f H : E → F} {x₀ : E} {ρ r : ℝ}
    (hH : HarmonicOnNhd H (ball x₀ r)) (hf : MemLp f 2 (μ.restrict (ball x₀ r)))
    (hHm : MemLp H 2 (μ.restrict (ball x₀ r))) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖f x - ⨍ y in ball x₀ ρ, f y ∂μ‖ ^ 2 ∂μ ≤
      4 * (2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2) * (ρ / r) ^ (finrank ℝ E + 2) *
          (∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ) +
        (4 * (2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2) + 2) *
          ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ := by
  have hr : 0 < r := hρ.trans_le hρr
  have hsubρ : ball x₀ ρ ⊆ ball x₀ r := ball_subset_ball hρr
  have hfint : ∀ t ≤ r, IntegrableOn f (ball x₀ t) μ ∧
      ∀ c, IntegrableOn (fun x => ‖f x - c‖ ^ 2) (ball x₀ t) μ := fun t ht =>
    integrableOn_and_integrableOn_norm_sub_sq hf (ball_subset_ball ht) measure_ball_lt_top.ne
  have hHint : ∀ c, IntegrableOn (fun x => ‖H x - c‖ ^ 2) (ball x₀ r) μ :=
    (integrableOn_and_integrableOn_norm_sub_sq hHm subset_rfl measure_ball_lt_top.ne).2
  have hfH : IntegrableOn (fun x => ‖f x - H x‖ ^ 2) (ball x₀ r) μ :=
    (hf.sub hHm).integrable_norm_pow (p := 2) two_ne_zero
  have hE0 : 0 ≤ ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hψr : 0 ≤ ∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ :=
    setIntegral_nonneg measurableSet_ball fun _ _ => by positivity
  have hD : (0 : ℝ) ≤ 2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2 := by positivity
  have hq0 : 0 ≤ (ρ / r) ^ (finrank ℝ E + 2) := by positivity
  have hq1 : (ρ / r) ^ (finrank ℝ E + 2) ≤ 1 :=
    pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  -- The decay of the harmonic `H` from `B_r` to `B_ρ`.
  have hdecay := hH.setIntegral_ball_norm_sub_setAverage_sq_le (hHint (⨍ y in ball x₀ r, f y ∂μ))
    hρ.le hρr
  -- On `B_ρ`, compare `f` with the average of `H`, then split off `f - H`.
  have step1 := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
    measure_ball_lt_top.ne (hfint ρ hρr).1 ((hfint ρ hρr).2 (⨍ y in ball x₀ ρ, H y ∂μ))
  have step2 : ∫ x in ball x₀ ρ, ‖f x - ⨍ y in ball x₀ ρ, H y ∂μ‖ ^ 2 ∂μ ≤
      2 * (∫ x in ball x₀ ρ, ‖H x - ⨍ y in ball x₀ ρ, H y ∂μ‖ ^ 2 ∂μ) +
        2 * ∫ x in ball x₀ ρ, ‖f x - H x‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (((hHint _).mono_set hsubρ).const_mul 2) ((hfH.mono_set hsubρ).const_mul 2)]
    refine setIntegral_mono_on ((hfint ρ hρr).2 _)
      ((((hHint _).mono_set hsubρ).const_mul 2).add ((hfH.mono_set hsubρ).const_mul 2))
      measurableSet_ball fun x _ => ?_
    have := (pow_le_pow_left₀ (norm_nonneg _)
      (norm_add_le (H x - ⨍ y in ball x₀ ρ, H y ∂μ) (f x - H x)) 2).trans add_sq_le
    rw [sub_add_sub_cancel'] at this
    linarith
  -- On `B_r`, compare `H` with the average of `f`.
  have step3 : ∫ x in ball x₀ r, ‖H x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ ≤
      2 * (∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ) +
        2 * ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (((hfint r le_rfl).2 _).const_mul 2) (hfH.const_mul 2)]
    refine setIntegral_mono_on (hHint _) ((((hfint r le_rfl).2 _).const_mul 2).add
      (hfH.const_mul 2)) measurableSet_ball fun x _ => ?_
    have := (pow_le_pow_left₀ (norm_nonneg _)
      (norm_add_le (f x - ⨍ y in ball x₀ r, f y ∂μ) (-(f x - H x))) 2).trans add_sq_le
    rw [norm_neg, ← sub_eq_add_neg, sub_sub_sub_cancel_left] at this
    linarith
  have step4 : ∫ x in ball x₀ ρ, ‖f x - H x‖ ^ 2 ∂μ ≤ ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ :=
    setIntegral_mono_set hfH (ae_of_all _ fun _ => by positivity) hsubρ.eventuallyLE
  calc ∫ x in ball x₀ ρ, ‖f x - ⨍ y in ball x₀ ρ, f y ∂μ‖ ^ 2 ∂μ
      ≤ 2 * (2 ^ (3 * finrank ℝ E + 8) * (finrank ℝ E + 1) ^ 2 * (ρ / r) ^ (finrank ℝ E + 2) *
          (2 * (∫ x in ball x₀ r, ‖f x - ⨍ y in ball x₀ r, f y ∂μ‖ ^ 2 ∂μ) +
            2 * ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ)) +
          2 * ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ∂μ := by
        refine step1.trans (step2.trans (add_le_add ?_ ?_))
        · gcongr
          exact hdecay.trans (by gcongr)
        · gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hq1 (mul_nonneg hD hE0)]

/-- **The comparison estimate.** Let `u ∈ H¹(Ω)` solve `-Δu = -div G` weakly on `Ω ⊆ ℝ^{n+1}`,
and let `B_r = ball x₀ r ⊆ Ω` be a ball on which `G` is `α`-Hölder with constant `K`. For
`0 < ρ ≤ r`, the square mean oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` of the gradient
satisfies `ψ(ρ) ≤ A (ρ / r)^{n+3} ψ(r) + B K² r^{n+1+2α}` with `A`, `B` depending only on `n`. -/
private theorem setIntegral_norm_gradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {u : W1p volume Omega 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K α : ℝ≥0}
    {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ} (hα : 0 < α)
    (hG : HolderOnWith K α G (ball x₀ r))
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hball : ball x₀ r ⊆ Omega) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * decayConst n * (ρ / r) ^ ((n : ℝ) + 3) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        (4 * decayConst n + 2) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
          K ^ 2 * r ^ ((n : ℝ) + 1 + 2 * α) := by
  have hr : 0 < r := hρ.trans_le hρr
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ r, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hx₀ : x₀ ∈ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))) := hball (mem_ball_self hr)
  have : IsFiniteMeasure (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  -- On `B_r`, the field `G - G x₀` is bounded by `K r^α`.
  have hbd : ∀ x ∈ ball x₀ r, ‖G x - G x₀‖ ≤ K * r ^ (α : ℝ) := fun x hx => by
    rw [← dist_eq_norm]
    calc dist (G x) (G x₀) ≤ K * dist x x₀ ^ (α : ℝ) := hG.dist_le hx (mem_ball_self hr)
      _ ≤ K * r ^ (α : ℝ) := by gcongr; exact (mem_ball.1 hx).le
  have hGc : MemLp (fun x => G x - G x₀) 2
      (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    MemLp.of_bound (((hG.continuousOn hα).aestronglyMeasurable
      measurableSet_ball).sub aestronglyMeasurable_const) (K * r ^ (α : ℝ))
      ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hbd))
  -- Harmonic replacement on `B_r`, with energy error at most `‖G - G x₀‖_{L²(B_r)}`.
  obtain ⟨w, -, -, ⟨h, hh, hwh⟩, hest⟩ :=
    exists_sub_mem_w1p0Submodule_harmonicOnNhd_ae_eq_of_subset_ball (Omega := B) (z := x₀)
      (R := r) subset_rfl (W1p.restrictL hB u)
  have hest' := hest hGc.toLp (forall_energyFormH1_restrictL_eq_inner hB hu hGc)
  -- The gradient of the replacement is harmonic.
  obtain ⟨H, hH, hwH⟩ :=
    W1p.exists_harmonicOnNhd_ae_eq_gradient (hh.weaklyHarmonicOn.congr_ae hwh.symm)
  have hHm : MemLp H 2 (volume.restrict (ball x₀ r)) := (Lp.memLp (W1p.gradient w)).ae_eq hwH
  have hfm : MemLp f 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  -- The energy error `∫_{B_r} ‖∇u - H‖²` is at most `|B_r| (K r^α)²`.
  have hE : ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 ≤
      volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * K ^ 2 *
        r ^ ((n : ℝ) + 1 + 2 * α) := by
    have h1 : ∫ x in ball x₀ r, ‖f x - H x‖ ^ 2 = ‖W1p.gradient (W1p.restrictL hB u - w)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      have hsub : W1p.gradient (W1p.restrictL hB u - w) =
          W1p.gradient (W1p.restrictL hB u) - W1p.gradient w := by
        simp only [← W1p.gradientL_apply, map_sub]
      refine integral_congr_ae ?_
      filter_upwards [W1p.gradient_restrictL_ae hB u, hwH,
        Lp.coeFn_sub (W1p.gradient (W1p.restrictL hB u)) (W1p.gradient w)] with x h1 h2 h3
      rw [hsub, h3, real_inner_self_eq_norm_sq, Pi.sub_apply, h1, h2]
    have h2 : ‖hGc.toLp‖ ^ 2 ≤ volume.real (ball x₀ r) * (K * r ^ (α : ℝ)) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      calc ∫ x in B, ⟪MemLp.toLp _ hGc x, MemLp.toLp _ hGc x⟫_ℝ
          = ∫ x in ball x₀ r, ‖G x - G x₀‖ ^ 2 := by
            refine integral_congr_ae ?_
            filter_upwards [hGc.coeFn_toLp] with x hx
            rw [hx, real_inner_self_eq_norm_sq]
        _ ≤ ∫ x in ball x₀ r, (K * r ^ (α : ℝ)) ^ 2 :=
            setIntegral_mono_on ((hGc.integrable_norm_pow (p := 2) two_ne_zero))
              (integrableOn_const measure_ball_lt_top.ne) measurableSet_ball
              fun x hx => pow_le_pow_left₀ (norm_nonneg _) (hbd x hx) 2
        _ = volume.real (ball x₀ r) * (K * r ^ (α : ℝ)) ^ 2 := by
            rw [setIntegral_const, smul_eq_mul]
    rw [h1]
    calc ‖W1p.gradient (W1p.restrictL hB u - w)‖ ^ 2 ≤ ‖hGc.toLp‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hest' 2
      _ ≤ volume.real (ball x₀ r) * (K * r ^ (α : ℝ)) ^ 2 := h2
      _ = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * K ^ 2 *
            r ^ ((n : ℝ) + 1 + 2 * α) := by
          rw [Measure.addHaar_real_ball_of_pos _ _ hr, finrank_euclideanSpace_fin,
            Real.rpow_add hr, mul_comm (2 : ℝ), Real.rpow_mul hr.le, Real.rpow_two,
            ← Real.rpow_natCast, Nat.cast_add, Nat.cast_one]
          ring
  have hcomp := setIntegral_norm_sub_setAverage_sq_le_of_harmonicOnNhd hH hfm hHm hρ hρr
  have hq : (ρ / r) ^ (finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) + 2) =
      (ρ / r) ^ ((n : ℝ) + 3) := by
    rw [← Real.rpow_natCast, finrank_euclideanSpace_fin]
    push_cast
    ring_nf
  rw [hq, finrank_euclideanSpace_fin] at hcomp
  have hE' := mul_le_mul_of_nonneg_left hE (by positivity [decayConst_nonneg n] :
    (0 : ℝ) ≤ 4 * decayConst n + 2)
  unfold decayConst at hE' ⊢
  linarith

/-- **Campanato decay of the gradient.** For `0 < α < 1` there is `C`, depending only on `n` and
`α`, such that the following holds. Let `u ∈ H¹(Ω)` solve `-Δu = -div G` weakly on
`Ω ⊆ ℝ^{n+1}`. If `ball x R ⊆ Ω`, `G` is `α`-Hölder with constant `K` on `ball x R` and
`0 < ρ ≤ R`, then
`∫_{B_ρ} ‖∇u - (∇u)_{B_ρ}‖² ≤ C ρ^{n+1+2α} (R^{-(n+1+2α)} ‖∇u‖²_{L²(Ω)} + K²)`. -/
private theorem exists_setIntegral_norm_gradient_sub_setAverage_sq_le {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {x : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ},
      HolderOnWith K α G (ball x R) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball x R ⊆ Omega → ∀ ρ, 0 < ρ → ρ ≤ R →
        ∫ y in ball x ρ, ‖W1p.gradient u y - ⨍ z in ball x ρ, W1p.gradient u z‖ ^ 2 ≤
          C * ρ ^ ((n : ℝ) + 1 + 2 * α) *
            (R ^ (-((n : ℝ) + 1 + 2 * α)) * ‖W1p.gradient u‖ ^ 2 + K ^ 2) := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  have hγ : (n : ℝ) + 1 + 2 * α < n + 3 := by
    have : (α : ℝ) < 1 := hα1
    linarith
  obtain ⟨ε₀, C, hε₀, hC, hit⟩ := exists_le_mul_div_rpow_mul_add_mul_rpow_of_le_mul_add
    (by positivity [decayConst_nonneg n] : 0 ≤ 4 * decayConst n) hγ hγ
  refine ⟨C * max 1 ((4 * decayConst n + 2) * ω), by positivity, ?_⟩
  intro Omega u G K x R hG hu hball ρ hρ hρR
  have hR : 0 < R := hρ.trans_le hρR
  set f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) := ⇑(W1p.gradient u)
  set ψ : ℝ → ℝ := fun t => ∫ y in ball x t, ‖f y - ⨍ z in ball x t, f z‖ ^ 2
  have hfint : ∀ t ≤ R, IntegrableOn f (ball x t) ∧
      ∀ c, IntegrableOn (fun y => ‖f y - c‖ ^ 2) (ball x t) := fun t ht =>
    integrableOn_and_integrableOn_norm_sub_sq (Lp.memLp (W1p.gradient u))
      ((ball_subset_ball ht).trans hball) measure_ball_lt_top.ne
  have hψ0 : ∀ t, 0 ≤ ψ t := fun t => setIntegral_nonneg measurableSet_ball fun _ _ => by
    positivity
  -- `ψ` is nondecreasing, since the average is the best constant in square mean.
  have hmono : MonotoneOn ψ (Ioc 0 R) := fun s hs t ht hst =>
    (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
      (hfint s hs.2).1 ((hfint s hs.2).2 _)).trans
      (setIntegral_mono_set ((hfint t ht.2).2 _) (ae_of_all _ fun _ => by positivity)
        (ball_subset_ball hst).eventuallyLE)
  have hdec := hit (φ := ψ) (R := R) (B := (4 * decayConst n + 2) * ω * K ^ 2) (ε := 0)
    (by positivity [decayConst_nonneg n]) hε₀.le hmono (fun t _ => hψ0 t)
    (fun s t hs hst htR => by
      have := setIntegral_norm_gradient_sub_setAverage_sq_le hα
        (hG.mono (ball_subset_ball htR)) hu hs hst
        ((ball_subset_ball htR).trans hball)
      simp only [ψ, add_zero]
      linarith) ρ R hρ hρR le_rfl
  -- `ψ R ≤ ‖∇u‖²`.
  have hψR : ψ R ≤ ‖W1p.gradient u‖ ^ 2 := by
    have hL2 : ‖W1p.gradient u‖ ^ 2 = ∫ y in Omega, ‖f y‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp_rw [real_inner_self_eq_norm_sq]
      rfl
    have h0 := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq
      measure_ball_lt_top.ne (hfint R le_rfl).1 ((hfint R le_rfl).2 0)
    simp only [sub_zero] at h0
    rw [hL2]
    exact h0.trans (setIntegral_mono_set
      ((Lp.memLp (W1p.gradient u)).integrable_norm_pow (p := 2) two_ne_zero)
      (ae_of_all _ fun _ => by positivity) hball.eventuallyLE)
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = (n : ℝ) + 1 + 2 * α := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max 1 ((4 * decayConst n + 2) * ω) := ⟨_, rfl⟩
  rw [← hγ] at hdec ⊢
  rw [← hM]
  have hργ : 0 ≤ ρ ^ γ := by positivity
  have hRγ : 0 ≤ R ^ (-γ) := by positivity
  have h1 : (ρ / R) ^ γ * ψ R ≤ M * ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 := by
    rw [Real.div_rpow hρ.le hR.le, div_eq_mul_inv, ← Real.rpow_neg hR.le]
    calc ρ ^ γ * R ^ (-γ) * ψ R ≤ ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hψR (by positivity)
      _ ≤ M * (ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2) :=
          le_mul_of_one_le_left (by positivity) (hM ▸ le_max_left _ _)
      _ = M * ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 := by ring
  have h2 : (4 * decayConst n + 2) * ω * K ^ 2 * ρ ^ γ ≤ M * K ^ 2 * ρ ^ γ := by
    have h := mul_le_mul_of_nonneg_right (hM ▸ le_max_right _ _ :
      (4 * decayConst n + 2) * ω ≤ M) (by positivity : (0 : ℝ) ≤ K ^ 2 * ρ ^ γ)
    linarith
  calc ψ ρ ≤ C * ((ρ / R) ^ γ * ψ R + (4 * decayConst n + 2) * ω * K ^ 2 * ρ ^ γ) := hdec
    _ ≤ C * (M * ρ ^ γ * R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 + M * K ^ 2 * ρ ^ γ) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) hC.le
    _ = C * M * ρ ^ γ * (R ^ (-γ) * ‖W1p.gradient u‖ ^ 2 + K ^ 2) := by ring

/-- Jensen's inequality on a ball: the square of the mean of `‖g‖` over `closedBall z t` is at
most the mean of `‖g‖²` over `ball z t`. -/
private theorem sq_setAverage_closedBall_norm_le {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [NormedAddCommGroup F] {g : E → F} {z : E} {t : ℝ}
    (ht : 0 < t) (hg : IntegrableOn g (ball z t) μ)
    (hg2 : IntegrableOn (fun y => ‖g y‖ ^ 2) (ball z t) μ) :
    (⨍ y in closedBall z t, ‖g y‖ ∂μ) ^ 2 ≤
      (∫ y in ball z t, ‖g y‖ ^ 2 ∂μ) / μ.real (ball z t) := by
  rw [Measure.restrict_congr_set (μ.addHaar_closedBall_ae_eq_ball z ht), div_eq_inv_mul,
    ← smul_eq_mul, ← setAverage_eq]
  exact (Even.convexOn_pow even_two).map_set_average_le (continuous_pow 2).continuousOn
    isClosed_univ (measure_ball_pos μ z ht).ne' measure_ball_lt_top.ne
    (ae_of_all _ fun _ => Set.mem_univ _) hg.norm hg2

/-- **The mean oscillation of the gradient.** For `0 < α < 1` there is `C`, depending only on `n`
and `α`, such that the following holds. Let `u ∈ H¹(Ω)` solve `-Δu = -div G` weakly on
`Ω ⊆ ℝ^{n+1}`. If `ball x R ⊆ Ω`, `G` is `α`-Hölder with constant `K` on `ball x R` and
`0 < t ≤ R`, then the mean oscillation of `∇u` on `closedBall x t` is at most
`C (R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)} + K) t^α`. -/
private theorem exists_setAverage_norm_gradient_sub_le {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {x : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ},
      HolderOnWith K α G (ball x R) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      ball x R ⊆ Omega → ∀ t, 0 < t → t ≤ R →
        ⨍ y in closedBall x t, ‖W1p.gradient u y - ⨍ z in closedBall x t, W1p.gradient u z‖ ≤
          C * (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ + K) * t ^ (α : ℝ) := by
  obtain ⟨C, hC, hdec⟩ := exists_setIntegral_norm_gradient_sub_setAverage_sq_le hα hα1 (n := n)
  have hω : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    measureReal_ball_pos _ _ one_pos
  refine ⟨√(C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)), by positivity, ?_⟩
  intro Omega u G K x R hG hu hball t ht htR
  have hR : 0 < R := ht.trans_le htR
  have hint := integrableOn_and_integrableOn_norm_sub_sq (Lp.memLp (W1p.gradient u))
    ((ball_subset_ball htR).trans hball) measure_ball_lt_top.ne
  -- The averages over `closedBall x t` and `ball x t` agree.
  have havg : ⨍ z in closedBall x t, W1p.gradient u z = ⨍ z in ball x t, W1p.gradient u z := by
    rw [Measure.restrict_congr_set (volume.addHaar_closedBall_ae_eq_ball x ht)]
  rw [havg]
  have hJ := sq_setAverage_closedBall_norm_le ht (hint.1.sub (integrableOn_const
    measure_ball_lt_top.ne)) (hint.2 (⨍ z in ball x t, W1p.gradient u z))
  have hψ := hdec hG hu hball t ht htR
  have hN := norm_nonneg (W1p.gradient u)
  have ha2 : (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) ^ 2 =
      R ^ (-((n : ℝ) + 1 + 2 * α)) * ‖W1p.gradient u‖ ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 2
    push_cast
    ring
  have hvol : volume.real (ball x t) =
      t ^ (n + 1) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
    rw [Measure.addHaar_real_ball_of_pos _ _ ht, finrank_euclideanSpace_fin]
  have htγ : t ^ ((n : ℝ) + 1 + 2 * α) = t ^ (n + 1) * (t ^ (α : ℝ)) ^ 2 := by
    rw [Real.rpow_add ht, ← Real.rpow_natCast, mul_comm (2 : ℝ), Real.rpow_mul ht.le,
      Real.rpow_two]
    push_cast
    rfl
  have htn : 0 < t ^ (n + 1) := by positivity
  rw [← pow_le_pow_iff_left₀ (average_nonneg fun _ => norm_nonneg _) (by positivity) two_ne_zero]
  refine hJ.trans ?_
  rw [hvol, div_le_iff₀ (by positivity), mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  refine hψ.trans ?_
  rw [htγ, ← ha2]
  have hK : (0 : ℝ) ≤ K := K.2
  have hcross : 0 ≤ R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ * K := by positivity
  have key : C * (t ^ (n + 1) * (t ^ (α : ℝ)) ^ 2) *
      ((R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖) ^ 2 + (K : ℝ) ^ 2) ≤
      C * (t ^ (n + 1) * (t ^ (α : ℝ)) ^ 2) *
      (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ + K) ^ 2 := by
    gcongr
    nlinarith
  calc _ ≤ _ := key
    _ = C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
          (R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ + K) ^ 2 * (t ^ (α : ℝ)) ^ 2 *
          (t ^ (n + 1) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
        field_simp

/-- The average of `∇u` over `closedBall z R`, for `ball z R ⊆ Ω`, is at most
`ω^{-1/2} R^{-(n+1)/2} ‖∇u‖_{L²(Ω)}` in norm, where `ω` is the measure of the unit ball. -/
private theorem norm_setAverage_closedBall_gradient_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hR : 0 < R) (hball : ball z R ⊆ Omega) :
    ‖⨍ y in closedBall z R, W1p.gradient u y‖ ≤
      (√(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)))⁻¹ *
        (R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖) := by
  have hω : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    measureReal_ball_pos _ _ one_pos
  have hint := integrableOn_and_integrableOn_norm_sub_sq (Lp.memLp (W1p.gradient u)) hball
    measure_ball_lt_top.ne
  have hint2 := hint.2 0
  simp only [sub_zero] at hint2
  have h1 : ‖⨍ y in closedBall z R, W1p.gradient u y‖ ≤
      ⨍ y in closedBall z R, ‖W1p.gradient u y‖ := by
    rw [setAverage_eq, setAverage_eq, norm_smul, smul_eq_mul,
      Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
  refine h1.trans ?_
  rw [← pow_le_pow_iff_left₀ (average_nonneg fun _ => norm_nonneg _) (by positivity)
    two_ne_zero]
  refine (sq_setAverage_closedBall_norm_le hR hint.1 hint2).trans ?_
  have hL2 : ∫ y in ball z R, ‖W1p.gradient u y‖ ^ 2 ≤ ‖W1p.gradient u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp_rw [real_inner_self_eq_norm_sq]
    exact setIntegral_mono_set
      ((Lp.memLp (W1p.gradient u)).integrable_norm_pow (p := 2) two_ne_zero)
      (ae_of_all _ fun _ => by positivity) hball.eventuallyLE
  have hR2 : (R ^ (-((n : ℝ) + 1) / 2)) ^ 2 = (R ^ (n + 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le, ← Real.rpow_natCast R (n + 1),
      ← Real.rpow_neg hR.le]
    congr 1
    push_cast
    ring
  rw [Measure.addHaar_real_ball_of_pos _ _ hR, finrank_euclideanSpace_fin, mul_pow, mul_pow,
    inv_pow, Real.sq_sqrt hω.le, hR2]
  calc (∫ y in ball z R, ‖W1p.gradient u y‖ ^ 2) /
        (R ^ (n + 1) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
      ≤ ‖W1p.gradient u‖ ^ 2 /
        (R ^ (n + 1) * volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by
        gcongr
    _ = _ := by field_simp

end Comparison

/-- **Interior Hölder continuity of the gradient for `-Δu = -div G`.** Let `0 < α < 1`. There is
a constant `C`, depending only on `n` and `α`, such that the following holds. Let `Ω ⊆ ℝ^{n+1}` be
open and let `u ∈ H¹(Ω)` be a weak solution of `-Δu = -div G` in `Ω`, that is
`∫_Ω ⟨∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`, where `G` is `α`-Hölder with constant
`K` on the closed `R`-thickening of `S`, which lies in `Ω`. Then the precise representative of
`∇u` is `α`-Hölder on `S`, with constant `C (K + R^{-(n+1)/2-α} ‖∇u‖_{L²(Ω)})`.

The precise representative agrees with `∇u` almost everywhere on `Ω`
(`TauCeti.MeasureTheory.ae_eq_restrict_preciseRepresentative`). The exponent of `G` passes to
`∇u` without loss; this is false for `α = 1`, which is why `α < 1` is assumed. -/
theorem exists_holderOnWith_preciseRepresentative_gradient {α : ℝ≥0} (hα : 0 < α)
    (hα1 : α < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
      {u : W1p volume Omega 2}
      {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))} {K : ℝ≥0}
      {S : Set (EuclideanSpace ℝ (Fin (n + 1)))} {R : ℝ},
      HolderOnWith K α G (cthickening R S) →
      (∀ φ : 𝓓(Omega, ℝ),
        energyFormH1 (fun _ => 1) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
          ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ) →
      0 < R → cthickening R S ⊆ Omega →
        HolderOnWith (C * (K + R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖)).toNNReal α
          (preciseRepresentative volume
            (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))))
          S := by
  obtain ⟨C₀, hC₀, hosc⟩ := exists_setAverage_norm_gradient_sub_le hα hα1 (n := n)
  obtain ⟨ω, hω⟩ : ∃ ω, ω = volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    ⟨_, rfl⟩
  have hα' : (0 : ℝ) < α := hα
  have hcα : 0 < 1 - (2 : ℝ) ^ (-(α : ℝ)) :=
    sub_pos.2 (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.2 hα'))
  obtain ⟨cα, hcαdef⟩ : ∃ cα : ℝ, cα = 2 ^ (n + 1) / (1 - 2 ^ (-(α : ℝ))) := ⟨_, rfl⟩
  have hcα0 : 0 ≤ cα := hcαdef ▸ by positivity
  refine ⟨2 * 2 ^ (α : ℝ) * cα * C₀ + 2 * 2 ^ (α : ℝ) * (cα * C₀ + (√ω)⁻¹), by positivity, ?_⟩
  intro Omega u G K S R hG hu hR hRS
  have hball : ∀ z ∈ S, ball z R ⊆ Omega := fun z hz =>
    (ball_subset_thickening hz R).trans ((thickening_subset_cthickening R S).trans hRS)
  have hcball : ∀ z ∈ S, closedBall z R ⊆ Omega := fun z hz =>
    (closedBall_subset_cthickening hz R).trans hRS
  have hint : ∀ z ∈ S, ∀ t ≤ R, IntegrableOn (W1p.gradient u) (closedBall z t) := fun z hz t ht =>
    have : IsFiniteMeasure (volume.restrict (closedBall z t)) :=
      isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono
      ((closedBall_subset_closedBall ht).trans (hcball z hz)) le_rfl)).integrable one_le_two
  obtain ⟨a, ha⟩ : ∃ a, a = R ^ (-(((n : ℝ) + 1) / 2 + α)) * ‖W1p.gradient u‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := ha ▸ by positivity
  rw [← ha]
  have hM : ∀ z ∈ S, ∀ t, 0 < t → t ≤ R →
      ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
        C₀ * (a + K) * t ^ (α : ℝ) := fun z hz t ht htR => by
    rw [ha]
    exact hosc (hG.mono ((ball_subset_thickening hz R).trans
      (thickening_subset_cthickening R S))) hu (hball z hz) t ht htR
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have hK : (0 : ℝ) ≤ K := K.2
  suffices h : dist (preciseRepresentative volume (W1p.gradient u) x)
      (preciseRepresentative volume (W1p.gradient u) y) ≤
      (2 * 2 ^ (α : ℝ) * cα * C₀ + 2 * 2 ^ (α : ℝ) * (cα * C₀ + (√ω)⁻¹)) * (K + a) *
        dist x y ^ (α : ℝ) from
    h.trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (by positivity))
  rcases le_or_gt (2 * dist x y) R with hd | hd
  · -- Nearby points: Campanato's estimate.
    have h := dist_preciseRepresentative_le_of_setAverage_norm_sub_le hα' (hint x hx _ hd)
      (fun r hr hr' => hM x hx r hr (hr'.trans hd))
      (fun r hr hr' => hM y hy r hr (by linarith [dist_nonneg (x := x) (y := y)]))
    rw [finrank_euclideanSpace_fin, ← hcαdef] at h
    refine h.trans ?_
    have hd0 : 0 ≤ dist x y ^ (α : ℝ) := by positivity
    have h1 : 0 ≤ 2 * 2 ^ (α : ℝ) * (cα * C₀ + (√ω)⁻¹) * (K + a) * dist x y ^ (α : ℝ) := by
      positivity
    nlinarith
  · -- Distant points: both values are controlled by averages over balls of radius `R`.
    have hbound : ∀ z ∈ S, ‖preciseRepresentative volume (W1p.gradient u) z‖ ≤
        (cα * C₀ + (√ω)⁻¹) * (a + K) * R ^ (α : ℝ) := fun z hz => by
      have h1 := norm_setAverage_closedBall_sub_preciseRepresentative_le hα' (hint z hz R le_rfl)
        (fun r hr hr' => hM z hz r hr hr') hR le_rfl
      rw [finrank_euclideanSpace_fin, ← hcαdef] at h1
      have h2 := norm_setAverage_closedBall_gradient_le u hR (hball z hz)
      have haR : R ^ (-((n : ℝ) + 1) / 2) * ‖W1p.gradient u‖ = a * R ^ (α : ℝ) := by
        rw [ha, mul_right_comm, ← Real.rpow_add hR]
        congr 2
        ring
      rw [← hω, haR, ← mul_assoc] at h2
      have h3 := norm_sub_le (⨍ y in closedBall z R, W1p.gradient u y)
        ((⨍ y in closedBall z R, W1p.gradient u y) -
          preciseRepresentative volume (W1p.gradient u) z)
      rw [sub_sub_cancel] at h3
      have : (√ω)⁻¹ * a * R ^ (α : ℝ) ≤ (√ω)⁻¹ * (a + K) * R ^ (α : ℝ) := by gcongr; linarith
      linarith
    have hRd : R ^ (α : ℝ) ≤ 2 ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
      rw [← Real.mul_rpow zero_le_two dist_nonneg]
      exact Real.rpow_le_rpow hR.le hd.le hα'.le
    have hsum := dist_le_norm_add_norm (preciseRepresentative volume (W1p.gradient u) x)
      (preciseRepresentative volume (W1p.gradient u) y)
    have hc : 0 ≤ (cα * C₀ + (√ω)⁻¹) * (a + K) := by positivity
    have h1 : 0 ≤ 2 * 2 ^ (α : ℝ) * cα * C₀ * (K + a) * dist x y ^ (α : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left hRd hc
    nlinarith [hbound x hx, hbound y hy]


end PDE

end TauCeti
