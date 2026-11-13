/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.Sobolev.BesselPotential.Algebra
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding

/-!
# Elliptic regularity of the vacuum operator on smooth fields

The gauge-fixed vortex operator at the vacuum, `L₀ = gaugeFixedOperator vacuumField`, is a
constant-coefficient first-order operator with `L₀* L₀ = -Δ + 1 / 4`, so that
`‖L₀ φ‖₂² = ‖∂₁ φ‖₂² + ‖∂₂ φ‖₂² + ‖φ‖₂² / 4` for compactly supported smooth fields
(`integral_norm_sq_gaugeFixedOperator_vacuumField`). This file turns the energy identity into
regularity on the integer Sobolev scale of plane-vortex fields (`sobolevFields`), for smooth
fields with no support or decay assumption.

* **First step.** If a smooth field `y` and `L₀ y` are square integrable, so are the first
  derivatives of `y` (`mem_sobolevFields_one_of_gaugeFixedOperator_vacuumField`). The energy
  identity is applied to the truncations `ρₙ y` by cutoffs `ρₙ` equal to one on the disc of radius
  `n + 1`, whose gradients are uniformly bounded. By the Leibniz rule
  `L₀ (ρₙ y) = ρₙ L₀ y + σ(dρₙ) y` (`gaugeFixedOperator_fun_smul`), the norms `‖L₀ (ρₙ y)‖₂` are
  bounded independently of `n`, hence so are `‖∂ (ρₙ y)‖₂`, and Fatou's lemma bounds `‖∂ y‖₂`.
* **Induction.** `L₀` commutes with directional derivatives
  (`gaugeFixedOperator_vacuumField_fderiv_apply`), so if `y` and `L₀ y` lie in `H^k`, so do every
  derivative `∂_v y` and `L₀ ∂_v y = ∂_v L₀ y` one order lower; by induction `y ∈ H^(k+1)`
  (`mem_sobolevFields_add_one_of_gaugeFixedOperator_vacuumField`).

For a field `vacuum + ψ`, `L₀ ψ` plus the quadratic remainder of the vortex equation is the
gauge-fixing row `d₀* ψ` followed by the three vortex defects of `vacuum + ψ`
(`gaugeFixedOperator_vacuumField_add_quadraticTerm`). The quadratic remainder is a sum of
products of coordinates of `ψ`. Products of bounded functions stay in `L²` and in `H¹`, and
`H^k(ℂ)` is an algebra for `k ≥ 2`, so a bootstrap gives: a smooth bounded square-integrable `ψ`
whose gauge-fixing row and vortex defects lie in every `H^k` lies itself in every `H^k`
(`mem_sobolevFields_of_forall_mem_sobolevFields_equation`). This applies to the deformation of the
vacuum of a plane vortex in its winding end trivialization, cut off near the origin, where the
gauge-fixing row and the vortex defects vanish outside a compact set.

## Main results

* `TauCeti.Vortex.mem_sobolevFields_add_one_of_gaugeFixedOperator_vacuumField`: for smooth `y`,
  `y ∈ H^k` and `L₀ y ∈ H^k` imply `y ∈ H^(k+1)`.
* `TauCeti.Vortex.mem_sobolevFields_of_forall_mem_sobolevFields_equation`: Sobolev regularity of
  all orders for smooth bounded gauge-fixed vortex deformations of the vacuum in `L²`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, §1 (elliptic regularity on the
  Sobolev scale).
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory TemperedDistribution ContinuousLinearMap
open scoped Topology ContDiff ENNReal

/-- **The vacuum operator commutes with directional derivatives** of `C²` fields:
`L₀ (∂_v y) = ∂_v (L₀ y)`. -/
theorem gaugeFixedOperator_vacuumField_fderiv_apply {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : ContDiff ℝ 2 y) (v : ℂ) :
    gaugeFixedOperator vacuumField (fun z ↦ fderiv ℝ y z v) =
      fun z ↦ fderiv ℝ (gaugeFixedOperator vacuumField y) z v := by
  funext z
  have hyi (i : Fin 4) : ContDiff ℝ 2 (fun w ↦ y w i) :=
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 4) →L[ℝ] ℝ).contDiff.comp hy
  have hcoord (i : Fin 4) :
      (fun w ↦ fderiv ℝ y w v i) = fun w ↦ fderiv ℝ (fun t ↦ y t i) w v :=
    funext fun w ↦ (((hy.differentiable two_ne_zero) w).fderiv_piLp_apply i v).symm
  have hpt (i : Fin 4) : fderiv ℝ y z v i = fderiv ℝ (fun t ↦ y t i) z v :=
    congrFun (hcoord i) z
  have hd0 (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ y w i) z :=
    (hyi i).differentiable two_ne_zero z
  have hd1 (i : Fin 4) (u : ℂ) : DifferentiableAt ℝ (fun w ↦ fderiv ℝ (fun t ↦ y t i) w u) z :=
    (((hyi i).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero z).clm_apply
      (differentiableAt_const u)
  have hL : DifferentiableAt ℝ (gaugeFixedOperator vacuumField y) z :=
    (contDiff_gaugeFixedOperator (n := 1) contDiff_vacuumField
      (hy.of_le (by norm_num))).differentiable one_ne_zero z
  have hcomm (i : Fin 4) (u : ℂ) :=
    fderiv_fderiv_apply_comm ((hyi i).contDiffAt (x := z)) (by simp) u v
  ext i
  rw [← hL.fderiv_piLp_apply]
  fin_cases i <;>
    simp [gaugeFixedOperator_apply_zero, gaugeFixedOperator_apply_one,
      gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three, vacuumField_apply, hcoord,
      fderiv_fun_add, fderiv_fun_sub, fderiv_const_mul, fderiv_mul_const, hd0, hd1, hcomm,
      hpt] <;> ring

/-- **The energy identity of the vacuum operator** for smooth compactly supported fields:
`‖L₀ φ‖₂² = ‖∂₁ φ‖₂² + ‖∂₂ φ‖₂² + ‖φ‖₂² / 4`. -/
theorem integral_norm_sq_gaugeFixedOperator_vacuumField {φ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    ∫ z, ‖gaugeFixedOperator vacuumField φ z‖ ^ 2 =
      (∫ z, ‖fderiv ℝ φ z 1‖ ^ 2) + (∫ z, ‖fderiv ℝ φ z I‖ ^ 2) + 1 / 4 * ∫ z, ‖φ z‖ ^ 2 := by
  have h := integral_norm_sq_vacuumOperator (μ := volume) (hc.toSchwartzMap hφ)
  simp only [funext (hc.toSchwartzMap_toFun hφ), SchwartzMap.lineDerivOp_apply_eq_fderiv,
    ← gaugeFixedOperator_vacuumField] at h
  exact h

/-- **The first regularity step for the vacuum operator.** A smooth field `y` in `L²` such that
`L₀ y` is in `L²` has square-integrable first derivatives, so it lies in `H¹`. -/
theorem mem_sobolevFields_one_of_gaugeFixedOperator_vacuumField
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ ∞ y) (h₀ : y ∈ sobolevFields 0)
    (hL : gaugeFixedOperator vacuumField y ∈ sobolevFields 0) : y ∈ sobolevFields 1 := by
  -- Cutoffs `ρₙ`, equal to one on the disc of radius `n + 1`, with uniformly bounded gradients.
  obtain ⟨C, hC0, hcut⟩ := exists_cutoff_fderiv_bound (E := ℂ)
  choose ρ ρ' hρs hρ01 hρ1 hρ0 hρd hρb using fun n : ℕ ↦ hcut 0 ((n : ℝ) + 1) (by positivity)
  have hρC (n : ℕ) (z : ℂ) : ‖fderiv ℝ (ρ n) z‖ ≤ C := by
    rw [(hρd n z).fderiv]
    exact (hρb n z).trans (mul_le_of_le_one_right hC0 (inv_le_one_of_one_le₀ (by simp)))
  have hρ1' (z : ℂ) : ∀ᶠ n in atTop, ∀ᶠ t in 𝓝 z, ρ n t = 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖z‖
    filter_upwards [eventually_ge_atTop N] with n hn
    filter_upwards [Metric.ball_mem_nhds z one_pos] with t ht
    refine hρ1 n t ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [Metric.mem_ball, dist_eq_norm] at ht
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith [norm_le_norm_add_norm_sub' t z]
  set φ : ℕ → ℂ → EuclideanSpace ℝ (Fin 4) := fun n z ↦ ρ n z • y z with hφdef
  have hφ (n : ℕ) : ContDiff ℝ ∞ (φ n) := (hρs n ⊤).smul hy
  have hφc (n : ℕ) : HasCompactSupport (φ n) :=
    (HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * ((n : ℝ) + 1))) fun z hz ↦
      hρ0 n z (by simpa using hz)).smul_right
  -- `‖L₀ (ρₙ y)‖ ≤ ‖L₀ y‖ + C ‖y‖`, by the Leibniz rule.
  have hbound (n : ℕ) (z : ℂ) : ‖gaugeFixedOperator vacuumField (φ n) z‖ ^ 2 ≤
      2 * ‖gaugeFixedOperator vacuumField y z‖ ^ 2 + 2 * C ^ 2 * ‖y z‖ ^ 2 := by
    rw [hφdef, gaugeFixedOperator_fun_smul _ ((hρs n ⊤).differentiable (by simp) z)
      (hy.differentiable (by simp) z)]
    have h₁ := norm_add_le (ρ n z • gaugeFixedOperator vacuumField y z)
      (gaugeFixedOperatorSymbol (fderiv ℝ (ρ n) z) (y z))
    have h₂ : ‖ρ n z • gaugeFixedOperator vacuumField y z‖ ≤
        ‖gaugeFixedOperator vacuumField y z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (hρ01 n z).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hρ01 n z).2
    have h₃ : ‖gaugeFixedOperatorSymbol (fderiv ℝ (ρ n) z) (y z)‖ ≤ C * ‖y z‖ := by
      have h := norm_sq_gaugeFixedOperatorSymbol (fderiv ℝ (ρ n) z) (y z)
      rw [← mul_pow] at h
      rw [(pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h]
      exact mul_le_mul_of_nonneg_right (hρC n z) (norm_nonneg _)
    have h₄ : ‖ρ n z • gaugeFixedOperator vacuumField y z +
        gaugeFixedOperatorSymbol (fderiv ℝ (ρ n) z) (y z)‖ ≤
        ‖gaugeFixedOperator vacuumField y z‖ + C * ‖y z‖ := by linarith
    calc _ ≤ (‖gaugeFixedOperator vacuumField y z‖ + C * ‖y z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h₄ 2
      _ ≤ _ := by nlinarith [sq_nonneg (‖gaugeFixedOperator vacuumField y z‖ - C * ‖y z‖)]
  set M := ∫ z, (2 * ‖gaugeFixedOperator vacuumField y z‖ ^ 2 + 2 * C ^ 2 * ‖y z‖ ^ 2)
  have hM (n : ℕ) : ∫ z, ‖gaugeFixedOperator vacuumField (φ n) z‖ ^ 2 ≤ M :=
    integral_mono_of_nonneg (ae_of_all _ fun z ↦ by positivity)
      (((integrable_norm_sq_of_mem_sobolevFields_zero hL).const_mul 2).add
        ((integrable_norm_sq_of_mem_sobolevFields_zero h₀).const_mul _))
      (ae_of_all _ (hbound n))
  -- The energy identity bounds `‖∂_v (ρₙ y)‖₂` for `v = 1, I`; Fatou's lemma passes to `∂_v y`.
  have hder (v : ℂ) (hv : v = 1 ∨ v = I) : (fun z ↦ fderiv ℝ y z v) ∈ sobolevFields 0 := by
    have hcont (g : ℂ → EuclideanSpace ℝ (Fin 4)) (hg : ContDiff ℝ ∞ g) :
        Continuous fun z ↦ fderiv ℝ g z v :=
      (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    have heLp (n : ℕ) : eLpNorm (fun z ↦ fderiv ℝ (φ n) z v) 2 volume ≤ ENNReal.ofReal √M := by
      have hmem : MemLp (fun z ↦ fderiv ℝ (φ n) z v) 2 volume :=
        (hcont _ (hφ n)).memLp_of_hasCompactSupport
          (((hφc n).fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] _ ↦ L v) (by simp))
      have hint : ∫ z, ‖fderiv ℝ (φ n) z v‖ ^ 2 ≤ M := by
        refine le_trans ?_ (hM n)
        have h := integral_norm_sq_gaugeFixedOperator_vacuumField (hφ n) (hφc n)
        have h₁ : 0 ≤ ∫ z, ‖fderiv ℝ (φ n) z 1‖ ^ 2 := integral_nonneg fun z ↦ sq_nonneg _
        have h₂ : 0 ≤ ∫ z, ‖fderiv ℝ (φ n) z I‖ ^ 2 := integral_nonneg fun z ↦ sq_nonneg _
        have h₃ : 0 ≤ ∫ z, ‖φ n z‖ ^ 2 := integral_nonneg fun z ↦ sq_nonneg _
        rcases hv with rfl | rfl <;> linarith
      rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      refine ENNReal.ofReal_le_ofReal ?_
      simp only [ENNReal.toReal_ofNat, Real.rpow_two]
      rw [Real.sqrt_eq_rpow, one_div]
      exact Real.rpow_le_rpow (integral_nonneg fun z ↦ sq_nonneg _) hint (by norm_num)
    refine mem_sobolevFields_zero_of_memLp ?_
    refine (Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall heLp)
      (fun n ↦ (hcont _ (hφ n)).aestronglyMeasurable) (hcont y hy).aestronglyMeasurable
      (ae_of_all _ fun z ↦ ?_)).trans_lt ENNReal.ofReal_lt_top
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hρ1' z] with n hn
    have heq : φ n =ᶠ[𝓝 z] y := by
      filter_upwards [hn] with t ht
      simp [hφdef, ht]
    rw [heq.fderiv_eq]
  simpa using mem_sobolevFields_add_one_of_fderiv_apply_one_of_fderiv_apply_I (s := 0)
    (hy.of_le (by simp)) h₀ (hder 1 (.inl rfl)) (hder I (.inr rfl))

/-- **Elliptic regularity of the vacuum operator on smooth fields.** For every natural `k`, a smooth
field `y` in `H^k` with `L₀ y` in `H^k` lies in `H^(k+1)`. -/
theorem mem_sobolevFields_add_one_of_gaugeFixedOperator_vacuumField
    {y : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : ContDiff ℝ ∞ y) {k : ℕ} (hk : y ∈ sobolevFields k)
    (hL : gaugeFixedOperator vacuumField y ∈ sobolevFields k) : y ∈ sobolevFields (k + 1) := by
  induction k generalizing y with
  | zero =>
    simpa using mem_sobolevFields_one_of_gaugeFixedOperator_vacuumField hy (by simpa using hk)
      (by simpa using hL)
  | succ k ih =>
    push_cast at hk hL ⊢
    refine mem_sobolevFields_add_one_of_fderiv_apply (hy.of_le (by simp)) hk fun v ↦ ?_
    have hdy : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ y z v) :=
      (hy.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    refine ih hdy (fderiv_apply_mem_sobolevFields (Nat.cast_nonneg k) (hy.of_le (by simp)) hk v) ?_
    rw [gaugeFixedOperator_vacuumField_fderiv_apply (hy.of_le (by simp))]
    exact fderiv_apply_mem_sobolevFields (Nat.cast_nonneg k)
      (contDiff_gaugeFixedOperator contDiff_vacuumField (hy.of_le (by simp))) hL v

/-- **The gauge-fixed vortex equation about the vacuum.** For a field `vacuum + ψ`, the vacuum
operator `L₀ ψ` plus the quadratic remainder of the vortex equation is the gauge-fixing row
`d₀* ψ` followed by the three vortex defects of `vacuum + ψ`. -/
theorem gaugeFixedOperator_vacuumField_add_quadraticTerm {ψ : ℂ → EuclideanSpace ℝ (Fin 4)}
    {z : ℂ} (hψ : DifferentiableAt ℝ ψ z) :
    gaugeFixedOperator vacuumField ψ z +
        !₂[0, quadraticTerm ψ z 0, quadraticTerm ψ z 1, quadraticTerm ψ z 2] =
      !₂[gaugeAdjoint vacuumField ψ z, equation (vacuumField + ψ) z 0,
        equation (vacuumField + ψ) z 1, equation (vacuumField + ψ) z 2] := by
  have hψi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ ψ w i) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp z hψ
  have hvac (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ vacuumField w i) z :=
    (contDiff_euclidean.1 (contDiff_vacuumField (n := 1)) i).differentiable one_ne_zero z
  have h := equation_add_smul hvac hψi 1
  rw [one_smul, one_smul, one_pow, one_smul, equation_vacuumField, zero_add] at h
  ext i
  fin_cases i <;> simp [h, gaugeFixedOperator_apply_zero, gaugeFixedOperator_apply_one,
    gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three]

/-- The quadratic remainder of the vortex equation, a sum of products of coordinates, lies in
`H^k` for a smooth bounded field in `H^k`: below order two by the boundedness of the factors, from
order two on because `H^k(ℂ)` is an algebra. -/
private theorem quadraticTerm_mem_sobolevFields {ψ : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hψ : ContDiff ℝ ∞ ψ) {B : ℝ} (hB : ∀ z, ‖ψ z‖ ≤ B) {k : ℕ} (hk : ψ ∈ sobolevFields k) :
    (fun z ↦ !₂[0, quadraticTerm ψ z 0, quadraticTerm ψ z 1, quadraticTerm ψ z 2]) ∈
      sobolevFields k := by
  have hc (i : Fin 4) : (fun z ↦ ψ z i) ∈ realSobolevFunctions ℂ k 2 := mem_sobolevFields.1 hk i
  have hcd (i : Fin 4) : ContDiff ℝ ∞ (fun z ↦ ψ z i) := contDiff_euclidean.1 hψ i
  have hcB (i : Fin 4) (z : ℂ) : |ψ z i| ≤ B :=
    (Real.norm_eq_abs (ψ z i) ▸ PiLp.norm_apply_le (ψ z) i).trans (hB z)
  have hmul (i j : Fin 4) :
      (fun z ↦ ψ z i) * (fun z ↦ ψ z j) ∈ realSobolevFunctions ℂ k 2 := by
    rcases k with _ | _ | k
    · simpa using mul_mem_realSobolevFunctions_zero_of_bounded (hcd i).continuous (hcB i)
        (by simpa using hc j)
    · simpa using mul_mem_realSobolevFunctions_one_of_bounded ((hcd i).of_le (by simp))
        ((hcd j).of_le (by simp)) (hcB i) (hcB j) (by simpa using hc i) (by simpa using hc j)
    · refine mul_mem_realSobolevFunctions (finrank_real_complex_lt_two_mul ?_) (hc i) (hc j)
      push_cast
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  refine mem_sobolevFields.2 fun i ↦ ?_
  fin_cases i
  · convert zero_mem (realSobolevFunctions ℂ k 2) using 1
    funext z
    simp
  · convert Submodule.smul_mem _ (1 / 2 : ℝ) (add_mem (hmul 2 2) (hmul 3 3)) using 1
    funext z
    simp
    ring
  · convert sub_mem (neg_mem (hmul 0 3)) (hmul 1 2) using 1
    funext z
    simp
  · convert sub_mem (hmul 0 2) (hmul 1 3) using 1
    funext z
    simp

/-- **Regularity of gauge-fixed vortex deformations of the vacuum.** Let `ψ` be a smooth bounded
field in `L²` such that the gauge-fixing row `d₀* ψ` and the vortex defects of `vacuum + ψ` lie in
every `H^k`, for instance because they vanish outside a compact set. Then `ψ` lies in every
`H^k`. -/
theorem mem_sobolevFields_of_forall_mem_sobolevFields_equation
    {ψ : ℂ → EuclideanSpace ℝ (Fin 4)} (hψ : ContDiff ℝ ∞ ψ) {B : ℝ} (hB : ∀ z, ‖ψ z‖ ≤ B)
    (h₀ : ψ ∈ sobolevFields 0)
    (hE : ∀ k : ℕ, (fun z ↦ !₂[gaugeAdjoint vacuumField ψ z, equation (vacuumField + ψ) z 0,
      equation (vacuumField + ψ) z 1, equation (vacuumField + ψ) z 2]) ∈ sobolevFields k)
    (k : ℕ) : ψ ∈ sobolevFields k := by
  induction k with
  | zero => simpa using h₀
  | succ k ih =>
    have hL : gaugeFixedOperator vacuumField ψ ∈ sobolevFields k := by
      convert sub_mem (hE k) (quadraticTerm_mem_sobolevFields hψ hB ih) using 1
      funext z
      rw [Pi.sub_apply, ← gaugeFixedOperator_vacuumField_add_quadraticTerm
        (hψ.differentiable (by simp) z), add_sub_cancel_right]
    exact_mod_cast mem_sobolevFields_add_one_of_gaugeFixedOperator_vacuumField hψ ih hL

end TauCeti.Vortex
