/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.Gamma.SectorialDigamma
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Completed.LogDeriv
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ThreeFourOne
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Hadamard
import TauCeti.NumberTheory.LFunctions.Zeros.ZeroFree.RiemannZeta
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.Bounds
import TauCeti.NumberTheory.LSeries.RiemannZeta.LogDeriv.NearOne

/-!
# The de la Vallée Poussin zero-free region for Dirichlet L-functions

We prove `TauCeti.dirichletLFunction_zeroFreeRegion`, giving one absolute constant `c` with
`0 < c ≤ Real.log 3 / 2` such that for every modulus `q ≥ 1` and every Dirichlet character `χ`
modulo `q`, any zero `ρ` of `χ.LFunction` (read through `0 < meromorphicOrderAt χ.LFunction ρ`,
which excludes the pole of principal characters at `s = 1`) in `Re ρ ≥ 1 - c / log (q (|Im ρ| + 3))`
is real and simple, forces `χ ^ 2 = 1`, and is unique in that region (Landau–Page exceptional zero).

The proof reduces principal characters to `TauCeti.riemannZeta_zeroFreeRegion` and nonprincipal
characters to their primitive character `χ.primitiveCharacter` via
`DirichletCharacter.meromorphicOrderAt_LFunction_changeLevel`. For primitive nonprincipal `χ`, the
`3-4-1` inequality (`DirichletCharacter.threeFourOne_neg_re_logDeriv_LFunction_nonneg`) rules out
all zeros of complex characters and all zeros with `|Im ρ| ≥ η / 2` for quadratic characters.
Near the real axis for quadratic `χ`, pairing conjugate zeros `{ρ, star ρ}` (or distinct real
zeros `{ρ₁, ρ₂}`, or a multiple real zero) in
`DirichletCharacter.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor`
contradicts the real-axis bound `(logDeriv χ.LFunction (1 + η)).re ≤ 1 / η + O(log q)`.

## Main results

* `TauCeti.dirichletLFunction_zeroFreeRegion`: the classical Landau–Page zero-free region for
  every `DirichletCharacter.LFunction`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §14.
-/

public section

open Complex DirichletCharacter Filter Set TauCeti.LFunctions
open scoped Topology

namespace TauCeti

private theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta 1 = (-1 : ℤ) := by
  have heq : riemannZeta =ᶠ[𝓝[≠] (1 : ℂ)]
      fun z : ℂ ↦ (Gammaℝ z)⁻¹ * completedRiemannZeta z := by
    filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds one_ne_zero)] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv, mul_comm]
  have ha : AnalyticAt ℂ (fun z : ℂ ↦ (Gammaℝ z)⁻¹) 1 :=
    Complex.differentiable_Gammaℝ_inv.analyticAt 1
  have hne : (Gammaℝ (1 : ℂ))⁻¹ ≠ 0 := by simp
  rw [meromorphicOrderAt_congr heq]
  exact (meromorphicOrderAt_mul_of_ne_zero ha hne).trans meromorphicOrderAt_completedRiemannZeta_one

private theorem meromorphicOrderAt_LFunction_one_at_one (q : ℕ) [NeZero q] :
    meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction 1 = (-1 : ℤ) := by
  rw [← changeLevel_one (q.one_dvd),
    meromorphicOrderAt_LFunction_changeLevel (1 : DirichletCharacter ℂ 1) q.one_dvd
      (by norm_num),
    LFunction_modOne_eq, meromorphicOrderAt_riemannZeta_one]

private theorem exists_norm_logDeriv_gammaFactor_le_log :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (η : ℝ),
      0 < η → η ≤ 1 → ∀ u : ℝ,
      ‖logDeriv χ.gammaFactor (1 + η + u * I)‖ ≤ C * Real.log (|u| + 3) := by
  obtain ⟨C, hC0, hC⟩ := Complex.exists_norm_digamma_le_log (a := 1 / 2) (b := 3 / 2) (by norm_num)
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  refine ⟨C / 2 + |Real.log Real.pi| / 2 + 1, by positivity, fun χ η hη hη1 u ↦ ?_⟩
  set s : ℂ := 1 + η + u * I
  have hs_re : s.re = 1 + η := by simp [s]
  have hs_im : s.im = u := by simp [s]
  have hspos : 0 < s.re := by linarith
  classical
  rw [χ.logDeriv_gammaFactor_eq_digamma (χ.gammaFactor_ne_zero_of_re_pos hspos)]
  set κ : ℂ := if χ.Even then 0 else 1
  have hκ_re : κ.re ∈ Icc (0 : ℝ) 1 := by
    dsimp [κ]
    split_ifs <;> simp
  have hκ_im : κ.im = 0 := by
    dsimp [κ]
    split_ifs <;> simp
  set z : ℂ := (s + κ) / 2
  have hz_re : z.re ∈ Icc (1 / 2 : ℝ) (3 / 2) := by
    simp only [z, div_ofNat_re, add_re, hs_re]
    exact ⟨by linarith [hκ_re.1], by linarith [hκ_re.2]⟩
  have hz_im : z.im = u / 2 := by
    simp [z, hs_im, hκ_im]
  have hψ := hC z hz_re
  have him : |z.im| + 2 ≤ |u| + 3 := by
    rw [hz_im, abs_div, abs_two]
    linarith [abs_nonneg u]
  have hlog_le : Real.log (|z.im| + 2) ≤ Real.log (|u| + 3) :=
    Real.log_le_log (by positivity) him
  have hlog3_le : 1 ≤ Real.log (|u| + 3) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith [abs_nonneg u]))
  have h1 : ‖digamma z / 2‖ ≤ (C / 2) * Real.log (|u| + 3) := by
    rw [norm_div, Complex.norm_two]
    have hmul := hψ.trans (mul_le_mul_of_nonneg_left hlog_le hC0.le)
    linarith
  have h2 : ‖(Real.log Real.pi : ℂ) / 2‖ ≤ (|Real.log Real.pi| / 2) * Real.log (|u| + 3) := by
    rw [norm_div, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left hlog3_le (by positivity : 0 ≤ |Real.log Real.pi| / 2)
    linarith
  calc
    ‖digamma z / 2 - (Real.log Real.pi : ℂ) / 2‖
        ≤ ‖digamma z / 2‖ + ‖(Real.log Real.pi : ℂ) / 2‖ := norm_sub_le _ _
    _ ≤ (C / 2 + |Real.log Real.pi| / 2) * Real.log (|u| + 3) := by linarith
    _ ≤ (C / 2 + |Real.log Real.pi| / 2 + 1) * Real.log (|u| + 3) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)

private theorem neg_re_logDeriv_LFunction_one_ofReal_le {C₀ : ℝ}
    (hC₀ : ∀ η : ℝ, 0 < η → η ≤ 1 → ‖-logDeriv riemannZeta (1 + η) - (η : ℂ)⁻¹‖ ≤ C₀)
    {q : ℕ} [NeZero q] {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    -(logDeriv (1 : DirichletCharacter ℂ q).LFunction (1 + η)).re ≤
      1 / η + max C₀ 0 + Real.log q := by
  have hs1 : (1 : ℝ) ≤ ((1 : ℂ) + η).re := by simp; linarith
  have hne1 : ((1 : ℂ) + η) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, one_re, ofReal_re] at this
    linarith
  have hch := norm_logDeriv_LFunction_changeLevel_sub_le (1 : DirichletCharacter ℂ 1) q.one_dvd
    hs1 (.inr hne1)
  rw [changeLevel_one, LFunction_modOne_eq] at hch
  have hre_ch : -(logDeriv (1 : DirichletCharacter ℂ q).LFunction (1 + η)).re ≤
      -(logDeriv riemannZeta (1 + η)).re + Real.log q := by
    have := Complex.re_le_norm (logDeriv riemannZeta (1 + η) -
      logDeriv (1 : DirichletCharacter ℂ q).LFunction (1 + η))
    rw [norm_sub_rev] at this
    have hsub := this.trans hch
    simp only [Complex.sub_re] at hsub
    linarith
  have hre_ζ : -(logDeriv riemannZeta (1 + η)).re ≤ 1 / η + max C₀ 0 := by
    have hnorm := (Complex.re_le_norm _).trans (hC₀ η hη hη1)
    have hsub_re : (-logDeriv riemannZeta (1 + η) - (η : ℂ)⁻¹).re =
        -(logDeriv riemannZeta (1 + η)).re - 1 / η := by
      simp [one_div]
    rw [hsub_re] at hnorm
    linarith [le_max_left C₀ 0]
  linarith

private theorem neg_re_logDeriv_LFunction_le_of_ne_one {C_γ : ℝ}
    (hγ : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (η : ℝ), 0 < η → η ≤ 1 → ∀ u : ℝ,
      ‖logDeriv χ.gammaFactor (1 + η + u * I)‖ ≤ C_γ * Real.log (|u| + 3))
    {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (u : ℝ) :
    -(logDeriv ψ.LFunction (1 + η + u * I)).re ≤
      (3 / 2) * Real.log q + C_γ * Real.log (|u| + 3) := by
  let q₀ : ℕ := ψ.conductor
  have : NeZero q₀ := ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos ψ.conductor_dvd_level (NeZero.pos q))⟩
  let ψ₀ : DirichletCharacter ℂ q₀ := ψ.primitiveCharacter
  have hψ₀_prim : ψ₀.IsPrimitive := ψ.primitiveCharacter_isPrimitive
  have hψ₀_ne : ψ₀ ≠ 1 := by
    intro h
    apply hψ
    rw [← ψ.changeLevel_primitiveCharacter]
    change changeLevel ψ.conductor_dvd_level ψ₀ = 1
    rw [h, map_one]
  set s : ℂ := 1 + η + u * I
  have hs1 : 1 ≤ s.re := by simp [s]; linarith
  have hch := norm_logDeriv_LFunction_changeLevel_sub_le ψ₀ ψ.conductor_dvd_level hs1 (.inl hψ₀_ne)
  rw [ψ.changeLevel_primitiveCharacter] at hch
  have hre_ch : -(logDeriv ψ.LFunction s).re ≤ -(logDeriv ψ₀.LFunction s).re + Real.log q := by
    have := Complex.re_le_norm (logDeriv ψ₀.LFunction s - logDeriv ψ.LFunction s)
    rw [norm_sub_rev] at this
    have hsub := this.trans hch
    simp only [Complex.sub_re] at hsub
    linarith
  have hhad := ψ₀.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor
    hψ₀_prim hψ₀_ne (S := ∅) (by simp) hs1
  rw [Finset.sum_empty] at hhad
  have hq₀ : Real.log q₀ ≤ Real.log q := by
    refine Real.log_le_log (by exact_mod_cast NeZero.pos q₀) ?_
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) ψ.conductor_dvd_level
  have hγs : (logDeriv ψ₀.gammaFactor s).re ≤ C_γ * Real.log (|u| + 3) :=
    (Complex.re_le_norm _).trans (hγ ψ₀ η hη hη1 u)
  linarith

private theorem neg_re_logDeriv_LFunction_le_single_zero {C_γ : ℝ}
    (hγ : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (η : ℝ), 0 < η → η ≤ 1 → ∀ u : ℝ,
      ‖logDeriv χ.gammaFactor (1 + η + u * I)‖ ≤ C_γ * Real.log (|u| + 3))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {β u : ℝ} (hβ : 0 < β) (hz : χ.LFunction (β + u * I) = 0)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    -(logDeriv χ.LFunction (1 + η + u * I)).re ≤
      -(1 / (1 + η - β)) + Real.log q / 2 + C_γ * Real.log (|u| + 3) := by
  set s : ℂ := 1 + η + u * I
  set ρ : ℂ := β + u * I
  have hs1 : 1 ≤ s.re := by simp [s]; linarith
  have hρpos : 0 < ρ.re := by simpa [ρ] using hβ
  have hhad := χ.re_one_div_sub_le_re_logDeriv_LFunction_add_gammaFactor hprim hne hρpos hz hs1
  have hsρ : s - ρ = ((1 + η - β : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [s, ρ]
  rw [hsρ, one_div, ← ofReal_inv, ofReal_re, ← one_div] at hhad
  have hγs : (logDeriv χ.gammaFactor s).re ≤ C_γ * Real.log (|u| + 3) :=
    (Complex.re_le_norm _).trans (hγ χ η hη hη1 u)
  linarith

private theorem sum_retained_zeros_le {C₀ C_γ : ℝ}
    (hC₀ : ∀ η : ℝ, 0 < η → η ≤ 1 → ‖-logDeriv riemannZeta (1 + η) - (η : ℂ)⁻¹‖ ≤ C₀)
    (hγ : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (η : ℝ), 0 < η → η ≤ 1 → ∀ u : ℝ,
      ‖logDeriv χ.gammaFactor (1 + η + u * I)‖ ≤ C_γ * Real.log (|u| + 3))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {S : Finset ℂ} (hS : ∀ ρ ∈ S, 0 < ρ.re) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η : ℂ) - ρ)).re ≤
      1 / η + (max C₀ 0 + 3 / 2 + C_γ * Real.log 3) * Real.log (3 * q) := by
  have hs1 : 1 ≤ ((1 : ℂ) + η).re := by simp; linarith
  have hhad := χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor
    hprim hne hS hs1
  have h341 := χ.re_logDeriv_LFunction_le_neg_re_logDeriv_one (σ := 1 + η) (by linarith)
  simp only [Complex.ofReal_add, Complex.ofReal_one] at h341
  have h1 := neg_re_logDeriv_LFunction_one_ofReal_le (q := q) hC₀ hη hη1
  have hγ0 : (logDeriv χ.gammaFactor (1 + η)).re ≤ C_γ * Real.log 3 := by
    have := (Complex.re_le_norm _).trans (hγ χ η hη hη1 0)
    simpa using this
  have hCγ0 : 0 ≤ C_γ := by
    have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hn := hγ χ 1 zero_lt_one le_rfl 0
    have hlog_eq : Real.log (|(0 : ℝ)| + 3) = Real.log 3 := by simp
    rw [hlog_eq] at hn
    exact nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hn) h3
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog3q : Real.log 3 ≤ Real.log (3 * q) :=
    Real.log_le_log (by norm_num) (by linarith)
  have h1_le : 1 ≤ Real.log (3 * q) := hlog3.le.trans hlog3q
  have hlogq_le : Real.log q ≤ Real.log (3 * q) :=
    Real.log_le_log (by positivity) (by linarith)
  have hC0_le : max C₀ 0 ≤ max C₀ 0 * Real.log (3 * q) :=
    le_mul_of_one_le_right (le_max_right _ _) h1_le
  have hγ_le : C_γ * Real.log 3 ≤ (C_γ * Real.log 3) * Real.log (3 * q) :=
    le_mul_of_one_le_right (mul_nonneg hCγ0 (zero_le_one.trans hlog3.le)) h1_le
  linarith

private theorem zero_props_of_primitive_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) {ρ : ℂ} (hρpos : 0 < ρ.re)
    (hord : 0 < meromorphicOrderAt χ.LFunction ρ) :
    χ.LFunction ρ = 0 ∧ 1 ≤ analyticOrderNatAt χ.LFunction ρ ∧
      (analyticOrderNatAt χ.LFunction ρ = 1 ↔ meromorphicOrderAt χ.LFunction ρ = 1) := by
  have haL := (DirichletCharacter.differentiable_LFunction hne).analyticAt ρ
  have hne_top : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    rw [← analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hprim hne hρpos]
    exact analyticOrderAt_dirichletData_entireCompletion_ne_top χ hprim ρ
  have hm_eq : meromorphicOrderAt χ.LFunction ρ = (analyticOrderNatAt χ.LFunction ρ : ℤ) := by
    rw [haL.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt hne_top]
    rfl
  rw [hm_eq] at hord
  have hm_pos : 0 < analyticOrderNatAt χ.LFunction ρ := by exact_mod_cast hord
  have hzero : χ.LFunction ρ = 0 := by
    rw [← haL.analyticOrderAt_ne_zero, ← Nat.cast_analyticOrderNatAt hne_top]
    exact_mod_cast hm_pos.ne'
  refine ⟨hzero, hm_pos, ?_⟩
  rw [hm_eq]
  exact_mod_cast Iff.rfl

private theorem sq_eq_one_and_abs_im_lt_of_primitive_ne_one {C₀ C_γ C_ζ K : ℝ}
    (hC₀ : ∀ η : ℝ, 0 < η → η ≤ 1 → ‖-logDeriv riemannZeta (1 + η) - (η : ℂ)⁻¹‖ ≤ C₀)
    (hγ : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (η : ℝ), 0 < η → η ≤ 1 → ∀ u : ℝ,
      ‖logDeriv χ.gammaFactor (1 + η + u * I)‖ ≤ C_γ * Real.log (|u| + 3))
    (hζ : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤
        η / (η ^ 2 + u ^ 2) + C_ζ * Real.log (|u| + 3))
    (hK1 : 1 ≤ K)
    (hK1_le : 3 * (max C₀ 0 + 1) + 4 * (1 / 2 + max C_γ 0) +
      max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0) ≤ K)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hρpos : 0 < ρ.re)
    (hre : 1 - 1 / (160 * K) / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
    (hord : 0 < meromorphicOrderAt χ.LFunction ρ) :
    χ ^ 2 = 1 ∧ |ρ.im| < (1 / (16 * K * Real.log (q * (|ρ.im| + 3)))) / 2 := by
  obtain ⟨hzero, -, -⟩ := zero_props_of_primitive_ne_one χ hprim hne hρpos hord
  set β : ℝ := ρ.re
  set t : ℝ := ρ.im
  have hβ_lt : β < 1 := by
    by_contra h
    push Not at h
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) h hzero
  have hρ_eq : ρ = (β : ℂ) + t * I := (Complex.re_add_im ρ).symm
  rw [hρ_eq] at hzero
  set L : ℝ := Real.log (q * (|t| + 3))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hL3 : Real.log (3 * q) ≤ L := by
    refine Real.log_le_log (by positivity) ?_
    nlinarith [abs_nonneg t]
  have hL1 : 1 < L := hlog3.trans_le ((Real.log_le_log (by norm_num) (by linarith)).trans hL3)
  have hLpos : 0 < L := zero_lt_one.trans hL1
  have hlogq_le : Real.log q ≤ L := Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
  have hlogt_le : Real.log (|t| + 3) ≤ L :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg t])
  have hlog2t_le : Real.log (|2 * t| + 3) ≤ 2 * L := by
    have h2 : |2 * t| + 3 ≤ 2 * (|t| + 3) := by rw [abs_mul, abs_two]; linarith
    have hlog2 : Real.log 2 ≤ 1 := (Real.log_le_iff_le_exp (by norm_num)).mpr
      (by linarith [Real.exp_one_gt_d9])
    calc
      Real.log (|2 * t| + 3) ≤ Real.log (2 * (|t| + 3)) := Real.log_le_log (by positivity) h2
      _ = Real.log 2 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ 1 + L := by linarith
      _ ≤ L + L := by linarith
      _ = 2 * L := by ring
  set η : ℝ := 1 / (16 * K * L)
  have hηpos : 0 < η := by positivity
  have hη1 : η ≤ 1 := by
    refine div_le_one_of_le₀ ?_ (by positivity)
    nlinarith
  have h341_core (hcase : χ ^ 2 ≠ 1 ∨ (χ ^ 2 = 1 ∧ η / 2 ≤ |t|)) : False := by
    have h341 := χ.threeFourOne_neg_re_logDeriv_LFunction_nonneg (σ := 1 + η) (by linarith) t
    simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.neg_re] at h341
    have hterm1 : -(logDeriv (1 : DirichletCharacter ℂ q).LFunction (1 + η)).re ≤
        1 / η + (max C₀ 0 + 1) * L := by
      have := neg_re_logDeriv_LFunction_one_ofReal_le (q := q) hC₀ hηpos hη1
      have hC0L : max C₀ 0 ≤ max C₀ 0 * L := le_mul_of_one_le_right (le_max_right _ _) hL1.le
      linarith
    have htermχ : -(logDeriv χ.LFunction (1 + η + t * I)).re ≤
        -(1 / (1 + η - β)) + (1 / 2 + max C_γ 0) * L := by
      have h0 := neg_re_logDeriv_LFunction_le_single_zero hγ χ hprim hne hρpos hzero hηpos hη1
      have hγL : C_γ * Real.log (|t| + 3) ≤ max C_γ 0 * L :=
        mul_le_mul (le_max_left _ _) hlogt_le (Real.log_nonneg (by linarith [abs_nonneg t]))
          (le_max_right _ _)
      linarith
    have htermχ2 : -(logDeriv (χ ^ 2).LFunction (1 + η + 2 * t * I)).re ≤
        1 / (2 * η) + max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0) * L := by
      rcases hcase with hsq | ⟨hχ2_1, ht_big⟩
      · have h0 := neg_re_logDeriv_LFunction_le_of_ne_one hγ (χ ^ 2) hsq hηpos hη1 (2 * t)
        have h2t_eq : (1 : ℂ) + η + 2 * t * I = 1 + η + ((2 * t : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [← h2t_eq] at h0
        have hγL : C_γ * Real.log (|2 * t| + 3) ≤ 2 * max C_γ 0 * L := by
          have : C_γ * Real.log (|2 * t| + 3) ≤ max C_γ 0 * (2 * L) :=
            mul_le_mul (le_max_left _ _) hlog2t_le
              (Real.log_nonneg (by linarith [abs_nonneg (2 * t)])) (le_max_right _ _)
          linarith
        have hm := le_max_left (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0)
        have hmL : (3 / 2 + 2 * max C_γ 0) * L ≤
            max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0) * L :=
          mul_le_mul_of_nonneg_right hm hLpos.le
        have hhalf : 0 ≤ 1 / (2 * η) := by positivity
        linarith
      · have h2t_re : 1 ≤ ((1 : ℂ) + η + 2 * t * I).re := by simp; linarith
        have h2t_ne1 : (1 : ℂ) + η + 2 * t * I ≠ 1 := by
          intro h
          have hre_eq := congrArg Complex.re h
          have hre_lhs : ((1 : ℂ) + η + 2 * t * I).re = 1 + η := by simp
          rw [hre_lhs, Complex.one_re] at hre_eq
          linarith
        have hch := norm_logDeriv_LFunction_changeLevel_sub_le (1 : DirichletCharacter ℂ 1)
          q.one_dvd h2t_re (.inr h2t_ne1)
        rw [changeLevel_one, LFunction_modOne_eq] at hch
        have hre_ch : -(logDeriv (1 : DirichletCharacter ℂ q).LFunction (1 + η + 2 * t * I)).re ≤
            -(logDeriv riemannZeta (1 + η + 2 * t * I)).re + Real.log q := by
          have := Complex.re_le_norm (logDeriv riemannZeta (1 + η + 2 * t * I) -
            logDeriv (1 : DirichletCharacter ℂ q).LFunction (1 + η + 2 * t * I))
          rw [norm_sub_rev] at this
          have hsub := this.trans hch
          simp only [Complex.sub_re] at hsub
          linarith
        have hζ2 := hζ η hηpos hη1 (2 * t)
        have h2t_eq : (1 : ℂ) + η + 2 * t * I = 1 + η + ((2 * t : ℝ) : ℂ) * I := by
          push_cast; ring
        rw [← h2t_eq] at hζ2
        have h4t : η ^ 2 ≤ (2 * t) ^ 2 := by
          have := (sq_le_sq₀ (by positivity) (abs_nonneg t)).mpr ht_big
          rw [div_pow, sq_abs] at this
          linarith
        have hpole : η / (η ^ 2 + (2 * t) ^ 2) ≤ 1 / (2 * η) := by
          calc
            η / (η ^ 2 + (2 * t) ^ 2) ≤ η / (2 * η ^ 2) :=
              div_le_div_of_nonneg_left hηpos.le (by positivity) (by linarith)
            _ = 1 / (2 * η) := by field_simp
        have hζL : C_ζ * Real.log (|2 * t| + 3) ≤ 2 * max C_ζ 0 * L := by
          have : C_ζ * Real.log (|2 * t| + 3) ≤ max C_ζ 0 * (2 * L) :=
            mul_le_mul (le_max_left _ _) hlog2t_le
              (Real.log_nonneg (by linarith [abs_nonneg (2 * t)])) (le_max_right _ _)
          linarith
        have hm := le_max_right (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0)
        have hmL : (1 + 2 * max C_ζ 0) * L ≤
            max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0) * L :=
          mul_le_mul_of_nonneg_right hm hLpos.le
        rw [hχ2_1]
        linarith
    have hcomb : 4 / (1 + η - β) ≤ 7 / (2 * η) + K * L := by
      have hKL : (3 * (max C₀ 0 + 1) + 4 * (1 / 2 + max C_γ 0) +
          max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0)) * L ≤ K * L :=
        mul_le_mul_of_nonneg_right hK1_le hLpos.le
      have hK1L : (3 * (max C₀ 0 + 1) + 4 * (1 / 2 + max C_γ 0) +
          max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0)) * L =
          3 * ((max C₀ 0 + 1) * L) + 4 * ((1 / 2 + max C_γ 0) * L) +
          max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0) * L := by ring
      have h3div : 3 * (1 / η) = 3 / η := by ring
      have h4div : 4 * (1 / (1 + η - β)) = 4 / (1 + η - β) := by ring
      have h72 : 3 / η + 1 / (2 * η) = 7 / (2 * η) := by field_simp; ring
      linarith only [h341, hterm1, htermχ, htermχ2, hKL, hK1L, h3div, h4div, h72]
    have hKL_eq : K * L = 1 / (16 * η) := by
      dsimp [η]; field_simp
    have h1β : 1 - β ≤ η / 10 := by
      have : 1 / (160 * K) / L = η / 10 := by dsimp [η]; ring
      linarith only [hre, this]
    have h1ηβ_pos : 0 < 1 + η - β := by linarith only [hβ_lt, hηpos]
    have hlo : 40 / (11 * η) ≤ 4 / (1 + η - β) := by
      rw [div_le_div_iff₀ (by positivity) h1ηβ_pos]
      linarith only [h1β]
    have hcon : 40 / (11 * η) ≤ 57 / (16 * η) := by
      have : 7 / (2 * η) + 1 / (16 * η) = 57 / (16 * η) := by field_simp; ring
      linarith only [hlo, hcomb, hKL_eq, this]
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hcon
    linarith only [hcon, hηpos]
  have hsq : χ ^ 2 = 1 := by
    by_contra h
    exact h341_core (.inl h)
  have ht_lt : |t| < η / 2 := by
    by_contra h
    push Not at h
    exact h341_core (.inr ⟨hsq, h⟩)
  exact ⟨hsq, ht_lt⟩

private theorem real_and_sq_eq_one_of_primitive_ne_one {C₀ C_γ C_ζ : ℝ}
    (hC₀ : ∀ η : ℝ, 0 < η → η ≤ 1 → ‖-logDeriv riemannZeta (1 + η) - (η : ℂ)⁻¹‖ ≤ C₀)
    (hγ : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) (η : ℝ), 0 < η → η ≤ 1 → ∀ u : ℝ,
      ‖logDeriv χ.gammaFactor (1 + η + u * I)‖ ≤ C_γ * Real.log (|u| + 3))
    (hζ : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤
        η / (η ^ 2 + u ^ 2) + C_ζ * Real.log (|u| + 3)) :
    ∃ K : ℝ, 1 ≤ K ∧ max C₀ 0 + 3 / 2 + C_γ * Real.log 3 ≤ K ∧
      ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ ρ : ℂ, 0 < ρ.re →
      1 - 1 / (160 * K) / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
      0 < meromorphicOrderAt χ.LFunction ρ →
      ρ.im = 0 ∧ χ ^ 2 = 1 := by
  let K₁ : ℝ := 3 * (max C₀ 0 + 1) + 4 * (1 / 2 + max C_γ 0) +
    max (3 / 2 + 2 * max C_γ 0) (1 + 2 * max C_ζ 0)
  let K₂ : ℝ := max C₀ 0 + 3 / 2 + C_γ * Real.log 3
  let K : ℝ := max 1 (max K₁ K₂)
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK1_le : K₁ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK2_le : K₂ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hK1, hK2_le, fun {q} _ χ hprim hne ρ hρpos hre hord ↦ ?_⟩
  obtain ⟨hsq, ht_lt⟩ := sq_eq_one_and_abs_im_lt_of_primitive_ne_one
    hC₀ hγ hζ hK1 hK1_le χ hprim hne hρpos hre hord
  refine ⟨?_, hsq⟩
  by_contra ht0
  obtain ⟨hzero, hm_pos, -⟩ := zero_props_of_primitive_ne_one χ hprim hne hρpos hord
  set β : ℝ := ρ.re
  set t : ℝ := ρ.im
  have hβ_lt : β < 1 := by
    by_contra h
    push Not at h
    exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) h hzero
  set L : ℝ := Real.log (q * (|t| + 3))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog3 : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hL3 : Real.log (3 * q) ≤ L := by
    refine Real.log_le_log (by positivity) ?_
    nlinarith [abs_nonneg t]
  have hlog3q_ge1 : 1 ≤ Real.log (3 * q) :=
    hlog3.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlog3q_pos : 0 < Real.log (3 * q) := zero_lt_one.trans_le hlog3q_ge1
  set η₀ : ℝ := 1 / (16 * K * Real.log (3 * q))
  have hη₀_pos : 0 < η₀ := by positivity
  have hη₀_1 : η₀ ≤ 1 := by
    refine div_le_one_of_le₀ ?_ (by positivity)
    nlinarith
  have hη_le_η₀ : 1 / (16 * K * L) ≤ η₀ :=
    div_le_div_of_nonneg_left zero_le_one (by positivity)
      (mul_le_mul_of_nonneg_left hL3 (by positivity))
  have ht_lt_η₀ : |t| < η₀ / 2 := lt_of_lt_of_le ht_lt (by linarith only [hη_le_η₀])
  have h1β_0 : 1 - β ≤ η₀ / 10 := by
    have hη_eq : 1 / (160 * K) / Real.log (3 * q) = η₀ / 10 := by dsimp [η₀]; ring
    have hLinv : 1 / (160 * K) / L ≤ 1 / (160 * K) / Real.log (3 * q) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hL3
    linarith only [hre, hLinv, hη_eq]
  have hquad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hsq
  have hconj_zero : χ.LFunction (star ρ) = 0 :=
    (LFunction_conj_eq_zero_iff_of_isQuadratic hquad ρ).mpr hzero
  have hne_conj : ρ ≠ star ρ := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at him
    exact ht0 (by linarith only [him])
  have hm₁ : (1 : ℝ) ≤ analyticOrderNatAt χ.LFunction ρ := by exact_mod_cast hm_pos
  have hm₂ : (1 : ℝ) ≤ analyticOrderNatAt χ.LFunction (star ρ) := by
    have hstar_pos : 0 < (star ρ).re := by simpa [Complex.star_def] using hρpos
    have haL := (DirichletCharacter.differentiable_LFunction hne).analyticAt (star ρ)
    have hne_top : analyticOrderAt χ.LFunction (star ρ) ≠ ⊤ := by
      rw [← analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hprim hne hstar_pos]
      exact analyticOrderAt_dirichletData_entireCompletion_ne_top χ hprim (star ρ)
    have hp : 1 ≤ analyticOrderNatAt χ.LFunction (star ρ) := by
      rw [Nat.one_le_iff_ne_zero, ← Nat.cast_ne_zero (R := ℕ∞), Nat.cast_analyticOrderNatAt hne_top]
      exact haL.analyticOrderAt_ne_zero.mpr hconj_zero
    exact_mod_cast hp
  have hS : ∀ z ∈ ({ρ, star ρ} : Finset ℂ), 0 < z.re := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with h1 | h2
    · rw [h1]; exact hρpos
    · rw [h2]; simpa [Complex.star_def] using hρpos
  have hsum := sum_retained_zeros_le hC₀ hγ χ hprim hne hS hη₀_pos hη₀_1
  rw [Finset.sum_pair hne_conj] at hsum
  have hre_pair (z : ℂ) (hz_re : z.re = β) (hz_im : z.im ^ 2 = t ^ 2) :
      (1 / ((1 + η₀ : ℂ) - z)).re = (1 + η₀ - β) / ((1 + η₀ - β) ^ 2 + t ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re, hz_re,
      Complex.sub_im, Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, zero_sub]
    have him2 : (-z.im) * (-z.im) = t ^ 2 := by nlinarith [hz_im]
    rw [← sq, him2]
  have hre1 : (1 / ((1 + η₀ : ℂ) - ρ)).re = (1 + η₀ - β) / ((1 + η₀ - β) ^ 2 + t ^ 2) :=
    hre_pair ρ rfl rfl
  have hre2 : (1 / ((1 + η₀ : ℂ) - star ρ)).re = (1 + η₀ - β) / ((1 + η₀ - β) ^ 2 + t ^ 2) :=
    hre_pair (star ρ) (by simp [β]) (by simp [t])
  have hden_pos : 0 < (1 + η₀ - β) ^ 2 + t ^ 2 := by positivity
  have hnum_pos : 0 < 1 + η₀ - β := by linarith only [hβ_lt, hη₀_pos]
  have hterm_lo : 100 / (146 * η₀) ≤ (1 + η₀ - β) / ((1 + η₀ - β) ^ 2 + t ^ 2) := by
    have hden_hi : (1 + η₀ - β) ^ 2 + t ^ 2 ≤ (146 / 100) * η₀ ^ 2 := by
      have h1 : (1 + η₀ - β) ^ 2 ≤ (11 / 10 * η₀) ^ 2 := by
        nlinarith only [hnum_pos, h1β_0, hη₀_pos]
      have h2 : t ^ 2 ≤ (η₀ / 2) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg t) (by positivity)).mpr ht_lt_η₀.le
      nlinarith only [h1, h2]
    calc
      100 / (146 * η₀) = η₀ / ((146 / 100) * η₀ ^ 2) := by field_simp
      _ ≤ (1 + η₀ - β) / ((146 / 100) * η₀ ^ 2) :=
          div_le_div_of_nonneg_right (by linarith only [hβ_lt]) (by positivity)
      _ ≤ (1 + η₀ - β) / ((1 + η₀ - β) ^ 2 + t ^ 2) :=
          div_le_div_of_nonneg_left hnum_pos.le hden_pos hden_hi
  have hpair_lo : 200 / (146 * η₀) ≤
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ)).re +
      (analyticOrderNatAt χ.LFunction (star ρ) : ℝ) * (1 / ((1 + η₀ : ℂ) - star ρ)).re := by
    rw [hre1, hre2]
    have hprod1 : 100 / (146 * η₀) ≤
        (analyticOrderNatAt χ.LFunction ρ : ℝ) * ((1 + η₀ - β) / ((1 + η₀ - β) ^ 2 + t ^ 2)) := by
      simpa only [one_mul] using mul_le_mul hm₁ hterm_lo (by positivity) (by positivity)
    have hprod2 : 100 / (146 * η₀) ≤
        (analyticOrderNatAt χ.LFunction (star ρ) : ℝ) *
          ((1 + η₀ - β) / ((1 + η₀ - β) ^ 2 + t ^ 2)) := by
      simpa only [one_mul] using mul_le_mul hm₂ hterm_lo (by positivity) (by positivity)
    have h200 : 100 / (146 * η₀) + 100 / (146 * η₀) = 200 / (146 * η₀) := by ring
    linarith only [hprod1, hprod2, h200]
  have hK2_rhs : (max C₀ 0 + 3 / 2 + C_γ * Real.log 3) * Real.log (3 * q) ≤ 1 / (16 * η₀) := by
    have h1 : (max C₀ 0 + 3 / 2 + C_γ * Real.log 3) * Real.log (3 * q) ≤
        K * Real.log (3 * q) :=
      mul_le_mul_of_nonneg_right hK2_le hlog3q_pos.le
    have h2 : K * Real.log (3 * q) = 1 / (16 * η₀) := by dsimp [η₀]; field_simp
    linarith only [h1, h2]
  have hcon : 200 / (146 * η₀) ≤ 17 / (16 * η₀) := by
    have h17 : 1 / η₀ + 1 / (16 * η₀) = 17 / (16 * η₀) := by field_simp; ring
    linarith only [hpair_lo, hsum, hK2_rhs, h17]
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hcon
  linarith only [hcon, hη₀_pos]

private theorem primitive_nonprincipal_zeroFreeRegion :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ ≤ Real.log 3 / 2 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
        (∀ ρ : ℂ, 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
          0 < meromorphicOrderAt χ.LFunction ρ →
          ρ.im = 0 ∧ χ ^ 2 = 1 ∧ meromorphicOrderAt χ.LFunction ρ = 1) ∧
        ∀ ρ₁ ρ₂ : ℂ, 1 - c₁ / Real.log (q * (|ρ₁.im| + 3)) ≤ ρ₁.re →
          1 - c₁ / Real.log (q * (|ρ₂.im| + 3)) ≤ ρ₂.re →
          0 < meromorphicOrderAt χ.LFunction ρ₁ →
          0 < meromorphicOrderAt χ.LFunction ρ₂ → ρ₁ = ρ₂ := by
  obtain ⟨C₀, hC₀⟩ := exists_norm_neg_logDeriv_riemannZeta_one_add_sub_inv_le
  obtain ⟨C_γ, _, hγ⟩ := exists_norm_logDeriv_gammaFactor_le_log
  obtain ⟨C_ζ, _, hζ⟩ := exists_neg_re_logDeriv_riemannZeta_one_add_le
  have hζ' : ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : ℝ,
      -(logDeriv riemannZeta (1 + η + u * I)).re ≤ η / (η ^ 2 + u ^ 2) + C_ζ * Real.log (|u| + 3) :=
    fun η hη hη1 u ↦ (hζ η hη hη1 u).1
  obtain ⟨K, hK1, hK2_le, hreal_sq⟩ := real_and_sq_eq_one_of_primitive_ne_one hC₀ hγ hζ'
  let c₁ : ℝ := min (Real.log 3 / 2) (1 / (160 * K))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc₁_pos : 0 < c₁ := lt_min (half_pos hlog3) (by positivity)
  have hc₁_log : c₁ ≤ Real.log 3 / 2 := min_le_left _ _
  have hc₁_K : c₁ ≤ 1 / (160 * K) := min_le_right _ _
  refine ⟨c₁, hc₁_pos, hc₁_log, fun q _ χ hprim hne ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hre_half (ρ : ℂ) (hre : 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) : 0 < ρ.re := by
    have hlog_ge : Real.log 3 ≤ Real.log (q * (|ρ.im| + 3)) :=
      Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
    have hc_le : c₁ / Real.log (q * (|ρ.im| + 3)) ≤ 1 / 2 := by
      calc
        c₁ / Real.log (q * (|ρ.im| + 3)) ≤ (Real.log 3 / 2) / Real.log 3 :=
          div_le_div₀ (by positivity) hc₁_log hlog3 hlog_ge
        _ = 1 / 2 := by field_simp
    linarith
  have hreal_part (ρ : ℂ) (hre : 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
      (hord : 0 < meromorphicOrderAt χ.LFunction ρ) : ρ.im = 0 ∧ χ ^ 2 = 1 := by
    have hlog_pos : 0 < Real.log (q * (|ρ.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg ρ.im])
    have hre' : 1 - 1 / (160 * K) / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re := by
      have : c₁ / Real.log (q * (|ρ.im| + 3)) ≤ 1 / (160 * K) / Real.log (q * (|ρ.im| + 3)) :=
        div_le_div_of_nonneg_right hc₁_K hlog_pos.le
      linarith
    exact hreal_sq χ hprim hne ρ (hre_half ρ hre) hre' hord
  have hlog3_gt : 1 < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hlog3q_ge1 : 1 ≤ Real.log (3 * q) :=
    hlog3_gt.le.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlog3q_pos : 0 < Real.log (3 * q) := zero_lt_one.trans_le hlog3q_ge1
  set η₀ : ℝ := 1 / (16 * K * Real.log (3 * q))
  have hη₀_pos : 0 < η₀ := by positivity
  have hη₀_1 : η₀ ≤ 1 := by
    refine div_le_one_of_le₀ ?_ (by positivity)
    nlinarith
  have hgap (ρ : ℂ) (hre : 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) :
      1 - ρ.re ≤ η₀ / 10 := by
    have hlog_ge : Real.log (3 * q) ≤ Real.log (q * (|ρ.im| + 3)) :=
      Real.log_le_log (by positivity) (by nlinarith [abs_nonneg ρ.im])
    have hc_le : c₁ / Real.log (q * (|ρ.im| + 3)) ≤ 1 / (160 * K) / Real.log (3 * q) :=
      div_le_div₀ (by positivity) hc₁_K hlog3q_pos hlog_ge
    have : 1 / (160 * K) / Real.log (3 * q) = η₀ / 10 := by dsimp [η₀]; ring
    linarith
  have hη_bound (S : Finset ℂ) (hS : ∀ ρ ∈ S, 0 < ρ.re) :
      ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ)).re ≤
        17 / (16 * η₀) := by
    have h0 := sum_retained_zeros_le hC₀ hγ χ hprim hne hS hη₀_pos hη₀_1
    have hK2 : (max C₀ 0 + 3 / 2 + C_γ * Real.log 3) * Real.log (3 * q) ≤ 1 / (16 * η₀) := by
      have hL_ge : (max C₀ 0 + 3 / 2 + C_γ * Real.log 3) * Real.log (3 * q) ≤
          K * Real.log (3 * q) :=
        mul_le_mul_of_nonneg_right hK2_le hlog3q_pos.le
      have hKeq : K * Real.log (3 * q) = 1 / (16 * η₀) := by dsimp [η₀]; field_simp
      linarith
    have h17 : 1 / η₀ + 1 / (16 * η₀) = 17 / (16 * η₀) := by field_simp; ring
    linarith
  have hreal_contrib (ρ : ℂ) (him : ρ.im = 0) (hre : 1 - c₁ / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
      (hord : 0 < meromorphicOrderAt χ.LFunction ρ) :
      10 / (11 * η₀) ≤ (1 / ((1 + η₀ : ℂ) - ρ)).re ∧ ρ.re < 1 := by
    have hzero := (zero_props_of_primitive_ne_one χ hprim hne (hre_half ρ hre) hord).1
    have hlt1 : ρ.re < 1 := by
      by_contra h
      push Not at h
      exact χ.LFunction_ne_zero_of_one_le_re (.inl hne) h hzero
    have hsub : (1 + η₀ : ℂ) - ρ = ((1 + η₀ - ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hsub, one_div, ← ofReal_inv, ofReal_re, ← one_div]
    have hpos : 0 < 1 + η₀ - ρ.re := by linarith
    have hle : 1 + η₀ - ρ.re ≤ 11 * η₀ / 10 := by linarith [hgap ρ hre]
    refine ⟨?_, hlt1⟩
    rw [div_le_div_iff₀ (by positivity) hpos]
    linarith
  constructor
  · intro ρ hre hord
    obtain ⟨him, hsq⟩ := hreal_part ρ hre hord
    refine ⟨him, hsq, ?_⟩
    obtain ⟨-, hm1, hiff⟩ := zero_props_of_primitive_ne_one χ hprim hne (hre_half ρ hre) hord
    rw [← hiff]
    by_contra hm_ne
    have hm2 : (2 : ℝ) ≤ analyticOrderNatAt χ.LFunction ρ := by
      have : 2 ≤ analyticOrderNatAt χ.LFunction ρ := by omega
      exact_mod_cast this
    have hS := hη_bound {ρ} (by simpa using hre_half ρ hre)
    rw [Finset.sum_singleton] at hS
    obtain ⟨hlo, -⟩ := hreal_contrib ρ him hre hord
    have h20 : 20 / (11 * η₀) ≤ 17 / (16 * η₀) := by
      have hmul : 2 * (10 / (11 * η₀)) ≤
          (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ)).re :=
        mul_le_mul hm2 hlo (by positivity) (by positivity)
      have h2eq : 2 * (10 / (11 * η₀)) = 20 / (11 * η₀) := by ring
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h20
    linarith
  · intro ρ₁ ρ₂ hre₁ hre₂ hord₁ hord₂
    by_contra hne12
    obtain ⟨him₁, -⟩ := hreal_part ρ₁ hre₁ hord₁
    obtain ⟨him₂, -⟩ := hreal_part ρ₂ hre₂ hord₂
    have hm₁ : (1 : ℝ) ≤ analyticOrderNatAt χ.LFunction ρ₁ := by
      exact_mod_cast (zero_props_of_primitive_ne_one χ hprim hne (hre_half ρ₁ hre₁) hord₁).2.1
    have hm₂ : (1 : ℝ) ≤ analyticOrderNatAt χ.LFunction ρ₂ := by
      exact_mod_cast (zero_props_of_primitive_ne_one χ hprim hne (hre_half ρ₂ hre₂) hord₂).2.1
    have hS := hη_bound {ρ₁, ρ₂} (fun z hz ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with h1 | h2
      · rw [h1]; exact hre_half ρ₁ hre₁
      · rw [h2]; exact hre_half ρ₂ hre₂)
    rw [Finset.sum_pair hne12] at hS
    obtain ⟨hlo₁, -⟩ := hreal_contrib ρ₁ him₁ hre₁ hord₁
    obtain ⟨hlo₂, -⟩ := hreal_contrib ρ₂ him₂ hre₂ hord₂
    have h20 : 20 / (11 * η₀) ≤ 17 / (16 * η₀) := by
      have hmul1 : 10 / (11 * η₀) ≤
          (analyticOrderNatAt χ.LFunction ρ₁ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ₁)).re := by
        simpa only [one_mul] using mul_le_mul hm₁ hlo₁ (by positivity) (by positivity)
      have hmul2 : 10 / (11 * η₀) ≤
          (analyticOrderNatAt χ.LFunction ρ₂ : ℝ) * (1 / ((1 + η₀ : ℂ) - ρ₂)).re := by
        simpa only [one_mul] using mul_le_mul hm₂ hlo₂ (by positivity) (by positivity)
      have h2eq : 10 / (11 * η₀) + 10 / (11 * η₀) = 20 / (11 * η₀) := by ring
      linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at h20
    linarith

/-- **Layer 6.3–6.4 at `K = ℚ`, the region for Dirichlet L-functions.** There is one absolute
constant `c`, with `0 < c ≤ log 3 / 2`, such that for every modulus `q ≥ 1` and every Dirichlet
character `χ` modulo `q`, primitive or not, a zero `ρ` of `L(·, χ)` with
`Re ρ ≥ 1 − c / log (q (|Im ρ| + 3))` is real, simple, and occurs only for a real character
(`χ² = 1`), and there is at most one such zero (Davenport §14). -/
theorem dirichletLFunction_zeroFreeRegion :
    ∃ c : ℝ, 0 < c ∧ c ≤ Real.log 3 / 2 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        (∀ ρ : ℂ, 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re →
          0 < meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ →
          ρ.im = 0 ∧ χ ^ 2 = 1 ∧ meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ = 1) ∧
        ∀ ρ₁ ρ₂ : ℂ, 1 - c / Real.log (q * (|ρ₁.im| + 3)) ≤ ρ₁.re →
          1 - c / Real.log (q * (|ρ₂.im| + 3)) ≤ ρ₂.re →
          0 < meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ₁ →
          0 < meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ₂ → ρ₁ = ρ₂ := by
  obtain ⟨c_ζ, hc_ζ, hζ_zfr⟩ := riemannZeta_zeroFreeRegion
  obtain ⟨c₁, hc₁, hc₁_log, hprim_zfr⟩ := primitive_nonprincipal_zeroFreeRegion
  let c : ℝ := min c_ζ c₁
  refine ⟨c, lt_min hc_ζ hc₁, (min_le_right _ _).trans hc₁_log, fun q _ χ ↦ ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hc_log : c ≤ Real.log 3 / 2 := (min_le_right _ _).trans hc₁_log
  have hre_half (ρ : ℂ) (hre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) : 0 < ρ.re := by
    have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hlog_ge : Real.log 3 ≤ Real.log (q * (|ρ.im| + 3)) :=
      Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg ρ.im])
    have hc_le : c / Real.log (q * (|ρ.im| + 3)) ≤ 1 / 2 := by
      calc
        c / Real.log (q * (|ρ.im| + 3)) ≤ (Real.log 3 / 2) / Real.log 3 :=
          div_le_div₀ (by positivity) hc_log hlog3 hlog_ge
        _ = 1 / 2 := by field_simp
    linarith
  by_cases hχ1 : χ = 1
  · subst hχ1
    have no_zero (ρ : ℂ) (hre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re)
        (hord : 0 < meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction ρ) : False := by
      rcases eq_or_ne ρ 1 with rfl | hρ1
      · rw [meromorphicOrderAt_LFunction_one_at_one q] at hord
        exact absurd hord (by decide)
      · have hpos := hre_half ρ hre
        rw [← changeLevel_one (q.one_dvd),
          meromorphicOrderAt_LFunction_changeLevel (1 : DirichletCharacter ℂ 1) q.one_dvd hpos,
          LFunction_modOne_eq, (analyticOn_riemannZeta ρ hρ1).meromorphicOrderAt_eq] at hord
        have hζ0 : riemannZeta ρ = 0 := by
          by_contra hne
          rw [(analyticOn_riemannZeta ρ hρ1).analyticOrderAt_eq_zero.mpr hne] at hord
          simp at hord
        have hlog_ge : Real.log (|ρ.im| + 3) ≤ Real.log (q * (|ρ.im| + 3)) :=
          Real.log_le_log (by linarith [abs_nonneg ρ.im]) (by nlinarith [abs_nonneg ρ.im])
        have hc_le : c / Real.log (q * (|ρ.im| + 3)) ≤ c_ζ / Real.log (|ρ.im| + 3) :=
          div_le_div₀ hc_ζ.le (min_le_left _ _)
            (Real.log_pos (by linarith [abs_nonneg ρ.im])) hlog_ge
        exact hζ_zfr ρ hρ1 (by linarith) hζ0
    exact ⟨fun ρ hre hord ↦ (no_zero ρ hre hord).elim,
      fun ρ₁ _ hre₁ _ hord₁ _ ↦ (no_zero ρ₁ hre₁ hord₁).elim⟩
  · let q₀ : ℕ := χ.conductor
    have : NeZero q₀ := ⟨Nat.ne_of_gt (Nat.pos_of_dvd_of_pos χ.conductor_dvd_level (NeZero.pos q))⟩
    let χ₀ : DirichletCharacter ℂ q₀ := χ.primitiveCharacter
    have hχ₀_prim : χ₀.IsPrimitive := χ.primitiveCharacter_isPrimitive
    have hχ₀_ne : χ₀ ≠ 1 := by
      intro h
      apply hχ1
      rw [← χ.changeLevel_primitiveCharacter]
      change changeLevel χ.conductor_dvd_level χ₀ = 1
      rw [h, map_one]
    obtain ⟨hsingle, huniq⟩ := hprim_zfr q₀ χ₀ hχ₀_prim hχ₀_ne
    have htransfer (ρ : ℂ) (hre : 1 - c / Real.log (q * (|ρ.im| + 3)) ≤ ρ.re) :
        1 - c₁ / Real.log (q₀ * (|ρ.im| + 3)) ≤ ρ.re ∧
          meromorphicOrderAt χ.LFunction ρ = meromorphicOrderAt χ₀.LFunction ρ := by
      have hpos := hre_half ρ hre
      have hq₀ : (q₀ : ℝ) ≤ q := by
        exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
      have hlog_ge : Real.log (q₀ * (|ρ.im| + 3)) ≤ Real.log (q * (|ρ.im| + 3)) := by
        refine Real.log_le_log ?_ ?_
        · have : (0 : ℝ) < q₀ := by exact_mod_cast NeZero.pos q₀
          positivity
        · exact mul_le_mul_of_nonneg_right hq₀ (by linarith [abs_nonneg ρ.im])
      have hlog_pos : 0 < Real.log (q₀ * (|ρ.im| + 3)) := by
        have hq₀1 : (1 : ℝ) ≤ q₀ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₀)
        exact Real.log_pos (by nlinarith [abs_nonneg ρ.im])
      have hc_le : c / Real.log (q * (|ρ.im| + 3)) ≤ c₁ / Real.log (q₀ * (|ρ.im| + 3)) :=
        div_le_div₀ hc₁.le (min_le_right _ _) hlog_pos hlog_ge
      have hord_eq : meromorphicOrderAt χ.LFunction ρ = meromorphicOrderAt χ₀.LFunction ρ := by
        rw [← χ.changeLevel_primitiveCharacter]
        exact meromorphicOrderAt_LFunction_changeLevel χ₀ χ.conductor_dvd_level hpos
      exact ⟨by linarith, hord_eq⟩
    refine ⟨fun ρ hre hord ↦ ?_, fun ρ₁ ρ₂ hre₁ hre₂ hord₁ hord₂ ↦ ?_⟩
    · obtain ⟨hre', hord_eq⟩ := htransfer ρ hre
      rw [hord_eq] at hord ⊢
      obtain ⟨him, hsq, h1⟩ := hsingle ρ hre' hord
      refine ⟨him, ?_, h1⟩
      rw [← χ.changeLevel_primitiveCharacter]
      change (changeLevel χ.conductor_dvd_level χ₀) ^ 2 = 1
      rw [← map_pow, hsq, map_one]
    · obtain ⟨hre₁', hord_eq₁⟩ := htransfer ρ₁ hre₁
      obtain ⟨hre₂', hord_eq₂⟩ := htransfer ρ₂ hre₂
      rw [hord_eq₁] at hord₁
      rw [hord_eq₂] at hord₂
      exact huniq ρ₁ ρ₂ hre₁' hre₂' hord₁ hord₂

end TauCeti
