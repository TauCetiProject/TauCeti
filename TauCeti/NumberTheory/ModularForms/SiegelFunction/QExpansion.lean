/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.SiegelFunction.Basic
public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent
import TauCeti.Analysis.Analytic.Order
import TauCeti.Analysis.Calculus.Deriv.Polynomial
import TauCeti.RingTheory.PowerSeries.SubringCoeff
import TauCeti.RingTheory.Subring.Basic

/-!
# Fourier expansions of Siegel functions at infinity

For an integral vector `a = (a₀, a₁)` with `0 ≤ a₀ < N`, writing `t = q_N = e^{2π i τ / N}`,
the theta-product part of `g_{a/N}(τ)` is the function `siegelThetaDisc N a` evaluated at `t`:

  `(1 - ζ t^{a₀}) ∏_{n ≥ 1} (1 - ζ t^{N n + a₀}) (1 - ζ⁻¹ t^{N n - a₀})`,

where `ζ = e^{2π i a₁ / N}`. This product converges to a holomorphic function on the open unit
disc `‖t‖ < 1`, so its Taylor coefficients at `t = 0` coincide with those of its finite partial
products (`qExpansion_siegelThetaDisc_coeff_eq`) and therefore lie in any subring of `ℂ` containing
`e^{2π i / N}` — in particular in `ℤ[ζ_N]` and in the ring of all algebraic integers.

Combined with the exponential prefactor `e^{π i B₂(a₀/N) τ}` and `SL₂(ℤ)`-transport from
`SiegelFunction.Transform`, these expansions establish cusp meromorphy at `i∞` (and hence at all
cusps) and cyclotomic / algebraic-integer Fourier coefficients for powers `g_{a/N}^{12 k}` whenever
`N ∣ 6 * k` (in particular for the `Γ(N)`-invariant level-`N` power `g_{a/N}^{12 N / gcd(6, N)}` of
`SiegelFunction.Congruence`), providing the input for level-`N` modular function field membership
and `ℤ[j]`-integrality of Siegel modular units.

See `TauCeti.NumberTheory.ModularForms.SiegelFunction.KubertLang` for the extension to
Kubert–Lang products `∏ g_{aᵢ/N}^{mᵢ}`.

## Main definitions and results

* `TauCeti.ModularForm.siegelThetaDisc`: the holomorphic theta-product factor on the unit disc.
* `TauCeti.ModularForm.analyticOnNhd_siegelThetaDisc` and
  `TauCeti.ModularForm.analyticAt_siegelThetaDisc`: unit-disc analyticity of `siegelThetaDisc`.
* `TauCeti.ModularForm.qExpansion_siegelThetaDisc_coeff_eq` and
  `TauCeti.ModularForm.qExpansion_siegelThetaDisc_coeff_mem`: polynomial truncation formula and
  subring membership for the `q_N`-coefficients of `siegelThetaDisc`.
* `TauCeti.ModularForm.siegelFunction_div_eq_mul_siegelThetaDisc` and
  `TauCeti.ModularForm.siegelFunction_div_eq`: factorization of `g_{a/N}` into its constant phase,
  its `q`-power factor, and `siegelThetaDisc`.
* `TauCeti.ModularForm.siegelFunction_div_pow_twelve_mul_eq`,
  `TauCeti.ModularForm.meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul`,
  `TauCeti.ModularForm.laurentQExpansion_siegelFunction_div_pow_twelve_mul`,
  `TauCeti.ModularForm.orderTop_laurentQExpansion_siegelFunction_div_pow_twelve_mul`, and
  `TauCeti.ModularForm.laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem`: cusp
  meromorphy, exact `q_N`-Laurent expansion, cusp order, and subring coefficient membership for
  `g_{a/N}^{12 k}` when `N ∣ 6 * k` (with specializations at `12 * N / Nat.gcd 6 N`).

## References

* D. S. Kubert, S. Lang, *Modular Units*, Chapter 2, §1 and Chapter 3, §5.
* D. H. Shin, *Generation of class fields by Siegel–Ramachandra invariants*, §2.
-/

public section

open Complex Filter Polynomial
open UpperHalfPlane hiding I
open scoped Real Topology

namespace TauCeti.ModularForm

local notation "𝕢" => Function.Periodic.qParam

/-! ### The theta-product factor on the unit disc -/

/-- The theta-product factor of `g_{a/N}` as a function on the open unit disc in
`t = e^{2π i τ / N}`, with `a₀` reduced modulo `N` to `{0, ..., N - 1}` so that every exponent of
`t` is positive for `n ≥ 1`. -/
noncomputable def siegelThetaDisc (N : ℕ) (a : Fin 2 → ℤ) (t : ℂ) : ℂ :=
  (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat) *
    ∏' n : ℕ, (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (N * (n + 1) + (a 0 % (N : ℤ)).toNat)) *
      (1 - (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ *
        t ^ (N * (n + 1) - (a 0 % (N : ℤ)).toNat))

/-- The defining infinite product of `siegelThetaDisc`. -/
theorem siegelThetaDisc_def (N : ℕ) (a : Fin 2 → ℤ) (t : ℂ) :
    siegelThetaDisc N a t =
      (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat) *
        ∏' n : ℕ,
          (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (N * (n + 1) + (a 0 % (N : ℤ)).toNat)) *
            (1 - (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ *
              t ^ (N * (n + 1) - (a 0 % (N : ℤ)).toNat)) :=
  (rfl)

section ThetaDisc

variable {N : ℕ} [NeZero N] (a : Fin 2 → ℤ)

/-- On the unit disc, the theta-product factor splits into its two half-products without any
singularity at `t = 0`: the `n = 0` term of the second half-product is factored out. -/
theorem siegelThetaDisc_eq_of_norm_lt_one {t : ℂ} (ht : ‖t‖ < 1) :
    siegelThetaDisc N a t =
      (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat) *
        (1 - (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ * t ^ (N - (a 0 % (N : ℤ)).toNat)) *
        ((∏' n : ℕ, (1 - (t ^ N) ^ (n + 1) *
            (cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat))) *
          ∏' n : ℕ, (1 - (t ^ N) ^ (n + 1) *
            ((cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ * t ^ (N - (a 0 % (N : ℤ)).toNat)))) := by
  set c := (a 0 % (N : ℤ)).toNat
  set ζ := cexp (2 * π * I * (a 1 : ℂ) / N)
  have hc : c < N := Int.natMod_lt (m := a 0) (NeZero.ne N)
  have htN : ‖t ^ N‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg t) ht (NeZero.ne N)
  have hm₁ : Multipliable fun n : ℕ ↦ 1 - ζ * t ^ (N * (n + 1) + c) :=
    (multipliable_one_sub_pow_mul htN (ζ * t ^ c)).congr fun n ↦ by
      rw [pow_add, ← pow_mul]
      ring
  have hm₂_tail : Multipliable fun n : ℕ ↦ 1 - ζ⁻¹ * t ^ (N * (n + 1 + 1) - c) :=
    (multipliable_one_sub_pow_mul htN (ζ⁻¹ * t ^ (N - c))).congr fun n ↦ by
      have hexp : N * (n + 1 + 1) - c = N * (n + 1) + (N - c) := by
        rw [mul_add, mul_one]
        omega
      rw [hexp, pow_add, ← pow_mul]
      ring
  have hm₂ : Multipliable fun n : ℕ ↦ 1 - ζ⁻¹ * t ^ (N * (n + 1) - c) := by
    have hshift : Multipliable fun n : ℕ ↦
        (fun k : ℕ ↦ 1 - ζ⁻¹ * t ^ (N * (k + 1) - c)) (n + 1) := hm₂_tail
    exact (hshift.hasProd.prod_range_mul).multipliable
  have h1 : (1 - ζ * t ^ c) *
      ((∏' n : ℕ, (1 - ζ * t ^ (N * (n + 1) + c))) *
        ∏' n : ℕ, (1 - ζ⁻¹ * t ^ (N * (n + 1) - c))) =
      (1 - ζ * t ^ c) * (1 - ζ⁻¹ * t ^ (N - c)) *
        ((∏' n : ℕ, (1 - (t ^ N) ^ (n + 1) * (ζ * t ^ c))) *
          ∏' n : ℕ, (1 - (t ^ N) ^ (n + 1) * (ζ⁻¹ * t ^ (N - c)))) := by
    have ht2 := tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - ζ⁻¹ * t ^ (N * (n + 1) - c)) hm₂_tail
    rw [ht2]
    have h0 : N * (0 + 1) - c = N - c := by omega
    rw [h0]
    have heq₁ : (∏' n : ℕ, (1 - ζ * t ^ (N * (n + 1) + c))) =
        ∏' n : ℕ, (1 - (t ^ N) ^ (n + 1) * (ζ * t ^ c)) :=
      tprod_congr fun n ↦ by rw [pow_add, ← pow_mul]; ring
    have heq₂ : (∏' n : ℕ, (1 - ζ⁻¹ * t ^ (N * (n + 1 + 1) - c))) =
        ∏' n : ℕ, (1 - (t ^ N) ^ (n + 1) * (ζ⁻¹ * t ^ (N - c))) :=
      tprod_congr fun n ↦ by
        have := hc.le
        have hexp : N * (n + 1 + 1) - c = N * (n + 1) + (N - c) := by
          rw [mul_add, mul_one]
          omega
        rw [hexp, pow_add, ← pow_mul]
        ring
    rw [heq₁, heq₂]
    ring
  rw [siegelThetaDisc_def, hm₁.tprod_mul hm₂, h1]

/-- The theta-product factor `siegelThetaDisc N a` is analytic on the open unit disc. -/
theorem analyticOnNhd_siegelThetaDisc :
    AnalyticOnNhd ℂ (siegelThetaDisc N a) (Metric.ball (0 : ℂ) 1) := by
  have hdiff : DifferentiableOn ℂ (siegelThetaDisc N a) (Metric.ball (0 : ℂ) 1) := by
    refine DifferentiableOn.congr ?_ fun t ht ↦ siegelThetaDisc_eq_of_norm_lt_one a
      (mem_ball_zero_iff.mp ht)
    have hq₁ : ∀ t ∈ Metric.ball (0 : ℂ) 1, ‖t ^ N‖ < 1 := fun t ht ↦ by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg t) (mem_ball_zero_iff.mp ht) (NeZero.ne N)
    exact ((differentiableOn_const _).sub ((differentiableOn_const _).mul
        (differentiableOn_id.pow _))).mul
      ((differentiableOn_const _).sub ((differentiableOn_const _).mul
        (differentiableOn_id.pow _))) |>.mul
      ((differentiableOn_tprod_one_sub_pow_mul Metric.isOpen_ball (differentiableOn_id.pow N) hq₁
        ((differentiableOn_const _).mul (differentiableOn_id.pow _))).mul
        (differentiableOn_tprod_one_sub_pow_mul Metric.isOpen_ball (differentiableOn_id.pow N) hq₁
          ((differentiableOn_const _).mul (differentiableOn_id.pow _))))
  exact hdiff.analyticOnNhd Metric.isOpen_ball

/-- The theta-product factor `siegelThetaDisc N a` is analytic at `0`. -/
theorem analyticAt_siegelThetaDisc : AnalyticAt ℂ (siegelThetaDisc N a) 0 :=
  analyticOnNhd_siegelThetaDisc a 0 (Metric.mem_ball_self one_pos)

/-- At `t = 0`, `siegelThetaDisc N a 0` is `1 - e^{2π i a₁ / N}` when `N ∣ a₀` and `1` otherwise. -/
theorem siegelThetaDisc_zero :
    siegelThetaDisc N a 0 =
      if a 0 % (N : ℤ) = 0 then 1 - cexp (2 * π * I * (a 1 : ℂ) / N) else 1 := by
  rw [siegelThetaDisc_eq_of_norm_lt_one a (by simp)]
  have hc : (a 0 % (N : ℤ)).toNat < N := Int.natMod_lt (m := a 0) (NeZero.ne N)
  have hN0 : (0 : ℂ) ^ N = 0 := zero_pow (NeZero.ne N)
  have hsub0 : (0 : ℂ) ^ (N - (a 0 % (N : ℤ)).toNat) = 0 := zero_pow (by omega)
  have hmod : (a 0 % (N : ℤ)).toNat = 0 ↔ a 0 % (N : ℤ) = 0 := by
    have h0 := Int.emod_nonneg (a 0) (Int.natCast_ne_zero.mpr (NeZero.ne N))
    omega
  simp only [hN0, zero_pow (Nat.succ_ne_zero _), zero_mul, mul_zero, sub_zero, tprod_one,
    mul_one, hsub0]
  by_cases h0 : a 0 % (N : ℤ) = 0
  · simp [h0]
  · simp [h0, hmod.not.mpr h0]

/-- `siegelThetaDisc N a 0 = 0` if and only if `a / N ∈ ℤ²`. -/
@[simp]
theorem siegelThetaDisc_zero_eq_zero_iff :
    siegelThetaDisc N a 0 = 0 ↔ ∀ i, (N : ℤ) ∣ a i := by
  rw [siegelThetaDisc_zero]
  constructor
  · intro h
    split_ifs at h with h0
    · rw [sub_eq_zero] at h
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h.symm
      have hk' : (a 1 : ℤ) = k * N := by
        have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
        have : ((a 1 : ℂ) / N) = (k : ℂ) := mul_left_cancel₀ hpi (by linear_combination hk)
        have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
        exact_mod_cast (div_eq_iff hN').mp this
      intro i
      fin_cases i
      · exact Int.dvd_of_emod_eq_zero h0
      · exact ⟨k, hk'.trans (mul_comm _ _)⟩
    · exact absurd h one_ne_zero
  · intro ha
    have h0 : a 0 % (N : ℤ) = 0 := Int.emod_eq_zero_of_dvd (ha 0)
    obtain ⟨k, hk⟩ := ha 1
    have heq : 2 * π * I * (a 1 : ℂ) / N = (k : ℂ) * (2 * π * I) := by
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      have ha1 : (a 1 : ℂ) = N * k := by exact_mod_cast hk
      rw [ha1]
      field_simp
    simp [h0, heq, Complex.exp_int_mul_two_pi_mul_I]

/-- When `a / N ∉ ℤ²`, `siegelThetaDisc N a 0 ≠ 0`. -/
theorem siegelThetaDisc_zero_ne_zero (ha : ¬ ∀ i, (N : ℤ) ∣ a i) :
    siegelThetaDisc N a 0 ≠ 0 :=
  (siegelThetaDisc_zero_eq_zero_iff a).not.mpr ha

/-- Expressing `g_{a/N}` in terms of `siegelThetaDisc N a (𝕢 N τ)` when `0 ≤ a₀ < N`. -/
theorem siegelFunction_div_eq_mul_siegelThetaDisc {a : Fin 2 → ℤ} (ha0 : 0 ≤ a 0)
    (haN : a 0 < N) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ =
      -cexp (π * I * ((a 1 : ℂ) / N) * ((a 0 : ℂ) / N - 1)) *
        cexp (π * I * bernoulliFun 2 ((a 0 : ℝ) / N) * τ) *
        siegelThetaDisc N a (𝕢 N τ) := by
  have hmod : (a 0 % (N : ℤ)).toNat = (a 0).toNat := by
    rw [Int.emod_eq_of_lt ha0 (by exact_mod_cast haN)]
  have hq : 𝕢 N τ ^ N = cexp (2 * π * I * τ) := by
    rw [← mul_one (N : ℝ), TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne N)]
    simp [Function.Periodic.qParam]
  have hw : cexp (2 * π * I * (a 1 : ℂ) / N) * 𝕢 N τ ^ (a 0 % (N : ℤ)).toNat =
      cexp (2 * π * I * (((a 0 : ℝ) / N : ℝ) * τ + ((a 1 : ℝ) / N : ℝ))) := by
    rw [hmod, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have ha0' : (((a 0).toNat : ℕ) : ℂ) = (a 0 : ℂ) := by
      exact_mod_cast Int.toNat_of_nonneg ha0
    push_cast
    rw [ha0']
    ring
  have heq : siegelThetaDisc N a (𝕢 N τ) =
      qTheta (cexp (2 * π * I * τ))
        (cexp (2 * π * I * (((a 0 : ℝ) / N : ℝ) * τ + ((a 1 : ℝ) / N : ℝ)))) := by
    rw [siegelThetaDisc_def, qTheta_def, hw]
    congr 1
    refine tprod_congr fun n ↦ ?_
    have hexp₁ : cexp (2 * π * I * (a 1 : ℂ) / N) *
        𝕢 N τ ^ (N * (n + 1) + (a 0 % (N : ℤ)).toNat) =
        cexp (2 * π * I * τ) ^ (n + 1) *
          cexp (2 * π * I * (((a 0 : ℝ) / N : ℝ) * τ + ((a 1 : ℝ) / N : ℝ))) := by
      rw [pow_add, pow_mul, hq, ← hw]
      ring
    have hexp₂ : (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ *
        𝕢 N τ ^ (N * (n + 1) - (a 0 % (N : ℤ)).toNat) =
        cexp (2 * π * I * τ) ^ (n + 1) *
          (cexp (2 * π * I * (((a 0 : ℝ) / N : ℝ) * τ + ((a 1 : ℝ) / N : ℝ))))⁻¹ := by
      rw [← hw, mul_inv]
      have hle : (a 0 % (N : ℤ)).toNat ≤ N * (n + 1) :=
        (Int.natMod_lt (m := a 0) (NeZero.ne N)).le.trans
          (Nat.le_mul_of_pos_right N (Nat.succ_pos n))
      have hsub : 𝕢 N τ ^ (N * (n + 1) - (a 0 % (N : ℤ)).toNat) *
          𝕢 N τ ^ (a 0 % (N : ℤ)).toNat = 𝕢 N τ ^ (N * (n + 1)) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have hpow : 𝕢 N τ ^ (N * (n + 1) - (a 0 % (N : ℤ)).toNat) =
          𝕢 N τ ^ (N * (n + 1)) * (𝕢 N τ ^ (a 0 % (N : ℤ)).toNat)⁻¹ :=
        (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ (Function.Periodic.qParam_ne_zero _))).mpr hsub
      rw [hpow, pow_mul, hq]
      ring
    rw [hexp₁, hexp₂]
  rw [siegelFunction_eq_qTheta, heq]
  simp only [ofReal_div, ofReal_intCast, ofReal_natCast]
  ring

/-- The cusp function of `τ ↦ siegelThetaDisc N a (𝕢 N τ)` agrees with `siegelThetaDisc N a` near
`0`. -/
theorem cuspFunction_siegelThetaDisc_eventuallyEq :
    cuspFunction N (fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)) =ᶠ[𝓝 0] siegelThetaDisc N a := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine TauCeti.UpperHalfPlane.cuspFunction_eventuallyEq_nhds_of_continuousAt ?_
    (analyticAt_siegelThetaDisc a).continuousAt
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) zero_lt_one)] with q hq hq1
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq
  have him : 0 < (Function.Periodic.invQParam N q).im :=
    Function.Periodic.im_invQParam_pos_of_norm_lt_one (Nat.cast_pos.mpr (NeZero.pos N))
      (mem_ball_zero_iff.mp hq1) hq
  rw [TauCeti.UpperHalfPlane.cuspFunction_of_ne_zero hq, ofComplex_apply_of_im_pos him,
    Function.Periodic.qParam_right_inv hN hq]

/-- `τ ↦ siegelThetaDisc N a (𝕢 N τ)` has an analytic cusp function at `0`. -/
theorem analyticAt_cuspFunction_siegelThetaDisc :
    AnalyticAt ℂ (cuspFunction N fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)) 0 :=
  (analyticAt_siegelThetaDisc a).congr (cuspFunction_siegelThetaDisc_eventuallyEq a).symm

/-- The constant term of the `q_N`-expansion of `siegelThetaDisc N a` is its value at `0`. -/
theorem qExpansion_siegelThetaDisc_coeff_zero :
    (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ))).coeff 0 = siegelThetaDisc N a 0 := by
  rw [_root_.UpperHalfPlane.qExpansion_coeff]
  simpa using (cuspFunction_siegelThetaDisc_eventuallyEq a).eq_of_nhds

private noncomputable def thetaTerm (N c : ℕ) (ζ t : ℂ) (n : ℕ) : ℂ :=
  (1 - ζ * t ^ (N * (n + 1) + c)) * (1 - ζ⁻¹ * t ^ (N * (n + 1) - c))

private theorem norm_thetaTerm_sub_one_le (N c m : ℕ) (hN : 1 ≤ N) (hc : c < N)
    (ζ t : ℂ) (ht : ‖t‖ ≤ 1 / 2) (k : ℕ) :
    ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖ ≤
      (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖) * ‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k := by
  have ht1 : ‖t‖ ≤ 1 := ht.trans (by norm_num)
  have hexp₁ : m + 1 + k ≤ N * (k + (m + 1) + 1) + c := by nlinarith
  have hexp₂ : m + 1 + k ≤ N * (k + (m + 1) + 1) - c := by
    have hmul : m + 1 + k + c ≤ N * (k + (m + 1) + 1) := by nlinarith
    omega
  have hpow_le (e : ℕ) (he : m + 1 + k ≤ e) :
      ‖t‖ ^ e ≤ ‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k := by
    calc ‖t‖ ^ e ≤ ‖t‖ ^ (m + 1 + k) :=
          pow_le_pow_of_le_one (norm_nonneg t) ht1 he
      _ = ‖t‖ ^ (m + 1) * ‖t‖ ^ k := pow_add _ _ _
      _ ≤ ‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg t) ht k) (by positivity)
  have h1 : ‖ζ * t ^ (N * (k + (m + 1) + 1) + c)‖ ≤
      ‖ζ‖ * (‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hpow_le _ hexp₁) (norm_nonneg _)
  have h2 : ‖ζ⁻¹ * t ^ (N * (k + (m + 1) + 1) - c)‖ ≤
      ‖ζ⁻¹‖ * (‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k) := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hpow_le _ hexp₂) (norm_nonneg _)
  have h12 : ‖ζ * t ^ (N * (k + (m + 1) + 1) + c)‖ *
      ‖ζ⁻¹ * t ^ (N * (k + (m + 1) + 1) - c)‖ ≤
      (‖ζ‖ * ‖ζ⁻¹‖) * (‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k) := by
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    have hpow₃ := hpow_le ((N * (k + (m + 1) + 1) + c) + (N * (k + (m + 1) + 1) - c))
      (hexp₁.trans (Nat.le_add_right _ _))
    rw [pow_add] at hpow₃
    calc (‖ζ‖ * ‖t‖ ^ (N * (k + (m + 1) + 1) + c)) *
          (‖ζ⁻¹‖ * ‖t‖ ^ (N * (k + (m + 1) + 1) - c))
        = (‖ζ‖ * ‖ζ⁻¹‖) * (‖t‖ ^ (N * (k + (m + 1) + 1) + c) *
            ‖t‖ ^ (N * (k + (m + 1) + 1) - c)) := by ring
      _ ≤ (‖ζ‖ * ‖ζ⁻¹‖) * (‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left hpow₃ (by positivity)
  rw [thetaTerm]
  calc ‖(1 - ζ * t ^ (N * (k + (m + 1) + 1) + c)) *
          (1 - ζ⁻¹ * t ^ (N * (k + (m + 1) + 1) - c)) - 1‖
      ≤ ‖ζ * t ^ (N * (k + (m + 1) + 1) + c)‖ +
          ‖ζ⁻¹ * t ^ (N * (k + (m + 1) + 1) - c)‖ +
          ‖ζ * t ^ (N * (k + (m + 1) + 1) + c)‖ *
            ‖ζ⁻¹ * t ^ (N * (k + (m + 1) + 1) - c)‖ :=
        TauCeti.norm_one_sub_mul_one_sub_sub_one_le _ _
    _ ≤ ‖ζ‖ * (‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k) +
          ‖ζ⁻¹‖ * (‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k) +
          (‖ζ‖ * ‖ζ⁻¹‖) * (‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k) := add_le_add (add_le_add h1 h2) h12
    _ = (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖) * ‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k := by ring

private theorem summable_norm_thetaTerm_sub_one (N c m : ℕ) (hN : 1 ≤ N) (hc : c < N)
    (ζ t : ℂ) (ht : ‖t‖ ≤ 1 / 2) :
    Summable (fun k : ℕ ↦ ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖) ∧
      ∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖ ≤
        2 * (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖) * ‖t‖ ^ (m + 1) := by
  have hterm := fun k ↦ norm_thetaTerm_sub_one_le N c m hN hc ζ t ht k
  have hgeom : Summable fun k : ℕ ↦
      (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖) * ‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k :=
    summable_geometric_two.mul_left _
  have hsum := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hgeom
  refine ⟨hsum, ?_⟩
  calc ∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖
      ≤ ∑' k : ℕ, (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖) * ‖t‖ ^ (m + 1) * (1 / 2 : ℝ) ^ k :=
        Summable.tsum_le_tsum hterm hsum hgeom
    _ = (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖) * ‖t‖ ^ (m + 1) * ∑' k : ℕ, (1 / 2 : ℝ) ^ k :=
        tsum_mul_left
    _ = 2 * (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖) * ‖t‖ ^ (m + 1) := by
        rw [tsum_geometric_two]
        ring

private theorem tprod_thetaTerm_sub_one_isBigO (N c m : ℕ) (hN : 1 ≤ N) (hc : c < N)
    (ζ : ℂ) :
    (fun t : ℂ ↦ (∏' k : ℕ, thetaTerm N c ζ t (k + (m + 1))) - 1) =O[𝓝 0]
      fun t ↦ t ^ (m + 1) := by
  set C₀ : ℝ := 2 * (‖ζ‖ + ‖ζ⁻¹‖ + ‖ζ‖ * ‖ζ⁻¹‖)
  refine Asymptotics.IsBigO.of_bound (2 * C₀) ?_
  have hsmall : ∀ᶠ t : ℂ in 𝓝 0, ‖t‖ ≤ 1 / 2 ∧ C₀ * ‖t‖ ^ (m + 1) ≤ 1 / 2 := by
    have hpow : Tendsto (fun t : ℂ ↦ C₀ * ‖t‖ ^ (m + 1)) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul ((continuous_norm.tendsto (0 : ℂ)).pow (m + 1)))
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2),
      hpow.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with t ht hCt
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using ht, hCt⟩
  filter_upwards [hsmall] with t ⟨ht, hCt⟩
  have ht' := summable_norm_thetaTerm_sub_one N c m hN hc ζ t ht
  have hprod := norm_tprod_one_add_sub_one_le
    (f := fun k ↦ thetaTerm N c ζ t (k + (m + 1)) - 1) ht'.1
  simp only [add_sub_cancel] at hprod
  have hsum_nn : 0 ≤ ∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖ :=
    tsum_nonneg fun _ ↦ norm_nonneg _
  have hexp : Real.exp (∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖) - 1 ≤
      2 * ∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖ := by
    have h_abs := Real.abs_exp_sub_one_le (by
      rw [abs_of_nonneg hsum_nn]
      exact (ht'.2.trans hCt).trans (by norm_num) :
      |∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖| ≤ 1)
    rw [abs_of_nonneg hsum_nn] at h_abs
    exact (le_abs_self _).trans h_abs
  calc ‖(∏' k : ℕ, thetaTerm N c ζ t (k + (m + 1))) - 1‖
      ≤ Real.exp (∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖) - 1 := hprod
    _ ≤ 2 * ∑' k : ℕ, ‖thetaTerm N c ζ t (k + (m + 1)) - 1‖ := hexp
    _ ≤ 2 * (C₀ * ‖t‖ ^ (m + 1)) := by gcongr; exact ht'.2
    _ = 2 * C₀ * ‖t ^ (m + 1)‖ := by rw [norm_pow, ← mul_assoc]

private theorem thetaTerm_sub_finset_prod_eq (N c m : ℕ) (hN : 1 ≤ N) (hc : c < N)
    (ζ t : ℂ) (ht : ‖t‖ ≤ 1 / 2) :
    (1 - ζ * t ^ c) * (∏' n : ℕ, thetaTerm N c ζ t n) -
        (1 - ζ * t ^ c) * ∏ n ∈ Finset.range (m + 1), thetaTerm N c ζ t n =
      ((1 - ζ * t ^ c) * ∏ n ∈ Finset.range (m + 1), thetaTerm N c ζ t n) *
        ((∏' k : ℕ, thetaTerm N c ζ t (k + (m + 1))) - 1) := by
  have hmult1 := multipliable_one_add_of_summable
    (f := fun k : ℕ ↦ thetaTerm N c ζ t (k + (m + 1)) - 1)
    (summable_norm_thetaTerm_sub_one N c m hN hc ζ t ht).1
  have hmult : Multipliable (fun k : ℕ ↦ thetaTerm N c ζ t (k + (m + 1))) := by
    simpa only [add_sub_cancel] using hmult1
  have hsplit := hmult.prod_mul_tprod_nat_mul'
  rw [← hsplit]
  ring

/-- Truncating the infinite product in `siegelThetaDisc N a` at index `m` leaves an `O(t^{m+1})`
remainder at `t = 0`. -/
theorem siegelThetaDisc_sub_finset_prod_isBigO (m : ℕ) :
    (fun t : ℂ ↦ siegelThetaDisc N a t -
      (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat) *
        ∏ n ∈ Finset.range (m + 1),
          (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (N * (n + 1) + (a 0 % (N : ℤ)).toNat)) *
          (1 - (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ *
            t ^ (N * (n + 1) - (a 0 % (N : ℤ)).toNat))) =O[𝓝 0]
      fun t ↦ t ^ (m + 1) := by
  have hc : (a 0 % (N : ℤ)).toNat < N := Int.natMod_lt (m := a 0) (NeZero.ne N)
  have htail_bigO := tprod_thetaTerm_sub_one_isBigO N (a 0 % (N : ℤ)).toNat m
    (NeZero.pos N) hc (cexp (2 * π * I * (a 1 : ℂ) / N))
  have htheta_cont (n : ℕ) :
      Continuous (fun t : ℂ ↦ thetaTerm N (a 0 % (N : ℤ)).toNat
        (cexp (2 * π * I * (a 1 : ℂ) / N)) t n) := by
    unfold thetaTerm; fun_prop
  have hprefix_cont : Continuous (fun t : ℂ ↦
      (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat) *
        ∏ n ∈ Finset.range (m + 1),
          thetaTerm N (a 0 % (N : ℤ)).toNat (cexp (2 * π * I * (a 1 : ℂ) / N)) t n) :=
    (by fun_prop : Continuous fun t : ℂ ↦
      1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat).mul
      (continuous_finsetProd _ fun n _ ↦ htheta_cont n)
  have hprefix_bigO :
      (fun t : ℂ ↦ (1 - cexp (2 * π * I * (a 1 : ℂ) / N) * t ^ (a 0 % (N : ℤ)).toNat) *
        ∏ n ∈ Finset.range (m + 1),
          thetaTerm N (a 0 % (N : ℤ)).toNat (cexp (2 * π * I * (a 1 : ℂ) / N)) t n) =O[𝓝 0]
      fun _ ↦ (1 : ℂ) :=
    hprefix_cont.continuousAt.norm.isBoundedUnder_le.isBigO_one ℂ
  have hmul := hprefix_bigO.mul htail_bigO
  simp only [one_mul] at hmul
  refine hmul.congr' ?_ EventuallyEq.rfl
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1 / 2)] with t ht
  have ht' : ‖t‖ ≤ 1 / 2 := by simpa [Metric.mem_closedBall, dist_zero_right] using ht
  rw [siegelThetaDisc_def]
  exact (thetaTerm_sub_finset_prod_eq N (a 0 % (N : ℤ)).toNat m (NeZero.pos N) hc
    (cexp (2 * π * I * (a 1 : ℂ) / N)) t ht').symm

/-- The `m`-th `q_N`-coefficient of `siegelThetaDisc N a` equals the `m`-th coefficient of the
degree-`m` partial product polynomial over `ℂ`. -/
theorem qExpansion_siegelThetaDisc_coeff_eq (m : ℕ) :
    (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ))).coeff m =
      ((1 - C (cexp (2 * π * I * (a 1 : ℂ) / N)) * X ^ (a 0 % (N : ℤ)).toNat) *
        ∏ n ∈ Finset.range (m + 1),
          (1 - C (cexp (2 * π * I * (a 1 : ℂ) / N)) *
              X ^ (N * (n + 1) + (a 0 % (N : ℤ)).toNat)) *
            (1 - C (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ *
              X ^ (N * (n + 1) - (a 0 % (N : ℤ)).toNat))).coeff m := by
  set c := (a 0 % (N : ℤ)).toNat
  set ζ := cexp (2 * π * I * (a 1 : ℂ) / N)
  let P : ℂ[X] := (1 - C ζ * X ^ c) *
    ∏ n ∈ Finset.range (m + 1),
      (1 - C ζ * X ^ (N * (n + 1) + c)) * (1 - C ζ⁻¹ * X ^ (N * (n + 1) - c))
  have hP_eval (t : ℂ) : P.eval t =
      (1 - ζ * t ^ c) * ∏ n ∈ Finset.range (m + 1),
        (1 - ζ * t ^ (N * (n + 1) + c)) * (1 - ζ⁻¹ * t ^ (N * (n + 1) - c)) := by
    simp [P, eval_prod]
  -- By `siegelThetaDisc_sub_finset_prod_isBigO`, `siegelThetaDisc N a - P.eval` vanishes to order
  -- at least `m + 1` at `0`, so its `m`-th derivative at `0` is zero.
  have hbigO : (fun t : ℂ ↦ siegelThetaDisc N a t - P.eval t) =O[𝓝 0] fun t ↦ t ^ (m + 1) := by
    simpa only [hP_eval] using siegelThetaDisc_sub_finset_prod_isBigO a m
  have hP_an : AnalyticAt ℂ (fun t : ℂ ↦ P.eval t) 0 := by
    simp_rw [Polynomial.eval_eq_sum_range]
    fun_prop
  have han : AnalyticAt ℂ (fun t : ℂ ↦ siegelThetaDisc N a t - P.eval t) 0 :=
    (analyticAt_siegelThetaDisc a).sub hP_an
  have hord : ((m + 1 : ℕ) : ℕ∞) ≤
      analyticOrderAt (fun t : ℂ ↦ siegelThetaDisc N a t - P.eval t) 0 := by
    have hle := han.analyticOrderAt_le_of_isBigO hbigO
    have hmon : analyticOrderAt (fun t : ℂ ↦ t ^ (m + 1)) 0 = ((m + 1 : ℕ) : ℕ∞) := by
      simpa only [Pi.pow_def, sub_zero] using
        analyticOrderAt_centeredMonomial (z₀ := (0 : ℂ)) (n := m + 1)
    rwa [hmon] at hle
  have hderiv_sub : iteratedDeriv m (fun t : ℂ ↦ siegelThetaDisc N a t - P.eval t) 0 = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp hord m (Nat.lt_succ_self m)
  have hderiv_eq : iteratedDeriv m (siegelThetaDisc N a) 0 =
      iteratedDeriv m (fun t ↦ P.eval t) 0 := by
    have h1 : ContDiffAt ℂ m (siegelThetaDisc N a) 0 := (analyticAt_siegelThetaDisc a).contDiffAt
    have h2 : ContDiffAt ℂ m (fun t : ℂ ↦ P.eval t) 0 := hP_an.contDiffAt
    rw [← sub_eq_zero, ← iteratedDeriv_fun_sub h1 h2]
    exact hderiv_sub
  rw [_root_.UpperHalfPlane.qExpansion_coeff,
    (cuspFunction_siegelThetaDisc_eventuallyEq a).iteratedDeriv_eq, hderiv_eq,
    Polynomial.iteratedDeriv_eval_zero]
  have hm_ne : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  rw [inv_mul_eq_div, mul_div_cancel_left₀ _ hm_ne]

/-- The `m`-th `q_N`-coefficient of `siegelThetaDisc N a` lies in any subring `S` of `ℂ`
containing `e^{2π i / N}`. -/
theorem qExpansion_siegelThetaDisc_coeff_mem (S : Subring ℂ)
    (hζ : cexp (2 * π * I / N) ∈ S) (m : ℕ) :
    (qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ))).coeff m ∈ S := by
  set c := (a 0 % (N : ℤ)).toNat
  have hzpow (k : ℤ) : cexp (2 * π * I / N) ^ k ∈ S :=
    S.zpow_mem_of_pow_eq_one hζ (NeZero.ne N)
      (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).pow_eq_one k
  have hζ_pow (k : ℤ) : cexp (2 * π * I * (k : ℂ) / N) = cexp (2 * π * I / N) ^ k := by
    rw [← Complex.exp_int_mul]
    congr 1
    ring
  have hζ_mem : cexp (2 * π * I * (a 1 : ℂ) / N) ∈ S := by
    rw [hζ_pow]
    exact hzpow (a 1)
  have hζ_inv_mem : (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ ∈ S := by
    rw [hζ_pow, ← zpow_neg]
    exact hzpow (-a 1)
  let P : S[X] := (1 - C ⟨_, hζ_mem⟩ * X ^ c) *
    ∏ n ∈ Finset.range (m + 1),
      (1 - C ⟨_, hζ_mem⟩ * X ^ (N * (n + 1) + c)) *
        (1 - C ⟨_, hζ_inv_mem⟩ * X ^ (N * (n + 1) - c))
  have hmap : Polynomial.map S.subtype P =
      (1 - C (cexp (2 * π * I * (a 1 : ℂ) / N)) * X ^ c) *
        ∏ n ∈ Finset.range (m + 1),
          (1 - C (cexp (2 * π * I * (a 1 : ℂ) / N)) * X ^ (N * (n + 1) + c)) *
            (1 - C (cexp (2 * π * I * (a 1 : ℂ) / N))⁻¹ * X ^ (N * (n + 1) - c)) := by
    simp [P, Polynomial.map_prod]
  rw [qExpansion_siegelThetaDisc_coeff_eq, ← hmap, Polynomial.coeff_map]
  exact (P.coeff m).2

end ThetaDisc

/-! ### General factorization of `g_{a/N}` -/

section General

variable {N : ℕ} [NeZero N]

/-- Reducing the vector `a` modulo `N` leaves `siegelThetaDisc N a` unchanged. -/
@[simp]
theorem siegelThetaDisc_mod (a : Fin 2 → ℤ) (t : ℂ) :
    siegelThetaDisc N (fun i ↦ a i % (N : ℤ)) t = siegelThetaDisc N a t := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hmod0 : ((fun i ↦ a i % (N : ℤ)) 0 % (N : ℤ)).toNat = (a 0 % (N : ℤ)).toNat := by
    dsimp only
    rw [Int.emod_emod]
  have hζ : cexp (2 * π * I * ((a 1 % (N : ℤ) : ℤ) : ℂ) / N) =
      cexp (2 * π * I * (a 1 : ℂ) / N) := by
    have hdiv : a 1 = (a 1 / (N : ℤ)) * N + a 1 % (N : ℤ) := (Int.ediv_mul_add_emod (a 1) N).symm
    have hdiv' : (a 1 : ℂ) = (a 1 / (N : ℤ) : ℤ) * N + (a 1 % (N : ℤ) : ℤ) := by
      exact_mod_cast hdiv
    rw [hdiv']
    have heq : 2 * π * I * (((a 1 / (N : ℤ) : ℤ) : ℂ) * N + (a 1 % (N : ℤ) : ℤ)) / N =
        2 * π * I * ((a 1 % (N : ℤ) : ℤ) : ℂ) / N + (a 1 / (N : ℤ) : ℤ) * (2 * π * I) := by
      field_simp
      ring
    rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [siegelThetaDisc_def, hmod0, hζ]

/-- Exact factorization of `g_{a/N}` for an arbitrary integral vector `a : Fin 2 → ℤ`, reducing
`a₀` modulo `N` to `{0, ..., N - 1}` so that `siegelThetaDisc N a` captures the full infinite
product at `t = 𝕢 N τ`. -/
theorem siegelFunction_div_eq (a : Fin 2 → ℤ) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ =
      ((-1 : ℂ) ^ ((a 0 / (N : ℤ)) * (a 1 / (N : ℤ)) + a 0 / (N : ℤ) + a 1 / (N : ℤ) + 1) *
        cexp (-(π * I * ((a 0 / (N : ℤ) : ℤ) * ((a 1 % (N : ℤ) : ℤ) : ℂ) -
          (a 1 / (N : ℤ) : ℤ) * ((a 0 % (N : ℤ) : ℤ) : ℂ)) / N)) *
        cexp (π * I * ((a 1 % (N : ℤ) : ℤ) : ℂ) *
          (((a 0 % (N : ℤ) : ℤ) : ℂ) - N) / (N : ℂ) ^ 2)) *
        cexp (π * I * bernoulliFun 2 (((a 0 % (N : ℤ) : ℤ) : ℝ) / N) * τ) *
        siegelThetaDisc N a (𝕢 N τ) := by
  set r : Fin 2 → ℤ := fun i ↦ a i % (N : ℤ)
  set q : Fin 2 → ℤ := fun i ↦ a i / (N : ℤ)
  have hr0 : 0 ≤ r 0 := Int.emod_nonneg (a 0) (Int.natCast_ne_zero.mpr (NeZero.ne N))
  have hrN : r 0 < N := Int.emod_lt_of_pos (a 0) (Int.natCast_pos.mpr (NeZero.pos N))
  have ha_eq : (fun i ↦ (a i : ℝ) / N) = (fun i ↦ (r i : ℝ) / N) + fun i ↦ (q i : ℝ) := by
    ext i
    have h := Int.ediv_mul_add_emod (a i) N
    have h' : (a i : ℝ) = (q i : ℝ) * N + (r i : ℝ) := by exact_mod_cast h.symm
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    rw [Pi.add_apply, h']
    field_simp
    ring
  rw [ha_eq, siegelFunction_add_intCast _ _ τ.im_pos,
    siegelFunction_div_eq_mul_siegelThetaDisc hr0 hrN τ, siegelThetaDisc_mod]
  simp only [ofReal_intCast, ofReal_div, ofReal_natCast]
  have hphase1 : cexp (-(π * I * ((q 0 : ℂ) * ((r 1 : ℂ) / N) - (q 1 : ℂ) * ((r 0 : ℂ) / N)))) =
      cexp (-(π * I * ((q 0 : ℂ) * (r 1 : ℂ) - (q 1 : ℂ) * (r 0 : ℂ)) / N)) := by
    congr 1
    ring
  have hphase2 : cexp (π * I * ((r 1 : ℂ) / N) * ((r 0 : ℂ) / N - 1)) =
      cexp (π * I * (r 1 : ℂ) * ((r 0 : ℂ) - N) / (N : ℂ) ^ 2) := by
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    congr 1
    field_simp
  have hsign : ((-1 : ℂ) ^ (q 0 * q 1 + q 0 + q 1)) * (-1 : ℂ) =
      (-1 : ℂ) ^ (q 0 * q 1 + q 0 + q 1 + 1) := by
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0) (q 0 * q 1 + q 0 + q 1) 1, zpow_one]
  rw [hphase1, hphase2]
  calc
    ((-1 : ℂ) ^ (q 0 * q 1 + q 0 + q 1) *
        cexp (-(π * I * ((q 0 : ℂ) * (r 1 : ℂ) - (q 1 : ℂ) * (r 0 : ℂ)) / N))) *
        (-cexp (π * I * (r 1 : ℂ) * ((r 0 : ℂ) - N) / (N : ℂ) ^ 2) *
          cexp (π * I * bernoulliFun 2 ((r 0 : ℝ) / N) * τ) *
          siegelThetaDisc N a (𝕢 N τ))
      = ((-1 : ℂ) ^ (q 0 * q 1 + q 0 + q 1) * (-1 : ℂ)) *
          cexp (-(π * I * ((q 0 : ℂ) * (r 1 : ℂ) - (q 1 : ℂ) * (r 0 : ℂ)) / N)) *
          cexp (π * I * (r 1 : ℂ) * ((r 0 : ℂ) - N) / (N : ℂ) ^ 2) *
          cexp (π * I * bernoulliFun 2 ((r 0 : ℝ) / N) * τ) *
          siegelThetaDisc N a (𝕢 N τ) := by ring
    _ = _ := by rw [hsign]

/-- The `(2 * N)`-th power of the constant prefactor in `siegelFunction_div_eq` is an explicit
`N`-th root of unity. -/
theorem neg_one_zpow_mul_exp_mul_exp_pow_two_mul (a : Fin 2 → ℤ) :
    ((-1 : ℂ) ^ ((a 0 / (N : ℤ)) * (a 1 / (N : ℤ)) + a 0 / (N : ℤ) + a 1 / (N : ℤ) + 1) *
      cexp (-(π * I * ((a 0 / (N : ℤ) : ℤ) * ((a 1 % (N : ℤ) : ℤ) : ℂ) -
        (a 1 / (N : ℤ) : ℤ) * ((a 0 % (N : ℤ) : ℤ) : ℂ)) / N)) *
      cexp (π * I * ((a 1 % (N : ℤ) : ℤ) : ℂ) *
        (((a 0 % (N : ℤ) : ℤ) : ℂ) - N) / (N : ℂ) ^ 2)) ^ (2 * N) =
      cexp (2 * π * I / N) ^ ((a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N)) := by
  set r : Fin 2 → ℤ := fun i ↦ a i % (N : ℤ)
  set q : Fin 2 → ℤ := fun i ↦ a i / (N : ℤ)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [mul_pow, mul_pow]
  have hsign : ((-1 : ℂ) ^ (q 0 * q 1 + q 0 + q 1 + 1)) ^ (2 * N) = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul]
    refine Even.neg_one_zpow ⟨(q 0 * q 1 + q 0 + q 1 + 1) * N, ?_⟩
    push_cast
    ring
  have htrans :
      cexp (-(π * I * ((q 0 : ℂ) * (r 1 : ℂ) - (q 1 : ℂ) * (r 0 : ℂ)) / N)) ^ (2 * N) = 1 := by
    rw [← Complex.exp_nat_mul]
    have heq : ((2 * N : ℕ) : ℂ) *
        (-(π * I * ((q 0 : ℂ) * (r 1 : ℂ) - (q 1 : ℂ) * (r 0 : ℂ)) / N)) =
        ((q 1 * r 0 - q 0 * r 1 : ℤ) : ℂ) * (2 * π * I) := by
      push_cast
      field_simp
      ring
    rw [heq, Complex.exp_int_mul_two_pi_mul_I]
  have hconst : cexp (π * I * (r 1 : ℂ) * ((r 0 : ℂ) - N) / (N : ℂ) ^ 2) ^ (2 * N) =
      cexp (2 * π * I / N) ^ (r 1 * (r 0 - N)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul]
    congr 1
    push_cast
    field_simp
  rw [hsign, htrans, hconst, one_mul, one_mul]

end General

/-! ### Fourier expansions of `g_{a/N}^{12 k}` and `g_{a/N}^{12 N / gcd(6, N)}` at period `N` -/

section Power

variable {N : ℕ} [NeZero N]

/-- Factorization of `g_{a/N}^{12 k}` (whenever `N ∣ 6 * k`) into a `2π i / N` root of unity,
an integer power of `𝕢 N τ`, and the `12 k`-th power of `siegelThetaDisc N a (𝕢 N τ)`. -/
theorem siegelFunction_div_pow_twelve_mul_eq (a : Fin 2 → ℤ) {k : ℕ} (hk : N ∣ 6 * k) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k) =
      cexp (2 * π * I / N) ^
          (((6 * k / N : ℕ) : ℤ) * (a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N)) *
        𝕢 N τ ^ (((6 * k / N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 -
          6 * k * (a 0 % (N : ℤ)) + k * N) *
        siegelThetaDisc N a (𝕢 N τ) ^ (12 * k) := by
  set r : Fin 2 → ℤ := fun i ↦ a i % (N : ℤ)
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  set m : ℕ := 6 * k / N
  have hmul_div : N * m = 6 * k := Nat.mul_div_cancel' hk
  have hmul_div' : (m : ℂ) * N = 6 * k := by exact_mod_cast (mul_comm N m ▸ hmul_div)
  have hexp_12k : 12 * k = (2 * N) * m := by
    calc 12 * k = 2 * (6 * k) := by ring
      _ = 2 * (N * m) := by rw [hmul_div]
      _ = (2 * N) * m := by ring
  rw [siegelFunction_div_eq a τ, mul_pow, mul_pow]
  have hphase :
      ((-1 : ℂ) ^ ((a 0 / (N : ℤ)) * (a 1 / (N : ℤ)) + a 0 / (N : ℤ) + a 1 / (N : ℤ) + 1) *
        cexp (-(π * I * ((a 0 / (N : ℤ) : ℤ) * ((r 1 : ℤ) : ℂ) -
          (a 1 / (N : ℤ) : ℤ) * ((r 0 : ℤ) : ℂ)) / N)) *
        cexp (π * I * ((r 1 : ℤ) : ℂ) * (((r 0 : ℤ) : ℂ) - N) / (N : ℂ) ^ 2)) ^ (12 * k) =
        cexp (2 * π * I / N) ^ ((m : ℤ) * r 1 * (r 0 - N)) := by
    rw [hexp_12k, pow_mul, neg_one_zpow_mul_exp_mul_exp_pow_two_mul,
      ← zpow_natCast _ m, ← _root_.zpow_mul]
    congr 1
    dsimp only [r]
    ring
  have hqpow : cexp (π * I * bernoulliFun 2 ((r 0 : ℝ) / N) * τ) ^ (12 * k) =
      𝕢 N τ ^ ((m : ℤ) * r 0 ^ 2 - 6 * k * r 0 + k * N) := by
    rw [← Complex.exp_nat_mul, bernoulliFun_two, Function.Periodic.qParam, ← Complex.exp_int_mul]
    congr 1
    push_cast
    field_simp
    linear_combination -12 * (r 0 : ℂ) ^ 2 * τ * hmul_div'
  rw [hphase, hqpow]

/-- The cusp function of `g_{a/N}^{12 k}` at period `N` is meromorphic at `0` whenever
`N ∣ 6 * k`. -/
theorem meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul (a : Fin 2 → ℤ)
    {k : ℕ} (hk : N ∣ 6 * k) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k)) 0 := by
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k)) =
      fun τ : ℍ ↦
        (cexp (2 * π * I / N) ^
            (((6 * k / N : ℕ) : ℤ) * (a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N)) *
          𝕢 N τ ^ (((6 * k / N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 -
            6 * k * (a 0 % (N : ℤ)) + k * N)) *
          siegelThetaDisc N a (𝕢 N τ) ^ (12 * k) := by
    funext τ
    exact siegelFunction_div_pow_twelve_mul_eq a hk τ
  rw [hfun]
  refine UpperHalfPlane.meromorphicAt_cuspFunction_mul ?_
    (UpperHalfPlane.meromorphicAt_cuspFunction_pow
      (analyticAt_cuspFunction_siegelThetaDisc a).meromorphicAt _)
  exact UpperHalfPlane.meromorphicAt_cuspFunction_mul
    (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
    (UpperHalfPlane.meromorphicAt_cuspFunction_qParam_zpow N _)

/-- Exact `q_N`-Laurent expansion of `g_{a/N}^{12 k}` at period `N` whenever `N ∣ 6 * k`. -/
theorem laurentQExpansion_siegelFunction_div_pow_twelve_mul (a : Fin 2 → ℤ)
    {k : ℕ} (hk : N ∣ 6 * k) :
    UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k)) =
      HahnSeries.single
          (((6 * k / N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 - 6 * k * (a 0 % (N : ℤ)) + k * N)
          (cexp (2 * π * I / N) ^
            (((6 * k / N : ℕ) : ℤ) * (a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N))) *
        ((qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)) : LaurentSeries ℂ) ^
          (12 * k)) := by
  set c : ℂ := cexp (2 * π * I / N) ^
    (((6 * k / N : ℕ) : ℤ) * (a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N))
  set e : ℤ := ((6 * k / N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 - 6 * k * (a 0 % (N : ℤ)) + k * N
  have hfun : (fun τ : ℍ ↦ siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k)) =
      (fun τ : ℍ ↦ c * 𝕢 N τ ^ e) *
        (fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)) ^ (12 * k) := by
    funext τ
    exact siegelFunction_div_pow_twelve_mul_eq a hk τ
  have hm_ce : MeromorphicAt (cuspFunction N fun τ : ℍ ↦ c * 𝕢 N τ ^ e) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_mul
      (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (UpperHalfPlane.meromorphicAt_cuspFunction_qParam_zpow N e)
  have hm_θ : MeromorphicAt (cuspFunction N fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)) 0 :=
    (analyticAt_cuspFunction_siegelThetaDisc a).meromorphicAt
  have hm_θp :
      MeromorphicAt (cuspFunction N ((fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)) ^ (12 * k))) 0 :=
    UpperHalfPlane.meromorphicAt_cuspFunction_pow hm_θ _
  have hce_eq : (fun τ : ℍ ↦ c * 𝕢 N τ ^ e) = (fun _ : ℍ ↦ c) * (fun τ : ℍ ↦ 𝕢 N τ ^ e) := rfl
  rw [hfun, UpperHalfPlane.laurentQExpansion_mul hm_ce hm_θp, hce_eq,
    UpperHalfPlane.laurentQExpansion_mul (UpperHalfPlane.meromorphicAt_cuspFunction_const _)
      (UpperHalfPlane.meromorphicAt_cuspFunction_qParam_zpow N e),
    UpperHalfPlane.laurentQExpansion_const,
    UpperHalfPlane.laurentQExpansion_qParam_zpow (Nat.cast_pos.mpr (NeZero.pos N)) e,
    UpperHalfPlane.laurentQExpansion_pow hm_θ,
    UpperHalfPlane.laurentQExpansion_of_analyticAt (analyticAt_cuspFunction_siegelThetaDisc a)]
  congr 1
  rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]

/-- When `a / N ∉ ℤ²` and `N ∣ 6 * k`, the `q_N`-order of `g_{a/N}^{12 k}` is
`((6 * k / N : ℕ) : ℤ) * (a 0 % N)^2 - 6 * k * (a 0 % N) + k * N`. -/
theorem orderTop_laurentQExpansion_siegelFunction_div_pow_twelve_mul {a : Fin 2 → ℤ}
    (ha : ¬ ∀ i, (N : ℤ) ∣ a i) {k : ℕ} (hk : N ∣ 6 * k) :
    (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k)).orderTop =
      ((((6 * k / N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 - 6 * k * (a 0 % (N : ℤ)) +
        k * N : ℤ) : WithTop ℤ) := by
  set P : PowerSeries ℂ := qExpansion N fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)
  have hP0 : P.coeff 0 ≠ 0 := by
    rw [qExpansion_siegelThetaDisc_coeff_zero]
    exact siegelThetaDisc_zero_ne_zero a ha
  have hP_ord : P.order = 0 :=
    PowerSeries.order_zero_of_isUnit
      (PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr (by simpa using hP0)))
  have hP_ordTop : (P : LaurentSeries ℂ).orderTop = 0 := by
    rw [PowerSeries.orderTop_coe, hP_ord]
    rfl
  have hpow_ordTop (m : ℕ) : ((P : LaurentSeries ℂ) ^ m).orderTop = 0 := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, HahnSeries.orderTop_mul, ih, hP_ordTop, add_zero]
  rw [laurentQExpansion_siegelFunction_div_pow_twelve_mul a hk, HahnSeries.orderTop_mul,
    HahnSeries.orderTop_single (zpow_ne_zero _ (Complex.exp_ne_zero _)), hpow_ordTop, add_zero]

/-- When `a / N ∉ ℤ²` and `N ∣ 6 * k`, the meromorphic order at `0` of the cusp function of
`g_{a/N}^{12 k}` is `((6 * k / N : ℕ) : ℤ) * (a 0 % N)^2 - 6 * k * (a 0 % N) + k * N`. -/
theorem meromorphicOrderAt_cuspFunction_siegelFunction_div_pow_twelve_mul {a : Fin 2 → ℤ}
    (ha : ¬ ∀ i, (N : ℤ) ∣ a i) {k : ℕ} (hk : N ∣ 6 * k) :
    meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k)) 0 =
      ((((6 * k / N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 - 6 * k * (a 0 % (N : ℤ)) +
        k * N : ℤ) : WithTop ℤ) := by
  rw [← UpperHalfPlane.orderTop_laurentQExpansion
    (meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul a hk)]
  exact orderTop_laurentQExpansion_siegelFunction_div_pow_twelve_mul ha hk

/-- Every `q_N`-Laurent coefficient of `g_{a/N}^{12 k}` (whenever `N ∣ 6 * k`) lies in any
subring `S` of `ℂ` containing `e^{2π i / N}` (in particular `ℤ[ζ_N]` and the ring of all
algebraic integers). -/
theorem laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem (S : Subring ℂ)
    (hζ : cexp (2 * π * I / N) ∈ S) (a : Fin 2 → ℤ) {k : ℕ} (hk : N ∣ 6 * k) (n : ℤ) :
    (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * k)).coeff n ∈ S := by
  have hc : cexp (2 * π * I / N) ^
      (((6 * k / N : ℕ) : ℤ) * (a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N)) ∈ S :=
    S.zpow_mem_of_pow_eq_one hζ (NeZero.ne N)
      (Complex.isPrimitiveRoot_exp N (NeZero.ne N)).pow_eq_one _
  obtain ⟨Q, hQ⟩ := (PowerSeries.mem_map_range S.subtype).mpr
    (fun m ↦ by simpa using qExpansion_siegelThetaDisc_coeff_mem a S hζ m)
  rw [laurentQExpansion_siegelFunction_div_pow_twelve_mul a hk, ← hQ,
    ← PowerSeries.coe_pow, ← map_pow (PowerSeries.map S.subtype), HahnSeries.coeff_single_mul,
    PowerSeries.coeff_coe]
  split_ifs
  · rw [mul_zero]
    exact S.zero_mem
  · rw [PowerSeries.coeff_map]
    exact S.mul_mem hc (((Q ^ (12 * k)).coeff _).2)

private theorem six_mul_div_gcd_six (N : ℕ) : N ∣ 6 * (N / Nat.gcd 6 N) := by
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_left 6 N
  refine ⟨m, ?_⟩
  calc 6 * (N / Nat.gcd 6 N) = (Nat.gcd 6 N * m) * (N / Nat.gcd 6 N) :=
        congrArg (· * (N / Nat.gcd 6 N)) hm
    _ = (Nat.gcd 6 N * (N / Nat.gcd 6 N)) * m := by ring
    _ = N * m := by rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right 6 N)]

private theorem twelve_mul_div_gcd_six (N : ℕ) :
    12 * N / Nat.gcd 6 N = 12 * (N / Nat.gcd 6 N) :=
  Nat.mul_div_assoc 12 (Nat.gcd_dvd_right 6 N)

private theorem six_mul_div_gcd_six_div (N : ℕ) [NeZero N] :
    6 * (N / Nat.gcd 6 N) / N = 6 / Nat.gcd 6 N := by
  rw [← Nat.mul_div_assoc 6 (Nat.gcd_dvd_right 6 N),
    Nat.mul_comm 6 N, Nat.mul_div_assoc N (Nat.gcd_dvd_left 6 N),
    Nat.mul_div_right _ (NeZero.pos N)]

/-- Factorization of the level-`N` power `g_{a/N}^{12 N / gcd(6, N)}`. -/
theorem siegelFunction_div_pow_eq (a : Fin 2 → ℤ) (τ : ℍ) :
    siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N) =
      cexp (2 * π * I / N) ^
          (((6 / Nat.gcd 6 N : ℕ) : ℤ) * (a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N)) *
        𝕢 N τ ^ (((6 / Nat.gcd 6 N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 -
          6 * (N / Nat.gcd 6 N : ℕ) * (a 0 % (N : ℤ)) + (N / Nat.gcd 6 N : ℕ) * N) *
        siegelThetaDisc N a (𝕢 N τ) ^ (12 * N / Nat.gcd 6 N) := by
  simpa only [twelve_mul_div_gcd_six, six_mul_div_gcd_six_div] using
    siegelFunction_div_pow_twelve_mul_eq a (six_mul_div_gcd_six N) τ

/-- The cusp function of `g_{a/N}^{12 N / gcd(6, N)}` at period `N` is meromorphic at `0`. -/
theorem meromorphicAt_cuspFunction_siegelFunction_div_pow (a : Fin 2 → ℤ) :
    MeromorphicAt (cuspFunction N fun τ : ℍ ↦
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N)) 0 := by
  rw [twelve_mul_div_gcd_six]
  exact meromorphicAt_cuspFunction_siegelFunction_div_pow_twelve_mul a (six_mul_div_gcd_six N)

/-- Exact `q_N`-Laurent expansion of `g_{a/N}^{12 N / gcd(6, N)}` at period `N`. -/
theorem laurentQExpansion_siegelFunction_div_pow (a : Fin 2 → ℤ) :
    UpperHalfPlane.laurentQExpansion N (fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N)) =
      HahnSeries.single
          (((6 / Nat.gcd 6 N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 -
            6 * (N / Nat.gcd 6 N : ℕ) * (a 0 % (N : ℤ)) + (N / Nat.gcd 6 N : ℕ) * N)
          (cexp (2 * π * I / N) ^
            (((6 / Nat.gcd 6 N : ℕ) : ℤ) * (a 1 % (N : ℤ)) * (a 0 % (N : ℤ) - N))) *
        ((qExpansion N (fun τ : ℍ ↦ siegelThetaDisc N a (𝕢 N τ)) : LaurentSeries ℂ) ^
          (12 * N / Nat.gcd 6 N)) := by
  simpa only [twelve_mul_div_gcd_six, six_mul_div_gcd_six_div] using
    laurentQExpansion_siegelFunction_div_pow_twelve_mul a (six_mul_div_gcd_six N)

/-- When `a / N ∉ ℤ²`, the `q_N`-order of `g_{a/N}^{12 N / gcd(6, N)}` is
`((6 / gcd(6, N) : ℕ) : ℤ) * (a 0 % N)^2 - 6 * (N / gcd(6, N)) * (a 0 % N) + (N / gcd(6, N)) * N`.
-/
theorem orderTop_laurentQExpansion_siegelFunction_div_pow {a : Fin 2 → ℤ}
    (ha : ¬ ∀ i, (N : ℤ) ∣ a i) :
    (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N)).orderTop =
      ((((6 / Nat.gcd 6 N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 -
        6 * (N / Nat.gcd 6 N : ℕ) * (a 0 % (N : ℤ)) + (N / Nat.gcd 6 N : ℕ) * N : ℤ) :
          WithTop ℤ) := by
  simpa only [twelve_mul_div_gcd_six, six_mul_div_gcd_six_div] using
    orderTop_laurentQExpansion_siegelFunction_div_pow_twelve_mul ha (six_mul_div_gcd_six N)

/-- When `a / N ∉ ℤ²`, the meromorphic order at `0` of the cusp function of
`g_{a/N}^{12 N / gcd(6, N)}` is
`((6 / gcd(6, N) : ℕ) : ℤ) * (a 0 % N)^2 - 6 * (N / gcd(6, N)) * (a 0 % N) + (N / gcd(6, N)) * N`.
-/
theorem meromorphicOrderAt_cuspFunction_siegelFunction_div_pow {a : Fin 2 → ℤ}
    (ha : ¬ ∀ i, (N : ℤ) ∣ a i) :
    meromorphicOrderAt (cuspFunction N fun τ : ℍ ↦
        siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N)) 0 =
      ((((6 / Nat.gcd 6 N : ℕ) : ℤ) * (a 0 % (N : ℤ)) ^ 2 -
        6 * (N / Nat.gcd 6 N : ℕ) * (a 0 % (N : ℤ)) + (N / Nat.gcd 6 N : ℕ) * N : ℤ) :
          WithTop ℤ) := by
  rw [← UpperHalfPlane.orderTop_laurentQExpansion
    (meromorphicAt_cuspFunction_siegelFunction_div_pow a)]
  exact orderTop_laurentQExpansion_siegelFunction_div_pow ha

/-- Every `q_N`-Laurent coefficient of `g_{a/N}^{12 N / gcd(6, N)}` lies in any subring `S` of
`ℂ` containing `e^{2π i / N}` (in particular `ℤ[ζ_N]` and the ring of all algebraic integers). -/
theorem laurentQExpansion_siegelFunction_div_pow_coeff_mem (S : Subring ℂ)
    (hζ : cexp (2 * π * I / N) ∈ S) (a : Fin 2 → ℤ) (n : ℤ) :
    (UpperHalfPlane.laurentQExpansion N fun τ : ℍ ↦
      siegelFunction (fun i ↦ (a i : ℝ) / N) τ ^ (12 * N / Nat.gcd 6 N)).coeff n ∈ S := by
  rw [twelve_mul_div_gcd_six]
  exact laurentQExpansion_siegelFunction_div_pow_twelve_mul_coeff_mem S hζ a
    (six_mul_div_gcd_six N) n

end Power

end TauCeti.ModularForm
