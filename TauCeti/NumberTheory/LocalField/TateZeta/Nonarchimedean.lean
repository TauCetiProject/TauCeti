/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.QuasiCharacter
public import TauCeti.NumberTheory.LocalField.TateZeta.Basic
public import TauCeti.NumberTheory.LocalField.Units.Haar
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.SpecificLimits.Basic
import TauCeti.NumberTheory.LocalField.HaarCharacter
import TauCeti.NumberTheory.LocalField.Unramified.Character
import TauCeti.NumberTheory.LocalField.Units.Shell

/-!
# The local Tate zeta integral over a nonarchimedean local field

Let `K` be a nonarchimedean local field with residue field of cardinality `q`, normalized
valuation `v_K` and normalized absolute value `|x| = q ^ (-v_K(x))`, and let `ν` be a Haar measure
on `Kˣ`. For a quasi-character `ω : Kˣ → ℂˣ` of exponent `r` (so `‖ω(x)‖ = |x| ^ r`) and a
continuous compactly supported test function `f : K → ℂ`, this file studies Tate's local zeta
integral

`z(s, ω; f) = ∫_{Kˣ} f(x) ω(x) |x| ^ s dν(x)`

(`TauCeti.TateZeta.localZetaIntegral` with `a = |·|`).

The proofs cut `Kˣ` into the compact shells `{x | v_K(x) = n}`, `n ∈ ℤ`
(`TauCeti.valuationShell`). Each shell is a
translate `ϖ ^ n 𝒪[K]ˣ` of the units of the ring of integers, so it has the `ν`-mass of `𝒪[K]ˣ`;
on it `|x| ^ s = (q ^ (-s)) ^ n`; and a compactly supported `f` vanishes on the shells with
`n < -N` for some `N`. Hence the integral is the Laurent series
`z(s, ω; f) = ∑ₙ dₙ (q ^ (-s)) ^ n` with `dₙ = ∫_{v_K(x) = n} f ω dν`, `‖dₙ‖ ≤ C q ^ (-n r)`
and `dₙ = 0` for `n < -N`, which converges absolutely for `re s + r > 0`.

## Main results

* `TauCeti.TateZeta.integrable_mul_of_characterExponent_pos`: `x ↦ f(x) c(x)` is integrable on
  `Kˣ` for every quasi-character `c` of positive exponent.
* `TauCeti.TateZeta.localZetaIntegral_convergent`: the integrand of `z(s, ω; f)` is integrable
  for `re s + r > 0`; for unitary `ω` this is the half-plane `re s > 0`.
* `TauCeti.TateZeta.differentiableOn_localZetaIntegral`: `s ↦ z(s, ω; f)` is holomorphic on
  `re s + r > 0`.
* `TauCeti.TateZeta.localZetaIntegral_indicator_integer_of_unramified`: for `ω` unramified,
  `z(s, ω; 1_𝒪) = ν(𝒪[K]ˣ) (1 - ω(ϖ) q ^ (-s))⁻¹` on `re s + r > 0`, where `ϖ` is a uniformizer;
  with the normalized measure `TauCeti.unitsHaar K` (`ν(𝒪[K]ˣ) = 1`) this is the local
  `L`-factor `(1 - ω(ϖ) q ^ (-s))⁻¹`
  (`localZetaIntegral_unitsHaar_indicator_integer_of_unramified`), and for `ω = 1` it is
  `(1 - q ^ (-s))⁻¹` on `re s > 0` (`localZetaIntegral_unitsHaar_indicator_integer_one`).
* `TauCeti.TateZeta.localZetaIntegral_eq_zero_of_apply_ne_one`: `z(s, ω; f) = 0` when `f` is
  invariant under a unit `u ∈ 𝒪[K]ˣ` with `ω(u) ≠ 1`.
* `TauCeti.TateZeta.localZetaIntegral_eq_zero_of_ramified`: for `ω` ramified, that is
  `¬ 𝒪[K]ˣ ≤ ker ω`, `z(s, ω; f) = 0` for every `f` invariant under `𝒪[K]ˣ`, in particular
  for `f = 1_𝒪` (`localZetaIntegral_indicator_integer_of_ramified`).

## Implementation notes

The measure is any Haar measure on `Kˣ`, so the statements hold for Kudla's normalization
`TauCeti.unitsHaar K` (`𝒪[K]ˣ` of mass one) and for Tate's (`𝒪[K]ˣ` of mass `N𝔡^(-1/2)` at a
completion of a number field) alike; the unramified value records the mass of `𝒪[K]ˣ`. The
characteristic of `K` is arbitrary.

## References

* J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, in J. W. S. Cassels
  and A. Fröhlich, eds., *Algebraic Number Theory*, §2.4.
* S. S. Kudla, *Tate's thesis*, in J. Bernstein and S. Gelbart, eds., *An Introduction to the
  Langlands Program*, §3, (3.4)–(3.6).
* At the completions of a number field, absolute convergence and the unramified Euler factor
  are `finiteLocalIdelicZetaIntegral_integrable` and `finiteLocalEulerFactor_norm` in
  `RiemannMasullo/Ch03_IdelicZeta/Sec3b.lean` of the Riemann–Masullo formalization
  (https://github.com/mccorvie/riemann-masullo); this file proves them for every
  nonarchimedean local field and every Haar measure, by the shell decomposition above.
-/

public section
noncomputable section

open MeasureTheory Complex ValuativeRel
open scoped NNReal

namespace TauCeti.TateZeta

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-! ### Quasi-characters on valuation shells -/

/-- `ω_s(x) = (q ^ (-s)) ^ n` on the shell of valuation `n`. -/
private theorem normalizedAbsCpowCharacter_of_mem_valuationShell (s : ℂ) {n : ℤ} {x : Kˣ}
    (hx : x ∈ valuationShell K n) :
    (normalizedAbsCpowCharacter K s x : ℂ) = ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n := by
  rw [coe_normalizedAbsCpowCharacter_apply_eq_zpow, mem_valuationShell.1 hx]

/-- `‖c(x)‖ = (q ^ (-r)) ^ n` on the shell of valuation `n`, for `c` of exponent `r`. -/
private theorem norm_apply_of_mem_valuationShell (c : Kˣ →ₜ* ℂˣ) {n : ℤ} {x : Kˣ}
    (hx : x ∈ valuationShell K n) :
    ‖(c x : ℂ)‖ = ((Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K c)) ^ n := by
  have hq := natCard_residueField_pos (K := K) (R := ℝ)
  rw [norm_coe_apply_eq_rpow_characterExponent, normalizedAbsoluteValue_of_mem_valuationShell hx,
    ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le]
  congr 1
  push_cast
  ring

variable [MeasurableSpace K] [BorelSpace K]

/-! ### Absolute convergence -/

/-- **Absolute convergence on shells.** For a Haar measure `ν` on `Kˣ`, a continuous compactly
supported `f : K → ℂ` and a quasi-character `c` of positive exponent, `x ↦ f(x) c(x)` is
integrable on `Kˣ`. -/
theorem integrable_mul_of_characterExponent_pos (ν : Measure Kˣ) [ν.IsHaarMeasure] {f : K → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) {c : Kˣ →ₜ* ℂˣ}
    (hc : 0 < characterExponent K c) :
    Integrable (fun x : Kˣ ↦ f x * (c x : ℂ)) ν := by
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨N, hN⟩ := exists_forall_valuationShell_eq_zero_of_hasCompactSupport hfc
  have hq := one_lt_natCard_residueField (K := K) (R := ℝ)
  set ρ := (Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K c)
  have hρ₀ : 0 < ρ := Real.rpow_pos_of_pos (zero_lt_one.trans hq) _
  have hρ : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  let g : C(Kˣ, ℂ) := ⟨fun x ↦ f x * (c x : ℂ),
    (hf.comp Units.continuous_val).mul (Units.continuous_val.comp c.continuous)⟩
  let s (n : ℤ) : TopologicalSpace.Compacts Kˣ := ⟨valuationShell K n, isCompact_valuationShell n⟩
  have hite (n : ℤ) : 0 ≤ (if -N ≤ n then ρ ^ n else 0) := by split_ifs <;> positivity
  have hbound (n : ℤ) :
      ‖g.restrict (s n)‖ ≤ max B 0 * (if -N ≤ n then ρ ^ n else 0) := by
    refine (ContinuousMap.norm_le _ (by have := hite n; positivity)).2 fun ⟨x, hx⟩ ↦ ?_
    rw [ContinuousMap.restrict_apply, ContinuousMap.coe_mk]
    split_ifs with hn
    · rw [norm_mul, norm_apply_of_mem_valuationShell c hx]
      exact mul_le_mul_of_nonneg_right ((hB x).trans (le_max_left _ _)) (by positivity)
    · rw [hN n (by omega) x hx, zero_mul, norm_zero, mul_zero]
  refine integrable_of_summable_norm_restrict (f := g) (s := s) ?_ iUnion_valuationShell
  refine ((summable_ite_le_zpow (-N) hρ₀ hρ).mul_left
    (max B 0 * ν.real (valuationShell K 0))).of_nonneg_of_le (fun n ↦ by positivity) fun n ↦ ?_
  have hsn : ν.real (s n) = ν.real (valuationShell K 0) := by
    rw [TopologicalSpace.Compacts.coe_mk, measureReal_valuationShell,
      measureReal_valuationShell]
  rw [hsn]
  calc ‖g.restrict (s n)‖ * ν.real (valuationShell K 0)
      ≤ (max B 0 * if -N ≤ n then ρ ^ n else 0) * ν.real (valuationShell K 0) :=
        mul_le_mul_of_nonneg_right (hbound n) measureReal_nonneg
    _ = _ := by ring

/-- **Convergence of the local zeta integral.** For a Haar measure `ν` on `Kˣ`, a continuous
compactly supported `f : K → ℂ` and a quasi-character `ω` of exponent `r`, the integrand
`f(x) ω(x) |x| ^ s` of `z(s, ω; f)` is integrable on `Kˣ` for `re s + r > 0`. For unitary `ω` this
is the half-plane `re s > 0`. -/
theorem localZetaIntegral_convergent (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {s : ℂ}
    (hs : 0 < s.re + characterExponent K ω) :
    Integrable (fun x : Kˣ ↦
      f x * (ω x : ℂ) * ((normalizedAbsoluteValue K (x : K) : ℝ) : ℂ) ^ s) ν := by
  refine (integrable_mul_of_characterExponent_pos ν hf hfc
    (c := ω * normalizedAbsCpowCharacter K s) (by simpa [add_comm] using hs)).congr
    (Filter.Eventually.of_forall fun x ↦ ?_)
  simp [mul_assoc]

/-- The local zeta integral as the sum over the shells `v_K(x) = n` of
`(∫_{v_K(x) = n} f ω dν) (q ^ (-s)) ^ n`, in the half-plane of absolute convergence. -/
private theorem localZetaIntegral_eq_tsum (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {s : ℂ}
    (hs : 0 < s.re + characterExponent K ω) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f s =
      ∑' n : ℤ, (∫ x in valuationShell K n, f x * (ω x : ℂ) ∂ν) *
        ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n := by
  rw [localZetaIntegral_def, ← setIntegral_univ, ← iUnion_valuationShell,
    integral_iUnion measurableSet_valuationShell pairwise_disjoint_valuationShell
      (localZetaIntegral_convergent ν ω hf hfc hs).integrableOn]
  refine tsum_congr fun n ↦ ?_
  rw [← integral_mul_const]
  refine setIntegral_congr_fun (measurableSet_valuationShell n) fun x hx ↦ ?_
  rw [← normalizedAbsCpowCharacter_of_mem_valuationShell s hx,
    coe_normalizedAbsCpowCharacter_apply]

/-- The shell coefficient `∫_{v_K(x) = n} f ω dν` has norm at most `B (q ^ (-r)) ^ n ν(𝒪[K]ˣ)`,
and vanishes below the support of `f`. -/
private theorem norm_setIntegral_shell_le (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) {N : ℤ}
    (hN : ∀ n < -N, ∀ x ∈ valuationShell K n, f x = 0) (n : ℤ) :
    ‖∫ x in valuationShell K n, f x * (ω x : ℂ) ∂ν‖ ≤
      max B 0 * ν.real (valuationShell K 0) *
        (if -N ≤ n then ((Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K ω)) ^ n else 0) := by
  have hfin : ν (valuationShell K n) < ⊤ := (isCompact_valuationShell n).measure_lt_top
  have hsn : ν.real (valuationShell K n) = ν.real (valuationShell K 0) := by
    rw [measureReal_valuationShell, measureReal_valuationShell]
  split_ifs with hn
  · refine (norm_setIntegral_le_of_norm_le_const (C := max B 0 *
      ((Nat.card 𝓀[K] : ℝ) ^ (-characterExponent K ω)) ^ n) hfin fun x hx ↦ ?_).trans_eq
      (by rw [hsn]; ring)
    rw [norm_mul, norm_apply_of_mem_valuationShell ω hx]
    exact mul_le_mul_of_nonneg_right ((hB x).trans (le_max_left _ _)) (by positivity)
  · rw [mul_zero, norm_le_zero_iff]
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
    rw [hN n (by omega) x hx, zero_mul]

/-- On a vertical strip `a < re s < b` with `a + r > 0`, the shell series of `z(s, ω; f)` is
dominated termwise by a summable sequence, so `s ↦ z(s, ω; f)` is holomorphic there. -/
private theorem differentiableOn_localZetaIntegral_strip (ν : Measure Kˣ) [ν.IsHaarMeasure]
    (ω : Kˣ →ₜ* ℂˣ) {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {a b : ℝ}
    (ha : 0 < a + characterExponent K ω) (hab : a < b) :
    DifferentiableOn ℂ (localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f)
      {s | a < s.re ∧ s.re < b} := by
  set r := characterExponent K ω
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfc
  obtain ⟨N, hN⟩ := exists_forall_valuationShell_eq_zero_of_hasCompactSupport hfc
  have hq := one_lt_natCard_residueField (K := K) (R := ℝ)
  have hq₀ : (0 : ℝ) < Nat.card 𝓀[K] := zero_lt_one.trans hq
  have hU : IsOpen {s : ℂ | a < s.re ∧ s.re < b} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  set ρa := (Nat.card 𝓀[K] : ℝ) ^ (-(r + a))
  set ρb := (Nat.card 𝓀[K] : ℝ) ^ (-(r + b))
  set C := max B 0 * ν.real (valuationShell K 0)
  have hterm (n : ℤ) (s : ℂ) (hs : a < s.re ∧ s.re < b) :
      ‖(∫ x in valuationShell K n, f x * (ω x : ℂ) ∂ν) * ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n‖ ≤
        C * ((if -N ≤ n then ρa ^ n else 0) + (if -N ≤ n then ρb ^ n else 0)) := by
    have hw : ‖((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n‖ = ((Nat.card 𝓀[K] : ℝ) ^ (-s.re)) ^ n := by
      rw [norm_zpow, ← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hq₀, neg_re]
    rw [norm_mul, hw]
    refine (mul_le_mul_of_nonneg_right (norm_setIntegral_shell_le ν ω hB hN n)
      (by positivity)).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    split_ifs
    · rw [← mul_zpow, ← Real.rpow_add hq₀, ← neg_add]
      exact (zpow_le_add_zpow_of_le_of_le (Real.rpow_pos_of_pos hq₀ _)
        (Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hs.2]))
        (Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hs.1])) n).trans_eq (add_comm _ _)
    · simp
  have hsum : Summable fun n : ℤ ↦
      C * ((if -N ≤ n then ρa ^ n else 0) + (if -N ≤ n then ρb ^ n else 0)) :=
    ((summable_ite_le_zpow (-N) (Real.rpow_pos_of_pos hq₀ _)
      (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith))).add
      (summable_ite_le_zpow (-N) (Real.rpow_pos_of_pos hq₀ _)
        (Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)))).mul_left C
  have hd : DifferentiableOn ℂ (fun s : ℂ ↦ ∑' n : ℤ,
      (∫ x in valuationShell K n, f x * (ω x : ℂ) ∂ν) * ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n)
      {s | a < s.re ∧ s.re < b} := by
    refine differentiableOn_tsum_of_summable_norm hsum (fun n ↦ ?_) hU hterm
    refine (DifferentiableOn.zpow ?_ (Or.inl fun s _ ↦ ?_)).const_mul _
    · exact (differentiable_neg.const_cpow (Or.inl (by exact_mod_cast hq₀.ne'))).differentiableOn
    · exact cpow_ne_zero_iff.2 (Or.inl (by exact_mod_cast hq₀.ne'))
  exact hd.congr fun s hs ↦ localZetaIntegral_eq_tsum ν ω hf hfc (by linarith [hs.1])

/-- **Holomorphy of the local zeta integral.** For a Haar measure `ν` on `Kˣ`, a continuous
compactly supported `f : K → ℂ` and a quasi-character `ω` of exponent `r`, the function
`s ↦ z(s, ω; f)` is holomorphic on the half-plane `re s + r > 0`. -/
theorem differentiableOn_localZetaIntegral (ν : Measure Kˣ) [ν.IsHaarMeasure] (ω : Kˣ →ₜ* ℂˣ)
    {f : K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    DifferentiableOn ℂ (localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f)
      {s | 0 < s.re + characterExponent K ω} := by
  intro s₀ (hs₀ : 0 < s₀.re + characterExponent K ω)
  -- Use the strip `(re s₀ - r) / 2 < re s < re s₀ + 1` around `s₀`.
  have hU : IsOpen {s : ℂ | (s₀.re - characterExponent K ω) / 2 < s.re ∧ s.re < s₀.re + 1} :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
  refine ((differentiableOn_localZetaIntegral_strip ν ω hf hfc (by linarith)
    (by linarith)).differentiableAt
    (hU.mem_nhds ⟨by linarith, by linarith⟩)).differentiableWithinAt

/-! ### Explicit values -/

/-- **The unramified local factor.** For an unramified quasi-character `ω` of exponent `r`, a
uniformizer `ϖ` and `re s + r > 0`,
`z(s, ω; 1_𝒪) = ν(𝒪[K]ˣ) (1 - ω(ϖ) q ^ (-s))⁻¹`. -/
theorem localZetaIntegral_indicator_integer_of_unramified (ν : Measure Kˣ) [ν.IsHaarMeasure]
    {ω : Kˣ →ₜ* ℂˣ} (hω : unitFiltration K 0 ≤ ω.ker) {ϖ : Kˣ}
    (hϖ : IsUniformizer K ϖ) {s : ℂ} (hs : 0 < s.re + characterExponent K ω) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω
        ((𝒪[K] : Set K).indicator 1) s =
      ν.real (unitFiltration K 0 : Set Kˣ) * (1 - ω ϖ * (Nat.card 𝓀[K] : ℂ) ^ (-s))⁻¹ := by
  have hq := one_lt_natCard_residueField (K := K) (R := ℝ)
  have hq₀ : (0 : ℝ) < Nat.card 𝓀[K] := zero_lt_one.trans hq
  have hϖ1 : ϖ ∈ valuationShell K 1 :=
    mem_valuationShell.2 (by rw [(isUniformizer_def ϖ).1 hϖ, toAdd_ofAdd])
  set c : ℂ := (ν.real (unitFiltration K 0 : Set Kˣ) : ℂ)
  set w := (ω ϖ : ℂ) * (Nat.card 𝓀[K] : ℂ) ^ (-s)
  have hw : ‖w‖ < 1 := by
    rw [norm_mul, norm_apply_of_mem_valuationShell ω hϖ1, zpow_one, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hq₀, neg_re, ← Real.rpow_add hq₀]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  have hd (n : ℤ) :
      (∫ x in valuationShell K n, (𝒪[K] : Set K).indicator 1 (x : K) * (ω x : ℂ) ∂ν) *
        ((Nat.card 𝓀[K] : ℂ) ^ (-s)) ^ n = if 0 ≤ n then c * w ^ n else 0 := by
    have hconst : ∀ x ∈ valuationShell K n, (𝒪[K] : Set K).indicator 1 (x : K) * (ω x : ℂ) =
        if 0 ≤ n then (ω ϖ : ℂ) ^ n else 0 := fun x hx ↦ by
      have hmem := (mem_integer_iff_toAdd_normalizedValuation_nonneg x).trans
        (by rw [mem_valuationShell.1 hx])
      -- An unramified character is the unramified character with value `ω(ϖ)` at `ϖ`.
      have hωx := apply_eq_unramifiedCharacter_of_isUniformizer (δ := ω.toMonoidHom)
        (fun u hu ↦ hω ((mem_unitFiltration_zero u).2 hu)) hϖ x
      rw [unramifiedCharacter_apply, mem_valuationShell.1 hx] at hωx
      by_cases hn : 0 ≤ n
      · simp only [hn, ↓reduceIte]
        rw [Set.indicator_of_mem (hmem.2 hn), Pi.one_apply, one_mul]
        exact (congrArg Units.val hωx).trans (Units.val_zpow_eq_zpow_val _ _)
      · simp only [hn, ↓reduceIte]
        rw [Set.indicator_of_notMem (mt hmem.1 hn), zero_mul]
    rw [setIntegral_congr_fun (measurableSet_valuationShell n) hconst, setIntegral_const,
      measureReal_valuationShell, Complex.real_smul]
    split_ifs
    · rw [mul_zpow]
      ring
    · rw [mul_zero, zero_mul]
  rw [localZetaIntegral_eq_tsum ν ω (continuous_indicator_integer K)
    (hasCompactSupport_indicator_integer K) hs]
  simp_rw [hd]
  refine HasSum.tsum_eq ?_
  set g : ℤ → ℂ := fun n ↦ if 0 ≤ n then c * w ^ n else 0
  have h₁ : HasSum (fun n : ℕ ↦ g n) (c * (1 - w)⁻¹) := by
    simpa [g] using (hasSum_geometric_of_norm_lt_one hw).mul_left c
  have h₂ : HasSum (fun n : ℕ ↦ g (-(n + 1))) 0 := by
    convert hasSum_zero with n
    exact ite_eq_right_iff.2 fun h ↦ absurd h (by omega)
  simpa using h₁.of_nat_of_neg_add_one h₂

/-- **The unramified local factor in Kudla's normalization.** With the Haar measure
`TauCeti.unitsHaar K` giving `𝒪[K]ˣ` mass one, an unramified quasi-character `ω` of exponent `r`
and `re s + r > 0`, `z(s, ω; 1_𝒪) = (1 - ω(ϖ) q ^ (-s))⁻¹`. For `ω = 1` this is
`(1 - q ^ (-s))⁻¹` on `re s > 0`. -/
theorem localZetaIntegral_unitsHaar_indicator_integer_of_unramified {ω : Kˣ →ₜ* ℂˣ}
    (hω : unitFiltration K 0 ≤ ω.ker) {ϖ : Kˣ} (hϖ : IsUniformizer K ϖ) {s : ℂ}
    (hs : 0 < s.re + characterExponent K ω) :
    localZetaIntegral (unitsHaar K) (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω
        ((𝒪[K] : Set K).indicator 1) s =
      (1 - ω ϖ * (Nat.card 𝓀[K] : ℂ) ^ (-s))⁻¹ := by
  rw [localZetaIntegral_indicator_integer_of_unramified _ hω hϖ hs, measureReal_def,
    unitsHaar_unitFiltration_zero, ENNReal.toReal_one, ofReal_one, one_mul]

/-- `z(s, 1; 1_𝒪) = (1 - q ^ (-s))⁻¹` on `re s > 0`, for the Haar measure giving `𝒪[K]ˣ`
mass one. At `s = 0` the integrand is not integrable, since its shell integrals are all `1`. -/
theorem localZetaIntegral_unitsHaar_indicator_integer_one {s : ℂ} (hs : 0 < s.re) :
    localZetaIntegral (unitsHaar K) (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) 1
        ((𝒪[K] : Set K).indicator 1) s =
      (1 - (Nat.card 𝓀[K] : ℂ) ^ (-s))⁻¹ := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  simpa using localZetaIntegral_unitsHaar_indicator_integer_of_unramified
    (ω := 1) (fun _ _ ↦ rfl) hϖ (s := s) (by simpa using hs)

/-- **Vanishing under a unit.** If `f` is invariant under multiplication by a unit `u ∈ 𝒪[K]ˣ`
with `ω(u) ≠ 1`, then `z(s, ω; f) = 0` for every `s`: the substitution `x ↦ u x` multiplies the
integral by `ω(u)⁻¹ ≠ 1`. -/
theorem localZetaIntegral_eq_zero_of_apply_ne_one (ν : Measure Kˣ) [ν.IsMulLeftInvariant]
    {ω : Kˣ →ₜ* ℂˣ} {u : Kˣ} (hu : u ∈ unitFiltration K 0) (hωu : ω u ≠ 1) {f : K → ℂ}
    (hf : ∀ x, f (u * x) = f x) (s : ℂ) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f s = 0 := by
  refine localZetaIntegral_eq_zero_of_comp_mul_left ν _ ω
    (fun x ↦ coe_normalizedAbsoluteValue_pos x) (fun x y ↦ by simp) hf ?_
  rw [normalizedAbsoluteValue_of_mem_unitFiltration_zero hu, NNRat.cast_one, ofReal_one, one_cpow,
    mul_one]
  exact fun h ↦ hωu (Units.ext h)

/-- **Ramified characters annihilate `𝒪[K]ˣ`-invariant test functions.** If `ω` is nontrivial
on `𝒪[K]ˣ`, then `z(s, ω; f) = 0` for every `s` and every `f` invariant under multiplication by
`𝒪[K]ˣ`. -/
theorem localZetaIntegral_eq_zero_of_ramified (ν : Measure Kˣ) [ν.IsMulLeftInvariant]
    {ω : Kˣ →ₜ* ℂˣ} (hω : ¬ unitFiltration K 0 ≤ ω.ker) {f : K → ℂ}
    (hf : ∀ v ∈ unitFiltration K 0, ∀ x, f (v * x) = f x) (s : ℂ) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω f s = 0 := by
  obtain ⟨u, hu, hωu⟩ := IsConcreteLE.not_le_iff_exists.1 hω
  exact localZetaIntegral_eq_zero_of_apply_ne_one ν hu hωu (hf u hu) s

/-- For `ω` nontrivial on `𝒪[K]ˣ`, `z(s, ω; 1_𝒪) = 0` for every `s`. -/
theorem localZetaIntegral_indicator_integer_of_ramified (ν : Measure Kˣ) [ν.IsMulLeftInvariant]
    {ω : Kˣ →ₜ* ℂˣ} (hω : ¬ unitFiltration K 0 ≤ ω.ker) (s : ℂ) :
    localZetaIntegral ν (fun x ↦ (normalizedAbsoluteValue K x : ℝ)) ω
      ((𝒪[K] : Set K).indicator 1) s = 0 := by
  refine localZetaIntegral_eq_zero_of_ramified ν hω (fun v hv x ↦ ?_) s
  simp only [Set.indicator, SetLike.mem_coe, mem_integer_iff_normalizedAbsoluteValue_le_one,
    map_mul, normalizedAbsoluteValue_of_mem_unitFiltration_zero hv, one_mul, Pi.one_apply]

end TauCeti.TateZeta
