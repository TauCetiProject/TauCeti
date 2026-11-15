/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
public import TauCeti.Analysis.Asymptotics.OrderSymbolExamples
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Poincaré expansions (DLMF 2.1.13–2.1.17)

A Poincaré expansion is an asymptotic expansion in one of three standard scales:
* at infinity in a set `X` of a normed field, `z ↦ (zⁿ)⁻¹` along `cobounded 𝕜 ⊓ 𝓟 X`;
* at `+∞` on `ℝ`, `x ↦ (xⁿ)⁻¹` along `atTop`;
* at a finite point `c`, `z ↦ (z - c)ⁿ` along the punctured filter `𝓝[X \ {c}] c` (DLMF 2.1.16).

Each is an asymptotic scale. Uniqueness of the coefficients holds at infinity when `X` is
unbounded and at `c` when `c` is an accumulation point of `X`. Both are instances of
`Asymptotics.HasAsymptoticExpansion.unique`. The unpunctured filter `𝓝[X] c` would not do: for
`X = {c}` every `(z - c)ⁿ` with `n ≥ 1` vanishes on it.

At infinity the expansion is characterized by the limits
`zⁿ (f z - ∑_{s<n} a_s z⁻ˢ) → a_n` (DLMF 2.1.15). A convergent series in `z⁻¹` is the expansion of
its sum. In a closed sector `|ph z| ≤ π/2 - δ` the functions `0`, `e^{-z}` and `e^{-√z}` all have
the zero expansion (DLMF 2.1.17), so an expansion does not determine its function.

## Main results

* `Asymptotics.isAsymptoticScale_inv_pow_cobounded`, `Asymptotics.isAsymptoticScale_inv_pow_atTop`,
  `Asymptotics.isAsymptoticScale_sub_pow`: the three scales.
* `Asymptotics.HasAsymptoticExpansion.unique_inv_pow`,
  `Asymptotics.HasAsymptoticExpansion.unique_sub_pow`: uniqueness.
* `Asymptotics.hasAsymptoticExpansion_inv_pow_iff`: the characterization 2.1.15.
* `Asymptotics.hasAsymptoticExpansion_of_hasSum`: convergent series.
* `Asymptotics.hasAsymptoticExpansion_zero_sector`, `Asymptotics.hasAsymptoticExpansion_exp_neg`,
  `Asymptotics.hasAsymptoticExpansion_exp_neg_sqrt`: the zero expansions of 2.1.17.
-/

@[expose] public section

open Filter Finset Bornology
open scoped Topology Real

namespace Asymptotics

section Scales

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

private lemma tendsto_inv_cobounded_inf_principal (X : Set 𝕜) :
    Tendsto (fun z : 𝕜 => z⁻¹) (cobounded 𝕜 ⊓ 𝓟 X) (𝓝 0) :=
  tendsto_inv₀_cobounded.mono_left inf_le_left

private lemma eventually_ne_zero_cobounded_inf_principal (X : Set 𝕜) :
    ∀ᶠ z in cobounded 𝕜 ⊓ 𝓟 X, z ≠ 0 :=
  (eventually_ne_cobounded (0 : 𝕜)).filter_mono inf_le_left

/-- The scale `z ↦ (zⁿ)⁻¹` at infinity in `X`. -/
theorem isAsymptoticScale_inv_pow_cobounded (X : Set 𝕜) :
    IsAsymptoticScale (cobounded 𝕜 ⊓ 𝓟 X) (fun (n : ℕ) (z : 𝕜) => (z ^ n)⁻¹) := by
  simpa only [inv_pow] using isAsymptoticScale_pow (tendsto_inv_cobounded_inf_principal X)

/-- The scale `x ↦ (xⁿ)⁻¹` at `+∞` on `ℝ`. -/
theorem isAsymptoticScale_inv_pow_atTop :
    IsAsymptoticScale atTop (fun n (x : ℝ) => (x ^ n)⁻¹) := by
  simpa only [inv_pow] using isAsymptoticScale_pow tendsto_inv_atTop_zero

/-- The scale `z ↦ (z - c)ⁿ` at `c` along the punctured filter `𝓝[X \ {c}] c` (DLMF 2.1.16). -/
theorem isAsymptoticScale_sub_pow (X : Set 𝕜) (c : 𝕜) :
    IsAsymptoticScale (𝓝[X \ {c}] c) (fun (n : ℕ) (z : 𝕜) => (z - c) ^ n) :=
  isAsymptoticScale_pow (tendsto_sub_nhds_zero_iff.mpr (tendsto_id.mono_left nhdsWithin_le_nhds))

/-- Uniqueness of the coefficients of an expansion at infinity in an unbounded set `X`. -/
theorem HasAsymptoticExpansion.unique_inv_pow {X : Set 𝕜} {a b : ℕ → E} {f : 𝕜 → E}
    (hX : (cobounded 𝕜 ⊓ 𝓟 X).NeBot)
    (ha : HasAsymptoticExpansion (cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) a f)
    (hb : HasAsymptoticExpansion (cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) b f) : a = b :=
  ha.unique (isAsymptoticScale_inv_pow_cobounded X)
    (fun n => ((eventually_ne_zero_cobounded_inf_principal X).mono fun _ hz =>
      inv_ne_zero (pow_ne_zero n hz)).frequently) hb

/-- Uniqueness of the coefficients of an expansion at an accumulation point `c` of `X`. -/
theorem HasAsymptoticExpansion.unique_sub_pow {X : Set 𝕜} {c : 𝕜} {a b : ℕ → E} {f : 𝕜 → E}
    (hX : (𝓝[X \ {c}] c).NeBot)
    (ha : HasAsymptoticExpansion (𝓝[X \ {c}] c) (fun n z => (z - c) ^ n) a f)
    (hb : HasAsymptoticExpansion (𝓝[X \ {c}] c) (fun n z => (z - c) ^ n) b f) : a = b :=
  ha.unique (isAsymptoticScale_sub_pow X c)
    (fun n => (Eventually.frequently (by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact pow_ne_zero n (sub_ne_zero.mpr hz.2)))) hb

/-- **DLMF 2.1.15.** At infinity in `X`, `f` has the expansion `∑ a_s z⁻ˢ` if and only if
`zⁿ (f z - ∑_{s<n} a_s z⁻ˢ) → a_n` for every `n`. -/
theorem hasAsymptoticExpansion_inv_pow_iff (X : Set 𝕜) (a : ℕ → E) (f : 𝕜 → E) :
    HasAsymptoticExpansion (cobounded 𝕜 ⊓ 𝓟 X) (fun n z => (z ^ n)⁻¹) a f ↔
      ∀ n, Tendsto (fun z => z ^ n • (f z - ∑ s ∈ range n, (z ^ s)⁻¹ • a s))
        (cobounded 𝕜 ⊓ 𝓟 X) (𝓝 (a n)) := by
  set l := cobounded 𝕜 ⊓ 𝓟 X
  have hne := eventually_ne_zero_cobounded_inf_principal X
  set r : ℕ → 𝕜 → E := fun n z => f z - ∑ s ∈ range n, (z ^ s)⁻¹ • a s with hr
  have hrec : ∀ n z, r n z = (z ^ n)⁻¹ • a n + r (n + 1) z := fun n z => by
    simp only [hr, sum_range_succ]; abel
  constructor
  · intro h n
    have h1 : (fun z => z ^ n • r (n + 1) z) =O[l] fun z => z⁻¹ := by
      refine ((isBigO_refl (fun z : 𝕜 => z ^ n) l).smul (h (n + 1))).congr' EventuallyEq.rfl ?_
      filter_upwards [hne] with z hz
      rw [smul_eq_mul, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hz),
        one_mul]
    have h2 : Tendsto (fun z => z ^ n • r (n + 1) z) l (𝓝 0) :=
      h1.trans_tendsto (tendsto_inv_cobounded_inf_principal X)
    have h3 := h2.const_add (a n)
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [hne] with z hz
    change a n + z ^ n • r (n + 1) z = z ^ n • r n z
    rw [hrec n z, smul_add, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hz), one_smul]
  · intro h n
    refine ((isBigO_refl (fun z : 𝕜 => (z ^ n)⁻¹) l).smul ((h n).isBigO_one 𝕜)).congr' ?_ ?_
    · filter_upwards [hne] with z hz
      rw [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hz), one_smul]
    · exact Eventually.of_forall fun z => by simp

end Scales

/-- A series `∑ a_s z⁻ˢ` convergent for `‖z‖ > R` is the expansion of its sum at infinity. -/
theorem hasAsymptoticExpansion_of_hasSum {R : ℝ} {a : ℕ → ℂ} {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, R < ‖z‖ → HasSum (fun s => (z ^ s)⁻¹ * a s) (f z)) :
    HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) a f := by
  intro n
  set R' := max R 0 + 1
  have hR' : 0 < R' := by positivity
  have hsum : ∃ r > 0, ∀ z : ℂ, ‖z‖ < r → Summable fun s => a s * z ^ s := by
    refine ⟨R'⁻¹, inv_pos.mpr hR', fun z hz => ?_⟩
    rcases eq_or_ne z 0 with rfl | hz0
    · exact summable_of_ne_finset_zero (s := {0}) fun s hs => by
        simp only [Finset.mem_singleton] at hs; simp [zero_pow hs]
    · have hlt : R < ‖z⁻¹‖ := by
        rw [norm_inv]
        have : R' < ‖z‖⁻¹ := by
          rw [lt_inv_comm₀ hR' (norm_pos_iff.mpr hz0)]; exact hz
        linarith [le_max_left R 0]
      simpa [mul_comm] using (hf z⁻¹ hlt).summable
  have h8 := (Complex.tsum_tail_isBigO_pow hsum n).comp_tendsto
    (tendsto_inv₀_cobounded (α := ℂ))
  refine h8.congr' ?_ (Eventually.of_forall fun z => by simp)
  have hev : ∀ᶠ z in cobounded ℂ, R < ‖z‖ :=
    tendsto_norm_cobounded_atTop.eventually (eventually_gt_atTop R)
  filter_upwards [hev] with z hz
  have hs := hf z hz
  rw [← hs.tsum_eq, ← hs.summable.sum_add_tsum_nat_add n]
  simp [mul_comm, smul_eq_mul]

/-! ### The zero expansions of DLMF 2.1.17 -/

/-- The sector `|arg z| ≤ π/2 - δ` lies in `{z | sin δ · ‖z‖ ≤ re z}`. -/
private lemma sector_subset {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ π / 2) :
    {z : ℂ | |Complex.arg z| ≤ π / 2 - δ} ⊆ {z : ℂ | Real.sin δ * ‖z‖ ≤ z.re} := fun z hz => by
  have h := (TauCeti.arg_mem_Icc_iff_norm_mul_cos_le_re (z := z)
    ⟨by linarith, by linarith [Real.pi_pos]⟩).mp (abs_le.mp hz)
  rwa [Real.cos_pi_div_two_sub, mul_comm] at h

/-- `e^{-z}` has the zero expansion at infinity in `{z | κ ‖z‖ ≤ re z}` for `κ > 0`. -/
private lemma hasAsymptoticExpansion_exp_neg_re {κ : ℝ} (hκ : 0 < κ) :
    HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z : ℂ | κ * ‖z‖ ≤ z.re})
      (fun n z => (z ^ n)⁻¹) (fun _ => (0 : ℂ)) fun z => Complex.exp (-z) := by
  intro n
  simp only [smul_zero, sum_const_zero, sub_zero]
  set l := cobounded ℂ ⊓ 𝓟 {z : ℂ | κ * ‖z‖ ≤ z.re}
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) l atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have hlim : Tendsto (fun z : ℂ => (κ * ‖z‖) ^ n * Real.exp (-(κ * ‖z‖))) l (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp (hnorm.const_mul_atTop hκ)
  obtain ⟨C, hC⟩ : ∃ C, ∀ᶠ z in l, (κ * ‖z‖) ^ n * Real.exp (-(κ * ‖z‖)) ≤ C :=
    ⟨1, hlim.eventually (ge_mem_nhds one_pos)⟩
  refine IsBigO.of_bound (C / κ ^ n) ?_
  have hsec : ∀ᶠ z in l, κ * ‖z‖ ≤ z.re := eventually_inf_principal.mpr
    (Eventually.of_forall fun z hz => hz)
  have hne : ∀ᶠ z in l, z ≠ 0 := (eventually_ne_cobounded (0 : ℂ)).filter_mono inf_le_left
  filter_upwards [hC, hsec, hne] with z hz hzs hz0
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [Complex.norm_exp, Complex.neg_re, norm_inv, norm_pow]
  have h1 : Real.exp (-z.re) ≤ Real.exp (-(κ * ‖z‖)) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(κ * ‖z‖)) ≤ C / κ ^ n * (‖z‖ ^ n)⁻¹ := by
    rw [mul_pow] at hz
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    calc Real.exp (-(κ * ‖z‖)) * κ ^ n
        = κ ^ n * ‖z‖ ^ n * Real.exp (-(κ * ‖z‖)) * (‖z‖ ^ n)⁻¹ := by
          field_simp
      _ ≤ C * (‖z‖ ^ n)⁻¹ := by gcongr
  linarith

/-- **DLMF 2.1.17.** `0` has the zero expansion at infinity in `|ph z| ≤ π/2 - δ`. -/
theorem hasAsymptoticExpansion_zero_sector (δ : ℝ) :
    HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) (fun _ => (0 : ℂ)) fun _ => 0 :=
  fun n => by simpa using isBigO_zero _ _

/-- **DLMF 2.1.17.** `e^{-z}` has the zero expansion at infinity in `|ph z| ≤ π/2 - δ`, for
`δ > 0`. -/
theorem hasAsymptoticExpansion_exp_neg {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) (fun _ => (0 : ℂ)) fun z => Complex.exp (-z) := by
  rcases lt_or_ge (π / 2) δ with hlt | hle
  · have hempty : {z : ℂ | |Complex.arg z| ≤ π / 2 - δ} = ∅ :=
      Set.eq_empty_of_forall_notMem fun z (hz : |Complex.arg z| ≤ π / 2 - δ) => by
        linarith [abs_nonneg (Complex.arg z)]
    intro n; simp [hempty]
  have hκ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  exact fun n => (hasAsymptoticExpansion_exp_neg_re hκ n).mono
    (inf_le_inf_left _ (principal_mono.mpr (sector_subset hδ hle)))

/-- **DLMF 2.1.17.** `e^{-√z}`, with the principal square root, has the zero expansion at infinity
in `|ph z| ≤ π/2 - δ`, for `δ > 0`. -/
theorem hasAsymptoticExpansion_exp_neg_sqrt {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ})
      (fun n z => (z ^ n)⁻¹) (fun _ => (0 : ℂ)) fun z => Complex.exp (-z ^ (1 / 2 : ℂ)) := by
  rcases lt_or_ge (π / 2) δ with hlt | hle
  · have hempty : {z : ℂ | |Complex.arg z| ≤ π / 2 - δ} = ∅ :=
      Set.eq_empty_of_forall_notMem fun z (hz : |Complex.arg z| ≤ π / 2 - δ) => by
        linarith [abs_nonneg (Complex.arg z)]
    intro n; simp [hempty]
  set κ := Real.sin δ
  have hκ : 0 < κ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  intro n
  simp only [smul_zero, sum_const_zero, sub_zero]
  set l := cobounded ℂ ⊓ 𝓟 {z : ℂ | |Complex.arg z| ≤ π / 2 - δ}
  let g : ℂ → ℂ := fun z => z ^ (2⁻¹ : ℂ)
  have hg_norm (z : ℂ) : ‖g z‖ = Real.sqrt ‖z‖ := by
    change ‖z ^ (2⁻¹ : ℂ)‖ = Real.sqrt ‖z‖
    rw [show (2⁻¹ : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_cpow_real,
      Real.sqrt_eq_rpow]
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) l atTop :=
    tendsto_norm_cobounded_atTop.mono_left inf_le_left
  have hg : Tendsto g l (cobounded ℂ ⊓ 𝓟 {w : ℂ | (1 / 2 : ℝ) * ‖w‖ ≤ w.re}) := by
    refine tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩
    · exact tendsto_norm_atTop_iff_cobounded.mp ((Real.tendsto_sqrt_atTop.comp hnorm).congr
        (fun z => (hg_norm z).symm))
    · filter_upwards [eventually_inf_principal.mpr (Eventually.of_forall fun z hz =>
        sector_subset hδ hle hz)] with z hz
      have hre : 0 ≤ z.re := (mul_nonneg hκ.le (norm_nonneg z)).trans hz
      change (1 / 2 : ℝ) * ‖g z‖ ≤ (g z).re
      rw [hg_norm, show (g z).re = Real.sqrt ((‖z‖ + z.re) / 2) from Complex.cpow_inv_two_re z]
      have hs := Real.sqrt_le_sqrt (show ‖z‖ / 4 ≤ (‖z‖ + z.re) / 2 by nlinarith [norm_nonneg z])
      rw [Real.sqrt_div (norm_nonneg z),
        show Real.sqrt (4 : ℝ) = 2 by norm_num [Real.sqrt_eq_iff_eq_sq]] at hs
      linarith
  have h := hasAsymptoticExpansion_exp_neg_re (κ := 1 / 2) (by norm_num) (2 * n)
  simp only [smul_zero, sum_const_zero, sub_zero] at h
  have hc := h.comp_tendsto hg
  have hb : (fun z => ((g z) ^ (2 * n))⁻¹) =O[l] fun z => (z ^ n)⁻¹ := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_)
    have hs : ‖g z‖ ^ 2 = ‖z‖ := by rw [hg_norm, Real.sq_sqrt (norm_nonneg z)]
    simp only [one_mul, norm_pow, norm_inv]
    rw [pow_mul, hs]
  simpa only [Function.comp_def, g, one_div, l] using hc.trans hb

end Asymptotics
