/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import TauCeti.Analysis.Asymptotics.AsymptoticExpansion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecificLimits.RCLike
import TauCeti.Analysis.Complex.SectorBounds
import TauCeti.Analysis.SpecialFunctions.Exp.CpowQuarter
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# The Borel–Ritt theorem

Every sequence `a : ℕ → ℂ` is the Poincaré expansion `∑ aₛ z⁻ˢ` at infinity of a function that is
holomorphic in `{1 < |z|}` off the negative real axis (DLMF §2.1(iii)). The function is

`f z = a₀ + ∑_{s ≥ 1} aₛ z⁻ˢ (1 - exp(-bₛ z^{1/4}))`, with `bₛ = ((1 + |aₛ|) 2ˢ)⁻¹`,

where `z^{1/4}` is the principal fourth root. Its real part is at least `|z|^{1/4} / 2`, so each
factor `exp(-bₛ z^{1/4})` decays faster than every power of `z⁻¹`, while for `|z| ≥ 1` and
`s ≥ 1` the damped terms are bounded by `2^{1-s}`. The expansion holds along the full filter
`cobounded ℂ`; restricted to a closed sector `|ph z| ≤ θ` with `θ ≤ π`, and to the positive real
axis, it gives the existence theorems of DLMF §2.1(iii).

The expansion does not determine the function: `exp(-c z^{1/4})` with `c > 0` is nowhere zero
and has the zero expansion along `cobounded ℂ`, and adding it to a Borel–Ritt function gives a
second function with the same expansion.

## Main results

* `Asymptotics.hasAsymptoticExpansion_cexp_neg_mul_cpow_quarter`: `exp(-c z^{1/4})` has the
  zero expansion, from the decay estimates of `TauCeti.Analysis.SpecialFunctions.Exp.CpowQuarter`.
* `Asymptotics.exists_hasAsymptoticExpansion_cobounded`: Borel–Ritt along `cobounded ℂ`.
* `Asymptotics.exists_hasAsymptoticExpansion_sector`: Borel–Ritt in a closed sector.
* `Asymptotics.exists_ne_hasAsymptoticExpansion_sector`: two functions that differ everywhere
  have the same expansion in the sector.
* `Asymptotics.exists_hasAsymptoticExpansion_atTop`: Borel–Ritt on the positive real axis.

The construction is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
files `DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean` and
`DLMF/AsymptoticApproximations/Basics/Existence.lean`.
-/

public section

noncomputable section

open Complex Filter Finset Bornology
open scoped Topology Real

namespace Asymptotics

/-! ### A function with the zero expansion -/

/-- For `c > 0`, the nowhere vanishing function `exp(-c z^{1/4})` has the zero expansion in
inverse powers of `z` along `cobounded ℂ`. -/
theorem hasAsymptoticExpansion_cexp_neg_mul_cpow_quarter {c : ℝ} (hc : 0 < c) :
    HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) (0 : ℕ → ℂ)
      fun z => cexp (-(c * z ^ (1 / 4 : ℂ))) :=
  hasAsymptoticExpansion_zero_iff.2 (TauCeti.isBigO_cexp_neg_mul_cpow_quarter hc)

/-! ### The Borel–Ritt function -/

/-- The damping weights `bₛ = ((1 + |aₛ|) 2ˢ)⁻¹`. -/
private def borelRittWeight (a : ℕ → ℂ) (s : ℕ) : ℝ := ((1 + ‖a s‖) * 2 ^ s)⁻¹

/-- The damped terms `aₛ z⁻ˢ (1 - exp(-bₛ z^{1/4}))`. -/
private def borelRittTerm (a : ℕ → ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (z ^ s)⁻¹ * a s * (1 - cexp (-(borelRittWeight a s * z ^ (1 / 4 : ℂ))))

/-- The Borel–Ritt function: `a₀` plus the sum of the damped terms of index `s ≥ 1`. -/
private def borelRitt (a : ℕ → ℂ) (z : ℂ) : ℂ := a 0 + ∑' k, borelRittTerm a (k + 1) z

/-- The damping weights are positive. -/
private lemma borelRittWeight_pos (a : ℕ → ℂ) (s : ℕ) : 0 < borelRittWeight a s := by
  unfold borelRittWeight; positivity

/-- `bₛ |aₛ| ≤ 2⁻ˢ`. -/
private lemma borelRittWeight_mul_le (a : ℕ → ℂ) (s : ℕ) :
    borelRittWeight a s * ‖a s‖ ≤ (1 / 2) ^ s := by
  unfold borelRittWeight
  rw [one_div_pow, ← div_eq_inv_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [norm_nonneg (a s), pow_pos (two_pos (α := ℝ)) s]

/-- The bound `|a_{k+1} z^{-k-1} (1 - exp(-b_{k+1} z^{1/4}))| ≤ 2⁻ᵏ |z|^{1/4} |z|^{-k-1}`. -/
private lemma norm_borelRittTerm_le (a : ℕ → ℂ) (k : ℕ) (z : ℂ) :
    ‖borelRittTerm a (k + 1) z‖ ≤ (1 / 2) ^ k * (‖z‖ ^ (1 / 4 : ℝ) * (‖z‖ ^ (k + 1))⁻¹) := by
  set b := borelRittWeight a (k + 1)
  have hb := borelRittWeight_pos a (k + 1)
  set ζ : ℂ := b * z ^ (1 / 4 : ℂ)
  have hre : 0 ≤ ζ.re := by
    rw [re_ofReal_mul]
    nlinarith [TauCeti.norm_rpow_le_two_mul_re_cpow_quarter (z := z),
      Real.rpow_nonneg (norm_nonneg z) (1 / 4 : ℝ)]
  have hζ : ‖ζ‖ = b * ‖z‖ ^ (1 / 4 : ℝ) := by
    have hq : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le, hq, norm_cpow_real]
  have h1 : ‖1 - cexp (-ζ)‖ ≤ 2 * ‖ζ‖ := by
    by_cases h : ‖ζ‖ ≤ 1
    · rw [norm_sub_rev, ← norm_neg ζ]
      exact norm_exp_sub_one_le (by rwa [norm_neg])
    · refine (norm_sub_le _ _).trans ?_
      rw [norm_one, Complex.norm_exp, neg_re]
      linarith [Real.exp_le_one_iff.2 (neg_nonpos.2 hre)]
  have hw := borelRittWeight_mul_le a (k + 1)
  rw [borelRittTerm, norm_mul, norm_mul, norm_inv, norm_pow]
  calc (‖z‖ ^ (k + 1))⁻¹ * ‖a (k + 1)‖ * ‖1 - cexp (-ζ)‖
      ≤ (‖z‖ ^ (k + 1))⁻¹ * ‖a (k + 1)‖ * (2 * (b * ‖z‖ ^ (1 / 4 : ℝ))) := by
        rw [← hζ]; gcongr
    _ = 2 * (b * ‖a (k + 1)‖) * (‖z‖ ^ (1 / 4 : ℝ) * (‖z‖ ^ (k + 1))⁻¹) := by ring
    _ ≤ 2 * (1 / 2) ^ (k + 1) * (‖z‖ ^ (1 / 4 : ℝ) * (‖z‖ ^ (k + 1))⁻¹) := by gcongr
    _ = _ := by rw [pow_succ]; ring

/-- For `|z| ≥ 1` and `m ≤ k`, the damped term of index `k + 1` is at most `2⁻ᵏ |z|⁻ᵐ`. -/
private lemma norm_borelRittTerm_le_pow (a : ℕ → ℂ) {k m : ℕ} (hm : m ≤ k) {z : ℂ}
    (hz : 1 ≤ ‖z‖) : ‖borelRittTerm a (k + 1) z‖ ≤ (1 / 2) ^ k * (‖z‖ ^ m)⁻¹ := by
  refine (norm_borelRittTerm_le a k z).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hq : ‖z‖ ^ (1 / 4 : ℝ) ≤ ‖z‖ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hz (by norm_num : (1 / 4 : ℝ) ≤ 1)
  calc ‖z‖ ^ (1 / 4 : ℝ) * (‖z‖ ^ (k + 1))⁻¹ ≤ ‖z‖ * (‖z‖ ^ (k + 1))⁻¹ := by gcongr
    _ = (‖z‖ ^ k)⁻¹ := by rw [pow_succ]; field_simp
    _ ≤ (‖z‖ ^ m)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hz hm)

/-- The damped terms are summable for `|z| ≥ 1`. -/
private lemma summable_borelRittTerm (a : ℕ → ℂ) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    Summable fun k => borelRittTerm a (k + 1) z :=
  Summable.of_norm_bounded summable_geometric_two fun k => by
    simpa using norm_borelRittTerm_le_pow a (Nat.zero_le k) hz

/-- The Borel–Ritt function is holomorphic in `{1 < |z|}` off the negative real axis. -/
private lemma differentiableOn_borelRitt (a : ℕ → ℂ) :
    DifferentiableOn ℂ (borelRitt a) ({z | 1 < ‖z‖} ∩ slitPlane) := by
  have hU : IsOpen ({z : ℂ | 1 < ‖z‖} ∩ slitPlane) :=
    (isOpen_lt continuous_const continuous_norm).inter isOpen_slitPlane
  refine DifferentiableOn.const_add (a 0) ?_
  refine differentiableOn_tsum_of_summable_norm summable_geometric_two (fun k z hz => ?_) hU
    (fun k z hz => by simpa using norm_borelRittTerm_le_pow a (Nat.zero_le k) hz.1.out.le)
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz.2
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold borelRittTerm
  refine ((differentiableAt_id.pow _).inv (pow_ne_zero _ hz0)).mul_const _ |>.mul ?_
  exact (differentiableAt_const _).sub
    (((differentiableAt_id.cpow_const hz.2).const_mul _).neg.cexp)

/-- The tail `∑_{k ≥ M + 1}` of the damped terms of index `k + 1` is `O(z^{-M-1})`. -/
private lemma isBigO_tsum_borelRittTerm (a : ℕ → ℂ) (M : ℕ) :
    (fun z => ∑' k, borelRittTerm a (k + (M + 1) + 1) z) =O[cobounded ℂ]
      fun z => (z ^ (M + 1))⁻¹ := by
  refine IsBigO.of_bound 2 ?_
  filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop 1] with z hz
  rw [norm_inv, norm_pow]
  refine tsum_of_norm_bounded (hasSum_geometric_two.mul_right _) fun k => ?_
  refine (norm_borelRittTerm_le_pow a (by omega : M + 1 ≤ k + (M + 1)) hz).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
    (by positivity)

/-- The difference between a damped term and the undamped term `aₛ z⁻ˢ` is `O(z⁻ᴺ)` for every
`N`. -/
private lemma isBigO_borelRittTerm_sub (a : ℕ → ℂ) (s N : ℕ) :
    (fun z => borelRittTerm a (s + 1) z - (z ^ (s + 1))⁻¹ * a (s + 1)) =O[cobounded ℂ]
      fun z => (z ^ N)⁻¹ := by
  have hpow : (fun z : ℂ => (z ^ (s + 1))⁻¹) =O[cobounded ℂ] fun _ => (1 : ℂ) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_ge_atTop 1] with z hz
    rw [norm_inv, norm_pow, norm_one, one_mul]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hz)
  have h := ((hpow.mul (TauCeti.isBigO_cexp_neg_mul_cpow_quarter
    (borelRittWeight_pos a (s + 1)) N)).const_mul_left (-a (s + 1)))
  refine h.congr (fun z => ?_) (fun z => one_mul _)
  simp only [borelRittTerm]
  ring

/-- The Borel–Ritt function has the expansion `∑ aₛ z⁻ˢ` along `cobounded ℂ`. -/
private lemma hasAsymptoticExpansion_borelRitt (a : ℕ → ℂ) :
    HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) a (borelRitt a) := by
  have hev := (tendsto_norm_cobounded_atTop (E := ℂ)).eventually_ge_atTop 1
  refine HasAsymptoticExpansion.of_isBigO fun N => ?_
  rcases N with _ | M
  · refine IsBigO.of_bound (‖a 0‖ + 2) ?_
    filter_upwards [hev] with z hz
    simp only [range_zero, sum_empty, sub_zero, pow_zero, inv_one, norm_one, mul_one, borelRitt]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    exact tsum_of_norm_bounded hasSum_geometric_two fun k => by
      simpa using norm_borelRittTerm_le_pow a (Nat.zero_le k) hz
  · have hmain : (fun z : ℂ => (z ^ (M + 1))⁻¹ * a (M + 1)) =O[cobounded ℂ]
        fun z => (z ^ (M + 1))⁻¹ :=
      (isBigO_const_mul_self (a (M + 1)) _ _).congr_left fun _ => mul_comm _ _
    have h := ((IsBigO.fun_sum (s := range (M + 1)) fun k _ =>
      isBigO_borelRittTerm_sub a k (M + 1)).add hmain).add (isBigO_tsum_borelRittTerm a M)
    refine h.congr' ?_ EventuallyEq.rfl
    filter_upwards [hev] with z hz
    have hsplit := (summable_borelRittTerm a hz).sum_add_tsum_nat_add (M + 1)
    have e1 : ∑ n ∈ range (M + 1), (z ^ n)⁻¹ • a n =
        a 0 + ∑ k ∈ range M, (z ^ (k + 1))⁻¹ * a (k + 1) := by
      rw [sum_range_succ']
      simp only [smul_eq_mul, pow_zero, inv_one, one_mul]
      ring
    rw [borelRitt, e1, ← hsplit, sum_sub_distrib,
      sum_range_succ (fun k => (z ^ (k + 1))⁻¹ * a (k + 1))]
    ring

/-! ### Borel–Ritt existence -/

/-- **Borel–Ritt** along `cobounded ℂ`: every sequence `a` is the expansion `∑ aₛ z⁻ˢ` at
infinity of a function holomorphic in `{1 < |z|}` off the negative real axis. -/
theorem exists_hasAsymptoticExpansion_cobounded (a : ℕ → ℂ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({z | 1 < ‖z‖} ∩ slitPlane) ∧
      HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) a f :=
  ⟨borelRitt a, differentiableOn_borelRitt a, hasAsymptoticExpansion_borelRitt a⟩

/-- **Borel–Ritt** in a sector (DLMF §2.1(iii)): for `θ ≤ π`, every sequence `a` is the
expansion `∑ aₛ z⁻ˢ` along `cobounded ℂ ⊓ 𝓟 {|ph z| ≤ θ}` of a function holomorphic in
`{1 < |z|, |ph z| < θ}`. -/
theorem exists_hasAsymptoticExpansion_sector (a : ℕ → ℂ) {θ : ℝ} (hθπ : θ ≤ π) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧
      HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ})
        (fun n z => (z ^ n)⁻¹) a f := by
  obtain ⟨f, hfd, hf⟩ := exists_hasAsymptoticExpansion_cobounded a
  refine ⟨f, hfd.mono fun z hz => ⟨hz.1, ?_⟩, hf.mono inf_le_left⟩
  exact mem_slitPlane_of_abs_arg_lt (hz.2.trans_le hθπ) (norm_pos_iff.1 (by linarith [hz.1]))

/-- Non-uniqueness in Borel–Ritt (DLMF §2.1(iii), 2.1.17): for `θ ≤ π`, every sequence `a` is
the expansion in the sector of two holomorphic functions that differ at every point. -/
theorem exists_ne_hasAsymptoticExpansion_sector (a : ℕ → ℂ) {θ : ℝ} (hθπ : θ ≤ π) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧
      DifferentiableOn ℂ g {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧ (∀ z, f z ≠ g z) ∧
      HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ}) (fun n z => (z ^ n)⁻¹) a f ∧
      HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ}) (fun n z => (z ^ n)⁻¹) a g := by
  obtain ⟨f, hfd, hf⟩ := exists_hasAsymptoticExpansion_sector a hθπ
  have he := (hasAsymptoticExpansion_cexp_neg_mul_cpow_quarter one_pos).mono
    (inf_le_left : cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ} ≤ _)
  refine ⟨f, fun z => f z + cexp (-((1 : ℝ) * z ^ (1 / 4 : ℂ))), hfd,
    hfd.add (TauCeti.differentiableOn_cexp_neg_mul_cpow_quarter.mono fun z hz =>
      mem_slitPlane_of_abs_arg_lt (hz.2.trans_le hθπ) (norm_pos_iff.1 (by linarith [hz.1]))),
    fun z h => ?_, hf, (hf.add he).congr_coeff fun n => add_zero _⟩
  exact Complex.exp_ne_zero _ (by linear_combination -h)

/-- **Borel–Ritt** on the positive real axis (DLMF §2.1(iii)): every sequence `a` is the
expansion `∑ aₛ x⁻ˢ` of a function of `x` as `x → +∞`. -/
theorem exists_hasAsymptoticExpansion_atTop (a : ℕ → ℂ) :
    ∃ f : ℝ → ℂ, HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹) a f := by
  obtain ⟨f, -, hf⟩ := exists_hasAsymptoticExpansion_cobounded a
  have h := hf.comp_tendsto (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  refine ⟨fun x => f x, HasAsymptoticExpansion.of_isBigO fun N => ?_⟩
  refine ((h.isBigO N).trans (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_))).congr_left
    fun x => ?_
  · simp
  · simp [Complex.real_smul]

end Asymptotics
