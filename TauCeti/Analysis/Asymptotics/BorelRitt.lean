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
import TauCeti.Analysis.SpecialFunctions.Exp.Decay
import TauCeti.Analysis.SpecialFunctions.Exp.StretchedDecay
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# The Borel–Ritt theorem

Every sequence `a : ℕ → ℂ` is the Poincaré expansion `∑ aₛ z⁻ˢ` at infinity of a function that is
holomorphic in `{1 < |z|}` off the negative real axis (DLMF §2.1(iii)). The function is

`f z = a₀ + ∑_{s ≥ 1} aₛ z⁻ˢ (1 - exp(-bₛ z^{1/4}))`, with `bₛ = ((1 + |aₛ|) 2ˢ)⁻¹`,

where `z^{1/4}` is the principal fourth root. Its real part is nonnegative, so each factor
`exp(-bₛ z^{1/4})` decays faster than every power of `z⁻¹`, while for `|z| ≥ 1` and `s ≥ 1` the
damped terms are bounded by `2^{-s}`. The expansion holds along the full filter `cobounded ℂ`.
For `θ ≤ π`, the function is holomorphic in the open exterior sector `{1 < |z|, |ph z| < θ}` and
its expansion holds along the closed sector `|ph z| ≤ θ`; together with the positive real axis
this gives the existence theorems of DLMF §2.1(iii).

The expansion does not determine the function: for `c > 0` and `0 < α < 1/2`, `exp(-c z^α)` is
nowhere zero and has the zero expansion along `cobounded ℂ`, and adding `exp(-z^{1/4})` to a
Borel–Ritt function gives a second function with the same expansion.

## Main results

* `Asymptotics.hasAsymptoticExpansion_cexp_neg_mul_cpow`: `exp(-c z^α)` has the zero expansion,
  from the decay estimate `TauCeti.isLittleO_cexp_neg_mul_cpow_cobounded`.
* `Asymptotics.exists_hasAsymptoticExpansion_cobounded`: Borel–Ritt along `cobounded ℂ`.
* `Asymptotics.exists_hasAsymptoticExpansion_sector`: Borel–Ritt with holomorphy in the open
  exterior sector and the expansion along the closed sector.
* `Asymptotics.exists_ne_hasAsymptoticExpansion_cobounded`: two functions that differ everywhere
  have the same expansion along `cobounded ℂ`; `Asymptotics.exists_ne_hasAsymptoticExpansion_sector`
  is its restriction to a sector.
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

/-- For `c > 0` and `0 < α < 1/2`, the nowhere vanishing function `exp(-c z^α)` has the zero
expansion in inverse powers of `z` along `cobounded ℂ`. -/
theorem hasAsymptoticExpansion_cexp_neg_mul_cpow {c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hα2 : α < 1 / 2) :
    HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) (0 : ℕ → ℂ)
      fun z => cexp (-(c * z ^ (α : ℂ))) :=
  hasAsymptoticExpansion_zero_iff.2 fun N =>
    (TauCeti.isLittleO_cexp_neg_mul_cpow_cobounded hc hα hα2 (-(N : ℝ))).isBigO.trans
      (isBigO_of_le _ fun z => le_of_eq (by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _),
          Real.rpow_neg (norm_nonneg z), Real.rpow_natCast, norm_inv, norm_pow]))

/-! ### The Borel–Ritt function -/

/-- The damping exponential `exp(-b z^α)` is holomorphic on the slit plane. -/
private lemma differentiableAt_cexp_neg_mul_cpow (b α : ℝ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (fun w : ℂ => cexp (-(b * w ^ (α : ℂ)))) z :=
  ((differentiableAt_id.cpow_const hz).const_mul _).neg.cexp

/-- For `θ ≤ π`, the open exterior sector `{1 < |z|, |ph z| < θ}` lies in the slit exterior
`{1 < |z|} ∩ slitPlane`. -/
private lemma setOf_sector_subset {θ : ℝ} (hθπ : θ ≤ π) :
    {z : ℂ | 1 < ‖z‖ ∧ |arg z| < θ} ⊆ {z | 1 < ‖z‖} ∩ slitPlane := fun z hz =>
  ⟨hz.1, mem_slitPlane_of_abs_arg_lt (hz.2.trans_le hθπ) (norm_pos_iff.1 (by linarith [hz.1]))⟩

/-- The damping weights `bₛ = ((1 + |aₛ|) 2ˢ)⁻¹`. -/
private def borelRittWeight (a : ℕ → ℂ) (s : ℕ) : ℝ := ((1 + ‖a s‖) * 2 ^ s)⁻¹

/-- The damped terms `aₛ z⁻ˢ (1 - exp(-bₛ z^{1/4}))`. -/
private def borelRittTerm (a : ℕ → ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  (z ^ s)⁻¹ * a s * (1 - cexp (-(borelRittWeight a s * z ^ ((1 / 4 : ℝ) : ℂ))))

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
  set ζ : ℂ := b * z ^ ((1 / 4 : ℝ) : ℂ)
  have hcos : 0 ≤ Real.cos (1 / 4 * π) := by
    rw [one_div_mul_eq_div, Real.cos_pi_div_four]; positivity
  have hre : 0 ≤ ζ.re := by
    rw [re_ofReal_mul]
    exact mul_nonneg hb.le (le_trans (mul_nonneg hcos (Real.rpow_nonneg (norm_nonneg z) _))
      (TauCeti.cos_mul_norm_rpow_le_re_cpow (y := 1 / 4) (abs_le.2 ⟨by norm_num, by norm_num⟩)))
  have hζ : ‖ζ‖ = b * ‖z‖ ^ (1 / 4 : ℝ) := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hb.le, norm_cpow_real]
  have hw := borelRittWeight_mul_le a (k + 1)
  rw [borelRittTerm, norm_mul, norm_mul, norm_inv, norm_pow]
  calc (‖z‖ ^ (k + 1))⁻¹ * ‖a (k + 1)‖ * ‖1 - cexp (-ζ)‖
      ≤ (‖z‖ ^ (k + 1))⁻¹ * ‖a (k + 1)‖ * (b * ‖z‖ ^ (1 / 4 : ℝ)) := by
        rw [← hζ]; gcongr; exact Complex.norm_one_sub_exp_neg_le hre
    _ = (b * ‖a (k + 1)‖) * (‖z‖ ^ (1 / 4 : ℝ) * (‖z‖ ^ (k + 1))⁻¹) := by ring
    _ ≤ (1 / 2) ^ (k + 1) * (‖z‖ ^ (1 / 4 : ℝ) * (‖z‖ ^ (k + 1))⁻¹) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_of_le_one (by norm_num) (by norm_num) k.le_succ) (by positivity)

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
  exact (differentiableAt_const _).sub (differentiableAt_cexp_neg_mul_cpow _ _ hz.2)

/-- The tail `∑_{k ≥ M + 1}` of the damped terms of index `k + 1` is `O(z^{-M-1})`. -/
private lemma isBigO_tsum_borelRittTerm (a : ℕ → ℂ) (M : ℕ) :
    (fun z => ∑' k, borelRittTerm a (k + (M + 1) + 1) z) =O[cobounded ℂ]
      fun z => (z ^ (M + 1))⁻¹ := by
  refine (isBigO_inv_pow_cobounded_of_norm_le (c := 0) (R := 1) (A := 2) (M + 1)
    fun z hz => ?_).congr_right fun z => inv_pow z _
  rw [sub_zero] at hz ⊢
  rw [div_eq_mul_inv]
  refine tsum_of_norm_bounded (hasSum_geometric_two.mul_right _) fun k => ?_
  refine (norm_borelRittTerm_le_pow a (by omega : M + 1 ≤ k + (M + 1)) hz.le).trans ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega))
    (by positivity)

/-- The difference between a damped term and the undamped term `aₛ z⁻ˢ` is `O(z⁻ᴺ)` for every
`N`. -/
private lemma isBigO_borelRittTerm_sub (a : ℕ → ℂ) (s N : ℕ) :
    (fun z => borelRittTerm a (s + 1) z - (z ^ (s + 1))⁻¹ * a (s + 1)) =O[cobounded ℂ]
      fun z => (z ^ N)⁻¹ := by
  have hpow : (fun z : ℂ => (z ^ (s + 1))⁻¹) =O[cobounded ℂ] fun _ => (1 : ℂ) :=
    ((tendsto_inv₀_cobounded.pow (s + 1)).isBigO_one ℂ).congr_left fun z => inv_pow z _
  have he := hasAsymptoticExpansion_zero_iff.1 (hasAsymptoticExpansion_cexp_neg_mul_cpow
    (borelRittWeight_pos a (s + 1)) (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)) N
  have h := (hpow.mul he).const_mul_left (-a (s + 1))
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

/-! ### Borel–Ritt existence and non-uniqueness -/

/-- **Borel–Ritt** along `cobounded ℂ`: every sequence `a` is the expansion `∑ aₛ z⁻ˢ` at
infinity of a function holomorphic in `{1 < |z|}` off the negative real axis. -/
theorem exists_hasAsymptoticExpansion_cobounded (a : ℕ → ℂ) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f ({z | 1 < ‖z‖} ∩ slitPlane) ∧
      HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) a f :=
  ⟨borelRitt a, differentiableOn_borelRitt a, hasAsymptoticExpansion_borelRitt a⟩

/-- **Borel–Ritt** in a sector (DLMF §2.1(iii)): for `θ ≤ π`, every sequence `a` is the
expansion `∑ aₛ z⁻ˢ` along the closed sector, `cobounded ℂ ⊓ 𝓟 {|ph z| ≤ θ}`, of a function
holomorphic in the open exterior sector `{1 < |z|, |ph z| < θ}`. -/
theorem exists_hasAsymptoticExpansion_sector (a : ℕ → ℂ) {θ : ℝ} (hθπ : θ ≤ π) :
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧
      HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ})
        (fun n z => (z ^ n)⁻¹) a f := by
  obtain ⟨f, hfd, hf⟩ := exists_hasAsymptoticExpansion_cobounded a
  exact ⟨f, hfd.mono (setOf_sector_subset hθπ), hf.mono inf_le_left⟩

/-- Non-uniqueness in Borel–Ritt along `cobounded ℂ` (DLMF §2.1(iii), 2.1.17): every sequence
`a` is the expansion along `cobounded ℂ` of two functions holomorphic in `{1 < |z|}` off the
negative real axis that differ at every point. -/
theorem exists_ne_hasAsymptoticExpansion_cobounded (a : ℕ → ℂ) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f ({z | 1 < ‖z‖} ∩ slitPlane) ∧
      DifferentiableOn ℂ g ({z | 1 < ‖z‖} ∩ slitPlane) ∧ (∀ z, f z ≠ g z) ∧
      HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) a f ∧
      HasAsymptoticExpansion (cobounded ℂ) (fun n z => (z ^ n)⁻¹) a g := by
  obtain ⟨f, hfd, hf⟩ := exists_hasAsymptoticExpansion_cobounded a
  have he := hasAsymptoticExpansion_cexp_neg_mul_cpow (c := 1) (α := 1 / 4) one_pos
    (by norm_num) (by norm_num)
  refine ⟨f, fun z => f z + cexp (-((1 : ℝ) * z ^ ((1 / 4 : ℝ) : ℂ))), hfd,
    hfd.add fun z hz => (differentiableAt_cexp_neg_mul_cpow _ _ hz.2).differentiableWithinAt,
    fun z h => ?_, hf, (hf.add he).congr_coeff fun n => add_zero _⟩
  exact Complex.exp_ne_zero _ (by linear_combination -h)

/-- Non-uniqueness in Borel–Ritt in a sector (DLMF §2.1(iii), 2.1.17): for `θ ≤ π`, every
sequence `a` is the expansion along the closed sector `|ph z| ≤ θ` of two functions holomorphic
in the open exterior sector `{1 < |z|, |ph z| < θ}` that differ at every point. -/
theorem exists_ne_hasAsymptoticExpansion_sector (a : ℕ → ℂ) {θ : ℝ} (hθπ : θ ≤ π) :
    ∃ f g : ℂ → ℂ, DifferentiableOn ℂ f {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧
      DifferentiableOn ℂ g {z | 1 < ‖z‖ ∧ |arg z| < θ} ∧ (∀ z, f z ≠ g z) ∧
      HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ}) (fun n z => (z ^ n)⁻¹) a f ∧
      HasAsymptoticExpansion (cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ θ}) (fun n z => (z ^ n)⁻¹) a g := by
  obtain ⟨f, g, hfd, hgd, hne, hf, hg⟩ := exists_ne_hasAsymptoticExpansion_cobounded a
  exact ⟨f, g, hfd.mono (setOf_sector_subset hθπ), hgd.mono (setOf_sector_subset hθπ), hne,
    hf.mono inf_le_left, hg.mono inf_le_left⟩

/-- **Borel–Ritt** on the positive real axis (DLMF §2.1(iii)): every sequence `a` is the
expansion `∑ aₛ x⁻ˢ` of a function of `x` as `x → +∞`. -/
theorem exists_hasAsymptoticExpansion_atTop (a : ℕ → ℂ) :
    ∃ f : ℝ → ℂ, HasAsymptoticExpansion atTop (fun n (x : ℝ) => (x ^ n)⁻¹) a f := by
  obtain ⟨f, -, hf⟩ := exists_hasAsymptoticExpansion_cobounded a
  have h := hf.comp_tendsto (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  refine ⟨fun x => f x, HasAsymptoticExpansion.of_isBigO fun N => ?_⟩
  refine (Complex.isBigO_ofReal_right.mp ((h.isBigO N).congr_right fun x => ?_)).congr_left
    fun x => ?_
  · simp
  simp [Complex.real_smul]

end Asymptotics
