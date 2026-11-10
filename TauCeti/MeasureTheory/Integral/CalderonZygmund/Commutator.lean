/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import TauCeti.MeasureTheory.Function.BoundedMeanOscillation
public import TauCeti.MeasureTheory.Integral.UncenteredMaximalFunction
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.CalderonZygmund.BoundedMeanOscillation
import TauCeti.MeasureTheory.Integral.JohnNirenberg

/-!
# The sharp maximal function of a commutator with a BMO function

Let `T` be a singular integral operator on `ℝⁿ = ι → ℝ`, `n ≥ 1`: a bounded linear operator on `L²`
given off the support of its argument by a kernel `K` that satisfies the standard smoothness
estimate in its first variable,

`‖K x y - K x' y‖ ≤ A dist x x' ^ δ dist y x' ^ (-(n + δ))` whenever `dist y x' > 2 dist x x'`,

and bounded in the `Lᵘ` norm for some `1 ≤ u < ∞`. For a function `b` of bounded mean oscillation
the **commutator** `[b, T] f = b T f - T (b f)` is in general not a singular integral of the same
kind, but its oscillation is controlled pointwise: for every `t > u`,

`([b, T] f)^#(x) ≤ C ‖b‖_{BMO} (M(‖T f‖^t)(x)^{1/t} + M(‖f‖^t)(x)^{1/t})`,

where `^#` is the sharp maximal function (`TauCeti.sharpMaximalFunction`), `M` is the uncentred
maximal function (`TauCeti.uncenteredMaximalFunction`), and `C` depends only on `n`, `u`, `t`, `δ`,
`A` and the `Lᵘ` bound of `T` (`TauCeti.exists_sharpMaximalFunction_smul_sub_le`). This is the
estimate of Janson and Strömberg behind the Coifman–Rochberg–Weiss theorem
`‖[b, T] f‖_p ≲ ‖b‖_{BMO} ‖f‖_p`: for `p > t`, the Fefferman–Stein inequality
(`TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction`) and the boundedness of the maximal function
on `L^{p/t}` reduce that `Lᵖ` bound to this pointwise estimate.

## The argument

Fix a ball `B = B(c, r)` containing `x` and put `m = b_{2B}`, the average of `b` over `2B`.
Splitting `(b - m) f = φ₁ + φ₂` with `φ₁ = 1_{2B} (b - m) f`, one has

`[b, T] f = (b - m) T f - T φ₁ - T φ₂`,

and each term is compared with a constant on `B`:

* `(b - m) T f`: by Hölder's inequality with the exponents `t` and `t' = t / (t - 1)`, its average
  over `B` is at most `(⨍_B |b - m|^{t'})^{1/t'} M(‖T f‖^t)(x)^{1/t}`, and the John–Nirenberg
  moment bound (`TauCeti.setLAverage_enorm_sub_setAverage_rpow_le`) controls the first factor by
  `‖b‖_{BMO}`.
* `T φ₁`: the `Lᵘ` bound of `T` and Hölder's inequality on `2B` with the exponents `t / u` and its
  conjugate bound the average of `‖T φ₁‖` over `B` by `‖b‖_{BMO} M(‖f‖^t)(x)^{1/t}`.
* `T φ₂`: since `φ₂` vanishes on `2B`, on `B` the operator is given by the kernel, and the
  smoothness estimate bounds `T φ₂ - ∫ K c z (φ₂ z) dz` by
  `A r^δ ∫_{(2B)ᶜ} dist(z, c)^(-(n+δ)) |b z - m| ‖f z‖ dz`. On the dyadic annulus at distance
  `2^(k+1) r` this is `4ⁿ 2^(-(k+1)δ)` times an average over `2^(k+1) · 2B`, which Hölder's
  inequality bounds by `(C + (k + 1) 2ⁿ) ‖b‖_{BMO} M(‖f‖^t)(x)^{1/t}`: the averages of `b` over
  consecutive concentric balls differ by at most `2ⁿ ‖b‖_{BMO}`. The series in `k` converges.

Finally, the mean oscillation of a function about its own average is at most twice its mean
oscillation about any constant (`TauCeti.setLAverage_enorm_sub_setAverage_le`).

The kernel representation is assumed in the form used by the `L^∞ → BMO` bound
(`ContinuousLinearMap.setLAverage_enorm_sub_setAverage_le_of_hormander`). For `u = 2` the `Lᵘ`
bound holds with the operator norm of `T`; for `1 < u < 2` it follows, under Hörmander's
condition, from the Calderón–Zygmund theorem (`ContinuousLinearMap.eLpNorm_le_of_hormander`),
which lets `t` be taken arbitrarily close to `1`. The function `b` enters only through
`‖b‖_{BMO}`; the commutator is formed on `L²`, so `b f` is assumed to lie in `L²`.

## Main declarations

* `TauCeti.exists_sharpMaximalFunction_smul_sub_le`: the pointwise sharp maximal function estimate
  for the commutator `[b, T] f = b T f - T (b f)`.

## References

* R. R. Coifman, R. Rochberg, G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. **103** (1976), 611–635.
* S. Janson, *Mean oscillation and commutators of singular integral operators*, Ark. Mat. **16**
  (1978), 263–270.
* J.-O. Strömberg, *Bounded mean oscillation with Orlicz norms and duality of Hardy spaces*,
  Indiana Univ. Math. J. **28** (1979), 511–544.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.5.
-/

public section

namespace TauCeti

open MeasureTheory Metric Set
open scoped ENNReal NNReal

variable {ι : Type*} [Fintype ι] {b : (ι → ℝ) → ℝ}

/-- The `Lᵠ` distance of `b` from a constant `a` on a ball `B` is at most `C(n, q)^{1/q} ‖b‖_{BMO}`
plus `‖b_B - a‖`: Minkowski's inequality for the normalized restriction of Lebesgue measure to `B`,
and the John–Nirenberg moment bound. -/
private theorem rpow_setLAverage_enorm_sub_rpow_le [Nonempty ι] (hb : LocallyIntegrable b volume)
    {q : ℝ} (hq : 1 ≤ q) (c : ι → ℝ) {r : ℝ} (hr : 0 < r) (a : ℝ) :
    (⨍⁻ x in ball c r, ‖b x - a‖ₑ ^ q) ^ q⁻¹ ≤
      ENNReal.ofReal ((1 + 7 * (⌈q⌉₊).factorial) *
        (2 ^ (Fintype.card ι + 1) / Real.log (3 / 2)) ^ q) ^ q⁻¹ * bmoSeminorm b volume +
        ‖(⨍ y in ball c r, b y) - a‖ₑ := by
  have hq0 : 0 < q := one_pos.trans_le hq
  set B := ball c r
  set m := ⨍ y in B, b y
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  set ν : Measure (ι → ℝ) := (volume.restrict B univ)⁻¹ • volume.restrict B
  have hmeas : AEMeasurable (fun x => ‖b x - m‖ₑ) ν :=
    (hb.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.restrict.smul_measure _
  -- Minkowski's inequality for the probability measure `ν`, the normalized restriction to `B`.
  have hmink := ENNReal.lintegral_Lp_add_le (μ := ν) hmeas (aemeasurable_const (b := ‖m - a‖ₑ)) hq
  have hconst : (∫⁻ _, ‖m - a‖ₑ ^ q ∂ν) ^ (1 / q) = ‖m - a‖ₑ := by
    have : ∫⁻ _, ‖m - a‖ₑ ^ q ∂ν = ‖m - a‖ₑ ^ q := by
      rw [lintegral_const, _root_.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
        ENNReal.inv_mul_cancel hB0 hBtop, mul_one]
    rw [this, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  have hJN := setLAverage_enorm_sub_setAverage_rpow_le hb hq0 c r
  rw [one_div] at hmink hconst
  calc (⨍⁻ x in B, ‖b x - a‖ₑ ^ q) ^ q⁻¹
      ≤ (∫⁻ x, (fun x => ‖b x - m‖ₑ + ‖m - a‖ₑ) x ^ q ∂ν) ^ q⁻¹ := by
        rw [laverage_eq']
        gcongr with x
        calc ‖b x - a‖ₑ = ‖(b x - m) + (m - a)‖ₑ := by rw [sub_add_sub_cancel]
          _ ≤ _ := enorm_add_le _ _
    _ ≤ _ := hmink
    _ ≤ _ := by
        rw [hconst]
        gcongr
        rw [← laverage_eq']
        calc (⨍⁻ x in B, ‖b x - m‖ₑ ^ q) ^ q⁻¹ ≤ (_ * bmoSeminorm b volume ^ q) ^ q⁻¹ := by
              gcongr
          _ = _ := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq0.le), ← ENNReal.rpow_mul,
                mul_inv_cancel₀ hq0.ne', ENNReal.rpow_one]

/-- Doubling the radius of a sup-norm ball multiplies its volume by `2ⁿ`. -/
private theorem volume_ball_two_mul_div (c : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    volume (ball c (2 * s)) / volume (ball c s) = 2 ^ Fintype.card ι := by
  rw [Real.volume_pi_ball c (by positivity), Real.volume_pi_ball c hs,
    show 2 * (2 * s) = 2 * (2 * s) from rfl, mul_left_comm, mul_pow,
    ENNReal.ofReal_mul (by positivity), ENNReal.mul_div_cancel_right
      (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top,
    ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- The averages of `b` over concentric balls of radii `s` and `2s` differ by at most
`2ⁿ ‖b‖_{BMO}`. -/
private theorem enorm_setAverage_ball_sub_setAverage_ball_two_mul_le
    (hb : LocallyIntegrable b volume) (c : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    ‖(⨍ y in ball c s, b y) - ⨍ y in ball c (2 * s), b y‖ₑ ≤
      2 ^ Fintype.card ι * bmoSeminorm b volume := by
  refine (enorm_setAverage_sub_le_of_subset (s := ball c s) (t := ball c (2 * s))
    (ball_subset_ball (by linarith))
    (measure_ball_pos volume c hs).ne' measure_ball_lt_top.ne
    hb.aestronglyMeasurable.restrict _).trans ?_
  rw [volume_ball_two_mul_div c hs]
  gcongr
  exact setLAverage_enorm_sub_setAverage_le_bmoSeminorm b volume c _

/-- The averages of `b` over concentric balls of radii `ρ` and `2ʲ ρ` differ by at most
`j 2ⁿ ‖b‖_{BMO}`. -/
private theorem enorm_setAverage_ball_two_pow_mul_sub_le
    (hb : LocallyIntegrable b volume) (c : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    ‖(⨍ y in ball c (2 ^ j * ρ), b y) - ⨍ y in ball c ρ, b y‖ₑ ≤
      j * 2 ^ Fintype.card ι * bmoSeminorm b volume := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hstep := enorm_setAverage_ball_sub_setAverage_ball_two_mul_le hb c
      (show 0 < 2 ^ j * ρ by positivity)
    rw [enorm_sub_rev, ← mul_assoc, ← pow_succ'] at hstep
    calc ‖(⨍ y in ball c (2 ^ (j + 1) * ρ), b y) - ⨍ y in ball c ρ, b y‖ₑ
        ≤ ‖(⨍ y in ball c (2 ^ (j + 1) * ρ), b y) - ⨍ y in ball c (2 ^ j * ρ), b y‖ₑ +
            ‖(⨍ y in ball c (2 ^ j * ρ), b y) - ⨍ y in ball c ρ, b y‖ₑ := by
          rw [← sub_add_sub_cancel _ (⨍ y in ball c (2 ^ j * ρ), b y)]
          exact enorm_add_le _ _
      _ ≤ 2 ^ Fintype.card ι * bmoSeminorm b volume +
            j * 2 ^ Fintype.card ι * bmoSeminorm b volume :=
          add_le_add hstep ih
      _ = (j + 1 : ℕ) * 2 ^ Fintype.card ι * bmoSeminorm b volume := by push_cast; ring

/-- Hölder's inequality against `b - a` on a ball containing `x`, for conjugate exponents `t'` and
`t`: the average of `‖b - a‖ φ` is at most `(C(n, t')^{1/t'} ‖b‖_{BMO} + ‖b_B - a‖)` times
`M(φ^t)(x)^{1/t}`, with `M` the uncentred maximal function. -/
private theorem setLAverage_enorm_sub_mul_le [Nonempty ι] (hb : LocallyIntegrable b volume)
    {t t' : ℝ} (htt : t'.HolderConjugate t) {φ : (ι → ℝ) → ℝ≥0∞} (hφ : AEMeasurable φ volume)
    (c : ι → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ) {x : ι → ℝ} (hx : x ∈ ball c ρ) :
    ⨍⁻ z in ball c ρ, ‖b z - a‖ₑ * φ z ≤
      (ENNReal.ofReal ((1 + 7 * (⌈t'⌉₊).factorial) *
        (2 ^ (Fintype.card ι + 1) / Real.log (3 / 2)) ^ t') ^ t'⁻¹ * bmoSeminorm b volume +
        ‖(⨍ y in ball c ρ, b y) - a‖ₑ) *
        uncenteredMaximalFunction volume (fun z => φ z ^ t) x ^ t⁻¹ := by
  have hhol := ENNReal.lintegral_mul_le_Lp_mul_Lq
    ((volume.restrict (ball c ρ) univ)⁻¹ • volume.restrict (ball c ρ)) htt
    (f := fun z => ‖b z - a‖ₑ)
    ((hb.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.restrict.smul_measure _)
    (hφ.restrict.smul_measure _)
  simp only [one_div, Pi.mul_apply, ← laverage_eq'] at hhol
  refine hhol.trans (mul_le_mul' (rpow_setLAverage_enorm_sub_rpow_le hb htt.lt.le c hρ a) ?_)
  gcongr
  · exact inv_nonneg.2 htt.symm.nonneg
  simpa only [enorm_eq_self] using
    setLAverage_le_uncenteredMaximalFunction volume (fun z => φ z ^ t) hx

/-- A point off `ball c (2r)` lies in one of the dyadic annuli
`2^(k+1) r ≤ dist z c < 2^(k+2) r`. -/
private theorem exists_two_pow_mul_le_dist_lt {c z : ι → ℝ} {r : ℝ} (hr : 0 < r)
    (hz : z ∉ ball c (2 * r)) :
    ∃ k : ℕ, 2 ^ (k + 1) * r ≤ dist z c ∧ dist z c < 2 ^ (k + 1) * (2 * r) := by
  rw [mem_ball, not_lt] at hz
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := dist z c / (2 * r))
    ((one_le_div (by positivity)).2 hz) one_lt_two
  refine ⟨k, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at hk1
    have : (2 : ℝ) ^ (k + 1) * r = 2 ^ k * (2 * r) := by ring
    linarith
  · rw [div_lt_iff₀ (by positivity)] at hk2
    linarith

/-- The arithmetic of the `k`-th dyadic annulus: `r^δ (2^(k+1) r)^(-(n+δ))` times the volume
`(2 · 2^(k+2) r)ⁿ` of the enclosing ball is `4ⁿ 2^(-(k+1)δ)`. -/
private theorem rpow_mul_rpow_neg_mul_pow_eq (n : ℕ) {r δ : ℝ} (hr : 0 < r) (k : ℕ) :
    r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ)) * (2 * (2 ^ (k + 1) * (2 * r))) ^ n =
      4 ^ n * 2 ^ (-((k + 1) * δ)) := by
  have h2 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  rw [Real.rpow_neg (by positivity), Real.rpow_add (by positivity), Real.rpow_natCast,
    Real.mul_rpow h2.le hr.le]
  have : (2 : ℝ) ^ (-((k + 1) * δ)) = (((2 : ℝ) ^ (k + 1)) ^ δ)⁻¹ := by
    rw [Real.rpow_neg zero_le_two, Real.rpow_mul zero_le_two, ← Real.rpow_natCast]
    push_cast
    rfl
  rw [this]
  have hrδ : 0 < r ^ δ := Real.rpow_pos_of_pos hr δ
  have h2δ : 0 < ((2 : ℝ) ^ (k + 1)) ^ δ := Real.rpow_pos_of_pos h2 δ
  field_simp
  simp only [mul_pow]
  norm_num

variable {E : Type*} [NormedAddCommGroup E]

/-- **The far part.** Off `ball c (2r)`, the weight `r^δ dist(z, c)^(-(n+δ))` integrated against
`‖b - b_{2B}‖ ‖f‖` is at most a convergent series times `‖b‖_{BMO} M(‖f‖^t)(x)^{1/t}`. The proof
splits the complement into dyadic annuli, applies Hölder's inequality on each enclosing ball, and
sums the telescoped averages of `b`. -/
private theorem setLIntegral_compl_ball_le [Nonempty ι] (hb : LocallyIntegrable b volume)
    {t t' : ℝ} (htt : t'.HolderConjugate t) {f : (ι → ℝ) → E} (hf : AEStronglyMeasurable f volume)
    (c : ι → ℝ) {r : ℝ} (hr : 0 < r) {δ : ℝ} (hδ : 0 ≤ δ) {x : ι → ℝ} (hx : x ∈ ball c r) :
    ∫⁻ z in (ball c (2 * r))ᶜ, ENNReal.ofReal (r ^ δ * dist z c ^ (-(Fintype.card ι + δ))) *
        (‖b z - ⨍ y in ball c (2 * r), b y‖ₑ * ‖f z‖ₑ) ≤
      (∑' k : ℕ, ENNReal.ofReal (4 ^ Fintype.card ι * 2 ^ (-((k + 1) * δ))) *
        (ENNReal.ofReal ((1 + 7 * (⌈t'⌉₊).factorial) *
          (2 ^ (Fintype.card ι + 1) / Real.log (3 / 2)) ^ t') ^ t'⁻¹ +
          (k + 1) * 2 ^ Fintype.card ι)) * bmoSeminorm b volume *
        uncenteredMaximalFunction volume (fun z => ‖f z‖ₑ ^ t) x ^ t⁻¹ := by
  set n := Fintype.card ι
  set m := ⨍ y in ball c (2 * r), b y
  set W : (ι → ℝ) → ℝ≥0∞ := fun z => ‖b z - m‖ₑ * ‖f z‖ₑ
  set S : ℕ → Set (ι → ℝ) := fun k => ball c (2 ^ (k + 1) * (2 * r))
  set C' := ENNReal.ofReal ((1 + 7 * (⌈t'⌉₊).factorial) *
    (2 ^ (n + 1) / Real.log (3 / 2)) ^ t') ^ t'⁻¹
  set β := bmoSeminorm b volume
  set M := uncenteredMaximalFunction volume (fun z => ‖f z‖ₑ ^ t) x ^ t⁻¹
  have hW : AEMeasurable W volume :=
    (hb.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.mul hf.enorm
  -- Each point off `ball c (2r)` lies in one dyadic annulus.
  have hpt : ∀ z ∈ (ball c (2 * r))ᶜ,
      ENNReal.ofReal (r ^ δ * dist z c ^ (-(n + δ))) * W z ≤
        ∑' k : ℕ, ENNReal.ofReal (r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ))) *
          (S k).indicator W z := by
    intro z hz
    obtain ⟨k, hk1, hk2⟩ := exists_two_pow_mul_le_dist_lt hr hz
    refine le_trans ?_ (le_tsum _ k)
    rw [indicator_of_mem (mem_ball.2 hk2)]
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (neg_nonpos.2 (by positivity)))
      (Real.rpow_nonneg hr.le _))) _
  -- On each annulus, Hölder's inequality and the telescoping of averages bound the integral.
  have hk : ∀ k : ℕ, ENNReal.ofReal (r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ))) *
      ∫⁻ z in S k, W z ≤ ENNReal.ofReal (4 ^ n * 2 ^ (-((k + 1) * δ))) *
        (C' + (k + 1) * 2 ^ n) * β * M := by
    intro k
    have hρ : 0 < 2 ^ (k + 1) * (2 * r) := by positivity
    have hxS : x ∈ S k := ball_subset_ball (by
      have : (1 : ℝ) ≤ 2 ^ (k + 1) := one_le_pow₀ one_le_two
      nlinarith) hx
    have hhol := setLAverage_enorm_sub_mul_le hb htt hf.enorm c hρ m hxS
    have htel := enorm_setAverage_ball_two_pow_mul_sub_le hb c (show 0 < 2 * r by positivity)
      (k + 1)
    rw [← measure_mul_setLAverage _ measure_ball_lt_top.ne, Real.volume_pi_ball c hρ, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), rpow_mul_rpow_neg_mul_pow_eq n hr k, mul_assoc,
      mul_assoc]
    gcongr
    calc ⨍⁻ z in S k, W z ≤ (C' * β + ‖(⨍ y in S k, b y) - m‖ₑ) * M := hhol
      _ ≤ (C' * β + (k + 1) * 2 ^ n * β) * M := by
          gcongr
          exact htel.trans_eq (by push_cast; ring)
      _ = (C' + (k + 1) * 2 ^ n) * (β * M) := by ring
  calc ∫⁻ z in (ball c (2 * r))ᶜ, ENNReal.ofReal (r ^ δ * dist z c ^ (-(n + δ))) * W z
      ≤ ∫⁻ z in (ball c (2 * r))ᶜ, ∑' k : ℕ,
          ENNReal.ofReal (r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ))) * (S k).indicator W z :=
        setLIntegral_mono' measurableSet_ball.compl hpt
    _ ≤ ∫⁻ z, ∑' k : ℕ,
          ENNReal.ofReal (r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ))) * (S k).indicator W z :=
        setLIntegral_le_lintegral _ _
    _ = ∑' k : ℕ, ENNReal.ofReal (r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ))) *
          ∫⁻ z in S k, W z := by
        rw [lintegral_tsum fun k => (hW.indicator measurableSet_ball).const_mul _]
        congr 1 with k
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_ball]
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (4 ^ n * 2 ^ (-((k + 1) * δ))) * (C' + (k + 1) * 2 ^ n) * β * M :=
        tsum_le_tsum hk
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]

variable [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The kernel step.** If `φ ∈ L²` vanishes on `ball c (2r)`, then on `ball c r` the function
`T φ` stays within `A ∫_{(2B)ᶜ} r^δ dist(z, c)^(-(n+δ)) ‖φ z‖ dz` of the kernel integral at the
centre, by the smoothness of the kernel in its first variable. -/
private theorem ae_enorm_apply_sub_integral_le
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hKm : ∀ x, AEStronglyMeasurable (K x) volume)
    {A : ℝ≥0} {δ : ℝ} (hδ : 0 ≤ δ)
    (hK : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ))))
    (hrep : ∀ (φ : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
      (∀ᵐ z, z ∈ ball y ρ → φ z = 0) → ∀ᵐ x, x ∈ ball y ρ → T φ x = ∫ z, K x z (φ z))
    (φ : Lp E 2 (volume : Measure (ι → ℝ))) (c : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hφ : ∀ᵐ z, z ∈ ball c (2 * r) → φ z = 0) :
    ∀ᵐ y, y ∈ ball c r → ‖T φ y - ∫ z, K c z (φ z)‖ₑ ≤
      A * ∫⁻ z in (ball c (2 * r))ᶜ,
        ENNReal.ofReal (r ^ δ * dist z c ^ (-(Fintype.card ι + δ))) * ‖φ z‖ₑ := by
  filter_upwards [hrep φ c (2 * r) hφ] with y hy hyB
  rw [hy (ball_subset_ball (by linarith) hyB)]
  have hmeas (x : ι → ℝ) : AEStronglyMeasurable (fun z => K x z (φ z)) volume := by
    simpa using (ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂
      (Lp.aestronglyMeasurable φ) (hKm x)
  refine (enorm_integral_sub_integral_le_lintegral_enorm_sub (hmeas y) (hmeas c)).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← lintegral_indicator measurableSet_ball.compl]
  refine lintegral_mono_ae ?_
  filter_upwards [hφ] with z hz
  by_cases hzB : z ∈ ball c (2 * r)
  · simp [hz hzB]
  rw [indicator_of_mem (mem_compl hzB)]
  have hyc : dist y c < r := mem_ball.1 hyB
  have hd : 2 * dist y c < dist z c := by
    rw [mem_ball, not_lt] at hzB
    linarith
  have hKyz : ‖K y z - K c z‖ₑ ≤
      A * ENNReal.ofReal (r ^ δ * dist z c ^ (-(Fintype.card ι + δ))) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul A.coe_nonneg]
    refine ENNReal.ofReal_le_ofReal ((hK y c z hd).trans ?_)
    gcongr
  calc ‖K y z (φ z) - K c z (φ z)‖ₑ = ‖(K y z - K c z) (φ z)‖ₑ := by
        rw [sub_apply]
    _ ≤ ‖K y z - K c z‖ₑ * ‖φ z‖ₑ := ContinuousLinearMap.le_opENorm _ _
    _ ≤ _ := by rw [← mul_assoc]; gcongr

/-- **The local part.** If `‖φ‖ ≤ 1_{2B} ‖b - b_{2B}‖ ‖f‖`, then the average of `‖T φ‖` over `B` is
controlled through the `Lᵘ` bound of `T` and Hölder's inequality on `2B` with the exponents
`t / u` and its conjugate. -/
private theorem setLAverage_enorm_apply_le [Nonempty ι]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {u t : ℝ} (hu : 1 ≤ u) (hut : u < t) {N : ℝ≥0}
    (hTu : ∀ φ : Lp E 2 (volume : Measure (ι → ℝ)),
      eLpNorm (T φ) (ENNReal.ofReal u) volume ≤ N * eLpNorm φ (ENNReal.ofReal u) volume)
    (hb : LocallyIntegrable b volume) {f : (ι → ℝ) → E} (hf : AEStronglyMeasurable f volume)
    (φ : Lp E 2 (volume : Measure (ι → ℝ))) (c : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hφ : ∀ᵐ z, ‖φ z‖ₑ ≤ (ball c (2 * r)).indicator
      (fun z => ‖b z - ⨍ y in ball c (2 * r), b y‖ₑ * ‖f z‖ₑ) z)
    {x : ι → ℝ} (hx : x ∈ ball c r) :
    ⨍⁻ y in ball c r, ‖T φ y‖ₑ ≤
      (2 ^ Fintype.card ι : ℝ≥0∞) ^ u⁻¹ * N *
        (ENNReal.ofReal ((1 + 7 * (⌈u * (t / u).conjExponent⌉₊).factorial) *
          (2 ^ (Fintype.card ι + 1) / Real.log (3 / 2)) ^ (u * (t / u).conjExponent)) ^
            (u * (t / u).conjExponent)⁻¹ * bmoSeminorm b volume) *
        uncenteredMaximalFunction volume (fun z => ‖f z‖ₑ ^ t) x ^ t⁻¹ := by
  set n := Fintype.card ι
  have hu0 : 0 < u := one_pos.trans_le hu
  set v := t / u
  have hv : 1 < v := (one_lt_div hu0).2 hut
  set v' := v.conjExponent
  have hvv : v'.HolderConjugate v := (Real.HolderConjugate.conjExponent hv).symm
  set w := u * v'
  have hw : 1 ≤ w := one_le_mul_of_one_le_of_one_le hu hvv.lt.le
  set B := ball c r
  set B2 := ball c (2 * r)
  set m := ⨍ y in B2, b y
  set J := ENNReal.ofReal ((1 + 7 * (⌈w⌉₊).factorial) *
    (2 ^ (n + 1) / Real.log (3 / 2)) ^ w) ^ w⁻¹ * bmoSeminorm b volume
  set Mf := uncenteredMaximalFunction volume (fun z => ‖f z‖ₑ ^ t) x
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  have hB2 : volume B2 = 2 ^ n * volume B := by
    rw [← volume_ball_two_mul_div c hr, ENNReal.div_mul_cancel hB0 hBtop]
  -- The `Lᵘ` norm of `φ` is controlled by Hölder's inequality on `B2`.
  have hφu : ∫⁻ z, ‖φ z‖ₑ ^ u ≤ volume B2 * (J ^ u * (Mf ^ t⁻¹) ^ u) := by
    have hbm : AEMeasurable (fun z => ‖b z - m‖ₑ ^ u) (volume.restrict B2) :=
      (hb.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.restrict.pow_const _
    have hfm : AEMeasurable (fun z => ‖f z‖ₑ ^ u) (volume.restrict B2) :=
      hf.enorm.restrict.pow_const _
    have hhol := ENNReal.lintegral_mul_le_Lp_mul_Lq
      ((volume.restrict B2 univ)⁻¹ • volume.restrict B2) hvv (hbm.smul_measure _)
      (hfm.smul_measure _)
    simp only [Pi.mul_apply, ← laverage_eq', ← ENNReal.rpow_mul] at hhol
    have hw' : u * v' = w := rfl
    have huv : u * v = t := mul_div_cancel₀ t hu0.ne'
    rw [hw', huv] at hhol
    have h1 : (⨍⁻ z in B2, ‖b z - m‖ₑ ^ w) ^ (1 / v') ≤ J ^ u := by
      have hJ := rpow_setLAverage_enorm_sub_rpow_le hb hw c (show 0 < 2 * r by positivity) m
      rw [sub_self, enorm_zero, add_zero] at hJ
      calc (⨍⁻ z in B2, ‖b z - m‖ₑ ^ w) ^ (1 / v') = ((⨍⁻ z in B2, ‖b z - m‖ₑ ^ w) ^ w⁻¹) ^ u := by
            rw [← ENNReal.rpow_mul]
            congr 1
            simp only [w]
            field_simp
        _ ≤ J ^ u := by gcongr
    have h2 : (⨍⁻ z in B2, ‖f z‖ₑ ^ t) ^ (1 / v) ≤ (Mf ^ t⁻¹) ^ u := by
      have hM : ⨍⁻ z in B2, ‖f z‖ₑ ^ t ≤ Mf := by
        simpa only [enorm_eq_self] using setLAverage_le_uncenteredMaximalFunction volume
          (fun z => ‖f z‖ₑ ^ t) (ball_subset_ball (by linarith) hx)
      calc (⨍⁻ z in B2, ‖f z‖ₑ ^ t) ^ (1 / v) = ((⨍⁻ z in B2, ‖f z‖ₑ ^ t) ^ t⁻¹) ^ u := by
            rw [← ENNReal.rpow_mul]
            congr 1
            simp only [v]
            field_simp
        _ ≤ (Mf ^ t⁻¹) ^ u := by
            gcongr
            exact inv_nonneg.2 (hu0.trans hut).le
    calc ∫⁻ z, ‖φ z‖ₑ ^ u ≤ ∫⁻ z, B2.indicator (fun z => ‖b z - m‖ₑ ^ u * ‖f z‖ₑ ^ u) z := by
          refine lintegral_mono_ae ?_
          filter_upwards [hφ] with z hz
          refine (ENNReal.rpow_le_rpow hz hu0.le).trans_eq ?_
          by_cases hzB : z ∈ B2
          · simp [indicator_of_mem hzB, ENNReal.mul_rpow_of_nonneg _ _ hu0.le]
          · simp [indicator_of_notMem hzB, ENNReal.zero_rpow_of_pos hu0]
      _ = volume B2 * ⨍⁻ z in B2, ‖b z - m‖ₑ ^ u * ‖f z‖ₑ ^ u := by
          rw [lintegral_indicator measurableSet_ball, measure_mul_setLAverage _
            measure_ball_lt_top.ne]
      _ ≤ volume B2 * (J ^ u * (Mf ^ t⁻¹) ^ u) := by
          gcongr
          exact hhol.trans (mul_le_mul' h1 h2)
  have hTφu : ∫⁻ y in B, ‖T φ y‖ₑ ^ u ≤ N ^ u * (volume B2 * (J ^ u * (Mf ^ t⁻¹) ^ u)) := by
    have hu' : ENNReal.ofReal u ≠ 0 := (ENNReal.ofReal_pos.2 hu0).ne'
    calc ∫⁻ y in B, ‖T φ y‖ₑ ^ u ≤ ∫⁻ y, ‖T φ y‖ₑ ^ u := setLIntegral_le_lintegral _ _
      _ = eLpNorm (T φ) (ENNReal.ofReal u) volume ^ u := by
          rw [eLpNorm_eq_eLpNorm' hu' ENNReal.ofReal_ne_top (Lp.aestronglyMeasurable _),
            ENNReal.toReal_ofReal hu0.le, lintegral_rpow_enorm_eq_rpow_eLpNorm' hu0]
      _ ≤ (N * eLpNorm φ (ENNReal.ofReal u) volume) ^ u := by gcongr; exact hTu φ
      _ = N ^ u * ∫⁻ z, ‖φ z‖ₑ ^ u := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hu0.le,
            eLpNorm_eq_eLpNorm' hu' ENNReal.ofReal_ne_top (Lp.aestronglyMeasurable _),
            ENNReal.toReal_ofReal hu0.le, lintegral_rpow_enorm_eq_rpow_eLpNorm' hu0]
      _ ≤ _ := by gcongr
  have hX : ⨍⁻ y in B, ‖T φ y‖ₑ ^ u ≤
      ((2 ^ n : ℝ≥0∞) ^ u⁻¹ * N * J * Mf ^ t⁻¹) ^ u := by
    rw [setLAverage_eq, ENNReal.div_le_iff hB0 hBtop]
    refine hTφu.trans_eq ?_
    have key : ((2 ^ n : ℝ≥0∞) ^ u⁻¹ * N * J * Mf ^ t⁻¹) ^ u =
        2 ^ n * N ^ u * (J ^ u * (Mf ^ t⁻¹) ^ u) := by
      rw [ENNReal.mul_rpow_of_nonneg ((2 ^ n : ℝ≥0∞) ^ u⁻¹ * N * J) (Mf ^ t⁻¹) hu0.le,
        ENNReal.mul_rpow_of_nonneg ((2 ^ n : ℝ≥0∞) ^ u⁻¹ * N) J hu0.le,
        ENNReal.mul_rpow_of_nonneg ((2 ^ n : ℝ≥0∞) ^ u⁻¹) (N : ℝ≥0∞) hu0.le,
        ENNReal.rpow_inv_rpow hu0.ne']
      ring
    rw [hB2, key]
    ring
  calc ⨍⁻ y in B, ‖T φ y‖ₑ ≤ (⨍⁻ y in B, ‖T φ y‖ₑ ^ u) ^ u⁻¹ := by
        rw [ENNReal.le_rpow_inv_iff hu0]
        exact rpow_laverage_le_laverage_rpow (Lp.aestronglyMeasurable (T φ)).enorm.restrict hu
    _ ≤ (((2 ^ n : ℝ≥0∞) ^ u⁻¹ * N * J * Mf ^ t⁻¹) ^ u) ^ u⁻¹ := by gcongr
    _ = _ := ENNReal.rpow_rpow_inv hu0.ne' _

/-- The series `∑ₖ 4ⁿ 2^(-(k+1)δ) (a + (k+1) 2ⁿ)` of the far part converges for `δ > 0`. -/
private theorem tsum_ofReal_mul_add_ne_top (n : ℕ) {δ : ℝ} (hδ : 0 < δ) {a : ℝ≥0∞} (ha : a ≠ ⊤) :
    ∑' k : ℕ, ENNReal.ofReal (4 ^ n * 2 ^ (-((k + 1) * δ))) * (a + (k + 1) * 2 ^ n) ≠ ⊤ := by
  set ρ : ℝ := 2 ^ (-δ)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hδ)
  have hpow (k : ℕ) : (2 : ℝ) ^ (-((k + 1) * δ)) = ρ * ρ ^ k := by
    rw [← pow_succ', ← Real.rpow_mul_natCast zero_le_two]
    push_cast
    ring_nf
  set g : ℕ → ℝ := fun k => 4 ^ n * (ρ * ρ ^ k) * (a.toReal + (k + 1) * 2 ^ n)
  have hg0 (k : ℕ) : 0 ≤ g k := by positivity
  have hg : Summable g := by
    have h1 := (summable_geometric_of_lt_one hρ0 hρ1).mul_left (4 ^ n * ρ * (a.toReal + 2 ^ n))
    have h2 := (summable_pow_mul_geometric_of_norm_lt_one 1
      (by rwa [Real.norm_of_nonneg hρ0])).mul_left (4 ^ n * ρ * 2 ^ n)
    refine (h1.add h2).congr fun k => ?_
    simp only [g, pow_one]
    ring
  have hterm (k : ℕ) : ENNReal.ofReal (4 ^ n * 2 ^ (-((k + 1) * δ))) * (a + (k + 1) * 2 ^ n) =
      ENNReal.ofReal (g k) := by
    simp only [g]
    rw [hpow, ENNReal.ofReal_mul (show 0 ≤ 4 ^ n * (ρ * ρ ^ k) by positivity)]
    congr 1
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal ha,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg hg0 hg]
  exact ENNReal.ofReal_ne_top

/-- **Splitting the commutator.** For a measurable set `S` and a constant `m`, write
`(b - m) f = φ₁ + φ₂` with `φ₁` supported on `S` and `φ₂` vanishing on `S`. Then
`b T f - T (b f) = (b - m) T f - T φ₁ - T φ₂` almost everywhere. -/
private theorem exists_smul_sub_eq_sub_sub_sub
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
    {f g : Lp E 2 (volume : Measure (ι → ℝ))}
    (hg : (g : (ι → ℝ) → E) =ᵐ[volume] fun z => b z • f z) {S : Set (ι → ℝ)}
    (hS : MeasurableSet S) (m : ℝ) :
    ∃ φ₁ φ₂ : Lp E 2 (volume : Measure (ι → ℝ)),
      (∀ᵐ z, ‖φ₁ z‖ₑ ≤ S.indicator (fun z => ‖b z - m‖ₑ * ‖f z‖ₑ) z) ∧
      (∀ᵐ z, z ∈ S → φ₂ z = 0) ∧ (∀ᵐ z, ‖φ₂ z‖ₑ ≤ ‖b z - m‖ₑ * ‖f z‖ₑ) ∧
      ∀ᵐ z, b z • T f z - T g z = (b z - m) • T f z - T φ₁ z - T φ₂ z := by
  set h : Lp E 2 (volume : Measure (ι → ℝ)) := g - m • f
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂ : Lp E 2 (volume : Measure (ι → ℝ)), φ₂ =ᵐ[volume] Sᶜ.indicator h :=
    ⟨_, ((Lp.memLp h).indicator hS.compl.nullMeasurableSet).coeFn_toLp⟩
  have hh : ∀ᵐ z ∂volume, h z = (b z - m) • f z := by
    filter_upwards [Lp.coeFn_sub g (m • f), Lp.coeFn_smul m f, hg] with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, sub_smul]
  refine ⟨h - φ₂, φ₂, ?_, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub h φ₂, hφ₂, hh] with z h1 h2 h3
    rw [h1, Pi.sub_apply, h2]
    by_cases hz : z ∈ S
    · rw [indicator_of_notMem (notMem_compl_iff.2 hz), indicator_of_mem hz, sub_zero, h3,
        enorm_smul]
    · rw [indicator_of_mem (mem_compl hz), indicator_of_notMem hz, sub_self, enorm_zero]
  · filter_upwards [hφ₂] with z hz hzS
    rw [hz, indicator_of_notMem (notMem_compl_iff.2 hzS)]
  · filter_upwards [hφ₂, hh] with z h1 h2
    rw [h1]
    refine (enorm_indicator_le_enorm_self _ _).trans_eq ?_
    rw [h2, enorm_smul]
  · -- `g = (h - φ₂) + φ₂ + m f`, and `T` is linear.
    have hTg : T g = T (h - φ₂) + T φ₂ + m • T f := by
      rw [← map_add, sub_add_cancel, ← map_smul, ← map_add, sub_add_cancel]
    have e1 := Lp.coeFn_add (T (h - φ₂) + T φ₂) (m • T f)
    rw [← hTg] at e1
    filter_upwards [e1, Lp.coeFn_add (T (h - φ₂)) (T φ₂), Lp.coeFn_smul m (T f)] with z e1 e2 e3
    rw [e1, Pi.add_apply, e2, e3, Pi.add_apply, Pi.smul_apply, sub_smul]
    abel

variable [CompleteSpace F]

/-- **The sharp maximal function of a commutator with a BMO function.** Let `n ≥ 1`, `1 ≤ u < t`
and `δ > 0`. There is a constant `C`, depending only on `n`, `u`, `t`, `δ`, `A` and `N`, with the
following property. Let `T` be a bounded linear operator on `L²(ℝⁿ)`, `ℝⁿ = ι → ℝ` with the sup
norm, such that

* `T φ x = ∫ K x z (φ z) dz` for almost every `x` in any ball on which `φ` vanishes;
* the kernel satisfies the standard smoothness estimate in its first variable,
  `‖K x y - K x' y‖ ≤ A dist x x' ^ δ dist y x' ^ (-(n + δ))` whenever `dist y x' > 2 dist x x'`;
* `‖T φ‖_u ≤ N ‖φ‖_u` for every `φ ∈ L²` (for `u = 2` this holds with `N = ‖T‖`).

Let `b` be real and locally integrable, and let `f, g ∈ L²` with `g = b f`, so that
`[b, T] f = b T f - T g` is the commutator of `T` with multiplication by `b`. Then at every point
`x`, with `M` the uncentred maximal function,

`([b, T] f)^#(x) ≤ C ‖b‖_{BMO} (M(‖T f‖^t)(x)^{1/t} + M(‖f‖^t)(x)^{1/t})`.

The inequality is in `ℝ≥0∞`; it is informative when `‖b‖_{BMO} < ∞`. -/
theorem exists_sharpMaximalFunction_smul_sub_le [Nonempty ι] {u t δ : ℝ} (hu : 1 ≤ u) (hut : u < t)
    (hδ : 0 < δ) (A N : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 (volume : Measure (ι → ℝ)))
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F},
      (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (φ : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → φ z = 0) → ∀ᵐ x, x ∈ ball y ρ → T φ x = ∫ z, K x z (φ z)) →
      (∀ φ : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T φ) (ENNReal.ofReal u) volume ≤ N * eLpNorm φ (ENNReal.ofReal u) volume) →
      ∀ {b : (ι → ℝ) → ℝ}, LocallyIntegrable b volume →
      ∀ f g : Lp E 2 (volume : Measure (ι → ℝ)), (g : (ι → ℝ) → E) =ᵐ[volume] (fun z => b z • f z) →
      ∀ x, sharpMaximalFunction volume (fun z => b z • T f z - T g z) x ≤
        C * bmoSeminorm b volume *
          (uncenteredMaximalFunction volume (fun z => ‖T f z‖ₑ ^ t) x ^ t⁻¹ +
            uncenteredMaximalFunction volume (fun z => ‖f z‖ₑ ^ t) x ^ t⁻¹) := by
  set n := Fintype.card ι
  have hu0 : 0 < u := one_pos.trans_le hu
  have ht : 1 < t := hu.trans_lt hut
  set t' := t.conjExponent
  have htt : t'.HolderConjugate t := (Real.HolderConjugate.conjExponent ht).symm
  set w := u * (t / u).conjExponent
  have hw0 : 0 < w :=
    mul_pos hu0 (Real.HolderConjugate.conjExponent ((one_lt_div hu0).2 hut)).symm.pos
  set C' := ENNReal.ofReal ((1 + 7 * (⌈t'⌉₊).factorial) *
    (2 ^ (n + 1) / Real.log (3 / 2)) ^ t') ^ t'⁻¹
  have hC' : C' ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 htt.nonneg) ENNReal.ofReal_ne_top
  set C₁ : ℝ≥0∞ := C' + 2 ^ n
  set C₂ : ℝ≥0∞ := (2 ^ n : ℝ≥0∞) ^ u⁻¹ * N * ENNReal.ofReal ((1 + 7 * (⌈w⌉₊).factorial) *
    (2 ^ (n + 1) / Real.log (3 / 2)) ^ w) ^ w⁻¹
  set C₃ : ℝ≥0∞ := A * ∑' k : ℕ, ENNReal.ofReal (4 ^ n * 2 ^ (-((k + 1) * δ))) *
    (C' + (k + 1) * 2 ^ n)
  have hC₁ : C₁ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hC', by simp⟩
  have hC₂ : C₂ ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.coe_ne_top) ?_
    · exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hu0.le) (by simp)
    · exact ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hw0.le) ENNReal.ofReal_ne_top
  have hC₃ : C₃ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top (tsum_ofReal_mul_add_ne_top n hδ hC')
  refine ⟨(2 * (C₁ + C₂ + C₃)).toNNReal, fun T K hKm hK hrep hTu b hb f g hg x => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top (by simp)
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hC₁, hC₂⟩, hC₃⟩))]
  set β := bmoSeminorm b volume
  set M₁ := uncenteredMaximalFunction volume (fun z => ‖T f z‖ₑ ^ t) x ^ t⁻¹
  set M₂ := uncenteredMaximalFunction volume (fun z => ‖f z‖ₑ ^ t) x ^ t⁻¹
  set G : (ι → ℝ) → F := fun z => b z • T f z - T g z
  refine sharpMaximalFunction_le fun c r hx => ?_
  have hr : 0 < r := pos_of_mem_ball hx
  set B := ball c r
  set B2 := ball c (2 * r)
  set m := ⨍ y in B2, b y
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hBtop : volume B ≠ ⊤ := measure_ball_lt_top.ne
  -- Split `(b - m) f` into its parts near `B` and far from it.
  obtain ⟨h₁, h₂, hh₁le, hh₂van, hh₂le, hGdecomp⟩ :=
    exists_smul_sub_eq_sub_sub_sub T hg (measurableSet_ball : MeasurableSet B2) m
  set a : F := -∫ z, K c z (h₂ z)
  -- The far part is nearly constant on `B`.
  have hfar : A * ∫⁻ z in B2ᶜ,
      ENNReal.ofReal (r ^ δ * dist z c ^ (-(n + δ))) * ‖h₂ z‖ₑ ≤ C₃ * β * M₂ := by
    calc A * ∫⁻ z in B2ᶜ, ENNReal.ofReal (r ^ δ * dist z c ^ (-(n + δ))) * ‖h₂ z‖ₑ
        ≤ A * ∫⁻ z in B2ᶜ, ENNReal.ofReal (r ^ δ * dist z c ^ (-(n + δ))) *
            (‖b z - m‖ₑ * ‖f z‖ₑ) := by
          refine mul_le_mul' le_rfl (lintegral_mono_ae ?_)
          filter_upwards [ae_restrict_of_ae hh₂le] with z hz
          gcongr
      _ ≤ A * ((∑' k : ℕ, ENNReal.ofReal (4 ^ n * 2 ^ (-((k + 1) * δ))) *
            (C' + (k + 1) * 2 ^ n)) * β * M₂) := by
          gcongr
          exact setLIntegral_compl_ball_le hb htt (Lp.aestronglyMeasurable f) c hr hδ.le hx
      _ = C₃ * β * M₂ := by simp only [C₃]; ring
  have hpt : ∀ᵐ y ∂volume.restrict B, ‖G y - a‖ₑ ≤
      ‖b y - m‖ₑ * ‖T f y‖ₑ + ‖T h₁ y‖ₑ + C₃ * β * M₂ := by
    filter_upwards [ae_restrict_of_ae hGdecomp, (ae_restrict_iff' measurableSet_ball).2
      (ae_enorm_apply_sub_integral_le T hKm hδ.le hK hrep h₂ c hr hh₂van)] with y hy hfy
    simp only [G]
    rw [hy]
    calc ‖(b y - m) • T f y - T h₁ y - T h₂ y - a‖ₑ
        = ‖(b y - m) • T f y - T h₁ y - (T h₂ y - ∫ z, K c z (h₂ z))‖ₑ := by
          simp only [a]; congr 1; abel
      _ ≤ ‖(b y - m) • T f y‖ₑ + ‖T h₁ y‖ₑ + ‖T h₂ y - ∫ z, K c z (h₂ z)‖ₑ :=
          enorm_sub_le.trans (by gcongr; exact enorm_sub_le)
      _ ≤ _ := by
          rw [enorm_smul]
          gcongr
          exact hfy.trans hfar
  -- The three terms.
  have hI : ⨍⁻ y in B, ‖b y - m‖ₑ * ‖T f y‖ₑ ≤ C₁ * β * M₁ := by
    refine (setLAverage_enorm_sub_mul_le hb htt (Lp.aestronglyMeasurable (T f)).enorm c hr m
      hx).trans ?_
    calc (C' * β + ‖(⨍ y in B, b y) - m‖ₑ) * M₁ ≤ (C' * β + 2 ^ n * β) * M₁ := by
          gcongr
          exact enorm_setAverage_ball_sub_setAverage_ball_two_mul_le hb c hr
      _ = C₁ * β * M₁ := by simp only [C₁]; ring
  have hII : ⨍⁻ y in B, ‖T h₁ y‖ₑ ≤ C₂ * β * M₂ :=
    (setLAverage_enorm_apply_le T hu hut hTu hb (Lp.aestronglyMeasurable f) h₁ c hr hh₁le
      hx).trans_eq (by simp only [C₂]; ring)
  have hmain : ⨍⁻ y in B, ‖G y - a‖ₑ ≤ (C₁ + C₂ + C₃) * β * (M₁ + M₂) := by
    calc ⨍⁻ y in B, ‖G y - a‖ₑ
        ≤ ⨍⁻ y in B, (‖b y - m‖ₑ * ‖T f y‖ₑ + ‖T h₁ y‖ₑ + C₃ * β * M₂) :=
          laverage_mono_ae hpt
      _ = (⨍⁻ y in B, ‖b y - m‖ₑ * ‖T f y‖ₑ) + (⨍⁻ y in B, ‖T h₁ y‖ₑ) + C₃ * β * M₂ := by
          have hF : AEMeasurable (fun y => ‖b y - m‖ₑ * ‖T f y‖ₑ) (volume.restrict B) :=
            ((hb.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.mul
              (Lp.aestronglyMeasurable (T f)).enorm).restrict
          rw [setLAverage_eq, lintegral_add_right _ measurable_const, lintegral_add_left' hF,
            setLIntegral_const, ENNReal.add_div, ENNReal.add_div,
            ENNReal.mul_div_cancel_right hB0 hBtop, ← setLAverage_eq, ← setLAverage_eq]
      _ ≤ C₁ * β * M₁ + C₂ * β * M₂ + C₃ * β * M₂ := by gcongr
      _ ≤ (C₁ + C₂ + C₃) * β * (M₁ + M₂) := by
          have h1 : M₁ ≤ M₁ + M₂ := le_self_add
          have h2 : M₂ ≤ M₁ + M₂ := le_add_self
          calc C₁ * β * M₁ + C₂ * β * M₂ + C₃ * β * M₂
              ≤ C₁ * β * (M₁ + M₂) + C₂ * β * (M₁ + M₂) + C₃ * β * (M₁ + M₂) := by gcongr
            _ = _ := by ring
  have hGm : AEStronglyMeasurable G (volume.restrict B) :=
    ((hb.aestronglyMeasurable.smul (Lp.aestronglyMeasurable (T f))).sub
      (Lp.aestronglyMeasurable (T g))).restrict
  by_cases hGi : IntegrableOn G B
  · calc ⨍⁻ y in B, ‖G y - ⨍ z in B, G z‖ₑ ≤ 2 * ⨍⁻ y in B, ‖G y - a‖ₑ :=
          setLAverage_enorm_sub_setAverage_le hGi a
      _ ≤ 2 * ((C₁ + C₂ + C₃) * β * (M₁ + M₂)) := by gcongr
      _ = _ := by ring
  · rw [setLAverage_enorm_sub_const_eq_top hGm hBtop hGi a, top_le_iff] at hmain
    rw [mul_assoc 2, mul_assoc 2, hmain,
      ENNReal.mul_top two_ne_zero]
    exact le_top

end TauCeti
