/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.BoundedMeanOscillation
public import TauCeti.MeasureTheory.Integral.JohnNirenberg
public import TauCeti.MeasureTheory.Integral.JohnNirenberg.HigherOscillation
public import TauCeti.MeasureTheory.Integral.MaximalFunction
public import TauCeti.MeasureTheory.Integral.SharpMaximalFunction
public import TauCeti.MeasureTheory.Integral.UncenteredMaximalFunction
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.DistRpow

/-!
# The sharp maximal function of a commutator with a function of bounded mean oscillation

Let `T` be a singular integral operator and let `b` have bounded mean oscillation. The
**commutator** of `T` with multiplication by `b` is

`[b, T] f = b T f - T (b f)`.

Coifman, Rochberg and Weiss proved that `[b, T]` is bounded on `Lᵖ` for `1 < p < ∞`, with norm
`O(‖b‖_{BMO})`. This is the perturbative engine of the `W^{1,p}` and `W^{2,p}` theories of elliptic
equations whose coefficients have vanishing mean oscillation: freezing a coefficient `a` at a
point leaves an error that is a commutator `[a, T]` of a Calderón–Zygmund operator with `a`.

This file proves the pointwise estimate on which Janson's and Strömberg's proofs of that theorem
rest: for `1 ≤ s < q < ∞`,

`([b, T] f)^# x ≤ C ‖b‖_{BMO} ((M(‖T f‖^q) x)^{1/q} + (M(‖f‖^q) x)^{1/q})`

at every point `x`, where `^#` is the sharp maximal function and `M` a Hardy–Littlewood maximal
function. The operator `T` is bounded on `L²`, given away from the support of its argument by a
kernel `K` with the standard smoothness estimate in its first variable, and bounded in the `Lˢ`
norm. Calderón–Zygmund operators satisfy the `Lˢ` bound for every `1 < s < q`; the case `s = 1`
requires an additional strong `L¹` bound. The estimate is proved in two settings.

* On `ℝⁿ = ι → ℝ`, `n ≥ 1`, with Lebesgue measure and the sup distance, so that balls are cubes,
  for every locally integrable `b` of bounded mean oscillation, with the centred maximal function
  (`TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`). This is the setting
  of the Fefferman–Stein inequality `TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction`.
* For an additive Haar measure on a finite-dimensional real normed space `V`, for every bounded
  `b`, with the uncentred maximal function and constants independent of `‖b‖_∞`
  (`TauCeti.exists_sharpMaximalFunction_commutator_le`). Here `b` is measured by a bound for its
  `r`-th mean oscillation `(⨍_B |b - b_B|^r)^(1/r)` on every ball, where `r⁻¹ + q⁻¹ = s⁻¹`; on
  Euclidean space, with its round balls, the `Lᵖ` form of the John–Nirenberg inequality bounds it
  by a multiple of `‖b‖_{BMO}` (`TauCeti.exists_sharpMaximalFunction_commutator_le_bmoSeminorm`).

## The proof

Fix a ball `B = B(c, r)` containing `x`, let `2B = B(c, 2 r)` and `a = b_{2B}`. Split
`(b - a) f = h₁ + h₂` with `h₁` supported on `2B` and `h₂` vanishing there. Then

`[b, T] f = (b - a) T f - T h₁ - T h₂`,

and the three terms are compared with the constant `-∫ K c z (h₂ z) dz` on `B`.

* `(b - a) T f`: by Hölder's inequality, `⨍_B |b - a| ‖T f‖` is at most the `L^{q'}` mean
  oscillation of `b`, which the John–Nirenberg inequality bounds by `‖b‖_{BMO}`
  (`TauCeti.setLAverage_enorm_sub_setAverage_rpow_le_of_bmoSeminorm_le`), times the `L^q` average of
  `T f`, which the maximal function bounds.
* `T h₁`: by Hölder's inequality and the `Lˢ` bound,
  `⨍_B ‖T h₁‖ ≤ A |B|^{-1/s} ‖(b - a) f‖_{Lˢ(2B)}`, and the same Hölder and John–Nirenberg
  argument bounds the right-hand side.
* `T h₂`: for almost every `y ∈ B`, `‖T h₂ y - ∫ K c z (h₂ z) dz‖` is at most
  `∫ ‖K y z - K c z‖ ‖h₂ z‖ dz`.
  On the dyadic annuli around `2B` the kernel difference decays like `2^(-kδ)` relative to the
  measure of the enclosing ball, while the averages of `b` over the dyadic balls drift from `b_{2B}`
  only linearly in `k` (`TauCeti.enorm_setAverage_ball_two_pow_mul_sub_le`). The sum over `k`
  converges.

Integrating this estimate, with the `Lᵖ` bounds for the maximal function for `q < p`, leads to the
Coifman–Rochberg–Weiss theorem. The Fefferman–Stein inequality available here
(`TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction`) assumes that its argument is integrable, which
is not known a priori for `[b, T] f`; completing the argument requires a suitable a priori version
of that inequality together with an approximation or truncation argument.

## Main declarations

* `TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`: the sharp maximal
  function estimate for `[b, T] f` on `ι → ℝ`.
* `TauCeti.exists_sharpMaximalFunction_commutator_le`: the estimate for an additive Haar measure on
  a finite-dimensional normed space and a bounded `b`, in terms of a uniform bound on a
  higher-order mean oscillation of `b` on balls.
* `TauCeti.exists_sharpMaximalFunction_commutator_le_bmoSeminorm`: the estimate in terms of
  `‖b‖_{BMO}` on Euclidean space.

## References

* R. R. Coifman, R. Rochberg, G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. **103** (1976), 611–635.
* S. Janson, *Mean oscillation and commutators of singular integral operators*, Ark. Mat. **16**
  (1978), 263–270.
* J.-O. Strömberg, *Bounded mean oscillation with Orlicz norms and duality of Hardy spaces*,
  Indiana Univ. Math. J. **28** (1979), 511–544.
* L. Grafakos, *Modern Fourier Analysis*, Section 3.5.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace TauCeti

section Pi

variable {ι : Type*} [Fintype ι] [Nonempty ι] {E G : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup G]

/-- The arithmetic of the dyadic annuli: `C r^δ (2^(k+1) r)^(-(n+δ)) (2 · 2^(k+2) r)ⁿ = C 4ⁿ
(2^(-δ))^(k+1)`. -/
private theorem mul_rpow_mul_rpow_neg_mul_pow_eq (C : ℝ) (n k : ℕ) {r δ : ℝ} (hr : 0 < r) :
    C * r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ)) * (2 * (2 ^ (k + 2) * r)) ^ n =
      C * 4 ^ n * (2 ^ (-δ)) ^ (k + 1) := by
  set u : ℝ := 2 ^ (k + 1) * r
  have hu : 0 < u := by positivity
  have h4 : 2 * (2 ^ (k + 2) * r) = 4 * u := by simp only [u]; ring
  have hru : r = u * (2 ^ (k + 1))⁻¹ := by simp only [u]; field_simp
  rw [h4, mul_pow, Real.rpow_neg hu.le, Real.rpow_add hu, hru,
    Real.mul_rpow hu.le (by positivity), Real.inv_rpow (by positivity), ← Real.rpow_natCast u n,
    ← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul zero_le_two, Real.rpow_neg zero_le_two,
    ← Real.rpow_natCast (2 ^ δ)⁻¹ (k + 1), Real.inv_rpow (by positivity),
    ← Real.rpow_mul zero_le_two,
    mul_comm δ]
  field_simp

/-- **The local part.** Let `T` be bounded in the `Lˢ` norm with constant `A`, and let `h ∈ L²` be
`(b - b_{2B}) f` on the ball `2B = B(c, 2 r)` and zero off it. Then for `x ∈ B = B(c, r)` and
`s < q`,

`∫_B ‖T h‖ ≤ A C 2^{n/q} 2^{n/s} ‖b‖_{BMO} |B| (M(‖f‖^q) x)^{1/q}`,

by Hölder's inequality on `B`, the `Lˢ` bound, and the John–Nirenberg estimate on `2B`. -/
private theorem setLIntegral_enorm_apply_le_of_eLpNorm_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {s q : ℝ} (hs : 1 ≤ s) (hsq : s < q) {A : ℝ≥0}
    (hT : ∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
      eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume)
    {b : (ι → ℝ) → ℝ} (hb : LocallyIntegrable b volume) {M : ℝ≥0}
    (hM : bmoSeminorm b volume ≤ M) {f : (ι → ℝ) → E} (hf : AEStronglyMeasurable f volume)
    {h : Lp E 2 (volume : Measure (ι → ℝ))} {c x : ι → ℝ} {r : ℝ} (hx : x ∈ ball c r)
    (hh : h =ᵐ[volume] (ball c (2 * r)).indicator
      (fun y => (b y - ⨍ z in ball c (2 * r), b z) • f y)) :
    ∫⁻ y in ball c r, ‖T h y‖ₑ ≤
      A * bmoHolderConst (Fintype.card ι) s q * (2 ^ Fintype.card ι : ℝ≥0∞) ^ q⁻¹ *
        (2 ^ Fintype.card ι : ℝ≥0∞) ^ s⁻¹ * M * volume (ball c r) *
          maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹ := by
  set n := Fintype.card ι
  set B := ball c r
  set B₁ := ball c (2 * r)
  set a := ⨍ z in B₁, b z
  set Mf := maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x
  have hr : 0 < r := pos_of_mem_ball hx
  have hs0 : 0 < s := one_pos.trans_le hs
  have hsR : (ENNReal.ofReal s).toReal = s := ENNReal.toReal_ofReal hs0.le
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hBtop : volume B ≠ ∞ := measure_ball_lt_top.ne
  have hxB₁ : x ∈ B₁ := ball_subset_ball (by linarith) hx
  have hφ : AEStronglyMeasurable (fun y => (b y - a) • f y) (volume.restrict B₁) :=
    ((hb.aestronglyMeasurable.sub aestronglyMeasurable_const).smul hf).restrict
  -- The `Lˢ` norm of `h` is that of `(b - a) f` on `B₁`, bounded by the John–Nirenberg estimate.
  have hint := setLIntegral_enorm_sub_mul_enorm_rpow_le hb hM hf hs hsq hxB₁ (a := a)
    (κ := 0) (by simp [a, B₁])
  have hh_norm : eLpNorm h (ENNReal.ofReal s) volume ≤
      bmoHolderConst n s q * M * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * volume B₁ ^ s⁻¹ * Mf ^ q⁻¹ := by
    rw [eLpNorm_congr_ae hh,
      eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball.nullMeasurableSet,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hφ, hsR]
    simp_rw [enorm_smul]
    calc (∫⁻ y in B₁, (‖b y - a‖ₑ * ‖f y‖ₑ) ^ s) ^ (1 / s)
        ≤ (((bmoHolderConst n s q + 0) * M) ^ s * (2 ^ n : ℝ≥0∞) ^ (s / q) * volume B₁ *
            Mf ^ (s / q)) ^ (1 / s) := by
          gcongr
      _ = bmoHolderConst n s q * M * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * volume B₁ ^ s⁻¹ * Mf ^ q⁻¹ := by
          have hsq' : s / q * (1 / s) = q⁻¹ := by field_simp
          rw [add_zero, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_one_div_cancel hs0.ne', ENNReal.rpow_one, hsq', one_div]
  -- Hölder's inequality on `B` and the `Lˢ` bound for `T`.
  have hloc : ∫⁻ y in B, ‖T h y‖ₑ ≤
      A * eLpNorm h (ENNReal.ofReal s) volume * volume B ^ (1 - s⁻¹) := by
    calc ∫⁻ y in B, ‖T h y‖ₑ = eLpNorm (T h) 1 (volume.restrict B) :=
          (eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable _).restrict).symm
      _ ≤ eLpNorm (T h) (ENNReal.ofReal s) (volume.restrict B) *
            (volume.restrict B) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal s).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by simpa using hs)
            (Lp.aestronglyMeasurable _).restrict
      _ ≤ eLpNorm (T h) (ENNReal.ofReal s) volume * volume B ^ (1 - s⁻¹) := by
          rw [Measure.restrict_apply_univ, hsR, ENNReal.toReal_one, div_one, one_div]
          exact mul_le_mul_left (eLpNorm_restrict_le _ _ _ _) _
      _ ≤ A * eLpNorm h (ENNReal.ofReal s) volume * volume B ^ (1 - s⁻¹) := by gcongr; exact hT h
  have hB₁ : volume B₁ = 2 ^ n * volume B := by
    simp only [B₁, B]
    rw [volume.addHaar_ball_mul_of_pos c two_pos, volume.addHaar_ball_center c,
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat, Module.finrank_fintype_fun_eq_card]
  calc ∫⁻ y in B, ‖T h y‖ₑ
      ≤ A * (bmoHolderConst n s q * M * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * volume B₁ ^ s⁻¹ * Mf ^ q⁻¹) *
          volume B ^ (1 - s⁻¹) := hloc.trans (by gcongr)
    _ = A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (2 ^ n : ℝ≥0∞) ^ s⁻¹ * M *
          (volume B ^ s⁻¹ * volume B ^ (1 - s⁻¹)) * Mf ^ q⁻¹ := by
        rw [hB₁, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
        ring
    _ = A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (2 ^ n : ℝ≥0∞) ^ s⁻¹ * M * volume B *
          Mf ^ q⁻¹ := by
        rw [← ENNReal.rpow_add _ _ hB0 hBtop, add_sub_cancel, ENNReal.rpow_one]

/-- The constant of the far part, `TauCeti.lintegral_enorm_sub_apply_le`: a sum over the dyadic
annuli `2^(k+1) r ≤ dist z c < 2^(k+2) r`, convergent since `2^(-δ) < 1`. -/
private noncomputable def farConst (n : ℕ) (q : ℝ) (C₀ : ℝ≥0) (δ : ℝ) : ℝ≥0∞ :=
  (∑' k : ℕ, ENNReal.ofReal (C₀ * 4 ^ n * (2 ^ (-δ)) ^ (k + 1)) *
    (bmoHolderConst n 1 q + ((k + 2 : ℕ) + 1) * 2 ^ n)) * (2 ^ n : ℝ≥0∞) ^ q⁻¹

private theorem farConst_ne_top (n : ℕ) {q : ℝ} (hq : 1 < q) (C₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    farConst n q C₀ δ ≠ ∞ := by
  set D := (bmoHolderConst n 1 q).toReal
  have hD : bmoHolderConst n 1 q = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal (bmoHolderConst_ne_top n one_pos hq)).symm
  set ρ : ℝ := 2 ^ (-δ)
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos hδ)
  set u : ℕ → ℝ := fun k => C₀ * 4 ^ n * ρ ^ (k + 1) * (D + ((k + 2 : ℕ) + 1) * 2 ^ n)
  have hu0 : ∀ k, 0 ≤ u k := fun k => by positivity
  have hu : Summable u := by
    have h1 : Summable fun k : ℕ => ρ ^ k := summable_geometric_of_lt_one hρ0 hρ1
    have h2 : Summable fun k : ℕ => (k : ℝ) ^ 1 * ρ ^ k :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hρ0])
    refine ((h1.mul_left (C₀ * 4 ^ n * ρ * (D + 3 * 2 ^ n))).add
      (h2.mul_left (C₀ * 4 ^ n * ρ * 2 ^ n))).congr fun k => ?_
    simp only [u]
    push_cast
    ring
  have hsum : ∑' k : ℕ, ENNReal.ofReal (C₀ * 4 ^ n * ρ ^ (k + 1)) *
      (bmoHolderConst n 1 q + ((k + 2 : ℕ) + 1) * 2 ^ n) = ENNReal.ofReal (∑' k, u k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hu0 hu]
    refine tsum_congr fun k => ?_
    simp only [u]
    rw [hD, ENNReal.ofReal_mul (p := (C₀ : ℝ) * 4 ^ n * ρ ^ (k + 1)) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (p := ((k + 2 : ℕ) : ℝ) + 1) (by positivity),
      ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one,
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  rw [farConst, hsum]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))

/-- **The far part.** Let `K` satisfy the standard smoothness estimate in its first variable, and
let `h` be `(b - b_{2B}) f` off the ball `2B = B(c, 2 r)` and zero on it. For `x, y ∈ B(c, r)`,

`∫ ‖(K y z - K c z) (h z)‖ dz ≤ C ‖b‖_{BMO} (M(‖f‖^q) x)^{1/q}`.

Off `2B`, the kernel difference is at most `C₀ r^δ dist z c^(-(n+δ))`. On the annulus
`2^(k+1) r ≤ dist z c < 2^(k+2) r` this is `C₀ 4ⁿ 2^(-(k+1)δ) / |B(c, 2^(k+2) r)|`, while the
average of `|b - b_{2B}| ‖f‖` over `B(c, 2^(k+2) r)` grows only linearly in `k`. -/
private theorem lintegral_enorm_sub_apply_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} {C₀ : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ))))
    {b : (ι → ℝ) → ℝ} (hb : LocallyIntegrable b volume) {M : ℝ≥0}
    (hM : bmoSeminorm b volume ≤ M) {q : ℝ} (hq : 1 < q) {f : (ι → ℝ) → E}
    (hf : AEStronglyMeasurable f volume) {c x y : ι → ℝ} {r : ℝ} (hx : x ∈ ball c r)
    (hy : y ∈ ball c r) {h : (ι → ℝ) → E}
    (hh : h =ᵐ[volume] (ball c (2 * r))ᶜ.indicator
      (fun z => (b z - ⨍ w in ball c (2 * r), b w) • f z)) :
    ∫⁻ z, ‖(K y z - K c z) (h z)‖ₑ ≤
      farConst (Fintype.card ι) q C₀ δ * M *
        maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹ := by
  set n := Fintype.card ι
  set a := ⨍ w in ball c (2 * r), b w
  set g : (ι → ℝ) → ℝ≥0∞ := fun z => ‖b z - a‖ₑ * ‖f z‖ₑ
  set Mf := maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x
  set c' : ℕ → ℝ := fun k => C₀ * r ^ δ * (2 ^ (k + 1) * r) ^ (-(n + δ))
  have hr : 0 < r := pos_of_mem_ball hx
  have hgm : AEMeasurable g volume :=
    (hb.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.mul hf.enorm
  -- Pointwise domination by a sum over the dyadic annuli.
  have hpt : ∀ᵐ z, ‖(K y z - K c z) (h z)‖ₑ ≤
      ∑' k : ℕ, ENNReal.ofReal (c' k) * (ball c (2 ^ (k + 2) * r)).indicator g z := by
    filter_upwards [hh] with z hz
    rw [hz]
    by_cases hzB : z ∈ ball c (2 * r)
    · simp [hzB]
    have hd : 2 * r ≤ dist z c := not_lt.1 hzB
    have hyc : dist y c < r := hy
    rw [indicator_of_mem (mem_compl hzB)]
    calc ‖(K y z - K c z) ((b z - a) • f z)‖ₑ
        ≤ ‖K y z - K c z‖ₑ * g z := by
          simpa only [g, enorm_smul] using
            ContinuousLinearMap.le_opENorm (K y z - K c z) ((b z - a) • f z)
      _ ≤ ENNReal.ofReal (C₀ * r ^ δ) * ENNReal.ofReal (dist z c ^ (-(n + δ))) * g z := by
          gcongr
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ((hK y c z (by linarith)).trans ?_)
          rw [← mul_assoc]
          gcongr
      _ ≤ ENNReal.ofReal (C₀ * r ^ δ) * (∑' k : ℕ, (ball c (2 ^ (k + 2) * r)).indicator
            (fun _ => ENNReal.ofReal ((2 ^ (k + 1) * r) ^ (-(n + δ)))) z) * g z := by
          gcongr
          exact ofReal_dist_rpow_neg_le_tsum hr (by positivity) hd
      _ = ∑' k : ℕ, ENNReal.ofReal (c' k) * (ball c (2 ^ (k + 2) * r)).indicator g z := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
          refine tsum_congr fun k => ?_
          by_cases hzk : z ∈ ball c (2 ^ (k + 2) * r)
          · simp only [indicator_of_mem hzk, c']
            rw [ENNReal.ofReal_mul (p := (C₀ : ℝ) * r ^ δ) (by positivity)]
          · simp [indicator_of_notMem hzk]
  -- Each annulus contributes `C₀ 4ⁿ 2^(-(k+1)δ)` times the bound on `2^(k+2) B`.
  have hk : ∀ k : ℕ, ENNReal.ofReal (c' k) * ∫⁻ z in ball c (2 ^ (k + 2) * r), g z ≤
      ENNReal.ofReal (C₀ * 4 ^ n * (2 ^ (-δ)) ^ (k + 1)) *
        (bmoHolderConst n 1 q + ((k + 2 : ℕ) + 1) * 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ *
          (M * Mf ^ q⁻¹) := by
    intro k
    have hxk : x ∈ ball c (2 ^ (k + 2) * r) :=
      ball_subset_ball (le_mul_of_one_le_left hr.le (one_le_pow₀ one_le_two)) hx
    have hak : ‖(⨍ y in ball c (2 ^ (k + 2) * r), b y) - a‖ₑ ≤
        ((k + 2 : ℕ) + 1) * 2 ^ n * M := by
      refine (enorm_setAverage_ball_sub_setAverage_ball_le hb.aestronglyMeasurable c hr
        (k + 2)).trans ?_
      rw [Module.finrank_fintype_fun_eq_card]
      gcongr
    calc ENNReal.ofReal (c' k) * ∫⁻ z in ball c (2 ^ (k + 2) * r), g z
        ≤ ENNReal.ofReal (c' k) * ((bmoHolderConst n 1 q + ((k + 2 : ℕ) + 1) * 2 ^ n) * M *
            (2 ^ n : ℝ≥0∞) ^ q⁻¹ * volume (ball c (2 ^ (k + 2) * r)) * Mf ^ q⁻¹) := by
          gcongr
          exact setLIntegral_enorm_sub_mul_enorm_le hb hM hf hq hxk hak
      _ = ENNReal.ofReal (c' k * (2 * (2 ^ (k + 2) * r)) ^ n) *
            (bmoHolderConst n 1 q + ((k + 2 : ℕ) + 1) * 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ *
              (M * Mf ^ q⁻¹) := by
          rw [Real.volume_pi_ball c (by positivity), ENNReal.ofReal_mul (p := c' k) (by positivity)]
          ring
      _ = _ := by
          simp only [c']
          rw [mul_rpow_mul_rpow_neg_mul_pow_eq _ _ _ hr]
  calc ∫⁻ z, ‖(K y z - K c z) (h z)‖ₑ
      ≤ ∫⁻ z, ∑' k : ℕ, ENNReal.ofReal (c' k) * (ball c (2 ^ (k + 2) * r)).indicator g z :=
        lintegral_mono_ae hpt
    _ = ∑' k : ℕ, ENNReal.ofReal (c' k) * ∫⁻ z in ball c (2 ^ (k + 2) * r), g z := by
        rw [lintegral_tsum fun k => (hgm.indicator measurableSet_ball).const_mul _]
        refine tsum_congr fun k => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_ball]
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (C₀ * 4 ^ n * (2 ^ (-δ)) ^ (k + 1)) *
          (bmoHolderConst n 1 q + ((k + 2 : ℕ) + 1) * 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ *
            (M * Mf ^ q⁻¹) :=
        tsum_le_tsum hk
    _ = farConst n q C₀ δ * M * Mf ^ q⁻¹ := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, farConst]
        ring

/-- The constant of the commutator estimate, the sum of the constants of its three parts. -/
private noncomputable def commutatorConst (n : ℕ) (s q : ℝ) (A C₀ : ℝ≥0) (δ : ℝ) : ℝ≥0∞ :=
  (bmoHolderConst n 1 q + 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ +
    A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (2 ^ n : ℝ≥0∞) ^ s⁻¹ + farConst n q C₀ δ

private theorem commutatorConst_ne_top (n : ℕ) {s q : ℝ} (hs : 1 ≤ s) (hsq : s < q)
    (A C₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) : commutatorConst n s q A C₀ δ ≠ ∞ := by
  have hq : 1 < q := hs.trans_lt hsq
  have h2 : ∀ e : ℝ, 0 ≤ e → (2 ^ n : ℝ≥0∞) ^ e ≠ ∞ := fun e he =>
    ENNReal.rpow_ne_top_of_nonneg he (by simp)
  have hq0 : 0 ≤ q⁻¹ := by positivity
  have hs0 : 0 ≤ s⁻¹ := by positivity
  unfold commutatorConst
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top
    (ENNReal.add_ne_top.2 ⟨bmoHolderConst_ne_top n one_pos hq, by simp⟩) (h2 _ hq0), ?_⟩,
    farConst_ne_top n hq C₀ hδ⟩
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (bmoHolderConst_ne_top n (one_pos.trans_le hs) hsq)) (h2 _ hq0)) (h2 _ hs0)

/-- **The commutator estimate on one ball**, with an explicit constant. -/
private theorem setLAverage_enorm_smul_sub_sub_setAverage_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F} (hKm : ∀ x, AEStronglyMeasurable (K x) volume)
    {C₀ : ℝ≥0} {δ : ℝ} (hδ : 0 < δ)
    (hK : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ))))
    (hrep : ∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
      (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z))
    {s q : ℝ} (hs : 1 ≤ s) (hsq : s < q) {A : ℝ≥0}
    (hT : ∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
      eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume)
    {b : (ι → ℝ) → ℝ} (hb : LocallyIntegrable b volume) {M : ℝ≥0}
    (hM : bmoSeminorm b volume ≤ M) (f g : Lp E 2 (volume : Measure (ι → ℝ)))
    (hg : g =ᵐ[volume] fun y => b y • f y) {c x : ι → ℝ} {r : ℝ} (hx : x ∈ ball c r) :
    ⨍⁻ y in ball c r, ‖(b y • T f y - T g y) - ⨍ z in ball c r, (b z • T f z - T g z)‖ₑ ≤
      2 * commutatorConst (Fintype.card ι) s q A C₀ δ * M *
        (maximalFunction volume (fun y => ‖T f y‖ₑ ^ q) x ^ q⁻¹ +
          maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹) := by
  set n := Fintype.card ι
  set B := ball c r
  set B₁ := ball c (2 * r)
  set a := ⨍ z in B₁, b z
  set X := maximalFunction volume (fun y => ‖T f y‖ₑ ^ q) x
  set Y := maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x
  set Φ : (ι → ℝ) → F := fun y => b y • T f y - T g y
  have hq : 1 < q := hs.trans_lt hsq
  have hr : 0 < r := pos_of_mem_ball hx
  have hB0 : volume B ≠ 0 := (measure_ball_pos volume c hr).ne'
  have hBtop : volume B ≠ ∞ := measure_ball_lt_top.ne
  -- Split `g - a f = (b - a) f` into its parts `h₁` on `B₁` and `h₂` off `B₁`.
  set φ : Lp E 2 (volume : Measure (ι → ℝ)) := g - a • f
  have hφ : ⇑φ =ᵐ[volume] fun y => (b y - a) • f y := by
    filter_upwards [Lp.coeFn_sub g (a • f), Lp.coeFn_smul a f, hg] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, sub_smul]
  set h₁ : Lp E 2 (volume : Measure (ι → ℝ)) :=
    ((Lp.memLp φ).indicator measurableSet_ball.nullMeasurableSet (s := B₁)).toLp _
  set h₂ := φ - h₁
  have hh₁ : ⇑h₁ =ᵐ[volume] B₁.indicator fun y => (b y - a) • f y := by
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp φ).indicator
      measurableSet_ball.nullMeasurableSet (s := B₁)), hφ] with y h1 h2
    rw [h1]
    by_cases hy : y ∈ B₁ <;> simp [hy, h2]
  have hh₂ : ⇑h₂ =ᵐ[volume] B₁ᶜ.indicator fun y => (b y - a) • f y := by
    filter_upwards [Lp.coeFn_sub φ h₁, hh₁, hφ] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    by_cases hy : y ∈ B₁ <;> simp [hy]
  -- `T g = T h₁ + T h₂ + a T f`.
  have hTg : ∀ᵐ y, T g y = T h₁ y + T h₂ y + a • T f y := by
    have hgφ : g = h₁ + h₂ + a • f := by
      simp only [h₂, φ, add_sub_cancel, sub_add_cancel]
    filter_upwards [Lp.coeFn_add (T h₁ + T h₂) (a • T f), Lp.coeFn_add (T h₁) (T h₂),
      Lp.coeFn_smul a (T f)] with y h1 h2 h3
    rw [hgφ, map_add, map_add, map_smul, h1, Pi.add_apply, h2, Pi.add_apply, h3, Pi.smul_apply]
  -- Off `B₁` the operator is given by the kernel.
  have hrep₂ : ∀ᵐ y, y ∈ B₁ → T h₂ y = ∫ z, K y z (h₂ z) := hrep h₂ c (2 * r) (by
    filter_upwards [hh₂] with z hz hzB
    rw [hz, indicator_of_notMem (notMem_compl_iff.2 hzB)])
  set A₀ : F := ∫ z, K c z (h₂ z)
  -- The pointwise bound on `B`.
  have hpt : ∀ᵐ y ∂volume.restrict B, ‖Φ y - (-A₀)‖ₑ ≤
      ‖b y - a‖ₑ * ‖T f y‖ₑ + ‖T h₁ y‖ₑ + farConst n q C₀ δ * M * Y ^ q⁻¹ := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hTg, hrep₂] with y h1 h2 hyB
    have hfar : ‖T h₂ y - A₀‖ₑ ≤ farConst n q C₀ δ * M * Y ^ q⁻¹ := by
      rw [h2 (ball_subset_ball (by linarith) hyB)]
      refine (MeasureTheory.enorm_integral_sub_integral_le_lintegral_enorm_sub
        ((ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable h₂)
          (hKm y))
        ((ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable h₂)
          (hKm c))).trans ?_
      simpa only [ContinuousLinearMap.apply_apply, sub_apply] using
        lintegral_enorm_sub_apply_le hδ hK hb hM hq (Lp.aestronglyMeasurable f) hx hyB hh₂
    have heq : Φ y - (-A₀) = (b y - a) • T f y - T h₁ y - (T h₂ y - A₀) := by
      simp only [Φ, h1, sub_smul]
      abel
    rw [heq]
    calc ‖(b y - a) • T f y - T h₁ y - (T h₂ y - A₀)‖ₑ
        ≤ ‖(b y - a) • T f y - T h₁ y‖ₑ + ‖T h₂ y - A₀‖ₑ := enorm_sub_le
      _ ≤ ‖(b y - a) • T f y‖ₑ + ‖T h₁ y‖ₑ + ‖T h₂ y - A₀‖ₑ := by gcongr; exact enorm_sub_le
      _ ≤ _ := by rw [enorm_smul]; gcongr
  -- The three parts.
  have hI : ∫⁻ y in B, ‖b y - a‖ₑ * ‖T f y‖ₑ ≤
      (bmoHolderConst n 1 q + 2 ^ n) * M * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * volume B * X ^ q⁻¹ := by
    refine setLIntegral_enorm_sub_mul_enorm_le hb hM (Lp.aestronglyMeasurable _) hq hx ?_
    have h0 := enorm_setAverage_ball_sub_setAverage_ball_le hb.aestronglyMeasurable c hr 0
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add,
      Module.finrank_fintype_fun_eq_card] at h0
    exact h0.trans (by gcongr)
  have hII := setLIntegral_enorm_apply_le_of_eLpNorm_le T hs hsq hT hb hM
    (Lp.aestronglyMeasurable f) hx hh₁
  have hbm : AEMeasurable (fun y => ‖b y - a‖ₑ * ‖T f y‖ₑ) (volume.restrict B) :=
    ((hb.aestronglyMeasurable.sub aestronglyMeasurable_const).enorm.mul
      (Lp.aestronglyMeasurable _).enorm).restrict
  have hosc : ⨍⁻ y in B, ‖Φ y - (-A₀)‖ₑ ≤
      commutatorConst n s q A C₀ δ * M * (X ^ q⁻¹ + Y ^ q⁻¹) := by
    rw [setLAverage_eq, ENNReal.div_le_iff hB0 hBtop]
    calc ∫⁻ y in B, ‖Φ y - (-A₀)‖ₑ
        ≤ ∫⁻ y in B, (‖b y - a‖ₑ * ‖T f y‖ₑ + ‖T h₁ y‖ₑ + farConst n q C₀ δ * M * Y ^ q⁻¹) :=
          lintegral_mono_ae hpt
      _ = (∫⁻ y in B, ‖b y - a‖ₑ * ‖T f y‖ₑ) + (∫⁻ y in B, ‖T h₁ y‖ₑ) +
            farConst n q C₀ δ * M * Y ^ q⁻¹ * volume B := by
          rw [lintegral_add_left' (f := fun y => ‖b y - a‖ₑ * ‖T f y‖ₑ + ‖T h₁ y‖ₑ)
            (hbm.add (Lp.aestronglyMeasurable _).enorm.restrict), lintegral_add_left' hbm,
            setLIntegral_const]
      _ ≤ (bmoHolderConst n 1 q + 2 ^ n) * M * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * volume B * X ^ q⁻¹ +
            A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (2 ^ n : ℝ≥0∞) ^ s⁻¹ * M * volume B *
              Y ^ q⁻¹ + farConst n q C₀ δ * M * Y ^ q⁻¹ * volume B := by
          gcongr
      _ ≤ commutatorConst n s q A C₀ δ * M * (X ^ q⁻¹ + Y ^ q⁻¹) * volume B := by
          unfold commutatorConst
          have h1 : (bmoHolderConst n 1 q + 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * X ^ q⁻¹ ≤
              (bmoHolderConst n 1 q + 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (X ^ q⁻¹ + Y ^ q⁻¹) := by
            gcongr; exact le_self_add
          have h2 : (A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (2 ^ n : ℝ≥0∞) ^ s⁻¹ +
              farConst n q C₀ δ) * Y ^ q⁻¹ ≤ (A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ *
                (2 ^ n : ℝ≥0∞) ^ s⁻¹ + farConst n q C₀ δ) * (X ^ q⁻¹ + Y ^ q⁻¹) := by
            gcongr; exact le_add_self
          calc _ = ((bmoHolderConst n 1 q + 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * X ^ q⁻¹ +
                (A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (2 ^ n : ℝ≥0∞) ^ s⁻¹ +
                  farConst n q C₀ δ) * Y ^ q⁻¹) * M * volume B := by ring
            _ ≤ ((bmoHolderConst n 1 q + 2 ^ n) * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (X ^ q⁻¹ + Y ^ q⁻¹) +
                (A * bmoHolderConst n s q * (2 ^ n : ℝ≥0∞) ^ q⁻¹ * (2 ^ n : ℝ≥0∞) ^ s⁻¹ +
                  farConst n q C₀ δ) * (X ^ q⁻¹ + Y ^ q⁻¹)) * M * volume B := by gcongr
            _ = _ := by ring
  -- Comparing with the constant `-A₀` bounds the mean oscillation.
  set R := commutatorConst n s q A C₀ δ * M * (X ^ q⁻¹ + Y ^ q⁻¹)
  suffices h : ⨍⁻ y in B, ‖Φ y - ⨍ z in B, Φ z‖ₑ ≤ 2 * R by
    refine h.trans_eq ?_
    simp only [R]
    ring
  rcases eq_or_ne R ∞ with hR | hR
  · rw [hR, ENNReal.mul_top two_ne_zero]
    exact le_top
  have hint : IntegrableOn Φ B := by
    have hfin : ∫⁻ y in B, ‖Φ y - (-A₀)‖ₑ < ∞ := by
      rw [← measure_mul_setLAverage _ hBtop]
      exact ENNReal.mul_lt_top hBtop.lt_top (hosc.trans_lt hR.lt_top)
    have hΦm : AEStronglyMeasurable Φ (volume.restrict B) :=
      ((hb.aestronglyMeasurable.smul (Lp.aestronglyMeasurable _)).sub
        (Lp.aestronglyMeasurable _)).restrict
    have : IntegrableOn (fun y => Φ y - (-A₀)) B := ⟨hΦm.sub aestronglyMeasurable_const, hfin⟩
    refine (this.add (integrableOn_const hBtop : IntegrableOn (fun _ => -A₀) B)).congr_fun
      (fun y _ => ?_) measurableSet_ball
    simp
  calc ⨍⁻ y in B, ‖Φ y - ⨍ z in B, Φ z‖ₑ ≤ 2 * ⨍⁻ y in B, ‖Φ y - (-A₀)‖ₑ :=
        setLAverage_enorm_sub_setAverage_le hint _
    _ ≤ 2 * R := by gcongr

/-- **The sharp maximal function of a commutator with a BMO function.** Let `1 ≤ s < q`, `δ > 0`,
and let `A`, `C₀` be constants. There is a constant `C`, depending only on these and the
dimension `n ≥ 1`, with the following property on `ℝⁿ = ι → ℝ` with the sup distance.

Let `T` be a bounded linear operator on `L²` such that `T h x = ∫ K x z (h z) dz` for almost every
`x` in any ball on which `h` vanishes, where the kernel satisfies the standard smoothness estimate
in its first variable,

`‖K x y - K x' y‖ ≤ C₀ dist x x' ^ δ dist y x' ^ (-(n + δ))` whenever `dist y x' > 2 dist x x'`,

and such that `‖T h‖_s ≤ A ‖h‖_s` for `h ∈ L²`. Let `b` be locally integrable with
`‖b‖_{BMO} ≤ M`, and let `f, g ∈ L²` with `g = b f`. Then the commutator
`[b, T] f = b T f - T (b f)` satisfies, at every point `x`,

`([b, T] f)^# x ≤ C M ((M(‖T f‖^q) x)^{1/q} + (M(‖f‖^q) x)^{1/q})`,

where `^#` is the sharp maximal function and `M` the centred Hardy–Littlewood maximal function.

Calderón–Zygmund operators with a standard kernel satisfy the hypotheses for `1 < s < q`, with the
`Lˢ` bound supplied by the Calderón–Zygmund theorem; the case `s = 1` requires an additional strong
`L¹` bound. Combined with an a priori form of the Fefferman–Stein inequality, an approximation
argument and the `Lᵖ` bounds for the maximal function, this is the route to the
Coifman–Rochberg–Weiss theorem that `[b, T]` is bounded on `Lᵖ`, `1 < p < ∞`, with norm
`O(‖b‖_{BMO})`. -/
theorem exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s q : ℝ} (hs : 1 ≤ s)
    (hsq : s < q) (A C₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, LocallyIntegrable b volume → bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))), g =ᵐ[volume] (fun y => b y • f y) →
      ∀ x, sharpMaximalFunction volume (fun y => b y • T f y - T g y) x ≤
        C * M * (maximalFunction volume (fun y => ‖T f y‖ₑ ^ q) x ^ q⁻¹ +
          maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹) := by
  have hC := ENNReal.mul_ne_top (by simp : (2 : ℝ≥0∞) ≠ ∞)
    (commutatorConst_ne_top (Fintype.card ι) hs hsq A C₀ hδ)
  refine ⟨(2 * commutatorConst (Fintype.card ι) s q A C₀ δ).toNNReal,
    fun T K hKm hK hrep hT b M hb hM f g hg x => sharpMaximalFunction_le fun c r hx => ?_⟩
  rw [ENNReal.coe_toNNReal hC]
  exact setLAverage_enorm_smul_sub_sub_setAverage_le T hKm hδ hK hrep hs hsq hT hb hM f g hg hx

end Pi

open Module

section General

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A bound `M ^ q` on the `q`-th mean oscillation, `q ≥ 1`, bounds the mean oscillation by `M`. -/
private theorem setLAverage_enorm_sub_setAverage_le_of_rpow {b : X → ℝ} {S : Set X} {q : ℝ}
    (hq : 1 ≤ q) {M : ℝ≥0∞}
    (hM : ⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q) :
    ⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ∂μ ≤ M := by
  refine (laverage_le_laverage_rpow_rpow hq).trans ?_
  calc (⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (M ^ q) ^ (1 / q) :=
        ENNReal.rpow_le_rpow hM (by positivity)
    _ = M := by rw [one_div, ENNReal.rpow_rpow_inv (one_pos.trans_le hq).ne']

/-- **The weighted mean of `‖b - a‖`.** If the `q`-th mean oscillation of `b` on `S` is at most
`M ^ q`, `q⁻¹ + r⁻¹ = s⁻¹` and `1 ≤ s`, then for every constant `a` and every `ψ ≥ 0`,
`⨍_S ‖b - a‖ ψ ≤ (M + ‖b_S - a‖) (⨍_S ψ ^ r) ^ (1 / r)`. -/
private theorem setLAverage_enorm_sub_mul_le {b : X → ℝ} {S : Set X} {q r s : ℝ}
    (hqrs : q.HolderTriple r s) (hs : 1 ≤ s) (hb : AEStronglyMeasurable b (μ.restrict S))
    {M : ℝ≥0∞} (hM : ⨍⁻ y in S, ‖b y - ⨍ z in S, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q) {ψ : X → ℝ≥0∞}
    (hψ : AEMeasurable ψ (μ.restrict S)) (a : ℝ) :
    ⨍⁻ y in S, ‖b y - a‖ₑ * ψ y ∂μ ≤
      (M + ‖(⨍ z in S, b z ∂μ) - a‖ₑ) * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) := by
  set bS := ⨍ z in S, b z ∂μ
  set κ := ‖bS - a‖ₑ
  have hr : 1 ≤ r := hs.trans hqrs.symm.lt.le
  have hu : AEMeasurable (fun y => ‖b y - bS‖ₑ) (μ.restrict S) :=
    (hb.sub (aestronglyMeasurable_const (b := bS))).enorm
  have h₁ : ⨍⁻ y in S, ‖b y - bS‖ₑ * ψ y ∂μ ≤ M * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) := by
    refine (laverage_mul_le_Lq_mul_Lr hu hψ hqrs hs).trans ?_
    gcongr
    calc (⨍⁻ y in S, ‖b y - bS‖ₑ ^ q ∂μ) ^ (1 / q) ≤ (M ^ q) ^ (1 / q) :=
          ENNReal.rpow_le_rpow hM (by have := hqrs.pos; positivity)
      _ = M := by rw [one_div, ENNReal.rpow_rpow_inv hqrs.pos.ne']
  have h₂ := laverage_le_laverage_rpow_rpow (μ := μ.restrict S) (u := ψ) hr
  calc ⨍⁻ y in S, ‖b y - a‖ₑ * ψ y ∂μ
      ≤ ⨍⁻ y in S, (‖b y - bS‖ₑ * ψ y + κ * ψ y) ∂μ := by
        refine setLAverage_mono_ae S (.of_forall fun y => ?_)
        simp only [← add_mul]
        gcongr
        calc ‖b y - a‖ₑ = ‖(b y - bS) + (bS - a)‖ₑ := by ring_nf
          _ ≤ _ := enorm_add_le _ _
    _ = ⨍⁻ y in S, ‖b y - bS‖ₑ * ψ y ∂μ + κ * ⨍⁻ y in S, ψ y ∂μ := by
        simp only [laverage_eq']
        rw [lintegral_add_left' (f := fun y => ‖b y - bS‖ₑ * ψ y) ((hu.mul hψ).smul_measure _),
          lintegral_const_mul' _ _ enorm_ne_top]
    _ ≤ M * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) + κ * (⨍⁻ y in S, ψ y ^ r ∂μ) ^ (1 / r) := by
        gcongr
    _ = _ := by rw [add_mul]

/-- The average of `u + v + κ` over a set of finite positive measure. -/
private theorem setLAverage_add_add_const {S : Set X} (h0 : μ S ≠ 0) (ht : μ S ≠ ∞)
    {u v : X → ℝ≥0∞} (hu : AEMeasurable u (μ.restrict S)) (κ : ℝ≥0∞) :
    ⨍⁻ x in S, (u x + v x + κ) ∂μ = ⨍⁻ x in S, u x ∂μ + ⨍⁻ x in S, v x ∂μ + κ := by
  rw [setLAverage_eq, setLAverage_eq, setLAverage_eq, lintegral_add_right _ measurable_const,
    lintegral_add_left' hu, setLIntegral_const, ENNReal.add_div, ENNReal.add_div,
    ENNReal.mul_div_cancel_right h0 ht]

end General

section Haar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

/-- Doubling the radius of a ball multiplies its Haar measure by `2ⁿ`. -/
private theorem measure_ball_two_mul (c : V) {ρ : ℝ} (hρ : 0 < ρ) :
    μ (ball c (2 * ρ)) = 2 ^ finrank ℝ V * μ (ball c ρ) := by
  rw [Measure.addHaar_ball_of_pos μ c (by positivity), Measure.addHaar_ball_of_pos μ c hρ,
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat, mul_assoc]

/-- The weight of the `k`-th dyadic annulus in the tail estimate:
`R^δ (2ᵏ · 2R)^(-(n + δ)) (2ᵏ⁺¹ · 2R)ⁿ = 2ⁿ (2^(-δ))^(k + 1)`. -/
private theorem rpow_mul_rpow_mul_pow_eq {R : ℝ} (hR : 0 < R) (n : ℕ) (δ : ℝ) (k : ℕ) :
    R ^ δ * (2 ^ k * (2 * R)) ^ (-((n : ℝ) + δ)) * (2 ^ (k + 1) * (2 * R)) ^ n =
      2 ^ n * ((2 : ℝ) ^ (-δ)) ^ (k + 1) := by
  set t : ℝ := 2 ^ (k + 1) * R
  have ht : 0 < t := by positivity
  have h₁ : 2 ^ k * (2 * R) = t := by simp only [t]; ring
  have h₂ : 2 ^ (k + 1) * (2 * R) = 2 * t := by simp only [t]; ring
  have h₃ : t ^ (-((n : ℝ) + δ)) * t ^ n = t ^ (-δ) := by
    rw [neg_add, Real.rpow_add ht, Real.rpow_neg ht.le (n : ℝ), Real.rpow_natCast,
      mul_right_comm, inv_mul_cancel₀ (pow_pos ht n).ne', one_mul]
  have h₄ : R ^ δ * t ^ (-δ) = ((2 : ℝ) ^ (-δ)) ^ (k + 1) := by
    rw [Real.mul_rpow (by positivity) hR.le]
    calc R ^ δ * ((2 ^ (k + 1)) ^ (-δ) * R ^ (-δ)) = (2 ^ (k + 1)) ^ (-δ) * (R ^ δ * R ^ (-δ)) := by
          ring
      _ = ((2 : ℝ) ^ (k + 1)) ^ (-δ) := by
          rw [← Real.rpow_add hR, add_neg_cancel, Real.rpow_zero, mul_one]
      _ = ((2 : ℝ) ^ (-δ)) ^ (k + 1) := by
          rw [← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul zero_le_two, mul_comm,
            Real.rpow_mul zero_le_two, Real.rpow_natCast]
  rw [h₁, h₂, mul_pow]
  calc R ^ δ * t ^ (-((n : ℝ) + δ)) * (2 ^ n * t ^ n)
      = 2 ^ n * (R ^ δ * (t ^ (-((n : ℝ) + δ)) * t ^ n)) := by ring
    _ = _ := by rw [h₃, h₄]

/-- The constant `∑ₖ (2^(-δ))^(k + 1) (1 + (k + 1) 2ⁿ)` of the tail estimate is finite for
`δ > 0`. -/
private theorem tsum_ofReal_mul_ne_top (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n) ≠ ∞ := by
  set ε : ℝ := (2 : ℝ) ^ (-δ)
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  set g : ℕ → ℝ := fun k => ε ^ (k + 1) * (1 + (k + 1) * 2 ^ n)
  have hg : Summable g := by
    have h₀ : Summable fun k : ℕ => ε ^ (k + 1) :=
      (summable_geometric_of_lt_one hε0 hε1).mul_left ε |>.congr fun k => by ring
    have h₁ : Summable fun k : ℕ => (k : ℝ) ^ 1 * ε ^ k :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hε0])
    have h₁' : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ 1 * ε ^ (k + 1) :=
      (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ 1 * ε ^ k) 1).2 h₁
    refine (h₀.add (h₁'.mul_left (2 ^ n))).congr fun k => ?_
    simp only [g, Nat.cast_add, Nat.cast_one, pow_one]
    ring
  have heq : ∀ k : ℕ, ENNReal.ofReal (ε ^ (k + 1)) * (1 + (k + 1) * 2 ^ n) =
      ENNReal.ofReal (g k) := fun k => by
    simp only [g]
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (1 : ℝ) + (k + 1) * 2 ^ n = ((1 + (k + 1) * 2 ^ n : ℕ) : ℝ) by push_cast; ring,
      ENNReal.ofReal_natCast]
    push_cast
    ring
  simp only [heq]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hg]
  exact ENNReal.ofReal_ne_top

/-- **One dyadic annulus of the tail estimate.** Under the hypotheses of the tail estimate, the
integral over `2ᵏ · 2R ≤ |y - c| < 2ᵏ⁺¹ · 2R` is at most
`2ⁿ |B(0, 1)| (2^(-δ))^(k + 1) (1 + (k + 1) 2ⁿ) M (M ψ^r)(x)^(1/r)`: the weight is at most its
value on the inner sphere, and the average of `b` over `B(c, 2ᵏ⁺¹ · 2R)` is within
`(k + 1) 2ⁿ M` of `b_{B(c, 2R)}`. -/
private theorem setLIntegral_annulus_ofReal_mul_le {b : V → ℝ} (hb : AEStronglyMeasurable b μ)
    {q r s : ℝ} (hqrs : q.HolderTriple r s) (hs : 1 ≤ s) {M : ℝ≥0∞}
    (hM : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q)
    {ψ : V → ℝ≥0∞} (hψ : AEMeasurable ψ μ) {δ : ℝ} (hδ : 0 < δ) {c x : V} {R : ℝ}
    (hx : x ∈ ball c R) (k : ℕ) :
    ∫⁻ y in ball c (2 ^ (k + 1) * (2 * R)) \ ball c (2 ^ k * (2 * R)),
        ENNReal.ofReal (R ^ δ * dist y c ^ (-((finrank ℝ V : ℝ) + δ))) *
          (‖b y - ⨍ z in ball c (2 * R), b z ∂μ‖ₑ * ψ y) ∂μ ≤
      2 ^ finrank ℝ V * μ (ball 0 1) *
        (ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ finrank ℝ V)) * M *
        uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r) := by
  set n := finrank ℝ V
  have hR : 0 < R := pos_of_mem_ball hx
  set ρ := 2 * R with hρdef
  have hρ : 0 < ρ := by positivity
  set a₀ := ⨍ z in ball c ρ, b z ∂μ
  set Φ : V → ℝ≥0∞ := fun y => ‖b y - a₀‖ₑ * ψ y
  set Mx := uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r)
  have hr0 : 0 < r := hqrs.symm.pos
  have hM₁ : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ∂μ ≤ M := fun c ρ =>
    setLAverage_enorm_sub_setAverage_le_of_rpow (hs.trans hqrs.lt.le) (hM c ρ)
  set ρk := 2 ^ (k + 1) * ρ
  have hρk : 0 < ρk := by positivity
  set Sk := ball c ρk \ ball c (2 ^ k * ρ)
  have hS : MeasurableSet Sk := measurableSet_ball.diff measurableSet_ball
  have hxk : x ∈ ball c ρk := by
    refine mem_ball.2 ((mem_ball.1 hx).trans_le ?_)
    have : (1 : ℝ) ≤ 2 ^ (k + 1) * 2 := by
      have := one_le_pow₀ (M₀ := ℝ) (n := k + 1) one_le_two; linarith
    simp only [ρk, ρ]; nlinarith
  -- On the annulus the weight is at most its value `w` at the inner radius.
  set w := ENNReal.ofReal (R ^ δ * (2 ^ k * ρ) ^ (-((n : ℝ) + δ)))
  have hw : ∀ y ∈ Sk, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ≤ w * Φ y := by
    intro y hy
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left ?_ (by positivity))) _
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (not_lt.1 fun h => hy.2 (mem_ball.2 h))
      (neg_nonpos.2 (by positivity))
  -- The weighted mean of `Φ` over the enclosing ball.
  have havg : ⨍⁻ y in ball c ρk, Φ y ∂μ ≤ (M + (k + 1) * (2 ^ n * M)) * Mx := by
    refine (setLAverage_enorm_sub_mul_le hqrs hs hb.restrict (hM c ρk) hψ.restrict a₀).trans ?_
    gcongr
    · refine (enorm_setAverage_ball_two_pow_mul_sub_le hb c hρ (k + 1)).trans ?_
      push_cast
      rw [mul_assoc]
      gcongr
      exact bmoSeminorm_le hM₁
    · refine ENNReal.rpow_le_rpow ?_ (by positivity)
      simpa only [enorm_eq_self] using
        setLAverage_le_uncenteredMaximalFunction μ (fun y => ψ y ^ r) hxk
  have hcoef :
      w * ENNReal.ofReal (ρk ^ n) = 2 ^ n * ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) := by
    rw [← ENNReal.ofReal_mul (by positivity), hρdef, rpow_mul_rpow_mul_pow_eq hR n δ k,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  calc ∫⁻ y in Sk, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ
      ≤ ∫⁻ y in Sk, w * Φ y ∂μ := setLIntegral_mono' hS hw
    _ = w * ∫⁻ y in Sk, Φ y ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ w * (μ (ball c ρk) * ⨍⁻ y in ball c ρk, Φ y ∂μ) := by
        rw [measure_mul_setLAverage _ measure_ball_lt_top.ne]
        gcongr
        exact sdiff_subset
    _ ≤ w * (ENNReal.ofReal (ρk ^ n) * μ (ball 0 1) * ((M + (k + 1) * (2 ^ n * M)) * Mx)) := by
        rw [Measure.addHaar_ball_of_pos μ c hρk]
        gcongr
    _ = w * ENNReal.ofReal (ρk ^ n) * μ (ball 0 1) * ((M + (k + 1) * (2 ^ n * M)) * Mx) := by
        ring
    _ = 2 ^ n * μ (ball 0 1) *
          (ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n)) * M * Mx := by
        rw [hcoef]
        ring

/-- **The tail estimate.** Let the `q`-th mean oscillation of `b` on every ball be at most `M ^ q`,
with `q⁻¹ + r⁻¹ = s⁻¹` and `1 ≤ s`, and let `x ∈ B(c, R)`. Integrating
`‖b - b_{B(c, 2R)}‖ ψ` against the kernel bound `R^δ |y - c|^(-(n + δ))` off `B(c, 2R)` gives at
most `2ⁿ |B(0, 1)| S M (M ψ^r)(x)^(1/r)`, where `S = ∑ₖ (2^(-δ))^(k + 1) (1 + (k + 1) 2ⁿ)` and
`M ψ^r` is the uncentred maximal function of `ψ ^ r`. The integral is split over the dyadic
annuli `2ᵏ · 2R ≤ |y - c| < 2ᵏ⁺¹ · 2R`. -/
private theorem setLIntegral_compl_ball_ofReal_mul_le {b : V → ℝ} (hb : AEStronglyMeasurable b μ)
    {q r s : ℝ} (hqrs : q.HolderTriple r s) (hs : 1 ≤ s) {M : ℝ≥0∞}
    (hM : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q)
    {ψ : V → ℝ≥0∞} (hψ : AEMeasurable ψ μ) {δ : ℝ} (hδ : 0 < δ) {c x : V} {R : ℝ}
    (hx : x ∈ ball c R) :
    ∫⁻ y in (ball c (2 * R))ᶜ, ENNReal.ofReal (R ^ δ * dist y c ^ (-((finrank ℝ V : ℝ) + δ))) *
        (‖b y - ⨍ z in ball c (2 * R), b z ∂μ‖ₑ * ψ y) ∂μ ≤
      2 ^ finrank ℝ V * μ (ball 0 1) *
        (∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) *
          (1 + (k + 1) * 2 ^ finrank ℝ V)) * M *
        uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r) := by
  set n := finrank ℝ V
  have hR : 0 < R := pos_of_mem_ball hx
  set ρ := 2 * R
  have hρ : 0 < ρ := by positivity
  set a₀ := ⨍ z in ball c ρ, b z ∂μ
  set Φ : V → ℝ≥0∞ := fun y => ‖b y - a₀‖ₑ * ψ y
  set Mx := uncenteredMaximalFunction μ (fun y => ψ y ^ r) x ^ (1 / r)
  -- The annuli cover the complement of `B(c, ρ)`.
  set S : ℕ → Set V := fun k => ball c (2 ^ (k + 1) * ρ) \ ball c (2 ^ k * ρ)
  have hcover : (ball c ρ)ᶜ ⊆ ⋃ k, S k := by
    intro y hy
    have hy' : 1 ≤ dist y c / ρ := by
      rw [le_div_iff₀ hρ, one_mul]
      simpa [mem_ball] using hy
    obtain ⟨k, hk₁, hk₂⟩ := exists_nat_pow_near hy' one_lt_two
    refine mem_iUnion.2 ⟨k, mem_ball.2 ?_, fun h => ?_⟩
    · rwa [div_lt_iff₀ hρ] at hk₂
    · rw [le_div_iff₀ hρ] at hk₁
      exact (mem_ball.1 h).not_ge hk₁
  calc ∫⁻ y in (ball c ρ)ᶜ, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ
      ≤ ∫⁻ y in ⋃ k, S k, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ y in S k, ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * Φ y ∂μ :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, 2 ^ n * μ (ball 0 1) *
          (ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n)) * M * Mx :=
        tsum_le_tsum fun k =>
          setLIntegral_annulus_ofReal_mul_le hb hqrs hs hM hψ hδ hx k
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **The local part.** If `T` is bounded in the `Lˢ` norm with constant `N` and `‖g‖ ≤ Φ` on
`B(c, 2R)` with `g = 0` off it, then
`⨍_{B(c, R)} ‖T g‖ ≤ N (2ⁿ)^(1/s) (⨍_{B(c, 2R)} Φ ^ s)^(1/s)`. -/
private theorem setLAverage_enorm_apply_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) {s : ℝ} (hs : 1 ≤ s)
    {N : ℝ≥0∞}
    (hT : ∀ g, eLpNorm (T g) (ENNReal.ofReal s) μ ≤ N * eLpNorm g (ENNReal.ofReal s) μ)
    {g : Lp E 2 μ} {c : V} {R : ℝ} (hR : 0 < R) {Φ : V → ℝ≥0∞}
    (hg : ∀ᵐ y ∂μ, ‖g y‖ₑ ^ s ≤ (ball c (2 * R)).indicator (fun y => Φ y ^ s) y) :
    ⨍⁻ z in ball c R, ‖T g z‖ₑ ∂μ ≤
      N * (2 ^ finrank ℝ V) ^ (1 / s) * (⨍⁻ y in ball c (2 * R), Φ y ^ s ∂μ) ^ (1 / s) := by
  have hs0 : 0 < s := one_pos.trans_le hs
  have hs' : (ENNReal.ofReal s).toReal = s := ENNReal.toReal_ofReal hs0.le
  have hs0' : ENNReal.ofReal s ≠ 0 := by simpa using hs0
  have hB0 : μ (ball c R) ≠ 0 := (measure_ball_pos μ c hR).ne'
  have hBt : μ (ball c R) ≠ ∞ := measure_ball_lt_top.ne
  set P := ⨍⁻ y in ball c (2 * R), Φ y ^ s ∂μ
  -- Multiplied by `μ(B(c, R)) ^ (1 / s)`, the `s`-th mean of `T g` is at most `‖T g‖_s`.
  have key : μ (ball c R) ^ (1 / s) * (⨍⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s) ≤
      μ (ball c R) ^ (1 / s) * (N * (2 ^ finrank ℝ V) ^ (1 / s) * P ^ (1 / s)) := by
    calc μ (ball c R) ^ (1 / s) * (⨍⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s)
        = (∫⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s) := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ (by positivity), measure_mul_setLAverage _ hBt]
      _ ≤ eLpNorm (T g) (ENNReal.ofReal s) μ := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0' ENNReal.ofReal_ne_top
            (Lp.aestronglyMeasurable _), hs']
          exact ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) (by positivity)
      _ ≤ N * eLpNorm g (ENNReal.ofReal s) μ := hT g
      _ ≤ N * (∫⁻ y in ball c (2 * R), Φ y ^ s ∂μ) ^ (1 / s) := by
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0' ENNReal.ofReal_ne_top
            (Lp.aestronglyMeasurable _), hs', ← lintegral_indicator measurableSet_ball]
          have := ENNReal.rpow_le_rpow (z := 1 / s) (lintegral_mono_ae hg) (by positivity)
          gcongr
      _ = μ (ball c R) ^ (1 / s) * (N * (2 ^ finrank ℝ V) ^ (1 / s) * P ^ (1 / s)) := by
          rw [← measure_mul_setLAverage _ measure_ball_lt_top.ne, measure_ball_two_mul c hR,
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
          ring
  calc ⨍⁻ z in ball c R, ‖T g z‖ₑ ∂μ ≤ (⨍⁻ z in ball c R, ‖T g z‖ₑ ^ s ∂μ) ^ (1 / s) :=
        laverage_le_laverage_rpow_rpow hs
    _ ≤ _ := (ENNReal.mul_le_mul_iff_right (by simp [hB0, hs0.le])
        (ENNReal.rpow_ne_top_of_nonneg (by positivity) hBt)).1 key

omit [FiniteDimensional ℝ V] [μ.IsAddHaarMeasure] in
/-- **The far part.** Let `T` be given by the kernel `K` on balls where its argument vanishes,
with the standard smoothness estimate in the first variable. If `‖g‖ ≤ Φ` and `g` vanishes on
`B(c, 2R)`, then for almost every `z ∈ B(c, R)`,
`‖T g z - ∫ K c y (g y) dy‖ ≤ A ∫_{|y - c| ≥ 2R} R^δ |y - c|^(-(n + δ)) Φ(y) dy`. -/
private theorem ae_enorm_apply_sub_integral_le (T : Lp E 2 μ →L[ℝ] Lp F 2 μ)
    {K : V → V → E →L[ℝ] F} (hK : ∀ x, AEStronglyMeasurable (K x) μ) {A : ℝ≥0} {δ : ℝ}
    (hKs : ∀ x x' y, 2 * dist x x' < dist y x' →
      ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-((finrank ℝ V : ℝ) + δ))))
    (hrep : ∀ (g : Lp E 2 μ) (y : V) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → g z = 0) →
      ∀ᵐ x ∂μ, x ∈ ball y ρ → T g x = ∫ z, K x z (g z) ∂μ)
    (hδ : 0 ≤ δ) {g : Lp E 2 μ} {c : V} {R : ℝ} {Φ : V → ℝ≥0∞}
    (hg : ∀ᵐ y ∂μ, ‖g y‖ₑ ≤ (ball c (2 * R))ᶜ.indicator Φ y) :
    ∀ᵐ z ∂μ.restrict (ball c R), ‖T g z - ∫ y, K c y (g y) ∂μ‖ₑ ≤
      A * ∫⁻ y in (ball c (2 * R))ᶜ,
        ENNReal.ofReal (R ^ δ * dist y c ^ (-((finrank ℝ V : ℝ) + δ))) * Φ y ∂μ := by
  rw [ae_restrict_iff' measurableSet_ball]
  have hvan : ∀ᵐ y ∂μ, y ∈ ball c (2 * R) → g y = 0 := by
    filter_upwards [hg] with y hy hyB
    simpa [indicator_of_notMem (notMem_compl_iff.2 hyB)] using hy
  filter_upwards [hrep g c (2 * R) hvan] with z hz hzB
  have hR : 0 < R := pos_of_mem_ball hzB
  rw [hz (ball_subset_ball (by linarith) hzB)]
  have hle : ∫⁻ y, ‖K z y (g y) - K c y (g y)‖ₑ ∂μ ≤ ∫⁻ y, ‖K z y - K c y‖ₑ * ‖g y‖ₑ ∂μ :=
    lintegral_mono fun y => by
      rw [← sub_apply]
      exact ContinuousLinearMap.le_opENorm _ _
  refine ((MeasureTheory.enorm_integral_sub_integral_le_lintegral_enorm_sub
    ((ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable g)
      (hK z))
    ((ContinuousLinearMap.apply ℝ F).aestronglyMeasurable_comp₂ (Lp.aestronglyMeasurable g)
      (hK c))).trans hle).trans ?_
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← lintegral_indicator measurableSet_ball.compl]
  refine lintegral_mono_ae ?_
  filter_upwards [hg] with y hy
  by_cases hyB : y ∈ ball c (2 * R)
  · rw [indicator_of_notMem (notMem_compl_iff.2 hyB)] at hy ⊢
    simp [nonpos_iff_eq_zero.1 hy]
  rw [indicator_of_mem hyB] at hy ⊢
  rw [← mul_assoc (A : ℝ≥0∞)]
  refine mul_le_mul' ?_ hy
  -- The kernel estimate, with `|z - c| < R` and `|y - c| ≥ 2R`.
  have hzc : dist z c < R := mem_ball.1 hzB
  have hyc : 2 * R ≤ dist y c := not_lt.1 fun h => hyB (mem_ball.2 h)
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul A.coe_nonneg]
  refine ENNReal.ofReal_le_ofReal ((hKs z c y (by linarith)).trans ?_)
  gcongr

variable [CompleteSpace F]

/-- **The sharp maximal function of a commutator with a singular integral operator**
(Coifman–Rochberg–Weiss). Let `μ` be an additive Haar measure on a finite-dimensional real normed
space `V` of dimension `n`, and let `T` be a bounded linear operator on `L²(μ)` given, on any ball
on which its argument vanishes, by a kernel `K` satisfying the standard smoothness estimate in the
first variable,

`‖K x y - K x' y‖ ≤ A |x - x'| ^ δ |y - x'| ^ (-(n + δ))` whenever `2 |x - x'| < |y - x'|`,

with `δ > 0`, and bounded in the `Lˢ` norm on `L²`: `‖T g‖_s ≤ N ‖g‖_s`. Let `q⁻¹ + r⁻¹ = s⁻¹`
with `1 ≤ s`. Then there is a constant `C` such that for every bounded `b` whose `q`-th mean
oscillation on every ball is at most `M ^ q`, every `f ∈ L²` and every point `x`,

`(b T f - T (b f))^# (x) ≤ C M ((M |T f|^r)(x)^(1/r) + (M |f|^r)(x)^(1/r))`,

where `g^#` is the sharp maximal function and `M` the uncentred Hardy–Littlewood maximal
function. The constant depends only on `V`, `μ`, `s`, `q`, `r`, `δ`, `A` and `N`, not on `T`,
`b`, `f` or `x`. -/
theorem exists_sharpMaximalFunction_commutator_le {q r s δ : ℝ} (hqrs : q.HolderTriple r s)
    (hs : 1 ≤ s) (hδ : 0 < δ) (A N : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 μ →L[ℝ] Lp F 2 μ) (K : V → V → E →L[ℝ] F),
      (∀ x, AEStronglyMeasurable (K x) μ) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-((finrank ℝ V : ℝ) + δ)))) →
      (∀ (g : Lp E 2 μ) (y : V) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → g z = 0) →
        ∀ᵐ x ∂μ, x ∈ ball y ρ → T g x = ∫ z, K x z (g z) ∂μ) →
      (∀ g : Lp E 2 μ,
        eLpNorm (T g) (ENNReal.ofReal s) μ ≤ N * eLpNorm g (ENNReal.ofReal s) μ) →
      ∀ (b : Lp ℝ ∞ μ) (M : ℝ≥0∞),
        (∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q) →
        ∀ (f : Lp E 2 μ) (x : V),
          sharpMaximalFunction μ (⇑(b • T f - T (b • f))) x ≤
            C * M * (uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) x ^ (1 / r) +
              uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) x ^ (1 / r)) := by
  set n := finrank ℝ V
  set S := ∑' k : ℕ, ENNReal.ofReal (((2 : ℝ) ^ (-δ)) ^ (k + 1)) * (1 + (k + 1) * 2 ^ n)
  have hS : S ≠ ∞ := tsum_ofReal_mul_ne_top n hδ
  set K₀ : ℝ≥0∞ := 1 + 2 ^ n + N * (2 ^ n) ^ (1 / s) + A * (2 ^ n * μ (ball 0 1) * S)
  have hK₀ : 2 * K₀ ≠ ∞ := by
    have : μ (ball (0 : V) 1) ≠ ∞ := measure_ball_lt_top.ne
    have : (2 ^ n : ℝ≥0∞) ^ (1 / s) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp)
    finiteness
  refine ⟨(2 * K₀).toNNReal, fun T K hK hKs hrep hTs b M hb f x => ?_⟩
  rw [ENNReal.coe_toNNReal hK₀]
  set MTf := uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) x ^ (1 / r)
  set Mf := uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) x ^ (1 / r)
  have hbm : AEStronglyMeasurable (b : V → ℝ) μ := Lp.aestronglyMeasurable b
  have hq1 : 1 ≤ q := hs.trans hqrs.lt.le
  have hM₁ : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ∂μ ≤ M := fun c ρ =>
    setLAverage_enorm_sub_setAverage_le_of_rpow hq1 (hb c ρ)
  refine sharpMaximalFunction_le fun c R hx => ?_
  have hR : 0 < R := pos_of_mem_ball hx
  set a₀ := ⨍ z in ball c (2 * R), b z ∂μ
  -- Split `(b - a₀) f = g₁ + g₂` with `g₁` supported in `B(c, 2R)` and `g₂` vanishing there.
  have hmem : MemLp (fun y => (b y - a₀) • f y) 2 μ :=
    ((Lp.memLp b).sub (memLp_top_const a₀)).smul (Lp.memLp f)
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : Lp E 2 μ,
      g₂ =ᵐ[μ] (ball c (2 * R))ᶜ.indicator fun y => (b y - a₀) • f y :=
    ⟨_, (hmem.indicator measurableSet_ball.compl.nullMeasurableSet).coeFn_toLp⟩
  set g₁ : Lp E 2 μ := b • f - a₀ • f - g₂
  have hg₁ : ⇑g₁ =ᵐ[μ] (ball c (2 * R)).indicator fun y => (b y - a₀) • f y := by
    filter_upwards [Lp.coeFn_sub (b • f - a₀ • f) g₂, Lp.coeFn_sub (b • f) (a₀ • f),
      Lp.coeFn_lpSMul (r := 2) b f, Lp.coeFn_smul a₀ f, hg₂] with z h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, h4, h5]
    simp only [Pi.smul_apply', Pi.smul_apply]
    by_cases hz : z ∈ ball c (2 * R) <;> simp [hz, sub_smul]
  have hsplit : T (b • f) = T g₁ + T g₂ + a₀ • T f := by
    simp only [g₁, map_sub, map_smul]
    abel
  have hh : ⇑(b • T f - T (b • f)) =ᵐ[μ] fun z => (b z - a₀) • T f z - T g₁ z - T g₂ z := by
    rw [hsplit]
    filter_upwards [Lp.coeFn_sub (b • T f) (T g₁ + T g₂ + a₀ • T f),
      Lp.coeFn_lpSMul (r := 2) b (T f),
      Lp.coeFn_add (T g₁ + T g₂) (a₀ • T f), Lp.coeFn_add (T g₁) (T g₂),
      Lp.coeFn_smul a₀ (T f)] with z h1 h2 h3 h4 h5
    rw [h1, Pi.sub_apply, h2, h3, Pi.add_apply, h4, Pi.add_apply, h5]
    simp only [Pi.smul_apply', Pi.smul_apply, sub_smul]
    abel
  -- The far part: on `B(c, R)`, `T g₂` stays within `A J` of the constant `∫ K c y (g₂ y) dy`.
  set a : F := ∫ y, K c y (g₂ y) ∂μ
  set J := ∫⁻ y in (ball c (2 * R))ᶜ,
    ENNReal.ofReal (R ^ δ * dist y c ^ (-((n : ℝ) + δ))) * (‖b y - a₀‖ₑ * ‖f y‖ₑ) ∂μ
  have hfar : ∀ᵐ z ∂μ.restrict (ball c R), ‖T g₂ z - a‖ₑ ≤ A * J := by
    refine ae_enorm_apply_sub_integral_le T hK hKs hrep hδ.le ?_
    filter_upwards [hg₂] with y hy
    rw [hy]
    by_cases hyB : y ∈ (ball c (2 * R))ᶜ
    · simp [hyB, enorm_smul]
    · simp [hyB]
  -- Pointwise on `B(c, R)`, compare `[b, T] f` with the constant `-a`.
  have hpt : ∀ᵐ z ∂μ.restrict (ball c R), ‖(b • T f - T (b • f)) z - -a‖ₑ ≤
      ‖b z - a₀‖ₑ * ‖T f z‖ₑ + ‖T g₁ z‖ₑ + A * J := by
    filter_upwards [ae_restrict_of_ae hh, hfar] with z h1 h2
    rw [h1]
    calc ‖(b z - a₀) • T f z - T g₁ z - T g₂ z - -a‖ₑ
        = ‖(b z - a₀) • T f z + -T g₁ z + -(T g₂ z - a)‖ₑ := by congr 1; abel
      _ ≤ ‖(b z - a₀) • T f z‖ₑ + ‖-T g₁ z‖ₑ + ‖-(T g₂ z - a)‖ₑ :=
          (enorm_add_le _ _).trans (by gcongr; exact enorm_add_le _ _)
      _ ≤ _ := by rw [enorm_smul, enorm_neg, enorm_neg]; gcongr
  -- The first term, by Hölder's inequality on `B(c, R)`.
  have h₁ : ⨍⁻ z in ball c R, ‖b z - a₀‖ₑ * ‖T f z‖ₑ ∂μ ≤ (1 + 2 ^ n) * M * MTf := by
    refine (setLAverage_enorm_sub_mul_le hqrs hs hbm.restrict (hb c R)
      (Lp.aestronglyMeasurable (T f)).enorm.restrict a₀).trans ?_
    have hdrift : ‖(⨍ z in ball c R, b z ∂μ) - a₀‖ₑ ≤ 2 ^ n * M := by
      rw [enorm_sub_rev]
      calc _ ≤ 2 ^ n * bmoSeminorm (⇑b) μ := by
            simpa [a₀] using enorm_setAverage_ball_two_pow_mul_sub_le hbm c hR 1
        _ ≤ 2 ^ n * M := by
            gcongr
            exact bmoSeminorm_le hM₁
    calc _ ≤ (M + 2 ^ n * M) * MTf := by
          gcongr
          refine ENNReal.rpow_le_rpow ?_ (by have := hqrs.symm.pos; positivity)
          simpa only [enorm_eq_self] using
            setLAverage_le_uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) hx
      _ = _ := by ring
  -- The second term, by the `Lˢ` bound of `T` and Hölder's inequality on `B(c, 2R)`.
  have hx₂ : x ∈ ball c (2 * R) := ball_subset_ball (by linarith) hx
  have h₂ : ⨍⁻ z in ball c R, ‖T g₁ z‖ₑ ∂μ ≤ N * (2 ^ n) ^ (1 / s) * M * Mf := by
    have hs0 : 0 < s := one_pos.trans_le hs
    have hg₁s : ∀ᵐ y ∂μ, ‖g₁ y‖ₑ ^ s ≤
        (ball c (2 * R)).indicator (fun y => (‖b y - a₀‖ₑ * ‖f y‖ₑ) ^ s) y := by
      filter_upwards [hg₁] with y hy
      rw [hy]
      by_cases hyB : y ∈ ball c (2 * R)
      · simp [hyB, enorm_smul]
      · simp [hyB, ENNReal.zero_rpow_of_pos hs0]
    refine (setLAverage_enorm_apply_le T hs hTs hR hg₁s).trans ?_
    have hHolder : (⨍⁻ y in ball c (2 * R), (‖b y - a₀‖ₑ * ‖f y‖ₑ) ^ s ∂μ) ^ (1 / s) ≤
        M * Mf := by
      refine (laverage_Lp_mul_le_Lq_mul_Lr
        (hbm.sub (aestronglyMeasurable_const (b := a₀))).enorm.restrict
        (Lp.aestronglyMeasurable f).enorm.restrict hqrs).trans ?_
      gcongr
      · calc _ ≤ (M ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow (hb c (2 * R))
              (by have := hqrs.pos; positivity)
          _ = M := by rw [one_div, ENNReal.rpow_rpow_inv hqrs.pos.ne']
      · refine ENNReal.rpow_le_rpow ?_ (by have := hqrs.symm.pos; positivity)
        simpa only [enorm_eq_self] using
          setLAverage_le_uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) hx₂
    calc _ ≤ N * (2 ^ n) ^ (1 / s) * (M * Mf) := by gcongr
      _ = _ := by ring
  -- The third term, by the kernel estimate on dyadic annuli.
  have h₃ : J ≤ 2 ^ n * μ (ball 0 1) * S * M * Mf :=
    setLIntegral_compl_ball_ofReal_mul_le hbm hqrs hs hb (Lp.aestronglyMeasurable f).enorm hδ hx
  have : IsFiniteMeasure (μ.restrict (ball c R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (⇑(b • T f - T (b • f))) (ball c R) μ :=
    ((Lp.memLp _).restrict _).integrable one_le_two
  calc ⨍⁻ z in ball c R, ‖(b • T f - T (b • f)) z -
        ⨍ w in ball c R, (b • T f - T (b • f)) w ∂μ‖ₑ ∂μ
      ≤ 2 * ⨍⁻ z in ball c R, ‖(b • T f - T (b • f)) z - -a‖ₑ ∂μ :=
        setLAverage_enorm_sub_setAverage_le hint (-a)
    _ ≤ 2 * ⨍⁻ z in ball c R, (‖b z - a₀‖ₑ * ‖T f z‖ₑ + ‖T g₁ z‖ₑ + A * J) ∂μ := by
        gcongr 2 * ?_
        exact laverage_mono_ae hpt
    _ = 2 * (⨍⁻ z in ball c R, ‖b z - a₀‖ₑ * ‖T f z‖ₑ ∂μ + ⨍⁻ z in ball c R, ‖T g₁ z‖ₑ ∂μ +
          A * J) := by
        rw [setLAverage_add_add_const (u := fun z => ‖b z - a₀‖ₑ * ‖T f z‖ₑ)
          (measure_ball_pos μ c hR).ne' measure_ball_lt_top.ne
          ((hbm.sub (aestronglyMeasurable_const (b := a₀))).enorm.mul
            (Lp.aestronglyMeasurable (T f)).enorm).restrict]
    _ ≤ 2 * ((1 + 2 ^ n) * M * MTf + N * (2 ^ n) ^ (1 / s) * M * Mf +
          A * (2 ^ n * μ (ball 0 1) * S * M * Mf)) := by
        gcongr
    _ = 2 * M * ((1 + 2 ^ n) * MTf + (N * (2 ^ n) ^ (1 / s) + A * (2 ^ n * μ (ball 0 1) * S)) *
          Mf) := by ring
    _ ≤ 2 * M * (K₀ * MTf + K₀ * Mf) := by
        gcongr
        · exact le_add_right (le_add_right le_rfl)
        · calc _ ≤ (1 + 2 ^ n) + (N * (2 ^ n) ^ (1 / s) + A * (2 ^ n * μ (ball 0 1) * S)) :=
                le_add_left le_rfl
            _ = K₀ := (add_assoc _ _ _).symm
    _ = 2 * K₀ * M * (MTf + Mf) := by ring

end Haar

section Euclidean

variable {ι E F : Type*} [Fintype ι] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- **The sharp maximal function of a commutator with a function of bounded mean oscillation**
(Coifman–Rochberg–Weiss), on `ℝⁿ = EuclideanSpace ℝ ι` with an additive Haar measure `μ`. Let `T`
be a bounded linear operator on `L²(μ)` given, on any ball on which its argument vanishes, by a
kernel `K` with the standard smoothness estimate in the first variable,

`‖K x y - K x' y‖ ≤ A |x - x'| ^ δ |y - x'| ^ (-(n + δ))` whenever `2 |x - x'| < |y - x'|`,

with `δ > 0`, and bounded in the `Lˢ` norm on `L²`, `‖T g‖_s ≤ N ‖g‖_s`, for some `1 ≤ s`. Then
for every `r > s` there is a constant `C` such that for every bounded `b`, every `f ∈ L²` and every
point `x`,

`(b T f - T (b f))^# (x) ≤ C ‖b‖_{BMO} ((M |T f|^r)(x)^(1/r) + (M |f|^r)(x)^(1/r))`,

where `g^#` is the sharp maximal function and `M` the uncentred Hardy–Littlewood maximal
function. The constant depends only on `ι`, `μ`, `s`, `r`, `δ`, `A` and `N`. This is
`TauCeti.exists_sharpMaximalFunction_commutator_le` with the `q`-th mean oscillation of `b`,
`q⁻¹ = s⁻¹ - r⁻¹`, bounded by the `Lᵖ` form of the John–Nirenberg inequality
(`TauCeti.exists_setLAverage_enorm_sub_setAverage_rpow_le_mul_bmoSeminorm_rpow`). -/
theorem exists_sharpMaximalFunction_commutator_le_bmoSeminorm {r s δ : ℝ} (hs : 1 ≤ s)
    (hsr : s < r) (hδ : 0 < δ) (A N : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 μ →L[ℝ] Lp F 2 μ)
      (K : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι → E →L[ℝ] F),
      (∀ x, AEStronglyMeasurable (K x) μ) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ A * (dist x x' ^ δ * dist y x' ^ (-((Fintype.card ι : ℝ) + δ)))) →
      (∀ (g : Lp E 2 μ) (y : EuclideanSpace ℝ ι) (ρ : ℝ), (∀ᵐ z ∂μ, z ∈ ball y ρ → g z = 0) →
        ∀ᵐ x ∂μ, x ∈ ball y ρ → T g x = ∫ z, K x z (g z) ∂μ) →
      (∀ g : Lp E 2 μ,
        eLpNorm (T g) (ENNReal.ofReal s) μ ≤ N * eLpNorm g (ENNReal.ofReal s) μ) →
      ∀ (b : Lp ℝ ∞ μ) (f : Lp E 2 μ) (x : EuclideanSpace ℝ ι),
        sharpMaximalFunction μ (⇑(b • T f - T (b • f))) x ≤
          C * bmoSeminorm (⇑b) μ *
            (uncenteredMaximalFunction μ (fun y => ‖T f y‖ₑ ^ r) x ^ (1 / r) +
              uncenteredMaximalFunction μ (fun y => ‖f y‖ₑ ^ r) x ^ (1 / r)) := by
  have hs0 : 0 < s := one_pos.trans_le hs
  have hr0 : 0 < r := hs0.trans hsr
  have hq0 : 0 < s⁻¹ - r⁻¹ := sub_pos.2 (inv_strictAnti₀ hs0 hsr)
  have hqrs : (s⁻¹ - r⁻¹)⁻¹.HolderTriple r s :=
    ⟨by rw [inv_inv, sub_add_cancel], inv_pos.2 hq0, hr0⟩
  set q := (s⁻¹ - r⁻¹)⁻¹
  have hq : 0 < q := inv_pos.2 hq0
  obtain ⟨C₀, hC₀⟩ := exists_setLAverage_enorm_sub_setAverage_rpow_le_mul_bmoSeminorm_rpow
    (ι := ι) hq
  obtain ⟨C, hC⟩ := exists_sharpMaximalFunction_commutator_le (μ := μ) (E := E) (F := F)
    hqrs hs hδ A N
  refine ⟨C * C₀ ^ (1 / q), fun T K hK hKs hrep hTs b f x => ?_⟩
  set M : ℝ≥0∞ := (C₀ : ℝ≥0∞) ^ (1 / q) * bmoSeminorm (⇑b) μ
  have hM : ∀ c ρ, ⨍⁻ y in ball c ρ, ‖b y - ⨍ z in ball c ρ, b z ∂μ‖ₑ ^ q ∂μ ≤ M ^ q := by
    intro c ρ
    refine (hC₀ ((Lp.memLp b).locallyIntegrable le_top) c ρ).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne',
      ENNReal.rpow_one]
  have hrank : (Module.finrank ℝ (EuclideanSpace ℝ ι) : ℝ) = Fintype.card ι := by
    rw [finrank_euclideanSpace]
  refine (hC T K hK (by simpa only [hrank] using hKs) hrep hTs b M hM f x).trans (le_of_eq ?_)
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ (by positivity)]
  ring

end Euclidean

end TauCeti
