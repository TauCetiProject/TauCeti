/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.JohnNirenberg.HigherOscillation
public import TauCeti.MeasureTheory.Integral.MaximalFunction
public import TauCeti.MeasureTheory.Integral.SharpMaximalFunction
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.DistRpow
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Truncation
import TauCeti.MeasureTheory.Function.LpSeminorm.Clipping

/-!
# The sharp maximal function of a commutator with a function of bounded mean oscillation

Let `T` be a singular integral operator on `ℝⁿ = ι → ℝ`, `n ≥ 1`, and let `b` have bounded mean
oscillation. The **commutator** of `T` with multiplication by `b` is

`[b, T] f = b T f - T (b f)`.

Coifman, Rochberg and Weiss proved that `[b, T]` is bounded on `Lᵖ` for `1 < p < ∞`, with norm
`O(‖b‖_{BMO})`. This is the perturbative engine of the `W^{1,p}` and `W^{2,p}` theories of elliptic
equations whose coefficients have vanishing mean oscillation: freezing a coefficient `a` at a
point leaves an error that is a commutator `[a, T]` of a Calderón–Zygmund operator with `a`.

This file proves that theorem by Janson's method. Its first step is the pointwise estimate, for
`1 < q < ∞`,

`([b, T] f)^# x ≤ C ‖b‖_{BMO} ((M(‖T f‖^q) x)^{1/q} + (M(‖f‖^q) x)^{1/q})`

at every point `x` (`TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`),
where `^#` is the sharp maximal function and `M` the centred Hardy–Littlewood maximal function.
The operator `T` is bounded on `L²`, given away from the support of its argument by a kernel `K`
with the standard smoothness estimate in its first variable, and bounded in some `Lˢ` norm with
`1 ≤ s < q`. Calderón–Zygmund operators satisfy the `Lˢ` bound for every `1 < s < q`; the case
`s = 1` requires an additional strong `L¹` bound. Balls are taken in the sup distance, so that they
are cubes.

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
  On the dyadic annulus `2^(k+1) r ≤ dist z c < 2^(k+2) r` the kernel difference is
  `O(2^(-kδ) / |2^(k+2) B|)`, while `|b_{2^(k+2) B} - b_{2B}| ≤ (k + 3) 2ⁿ ‖b‖_{BMO}`. The sum over
  `k` converges.

## From the pointwise estimate to `Lᵖ`

Let `1 ≤ s < q < p < ∞` and let `T` also be bounded in the `Lᵖ` norm. When `[b, T] f` is known to
lie in `Lᵖ`, the Fefferman–Stein inequality and the maximal inequality in `L^{p/q}` turn the
pointwise estimate into `‖[b, T] f‖_p ≤ C ‖b‖_{BMO} (‖T f‖_p + ‖f‖_p)`
(`TauCeti.eLpNorm_le_mul_eLpNorm_of_sharpMaximalFunction_le`), and the `Lᵖ` bound for `T f` gives
`‖[b, T] f‖_p ≤ C ‖b‖_{BMO} ‖f‖_p`.

For an unbounded `b` this a priori finiteness is not available, so `b` is clipped at the heights
`k : ℕ`. The clippings `b_k = max (-k) (min k b)` are bounded, so `[b_k, T] f ∈ Lᵖ` whenever
`f ∈ Lᵖ`, and `‖b_k‖_{BMO} ≤ 2 ‖b‖_{BMO}` (`TauCeti.bmoSeminorm_max_min_le`). Moreover `b_k f → b f`
in `L²` (`TauCeti.tendsto_eLpNorm_max_min_smul_sub`), so `T (b_k f) → T (b f)` almost everywhere
along a subsequence, and Fatou's lemma passes the uniform bound to `[b, T] f`. Since `T` is given
on `L²`, the theorem is stated for `f ∈ L²` with `b f ∈ L²`, and it is informative for
`f ∈ L² ∩ Lᵖ`; extending `[b, T]` by density to a bounded operator on all of `Lᵖ` is not carried
out here.

## Main declarations

* `TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`: the sharp maximal
  function estimate for `[b, T] f`.
* `TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`: the Coifman–Rochberg–Weiss
  theorem `‖[b, T] f‖_p ≤ C ‖b‖_{BMO} ‖f‖_p`.

## References

* R. R. Coifman, R. Rochberg, G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. **103** (1976), 611–635.
* S. Janson, *Mean oscillation and commutators of singular integral operators*, Ark. Mat. **16**
  (1978), 263–270.
* L. Grafakos, *Modern Fourier Analysis*, Section 3.5.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace TauCeti

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
      eLpNorm_eq_lintegral_rpow_eNorm_toReal (by positivity) ENNReal.ofReal_ne_top hφ, hsR]
    simp_rw [eNorm_smul]
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
          (eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable _).restrict).symm
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
    (hb.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm.mul hf.eNorm
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
          simpa only [g, eNorm_smul] using
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
        ≤ ‖(b y - a) • T f y - T h₁ y‖ₑ + ‖T h₂ y - A₀‖ₑ := eNorm_sub_le
      _ ≤ ‖(b y - a) • T f y‖ₑ + ‖T h₁ y‖ₑ + ‖T h₂ y - A₀‖ₑ := by gcongr; exact eNorm_sub_le
      _ ≤ _ := by rw [eNorm_smul]; gcongr
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
    ((hb.aestronglyMeasurable.sub aestronglyMeasurable_const).eNorm.mul
      (Lp.aestronglyMeasurable _).eNorm).restrict
  have hosc : ⨍⁻ y in B, ‖Φ y - (-A₀)‖ₑ ≤
      commutatorConst n s q A C₀ δ * M * (X ^ q⁻¹ + Y ^ q⁻¹) := by
    rw [setLAverage_eq, ENNReal.div_le_iff hB0 hBtop]
    calc ∫⁻ y in B, ‖Φ y - (-A₀)‖ₑ
        ≤ ∫⁻ y in B, (‖b y - a‖ₑ * ‖T f y‖ₑ + ‖T h₁ y‖ₑ + farConst n q C₀ δ * M * Y ^ q⁻¹) :=
          lintegral_mono_ae hpt
      _ = (∫⁻ y in B, ‖b y - a‖ₑ * ‖T f y‖ₑ) + (∫⁻ y in B, ‖T h₁ y‖ₑ) +
            farConst n q C₀ δ * M * Y ^ q⁻¹ * volume B := by
          rw [lintegral_add_left' (f := fun y => ‖b y - a‖ₑ * ‖T f y‖ₑ + ‖T h₁ y‖ₑ)
            (hbm.add (Lp.aestronglyMeasurable _).eNorm.restrict), lintegral_add_left' hbm,
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
`L¹` bound. Combined with the Fefferman–Stein inequality, a truncation argument and the `Lᵖ`
bounds for the maximal function, it gives the Coifman–Rochberg–Weiss theorem
`TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`. -/
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

/-! ### The Coifman–Rochberg–Weiss theorem -/

open scoped Topology

/-- **The a priori Coifman–Rochberg–Weiss estimate.** Under the hypotheses of
`TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`, with `T` bounded in the
`Lˢ` and the `Lᵖ` norm for `1 ≤ s < p`, the commutator `[b, T] f = b T f - T (b f)` satisfies
`‖[b, T] f‖_p ≤ C ‖b‖_{BMO} ‖f‖_p` whenever it is known to lie in `Lᵖ`. -/
private theorem exists_eLpNorm_smul_sub_le_of_memLp {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {s p : ℝ} (hs : 1 ≤ s) (hsp : s < p) (A C₀ : ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal p) volume ≤ A * eLpNorm h (ENNReal.ofReal p) volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, LocallyIntegrable b volume → bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))), g =ᵐ[volume] (fun y => b y • f y) →
      MemLp (fun y => b y • T f y - T g y) (ENNReal.ofReal p) volume →
      eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) volume ≤
        C * M * eLpNorm f (ENNReal.ofReal p) volume := by
  -- Janson's estimate at the exponent `q = (s + p) / 2`, strictly between `s` and `p`.
  set q := (s + p) / 2
  have hsq : s < q := by simp only [q]; linarith
  have hqp : q < p := by simp only [q]; linarith
  obtain ⟨CJ, hCJ⟩ :=
    exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow (ι := ι) (E := E) (F := F)
      hs hsq A C₀ hδ
  set D : ℝ≥0∞ := (ENNReal.ofReal (2 ^ (p + 1) * 2 ^ ((p + 2 * Fintype.card ι + 2) * p)) *
    maximalFunctionConst (Fintype.card ι) (p / q)) ^ p⁻¹
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by simp only [inv_nonneg]; linarith)
    (by finiteness)
  refine ⟨D.toNNReal * (2 * CJ) * (A + 1),
    fun T K hKm hK hrep hTs hTp b M hb hM f g hg hΦ => ?_⟩
  -- Both maximal functions in Janson's estimate are at most that of `u = ‖T f‖ + ‖f‖`.
  set u : (ι → ℝ) → ℝ := fun y => ‖T f y‖ + ‖f y‖
  have hmono {v : (ι → ℝ) → ℝ≥0∞} (hv : ∀ y, v y ≤ ‖u y‖ₑ) (x : ι → ℝ) :
      maximalFunction volume (fun y => v y ^ q) x ≤
        maximalFunction volume (fun y => ‖u y‖ₑ ^ q) x :=
    maximalFunction_mono_ae (.of_forall fun y => by
      simpa only [eNorm_eq_self] using ENNReal.rpow_le_rpow (hv y) (by linarith))
  have hu (y : ι → ℝ) : ‖u y‖ = ‖T f y‖ + ‖f y‖ := Real.norm_of_nonneg (by positivity)
  have hpt (x : ι → ℝ) : sharpMaximalFunction volume (fun y => b y • T f y - T g y) x ≤
      ↑(2 * CJ * M) * maximalFunction volume (fun y => ‖u y‖ₑ ^ q) x ^ q⁻¹ := by
    calc _ ≤ CJ * M * (maximalFunction volume (fun y => ‖T f y‖ₑ ^ q) x ^ q⁻¹ +
            maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹) :=
          hCJ T hKm hK hrep hTs hb hM f g hg x
      _ ≤ CJ * M * (maximalFunction volume (fun y => ‖u y‖ₑ ^ q) x ^ q⁻¹ +
            maximalFunction volume (fun y => ‖u y‖ₑ ^ q) x ^ q⁻¹) := by
          gcongr <;> first
            | exact inv_nonneg.2 (by linarith)
            | exact hmono (fun y => eNorm_le_iff_norm_le.2 (by simp [hu])) x
      _ = _ := by push_cast; ring
  have key := eLpNorm_le_mul_eLpNorm_of_sharpMaximalFunction_le (by linarith) (by linarith) hqp hΦ
    ((Lp.aestronglyMeasurable _).norm.add (Lp.aestronglyMeasurable _).norm) hpt
  -- `‖u‖_p ≤ ‖T f‖_p + ‖f‖_p ≤ (A + 1) ‖f‖_p`.
  have hu_le :
      eLpNorm u (ENNReal.ofReal p) volume ≤ ↑(A + 1) * eLpNorm f (ENNReal.ofReal p) volume :=
    calc eLpNorm u (ENNReal.ofReal p) volume
        ≤ eLpNorm (T f) (ENNReal.ofReal p) volume + eLpNorm f (ENNReal.ofReal p) volume := by
          rw [← eLpNorm_norm _ (Lp.aestronglyMeasurable (T f)),
            ← eLpNorm_norm _ (Lp.aestronglyMeasurable f)]
          exact eLpNorm_add_le (f := fun y => ‖T f y‖) (g := fun y => ‖f y‖)
            (ENNReal.one_le_ofReal.2 (by linarith : 1 ≤ p))
      _ ≤ A * eLpNorm f (ENNReal.ofReal p) volume + eLpNorm f (ENNReal.ofReal p) volume := by
          gcongr
          exact hTp f
      _ = ↑(A + 1) * eLpNorm f (ENNReal.ofReal p) volume := by push_cast; ring
  calc _ ≤ D * ↑(2 * CJ * M) * eLpNorm u (ENNReal.ofReal p) volume := key
    _ ≤ D * ↑(2 * CJ * M) * (↑(A + 1) * eLpNorm f (ENNReal.ofReal p) volume) := by gcongr
    _ = ↑(D.toNNReal * (2 * CJ) * (A + 1)) * M * eLpNorm f (ENNReal.ofReal p) volume := by
        simp only [ENNReal.coe_mul, ENNReal.coe_toNNReal hD, ENNReal.coe_add, ENNReal.coe_one,
          ENNReal.coe_ofNat]
        ring

omit [Nonempty ι] in
/-- The commutator `b T f - T (b f)` with an a.e. constant function `b = c` vanishes a.e. -/
private theorem smul_sub_ae_eq_zero_of_ae_eq_const {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {b : (ι → ℝ) → ℝ} {c : ℝ} (hc : b =ᵐ[volume] fun _ => c)
    (f g : Lp E 2 (volume : Measure (ι → ℝ))) (hg : g =ᵐ[volume] (fun y => b y • f y)) :
    (fun y => b y • T f y - T g y) =ᵐ[volume] 0 := by
  have hgc : g = c • f := Lp.ext <| hg.trans <| by
    filter_upwards [hc, Lp.coeFn_smul c f] with y hy hy'
    rw [hy, hy', Pi.smul_apply]
  filter_upwards [hc, Lp.coeFn_smul c (T f)] with y hy hy'
  simp only [hgc, map_smul, hy, hy', Pi.smul_apply, sub_self, Pi.zero_apply]

omit [Nonempty ι] in
/-- If `b` is bounded and `f ∈ Lᵖ`, the commutator `b T f - T (b f)` lies in `Lᵖ`. -/
private theorem memLp_smul_sub_of_abs_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume) {p : ℝ≥0∞} {A : ℝ≥0}
    (hTp : ∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
      eLpNorm (T h) p volume ≤ A * eLpNorm h p volume)
    {b : (ι → ℝ) → ℝ} (hb : AEStronglyMeasurable b volume) {k : ℝ} (hbk : ∀ y, |b y| ≤ k)
    (f g : Lp E 2 (volume : Measure (ι → ℝ))) (hg : g =ᵐ[volume] (fun y => b y • f y))
    (hf : eLpNorm f p volume ≠ ∞) :
    MemLp (fun y => b y • T f y - T g y) p volume := by
  have hT (h : Lp E 2 (volume : Measure (ι → ℝ))) (hh : eLpNorm h p volume ≠ ∞) :
      MemLp (T h) p volume :=
    (hTp h).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hh.lt_top)
  have hgp : eLpNorm g p volume ≠ ∞ := by
    rw [eLpNorm_congr_ae hg]
    exact (MemLp.of_le_mul (f := fun y => b y • f y) (lt_top_iff_ne_top.2 hf)
      (hb.smul (Lp.aestronglyMeasurable f)) (.of_forall fun y => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbk y) (norm_nonneg _))).eLpNorm_ne_top
  exact ((hT f hf).of_le_mul (f := fun y => b y • T f y) (hb.smul (Lp.aestronglyMeasurable _))
    (.of_forall fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbk y) (norm_nonneg _))).sub (hT g hgp)

omit [Nonempty ι] in
/-- Let `g_k ∈ L²` be the products `b_k f` of `f ∈ L²` with the clippings
`b_k = max (-k) (min k b)` of `b` at the heights `k : ℕ`, and let `g = b f ∈ L²`. Along a
subsequence, the clipped commutators `b_k T f - T g_k` converge almost everywhere to
`b T f - T g`: `g_k → g` in `L²` (`TauCeti.tendsto_eLpNorm_max_min_smul_sub`), so `T g_k → T g`
in `L²`. -/
private theorem exists_strictMono_ae_tendsto_smul_sub {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {b : (ι → ℝ) → ℝ} (hb : AEStronglyMeasurable b volume)
    (f g : Lp E 2 (volume : Measure (ι → ℝ))) (hg : g =ᵐ[volume] (fun y => b y • f y))
    (gk : ℕ → Lp E 2 (volume : Measure (ι → ℝ)))
    (hgk : ∀ k, gk k =ᵐ[volume] fun y => max (-(k : ℝ)) (min (k : ℝ) (b y)) • f y) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ y, Tendsto
      (fun i => max (-(ns i : ℝ)) (min (ns i : ℝ) (b y)) • T f y - T (gk (ns i)) y) atTop
        (𝓝 (b y • T f y - T g y)) := by
  have hclip (t : ℝ) : Tendsto (fun k : ℕ => max (-(k : ℝ)) (min (k : ℝ) t)) atTop (𝓝 t) :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop |t|] with k hk
      exact (max_neg_min_eq_self_of_abs_le hk).symm
  have hg_lim : Tendsto gk atTop (𝓝 g) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine ((tendsto_eLpNorm_max_min_smul_sub (by simp) hb ((Lp.memLp g).ae_eq hg)).comp
      tendsto_natCast_atTop_atTop).congr fun k => eLpNorm_congr_ae ?_
    filter_upwards [hgk k, hg] with y hy hgy
    simp only [Pi.sub_apply, hy, hgy]
  obtain ⟨ns, hns, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((T.continuous.tendsto g).comp hg_lim)).exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hns_ae] with y hy
  exact (((hclip (b y)).comp hns.tendsto_atTop).smul_const _).sub hy

omit [Nonempty ι] in
/-- **The Coifman–Rochberg–Weiss commutator theorem.** Let `1 ≤ s < p`, `δ > 0`, and let `A`,
`C₀` be constants. There is a constant `C`, depending only on these and the dimension `n`, with
the following property on `ℝⁿ = ι → ℝ` with the sup distance.

Let `T` be a bounded linear operator on `L²` such that `T h x = ∫ K x z (h z) dz` for almost every
`x` in any ball on which `h` vanishes, where the kernel satisfies the standard smoothness estimate
in its first variable,

`‖K x y - K x' y‖ ≤ C₀ dist x x' ^ δ dist y x' ^ (-(n + δ))` whenever `dist y x' > 2 dist x x'`,

and such that `‖T h‖_s ≤ A ‖h‖_s` and `‖T h‖_p ≤ A ‖h‖_p` for `h ∈ L²`. Let `b` be locally
integrable with `‖b‖_{BMO} ≤ M`, and let `f, g ∈ L²` with `g = b f`. Then the commutator
`[b, T] f = b T f - T (b f)` satisfies

`‖[b, T] f‖_p ≤ C M ‖f‖_p`.

Operators that, together with their adjoints, satisfy the Calderón–Zygmund cancellation
condition are bounded in every `Lʳ` norm, `1 < r < ∞`, uniformly over operators with the same
bounds (`TauCeti.exists_eLpNorm_le_of_setLIntegral_compl_closedBall_le`), so they satisfy the `Lˢ`
and `Lᵖ` hypotheses for every `1 < s < p < ∞`.
Since `T` is given on `L²`, the estimate is stated for `f ∈ L²` and `b f ∈ L²`; it is informative
for `f ∈ L² ∩ Lᵖ`, and the right-hand side does not involve any bound on `b` beyond its BMO
seminorm. -/
theorem exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {s p : ℝ} (hs : 1 ≤ s) (hsp : s < p) (A C₀ : ℝ≥0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal p) volume ≤ A * eLpNorm h (ENNReal.ofReal p) volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, LocallyIntegrable b volume → bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))), g =ᵐ[volume] (fun y => b y • f y) →
      eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) volume ≤
        C * M * eLpNorm f (ENNReal.ofReal p) volume := by
  -- In dimension zero `b` is constant, and `[b, T] f = b T f - T (b f) = 0`.
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨0, fun T K _ _ _ _ _ b M _ _ f g hg => ?_⟩
    rw [eLpNorm_congr_ae (smul_sub_ae_eq_zero_of_ae_eq_const T (c := b default)
      (.of_forall fun y => congrArg b (Subsingleton.elim _ _)) f g hg), eLpNorm_zero]
    exact zero_le
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_smul_sub_le_of_memLp (ι := ι) (E := E) (F := F) hs hsp A C₀ hδ
  refine ⟨2 * C₁ + 1, fun T K hKm hK hrep hTs hTp b M hb hM f g hg => ?_⟩
  have hbm := hb.aestronglyMeasurable
  -- If `‖b‖_{BMO} = 0`, then `b` is a.e. a constant `c` and `[b, T] f = c T f - T (c f) = 0`.
  rcases eq_or_ne M 0 with rfl | hM0
  · obtain ⟨c, hc⟩ := (bmoSeminorm_eq_zero_iff hb).1 (le_zero_iff.1 (by simpa using hM))
    rw [eLpNorm_congr_ae (smul_sub_ae_eq_zero_of_ae_eq_const T hc f g hg), eLpNorm_zero]
    exact zero_le
  -- If `f ∉ Lᵖ`, the right-hand side is infinite.
  by_cases hf : eLpNorm f (ENNReal.ofReal p) volume = ∞
  · rw [hf, ENNReal.mul_top (mul_ne_zero (by simp) (ENNReal.coe_ne_zero.2 hM0))]
    exact le_top
  -- Otherwise clip `b` at the heights `k`: the clippings `b_k` are bounded, so the clipped
  -- commutators lie in `Lᵖ`, and `‖b_k‖_{BMO} ≤ 2 ‖b‖_{BMO}`.
  set bk : ℕ → (ι → ℝ) → ℝ := fun k y => max (-(k : ℝ)) (min (k : ℝ) (b y))
  have hbkm (k : ℕ) : AEStronglyMeasurable (bk k) volume :=
    (continuous_const.max (continuous_const.min continuous_id)).comp_aestronglyMeasurable hbm
  have hbk (k : ℕ) (y : ι → ℝ) : |bk k y| ≤ k :=
    (abs_max_min_le _ _).trans_eq (abs_of_nonneg k.cast_nonneg)
  have hmem (k : ℕ) : MemLp (fun y => bk k y • f y) 2 volume :=
    (Lp.memLp f).of_le_mul (c := k) ((hbkm k).smul (Lp.aestronglyMeasurable f))
      (.of_forall fun y => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbk k y) (norm_nonneg _))
  set gk : ℕ → Lp E 2 (volume : Measure (ι → ℝ)) := fun k => (hmem k).toLp _
  have hgk (k : ℕ) : gk k =ᵐ[volume] fun y => bk k y • f y := (hmem k).coeFn_toLp
  have hbound (k : ℕ) : eLpNorm (fun y => bk k y • T f y - T (gk k) y) (ENNReal.ofReal p) volume ≤
      C₁ * ↑(2 * M) * eLpNorm f (ENNReal.ofReal p) volume := by
    refine hC₁ T hKm hK hrep hTs hTp ?_ ?_ f (gk k) (hgk k)
      (memLp_smul_sub_of_abs_le T hTp (hbkm k) (hbk k) f (gk k) (hgk k) hf)
    · exact hb.mono (hbkm k) (.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using abs_max_min_le_abs k.cast_nonneg (b y))
    · refine (bmoSeminorm_max_min_le hbm k).trans ?_
      push_cast
      gcongr
  -- Along a subsequence the clipped commutators converge a.e., and Fatou's lemma concludes.
  obtain ⟨ns, -, hlim⟩ := exists_strictMono_ae_tendsto_smul_sub T hbm f g hg gk hgk
  calc eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) volume
      ≤ atTop.liminf fun i =>
          eLpNorm (fun y => bk (ns i) y • T f y - T (gk (ns i)) y) (ENNReal.ofReal p) volume :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm (fun i => ((hbkm _).smul
          (Lp.aestronglyMeasurable _)).sub (Lp.aestronglyMeasurable _)) _
          ((hbm.smul (Lp.aestronglyMeasurable _)).sub (Lp.aestronglyMeasurable _)) hlim
    _ ≤ C₁ * ↑(2 * M) * eLpNorm f (ENNReal.ofReal p) volume :=
        liminf_le_of_frequently_le' (.of_forall fun i => hbound _)
    _ ≤ ↑(2 * C₁ + 1) * M * eLpNorm f (ENNReal.ofReal p) volume := by
        refine mul_le_mul' ?_ le_rfl
        push_cast
        calc (C₁ : ℝ≥0∞) * (2 * M) = 2 * C₁ * M := by ring
          _ ≤ (2 * C₁ + 1) * M := by gcongr; exact le_self_add

end TauCeti
