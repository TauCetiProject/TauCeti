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
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Cutoff
import TauCeti.MeasureTheory.Function.BoundedMeanOscillation.Truncation
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Operator.Extension
import TauCeti.MeasureTheory.Function.LpSeminorm.Clipping
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.StronglyMeasurable.SpanningSets
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Commutators of singular integral operators with functions of bounded mean oscillation

Let `T` be a singular integral operator on `ℝⁿ = ι → ℝ`, and let `b` have bounded mean
oscillation. The **commutator** of `T` with multiplication by `b` is

`[b, T] f = b T f - T (b f)`.

Coifman, Rochberg and Weiss proved that `[b, T]` is bounded on `Lᵖ` for `1 < p < ∞`, with norm
`O(‖b‖_{BMO})`. This is the perturbative engine of the `W^{1,p}` and `W^{2,p}` theories of elliptic
equations whose coefficients have vanishing mean oscillation: freezing a coefficient `a` at a
point leaves an error that is a commutator `[a, T]` of a Calderón–Zygmund operator with `a`.

This file proves that theorem (`TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`),
following Janson's proof. Its core is a pointwise estimate: for `1 < q < ∞` and `n ≥ 1`,

`([b, T] f)^# x ≤ C ‖b‖_{BMO} ((M(‖T f‖^q) x)^{1/q} + (M(‖f‖^q) x)^{1/q})`

at every point `x` (`TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`),
where `^#` is the sharp maximal function and `M` the centred Hardy–Littlewood maximal function.
The operator `T` is bounded on `L²`, given away from the support of its argument by a kernel `K`
with the standard smoothness estimate in its first variable, and bounded in some `Lˢ` norm with
`1 ≤ s < q`; the commutator theorem also uses a bound in the `Lᵖ` norm. Calderón–Zygmund
operators satisfy the `Lˢ` bound for every `1 < s < q`; the case `s = 1` requires an additional
strong `L¹` bound. Balls are taken in the sup distance, so that they are cubes.

## The pointwise estimate

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

## The `Lᵖ` bound

Fix `s < q < p`. The Fefferman–Stein inequality `TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction`
bounds `‖h‖_p` by `‖h^#‖_p` for `h ∈ Lᵖ`, and `(M(‖·‖^q))^{1/q}` is bounded on `Lᵖ`
(`TauCeti.eLpNorm_maximalFunction_rpow_rpow_inv_le`). Together with the pointwise estimate and the
`Lᵖ` bound for `T` they give `‖[b, T] f‖_p ≤ C ‖b‖_{BMO} ‖f‖_p` as soon as `[b, T] f ∈ Lᵖ`. This a
priori integrability holds for the clipped multipliers `bₖ = max (-k) (min k b)`, whose BMO
seminorm is at most `2 ‖b‖_{BMO}` (`TauCeti.bmoSeminorm_max_min_le`), and for the bounded
truncations `fₖ = 1_{Sₖ} f` with `Sₖ = spanningSets volume k ∩ {‖f‖ ≤ k}`. As `k → ∞`,
`fₖ → f` and `bₖ fₖ → b f` in `L²` by dominated convergence, so `T fₖ → T f` and
`T (bₖ fₖ) → T (b f)` almost everywhere along a subsequence, and the uniform bound passes to
`[b, T] f` by Fatou's lemma. In dimension `0` the commutator vanishes.

## The commutator on `Lᵖ`

Since `T` is only given on `L²`, and `b f` need not lie in `L²` for unbounded `b`, the bound above
is stated for `f ∈ L²` with `b f ∈ L²`. Among these, the `f ∈ Lᵖ` are dense in `Lᵖ`: truncating
`f` to the sets where `‖f‖` and `|b|` are at most `k`, inside sets of finite measure, gives such
functions converging to `f` in `Lᵖ`. So `[b, T]` extends uniquely to a bounded operator on `Lᵖ`
of norm `O(‖b‖_{BMO})`
(`TauCeti.exists_continuousLinearMap_apply_ae_eq_smul_sub_of_norm_sub_le_mul_rpow`), which is the
Coifman–Rochberg–Weiss theorem in its operator form.

## The small-radius estimate

On a ball `B = B(x₀, r)`, the commutator only sees `b` on `B`, up to an additive constant. There
`b` agrees, up to a constant, with a function of BMO seminorm `O(η_b(16 r))`
(`MeasureTheory.LocallyIntegrable.exists_bmoSeminorm_le_and_eqOn`), where `η_b` is the VMO modulus
of `b`. Hence `‖[b, T] f‖_{Lᵖ(B)} ≤ C η_b(16 r) ‖f‖_p` for `f` vanishing off `B`
(`TauCeti.exists_eLpNorm_restrict_ball_smul_sub_le_of_vmoModulus_le`). For `b` of vanishing mean
oscillation this is small for small balls, which is how the commutator theorem perturbs equations
with such coefficients.

## Main declarations

* `TauCeti.exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow`: the sharp maximal
  function estimate for `[b, T] f`.
* `TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`: the Coifman–Rochberg–Weiss
  theorem, `‖[b, T] f‖_p ≤ C ‖b‖_{BMO} ‖f‖_p` for `f ∈ L²` with `b f ∈ L²`.
* `TauCeti.exists_continuousLinearMap_apply_ae_eq_smul_sub_of_norm_sub_le_mul_rpow`: `[b, T]`
  extends uniquely to a bounded operator on `Lᵖ` with norm at most `C ‖b‖_{BMO}`.
* `TauCeti.exists_eLpNorm_restrict_ball_smul_sub_le_of_vmoModulus_le`: the **small-radius
  commutator estimate** `‖[b, T] f‖_{Lᵖ(B)} ≤ C η_b(16 r) ‖f‖_p` on a ball `B` of radius `r`, for
  `f` vanishing off `B`, where `η_b` is the VMO modulus of `b`.

## References

* R. R. Coifman, R. Rochberg, G. Weiss, *Factorization theorems for Hardy spaces in several
  variables*, Ann. of Math. **103** (1976), 611–635.
* S. Janson, *Mean oscillation and commutators of singular integral operators*, Ark. Mat. **16**
  (1978), 263–270.
* L. Grafakos, *Modern Fourier Analysis*, Section 3.5.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

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
`L¹` bound. Combined with the Fefferman–Stein inequality, an approximation argument and the `Lᵖ`
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

/-- The constant in the `Lᵖ` Fefferman–Stein inequality `eLpNorm_le_eLpNorm_sharpMaximalFunction`
in dimension `n`. -/
private noncomputable def feffermanSteinConst (n : ℕ) (p : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 ^ (p + 1) * 2 ^ ((p + 2 * n + 2) * p)) ^ (1 / p)

/-- **Integrating a sharp function estimate.** Let `1 < p` and `0 < q < p`. If `h ∈ Lᵖ` satisfies

`h^# ≤ c ((M(‖u‖^q))^{1/q} + (M(‖v‖^q))^{1/q})`

everywhere, then `‖h‖_p` is at most `c (‖u‖_p + ‖v‖_p)` times the Fefferman–Stein constant and
the constant of the `Lᵖ` bound for `(M(‖·‖^q))^{1/q}`. -/
private theorem eLpNorm_le_of_sharpMaximalFunction_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hqp : q < p)
    {h u : (ι → ℝ) → F} {v : (ι → ℝ) → G} (hh : MemLp h (ENNReal.ofReal p) volume)
    (hu : AEStronglyMeasurable u volume) (hv : AEStronglyMeasurable v volume) (c : ℝ≥0∞)
    (hbound : ∀ x, sharpMaximalFunction volume h x ≤
      c * (maximalFunction volume (fun y => ‖u y‖ₑ ^ q) x ^ q⁻¹ +
        maximalFunction volume (fun y => ‖v y‖ₑ ^ q) x ^ q⁻¹)) :
    eLpNorm h (ENNReal.ofReal p) volume ≤
      feffermanSteinConst (Fintype.card ι) p * c *
        maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) *
          (eLpNorm u (ENNReal.ofReal p) volume + eLpNorm v (ENNReal.ofReal p) volume) := by
  have hpR : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hp' : 1 < ENNReal.ofReal p := by simpa using hp
  set Mu : (ι → ℝ) → ℝ≥0∞ := fun x => maximalFunction volume (fun y => ‖u y‖ₑ ^ q) x ^ q⁻¹
  set Mv : (ι → ℝ) → ℝ≥0∞ := fun x => maximalFunction volume (fun y => ‖v y‖ₑ ^ q) x ^ q⁻¹
  have hcard : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℝ
  calc eLpNorm h (ENNReal.ofReal p) volume
      ≤ feffermanSteinConst (Fintype.card ι) p *
          eLpNorm (sharpMaximalFunction volume h) (ENNReal.ofReal p) volume := by
        simpa only [hpR, feffermanSteinConst] using
          eLpNorm_le_eLpNorm_sharpMaximalFunction hh hp'.le le_rfl hp' ENNReal.ofReal_ne_top
    _ ≤ feffermanSteinConst (Fintype.card ι) p *
          eLpNorm (fun x => c * (Mu + Mv) x) (ENNReal.ofReal p) volume := by
        gcongr
        exact eLpNorm_mono_eNorm (measurable_sharpMaximalFunction _ _).aestronglyMeasurable
          fun x => by simpa only [eNorm_eq_self, Pi.add_apply, Mu, Mv] using hbound x
    _ ≤ feffermanSteinConst (Fintype.card ι) p *
          (c * (eLpNorm Mu (ENNReal.ofReal p) volume + eLpNorm Mv (ENNReal.ofReal p) volume)) := by
        rw [eLpNorm_const_mul_ennreal_of_pos (by positivity)]
        gcongr
        exact eLpNorm_add_le hp'.le
    _ ≤ feffermanSteinConst (Fintype.card ι) p *
          (c * (maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) *
              eLpNorm u (ENNReal.ofReal p) volume +
            maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) *
              eLpNorm v (ENNReal.ofReal p) volume)) := by
        gcongr
        · have h := eLpNorm_maximalFunction_rpow_rpow_inv_le (p := ENNReal.ofReal p) volume
            hu.eNorm hq (by rwa [hpR])
          rwa [hpR, hcard] at h
        · have h := eLpNorm_maximalFunction_rpow_rpow_inv_le (p := ENNReal.ofReal p) volume
            hv.eNorm hq (by rwa [hpR])
          rwa [hpR, hcard] at h
    _ = _ := by ring

/-- **The commutator estimate for data in `Lᵖ`.** Let `1 < p`, `0 < q < p`, let `T` be bounded in
the `Lᵖ` norm with constant `Aₚ` on `L²`, let `b` be essentially bounded, and let `f, g ∈ L² ∩ Lᵖ`.
If `([b, T] f)^# ≤ c ((M(‖T f‖^q))^{1/q} + (M(‖f‖^q))^{1/q})`, where `[b, T] f = b T f - T g`,
then `‖[b, T] f‖_p ≤ C c (Aₚ + 1) ‖f‖_p`. The boundedness of `b` and the integrability of `f` and
`g` make `[b, T] f` an `Lᵖ` function, as the Fefferman–Stein inequality requires. -/
private theorem eLpNorm_smul_sub_le_of_sharpMaximalFunction_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {p q : ℝ} (hp : 1 < p) (hq : 0 < q) (hqp : q < p) {Aₚ : ℝ≥0}
    (hTp : ∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
      eLpNorm (T h) (ENNReal.ofReal p) volume ≤ Aₚ * eLpNorm h (ENNReal.ofReal p) volume)
    {b : (ι → ℝ) → ℝ} (hb : MemLp b ∞ volume) {f g : Lp E 2 (volume : Measure (ι → ℝ))}
    (hf : MemLp f (ENNReal.ofReal p) volume) (hg : MemLp g (ENNReal.ofReal p) volume) (c : ℝ≥0∞)
    (hbound : ∀ x, sharpMaximalFunction volume (fun y => b y • T f y - T g y) x ≤
      c * (maximalFunction volume (fun y => ‖T f y‖ₑ ^ q) x ^ q⁻¹ +
        maximalFunction volume (fun y => ‖f y‖ₑ ^ q) x ^ q⁻¹)) :
    eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) volume ≤
      feffermanSteinConst (Fintype.card ι) p * c *
        maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) * (Aₚ + 1) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  have hTmem (u : Lp E 2 (volume : Measure (ι → ℝ))) (hu : MemLp u (ENNReal.ofReal p) volume) :
      MemLp (T u) (ENNReal.ofReal p) volume :=
    (hTp u).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hu.eLpNorm_lt_top)
  calc eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) volume
      ≤ feffermanSteinConst (Fintype.card ι) p * c *
          maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) *
            (eLpNorm (T f) (ENNReal.ofReal p) volume + eLpNorm f (ENNReal.ofReal p) volume) :=
        eLpNorm_le_of_sharpMaximalFunction_le hp hq hqp ((hb.smul (hTmem f hf)).sub (hTmem g hg))
          (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) c hbound
    _ ≤ feffermanSteinConst (Fintype.card ι) p * c *
          maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) *
            (Aₚ * eLpNorm f (ENNReal.ofReal p) volume + eLpNorm f (ENNReal.ofReal p) volume) := by
        gcongr
        exact hTp f
    _ = _ := by ring

omit [Nonempty ι] in
/-- **Passing to the limit in commutators.** Let `bₖ → b` pointwise and `fₖ → f`, `gₖ → g` in
`L²`. If the functions `bₖ T fₖ - T gₖ` all have `Lᵖ` seminorm at most `B`, then so does
`b T f - T g`, by Fatou's lemma along a subsequence on which `T fₖ` and `T gₖ` converge almost
everywhere. -/
private theorem eLpNorm_smul_sub_le_of_tendsto {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {p : ℝ≥0∞} {bs : ℕ → (ι → ℝ) → ℝ} {b : (ι → ℝ) → ℝ}
    (hbs : ∀ k, AEStronglyMeasurable (bs k) volume) (hb : AEStronglyMeasurable b volume)
    (hbs_lim : ∀ y, Tendsto (fun k => bs k y) atTop (𝓝 (b y)))
    {fs gs : ℕ → Lp E 2 (volume : Measure (ι → ℝ))} {f g : Lp E 2 (volume : Measure (ι → ℝ))}
    (hfs : Tendsto fs atTop (𝓝 f)) (hgs : Tendsto gs atTop (𝓝 g)) {B : ℝ≥0∞}
    (hB : ∀ k, eLpNorm (fun y => bs k y • T (fs k) y - T (gs k) y) p volume ≤ B) :
    eLpNorm (fun y => b y • T f y - T g y) p volume ≤ B := by
  obtain ⟨ns₁, hns₁, h₁⟩ :=
    (tendstoInMeasure_of_tendsto_Lp ((T.continuous.tendsto f).comp hfs)).exists_seq_tendsto_ae
  obtain ⟨ns₂, hns₂, h₂⟩ := ((tendstoInMeasure_of_tendsto_Lp
    ((T.continuous.tendsto g).comp hgs)).comp hns₁.tendsto_atTop).exists_seq_tendsto_ae
  have hφ : Tendsto (fun k => ns₁ (ns₂ k)) atTop atTop :=
    hns₁.tendsto_atTop.comp hns₂.tendsto_atTop
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop)
    (f := fun k y => bs (ns₁ (ns₂ k)) y • T (fs (ns₁ (ns₂ k))) y - T (gs (ns₁ (ns₂ k))) y)
    (.of_forall fun k => hB _)
    (fun k => ((hbs _).smul (Lp.aestronglyMeasurable _)).sub (Lp.aestronglyMeasurable _))
    ((hb.smul (Lp.aestronglyMeasurable _)).sub (Lp.aestronglyMeasurable _)) ?_
  filter_upwards [h₁, h₂] with y hy₁ hy₂
  exact (((hbs_lim y).comp hφ).smul (hy₁.comp hns₂.tendsto_atTop)).sub hy₂

omit [Nonempty ι] in
/-- In dimension `0` the space is a point, so `g = b f` is a scalar multiple of `f` and the
commutator `b T f - T g` vanishes. -/
private theorem smul_sub_ae_eq_zero_of_isEmpty [IsEmpty ι] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {b : (ι → ℝ) → ℝ} {f g : Lp E 2 (volume : Measure (ι → ℝ))}
    (hg : g =ᵐ[volume] (fun y => b y • f y)) :
    (fun y => b y • T f y - T g y) =ᵐ[volume] 0 := by
  obtain ⟨x₀⟩ : Nonempty (ι → ℝ) := inferInstance
  have hgf : g = b x₀ • f := by
    refine Lp.ext (hg.trans ?_)
    filter_upwards [Lp.coeFn_smul (b x₀) f] with y hy
    rw [hy, Pi.smul_apply, Subsingleton.elim y x₀]
  have hTg : T g = b x₀ • T f := by rw [hgf, map_smul]
  filter_upwards [Lp.coeFn_smul (b x₀) (T f)] with y hy
  rw [hTg, hy, Pi.smul_apply, Subsingleton.elim y x₀, sub_self, Pi.zero_apply]

omit [Nonempty ι] in
/-- **Reduction to bounded data.** Let `g = b f` with `f, g ∈ L²`. If, for every `k`, the
commutator with the clipped multiplier `bₖ = max (-k) (min k b)` satisfies
`‖bₖ T F - T G‖_p ≤ B ‖F‖_p` for all `F, G ∈ L² ∩ Lᵖ` with `G = bₖ F`, then
`‖b T f - T g‖_p ≤ B ‖f‖_p`. The data are approximated by bounded truncations supported in sets of
finite measure, and the estimate passes to the limit by `eLpNorm_smul_sub_le_of_tendsto`. -/
private theorem eLpNorm_smul_sub_le_of_forall_max_min {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
    {p : ℝ≥0∞} {b : (ι → ℝ) → ℝ} (hb : AEStronglyMeasurable b volume)
    {f g : Lp E 2 (volume : Measure (ι → ℝ))} (hg : g =ᵐ[volume] (fun y => b y • f y))
    {B : ℝ≥0∞} (hB : ∀ (k : ℕ) (F G : Lp E 2 (volume : Measure (ι → ℝ))), MemLp F p volume →
      MemLp G p volume → G =ᵐ[volume] (fun y => max (-(k : ℝ)) (min k (b y)) • F y) →
      eLpNorm (fun y => max (-(k : ℝ)) (min k (b y)) • T F y - T G y) p volume ≤
        B * eLpNorm F p volume) :
    eLpNorm (fun y => b y • T f y - T g y) p volume ≤ B * eLpNorm f p volume := by
  set bs : ℕ → (ι → ℝ) → ℝ := fun k y => max (-(k : ℝ)) (min k (b y))
  have hbsm (k : ℕ) : AEStronglyMeasurable (bs k) volume :=
    (by fun_prop : Continuous fun t : ℝ => max (-(k : ℝ)) (min k t)).comp_aestronglyMeasurable hb
  have hbs_lim (y : ι → ℝ) : Tendsto (fun k => bs k y) atTop (𝓝 (b y)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop ⌈|b y|⌉₊).mono fun k hk =>
      (max_neg_min_eq_self_of_abs_le (Nat.ceil_le.1 hk)).symm)
  -- Truncate `f` to `Sₖ ∩ {‖f‖ ≤ k}`, where the `Sₖ` are spanning sets of finite measure.
  have hfm := Lp.stronglyMeasurable f
  set fs : ℕ → (ι → ℝ) → E := fun k => (spanningSets volume k ∩ {y | ‖f y‖ ≤ k}).indicator f
  have hfsm (k : ℕ) : AEStronglyMeasurable (fs k) volume :=
    (hfm.indicator (measurableSet_spanningSets_inter_norm_le hfm k)).aestronglyMeasurable
  have hfs_bd (k : ℕ) (y : ι → ℝ) : ‖fs k y‖ ≤ k := by
    by_cases hy : y ∈ spanningSets volume k ∩ {y | ‖f y‖ ≤ k} <;> simp_all [fs]
  have hfs_supp (k : ℕ) (y : ι → ℝ) (hy : y ∉ spanningSets volume k) : fs k y = 0 :=
    indicator_of_notMem (s := spanningSets volume k ∩ _) (fun h => hy h.1) _
  have hfs (k : ℕ) (r : ℝ≥0∞) : MemLp (fs k) r volume :=
    memLp_of_norm_le_of_measure_support_ne_top (hfsm k) (.of_forall (hfs_bd k))
      (measure_spanningSets_lt_top volume k).ne (hfs_supp k) r
  have hgs (k : ℕ) (r : ℝ≥0∞) : MemLp (fun y => bs k y • fs k y) r volume := by
    refine memLp_of_norm_le_of_measure_support_ne_top (u := fun y => bs k y • fs k y)
      (c := k * k) ((hbsm k).smul (hfsm k)) (.of_forall fun y => ?_)
      (measure_spanningSets_lt_top volume k).ne (fun y hy => ?_) r
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul ((abs_max_min_le _ _).trans_eq (Nat.abs_cast k)) (hfs_bd k y)
        (norm_nonneg _) (Nat.cast_nonneg _)
    · simp [hfs_supp k y hy]
  refine eLpNorm_smul_sub_le_of_tendsto T hbsm hb hbs_lim
    (tendsto_toLp_of_ae_tendsto_of_norm_le (by simp) (fun k => hfs k 2) EventuallyEq.rfl
      (fun k => .of_forall fun y => norm_indicator_le_norm_self _ y)
      (.of_forall (tendsto_indicator_spanningSets_inter_norm_le f)))
    (tendsto_toLp_of_ae_tendsto_of_norm_le (by simp) (fun k => hgs k 2) hg
      (fun k => .of_forall fun y => ?_)
      (.of_forall fun y => (hbs_lim y).smul (tendsto_indicator_spanningSets_inter_norm_le f y)))
    fun k => ?_
  · simp only [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_max_min_le_abs (Nat.cast_nonneg k) (b y))
      (norm_indicator_le_norm_self _ _) (norm_nonneg _) (abs_nonneg _)
  calc _ ≤ B * eLpNorm ((hfs k 2).toLp (fs k)) p volume :=
        hB k _ _ ((hfs k _).ae_eq (hfs k 2).coeFn_toLp.symm)
          ((hgs k _).ae_eq (hgs k 2).coeFn_toLp.symm)
          ((hgs k 2).coeFn_toLp.trans ((hfs k 2).coeFn_toLp.mono fun y hy => by simp only [hy, bs]))
    _ ≤ B * eLpNorm f p volume := by
        gcongr
        rw [eLpNorm_congr_ae (hfs k 2).coeFn_toLp]
        exact eLpNorm_mono_eNorm (hfsm k) fun y =>
          eNorm_le_iff_norm_le.2 (norm_indicator_le_norm_self _ _)

omit [Nonempty ι] in
/-- **The Coifman–Rochberg–Weiss theorem.** Let `1 ≤ s < p`, `δ > 0`, and let `A`, `Aₚ`, `C₀` be
constants. There is a constant `C`, depending only on these and the dimension `n`, with the
following property on `ℝⁿ = ι → ℝ` with the sup distance.

Let `T` be a bounded linear operator on `L²` such that `T h x = ∫ K x z (h z) dz` for almost every
`x` in any ball on which `h` vanishes, where the kernel satisfies the standard smoothness estimate
in its first variable,

`‖K x y - K x' y‖ ≤ C₀ dist x x' ^ δ dist y x' ^ (-(n + δ))` whenever `dist y x' > 2 dist x x'`,

and such that `‖T h‖_s ≤ A ‖h‖_s` and `‖T h‖_p ≤ Aₚ ‖h‖_p` for `h ∈ L²`. Let `b` be almost
everywhere strongly measurable with `‖b‖_{BMO} ≤ M`, and let `f, g ∈ L²` with `g = b f`. Then the
commutator
`[b, T] f = b T f - T (b f)` satisfies

`‖[b, T] f‖_p ≤ C M ‖f‖_p`.

Calderón–Zygmund operators with a standard kernel whose adjoint also has one satisfy the hypotheses
for every `1 < s < p < ∞`, with the `Lˢ` and `Lᵖ` bounds supplied by the Calderón–Zygmund theorem.
Since `T` is only given on `L²`, the commutator is stated for `f ∈ L²` with `b f ∈ L²`; neither
`f ∈ Lᵖ` nor any integrability of the commutator is assumed. -/
theorem exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s p : ℝ} (hs : 1 ≤ s)
    (hsp : s < p) (A Aₚ C₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal p) volume ≤ Aₚ * eLpNorm h (ENNReal.ofReal p) volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, AEStronglyMeasurable b volume → bmoSeminorm b volume ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))), g =ᵐ[volume] (fun y => b y • f y) →
        eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) volume ≤
          C * M * eLpNorm f (ENNReal.ofReal p) volume := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨0, fun T K _ _ _ _ _ b M _ _ f g hg => ?_⟩
    rw [eLpNorm_congr_ae (smul_sub_ae_eq_zero_of_isEmpty T hg), eLpNorm_zero]
    exact zero_le
  -- Janson's estimate, with an auxiliary exponent `s < q < p`, runs through the Fefferman–Stein
  -- inequality for clipped multipliers and bounded data, and the estimate passes to the limit.
  set q := (s + p) / 2
  have hsq : s < q := by simp only [q]; linarith
  have hqp : q < p := by simp only [q]; linarith
  obtain ⟨C₁, hC₁⟩ := exists_sharpMaximalFunction_smul_sub_le_of_norm_sub_le_mul_rpow
    (ι := ι) (E := E) (F := F) hs hsq A C₀ hδ
  set C : ℝ≥0∞ := feffermanSteinConst (Fintype.card ι) p *
    C₁ * 2 * maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) * (Aₚ + 1)
  have hC : C ≠ ∞ := by
    have hp0 : 0 ≤ 1 / p := one_div_nonneg.2 (by linarith)
    simp only [C, feffermanSteinConst]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top) (by simp)) (by simp))
      (ENNReal.rpow_ne_top_of_nonneg hp0 (maximalFunctionConst_ne_top _ _))) (by simp)
  refine ⟨C.toNNReal, fun T K hKm hK hrep hT hTp b M hb hM f g hg => ?_⟩
  rw [ENNReal.coe_toNNReal hC]
  refine eLpNorm_smul_sub_le_of_forall_max_min T hb hg fun k F G hF hG hGF => ?_
  -- The clipped multiplier has `‖bₖ‖_{BMO} ≤ 2 M`.
  have hbk : bmoSeminorm (fun y => max (-(k : ℝ)) (min k (b y))) volume ≤
      ((2 * M : ℝ≥0) : ℝ≥0∞) :=
    (bmoSeminorm_max_min_le hb k).trans (by push_cast; gcongr)
  calc _ ≤ feffermanSteinConst (Fintype.card ι) p *
          (C₁ * ((2 * M : ℝ≥0) : ℝ≥0∞)) * maximalFunctionConst (Fintype.card ι) (p / q) ^ (1 / p) *
            (Aₚ + 1) * eLpNorm F (ENNReal.ofReal p) volume :=
        eLpNorm_smul_sub_le_of_sharpMaximalFunction_le T (by linarith) (by linarith) hqp hTp
          (hb.memLp_top_max_min k) hF hG _
          (hC₁ T hKm hK hrep hT ((hb.memLp_top_max_min k).locallyIntegrable le_top) hbk _ _ hGF)
    _ = C * M * eLpNorm F (ENNReal.ofReal p) volume := by
        simp only [C]
        push_cast
        ring

omit [Nonempty ι] in
/-- **The small-radius commutator estimate.** Let `ℝⁿ = ι → ℝ` carry the sup distance, let
`1 ≤ s < p`, and let `T` be an operator as in
`TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`. Then for every locally integrable
`b`, every ball `B = B(x₀, r)` and every `f ∈ L²` vanishing off `B`, with `b f ∈ L²`,

`‖[b, T] f‖_{Lᵖ(B)} = ‖b T f - T (b f)‖_{Lᵖ(B)} ≤ C η_b(16 r) ‖f‖_p`,

where `η_b` is the VMO modulus of `b`, bounded here by `M`, and `C` depends only on
`n = Fintype.card ι`, `s`, `p`, `A`, `Aₚ`, `C₀` and `δ`. For `b` of vanishing mean oscillation the
bound `‖[b, T] f‖_{Lᵖ(B)} ≤ C η_b(16 r) ‖f‖_p` is therefore small for small balls `B`, uniformly in
their centre, for all such `f`. -/
theorem exists_eLpNorm_restrict_ball_smul_sub_le_of_vmoModulus_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s p : ℝ} (hs : 1 ≤ s)
    (hsp : s < p) (A Aₚ C₀ : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal p) volume ≤ Aₚ * eLpNorm h (ENNReal.ofReal p) volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, LocallyIntegrable b volume → ∀ (x₀ : ι → ℝ) (r : ℝ),
      vmoModulus b volume (16 * r) ≤ M →
      ∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))), (∀ᵐ y, y ∉ ball x₀ r → f y = 0) →
      g =ᵐ[volume] (fun y => b y • f y) →
      eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) (volume.restrict (ball x₀ r)) ≤
        C * M * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC⟩ := exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow (ι := ι) (E := E) (F := F)
    hs hsp A Aₚ C₀ hδ
  set n := Module.finrank ℝ (ι → ℝ)
  refine ⟨C * (2 + 20 * 8 ^ n), fun T K hKm hK hrep hTs hTp b M hb x₀ r hM f g hf hg => ?_⟩
  -- Replace `b` by a function `b'` of bounded mean oscillation with `b' = b - κ` on `B(x₀, r)`.
  obtain ⟨b', κ, hb'i, hbmo, hb'⟩ := hb.exists_bmoSeminorm_le_and_eqOn x₀ r
  replace hbmo : bmoSeminorm b' volume ≤ (((2 + 20 * 8 ^ n) * M : ℝ≥0) : ℝ≥0∞) := by
    refine hbmo.trans ?_
    push_cast
    gcongr
  -- `b' f = b f - κ f`, since `f` vanishes off `B(x₀, r)`.
  set g' : Lp E 2 (volume : Measure (ι → ℝ)) := g - κ • f
  have hg' : g' =ᵐ[volume] fun y => b' y • f y := by
    filter_upwards [Lp.coeFn_sub g (κ • f), Lp.coeFn_smul κ f, hf, hg] with y h1 h2 h3 h4
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h4]
    by_cases hy : y ∈ ball x₀ r
    · rw [hb' hy, sub_smul]
    · simp [h3 hy]
  -- On `B(x₀, r)`, the commutators with `b` and with `b'` agree.
  have heq : (fun y => b y • T f y - T g y) =ᵐ[volume.restrict (ball x₀ r)]
      fun y => b' y • T f y - T g' y := by
    have hTg' : T g' = T g - κ • T f := by simp [g', map_sub, map_smul]
    rw [hTg']
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (Lp.coeFn_sub (T g) (κ • T f)),
      ae_restrict_of_ae (Lp.coeFn_smul κ (T f))] with y hy h1 h2
    rw [h1, Pi.sub_apply, h2, Pi.smul_apply, hb' hy, sub_smul]
    abel
  calc eLpNorm (fun y => b y • T f y - T g y) (ENNReal.ofReal p) (volume.restrict (ball x₀ r))
      = eLpNorm (fun y => b' y • T f y - T g' y) (ENNReal.ofReal p)
          (volume.restrict (ball x₀ r)) :=
        eLpNorm_congr_ae heq
    _ ≤ eLpNorm (fun y => b' y • T f y - T g' y) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ C * (((2 + 20 * 8 ^ n) * M : ℝ≥0) : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) volume :=
        hC T hKm hK hrep hTs hTp hb'i.locallyIntegrable.aestronglyMeasurable hbmo f g' hg'
    _ = (C * (2 + 20 * 8 ^ n) : ℝ≥0) * M * eLpNorm f (ENNReal.ofReal p) volume := by
        push_cast; ring

/-! ### The commutator as a bounded operator on `Lᵖ`

The operator `T` is only given on `L²`, and for an unbounded `b` the product `b f` of an `Lᵖ`
function need not lie in `L²`, so `[b, T] f` is defined a priori only for `f ∈ L² ∩ Lᵖ` with
`b f ∈ L²`. These `f` are dense in `Lᵖ`: truncating `f` to the sets where `‖f‖` and `|b|` are at
most `k`, inside sets of finite measure, gives such functions converging to `f`. The
Coifman–Rochberg–Weiss bound therefore extends `[b, T]` uniquely to a bounded operator on `Lᵖ`
(`ContinuousLinearMap.exists_continuousLinearMap_apply_ae_eq_smul_sub`). -/

section Extension

omit [Nonempty ι]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The Coifman–Rochberg–Weiss theorem on `Lᵖ`.** Let `1 ≤ s`, let `1 ≤ p < ∞` with `s < p`,
and let `δ > 0` and `A`, `Aₚ`, `C₀` be constants. There is a constant `C`, depending only on these
and the dimension `n`, with the following property on `ℝⁿ = ι → ℝ` with the sup distance.

Let `T` be an operator as in `TauCeti.exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow`: bounded
on `L²`, given away from the support of its argument by a kernel with the standard smoothness
estimate in its first variable, and with `‖T h‖_s ≤ A ‖h‖_s` and `‖T h‖_p ≤ Aₚ ‖h‖_p` for `h ∈ L²`.
Let `b` be almost everywhere strongly measurable with `‖b‖_{BMO} ≤ M`. Then the commutator
`[b, T] f = b T f - T (b f)` extends to a bounded operator `S` on `Lᵖ` with

`‖S‖ ≤ C M`,

in the sense that `S f = b T f - T g` for all `f, g ∈ L²` with `f ∈ Lᵖ` and `g = b f`. These `f`
are dense in `Lᵖ`, so `S` is the only bounded operator on `Lᵖ` with this property. -/
theorem exists_continuousLinearMap_apply_ae_eq_smul_sub_of_norm_sub_le_mul_rpow
    [CompleteSpace F] {s : ℝ} (hs : 1 ≤ s)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) (hsp : ENNReal.ofReal s < p) (A Aₚ C₀ : ℝ≥0) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ C : ℝ≥0, ∀ (T : Lp E 2 (volume : Measure (ι → ℝ)) →L[ℝ] Lp F 2 volume)
      {K : (ι → ℝ) → (ι → ℝ) → E →L[ℝ] F}, (∀ x, AEStronglyMeasurable (K x) volume) →
      (∀ x x' y, 2 * dist x x' < dist y x' →
        ‖K x y - K x' y‖ ≤ C₀ * (dist x x' ^ δ * dist y x' ^ (-(Fintype.card ι + δ)))) →
      (∀ (h : Lp E 2 (volume : Measure (ι → ℝ))) (y : ι → ℝ) (ρ : ℝ),
        (∀ᵐ z, z ∈ ball y ρ → h z = 0) → ∀ᵐ x, x ∈ ball y ρ → T h x = ∫ z, K x z (h z)) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) (ENNReal.ofReal s) volume ≤ A * eLpNorm h (ENNReal.ofReal s) volume) →
      (∀ h : Lp E 2 (volume : Measure (ι → ℝ)),
        eLpNorm (T h) p volume ≤ Aₚ * eLpNorm h p volume) →
      ∀ {b : (ι → ℝ) → ℝ} {M : ℝ≥0}, AEStronglyMeasurable b volume → bmoSeminorm b volume ≤ M →
      ∃ S : Lp E p (volume : Measure (ι → ℝ)) →L[ℝ] Lp F p volume, ‖S‖ ≤ C * M ∧
        (∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))) (hf : MemLp f p volume),
          g =ᵐ[volume] (fun y => b y • f y) →
            S (hf.toLp f) =ᵐ[volume] fun y => b y • T f y - T g y) ∧
        ∀ S' : Lp E p (volume : Measure (ι → ℝ)) →L[ℝ] Lp F p volume,
          (∀ (f g : Lp E 2 (volume : Measure (ι → ℝ))) (hf : MemLp f p volume),
            g =ᵐ[volume] (fun y => b y • f y) →
              S' (hf.toLp f) =ᵐ[volume] fun y => b y • T f y - T g y) → S' = S := by
  have hp' : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp
  obtain ⟨C, hC⟩ := exists_eLpNorm_smul_sub_le_of_norm_sub_le_mul_rpow (ι := ι) (E := E) (F := F)
    hs ((ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hp).1 hsp) A Aₚ C₀ hδ
  refine ⟨C, fun T K hKm hK hrep hT hTp b M hb hM => ?_⟩
  refine T.exists_continuousLinearMap_apply_ae_eq_smul_sub hb hp (B := C * M) fun f g _ hg => ?_
  have := hC T hKm hK hrep hT (by rwa [hp']) hb hM f g hg
  rwa [hp', ← ENNReal.coe_mul] at this

end Extension

end TauCeti
