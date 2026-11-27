/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.SharpMaximalFunction
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.Average.Jensen
import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.MeasureTheory.Integral.UncenteredMaximalFunction

/-!
# Krylov's sharp function method

Let `0 < γ < p < ∞` with `1 < p`, and let `g : ℝ^{n+1} → E` and `G : ℝ^{n+1} → F` lie in `Lᵖ`.
Suppose that the `L¹` mean oscillation of `g` on every ball `B_ρ = ball c ρ` is controlled by
averages over the dilated ball `B_{κρ}`, for every `κ ≥ 1`:

`(⨍_{B_ρ} ‖g - g_{B_ρ}‖)^γ ≤ c₁ κ^(-γ) ⨍_{B_{κρ}} ‖g‖^γ + c₂ κ^(n + 1) ⨍_{B_{κρ}} ‖G‖^γ`
`  + c₃ κ^(n + 1) (L^(γq' - 1) δ)^(1/q') (⨍_{B_{κρ}} ‖g‖^(γq))^(1/q)`

for every pair of Hölder conjugate exponents `q, q'` with `γq ≤ p`. This is the form of Krylov's
mean oscillation estimates for the gradient or the Hessian of a solution of an elliptic equation
whose coefficients are frozen on `B_{κρ}` at a matrix of mean deviation at most `δ` from the
coefficients, the deviation being bounded by `L`. If `δ` is small enough, depending only on `n`,
`γ`, `p`, `c₁`, `c₂`, `c₃` and `L`, then

`‖g‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`

with `C` depending on the same quantities
(`TauCeti.PDE.exists_eLpNorm_le_of_forall_rpow_setAverage_norm_sub_le`). For `γ ≥ 1` the left
side is at most the mean oscillation in `L^γ`, `⨍_{B_ρ} ‖g - g_{B_ρ}‖^γ`, by Jensen's inequality,
so the estimate also holds under that hypothesis
(`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le`).

The estimate holds for every exponent `p` above the exponent `γ` of the averages. Mean oscillation
estimates in `L²` (`γ = 2`), which come from the `L²` theory of the frozen equation, give the range
`2 < p < ∞`; estimates with `γ` close to `1`, which come from the `L^γ` theory of the frozen
equation, give every `p > 1`.

## The argument

* **The sharp function.** Every average over `B_{κρ} ∋ x` is at most `2^(n + 1)` times the centred
  maximal function at `x` (`TauCeti.ofReal_setAverage_norm_rpow_le_two_pow_mul_maximalFunction`).
  Taking the supremum over the balls containing `x`, the `γ`-th power of the sharp maximal
  function of `g`, which is the supremum of the `L¹` mean oscillations, is bounded pointwise by
  `κ^(-γ) M(‖g‖^γ) + κ^(n + 1) M(‖G‖^γ) + κ^(n + 1) δ^(1/q') M(‖g‖^(γq))^(1/q)`, up to constants.
* **Absorption.** The Fefferman–Stein inequality for Euclidean balls
  (`TauCeti.exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow`) and the strong
  maximal inequality with the exponents `p / γ` and `p / (γq)`, where `1 < q < p / γ`
  (`TauCeti.lintegral_rpow_le_of_rpow_le_maximalFunction`) turn this into
  `∫ ‖g‖^p ≤ (c κ^(-p) + c' δ^(p/(γq'))) ∫ ‖g‖^p + c'' ∫ ‖G‖^p`. Choosing first `κ` large and then
  `δ` small, the first term is absorbed, since `∫ ‖g‖^p` is finite.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_le_of_forall_rpow_setAverage_norm_sub_le`: the `Lᵖ` estimate from
  mean oscillation estimates in `L¹` on all balls.
* `TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le`: the same from mean
  oscillation estimates in `L^γ`, `γ ≥ 1`.

## References

* N. V. Krylov, *Parabolic and elliptic equations with VMO coefficients*, Comm. Partial
  Differential Equations **32** (2007), 453–475.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Graduate
  Studies in Mathematics **96**, AMS, 2008 (the sharp function method).
* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193.
-/

public section

open Filter MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace TauCeti

namespace PDE

variable {n : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- The coefficient of the maximal function of `‖g‖^γ` in the pointwise bound for the sharp maximal
function. -/
private noncomputable def decayCoeff (n : ℕ) (c₁ γ κ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c₁ / κ ^ γ * 2 ^ (n + 1))

/-- The coefficient of the maximal function of `‖G‖^γ` in the pointwise bound for the sharp maximal
function. -/
private noncomputable def forcingCoeff (n : ℕ) (c₂ κ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c₂ * κ ^ (n + 1) * 2 ^ (n + 1))

/-- The coefficient of the `1/q`-th power of the maximal function of `‖g‖^(γq)` in the pointwise
bound for the sharp maximal function; it carries the coefficient deviation `δ`. -/
private noncomputable def deviationCoeff (n : ℕ) (c₃ L γ κ q q' δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c₃ * κ ^ (n + 1) * (L ^ (γ * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹)

/-- Every average over a ball containing `x` is at most `2^(n + 1)` times the centred maximal
function at `x`. -/
private theorem ofReal_setAverage_norm_rpow_le {H : Type*} [NormedAddCommGroup H]
    (h : EuclideanSpace ℝ (Fin (n + 1)) → H) {k : ℝ} (hk : 0 ≤ k)
    {c x : EuclideanSpace ℝ (Fin (n + 1))} {r : ℝ} (hx : x ∈ ball c r) :
    ENNReal.ofReal (⨍ y in ball c r, ‖h y‖ ^ k) ≤
      ENNReal.ofReal (2 ^ (n + 1)) * maximalFunction volume (fun y => ‖h y‖ₑ ^ k) x := by
  simpa only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow zero_le_two,
    ENNReal.ofReal_ofNat] using
    ofReal_setAverage_norm_rpow_le_two_pow_mul_maximalFunction volume hk hx

/-- **The mean oscillation estimate on one ball.** If the `γ`-th power of the mean oscillation of
`g` on `B_ρ = ball c ρ` is bounded by the averages over `B_{κρ}` of `‖g‖^γ`, of `‖G‖^γ` and of
`‖g‖^(γq)`, then for `x ∈ B_ρ` it is bounded by the maximal functions at `x` of the same
quantities. -/
private theorem rpow_setLAverage_enorm_sub_le {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} {γ : ℝ} (hγ : 0 ≤ γ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hgp : MemLp g p volume) {c₁ c₂ c₃ L q q' : ℝ}
    (hq : q.HolderConjugate q') {c x : EuclideanSpace ℝ (Fin (n + 1))} {ρ κ δ : ℝ} (hρ : 0 < ρ)
    (hκ : 1 ≤ κ) (hx : x ∈ ball c ρ)
    (h1 : (⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖) ^ γ ≤
      c₁ / κ ^ γ * (⨍ y in ball c (κ * ρ), ‖g y‖ ^ γ) +
        c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖G y‖ ^ γ) +
        c₃ * κ ^ (n + 1) * (L ^ (γ * q' - 1) * δ) ^ q'⁻¹ *
          (⨍ y in ball c (κ * ρ), ‖g y‖ ^ (γ * q)) ^ q⁻¹) :
    (⨍⁻ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ₑ) ^ γ ≤
      decayCoeff n c₁ γ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ γ) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ γ) x +
        deviationCoeff n c₃ L γ κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (γ * q)) x ^ q⁻¹ := by
  set r := κ * ρ
  have hxr : x ∈ ball c r := ball_subset_ball (le_mul_of_one_le_left hρ.le hκ) hx
  have hq1 : 0 ≤ q⁻¹ := inv_nonneg.2 hq.pos.le
  have hE1 := ofReal_setAverage_norm_rpow_le g hγ hxr
  have hE2 := ofReal_setAverage_norm_rpow_le G hγ hxr
  have hE3 : ENNReal.ofReal ((⨍ y in ball c r, ‖g y‖ ^ (γ * q)) ^ q⁻¹) ≤
      ENNReal.ofReal ((2 ^ (n + 1)) ^ q⁻¹) *
        maximalFunction volume (fun y => ‖g y‖ₑ ^ (γ * q)) x ^ q⁻¹ := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (average_nonneg fun y => by positivity) hq1,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hq1, ← ENNReal.mul_rpow_of_nonneg _ _ hq1]
    gcongr
    exact ofReal_setAverage_norm_rpow_le g (mul_nonneg hγ hq.pos.le) hxr
  -- On `B_ρ`, where `g` minus its mean is integrable, the mean oscillation passes to `ℝ≥0∞`.
  have : IsFiniteMeasure (volume.restrict (ball c ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hosc : (⨍⁻ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ₑ) ^ γ =
      ENNReal.ofReal ((⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖) ^ γ) := by
    have hi : IntegrableOn (fun y => ‖g y - ⨍ z in ball c ρ, g z‖ ^ (1 : ℝ)) (ball c ρ) := by
      have h := ((((hgp.restrict (ball c ρ)).mono_exponent hp).sub
        (memLp_const (⨍ z in ball c ρ, g z))).integrable le_rfl).norm
      simp only [Pi.sub_apply] at h
      simp only [Real.rpow_one]
      exact h
    have h := ofReal_setAverage_norm_rpow zero_le_one hi
    simp only [Real.rpow_one, ENNReal.rpow_one] at h
    rw [← ENNReal.ofReal_rpow_of_nonneg (average_nonneg fun y => norm_nonneg _) hγ, h]
  -- Each term of the real bound `h1`, multiplied by its coefficient, passes to `ℝ≥0∞`; a negative
  -- coefficient makes the term vanish.
  have hmul : ∀ {e K I : ℝ} {M : ℝ≥0∞}, 0 ≤ I → ENNReal.ofReal I ≤ ENNReal.ofReal K * M →
      ENNReal.ofReal (e * I) ≤ ENNReal.ofReal (e * K) * M := fun {e} {_} {I} {_} hI h => by
    rcases le_or_gt 0 e with he | he
    · rw [ENNReal.ofReal_mul he, ENNReal.ofReal_mul he, mul_assoc]
      gcongr
    · rw [ENNReal.ofReal_of_nonpos (by nlinarith)]
      positivity
  unfold decayCoeff forcingCoeff deviationCoeff
  rw [hosc]
  refine (ENNReal.ofReal_le_ofReal h1).trans
    (ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_add_le.trans
      (add_le_add (hmul (average_nonneg fun y => by positivity) hE1)
        (hmul (average_nonneg fun y => by positivity) hE2)))
      (hmul (Real.rpow_nonneg (average_nonneg fun y => by positivity) _) hE3)))

/-- **The pointwise estimate for the sharp maximal function.** If the mean oscillation estimate
holds on every ball for a fixed `κ ≥ 1`, then the `γ`-th power of the sharp maximal function of `g`
is bounded pointwise by the maximal functions of `‖g‖^γ`, of `‖G‖^γ` and of `‖g‖^(γq)`. -/
private theorem rpow_sharpMaximalFunction_le {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} {γ : ℝ} (hγ : 0 < γ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hgp : MemLp g p volume) {c₁ c₂ c₃ L q q' : ℝ}
    (hq : q.HolderConjugate q') {κ δ : ℝ} (hκ : 1 ≤ κ)
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (ρ : ℝ), 0 < ρ →
      (⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖) ^ γ ≤
        c₁ / κ ^ γ * (⨍ y in ball c (κ * ρ), ‖g y‖ ^ γ) +
          c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖G y‖ ^ γ) +
          c₃ * κ ^ (n + 1) * (L ^ (γ * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ y in ball c (κ * ρ), ‖g y‖ ^ (γ * q)) ^ q⁻¹)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    sharpMaximalFunction volume g x ^ γ ≤
      decayCoeff n c₁ γ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ γ) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ γ) x +
        deviationCoeff n c₃ L γ κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (γ * q)) x ^ q⁻¹ := by
  rw [← ENNReal.le_rpow_inv_iff hγ]
  refine sharpMaximalFunction_le fun c ρ hx => ?_
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.1 hx)
  rw [ENNReal.le_rpow_inv_iff hγ]
  exact rpow_setLAverage_enorm_sub_le hγ.le hp hgp hq hρ hκ hx (hosc c ρ hρ)

/-- The estimate before absorption: `∫ ‖g‖^s` is bounded by the Fefferman–Stein constant times
the integrated pointwise bound for the sharp maximal function, in which `∫ ‖g‖^s` reappears with
the factors `κ^(-γ)` and `δ^(1/q')`. -/
private theorem lintegral_enorm_rpow_le {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} (hgm : AEStronglyMeasurable g volume)
    (hGm : AEStronglyMeasurable G volume) {c₁ c₂ c₃ L γ q q' s κ δ : ℝ} (hγ : 0 < γ)
    (hq : 1 < q) (hqs : γ * q < s) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖g x‖ₑ ^ s ≤ CFS * ∫⁻ x, sharpMaximalFunction volume g x ^ s)
    (hpt : ∀ x, sharpMaximalFunction volume g x ^ γ ≤
      decayCoeff n c₁ γ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ γ) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ γ) x +
        deviationCoeff n c₃ L γ κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (γ * q)) x ^ q⁻¹) :
    ∫⁻ x, ‖g x‖ₑ ^ s ≤ CFS * (2 ^ (s / γ - 1) * (2 ^ (s / γ - 1) *
        (decayCoeff n c₁ γ κ ^ (s / γ) *
            (maximalFunctionConst (n + 1) (s / γ) * ∫⁻ x, ‖g x‖ₑ ^ s) +
          forcingCoeff n c₂ κ ^ (s / γ) *
            (maximalFunctionConst (n + 1) (s / γ) * ∫⁻ x, ‖G x‖ₑ ^ s)) +
      deviationCoeff n c₃ L γ κ q q' δ ^ (s / γ) *
        (maximalFunctionConst (n + 1) (s / γ / q) * ∫⁻ x, ‖g x‖ₑ ^ s))) := by
  have hsq : ∀ (y : ℝ≥0∞) (e : ℝ), e * (s / e) = s → (y ^ e) ^ (s / e) = y ^ s :=
    fun y e he => by rw [← ENNReal.rpow_mul, he]
  have hy1 : ∀ y : ℝ≥0∞, (y ^ γ) ^ (s / γ) = y ^ s := fun y => hsq y γ (by field_simp)
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hy3 : ∀ y : ℝ≥0∞, (y ^ (γ * q)) ^ (s / γ / q) = y ^ s := fun y => by
    rw [div_div]; exact hsq y (γ * q) (by field_simp)
  have hbound := lintegral_rpow_le_of_rpow_le_maximalFunction (g := fun x =>
      sharpMaximalFunction volume g x) volume
    (h₁ := fun y => ‖g y‖ₑ ^ γ) (h₂ := fun y => ‖G y‖ₑ ^ γ) (h₃ := fun y => ‖g y‖ₑ ^ (γ * q))
    (hgm.eNorm.pow_const γ) (hGm.eNorm.pow_const γ) (hgm.eNorm.pow_const _) hγ hq hqs hpt
  simp only [hy1, hy3, finrank_euclideanSpace, Fintype.card_fin] at hbound
  exact hFS.trans (mul_le_mul_right hbound _)

/-- The choice of the parameters: for finite `K₁, K₃`, there are `κ ≥ 1` and `δ > 0` making the
decaying term and the coefficient term of the estimate before absorption at most `1/4`. -/
private theorem exists_one_le_and_pos_of_ne_top (c₁ c₃ L : ℝ) {γ q q' s : ℝ} (hγ : 0 < γ)
    (hq' : 0 < q') (hs : 0 < s) {K₁ K₃ : ℝ≥0∞} (hK₁ : K₁ ≠ ∞) (hK₃ : K₃ ≠ ∞) :
    ∃ κ : ℝ, 1 ≤ κ ∧
      K₁ * decayCoeff n c₁ γ κ ^ (s / γ) ≤ 2⁻¹ / 2 ∧
      ∃ δ : ℝ, 0 < δ ∧ K₃ * deviationCoeff n c₃ L γ κ q q' δ ^ (s / γ) ≤ 2⁻¹ / 2 := by
  have hquarter : (0 : ℝ≥0∞) < 2⁻¹ / 2 :=
    ENNReal.div_pos (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ENNReal.ofNat_ne_top
  have hsγ : 0 < s / γ := div_pos hs hγ
  have h1 : Tendsto (fun κ : ℝ => c₁ / κ ^ γ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hγ)
  have h0 := h1.mul_const ((2 : ℝ) ^ (n + 1))
  rw [zero_mul] at h0
  have h0' : Tendsto (fun κ : ℝ => ENNReal.ofReal (c₁ / κ ^ γ * 2 ^ (n + 1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h0
  obtain ⟨κ, hκ, hκ1⟩ := ((eventually_ge_atTop 1).and
    (((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hK₁ hsγ).comp h0').eventually
      (gt_mem_nhds hquarter))).exists
  refine ⟨κ, hκ, hκ1.le, ?_⟩
  have hq'' : 0 < q'⁻¹ := inv_pos.2 hq'
  set e : ℝ → ℝ := fun δ =>
    c₃ * κ ^ (n + 1) * (L ^ (γ * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹
  have hc : ContinuousAt e 0 := by
    refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) continuousAt_const
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hq''.le)).comp (by fun_prop)
  have hc0' : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hc0 : e 0 = 0 := by simp [e, Real.zero_rpow hq''.ne']
    rwa [hc0] at h
  have hc0'' : Tendsto (fun δ => ENNReal.ofReal (e δ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hc0'
  obtain ⟨δ, hδ1, hδ⟩ := ((((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hK₃ hsγ).comp
    hc0'').eventually (gt_mem_nhds hquarter)).and self_mem_nhdsWithin).exists
  exact ⟨δ, hδ, hδ1.le⟩

/-- The estimate for fixed parameters `κ` and `δ` small enough for the absorption. -/
private theorem eLpNorm_le_of_le_quarter {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp_top : p ≠ ∞)
    (hgp : MemLp g p volume) (hGp : MemLp G p volume) {c₁ c₂ c₃ L γ q q' s κ δ : ℝ}
    (hs_def : s = p.toReal) (hγ : 0 < γ) (hq : 1 < q) (hqs : γ * q < s) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖g x‖ₑ ^ s ≤ CFS * ∫⁻ x, sharpMaximalFunction volume g x ^ s)
    (hpt : ∀ x, sharpMaximalFunction volume g x ^ γ ≤
      decayCoeff n c₁ γ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ γ) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ γ) x +
        deviationCoeff n c₃ L γ κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (γ * q)) x ^ q⁻¹)
    (hκ1 : CFS * 2 ^ (s / γ - 1) * 2 ^ (s / γ - 1) * maximalFunctionConst (n + 1) (s / γ) *
        decayCoeff n c₁ γ κ ^ (s / γ) ≤ 2⁻¹ / 2)
    (hδ1 : CFS * 2 ^ (s / γ - 1) * maximalFunctionConst (n + 1) (s / γ / q) *
        deviationCoeff n c₃ L γ κ q q' δ ^ (s / γ) ≤ 2⁻¹ / 2) :
    eLpNorm g p volume ≤
      (CFS * 2 ^ (s / γ - 1) * 2 ^ (s / γ - 1) * forcingCoeff n c₂ κ ^ (s / γ) *
        maximalFunctionConst (n + 1) (s / γ) * 2) ^ (1 / s) * eLpNorm G p volume := by
  have hs1 : 0 ≤ 1 / s := one_div_nonneg.2 (by nlinarith)
  have key := lintegral_enorm_rpow_le hgp.aestronglyMeasurable hGp.aestronglyMeasurable hγ hq hqs
    hFS hpt
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hgp.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hGp.aestronglyMeasurable, ← hs_def,
    ← ENNReal.mul_rpow_of_nonneg _ _ hs1]
  have hI := (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp_top hgp.eLpNorm_lt_top).ne
  rw [← hs_def] at hI
  refine ENNReal.rpow_le_rpow ((ENNReal.le_mul_two_of_le_add_div_two hI ?_).trans_eq
    (mul_right_comm _ _ _)) hs1
  -- The terms with the factors `κ^(-γ)` and `δ^(1/q')` are at most a quarter of `I = ∫ ‖g‖^s`
  -- each, so together they are absorbed.
  set I := ∫⁻ x, ‖g x‖ₑ ^ s
  set J := ∫⁻ x, ‖G x‖ₑ ^ s
  calc I ≤ CFS * 2 ^ (s / γ - 1) * 2 ^ (s / γ - 1) * maximalFunctionConst (n + 1) (s / γ) *
          decayCoeff n c₁ γ κ ^ (s / γ) * I +
        CFS * 2 ^ (s / γ - 1) * 2 ^ (s / γ - 1) * forcingCoeff n c₂ κ ^ (s / γ) *
          maximalFunctionConst (n + 1) (s / γ) * J +
        CFS * 2 ^ (s / γ - 1) * maximalFunctionConst (n + 1) (s / γ / q) *
          deviationCoeff n c₃ L γ κ q q' δ ^ (s / γ) * I :=
        key.trans_eq (by ring)
    _ ≤ 2⁻¹ / 2 * I +
        CFS * 2 ^ (s / γ - 1) * 2 ^ (s / γ - 1) * forcingCoeff n c₂ κ ^ (s / γ) *
          maximalFunctionConst (n + 1) (s / γ) * J +
        2⁻¹ / 2 * I := by
        gcongr
    _ = _ := by
        rw [add_right_comm, ← add_mul, ENNReal.add_halves, add_comm, ENNReal.div_eq_inv_mul]

/-- **Krylov's sharp function method.** Let `0 < γ < p < ∞` with `1 < p`, and let `c₁, c₂, c₃, L`
be real constants. There are constants `C` and `δ > 0`, depending only on `n`, `γ`, `p`, `c₁`,
`c₂`, `c₃` and `L`, with the following property. Let `g : ℝ^{n+1} → E` and `G : ℝ^{n+1} → F` lie
in `Lᵖ`, and suppose that for every pair of Hölder conjugate exponents `q, q'` with `γq ≤ p`, every
ball `B_ρ = ball c ρ` and every `κ ≥ 1`

`(⨍_{B_ρ} ‖g - g_{B_ρ}‖)^γ ≤ c₁ κ^(-γ) ⨍_{B_{κρ}} ‖g‖^γ + c₂ κ^(n + 1) ⨍_{B_{κρ}} ‖G‖^γ`
`  + c₃ κ^(n + 1) (L^(γq' - 1) δ)^(1/q') (⨍_{B_{κρ}} ‖g‖^(γq))^(1/q)`.

Then `‖g‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`. The left-hand side is the `γ`-th power of the mean oscillation in
`L¹`; by Jensen's inequality it is at most the mean oscillation in `L^γ` when `γ ≥ 1`, which is the
form of `TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le`. -/
theorem exists_eLpNorm_le_of_forall_rpow_setAverage_norm_sub_le [CompleteSpace E] {γ : ℝ}
    (hγ : 0 < γ) {p : ℝ≥0∞} (hp : 1 < p) (hγp : ENNReal.ofReal γ < p) (hp_top : p ≠ ∞)
    (c₁ c₂ c₃ L : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {g : EuclideanSpace ℝ (Fin (n + 1)) → E} {G : EuclideanSpace ℝ (Fin (n + 1)) → F},
        MemLp g p volume → MemLp G p volume →
        (∀ q q' : ℝ, q.HolderConjugate q' → ENNReal.ofReal (γ * q) ≤ p →
          ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (ρ κ : ℝ), 0 < ρ → 1 ≤ κ →
            (⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖) ^ γ ≤
              c₁ / κ ^ γ * (⨍ y in ball c (κ * ρ), ‖g y‖ ^ γ) +
                c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖G y‖ ^ γ) +
                c₃ * κ ^ (n + 1) * (L ^ (γ * q' - 1) * δ) ^ q'⁻¹ *
                  (⨍ y in ball c (κ * ρ), ‖g y‖ ^ (γ * q)) ^ q⁻¹) →
        eLpNorm g p volume ≤ C * eLpNorm G p volume := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = p.toReal := ⟨_, rfl⟩
  have hs : γ < s := by
    rw [hs_def, ← ENNReal.toReal_ofReal hγ.le]
    exact (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hp_top).2 hγp
  have hs1 : 1 < s := by
    rw [hs_def, ← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  have hsγ : 1 < s / γ := (one_lt_div hγ).2 hs
  obtain ⟨q, hq, hqs'⟩ := exists_between hsγ
  have hqs : γ * q < s := (lt_div_iff₀' hγ).1 hqs'
  obtain ⟨q', hqq⟩ : ∃ q' : ℝ, q.HolderConjugate q' :=
    ⟨_, Real.HolderConjugate.conjExponent hq⟩
  have hqp : ENNReal.ofReal (γ * q) ≤ p := by
    rw [← ENNReal.ofReal_toReal hp_top, ← hs_def]
    exact ENNReal.ofReal_le_ofReal hqs.le
  obtain ⟨CFS, hFS⟩ := exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow
    (ι := Fin (n + 1)) hs1
  have hcM := maximalFunctionConst_ne_top (n + 1)
  have h2 : (2 : ℝ≥0∞) ^ (s / γ - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  obtain ⟨κ, hκ, hκ1, δ, hδ, hδ1⟩ := exists_one_le_and_pos_of_ne_top (n := n) c₁ c₃ L (q := q)
    hγ hqq.symm.pos (by linarith : 0 < s)
    (K₁ := (CFS : ℝ≥0∞) * 2 ^ (s / γ - 1) * 2 ^ (s / γ - 1) * maximalFunctionConst (n + 1) (s / γ))
    (K₃ := (CFS : ℝ≥0∞) * 2 ^ (s / γ - 1) * maximalFunctionConst (n + 1) (s / γ / q))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
      (hcM _))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) (hcM _))
  set C : ℝ≥0∞ := ((CFS : ℝ≥0∞) * 2 ^ (s / γ - 1) * 2 ^ (s / γ - 1) *
    forcingCoeff n c₂ κ ^ (s / γ) * maximalFunctionConst (n + 1) (s / γ) * 2) ^ (1 / s)
  have hK₂ : C ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (by linarith)) (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)) (hcM _))
      ENNReal.ofNat_ne_top)
  refine ⟨C.toNNReal, δ, hδ, fun {g G} hgp hGp hosc => ?_⟩
  rw [ENNReal.coe_toNNReal hK₂]
  -- The Fefferman–Stein inequality applies to `g ∈ Lᵖ` itself, with `p₀ = p`.
  exact eLpNorm_le_of_le_quarter (zero_lt_one.trans hp).ne' hp_top hgp hGp hs_def hγ hq hqs
    (hFS hgp hp.le (by rw [hs_def, ENNReal.ofReal_toReal hp_top]))
    (rpow_sharpMaximalFunction_le hγ hp.le hgp hqq hκ fun c ρ hρ =>
      hosc q q' hqq hqp c ρ κ hρ hκ)
    hκ1 hδ1

/-- **Krylov's sharp function method, with mean oscillation in `L^γ`.** Let `1 ≤ γ < p < ∞` and let
`c₁, c₂, c₃, L` be real constants. There are constants `C` and `δ > 0`, depending only on `n`,
`γ`, `p`, `c₁`, `c₂`, `c₃` and `L`, with the following property. Let `g : ℝ^{n+1} → E` and
`G : ℝ^{n+1} → F` lie in `Lᵖ`, and suppose that for every pair of Hölder conjugate exponents
`q, q'` with `γq ≤ p`, every ball `B_ρ = ball c ρ` and every `κ ≥ 1`

`⨍_{B_ρ} ‖g - g_{B_ρ}‖^γ ≤ c₁ κ^(-γ) ⨍_{B_{κρ}} ‖g‖^γ + c₂ κ^(n + 1) ⨍_{B_{κρ}} ‖G‖^γ`
`  + c₃ κ^(n + 1) (L^(γq' - 1) δ)^(1/q') (⨍_{B_{κρ}} ‖g‖^(γq))^(1/q)`.

Then `‖g‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`. -/
theorem exists_eLpNorm_le_of_forall_setAverage_norm_sub_rpow_le [CompleteSpace E] {γ : ℝ}
    (hγ : 1 ≤ γ) {p : ℝ≥0∞} (hγp : ENNReal.ofReal γ < p) (hp_top : p ≠ ∞) (c₁ c₂ c₃ L : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {g : EuclideanSpace ℝ (Fin (n + 1)) → E} {G : EuclideanSpace ℝ (Fin (n + 1)) → F},
        MemLp g p volume → MemLp G p volume →
        (∀ q q' : ℝ, q.HolderConjugate q' → ENNReal.ofReal (γ * q) ≤ p →
          ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (ρ κ : ℝ), 0 < ρ → 1 ≤ κ →
            ⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ ^ γ ≤
              c₁ / κ ^ γ * (⨍ y in ball c (κ * ρ), ‖g y‖ ^ γ) +
                c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖G y‖ ^ γ) +
                c₃ * κ ^ (n + 1) * (L ^ (γ * q' - 1) * δ) ^ q'⁻¹ *
                  (⨍ y in ball c (κ * ρ), ‖g y‖ ^ (γ * q)) ^ q⁻¹) →
        eLpNorm g p volume ≤ C * eLpNorm G p volume := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hp : 1 < p := (ENNReal.one_le_ofReal.2 hγ).trans_lt hγp
  obtain ⟨C, δ, hδ, h⟩ :=
    exists_eLpNorm_le_of_forall_rpow_setAverage_norm_sub_le (n := n) (E := E) (F := F) hγ0 hp hγp
      hp_top c₁ c₂ c₃ L
  refine ⟨C, δ, hδ, fun {g G} hgp hGp hosc => h hgp hGp fun q q' hq hqp c ρ κ hρ hκ =>
    (le_trans ?_ (hosc q q' hq hqp c ρ κ hρ hκ))⟩
  -- Jensen's inequality for the convex power `t ↦ t^γ` on `[0, ∞)`.
  have : IsFiniteMeasure (volume.restrict (ball c ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hi : IntegrableOn (fun y => ‖g y - ⨍ z in ball c ρ, g z‖ ^ γ) (ball c ρ) := by
    have h := (((hgp.restrict (ball c ρ)).mono_exponent hγp.le).sub
      (memLp_const (⨍ z in ball c ρ, g z))).integrable_norm_rpow'
    simp only [ENNReal.toReal_ofReal hγ0.le] at h
    exact h
  exact rpow_setAverage_norm_le_setAverage_norm_rpow hγ hi

end PDE

end TauCeti
