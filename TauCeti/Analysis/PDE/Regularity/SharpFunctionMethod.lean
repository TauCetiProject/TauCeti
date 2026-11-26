/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.SharpMaximalFunction
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Integral.MaximalFunction
import TauCeti.MeasureTheory.Integral.UncenteredMaximalFunction

/-!
# Krylov's sharp function method

Let `g : ℝ^{n+1} → E` and `G : ℝ^{n+1} → F`, with `g, G ∈ Lᵖ` for some `2 < p < ∞`. Suppose
that the square mean oscillation of `g` on every ball `B_ρ = ball c ρ` is controlled by averages
over the dilated ball `B_{κρ}`, for every `κ ≥ 1`:

`⨍_{B_ρ} ‖g - g_{B_ρ}‖² ≤ c₁ κ⁻² ⨍_{B_{κρ}} ‖g‖² + c₂ κ^(n + 1) ⨍_{B_{κρ}} ‖G‖²`
`  + c₃ κ^(n + 1) (L^(2q' - 1) δ)^(1/q') (⨍_{B_{κρ}} ‖g‖^(2q))^(1/q)`

for every pair of Hölder conjugate exponents `q, q'` with `2q ≤ p`. This is the form of Krylov's
mean oscillation estimates for the gradient or the Hessian of a solution of an elliptic equation
whose coefficients are frozen on `B_{κρ}` at a matrix of mean deviation at most `δ` from the
coefficients, the deviation being bounded by `L`. If `δ` is small enough, depending only on `n`,
`p`, `c₁`, `c₂`, `c₃` and `L`, then

`‖g‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`

with `C` depending on the same quantities
(`TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le`).

## The argument

* **The sharp function.** Every average over `B_{κρ} ∋ x` is at most `2^(n + 1)` times the centred
  maximal function at `x` (`TauCeti.ofReal_setAverage_norm_rpow_le_two_pow_mul_maximalFunction`).
  With Jensen's inequality and the supremum over the balls containing `x`, the square of the sharp
  maximal function of `g` is bounded pointwise by
  `κ⁻² M(‖g‖²) + κ^(n + 1) M(‖G‖²) + κ^(n + 1) δ^(1/q') M(‖g‖^(2q))^(1/q)`, up to constants.
* **Absorption.** The Fefferman–Stein inequality for Euclidean balls
  (`TauCeti.exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow`) and the strong
  maximal inequality with the exponents `p / 2` and `p / (2q)`, where `1 < q < p / 2`
  (`TauCeti.lintegral_rpow_le_of_sq_le_maximalFunction`) turn this into
  `∫ ‖g‖^p ≤ (c κ^(-p) + c' δ^(p/(2q'))) ∫ ‖g‖^p + c'' ∫ ‖G‖^p`. Choosing first `κ` large and then
  `δ` small, the first term is absorbed, since `∫ ‖g‖^p` is finite.

## Main declarations

* `TauCeti.PDE.exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le`: the `Lᵖ` estimate from
  mean oscillation estimates on all balls.

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

/-- The coefficient of the maximal function of `‖g‖²` in the pointwise bound for the sharp maximal
function. -/
private noncomputable def decayCoeff (n : ℕ) (c₁ κ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c₁ / κ ^ 2 * 2 ^ (n + 1))

/-- The coefficient of the maximal function of `‖G‖²` in the pointwise bound for the sharp maximal
function. -/
private noncomputable def forcingCoeff (n : ℕ) (c₂ κ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c₂ * κ ^ (n + 1) * 2 ^ (n + 1))

/-- The coefficient of the `1/q`-th power of the maximal function of `‖g‖^(2q)` in the pointwise
bound for the sharp maximal function; it carries the coefficient deviation `δ`. -/
private noncomputable def deviationCoeff (n : ℕ) (c₃ L κ q q' δ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (c₃ * κ ^ (n + 1) * (L ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹)

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

/-- **The mean oscillation estimate on one ball.** If the square mean oscillation of `g` on
`B_ρ = ball c ρ` is bounded by the averages over `B_{κρ}` of `‖g‖²`, of `‖G‖²` and of `‖g‖^(2q)`,
then for `x ∈ B_ρ` the square of the mean oscillation of `g` on `B_ρ` is bounded by the maximal
functions at `x` of the same quantities. -/
private theorem sq_setLAverage_enorm_sub_le {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} {p : ℝ≥0∞} (h2p : 2 ≤ p) (hgp : MemLp g p volume)
    {c₁ c₂ c₃ L q q' : ℝ} (hq : q.HolderConjugate q') {c x : EuclideanSpace ℝ (Fin (n + 1))}
    {ρ κ δ : ℝ} (hρ : 0 < ρ) (hκ : 1 ≤ κ) (hx : x ∈ ball c ρ)
    (h1 : ⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ ^ 2 ≤
      c₁ / κ ^ 2 * (⨍ y in ball c (κ * ρ), ‖g y‖ ^ 2) +
        c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖G y‖ ^ 2) +
        c₃ * κ ^ (n + 1) * (L ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
          (⨍ y in ball c (κ * ρ), ‖g y‖ ^ (2 * q)) ^ q⁻¹) :
    (⨍⁻ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ₑ) ^ 2 ≤
      decayCoeff n c₁ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ 2) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        deviationCoeff n c₃ L κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
  set r := κ * ρ
  have hxr : x ∈ ball c r := ball_subset_ball (le_mul_of_one_le_left hρ.le hκ) hx
  have hq1 : 0 ≤ q⁻¹ := inv_nonneg.2 hq.pos.le
  have hE1 := ofReal_setAverage_norm_rpow_le g zero_le_two hxr
  have hE2 := ofReal_setAverage_norm_rpow_le G zero_le_two hxr
  simp only [Real.rpow_two, ENNReal.rpow_two] at hE1 hE2
  have hE3 : ENNReal.ofReal ((⨍ y in ball c r, ‖g y‖ ^ (2 * q)) ^ q⁻¹) ≤
      ENNReal.ofReal ((2 ^ (n + 1)) ^ q⁻¹) *
        maximalFunction volume (fun y => ‖g y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (average_nonneg fun y => by positivity) hq1,
      ← ENNReal.ofReal_rpow_of_nonneg (by positivity) hq1, ← ENNReal.mul_rpow_of_nonneg _ _ hq1]
    gcongr
    exact ofReal_setAverage_norm_rpow_le g (by linarith [hq.pos]) hxr
  -- Jensen's inequality on `B_ρ`.
  have : IsFiniteMeasure (volume.restrict (ball c ρ)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hjensen := sq_setLAverage_enorm_le_ofReal_setAverage_norm_sq
    (h := fun y => g y - ⨍ z in ball c ρ, g z)
    (((hgp.restrict (ball c ρ)).mono_exponent h2p).integrableOn_norm_sub_sq_of_subset subset_rfl
      measure_ball_lt_top.ne _)
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
  refine hjensen.trans ((ENNReal.ofReal_le_ofReal h1).trans
    (ENNReal.ofReal_add_le.trans (add_le_add (ENNReal.ofReal_add_le.trans
      (add_le_add (hmul (average_nonneg fun y => by positivity) hE1)
        (hmul (average_nonneg fun y => by positivity) hE2)))
      (hmul (Real.rpow_nonneg (average_nonneg fun y => by positivity) _) hE3))))

/-- **The pointwise estimate for the sharp maximal function.** If the mean oscillation estimate
holds on every ball for a fixed `κ ≥ 1`, then the square of the sharp maximal function of `g` is
bounded pointwise by the maximal functions of `‖g‖²`, of `‖G‖²` and of `‖g‖^(2q)`. -/
private theorem sq_sharpMaximalFunction_le {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} {p : ℝ≥0∞} (h2p : 2 ≤ p) (hgp : MemLp g p volume)
    {c₁ c₂ c₃ L q q' : ℝ} (hq : q.HolderConjugate q') {κ δ : ℝ} (hκ : 1 ≤ κ)
    (hosc : ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (ρ : ℝ), 0 < ρ →
      ⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ ^ 2 ≤
        c₁ / κ ^ 2 * (⨍ y in ball c (κ * ρ), ‖g y‖ ^ 2) +
          c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖G y‖ ^ 2) +
          c₃ * κ ^ (n + 1) * (L ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
            (⨍ y in ball c (κ * ρ), ‖g y‖ ^ (2 * q)) ^ q⁻¹)
    (x : EuclideanSpace ℝ (Fin (n + 1))) :
    sharpMaximalFunction volume g x ^ 2 ≤
      decayCoeff n c₁ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ 2) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        deviationCoeff n c₃ L κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (2 * q)) x ^ q⁻¹ := by
  rw [← ENNReal.rpow_two, ← ENNReal.le_rpow_inv_iff two_pos]
  refine sharpMaximalFunction_le fun c ρ hx => ?_
  have hρ : 0 < ρ := dist_nonneg.trans_lt (mem_ball.1 hx)
  rw [ENNReal.le_rpow_inv_iff two_pos, ENNReal.rpow_two]
  exact sq_setLAverage_enorm_sub_le h2p hgp hq hρ hκ hx (hosc c ρ hρ)

/-- The estimate before absorption: `∫ ‖g‖^s` is bounded by the Fefferman–Stein constant times
the integrated pointwise bound for the sharp maximal function, in which `∫ ‖g‖^s` reappears with
the factors `κ⁻²` and `δ^(1/q')`. -/
private theorem lintegral_enorm_rpow_le {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} (hgm : AEStronglyMeasurable g volume)
    (hGm : AEStronglyMeasurable G volume) {c₁ c₂ c₃ L q q' s κ δ : ℝ} (hq : 1 < q)
    (hqs : 2 * q < s) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖g x‖ₑ ^ s ≤ CFS * ∫⁻ x, sharpMaximalFunction volume g x ^ s)
    (hpt : ∀ x, sharpMaximalFunction volume g x ^ 2 ≤
      decayCoeff n c₁ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ 2) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        deviationCoeff n c₃ L κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (2 * q)) x ^ q⁻¹) :
    ∫⁻ x, ‖g x‖ₑ ^ s ≤ CFS * (2 ^ (s / 2 - 1) * (2 ^ (s / 2 - 1) *
        (decayCoeff n c₁ κ ^ (s / 2) * (maximalFunctionConst (n + 1) (s / 2) * ∫⁻ x, ‖g x‖ₑ ^ s) +
          forcingCoeff n c₂ κ ^ (s / 2) *
            (maximalFunctionConst (n + 1) (s / 2) * ∫⁻ x, ‖G x‖ₑ ^ s)) +
      deviationCoeff n c₃ L κ q q' δ ^ (s / 2) *
        (maximalFunctionConst (n + 1) (s / 2 / q) * ∫⁻ x, ‖g x‖ₑ ^ s))) := by
  have hsq : ∀ (y : ℝ≥0∞) (e : ℝ), e * (s / e) = s → (y ^ e) ^ (s / e) = y ^ s :=
    fun y e he => by rw [← ENNReal.rpow_mul, he]
  have hy2 : ∀ y : ℝ≥0∞, (y ^ 2) ^ (s / 2) = y ^ s := fun y => by
    rw [← ENNReal.rpow_natCast, Nat.cast_ofNat]
    exact hsq y 2 (by ring)
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  have hy3 : ∀ y : ℝ≥0∞, (y ^ (2 * q)) ^ (s / 2 / q) = y ^ s := fun y => by
    rw [div_div]; exact hsq y (2 * q) (by field_simp)
  have hbound := lintegral_rpow_le_of_sq_le_maximalFunction (g := fun x =>
      sharpMaximalFunction volume g x) volume
    (h₁ := fun y => ‖g y‖ₑ ^ 2) (h₂ := fun y => ‖G y‖ₑ ^ 2) (h₃ := fun y => ‖g y‖ₑ ^ (2 * q))
    (hgm.eNorm.pow_const 2) (hGm.eNorm.pow_const 2) (hgm.eNorm.pow_const _) hq hqs hpt
  simp only [hy2, hy3, finrank_euclideanSpace, Fintype.card_fin] at hbound
  exact hFS.trans (mul_le_mul_right hbound _)

/-- The choice of the parameters: for finite `K₁, K₃`, there are `κ ≥ 1` and `δ > 0` making the
decaying term and the coefficient term of the estimate before absorption at most `1/4`. -/
private theorem exists_one_le_and_pos_of_ne_top (c₁ c₃ L : ℝ) {q q' s : ℝ} (hq' : 0 < q')
    (hs : 0 < s) {K₁ K₃ : ℝ≥0∞} (hK₁ : K₁ ≠ ∞) (hK₃ : K₃ ≠ ∞) :
    ∃ κ : ℝ, 1 ≤ κ ∧
      K₁ * decayCoeff n c₁ κ ^ (s / 2) ≤ 2⁻¹ / 2 ∧
      ∃ δ : ℝ, 0 < δ ∧ K₃ * deviationCoeff n c₃ L κ q q' δ ^ (s / 2) ≤ 2⁻¹ / 2 := by
  have hquarter : (0 : ℝ≥0∞) < 2⁻¹ / 2 :=
    ENNReal.div_pos (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ENNReal.ofNat_ne_top
  have hs2 : 0 < s / 2 := by linarith
  have h1 : Tendsto (fun κ : ℝ => c₁ / κ ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  have h0 := h1.mul_const ((2 : ℝ) ^ (n + 1))
  rw [zero_mul] at h0
  have h0' : Tendsto (fun κ : ℝ => ENNReal.ofReal (c₁ / κ ^ 2 * 2 ^ (n + 1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h0
  obtain ⟨κ, hκ, hκ1⟩ := ((eventually_ge_atTop 1).and
    (((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hK₁ hs2).comp h0').eventually
      (gt_mem_nhds hquarter))).exists
  refine ⟨κ, hκ, hκ1.le, ?_⟩
  have hq'' : 0 < q'⁻¹ := inv_pos.2 hq'
  set e : ℝ → ℝ := fun δ => c₃ * κ ^ (n + 1) * (L ^ (2 * q' - 1) * δ) ^ q'⁻¹ * (2 ^ (n + 1)) ^ q⁻¹
  have hc : ContinuousAt e 0 := by
    refine ContinuousAt.mul (ContinuousAt.mul continuousAt_const ?_) continuousAt_const
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hq''.le)).comp (by fun_prop)
  have hc0' : Tendsto e (𝓝[>] 0) (𝓝 0) := by
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    have hc0 : e 0 = 0 := by simp [e, Real.zero_rpow hq''.ne']
    rwa [hc0] at h
  have hc0'' : Tendsto (fun δ => ENNReal.ofReal (e δ)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hc0'
  obtain ⟨δ, hδ1, hδ⟩ := ((((ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hK₃ hs2).comp
    hc0'').eventually (gt_mem_nhds hquarter)).and self_mem_nhdsWithin).exists
  exact ⟨δ, hδ, hδ1.le⟩

/-- The estimate for fixed parameters `κ` and `δ` small enough for the absorption. -/
private theorem eLpNorm_le_of_le_quarter {g : EuclideanSpace ℝ (Fin (n + 1)) → E}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → F} {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞)
    (hgp : MemLp g p volume) (hGp : MemLp G p volume) {c₁ c₂ c₃ L q q' s κ δ : ℝ}
    (hs_def : s = p.toReal) (hq : 1 < q) (hqs : 2 * q < s) {CFS : ℝ≥0∞}
    (hFS : ∫⁻ x, ‖g x‖ₑ ^ s ≤ CFS * ∫⁻ x, sharpMaximalFunction volume g x ^ s)
    (hpt : ∀ x, sharpMaximalFunction volume g x ^ 2 ≤
      decayCoeff n c₁ κ * maximalFunction volume (fun y => ‖g y‖ₑ ^ 2) x +
        forcingCoeff n c₂ κ * maximalFunction volume (fun y => ‖G y‖ₑ ^ 2) x +
        deviationCoeff n c₃ L κ q q' δ *
          maximalFunction volume (fun y => ‖g y‖ₑ ^ (2 * q)) x ^ q⁻¹)
    (hκ1 : CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2) *
        decayCoeff n c₁ κ ^ (s / 2) ≤ 2⁻¹ / 2)
    (hδ1 : CFS * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2 / q) *
        deviationCoeff n c₃ L κ q q' δ ^ (s / 2) ≤ 2⁻¹ / 2) :
    eLpNorm g p volume ≤
      (CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * forcingCoeff n c₂ κ ^ (s / 2) *
        maximalFunctionConst (n + 1) (s / 2) * 2) ^ (1 / s) * eLpNorm G p volume := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans hp).ne'
  have hs1 : 0 ≤ 1 / s := one_div_nonneg.2 (by linarith)
  have key := lintegral_enorm_rpow_le hgp.aestronglyMeasurable hGp.aestronglyMeasurable hq hqs
    hFS hpt
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hgp.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hGp.aestronglyMeasurable, ← hs_def,
    ← ENNReal.mul_rpow_of_nonneg _ _ hs1]
  have hI := (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hp_top hgp.eLpNorm_lt_top).ne
  rw [← hs_def] at hI
  refine ENNReal.rpow_le_rpow ((ENNReal.le_mul_two_of_le_add_div_two hI ?_).trans_eq
    (mul_right_comm _ _ _)) hs1
  -- The terms with the factors `κ⁻²` and `δ^(1/q')` are at most a quarter of `I = ∫ ‖g‖^s` each,
  -- so together they are absorbed.
  set I := ∫⁻ x, ‖g x‖ₑ ^ s
  set J := ∫⁻ x, ‖G x‖ₑ ^ s
  calc I ≤ CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2) *
          decayCoeff n c₁ κ ^ (s / 2) * I +
        CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * forcingCoeff n c₂ κ ^ (s / 2) *
          maximalFunctionConst (n + 1) (s / 2) * J +
        CFS * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2 / q) *
          deviationCoeff n c₃ L κ q q' δ ^ (s / 2) * I :=
        key.trans_eq (by ring)
    _ ≤ 2⁻¹ / 2 * I +
        CFS * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * forcingCoeff n c₂ κ ^ (s / 2) *
          maximalFunctionConst (n + 1) (s / 2) * J +
        2⁻¹ / 2 * I := by
        gcongr
    _ = _ := by
        rw [add_right_comm, ← add_mul, ENNReal.add_halves, add_comm, ENNReal.div_eq_inv_mul]

/-- **Krylov's sharp function method.** Let `2 < p < ∞` and let `c₁, c₂, c₃, L` be real constants.
There are constants `C` and `δ > 0`, depending only on `n`, `p`, `c₁`, `c₂`, `c₃` and `L`, with the
following property. Let `g : ℝ^{n+1} → E` and `G : ℝ^{n+1} → F` lie in `Lᵖ`, and suppose that for
every pair of Hölder conjugate exponents `q, q'` with `2q ≤ p`, every ball `B_ρ = ball c ρ` and
every `κ ≥ 1`

`⨍_{B_ρ} ‖g - g_{B_ρ}‖² ≤ c₁ κ⁻² ⨍_{B_{κρ}} ‖g‖² + c₂ κ^(n + 1) ⨍_{B_{κρ}} ‖G‖²`
`  + c₃ κ^(n + 1) (L^(2q' - 1) δ)^(1/q') (⨍_{B_{κρ}} ‖g‖^(2q))^(1/q)`.

Then `‖g‖_{Lᵖ} ≤ C ‖G‖_{Lᵖ}`. -/
theorem exists_eLpNorm_le_of_forall_setAverage_norm_sub_sq_le [CompleteSpace E]
    {p : ℝ≥0∞} (hp : 2 < p) (hp_top : p ≠ ∞) (c₁ c₂ c₃ L : ℝ) :
    ∃ C : ℝ≥0, ∃ δ : ℝ, 0 < δ ∧
      ∀ {g : EuclideanSpace ℝ (Fin (n + 1)) → E} {G : EuclideanSpace ℝ (Fin (n + 1)) → F},
        MemLp g p volume → MemLp G p volume →
        (∀ q q' : ℝ, q.HolderConjugate q' → ENNReal.ofReal (2 * q) ≤ p →
          ∀ (c : EuclideanSpace ℝ (Fin (n + 1))) (ρ κ : ℝ), 0 < ρ → 1 ≤ κ →
            ⨍ y in ball c ρ, ‖g y - ⨍ z in ball c ρ, g z‖ ^ 2 ≤
              c₁ / κ ^ 2 * (⨍ y in ball c (κ * ρ), ‖g y‖ ^ 2) +
                c₂ * κ ^ (n + 1) * (⨍ y in ball c (κ * ρ), ‖G y‖ ^ 2) +
                c₃ * κ ^ (n + 1) * (L ^ (2 * q' - 1) * δ) ^ q'⁻¹ *
                  (⨍ y in ball c (κ * ρ), ‖g y‖ ^ (2 * q)) ^ q⁻¹) →
        eLpNorm g p volume ≤ C * eLpNorm G p volume := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = p.toReal := ⟨_, rfl⟩
  have hs : 2 < s := by
    rw [hs_def]
    simpa using (ENNReal.toReal_lt_toReal ENNReal.ofNat_ne_top hp_top).2 hp
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = (1 + s / 2) / 2 := ⟨_, rfl⟩
  have hq : 1 < q := by rw [hq_def]; linarith
  have hqs : 2 * q < s := by rw [hq_def]; linarith
  obtain ⟨q', hqq⟩ : ∃ q' : ℝ, q.HolderConjugate q' :=
    ⟨_, Real.HolderConjugate.conjExponent hq⟩
  have hqp : ENNReal.ofReal (2 * q) ≤ p := by
    rw [← ENNReal.ofReal_toReal hp_top, ← hs_def]
    exact ENNReal.ofReal_le_ofReal hqs.le
  obtain ⟨CFS, hFS⟩ := exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow
    (ι := Fin (n + 1)) (show 1 < s by linarith)
  have hcM := maximalFunctionConst_ne_top (n + 1)
  have h2 : (2 : ℝ≥0∞) ^ (s / 2 - 1) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top
  obtain ⟨κ, hκ, hκ1, δ, hδ, hδ1⟩ := exists_one_le_and_pos_of_ne_top (n := n) c₁ c₃ L (q := q)
    hqq.symm.pos (by linarith : 0 < s)
    (K₁ := (CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2))
    (K₃ := (CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * maximalFunctionConst (n + 1) (s / 2 / q))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
      (hcM _))
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) (hcM _))
  set C : ℝ≥0∞ := ((CFS : ℝ≥0∞) * 2 ^ (s / 2 - 1) * 2 ^ (s / 2 - 1) *
    forcingCoeff n c₂ κ ^ (s / 2) * maximalFunctionConst (n + 1) (s / 2) * 2) ^ (1 / s)
  have hK₂ : C ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (by linarith)) (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top h2) h2)
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)) (hcM _))
      ENNReal.ofNat_ne_top)
  refine ⟨C.toNNReal, δ, hδ, fun {g G} hgp hGp hosc => ?_⟩
  rw [ENNReal.coe_toNNReal hK₂]
  -- The Fefferman–Stein inequality applies to `g ∈ Lᵖ` itself, with `p₀ = p`.
  exact eLpNorm_le_of_le_quarter hp hp_top hgp hGp hs_def hq hqs
    (hFS hgp (one_le_two.trans hp.le) (by rw [hs_def, ENNReal.ofReal_toReal hp_top]))
    (sq_sharpMaximalFunction_le hp.le hgp hqq hκ fun c ρ hρ => hosc q q' hqq hqp c ρ κ hρ hκ)
    hκ1 hδ1

end PDE

end TauCeti
