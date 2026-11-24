/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Sobolev
import TauCeti.MeasureTheory.Integral.AbsRpow

/-!
# Subcritical Yamabe quotients and their infima

Let `(M, g)` be a closed smooth Riemannian manifold of dimension `n > 2`, with volume `V`, energy
form `E_g(w, w) = aₙ ∫ |∇w|² dV + ∫ Scal_g w² dV` on `H¹(M)` (`TauCeti.Yamabe.energyForm`) and
critical exponent `pₙ = 2 n / (n - 2)`. For an exponent `q`, the subcritical Yamabe quotient is

`Q^q(w) = E_g(w, w) / (∫ |w| ^ q dV) ^ (2 / q)`

(`TauCeti.Yamabe.subcriticalYamabeQuotient`), and its infimum over nonzero `w ∈ H¹(M)` is the
subcritical Yamabe constant `Y_q`. At `q = pₙ` these are the weak Yamabe quotient and the Yamabe
invariant `Y` of the conformal class of `g`. The subcritical problems `2 ≤ q < pₙ` approximate the
Yamabe problem from below, and this file compares the constants `Y_q` across exponents.

Hölder's inequality `(∫ |w| ^ q dV) ^ (2 / q) ≤ (∫ |w| ^ q' dV) ^ (2 / q') V ^ (2 / q - 2 / q')`
for `q ≤ q'` drives everything:

* For `2 ≤ q ≤ pₙ`, comparing with `q = 2` bounds the scalar-curvature term below, so
  `Q^q ≥ -K V ^ (1 - 2 / q)` whenever `Scal_g ≥ -K` with `K ≥ 0`, and the constants `Y_q` are finite
  (`TauCeti.Yamabe.bddBelow_image_subcriticalYamabeQuotient`).
* For unit volume, `Q^q(w)` decreases in `q` when `E_g(w, w) ≥ 0` and increases in `q` when
  `E_g(w, w) ≤ 0`. Hence `|Y_q|` is nonincreasing in `q ∈ [2, pₙ]`
  (`TauCeti.Yamabe.antitoneOn_abs_sInf_subcriticalYamabeQuotient`). Unit volume is needed: on the
  unit round `S³`, of volume `2π²`, the constant function has `Q^4(1) = 6 (2π²) ^ (1 / 2) ≈ 26.66`,
  below `|Y_6| = Y(S³) ≈ 43.82`.
* If `Y ≥ 0`, then `Y_q → Y` as `q` increases to `pₙ`, for any volume
  (`TauCeti.Yamabe.tendsto_sInf_subcriticalYamabeQuotient_nhdsLT`). Below, every quotient is at
  least `Y V ^ (2 / pₙ - 2 / q)`, since the energy is nonnegative; above, the quotient of a fixed
  `w` converges to `Q^{pₙ}(w)` because the moments of `w` depend continuously on the exponent.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §4,
  Lemma 4.3.
* H. Yamabe, *On a deformation of Riemannian structures on compact manifolds*, Osaka Math. J. 12
  (1960), 21–37.
-/

public section

open Bundle Filter MeasureTheory Module Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [CompactSpace M]
  [IsManifold I ∞ M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-! ### Comparison of denominators -/

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **Hölder comparison of the denominators.** For `0 < q ≤ q' ≤ pₙ` and `w ∈ H¹(M)`,
`(∫ |w| ^ q dV) ^ (2 / q) ≤ (∫ |w| ^ q' dV) ^ (2 / q') V ^ (2 / q - 2 / q')`. -/
private theorem rpow_integral_abs_toLp_rpow_le {q q' : ℝ} (hq : 0 < q) (hqq' : q ≤ q')
    (hq' : q' ≤ criticalExponent (finrank ℝ E)) (w : SobolevH1 I M) :
    (∫ x, |SobolevH1.toLp w x| ^ q ∂riemannianVolume I M) ^ (2 / q) ≤
      (∫ x, |SobolevH1.toLp w x| ^ q' ∂riemannianVolume I M) ^ (2 / q') *
        riemannianTotalVolume I M ^ (2 / q - 2 / q') := by
  have hq'0 : 0 < q' := hq.trans_le hqq'
  have hn : 2 < finrank ℝ E := criticalExponent_pos_iff.1 (hq'0.trans_le hq')
  have h := (SobolevH1.memLp_toLp hn (ENNReal.ofReal_le_ofReal
    (hq'.trans (criticalExponent_def _).le)) w).integral_abs_rpow_le_mul_measureReal_univ_rpow
      hq hqq'
  rw [← riemannianTotalVolume_def] at h
  have hN' : 0 ≤ ∫ x, |SobolevH1.toLp w x| ^ q' ∂riemannianVolume I M :=
    integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hV := riemannianTotalVolume_nonneg (I := I) (M := M)
  refine (Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _) h
    (by positivity)).trans_eq ?_
  rw [Real.mul_rpow (Real.rpow_nonneg hN' _) (Real.rpow_nonneg hV _), ← Real.rpow_mul hN',
    ← Real.rpow_mul hV]
  congr 2 <;> field_simp

omit [T2Space M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Under unit volume the denominators increase with the exponent: for `0 < q ≤ q' ≤ pₙ`,
`(∫ |w| ^ q dV) ^ (2 / q) ≤ (∫ |w| ^ q' dV) ^ (2 / q')`. -/
private theorem rpow_integral_abs_toLp_rpow_le_of_riemannianTotalVolume_eq_one
    (hV : riemannianTotalVolume I M = 1) {q q' : ℝ} (hq : 0 < q)
    (hqq' : q ≤ q') (hq' : q' ≤ criticalExponent (finrank ℝ E)) (w : SobolevH1 I M) :
    (∫ x, |SobolevH1.toLp w x| ^ q ∂riemannianVolume I M) ^ (2 / q) ≤
      (∫ x, |SobolevH1.toLp w x| ^ q' ∂riemannianVolume I M) ^ (2 / q') := by
  simpa only [hV, Real.one_rpow, mul_one] using rpow_integral_abs_toLp_rpow_le hq hqq' hq' w

/-- The denominator of a nonzero `w ∈ H¹(M)` is positive for `0 < q ≤ pₙ`. -/
private theorem rpow_integral_abs_toLp_rpow_pos {q : ℝ} (hq : 0 < q)
    (hqp : q ≤ criticalExponent (finrank ℝ E)) {w : SobolevH1 I M} (hw : w ≠ 0) :
    0 < (∫ x, |SobolevH1.toLp w x| ^ q ∂riemannianVolume I M) ^ (2 / q) :=
  Real.rpow_pos_of_pos ((SobolevH1.integral_abs_toLp_rpow_pos_iff
    (criticalExponent_pos_iff.1 (hq.trans_le hqp)) hq
    (hqp.trans (criticalExponent_def _).le)).2 hw) _

/-! ### Lower bounds -/

/-- **Lower bound for the subcritical Yamabe quotient.** If `Scal_g ≥ -K` with `K ≥ 0`, then for
`2 ≤ q ≤ pₙ` every `w ∈ H¹(M)` satisfies `Q^q(w) ≥ -K V ^ (1 - 2 / q)`. -/
theorem neg_mul_rpow_le_subcriticalYamabeQuotient {q K : ℝ} (hq : 2 ≤ q)
    (hqp : q ≤ criticalExponent (finrank ℝ E)) (hK : 0 ≤ K)
    (hS : ∀ x, -K ≤ (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x)
    (w : SobolevH1 I M) :
    -K * riemannianTotalVolume I M ^ (1 - 2 / q) ≤ subcriticalYamabeQuotient I q w := by
  have hV := riemannianTotalVolume_nonneg (I := I) (M := M)
  rcases eq_or_ne w 0 with rfl | hw
  · rw [subcriticalYamabeQuotient_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hK) (Real.rpow_nonneg hV _)
  set S := (CovariantDerivative.leviCivitaConnection I M).scalarCurvature
  set f := ⇑(SobolevH1.toLp w)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous.continuousOn
  have hsq : Integrable (fun x ↦ f x ^ 2) (riemannianVolume I M) :=
    (Lp.memLp (SobolevH1.toLp w)).integrable_sq
  have hSff : Integrable (fun x ↦ S x * f x * f x) (riemannianVolume I M) := by
    simpa only [mul_assoc, ← sq] using hsq.bdd_mul
      (Continuous.aestronglyMeasurable
        (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous)
      (.of_forall fun x ↦ hC x (mem_univ x))
  -- The energy is at least `-K ∫ w²`, since the Dirichlet term is nonnegative.
  have hE : -K * ∫ x, f x ^ 2 ∂riemannianVolume I M ≤ energyForm I w w := by
    rw [energyForm_apply, ← integral_const_mul]
    refine le_add_of_nonneg_of_le (mul_nonneg (conformalCoefficient_nonneg _)
      (SobolevH1.dirichletForm_self_nonneg w)) (integral_mono (hsq.const_mul _) hSff fun x ↦ ?_)
    dsimp only
    rw [mul_assoc, ← sq]
    exact mul_le_mul_of_nonneg_right (hS x) (sq_nonneg _)
  -- Hölder's inequality compares `∫ w²` with the `q`-th moment.
  have h2 := rpow_integral_abs_toLp_rpow_le two_pos hq hqp w
  have hf2 : ∫ x, |f x| ^ (2 : ℝ) ∂riemannianVolume I M = ∫ x, f x ^ 2 ∂riemannianVolume I M :=
    integral_congr_ae (.of_forall fun x ↦ by simp only [Real.rpow_two, sq_abs])
  rw [div_self two_ne_zero, Real.rpow_one, hf2] at h2
  rw [subcriticalYamabeQuotient_def,
    le_div_iff₀ (rpow_integral_abs_toLp_rpow_pos (two_pos.trans_le hq) hqp hw)]
  calc -K * riemannianTotalVolume I M ^ (1 - 2 / q) *
        (∫ x, |f x| ^ q ∂riemannianVolume I M) ^ (2 / q) =
      -K * ((∫ x, |f x| ^ q ∂riemannianVolume I M) ^ (2 / q) *
        riemannianTotalVolume I M ^ (1 - 2 / q)) := by ring
    _ ≤ -K * ∫ x, f x ^ 2 ∂riemannianVolume I M :=
      mul_le_mul_of_nonpos_left h2 (neg_nonpos.2 hK)
    _ ≤ energyForm I w w := hE

/-- On a closed manifold of dimension `n > 2`, the subcritical Yamabe quotients of nonzero `H¹`
elements are bounded below for every exponent `2 ≤ q ≤ pₙ`. -/
theorem bddBelow_image_subcriticalYamabeQuotient {q : ℝ} (hq : 2 ≤ q)
    (hqp : q ≤ criticalExponent (finrank ℝ E)) :
    BddBelow (subcriticalYamabeQuotient I q '' {w : SobolevH1 I M | w ≠ 0}) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (CovariantDerivative.leviCivitaConnection I M).contMDiff_scalarCurvature.continuous.continuousOn
  refine ⟨_, fun _ ⟨w, _, h⟩ ↦ h ▸ neg_mul_rpow_le_subcriticalYamabeQuotient hq hqp
    (le_max_right C 0) (fun x ↦ ?_) w⟩
  have := hC x (mem_univ x)
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le ((CovariantDerivative.leviCivitaConnection I M).scalarCurvature x),
    le_max_left C 0]

/-! ### Monotonicity in the exponent under unit volume -/

/-- **Nonnegative energy makes the quotient decrease in the exponent.** For unit volume,
`0 < q ≤ q' ≤ pₙ` and `w ≠ 0` with `E_g(w, w) ≥ 0`, `Q^{q'}(w) ≤ Q^q(w)`. -/
theorem subcriticalYamabeQuotient_le_of_energyForm_nonneg
    (hV : riemannianTotalVolume I M = 1) {q q' : ℝ} (hq : 0 < q) (hqq' : q ≤ q')
    (hq' : q' ≤ criticalExponent (finrank ℝ E)) {w : SobolevH1 I M}
    (hE : 0 ≤ energyForm I w w) :
    subcriticalYamabeQuotient I q' w ≤ subcriticalYamabeQuotient I q w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [subcriticalYamabeQuotient_def, subcriticalYamabeQuotient_def]
  exact div_le_div_of_nonneg_left hE (rpow_integral_abs_toLp_rpow_pos hq (hqq'.trans hq') hw)
    (rpow_integral_abs_toLp_rpow_le_of_riemannianTotalVolume_eq_one hV hq hqq' hq' w)

/-- **Nonpositive energy makes the quotient increase in the exponent.** For unit volume,
`0 < q ≤ q' ≤ pₙ` and `w ≠ 0` with `E_g(w, w) ≤ 0`, `Q^q(w) ≤ Q^{q'}(w)`. -/
theorem subcriticalYamabeQuotient_le_of_energyForm_nonpos
    (hV : riemannianTotalVolume I M = 1) {q q' : ℝ} (hq : 0 < q) (hqq' : q ≤ q')
    (hq' : q' ≤ criticalExponent (finrank ℝ E)) {w : SobolevH1 I M}
    (hE : energyForm I w w ≤ 0) :
    subcriticalYamabeQuotient I q w ≤ subcriticalYamabeQuotient I q' w := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [subcriticalYamabeQuotient_def, subcriticalYamabeQuotient_def, ← neg_le_neg_iff, ← neg_div,
    ← neg_div]
  exact div_le_div_of_nonneg_left (neg_nonneg.2 hE)
    (rpow_integral_abs_toLp_rpow_pos hq (hqq'.trans hq') hw)
    (rpow_integral_abs_toLp_rpow_le_of_riemannianTotalVolume_eq_one hV hq hqq' hq' w)

/-- **Monotonicity of the subcritical Yamabe constants.** On a closed manifold of dimension `n > 2`
and unit volume, `|Y_q| = |inf {Q^q(w) | w ≠ 0}|` is nonincreasing in `q ∈ [2, pₙ]`. -/
theorem antitoneOn_abs_sInf_subcriticalYamabeQuotient (hV : riemannianTotalVolume I M = 1) :
    AntitoneOn (fun q ↦ |sInf (subcriticalYamabeQuotient I q '' {w : SobolevH1 I M | w ≠ 0})|)
      (Icc 2 (criticalExponent (finrank ℝ E))) := by
  intro q hq q' hq' hqq'
  dsimp only
  have : Nonempty M := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [riemannianTotalVolume_def, univ_eq_empty_iff.2 h, measureReal_empty] at hV
    exact zero_ne_one hV
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : SobolevH1 I M)
  have hq0 : 0 < q := two_pos.trans_le hq.1
  have hbdd := bddBelow_image_subcriticalYamabeQuotient (I := I) (M := M) hq.1 hq.2
  have hbdd' := bddBelow_image_subcriticalYamabeQuotient (I := I) (M := M) hq'.1 hq'.2
  have hne (r : ℝ) : (subcriticalYamabeQuotient I r '' {w : SobolevH1 I M | w ≠ 0}).Nonempty :=
    ⟨_, w₀, hw₀, rfl⟩
  have hpos {r : ℝ} (hr : r ∈ Icc 2 (criticalExponent (finrank ℝ E))) {w : SobolevH1 I M}
      (hw : w ≠ 0) :
      0 < (∫ x, |SobolevH1.toLp w x| ^ r ∂riemannianVolume I M) ^ (2 / r) :=
    rpow_integral_abs_toLp_rpow_pos (two_pos.trans_le hr.1) hr.2 hw
  by_cases hE : ∀ w : SobolevH1 I M, 0 ≤ energyForm I w w
  · -- Nonnegative energy: both constants are nonnegative and `Y_{q'} ≤ Y_q`.
    have h0 : 0 ≤ sInf (subcriticalYamabeQuotient I q' '' {w : SobolevH1 I M | w ≠ 0}) :=
      Real.sInf_nonneg fun _ ⟨w, hw, h⟩ ↦ h ▸ by
        rw [subcriticalYamabeQuotient_def]; exact div_nonneg (hE w) (hpos hq' hw).le
    refine (abs_of_nonneg h0).trans_le (le_trans ?_ (le_abs_self _))
    refine le_csInf (hne q) fun _ ⟨w, hw, h⟩ ↦ h ▸ (csInf_le hbdd' ⟨w, hw, rfl⟩).trans ?_
    exact subcriticalYamabeQuotient_le_of_energyForm_nonneg hV hq0 hqq' hq'.2 (hE w)
  · -- Some negative energy: both constants are negative and `Y_q ≤ Y_{q'}`.
    simp only [not_forall, not_le] at hE
    obtain ⟨w₁, hw₁⟩ := hE
    have hw₁0 : w₁ ≠ 0 := by rintro rfl; simp at hw₁
    have hneg {r : ℝ} (hr : r ∈ Icc 2 (criticalExponent (finrank ℝ E))) :
        sInf (subcriticalYamabeQuotient I r '' {w : SobolevH1 I M | w ≠ 0}) < 0 :=
      (csInf_le (bddBelow_image_subcriticalYamabeQuotient hr.1 hr.2) ⟨w₁, hw₁0, rfl⟩).trans_lt
        (by rw [subcriticalYamabeQuotient_def]; exact div_neg_of_neg_of_pos hw₁ (hpos hr hw₁0))
    rw [abs_of_neg (hneg hq'), abs_of_neg (hneg hq), neg_le_neg_iff]
    refine le_csInf (hne q') fun _ ⟨w, hw, h⟩ ↦ h ▸ ?_
    rcases le_or_gt (energyForm I w w) 0 with hEw | hEw
    · exact (csInf_le hbdd ⟨w, hw, rfl⟩).trans
        (subcriticalYamabeQuotient_le_of_energyForm_nonpos hV hq0 hqq' hq'.2 hEw)
    · rw [subcriticalYamabeQuotient_def]
      exact (hneg hq).le.trans (div_pos hEw (hpos hq' hw)).le

/-! ### Left continuity at the critical exponent -/

/-- If the energy is nonnegative, then for `0 < q ≤ pₙ` the subcritical constant `Y_q` is at least
`Y / V ^ (2 / q - 2 / pₙ)`. -/
private theorem div_rpow_le_sInf_subcriticalYamabeQuotient [Nonempty M]
    (hE : ∀ w : SobolevH1 I M, 0 ≤ energyForm I w w) {q : ℝ} (hq : 0 < q)
    (hqp : q ≤ criticalExponent (finrank ℝ E)) :
    sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}) /
        riemannianTotalVolume I M ^ (2 / q - 2 / criticalExponent (finrank ℝ E)) ≤
      sInf (subcriticalYamabeQuotient I q '' {w : SobolevH1 I M | w ≠ 0}) := by
  have hn : 2 < finrank ℝ E := criticalExponent_pos_iff.1 (hq.trans_le hqp)
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : SobolevH1 I M)
  have hVa : 0 < riemannianTotalVolume I M ^ (2 / q - 2 / criticalExponent (finrank ℝ E)) :=
    Real.rpow_pos_of_pos riemannianTotalVolume_pos _
  refine le_csInf ⟨_, w₀, hw₀, rfl⟩ fun _ ⟨w, hw, h⟩ ↦ h ▸ ?_
  calc sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}) /
        riemannianTotalVolume I M ^ (2 / q - 2 / criticalExponent (finrank ℝ E)) ≤
      weakYamabeQuotient I w /
        riemannianTotalVolume I M ^ (2 / q - 2 / criticalExponent (finrank ℝ E)) :=
      div_le_div_of_nonneg_right
        (csInf_le (bddBelow_image_weakYamabeQuotient hn) ⟨w, hw, rfl⟩) hVa.le
    _ = energyForm I w w /
        ((∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E) ∂riemannianVolume I M) ^
            (2 / criticalExponent (finrank ℝ E)) *
          riemannianTotalVolume I M ^ (2 / q - 2 / criticalExponent (finrank ℝ E))) := by
      rw [weakYamabeQuotient_def, div_div]
    _ ≤ subcriticalYamabeQuotient I q w := by
      rw [subcriticalYamabeQuotient_def]
      exact div_le_div_of_nonneg_left (hE w)
        (rpow_integral_abs_toLp_rpow_pos hq hqp hw)
        (rpow_integral_abs_toLp_rpow_le hq hqp le_rfl w)

/-- For a fixed nonzero `w ∈ H¹(M)`, `Q^q(w) → Q^{pₙ}(w)` as `q` increases to `pₙ`. -/
private theorem tendsto_subcriticalYamabeQuotient_nhdsLT (hn : 2 < finrank ℝ E)
    {w : SobolevH1 I M} (hw : w ≠ 0) :
    Tendsto (fun q ↦ subcriticalYamabeQuotient I q w) (𝓝[<] criticalExponent (finrank ℝ E))
      (𝓝 (weakYamabeQuotient I w)) := by
  have hp := criticalExponent_pos hn
  have hN : Tendsto (fun q ↦ ∫ x, |SobolevH1.toLp w x| ^ q ∂riemannianVolume I M)
      (𝓝[<] criticalExponent (finrank ℝ E))
      (𝓝 (∫ x, |SobolevH1.toLp w x| ^ criticalExponent (finrank ℝ E)
        ∂riemannianVolume I M)) :=
    ((SobolevH1.memLp_toLp hn (ENNReal.ofReal_le_ofReal (criticalExponent_def _).le)
      w).continuousOn_integral_abs_rpow _ ⟨hp, le_rfl⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsLT hp) Ioo_subset_Ioc_self)
  have hN0 := (SobolevH1.integral_abs_toLp_rpow_pos_iff hn hp (criticalExponent_def _).le).2 hw
  have hD := hN.rpow ((tendsto_const_nhds (x := (2 : ℝ))).div tendsto_id hp.ne'
    |>.mono_left nhdsWithin_le_nhds) (Or.inl hN0.ne')
  rw [weakYamabeQuotient_def]
  refine (tendsto_const_nhds.div hD (Real.rpow_pos_of_pos hN0 _).ne').congr fun q ↦ ?_
  simp only [subcriticalYamabeQuotient_def, Pi.div_apply, id_eq]

/-- **Left continuity of the subcritical Yamabe constants at the critical exponent.** On a closed
manifold of dimension `n > 2` whose Yamabe invariant `Y = inf {Q^{pₙ}(w) | w ≠ 0}` is nonnegative,
`Y_q = inf {Q^q(w) | w ≠ 0}` tends to `Y` as `q` increases to `pₙ`. -/
theorem tendsto_sInf_subcriticalYamabeQuotient_nhdsLT (hn : 2 < finrank ℝ E)
    (hY : 0 ≤ sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0})) :
    Tendsto (fun q ↦ sInf (subcriticalYamabeQuotient I q '' {w : SobolevH1 I M | w ≠ 0}))
      (𝓝[<] criticalExponent (finrank ℝ E))
      (𝓝 (sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}))) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · simp only [eq_empty_of_forall_notMem (s := {w : SobolevH1 I M | w ≠ 0})
      fun w hw ↦ hw (Subsingleton.elim w 0), image_empty]
    exact tendsto_const_nhds
  set Y := sInf (weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0})
  have hp := two_lt_criticalExponent hn
  have hIoo : Ioo 2 (criticalExponent (finrank ℝ E)) ∈ 𝓝[<] criticalExponent (finrank ℝ E) :=
    Ioo_mem_nhdsLT hp
  -- A nonnegative Yamabe invariant forces the energy to be nonnegative.
  have hE (w : SobolevH1 I M) : 0 ≤ energyForm I w w := by
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    have hQ := hY.trans (csInf_le (bddBelow_image_weakYamabeQuotient hn) ⟨w, hw, rfl⟩)
    rwa [weakYamabeQuotient_def, le_div_iff₀ (rpow_integral_abs_toLp_rpow_pos
      (criticalExponent_pos hn) le_rfl hw), zero_mul] at hQ
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · -- From below: `Y_q ≥ Y / V ^ (2 / q - 2 / pₙ)`, which tends to `Y`.
    have hlim : Tendsto (fun q ↦ Y / riemannianTotalVolume I M ^
        (2 / q - 2 / criticalExponent (finrank ℝ E))) (𝓝[<] criticalExponent (finrank ℝ E))
        (𝓝 Y) := by
      have hc : ContinuousAt (fun q ↦ Y / riemannianTotalVolume I M ^
          (2 / q - 2 / criticalExponent (finrank ℝ E))) (criticalExponent (finrank ℝ E)) :=
        continuousAt_const.div ((Real.continuousAt_const_rpow riemannianTotalVolume_pos.ne').comp
          ((continuousAt_const.div continuousAt_id (criticalExponent_pos hn).ne').sub
            continuousAt_const))
          (Real.rpow_pos_of_pos riemannianTotalVolume_pos _).ne'
      simpa only [sub_self, Real.rpow_zero, div_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
    filter_upwards [hlim.eventually (lt_mem_nhds ha), hIoo] with q hq hq'
    exact hq.trans_le (div_rpow_le_sInf_subcriticalYamabeQuotient hE
      (two_pos.trans hq'.1) hq'.2.le)
  · -- From above: a fixed `w` with `Q^{pₙ}(w) < b` has `Q^q(w) < b` for `q` near `pₙ`.
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : SobolevH1 I M)
    obtain ⟨_, ⟨w, hw, rfl⟩, hwb⟩ := exists_lt_of_csInf_lt
      (s := weakYamabeQuotient I '' {w : SobolevH1 I M | w ≠ 0}) ⟨_, w₀, hw₀, rfl⟩ hb
    filter_upwards [(tendsto_subcriticalYamabeQuotient_nhdsLT hn hw).eventually (gt_mem_nhds hwb),
      hIoo] with q hq hq'
    exact (csInf_le (bddBelow_image_subcriticalYamabeQuotient hq'.1.le hq'.2.le)
      ⟨w, hw, rfl⟩).trans_lt hq

end TauCeti.Yamabe
