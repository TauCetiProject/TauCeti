/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Bases.Unconditional
public import TauCeti.MeasureTheory.Function.Lp.HaarBasis.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Burkholder
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Unconditionality of the Haar basis of `Lᵖ([0, 1])`

For `1 < p < ∞` and real or complex scalars `𝕜`, the Haar basis `haarBasis 𝕜 p hp` of
`Lᵖ([0, 1]; 𝕜)` is unconditional, with Burkholder's sign-transform constant
`p* - 1 = max(p, p / (p - 1)) - 1` over `ℝ` and twice that constant over `𝕜`.

The proof follows Burkholder's Bellman-function method:

* For `2 ≤ p < ∞` and real coefficients, we integrate the scalar midpoint inequality
  `TauCeti.two_mul_burkholderPhi_abs_le` inductively over each split dyadic atom to show that
  `∫ Φ_p(|F_N|, |G_N|) ≥ 0` for any finite real Haar sum `F_N` and its sign transform `G_N`.
  Combining this with the majorization `TauCeti.mul_burkholderPhi_le` yields
  `‖G_N‖_p ≤ (p - 1) ‖F_N‖_p`.
* At `p = 2`, orthogonality of the Haar functions gives the Parseval identity
  `‖∑_{n ∈ s} a_n h_n‖_2 ^ 2 = ∑_{n ∈ s} ‖a_n‖ ^ 2 * 2 ^ (-⌊log₂ n⌋)` over both `ℝ` and `ℂ`, so
  unit-modulus multipliers are isometries.
* For `1 < p < 2` and real coefficients, duality with the conjugate exponent `q = p / (p - 1) > 2`
  via `MeasureTheory.Lp.toDual` and the contractivity of `dyadicProj ℝ q N` yields
  `‖G_N‖_p ≤ (q - 1) ‖F_N‖_p`.
* Splitting complex coefficients into real and imaginary parts yields the sign-transform bound
  `2 * (max(p, p / (p - 1)) - 1)` for any `[RCLike 𝕜]`. Since the initial projections
  `dyadicProj 𝕜 p N` are contractions, `SchauderBasis.norm_proj_le_of_sign_bound` gives a uniform
  bound on all finite coordinate projections and upgrades `haarBasis 𝕜 p hp` to
  `unconditionalHaarBasis 𝕜 p hp1 hp`.

## Main definitions

* `TauCeti.unitInterval.unconditionalHaarBasis`: the Haar basis of `Lᵖ([0, 1]; 𝕜)` (`1 < p < ∞`)
  as an `UnconditionalSchauderBasis`.

## Main results

* `TauCeti.unitInterval.norm_sum_smul_haarBasis_two_sq` and
  `TauCeti.unitInterval.norm_sum_mul_smul_haarBasis_two`: `L²` orthogonality and unit-modulus
  multiplier isometry for finite Haar expansions over `ℝ` and `ℂ`.
* `TauCeti.unitInterval.norm_sum_mul_smul_haarBasis_real_le`: Burkholder's bound
  `max(p, p / (p - 1)) - 1` for real Haar sign transforms on `Lᵖ([0, 1])`, `1 < p < ∞`.
* `TauCeti.unitInterval.norm_sum_mul_smul_haarBasis_le`: the sign-transform bound
  `2 * (max(p, p / (p - 1)) - 1)` over `ℝ` and `ℂ`.
* `TauCeti.unitInterval.norm_proj_haarBasis_real_le`, `TauCeti.unitInterval.norm_proj_haarBasis_le`,
  `TauCeti.unitInterval.nnNormProjBound_unconditionalHaarBasis_real_le`, and
  `TauCeti.unitInterval.nnNormProjBound_unconditionalHaarBasis_le`: uniform bounds on all finite
  Haar coordinate projections and on the unconditional basis constant.

## References

* D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
  Ann. Probab. **12** (1984), 647–702.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Graduate Texts in
  Mathematics 233, Springer (2016), §6.1.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped ENNReal unitInterval

namespace TauCeti.unitInterval

/-! ### Finite real Haar sums and Burkholder's estimate for `2 ≤ p` -/

/-- Pointwise finite real Haar expansion of length `N`. -/
private def haarSum (a : ℕ → ℝ) (N : ℕ) (x : I) : ℝ :=
  ∑ n ∈ Finset.range N, a n * haarFun n x

private theorem haarSum_succ (a : ℕ → ℝ) (N : ℕ) (x : I) :
    haarSum a (N + 1) x = haarSum a N x + a N * haarFun N x :=
  Finset.sum_range_succ _ N

private theorem measurable_haarSum (a : ℕ → ℝ) (N : ℕ) : Measurable (haarSum a N) :=
  Finset.measurable_sum _ fun n _ => measurable_const.mul (measurable_haarFun n)

private theorem abs_haarSum_le (a : ℕ → ℝ) (N : ℕ) (x : I) :
    |haarSum a N x| ≤ ∑ n ∈ Finset.range N, |a n| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (by simpa [Real.norm_eq_abs] using norm_haarFun_le n x)

private theorem haarSum_eq_of_mem_dyadicCell {N m : ℕ} (hm : m ∈ Set.Ico N (2 * N)) {x y : I}
    (hx : x ∈ dyadicCell m) (hy : y ∈ dyadicCell m) (a : ℕ → ℝ) :
    haarSum a N x = haarSum a N y :=
  Finset.sum_congr rfl fun n hn => by
    rw [haarFun_eq_of_mem_dyadicCell (Finset.mem_range.1 hn) hm hx hy]

private theorem coeFn_sum_smul_haarBasis {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (a : ℕ → 𝕜) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n • haarBasis 𝕜 p hp n : Lp 𝕜 p (volume : Measure I)) =ᵐ[volume]
      fun x => ∑ n ∈ Finset.range N, a n * (haarFun n x : 𝕜) := by
  have hterm (n : ℕ) : (a n • haarBasis 𝕜 p hp n : Lp 𝕜 p (volume : Measure I)) =ᵐ[volume]
      fun x => a n * (haarFun n x : 𝕜) :=
    (Lp.coeFn_smul _ _).trans ((coeFn_haarBasis (𝕜 := 𝕜) hp n).mono fun x hx => by
      rw [Pi.smul_apply, hx, smul_eq_mul])
  filter_upwards [Lp.coeFn_finsetSum (Finset.range N) fun n => a n • haarBasis 𝕜 p hp n,
    ae_all_iff.2 hterm] with x hx ht
  rw [hx, Finset.sum_apply]
  exact Finset.sum_congr rfl fun n _ => ht n

private theorem coeFn_sum_smul_haarBasis_real {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, a n • haarBasis ℝ p hp n : Lp ℝ p (volume : Measure I)) =ᵐ[volume]
      haarSum a N :=
  (coeFn_sum_smul_haarBasis (𝕜 := ℝ) hp a N).mono fun _ hx => by
    simpa only [haarSum, RCLike.ofReal_real_eq_id, id_eq] using hx

private theorem integrable_abs_haarSum_rpow {p : ℝ} (hp : 0 ≤ p) (a : ℕ → ℝ) (N : ℕ) :
    Integrable fun x => |haarSum a N x| ^ p := by
  refine Integrable.of_bound
    ((continuous_abs.measurable.comp (measurable_haarSum a N)).pow_const p).aestronglyMeasurable
    ((∑ n ∈ Finset.range N, |a n|) ^ p) (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (abs_haarSum_le a N x) hp

private theorem integrable_burkholderPhi_haarSum {p : ℝ} (hp : 2 ≤ p) (a b : ℕ → ℝ) (N : ℕ) :
    Integrable fun x => burkholderPhi p |haarSum a N x| |haarSum b N x| := by
  set A := ∑ n ∈ Finset.range N, |a n|
  set B := ∑ n ∈ Finset.range N, |b n|
  have hmA : Measurable fun x => |haarSum a N x| :=
    continuous_abs.measurable.comp (measurable_haarSum a N)
  have hmB : Measurable fun x => |haarSum b N x| :=
    continuous_abs.measurable.comp (measurable_haarSum b N)
  have hmeas : Measurable fun x => burkholderPhi p |haarSum a N x| |haarSum b N x| := by
    simp only [burkholderPhi_def]
    exact ((hmA.add hmB).pow_const (p - 1)).mul ((measurable_const.mul hmA).sub hmB)
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    ((A + B) ^ (p - 1) * ((p - 1) * A + B)) (ae_of_all _ fun x => ?_)
  have hFx : |haarSum a N x| ≤ A := abs_haarSum_le a N x
  have hGx : |haarSum b N x| ≤ B := abs_haarSum_le b N x
  rw [burkholderPhi_def, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) _)]
  refine mul_le_mul
    (Real.rpow_le_rpow (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (add_le_add hFx hGx) (by linarith))
    ?_ (abs_nonneg _) (Real.rpow_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.sum_nonneg fun _ _ => abs_nonneg _)) _)
  calc abs ((p - 1) * |haarSum a N x| - |haarSum b N x|)
      ≤ abs ((p - 1) * |haarSum a N x|) + abs |haarSum b N x| := abs_sub _ _
    _ = (p - 1) * |haarSum a N x| + |haarSum b N x| := by
        rw [abs_mul, abs_of_nonneg (by linarith), abs_abs, abs_abs]
    _ ≤ (p - 1) * A + B := by gcongr; linarith

/-- Splitting an integral on `I` over the `N` atoms of `dyadicFiltration N`. -/
private theorem integral_eq_sum_setIntegral_dyadicCell {N : ℕ} (hN : 0 < N) {f : I → ℝ}
    (hf : Integrable f) :
    ∫ x, f x = ∑ m ∈ Finset.Ico N (2 * N), ∫ x in dyadicCell m, f x := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Ico N (2 * N))) dyadicCell := by
    intro m₁ hm₁ m₂ hm₂ hne
    refine Set.disjoint_left.2 fun x hx₁ hx₂ => hne ?_
    exact ((dyadicAtom_eq_iff (Finset.mem_Ico.1 hm₁)).2 hx₁).symm.trans
      ((dyadicAtom_eq_iff (Finset.mem_Ico.1 hm₂)).2 hx₂)
  have hcov : ⋃ m ∈ Finset.Ico N (2 * N), dyadicCell m = Set.univ :=
    Set.eq_univ_of_forall fun x =>
      Set.mem_biUnion (Finset.mem_Ico.2 (dyadicAtom_mem_Ico hN x)) (mem_dyadicCell_dyadicAtom N x)
  rw [← setIntegral_univ, ← hcov,
    integral_biUnion_finset _ (fun m _ => measurableSet_dyadicCell m) hdisj
      (fun m _ => hf.integrableOn)]

private theorem volume_real_dyadicCell_two_mul_add {N e : ℕ} (hN : 0 < N) (he : e < 2) :
    volume.real (dyadicCell (2 * N + e)) = volume.real (dyadicCell N) / 2 := by
  rw [measureReal_def, measureReal_def, volume_dyadicCell_two_mul_add hN he, ENNReal.toReal_div,
    ENNReal.toReal_ofNat]

/-- On the split atom `dyadicCell N`, adding the `N`-th Haar term cannot decrease the integral of
`Φ_p(|F|, |G|)`: `F_N` and `G_N` are constant on `dyadicCell N`, and `h_N` is `+1` and `-1` on its
two equal halves. -/
private theorem setIntegral_burkholderPhi_haarSum_le_succ {p : ℝ} (hp : 2 ≤ p)
    {a ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) {N : ℕ} (hN : 0 < N) :
    ∫ x in dyadicCell N,
        burkholderPhi p |haarSum a N x| |haarSum (fun n => ε n * a n) N x| ≤
      ∫ x in dyadicCell N,
        burkholderPhi p |haarSum a (N + 1) x| |haarSum (fun n => ε n * a n) (N + 1) x| := by
  rcases (dyadicCell N).eq_empty_or_nonempty with hemp | ⟨x₀, hx₀⟩
  · simp [hemp]
  set u := haarSum a N x₀
  set v := haarSum (fun n => ε n * a n) N x₀
  have hmemN : N ∈ Set.Ico N (2 * N) := ⟨le_rfl, by omega⟩
  have hL : ∫ x in dyadicCell N,
        burkholderPhi p |haarSum a N x| |haarSum (fun n => ε n * a n) N x| =
      volume.real (dyadicCell N) * burkholderPhi p |u| |v| := by
    rw [setIntegral_congr_fun (measurableSet_dyadicCell N) fun x hx => by
      rw [haarSum_eq_of_mem_dyadicCell hmemN hx hx₀, haarSum_eq_of_mem_dyadicCell hmemN hx hx₀],
      setIntegral_const, smul_eq_mul]
  have hR0 : ∫ x in dyadicCell (2 * N),
        burkholderPhi p |haarSum a (N + 1) x| |haarSum (fun n => ε n * a n) (N + 1) x| =
      volume.real (dyadicCell (2 * N)) * burkholderPhi p |u + a N| |v + ε N * a N| := by
    rw [setIntegral_congr_fun (measurableSet_dyadicCell _) fun x hx => by
      have hxN := mem_dyadicCell_of_mem_two_mul_add (e := 0) hN two_pos hx
      simp only [haarSum_succ, haarFun_eq_one hN hx, mul_one]
      rw [haarSum_eq_of_mem_dyadicCell hmemN hxN hx₀, haarSum_eq_of_mem_dyadicCell hmemN hxN hx₀],
      setIntegral_const, smul_eq_mul]
  have hR1 : ∫ x in dyadicCell (2 * N + 1),
        burkholderPhi p |haarSum a (N + 1) x| |haarSum (fun n => ε n * a n) (N + 1) x| =
      volume.real (dyadicCell (2 * N + 1)) * burkholderPhi p |u - a N| |v - ε N * a N| := by
    rw [setIntegral_congr_fun (measurableSet_dyadicCell _) fun x hx => by
      have hxN := mem_dyadicCell_of_mem_two_mul_add hN one_lt_two hx
      simp only [haarSum_succ, haarFun_eq_neg_one hN hx, mul_neg, mul_one, ← sub_eq_add_neg]
      rw [haarSum_eq_of_mem_dyadicCell hmemN hxN hx₀, haarSum_eq_of_mem_dyadicCell hmemN hxN hx₀],
      setIntegral_const, smul_eq_mul]
  have hR : ∫ x in dyadicCell N,
        burkholderPhi p |haarSum a (N + 1) x| |haarSum (fun n => ε n * a n) (N + 1) x| =
      volume.real (dyadicCell N) / 2 *
        (burkholderPhi p |u + a N| |v + ε N * a N| +
          burkholderPhi p |u - a N| |v - ε N * a N|) := by
    have hvol0 : volume.real (dyadicCell (2 * N)) = volume.real (dyadicCell N) / 2 := by
      simpa using volume_real_dyadicCell_two_mul_add (e := 0) hN two_pos
    conv_lhs => rw [dyadicCell_eq_union hN]
    rw [setIntegral_union disjoint_dyadicCell_two_mul (measurableSet_dyadicCell _)
        (integrable_burkholderPhi_haarSum hp _ _ _).integrableOn
        (integrable_burkholderPhi_haarSum hp _ _ _).integrableOn,
      hR0, hR1, volume_real_dyadicCell_two_mul_add hN one_lt_two, hvol0, ← mul_add]
  rw [hL, hR]
  have hmid := two_mul_burkholderPhi_abs_le hp u v (a N) (hε N)
  nlinarith [measureReal_nonneg (μ := (volume : Measure I)) (s := dyadicCell N)]

/-- Adding the `N`-th Haar term (`0 < N`) does not decrease `∫ Φ_p(|F|, |G|)`. -/
private theorem integral_burkholderPhi_haarSum_le_succ {p : ℝ} (hp : 2 ≤ p)
    {a ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) {N : ℕ} (hN : 0 < N) :
    ∫ x, burkholderPhi p |haarSum a N x| |haarSum (fun n => ε n * a n) N x| ≤
      ∫ x, burkholderPhi p |haarSum a (N + 1) x| |haarSum (fun n => ε n * a n) (N + 1) x| := by
  rw [integral_eq_sum_setIntegral_dyadicCell hN (integrable_burkholderPhi_haarSum hp _ _ _),
    integral_eq_sum_setIntegral_dyadicCell hN (integrable_burkholderPhi_haarSum hp _ _ _)]
  refine Finset.sum_le_sum fun m hm => ?_
  by_cases hmN : m = N
  · subst hmN
    exact setIntegral_burkholderPhi_haarSum_le_succ hp hε hN
  · refine le_of_eq (setIntegral_congr_fun (measurableSet_dyadicCell m) fun x hx => ?_)
    have hxN : x ∉ dyadicCell N := fun h => hmN <|
      ((dyadicAtom_eq_iff (Finset.mem_Ico.1 hm)).2 hx).symm.trans
        ((dyadicAtom_eq_iff ⟨le_rfl, by omega⟩).2 h)
    simp [haarSum_succ, haarFun_eq_zero hN hxN]

/-- For `2 ≤ p`, the integral of `Φ_p(|F_N|, |G_N|)` is nonnegative for every `N`. -/
private theorem integral_burkholderPhi_haarSum_nonneg {p : ℝ} (hp : 2 ≤ p)
    {a ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) (N : ℕ) :
    0 ≤ ∫ x, burkholderPhi p |haarSum a N x| |haarSum (fun n => ε n * a n) N x| := by
  induction N with
  | zero => simp [haarSum]
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine integral_nonneg fun x => ?_
      simp only [Nat.zero_add, haarSum, Finset.sum_range_one, haarFun_zero, Pi.one_apply, mul_one,
        abs_mul, hε 0, one_mul, burkholderPhi_def]
      refine mul_nonneg (Real.rpow_nonneg (by positivity) _) ?_
      nlinarith [abs_nonneg (a 0)]
    · exact ih.trans (integral_burkholderPhi_haarSum_le_succ hp hε hN)

/-- Burkholder's `Lᵖ` sign-transform inequality for real Haar sums at `2 ≤ p`, in integral form. -/
private theorem integral_abs_haarSum_rpow_le {p : ℝ} (hp : 2 ≤ p)
    {a ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) (N : ℕ) :
    ∫ x, |haarSum (fun n => ε n * a n) N x| ^ p ≤
      (p - 1) ^ p * ∫ x, |haarSum a N x| ^ p := by
  set c := (p - 1) ^ (p - 1) / p ^ (p - 2)
  have hc : 0 ≤ c :=
    div_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  have hintF := integrable_abs_haarSum_rpow (by linarith : 0 ≤ p) a N
  have hintG := integrable_abs_haarSum_rpow (by linarith : 0 ≤ p) (fun n => ε n * a n) N
  have hintΦ := integrable_burkholderPhi_haarSum hp a (fun n => ε n * a n) N
  have hle : c * (∫ x, burkholderPhi p |haarSum a N x| |haarSum (fun n => ε n * a n) N x|) ≤
      (p - 1) ^ p * (∫ x, |haarSum a N x| ^ p) - ∫ x, |haarSum (fun n => ε n * a n) N x| ^ p := by
    rw [← integral_const_mul c, ← integral_const_mul ((p - 1) ^ p),
      ← integral_sub (hintF.const_mul _) hintG]
    exact integral_mono (hintΦ.const_mul c) ((hintF.const_mul _).sub hintG) fun x =>
      mul_burkholderPhi_le hp (abs_nonneg _) (abs_nonneg _)
  have hnonneg :
      0 ≤ c * (∫ x, burkholderPhi p |haarSum a N x| |haarSum (fun n => ε n * a n) N x|) :=
    mul_nonneg hc (integral_burkholderPhi_haarSum_nonneg hp hε N)
  linarith

/-- Burkholder's sign-transform bound `p - 1` for real finite Haar sums when `2 ≤ p < ∞`. -/
private theorem norm_sum_mul_smul_haarBasis_real_le_of_two_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp2 : 2 ≤ p) (hp : p ≠ ∞) {a ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p hp n‖ ≤
      (p.toReal - 1) * ‖∑ n ∈ Finset.range N, a n • haarBasis ℝ p hp n‖ := by
  have hp0 : p ≠ 0 := (zero_lt_two.trans_le hp2).ne'
  have hpr : 2 ≤ p.toReal := by
    simpa using (ENNReal.toReal_le_toReal ENNReal.ofNat_ne_top hp).2 hp2
  set F : Lp ℝ p (volume : Measure I) := ∑ n ∈ Finset.range N, a n • haarBasis ℝ p hp n
  set G : Lp ℝ p (volume : Measure I) := ∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p hp n
  have hFint : ∫ x, |haarSum a N x| ^ p.toReal = ‖F‖ ^ p.toReal := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp F]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sum_smul_haarBasis_real hp a N] with x hx
    rw [hx, Real.norm_eq_abs]
  have hGint : ∫ x, |haarSum (fun n => ε n * a n) N x| ^ p.toReal = ‖G‖ ^ p.toReal := by
    rw [← Lp.integral_norm_rpow_eq_norm_rpow hp0 hp G]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sum_smul_haarBasis_real hp (fun n => ε n * a n) N] with x hx
    rw [hx, Real.norm_eq_abs]
  have hpow : ‖G‖ ^ p.toReal ≤ ((p.toReal - 1) * ‖F‖) ^ p.toReal := by
    rw [← hGint, Real.mul_rpow (by linarith) (norm_nonneg F), ← hFint]
    exact integral_abs_haarSum_rpow_le hpr hε N
  exact (Real.rpow_le_rpow_iff (norm_nonneg G) (mul_nonneg (by linarith) (norm_nonneg F))
    (by linarith)).1 hpow

/-! ### `L²` orthogonality and isometry -/

/-- Orthogonality identity for finite real Haar sums. -/
private theorem integral_haarSum_mul_haarSum (a b : ℕ → ℝ) (N : ℕ) :
    ∫ x, haarSum a N x * haarSum b N x =
      ∑ n ∈ Finset.range N, a n * b n * ∫ x, haarFun n x ^ 2 := by
  have hint (n m : ℕ) : Integrable fun x => (a n * haarFun n x) * (b m * haarFun m x) := by
    refine Integrable.of_bound
      ((measurable_const.mul (measurable_haarFun n)).mul
        (measurable_const.mul (measurable_haarFun m))).aestronglyMeasurable
      (|a n| * |b m|) (ae_of_all _ fun x => ?_)
    rw [norm_mul, norm_mul, norm_mul]
    exact mul_le_mul (mul_le_of_le_one_right (norm_nonneg _) (norm_haarFun_le n x))
      (mul_le_of_le_one_right (norm_nonneg _) (norm_haarFun_le m x))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _)
  have hexp : (fun x => haarSum a N x * haarSum b N x) =
      fun x => ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
        (a n * haarFun n x) * (b m * haarFun m x) := by
    funext x
    rw [haarSum, haarSum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => Finset.mul_sum ..
  rw [hexp, integral_finsetSum _ fun n _ => integrable_finsetSum _ fun m _ => hint n m]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_finsetSum _ fun m _ => hint n m, Finset.sum_eq_single n]
  · have hmul : (fun x => (a n * haarFun n x) * (b n * haarFun n x)) =
        fun x => (a n * b n) * haarFun n x ^ 2 := funext fun x => by ring
    rw [hmul, integral_const_mul]
  · intro m _ hmn
    have hmul : (fun x => (a n * haarFun n x) * (b m * haarFun m x)) =
        fun x => (a n * b m) * (haarFun n x * haarFun m x) := funext fun x => by ring
    rw [hmul, integral_const_mul, integral_haarFun_mul_haarFun hmn.symm, mul_zero]
  · intro h; exact absurd hn h

private theorem sum_eq_sum_range_ite {α : Type*} [AddCommMonoid α] (s : Finset ℕ) (f : ℕ → α) :
    ∑ n ∈ s, f n = ∑ n ∈ Finset.range (s.sup id + 1), if n ∈ s then f n else 0 := by
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2]
  exact fun n hn => Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))

private theorem norm_sum_range_smul_haarBasis_two_sq {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, a n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n‖ ^ 2 =
      ∑ n ∈ Finset.range N, ‖a n‖ ^ 2 * ((2 ^ Nat.log 2 n : ℕ) : ℝ)⁻¹ := by
  have hre (x : I) :
      RCLike.re (∑ n ∈ Finset.range N, a n * (haarFun n x : 𝕜)) =
        haarSum (fun n => RCLike.re (a n)) N x := by
    simp [haarSum, map_sum]
  have him (x : I) :
      RCLike.im (∑ n ∈ Finset.range N, a n * (haarFun n x : 𝕜)) =
        haarSum (fun n => RCLike.im (a n)) N x := by
    simp [haarSum, map_sum]
  have hint (c : ℕ → ℝ) : Integrable fun x => haarSum c N x ^ 2 := by
    simpa [Real.rpow_two] using integrable_abs_haarSum_rpow (p := 2) zero_le_two c N
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  have hcongr : ∫ x, ‖(∑ n ∈ Finset.range N, a n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n :
        Lp 𝕜 2 (volume : Measure I)) x‖ ^ 2 =
      ∫ x, (haarSum (fun n => RCLike.re (a n)) N x ^ 2 +
        haarSum (fun n => RCLike.im (a n)) N x ^ 2) := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sum_smul_haarBasis (p := 2) ENNReal.ofNat_ne_top a N] with x hx
    rw [hx, RCLike.norm_sq_eq_def, hre, him, sq, sq]
  rw [hcongr, integral_add (hint _) (hint _)]
  simp only [sq, integral_haarSum_mul_haarSum, ← Finset.sum_add_distrib, ← add_mul,
    ← RCLike.norm_sq_eq_def]
  simp only [← sq, integral_haarFun_sq]

/-- **Parseval identity for finite Haar expansions in `L²([0, 1])`** over real or complex
scalars. -/
theorem norm_sum_smul_haarBasis_two_sq {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) (s : Finset ℕ) :
    ‖∑ n ∈ s, a n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n‖ ^ 2 =
      ∑ n ∈ s, ‖a n‖ ^ 2 * ((2 ^ Nat.log 2 n : ℕ) : ℝ)⁻¹ := by
  let a' : ℕ → 𝕜 := fun n => if n ∈ s then a n else 0
  have hL : ∑ n ∈ s, a n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n =
      ∑ n ∈ Finset.range (s.sup id + 1), a' n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n := by
    rw [sum_eq_sum_range_ite]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [a']; split_ifs <;> simp
  have hR : ∑ n ∈ s, ‖a n‖ ^ 2 * ((2 ^ Nat.log 2 n : ℕ) : ℝ)⁻¹ =
      ∑ n ∈ Finset.range (s.sup id + 1), ‖a' n‖ ^ 2 * ((2 ^ Nat.log 2 n : ℕ) : ℝ)⁻¹ := by
    rw [sum_eq_sum_range_ite]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [a']; split_ifs <;> simp
  rw [hL, hR, norm_sum_range_smul_haarBasis_two_sq]

/-- In `L²([0, 1])`, multiplying finite Haar expansions by unit-modulus scalars is an isometry. -/
theorem norm_sum_mul_smul_haarBasis_two {𝕜 : Type*} [RCLike 𝕜] {a ε : ℕ → 𝕜} {s : Finset ℕ}
    (hε : ∀ n ∈ s, ‖ε n‖ = 1) :
    ‖∑ n ∈ s, (ε n * a n) • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n‖ =
      ‖∑ n ∈ s, a n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n‖ := by
  have hsq : ‖∑ n ∈ s, (ε n * a n) • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n‖ ^ 2 =
      ‖∑ n ∈ s, a n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n‖ ^ 2 := by
    rw [norm_sum_smul_haarBasis_two_sq, norm_sum_smul_haarBasis_two_sq]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [norm_mul, hε n hn, one_mul]
  nlinarith [norm_nonneg (∑ n ∈ s, (ε n * a n) • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n),
    norm_nonneg (∑ n ∈ s, a n • haarBasis 𝕜 2 ENNReal.ofNat_ne_top n)]

/-! ### Duality for `1 < p < 2` and real/complex sign-transform bounds -/

/-- Pairing a real finite Haar sign transform `G_N ∈ Lᵖ` against `g ∈ L^q` equals pairing the
original Haar sum `F_N ∈ Lᵖ` against the sign transform of `dyadicProj ℝ q N g`. -/
private theorem toDual_haarSum_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp : p ≠ ∞) (hq : q ≠ ∞) (a ε : ℕ → ℝ) (N : ℕ)
    (g : Lp ℝ q (volume : Measure I)) :
    Lp.toDual ℝ (volume : Measure I) p q
        (∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p hp n) g =
      Lp.toDual ℝ (volume : Measure I) p q
        (∑ n ∈ Finset.range N, a n • haarBasis ℝ p hp n)
        (∑ n ∈ Finset.range N,
          (ε n * (haarBasis ℝ q hq).coord n g) • haarBasis ℝ q hq n) := by
  set b : ℕ → ℝ := fun n => (haarBasis ℝ q hq).coord n g
  have hint (n : ℕ) : Integrable fun x => (ε n * a n) * (haarFun n x * g x) :=
    (((Lp.memLp g).integrable Fact.out).norm.mono'
      ((measurable_haarFun n).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
      (ae_of_all _ fun x => by
        rw [Pi.mul_apply, norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_haarFun_le n x))).const_mul _
  rw [Lp.toDual_apply, Lp.toDual_apply]
  have hL : ∫ x, (∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p hp n :
        Lp ℝ p (volume : Measure I)) x * g x =
      ∑ n ∈ Finset.range N, a n * (ε n * b n) * ∫ x, haarFun n x ^ 2 := by
    have hc : ∫ x, (∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p hp n :
          Lp ℝ p (volume : Measure I)) x * g x =
        ∫ x, ∑ n ∈ Finset.range N, (ε n * a n) * (haarFun n x * g x) := by
      refine integral_congr_ae ?_
      filter_upwards [coeFn_sum_smul_haarBasis_real hp (fun n => ε n * a n) N] with x hx
      rw [hx, haarSum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hc, integral_finsetSum _ fun n _ => hint n]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_haarFun_sq]
    have hcoord := haarBasis_coord hq n g
    simp only [RCLike.ofReal_real_eq_id, id_eq] at hcoord
    have hpos : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.two_pow_pos _).ne'
    dsimp [b]
    rw [hcoord]
    field_simp
  have hR : ∫ x, (∑ n ∈ Finset.range N, a n • haarBasis ℝ p hp n :
        Lp ℝ p (volume : Measure I)) x *
        (∑ n ∈ Finset.range N, (ε n * b n) • haarBasis ℝ q hq n :
          Lp ℝ q (volume : Measure I)) x =
      ∑ n ∈ Finset.range N, a n * (ε n * b n) * ∫ x, haarFun n x ^ 2 := by
    rw [← integral_haarSum_mul_haarSum]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_sum_smul_haarBasis_real hp a N,
      coeFn_sum_smul_haarBasis_real hq (fun n => ε n * b n) N] with x h1 h2
    rw [h1, h2]
  exact hL.trans hR.symm

/-- Real Haar sign-transform bound for `1 < p < 2` by Hölder duality with `q = p / (p - 1) > 2`. -/
private theorem norm_sum_mul_smul_haarBasis_real_le_of_lt_two {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp2 : p < 2) {a ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p (hp2.trans ENNReal.ofNat_lt_top).ne n‖ ≤
      (p.toReal / (p.toReal - 1) - 1) *
        ‖∑ n ∈ Finset.range N, a n • haarBasis ℝ p (hp2.trans ENNReal.ofNat_lt_top).ne n‖ := by
  have hp : p ≠ ∞ := (hp2.trans ENNReal.ofNat_lt_top).ne
  set q := p.conjExponent
  have hq1 : 1 ≤ q := ENNReal.HolderConjugate.one_le q p
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have hq : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).2 hp1).ne
  have hpr1 : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  have hpr2 : p.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hp ENNReal.ofNat_ne_top).2 hp2
  have hq_toReal : q.toReal = p.toReal / (p.toReal - 1) :=
    (ENNReal.HolderConjugate.toReal (q := q) hpr1).conjExponent_eq.symm
  have hq2_real : 2 ≤ q.toReal := by
    rw [hq_toReal, le_div_iff₀ (by linarith)]
    linarith
  have hq2 : 2 ≤ q :=
    (ENNReal.toReal_le_toReal ENNReal.ofNat_ne_top hq).1 (by simpa using hq2_real)
  set F : Lp ℝ p (volume : Measure I) := ∑ n ∈ Finset.range N, a n • haarBasis ℝ p hp n
  set G : Lp ℝ p (volume : Measure I) := ∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p hp n
  rw [← (Lp.toDual ℝ (volume : Measure I) p q).norm_map G, ← hq_toReal]
  refine (Lp.toDual ℝ (volume : Measure I) p q G).opNorm_le_bound
    (mul_nonneg (by linarith) (norm_nonneg F)) fun g => ?_
  set H : Lp ℝ q (volume : Measure I) :=
    ∑ n ∈ Finset.range N, (ε n * (haarBasis ℝ q hq).coord n g) • haarBasis ℝ q hq n
  have hH : ‖H‖ ≤ (q.toReal - 1) * ‖g‖ := by
    calc ‖H‖ ≤ (q.toReal - 1) *
          ‖∑ n ∈ Finset.range N, (haarBasis ℝ q hq).coord n g • haarBasis ℝ q hq n‖ :=
            norm_sum_mul_smul_haarBasis_real_le_of_two_le hq2 hq hε N
      _ = (q.toReal - 1) * ‖dyadicProj ℝ q N g‖ := by
            rw [← (haarBasis ℝ q hq).proj_apply, haarBasis_proj]
      _ ≤ (q.toReal - 1) * (1 * ‖g‖) := by
            gcongr
            · linarith
            · exact (dyadicProj ℝ q N).le_of_opNorm_le (norm_dyadicProj_le ℝ q N) g
      _ = (q.toReal - 1) * ‖g‖ := by rw [one_mul]
  calc ‖Lp.toDual ℝ (volume : Measure I) p q G g‖
      = ‖Lp.toDual ℝ (volume : Measure I) p q F H‖ := by rw [toDual_haarSum_eq hp hq a ε N g]
    _ ≤ ‖Lp.toDual ℝ (volume : Measure I) p q F‖ * ‖H‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖F‖ * ‖H‖ := by rw [(Lp.toDual ℝ (volume : Measure I) p q).norm_map]
    _ ≤ ‖F‖ * ((q.toReal - 1) * ‖g‖) := by gcongr
    _ = (q.toReal - 1) * ‖F‖ * ‖g‖ := by ring

private theorem norm_sum_range_mul_smul_haarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) {a ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, (ε n * a n) • haarBasis ℝ p hp n‖ ≤
      (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
        ‖∑ n ∈ Finset.range N, a n • haarBasis ℝ p hp n‖ := by
  have hpr1 : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  rcases le_or_gt 2 p with hp2 | hp2
  · have hpr2 : 2 ≤ p.toReal := by
      simpa using (ENNReal.toReal_le_toReal ENNReal.ofNat_ne_top hp).2 hp2
    have hmax : max p.toReal (p.toReal / (p.toReal - 1)) = p.toReal :=
      max_eq_left ((div_le_iff₀ (by linarith)).2 (by nlinarith))
    rw [hmax]
    exact norm_sum_mul_smul_haarBasis_real_le_of_two_le hp2 hp hε N
  · have hpr2 : p.toReal < 2 := by
      simpa using (ENNReal.toReal_lt_toReal hp ENNReal.ofNat_ne_top).2 hp2
    have hmax : max p.toReal (p.toReal / (p.toReal - 1)) = p.toReal / (p.toReal - 1) :=
      max_eq_right ((le_div_iff₀ (by linarith)).2 (by nlinarith))
    rw [hmax]
    exact norm_sum_mul_smul_haarBasis_real_le_of_lt_two hp1 hp2 hε N

/-- **Burkholder's inequality for real Haar sign transforms.** For `1 < p < ∞` and signs
`ε n ∈ {-1, 1}`, changing signs in a finite real Haar expansion multiplies its `Lᵖ([0, 1])` norm
by at most `max(p, p / (p - 1)) - 1`. -/
theorem norm_sum_mul_smul_haarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    {a ε : ℕ → ℝ} {s : Finset ℕ} (hε : ∀ n ∈ s, |ε n| = 1) :
    ‖∑ n ∈ s, (ε n * a n) • haarBasis ℝ p hp n‖ ≤
      (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
        ‖∑ n ∈ s, a n • haarBasis ℝ p hp n‖ := by
  let a' : ℕ → ℝ := fun n => if n ∈ s then a n else 0
  let ε' : ℕ → ℝ := fun n => if n ∈ s then ε n else 1
  have hε' : ∀ n, |ε' n| = 1 := fun n => by
    dsimp [ε']; split_ifs with h
    · exact hε n h
    · exact abs_one
  have h1 : ∑ n ∈ s, (ε n * a n) • haarBasis ℝ p hp n =
      ∑ n ∈ Finset.range (s.sup id + 1), (ε' n * a' n) • haarBasis ℝ p hp n := by
    rw [sum_eq_sum_range_ite]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [a', ε']; split_ifs <;> simp
  have h2 : ∑ n ∈ s, a n • haarBasis ℝ p hp n =
      ∑ n ∈ Finset.range (s.sup id + 1), a' n • haarBasis ℝ p hp n := by
    rw [sum_eq_sum_range_ite]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [a']; split_ifs <;> simp
  rw [h1, h2]
  exact norm_sum_range_mul_smul_haarBasis_real_le hp1 hp hε' _

/-- Applying a contractive `ℝ`-linear map (such as `RCLike.reLm` or `RCLike.imLm`) to the
coefficients of a finite Haar expansion cannot increase its `Lᵖ` norm. -/
private theorem norm_sum_linearMap_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (f : 𝕜 →ₗ[ℝ] ℝ) (hf : ∀ z, |f z| ≤ ‖z‖) (a : ℕ → 𝕜) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, f (a n) • haarBasis ℝ p hp n‖ ≤
      ‖∑ n ∈ Finset.range N, a n • haarBasis 𝕜 p hp n‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [coeFn_sum_smul_haarBasis_real hp (fun n => f (a n)) N,
    coeFn_sum_smul_haarBasis hp a N] with x h1 h2
  rw [h1, h2, Real.norm_eq_abs]
  have hsum : haarSum (fun n => f (a n)) N x =
      f (∑ n ∈ Finset.range N, a n * (haarFun n x : 𝕜)) := by
    rw [haarSum, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_comm (a n), ← RCLike.real_smul_eq_coe_mul, map_smul, smul_eq_mul, mul_comm]
  rw [hsum]
  exact hf _

private theorem norm_sum_range_mul_smul_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞) {a : ℕ → 𝕜} {ε : ℕ → ℝ} (hε : ∀ n, |ε n| = 1)
    (N : ℕ) :
    ‖∑ n ∈ Finset.range N, ((ε n : 𝕜) * a n) • haarBasis 𝕜 p hp n‖ ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
        ‖∑ n ∈ Finset.range N, a n • haarBasis 𝕜 p hp n‖ := by
  have hpr1 : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp).2 hp1
  have hC0 : 0 ≤ max p.toReal (p.toReal / (p.toReal - 1)) - 1 := by
    linarith [le_max_left p.toReal (p.toReal / (p.toReal - 1))]
  have hFre : ‖∑ n ∈ Finset.range N, RCLike.re (a n) • haarBasis ℝ p hp n‖ ≤
      ‖∑ n ∈ Finset.range N, a n • haarBasis 𝕜 p hp n‖ :=
    norm_sum_linearMap_haarBasis_le (𝕜 := 𝕜) hp RCLike.reLm RCLike.abs_re_le_norm a N
  have hFim : ‖∑ n ∈ Finset.range N, RCLike.im (a n) • haarBasis ℝ p hp n‖ ≤
      ‖∑ n ∈ Finset.range N, a n • haarBasis 𝕜 p hp n‖ :=
    norm_sum_linearMap_haarBasis_le (𝕜 := 𝕜) hp RCLike.imLm RCLike.abs_im_le_norm a N
  have hGre := norm_sum_range_mul_smul_haarBasis_real_le hp1 hp hε N (a := fun n => RCLike.re (a n))
  have hGim := norm_sum_range_mul_smul_haarBasis_real_le hp1 hp hε N (a := fun n => RCLike.im (a n))
  have hG : ‖∑ n ∈ Finset.range N, ((ε n : 𝕜) * a n) • haarBasis 𝕜 p hp n‖ ≤
      1 * ‖∑ n ∈ Finset.range N, (ε n * RCLike.re (a n)) • haarBasis ℝ p hp n‖ +
        1 * ‖∑ n ∈ Finset.range N, (ε n * RCLike.im (a n)) • haarBasis ℝ p hp n‖ := by
    refine Lp.norm_le_add_of_ae_norm_le zero_le_one zero_le_one ?_
    filter_upwards [coeFn_sum_smul_haarBasis (𝕜 := 𝕜) hp (fun n => (ε n : 𝕜) * a n) N,
      coeFn_sum_smul_haarBasis_real hp (fun n => ε n * RCLike.re (a n)) N,
      coeFn_sum_smul_haarBasis_real hp (fun n => ε n * RCLike.im (a n)) N] with x hG' h1 h2
    rw [hG', h1, h2, one_mul, one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hre : RCLike.re (∑ n ∈ Finset.range N, (ε n : 𝕜) * a n * (haarFun n x : 𝕜)) =
        haarSum (fun n => ε n * RCLike.re (a n)) N x := by
      simp only [haarSum, map_sum, RCLike.re_mul_ofReal, RCLike.re_ofReal_mul]
    have him : RCLike.im (∑ n ∈ Finset.range N, (ε n : 𝕜) * a n * (haarFun n x : 𝕜)) =
        haarSum (fun n => ε n * RCLike.im (a n)) N x := by
      simp only [haarSum, map_sum, RCLike.im_mul_ofReal, RCLike.im_ofReal_mul]
    rw [← hre, ← him]
    set z := ∑ n ∈ Finset.range N, (ε n : 𝕜) * a n * (haarFun n x : 𝕜)
    nlinarith [RCLike.norm_sq_eq_def (z := z), sq_abs (RCLike.re z), sq_abs (RCLike.im z),
      abs_nonneg (RCLike.re z), abs_nonneg (RCLike.im z), norm_nonneg z]
  linarith [mul_le_mul_of_nonneg_left hFre hC0, mul_le_mul_of_nonneg_left hFim hC0]

/-- **Haar sign-transform bound over `ℝ` and `ℂ`.** For `1 < p < ∞` and signs `ε n ∈ {-1, 1}`,
changing signs in a finite `𝕜`-valued Haar expansion multiplies its `Lᵖ([0, 1]; 𝕜)` norm by at most
`2 * (max(p, p / (p - 1)) - 1)`. -/
theorem norm_sum_mul_smul_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp1 : 1 < p) (hp : p ≠ ∞) {a : ℕ → 𝕜} {ε : ℕ → ℝ} {s : Finset ℕ} (hε : ∀ n ∈ s, |ε n| = 1) :
    ‖∑ n ∈ s, ((ε n : 𝕜) * a n) • haarBasis 𝕜 p hp n‖ ≤
      2 * (max p.toReal (p.toReal / (p.toReal - 1)) - 1) *
        ‖∑ n ∈ s, a n • haarBasis 𝕜 p hp n‖ := by
  let a' : ℕ → 𝕜 := fun n => if n ∈ s then a n else 0
  let ε' : ℕ → ℝ := fun n => if n ∈ s then ε n else 1
  have hε' : ∀ n, |ε' n| = 1 := fun n => by
    dsimp [ε']; split_ifs with h
    · exact hε n h
    · exact abs_one
  have h1 : ∑ n ∈ s, ((ε n : 𝕜) * a n) • haarBasis 𝕜 p hp n =
      ∑ n ∈ Finset.range (s.sup id + 1), ((ε' n : 𝕜) * a' n) • haarBasis 𝕜 p hp n := by
    rw [sum_eq_sum_range_ite]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [a', ε']; split_ifs <;> simp
  have h2 : ∑ n ∈ s, a n • haarBasis 𝕜 p hp n =
      ∑ n ∈ Finset.range (s.sup id + 1), a' n • haarBasis 𝕜 p hp n := by
    rw [sum_eq_sum_range_ite]
    refine Finset.sum_congr rfl fun n _ => ?_
    dsimp [a']; split_ifs <;> simp
  rw [h1, h2]
  exact norm_sum_range_mul_smul_haarBasis_le hp1 hp hε' _

/-! ### Finite projection bounds and the unconditional Haar basis -/

/-- Every finite coordinate projection of the real Haar basis on `Lᵖ([0, 1])`, `1 < p < ∞`, has
norm at most `max(p, p / (p - 1)) / 2`. -/
theorem norm_proj_haarBasis_real_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis ℝ p hp) A‖ ≤
      max p.toReal (p.toReal / (p.toReal - 1)) / 2 := by
  have h := (haarBasis ℝ p hp).norm_proj_le_of_sign_bound (M := 1)
    (fun N ε hε f => by
      have hε' : ∀ n ∈ Finset.range N, |ε n| = 1 := fun n _ => (abs_eq zero_le_one).2 (hε n)
      simpa only [RCLike.ofReal_real_eq_id, id_eq, smul_smul, SchauderBasis.proj_apply] using
        norm_sum_mul_smul_haarBasis_real_le hp1 hp hε'
          (a := fun n => (haarBasis ℝ p hp).coord n f))
    (fun N => by rw [haarBasis_proj]; exact norm_dyadicProj_le ℝ p N) A
  linarith

/-- Every finite coordinate projection of the Haar basis on `Lᵖ([0, 1]; 𝕜)`, `1 < p < ∞`, has norm
at most `max(p, p / (p - 1)) - 1 / 2`. -/
theorem norm_proj_haarBasis_le {𝕜 : Type*} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ∞) (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis 𝕜 p hp) A‖ ≤
      max p.toReal (p.toReal / (p.toReal - 1)) - 1 / 2 := by
  have h := (haarBasis 𝕜 p hp).norm_proj_le_of_sign_bound (M := 1)
    (fun N ε hε f => by
      have hε' : ∀ n ∈ Finset.range N, |ε n| = 1 := fun n _ => (abs_eq zero_le_one).2 (hε n)
      simpa only [smul_smul, SchauderBasis.proj_apply] using
        norm_sum_mul_smul_haarBasis_le (𝕜 := 𝕜) hp1 hp hε'
          (a := fun n => (haarBasis 𝕜 p hp).coord n f))
    (fun N => by rw [haarBasis_proj]; exact norm_dyadicProj_le 𝕜 p N) A
  linarith

/-- In `L²([0, 1]; 𝕜)`, every finite Haar coordinate projection is a contraction. -/
theorem norm_proj_haarBasis_two_le {𝕜 : Type*} [RCLike 𝕜] (A : Finset ℕ) :
    ‖GeneralSchauderBasis.proj (haarBasis 𝕜 2 ENNReal.ofNat_ne_top) A‖ ≤ 1 := by
  have h := (haarBasis 𝕜 2 ENNReal.ofNat_ne_top).norm_proj_le_of_sign_bound (K := 1) (M := 1)
    (fun N ε hε f => by
      have hε' : ∀ n ∈ Finset.range N, ‖(ε n : 𝕜)‖ = 1 := fun n _ => by
        rw [RCLike.norm_ofReal, (abs_eq zero_le_one).2 (hε n)]
      simpa only [smul_smul, one_mul, SchauderBasis.proj_apply] using
        (norm_sum_mul_smul_haarBasis_two (𝕜 := 𝕜) hε'
          (a := fun n => (haarBasis 𝕜 2 ENNReal.ofNat_ne_top).coord n f)).le)
    (fun N => by rw [haarBasis_proj]; exact norm_dyadicProj_le 𝕜 2 N) A
  linarith

variable (𝕜 : Type*) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- **The unconditional Haar basis of `Lᵖ([0, 1])`**, `1 < p < ∞`, over real or complex scalars:
the classical Haar Schauder basis `haarBasis 𝕜 p hp` upgraded via its uniform finite-projection
bound (`norm_proj_haarBasis_le`). -/
def unconditionalHaarBasis (hp1 : 1 < p) (hp : p ≠ ∞) :
    UnconditionalSchauderBasis ℕ 𝕜 (Lp 𝕜 p (volume : Measure I)) :=
  (haarBasis 𝕜 p hp).toUnconditionalSchauderBasis
    ((haarBasis 𝕜 p hp).hasSum_expansion_of_forall_norm_proj_le (norm_proj_haarBasis_le hp1 hp))

variable {𝕜 p}

/-- The basis vectors of `unconditionalHaarBasis` are those of `haarBasis`. -/
@[simp]
theorem coe_unconditionalHaarBasis (hp1 : 1 < p) (hp : p ≠ ∞) :
    ⇑(unconditionalHaarBasis 𝕜 p hp1 hp) = ⇑(haarBasis 𝕜 p hp) :=
  SchauderBasis.coe_toUnconditionalSchauderBasis _ _

/-- The `n`-th vector of the unconditional Haar basis is a.e. the Haar function `hₙ`. -/
theorem coeFn_unconditionalHaarBasis (hp1 : 1 < p) (hp : p ≠ ∞) (n : ℕ) :
    unconditionalHaarBasis 𝕜 p hp1 hp n =ᵐ[volume] fun x => (haarFun n x : 𝕜) := by
  rw [coe_unconditionalHaarBasis]
  exact coeFn_haarBasis hp n

/-- The coordinate functionals of `unconditionalHaarBasis` are those of `haarBasis`. -/
@[simp]
theorem unconditionalHaarBasis_coord (hp1 : 1 < p) (hp : p ≠ ∞) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).coord = (haarBasis 𝕜 p hp).coord :=
  SchauderBasis.toUnconditionalSchauderBasis_coord _ _

/-- The finite projections of `unconditionalHaarBasis` are those of `haarBasis`. -/
@[simp]
theorem unconditionalHaarBasis_proj (hp1 : 1 < p) (hp : p ≠ ∞) (A : Finset ℕ) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).proj A = GeneralSchauderBasis.proj (haarBasis 𝕜 p hp) A :=
  SchauderBasis.toUnconditionalSchauderBasis_proj _ _ A

/-- Forgetting unconditionality recovers the classical Haar Schauder basis. -/
@[simp]
theorem unconditionalHaarBasis_toSchauderBasis (hp1 : 1 < p) (hp : p ≠ ∞) :
    (unconditionalHaarBasis 𝕜 p hp1 hp).toSchauderBasis = haarBasis 𝕜 p hp :=
  (haarBasis 𝕜 p hp).toUnconditionalSchauderBasis_toSchauderBasis _

/-- The unconditional basis constant of the real Haar basis of `Lᵖ([0, 1])`, `1 < p < ∞`, is at
most `max(p, p / (p - 1)) / 2`. -/
theorem nnNormProjBound_unconditionalHaarBasis_real_le (hp1 : 1 < p) (hp : p ≠ ∞) :
    ((unconditionalHaarBasis ℝ p hp1 hp).nnNormProjBound : ℝ) ≤
      max p.toReal (p.toReal / (p.toReal - 1)) / 2 :=
  (unconditionalHaarBasis ℝ p hp1 hp).coe_nnNormProjBound_le fun A => by
    rw [unconditionalHaarBasis_proj]
    exact norm_proj_haarBasis_real_le hp1 hp A

/-- The unconditional basis constant of the Haar basis of `Lᵖ([0, 1]; 𝕜)`, `1 < p < ∞`, is at most
`max(p, p / (p - 1)) - 1 / 2`. -/
theorem nnNormProjBound_unconditionalHaarBasis_le (hp1 : 1 < p) (hp : p ≠ ∞) :
    ((unconditionalHaarBasis 𝕜 p hp1 hp).nnNormProjBound : ℝ) ≤
      max p.toReal (p.toReal / (p.toReal - 1)) - 1 / 2 :=
  (unconditionalHaarBasis 𝕜 p hp1 hp).coe_nnNormProjBound_le fun A => by
    rw [unconditionalHaarBasis_proj]
    exact norm_proj_haarBasis_le hp1 hp A

/-- The unconditional basis constant of the Haar basis of `L²([0, 1]; 𝕜)` is at most `1`. -/
theorem nnNormProjBound_unconditionalHaarBasis_two_le :
    ((unconditionalHaarBasis 𝕜 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).nnNormProjBound : ℝ) ≤
      1 :=
  (unconditionalHaarBasis 𝕜 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top).coe_nnNormProjBound_le
    fun A => by
      rw [unconditionalHaarBasis_proj]
      exact norm_proj_haarBasis_two_le (𝕜 := 𝕜) A

end TauCeti.unitInterval
