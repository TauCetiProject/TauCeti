/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianTheta
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.PSeries.Square
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Exp.InvSubOne
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.PolyaVinogradov

/-!
# Mean squares of Jacobi twists of Gaussian theta series

Average over the numerator of the Jacobi symbol, with the odd part of the coefficient index
as denominator. Pairs whose product has square odd part are bounded by a convergent power sum.
For the other pairs the Pólya–Vinogradov bound is absorbed into a product of geometric sums.
This yields a uniform second moment for integrating tails of theta series of quadratic twists.

The estimate corresponds to `New.sum_sq_thetaSeries_jacobiSym_le` in
`Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open Finset Real
open scoped Nat ComplexConjugate

namespace TauCeti

private theorem exists_gaussianMonomial_weighted_le (j : Fin 2) {a : ℝ}
    (ha : 0 ≤ a + j.val) :
    ∃ C, ∀ x > 0, ‖gaussianMonomial j x‖ ≤ C * x ^ (-a) * exp (-x) := by
  obtain ⟨M, hM, h⟩ := exists_rpow_mul_exp_neg_mul_le
    (σ := (a + j.val) / 2) (c := π / 2) (div_nonneg ha (by norm_num)) (by positivity)
  refine ⟨M * exp 1, fun x hx ↦ ?_⟩
  have hpow := h (x ^ 2) (sq_nonneg x)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le] at hpow
  norm_num only [Nat.cast_ofNat] at hpow
  rw [show 2 * ((a + (j.val : ℝ)) / 2) = a + j.val by ring, Real.rpow_two] at hpow
  have hdecay : exp (-(π / 2 * x ^ 2)) ≤ exp 1 * exp (-x) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    calc
      -(π / 2 * x ^ 2) ≤ -(1 * x ^ 2) := by gcongr; linarith [Real.pi_gt_three]
      _ ≤ 1 + -x := by nlinarith [sq_nonneg (x - 1)]
  calc
    ‖gaussianMonomial j x‖ =
        (x ^ (a + j.val) * exp (-(π / 2 * x ^ (2 : ℕ)))) *
          (x ^ (-a) * exp (-(π / 2 * x ^ (2 : ℕ)))) := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hx, ← Real.exp_add,
        show a + (j.val : ℝ) + -a = j.val by ring, Real.rpow_natCast]
      refine (show ‖gaussianMonomial j x‖ = x ^ j.val * exp (-π * x ^ (2 : ℕ)) by
        fin_cases j <;> simp [norm_mul, abs_of_pos hx]).trans ?_
      congr 2
      ring
    _ ≤ M * (x ^ (-a) * (exp 1 * exp (-x))) :=
      mul_le_mul hpow (mul_le_mul_of_nonneg_left hdecay (by positivity)) (by positivity) hM
    _ = _ := by ring

private def oddPartJacobi (v n : ℕ) : ℂ := jacobiSym (-(v : ℤ)) (ordCompl[2] n)

private theorem norm_oddPartJacobi_le_one (v n : ℕ) : ‖oddPartJacobi v n‖ ≤ 1 := by
  have h := Int.abs_le_one_iff.mpr (jacobiSym.trichotomy (-(v : ℤ)) (ordCompl[2] n))
  unfold oddPartJacobi
  exact_mod_cast h

private def jacobiCorrelation (X n : ℕ) : ℂ := ∑ v ∈ Icc 1 X, oddPartJacobi v n

private theorem norm_jacobiCorrelation_le (X n : ℕ) : ‖jacobiCorrelation X n‖ ≤ X := by
  calc
    _ ≤ ∑ v ∈ Icc 1 X, ‖oddPartJacobi v n‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ Icc 1 X, (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦ norm_oddPartJacobi_le_one _ _
    _ = _ := by simp

private theorem sum_norm_gaussianTheta_jacobiSym_sq_le (j : Fin 2) (X : ℕ) {c : ℕ → ℂ}
    (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) {B : ℕ+ × ℕ+ → ℝ}
    (hB : Summable B) (hbound : ∀ q : ℕ+ × ℕ+,
      ‖gaussianMonomial j (q.1 * u)‖ * ‖gaussianMonomial j (q.2 * u)‖ *
        ‖jacobiCorrelation X ((q.1 : ℕ) * q.2)‖ ≤ B q) :
    (∑ v ∈ Icc 1 X, ‖gaussianTheta j (fun n ↦ c n * oddPartJacobi v n) u‖ ^ 2) ≤ ∑' q, B q := by
  let w (n : ℕ+) : ℂ := c n * gaussianMonomial j (n * u)
  let f (v : ℕ) (n : ℕ+) : ℂ := w n * oddPartJacobi v n
  have hw : Summable (fun n ↦ ‖w n‖) := (summable_gaussianTheta (j := j) hc hu).norm
  have hf (v : ℕ) : Summable fun n ↦ ‖f v n‖ := by
    refine hw.of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun n ↦ ?_
    simp only [f, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_oddPartJacobi_le_one _ _)
  let g (q : ℕ+ × ℕ+) : ℂ := ∑ v ∈ Icc 1 X, f v q.1 * conj (f v q.2)
  have hconj (v : ℕ) : Summable (fun n : ℕ+ ↦ ‖conj (f v n)‖) := by
    simpa only [Complex.norm_conj] using hf v
  have hp (v : ℕ) : Summable (fun q : ℕ+ × ℕ+ ↦ ‖f v q.1 * conj (f v q.2)‖) :=
    (hf v).mul_norm (hconj v)
  have hs : Summable (fun q : ℕ+ × ℕ+ ↦ ∑ v ∈ Icc 1 X, ‖f v q.1 * conj (f v q.2)‖) :=
    summable_sum (s := Icc 1 X) fun v _ ↦ hp v
  have hg : Summable fun q ↦ ‖g q‖ := hs.of_nonneg_of_le
    (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_sum_le _ _)
  have hsq (v : ℕ) : ((‖gaussianTheta j (fun n ↦ c n * oddPartJacobi v n) u‖ ^ 2 : ℝ) : ℂ) =
      ∑' q : ℕ+ × ℕ+, f v q.1 * conj (f v q.2) := by
    have hθ : gaussianTheta j (fun n ↦ c n * oddPartJacobi v n) u = ∑' n, f v n := by
      simp only [gaussianTheta_def, f, w, mul_right_comm (c _)]
    have hstar : conj (∑' n, f v n) = ∑' n, conj (f v n) := tsum_star
    rw [hθ, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, hstar]
    exact tsum_mul_tsum_of_summable_norm (hf v) (hconj v)
  have hle (q : ℕ+ × ℕ+) : ‖g q‖ ≤ B q := by
    have hfactor (v : ℕ) : f v q.1 * conj (f v q.2) = (w q.1 * conj (w q.2)) *
        oddPartJacobi v ((q.1 : ℕ) * q.2) := by
      have hn (n : ℕ+) : ordCompl[2] (n : ℕ) ≠ 0 := (Nat.ordCompl_pos 2 n.pos.ne').ne'
      simp only [f, oddPartJacobi, map_mul, map_intCast, Nat.ordCompl_mul,
        jacobiSym.mul_right' _ (hn q.1) (hn q.2), Int.cast_mul]
      ring
    have hwle (n : ℕ+) : ‖w n‖ ≤ ‖gaussianMonomial j (n * u)‖ := by
      simp only [w, norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc n)
    refine le_trans ?_ (hbound q)
    simp only [g, hfactor, ← mul_sum, jacobiCorrelation, norm_mul, Complex.norm_conj]
    gcongr <;> exact hwle _
  calc
    _ = ‖∑' q, g q‖ := by
      simp only [g, Summable.tsum_finsetSum (fun v _ ↦ (hp v).of_norm), ← hsq,
        ← Complex.ofReal_sum, Complex.norm_real]
      exact (norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)).symm
    _ ≤ _ := (norm_tsum_le_tsum_norm hg).trans (hg.tsum_le_tsum hle hB)

open scoped Classical in
private theorem gaussianPair_mul_norm_jacobiCorrelation_le {j : Fin 2} {δ C u : ℝ}
    (hδ : 0 < δ) (hu : 0 < u)
    (hw : ∀ x > 0, ‖gaussianMonomial j x‖ ≤ C * x ^ (-(1 / 2 + δ)) * exp (-x))
    (X : ℕ) (q : ℕ+ × ℕ+) :
    ‖gaussianMonomial j (q.1 * u)‖ * ‖gaussianMonomial j (q.2 * u)‖ *
        ‖jacobiCorrelation X ((q.1 : ℕ) * q.2)‖ ≤
      (C * u ^ (-(1 / 2 + δ))) ^ 2 *
        ((X : ℝ) * (if IsSquare (ordCompl[2] ((q.1 : ℕ) * q.2)) then
          ((q.1 : ℝ) * q.2) ^ (-(1 / 2 + δ)) else 0) +
          2 * (1 + 1 / δ) * (exp (-(q.1 * u)) * exp (-(q.2 * u)))) := by
  let a : ℝ := 1 / 2 + δ
  let b : ℝ := (q.1 : ℝ) * q.2
  let E : ℝ := exp (-(q.1 * u)) * exp (-(q.2 * u))
  have hn (n : ℕ+) : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hb : 0 < b := mul_pos (hn _) (hn _)
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left
    (by simpa only [one_rpow, mul_one] using (norm_nonneg _).trans (hw 1 zero_lt_one)) (exp_pos _)
  have he (n : ℕ+) : exp (-(n * u)) ≤ 1 :=
    exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (hn n).le hu.le))
  have hE₁ : E ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (he q.1) (he q.2) (exp_nonneg _) zero_le_one
  have hpair : ‖gaussianMonomial j (q.1 * u)‖ * ‖gaussianMonomial j (q.2 * u)‖ ≤
      (C * u ^ (-a)) ^ 2 * (b ^ (-a) * E) := by
    calc
      _ ≤ (C * ((q.1 : ℝ) * u) ^ (-a) * exp (-(q.1 * u))) *
          (C * ((q.2 : ℝ) * u) ^ (-a) * exp (-(q.2 * u))) :=
        mul_le_mul (hw _ (mul_pos (hn _) hu)) (hw _ (mul_pos (hn _) hu))
          (norm_nonneg _) (by positivity)
      _ = _ := by
        simp only [b, E, Real.mul_rpow (hn q.1).le (hn q.2).le,
          Real.mul_rpow (hn q.1).le hu.le, Real.mul_rpow (hn q.2).le hu.le]
        ring
  apply (mul_le_mul_of_nonneg_right hpair (norm_nonneg _)).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  by_cases hq : IsSquare (ordCompl[2] ((q.1 : ℕ) * q.2))
  · simp only [ite_eq_left hq]
    calc
      _ ≤ b ^ (-a) * 1 * (X : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hE₁ (by positivity))
          (norm_jacobiCorrelation_le _ _) (norm_nonneg _) (by positivity)
      _ ≤ _ := by
        have hnonneg : 0 ≤ 2 * (1 + 1 / δ) * E := by positivity
        simpa only [one_mul, mul_one, mul_comm (X : ℝ)] using
          le_add_of_nonneg_right (a := b ^ (-a) * (X : ℝ)) hnonneg
  · have h : ‖jacobiCorrelation X ((q.1 : ℕ) * q.2)‖ ≤ 2 * (1 + 1 / δ) * b ^ a := by
      simpa only [jacobiCorrelation, oddPartJacobi, b, a, Nat.cast_mul] using
        norm_sum_Icc_jacobiSym_neg_ordCompl_two_le hδ hq X
    have hcancel : b ^ (-a) * b ^ a = 1 := by
      rw [← Real.rpow_add hb, neg_add_cancel, Real.rpow_zero]
    simp only [ite_eq_right hq, mul_zero, zero_add]
    calc
      _ ≤ b ^ (-a) * E * (2 * (1 + 1 / δ) * b ^ a) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      _ = _ := by linear_combination (2 * (1 + 1 / δ) * E) * hcancel

/-- The second moment of the normalized Gaussian theta series twisted by `J(-v | n°)` is
bounded by `C * max X u⁻² * u^(-2δ)` over `1 ≤ v ≤ X`, with `C` independent of the
coefficients, scale and numerator cutoff. Here `n°` is the odd part of `n`. -/
theorem exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ 0, ∀ (X : ℕ) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) → ∀ u ≥ 0,
      (∑ v ∈ Icc 1 X, ‖gaussianThetaSeries j
        (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2) ≤
        C * max (X : ℝ) (u⁻¹ ^ 2) * u ^ (-2 * δ) := by
  classical
  let a : ℝ := 1 / 2 + δ
  let D (q : ℕ+ × ℕ+) : ℝ := if IsSquare (ordCompl[2] ((q.1 : ℕ) * q.2)) then
    ((q.1 : ℝ) * q.2) ^ (-a) else 0
  have hD : Summable D := by
    have h : -a < -1 / 2 := by dsimp [a]; linarith
    refine ((Nat.summable_rpow_isSquare_ordCompl 2 h).comp_injective
        (PNat.coe_injective.prodMap PNat.coe_injective)).congr ?_
    intro q
    simp only [D, Function.comp_apply, Prod.map, Set.indicator_apply, Set.mem_ofPred_eq]
  have hD₀ : 0 ≤ ∑' q, D q := tsum_nonneg fun q ↦ by unfold D; split <;> positivity
  obtain ⟨C, hw⟩ := exists_gaussianMonomial_weighted_le j (a := a) (by dsimp [a]; positivity)
  let P := 2 * (1 + 1 / δ)
  refine ⟨C ^ 2 * ((∑' q, D q) + P),
    mul_nonneg (sq_nonneg _) (add_nonneg hD₀ (by positivity)), fun X c hc u hu ↦ ?_⟩
  rcases hu.eq_or_lt with rfl | hu
  · simp [gaussianThetaSeries_def, Real.zero_rpow (by linarith : -(2 * δ) ≠ 0)]
  let e (n : ℕ+) := exp (-(n * u))
  have he : HasSum e (exp u - 1)⁻¹ := by
    refine (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ exp (-(n * u)))).2 ?_
    simpa only [Nat.cast_succ] using hasSum_exp_neg_nat_succ_mul hu
  have hden : u ≤ exp u - 1 := by linarith [add_one_le_exp u]
  have he₀ : 0 ≤ (exp u - 1)⁻¹ := inv_nonneg.mpr (hu.le.trans hden)
  have he_le : (exp u - 1)⁻¹ ≤ u⁻¹ := inv_anti₀ hu hden
  have hprod := he.summable.mul_of_nonneg he.summable (fun _ ↦ exp_nonneg _) (fun _ ↦ exp_nonneg _)
  have hsum : (∑' q : ℕ+ × ℕ+, e q.1 * e q.2) = ((exp u - 1)⁻¹) ^ 2 := by
    rw [← he.summable.tsum_mul_tsum he.summable hprod, he.tsum_eq, sq]
  have hB := ((hD.mul_left (X : ℝ)).add (hprod.mul_left P)).mul_left ((C * u ^ (-a)) ^ 2)
  have hraw := sum_norm_gaussianTheta_jacobiSym_sq_le j X hc hu hB
    (gaussianPair_mul_norm_jacobiCorrelation_le hδ hu hw X)
  rw [tsum_mul_left, (hD.mul_left (X : ℝ)).tsum_add (hprod.mul_left P), tsum_mul_left,
    tsum_mul_left, hsum] at hraw
  simp_rw [gaussianThetaSeries_def, norm_mul, Complex.norm_real, norm_of_nonneg (sqrt_nonneg u),
    mul_pow, sq_sqrt hu.le, ← mul_sum]
  calc
    _ ≤ u * ((C * u ^ (-a)) ^ 2 * (X * (∑' q, D q) + P * ((exp u - 1)⁻¹) ^ 2)) :=
      mul_le_mul_of_nonneg_left hraw hu.le
    _ ≤ u * ((C * u ^ (-a)) ^ 2 *
        (max (X : ℝ) (u⁻¹ ^ 2) * (∑' q, D q) + P * max (X : ℝ) (u⁻¹ ^ 2))) := by
      gcongr
      · exact le_max_left _ _
      · exact (pow_le_pow_left₀ he₀ he_le 2).trans (le_max_right _ _)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hu.le, Nat.cast_ofNat]
      have hh : u * u ^ (-a * 2) = u ^ (-2 * δ) :=
        calc
          _ = u ^ (1 + -a * 2) := by rw [Real.rpow_add hu, Real.rpow_one]
          _ = _ := by congr 1; dsimp [a]; ring
      linear_combination (C ^ 2 * max (X : ℝ) (u⁻¹ ^ 2) * ((∑' q, D q) + P)) * hh

/-- At scales `u ≥ 1 / T`, the Jacobi-twisted theta second moment over the numerators
`1 ≤ v ≤ T²` is at most `C * T² * u^(-2δ)`. -/
theorem exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le_cutoff
    (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ 0, ∀ (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) → ∀ {T : ℝ}, 0 ≤ T → ∀ {u : ℝ}, T⁻¹ ≤ u →
      (∑ v ∈ Icc 1 ⌊T ^ 2⌋₊, ‖gaussianThetaSeries j
        (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2) ≤
        C * T ^ 2 * u ^ (-2 * δ) := by
  obtain ⟨C, hC, h⟩ := exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le j hδ
  refine ⟨C, hC, fun c hc T hT u hu ↦ ?_⟩
  rcases hT.eq_or_lt with rfl | hT
  · simp
  have hu₀ := (inv_pos.mpr hT).trans_le hu
  refine (h _ c hc _ hu₀.le).trans ?_
  have hInv : u⁻¹ ≤ T := inv_le_of_inv_le₀ hT hu
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (max_le (Nat.floor_le (sq_nonneg T)) (pow_le_pow_left₀ (by positivity) hInv 2)) hC)
    (by positivity)

end TauCeti
