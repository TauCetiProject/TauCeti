/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Basic
import TauCeti.Analysis.PSeries.Square
import TauCeti.NumberTheory.DirichletCharacter.Bounds
import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.MeanSquare
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.Char
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.PolyaVinogradov
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.SeriesMeanSquare

/-!
# Mean square of Gaussian theta series twisted by Jacobi symbols

Average over the numerators of the Jacobi symbols. The pairs with square odd part are
controlled by a summable power weight; for the other pairs, Pólya–Vinogradov supplies the
saving. Integrating the resulting second moment bounds the sum of the joint theta tails.

## References

The argument adapts the real-character mean value method of M. Jutila,
*On mean values of Dirichlet polynomials with real characters*, Acta Arith. 27 (1975), and
D. R. Heath-Brown, *A mean value estimate for real character sums*, Acta Arith. 72 (1995).

The formal proof follows the diagonal/off-diagonal argument of `New.sum_sq_thetaSeries_jacobiSym_le`
and the tail averaging of `New.sum_thetaTailIntegral_le` in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Finset MeasureTheory Real Set
open scoped Nat

namespace TauCeti

private theorem norm_gaussianTheta_pair_le {j : Fin 2} {c : ℕ → ℂ} {s C u : ℝ}
    (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (hu : 0 < u)
    (h : ∀ x > 0, ‖gaussianMonomial j x‖ ≤ C * x ^ (-s)) (p : ℕ+ × ℕ+) :
    ‖c p.1 * gaussianMonomial j (p.1 * u)‖ * ‖c p.2 * gaussianMonomial j (p.2 * u)‖ ≤
      (C ^ 2 * u ^ (-2 * s)) * ((p.1 : ℝ) * p.2) ^ (-s) := by
  have hb (n : ℕ+) : ‖c n * gaussianMonomial j (n * u)‖ ≤ C * ((n : ℝ) * u) ^ (-s) := by
    rw [norm_mul, Complex.norm_real]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hc n)).trans (h _ (by positivity))
  have he : u ^ (-s) * u ^ (-s) = u ^ (-2 * s) := by rw [← Real.rpow_add hu]; ring_nf
  calc
    _ ≤ (C * ((p.1 : ℝ) * u) ^ (-s)) * (C * ((p.2 : ℝ) * u) ^ (-s)) := by
      exact mul_le_mul (hb _) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (hb _))
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), ← he]
      ring

private theorem gaussianTheta_pair_offDiag_le {j : Fin 2} {c : ℕ → ℂ} {δ C u : ℝ}
    (hδ : 0 < δ) (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (hu : 0 < u)
    (h : ∀ x > 0, ‖gaussianMonomial j x‖ ≤ C * x ^ (-(3 / 2 + δ))) (p : ℕ+ × ℕ+) :
    let b := ordCompl[2] ((p.1 : ℕ) * p.2)
    ‖c p.1 * gaussianMonomial j (p.1 * u)‖ * ‖c p.2 * gaussianMonomial j (p.2 * u)‖ *
      (2 * √(b : ℝ) * (1 + log b)) ≤
      (C ^ 2 * (2 * (1 + 2 / δ)) * u ^ (-3 - 2 * δ)) * ((p.1 : ℝ) * p.2) ^ (-1 - δ / 2) := by
  have hPV : 2 * √(ordCompl[2] ((p.1 : ℕ) * p.2) : ℕ) *
      (1 + log (ordCompl[2] ((p.1 : ℕ) * p.2) : ℕ)) ≤
      2 * (1 + 2 / δ) * ((p.1 : ℝ) * p.2) ^ (1 / 2 + δ / 2) := by
    simpa only [one_div_div, div_one, Nat.cast_mul] using
      two_mul_sqrt_ordCompl_mul_one_add_log_le (n := (p.1 : ℕ) * p.2) (ε := δ / 2)
        (by positivity)
  have hp : 0 < (p.1 : ℝ) * p.2 := by positivity
  calc
    _ ≤ (C ^ 2 * u ^ (-2 * (3 / 2 + δ)) * ((p.1 : ℝ) * p.2) ^ (-(3 / 2 + δ))) *
        (2 * (1 + 2 / δ) * ((p.1 : ℝ) * p.2) ^ (1 / 2 + δ / 2)) := by
      exact mul_le_mul (norm_gaussianTheta_pair_le hc hu h p) hPV
        (by positivity) (by positivity)
    _ = _ := by
      have he : -(3 / 2 + δ) + (1 / 2 + δ / 2) = -1 - δ / 2 := by ring
      rw [← he, Real.rpow_add hp (-(3 / 2 + δ)), show -2 * (3 / 2 + δ) = -3 - 2 * δ by ring]
      ring

private def thetaSquarePairs : Set (ℕ+ × ℕ+) := {p | IsSquare (ordCompl[2] ((p.1 : ℕ) * p.2))}

private noncomputable def thetaDiagonalWeight (δ : ℝ) : ℕ+ × ℕ+ → ℝ :=
  thetaSquarePairs.indicator (fun p ↦ ((p.1 : ℝ) * p.2) ^ (-(1 / 2 + δ)))

private theorem thetaDiagonalWeight_nonneg (δ : ℝ) (p : ℕ+ × ℕ+) :
    0 ≤ thetaDiagonalWeight δ p := by
  unfold thetaDiagonalWeight
  exact indicator_apply_nonneg (fun _ ↦ by positivity)

private theorem summable_thetaDiagonalWeight {δ : ℝ} (hδ : 0 < δ) :
    Summable (thetaDiagonalWeight δ) := by
  have hcast : Function.Injective (Prod.map (Subtype.val : ℕ+ → ℕ) (Subtype.val : ℕ+ → ℕ)) :=
    Subtype.val_injective.prodMap Subtype.val_injective
  have h := (Nat.summable_rpow_isSquare_ordCompl 2
    (s := -(1 / 2 + δ)) (by linarith)).comp_injective hcast
  refine h.congr fun p ↦ ?_
  rw [Function.comp_apply, ← indicator_comp_right, thetaDiagonalWeight]
  -- Pulling the square condition back along `Prod.map Subtype.val Subtype.val` gives
  -- `thetaSquarePairs`; the real casts of positive naturals already factor through `ℕ`.
  rfl

private theorem norm_sq_gaussianThetaSeries_mul_jacobiSym (j : Fin 2) (c : ℕ → ℂ) (v : ℕ)
    {u : ℝ} (hu : 0 ≤ u) :
    ‖gaussianThetaSeries j (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2 =
      u * ‖∑' n : ℕ+, (c n * (gaussianMonomial j (n * u) : ℂ)) *
        (jacobiSym (-(v : ℤ)) (ordCompl[2] (n : ℕ)) : ℂ)‖ ^ 2 := by
  rw [gaussianThetaSeries_def, norm_mul, mul_pow, Complex.norm_real,
    norm_of_nonneg (sqrt_nonneg u), Real.sq_sqrt hu, gaussianTheta_def]
  simp only [mul_right_comm]

private theorem gaussianTheta_jacobiSym_moment_le {j : Fin 2} {c : ℕ → ℂ} {u δ D E : ℝ}
    (hδ : 0 < δ) (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (hu : 0 < u)
    (hd : ∀ x > 0, ‖gaussianMonomial j x‖ ≤ D * x ^ (-(1 / 2 + δ)))
    (he : ∀ x > 0, ‖gaussianMonomial j x‖ ≤ E * x ^ (-(3 / 2 + δ))) (X : ℕ) :
    ∑ v ∈ Icc 1 X,
      ‖gaussianThetaSeries j (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2 ≤
    u * ((D ^ 2 * u ^ (-2 * (1 / 2 + δ)) * (X : ℝ)) * (∑' p, thetaDiagonalWeight δ p) +
      (E ^ 2 * (2 * (1 + 2 / δ)) * u ^ (-3 - 2 * δ)) *
        ∑' p : ℕ+ × ℕ+, ((p.1 : ℝ) * p.2) ^ (-1 - δ / 2)) := by
  classical
  let o (p : ℕ+ × ℕ+) := ((p.1 : ℝ) * p.2) ^ (-1 - δ / 2)
  have hds := summable_thetaDiagonalWeight hδ
  have ho₁ : Summable (fun n : ℕ+ ↦ (n : ℝ) ^ (-1 - δ / 2)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).comp_injective Subtype.val_injective
  have hpow (n : ℕ+) : 0 ≤ (n : ℝ) ^ (-1 - δ / 2) := by positivity
  have hos : Summable o := (ho₁.mul_of_nonneg ho₁ hpow hpow).congr
    fun _ ↦ (Real.mul_rpow (by positivity) (by positivity)).symm
  let K := E ^ 2 * (2 * (1 + 2 / δ))
  let a (n : ℕ+) := c n * (gaussianMonomial j (n * u) : ℂ)
  have ha : Summable (fun n ↦ ‖a n‖) :=
    (summable_gaussianTheta (j := j) hc hu).norm
  have ho₀ (p) : 0 ≤ o p := by dsimp [o]; positivity
  have hodd (n : ℕ+) : Odd (ordCompl[2] (n : ℕ)) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two n.ne_zero)
  let A := D ^ 2 * u ^ (-2 * (1 / 2 + δ)) * (X : ℝ)
  let B := K * u ^ (-3 - 2 * δ)
  let f (p : ℕ+ × ℕ+) : ℝ := ‖a p.1‖ * ‖a p.2‖ *
    (let b := ordCompl[2] ((p.1 : ℕ) * p.2)
     if IsSquare b then (X : ℝ) else min X (2 * √(b : ℝ) * (1 + log b)))
  -- The square and nonsquare pairs are paid for by different summable majorants.
  have hmajor (p : ℕ+ × ℕ+) : f p ≤ A * thetaDiagonalWeight δ p + B * o p := by
    dsimp only [f]
    split_ifs with hp
    · rw [thetaDiagonalWeight, indicator_of_mem (s := thetaSquarePairs) hp]
      refine (mul_le_mul_of_nonneg_right (norm_gaussianTheta_pair_le hc hu hd p)
        (Nat.cast_nonneg X)).trans ?_
      calc
        _ = A * ((p.1 : ℝ) * p.2) ^ (-(1 / 2 + δ)) := by dsimp only [A]; ring
        _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (by dsimp [B, K]; positivity) (ho₀ p))
    · rw [thetaDiagonalWeight, indicator_of_notMem (s := thetaSquarePairs) hp, mul_zero, zero_add]
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans
        (gaussianTheta_pair_offDiag_le hδ hc hu he p)
  have hs : Summable (fun p ↦ A * thetaDiagonalWeight δ p + B * o p) :=
    (hds.mul_left A).add (hos.mul_left B)
  have hf : Summable f := hs.of_nonneg_of_le (fun p ↦ by
    have hb : Odd (ordCompl[2] ((p.1 : ℕ) * p.2)) := by
      rw [Nat.ordCompl_mul]
      exact (hodd p.1).mul (hodd p.2)
    exact mul_nonneg (by positivity) ((norm_nonneg _).trans (norm_sum_jacobiSym_neg_Icc_le hb X)))
    hmajor
  have hsum : ∑' p, f p ≤ A * (∑' p, thetaDiagonalWeight δ p) + B * (∑' p, o p) := by
    simpa only [((hds.mul_left A).tsum_add (hos.mul_left B)), tsum_mul_left] using
      hf.tsum_le_tsum hmajor hs
  simp_rw [norm_sq_gaussianThetaSeries_mul_jacobiSym j c _ hu.le, ← mul_sum]
  have hmoment := sum_norm_sq_tsum_jacobiSym_neg_le (fun n : ℕ+ ↦ ordCompl[2] (n : ℕ)) a
    hodd ha X
  simp_rw [← Nat.ordCompl_mul] at hmoment
  exact mul_le_mul_of_nonneg_left (hmoment.trans hsum) hu.le

private theorem sum_norm_sq_gaussianThetaSeries_mul_jacobiSym_le_exp {j : Fin 2}
    {c : ℕ → ℂ} {u T : ℝ} (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) (hu : 0 < u) :
    ∑ v ∈ Icc 1 ⌊T ^ 2⌋₊,
      ‖gaussianThetaSeries j (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2
      ≤ 9 * T ^ 2 * exp (-u) ^ 2 / u := by
  have hterm (v : ℕ) :
      ‖gaussianThetaSeries j (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ≤
        3 * exp (-u) / √u := by
    apply norm_gaussianThetaSeries_le _ u
    intro n
    let b := ordCompl[2] (n : ℕ)
    let : NeZero b := ⟨(Nat.ordCompl_pos 2 n.ne_zero).ne'⟩
    have hJ : ‖(jacobiSym (-(v : ℤ)) b : ℂ)‖ ≤ 1 := by
      rw [← jacobiChar_intCast]
      exact (jacobiChar ℂ b).norm_le_one _
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hJ).trans (hc n)
  calc
    _ ≤ ∑ _v ∈ Icc 1 ⌊T ^ 2⌋₊, (3 * exp (-u) / √u) ^ 2 := by
      exact sum_le_sum fun v _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hterm v) 2
    _ ≤ T ^ 2 * (3 * exp (-u) / √u) ^ 2 := by
      simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
      exact mul_le_mul_of_nonneg_right (Nat.floor_le (sq_nonneg T)) (sq_nonneg _)
    _ = _ := by rw [div_pow, Real.sq_sqrt hu.le]; ring

/-- The Jacobi-symbol twists of a Gaussian theta series with unit-bounded coefficients have
second moment at most `C T² u^(-2δ)` over numerators `1 ≤ v ≤ T²`, at every scale `u ≥ 1/T`.
The constant is uniform in the coefficients and in the parity. The bound also retains the
exponential decay at large scales. -/
theorem exists_sum_norm_sq_gaussianThetaSeries_mul_jacobiSym_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) →
      ∀ T ≥ 0, ∀ u ≥ T⁻¹,
        ∑ v ∈ Icc 1 ⌊T ^ 2⌋₊,
          ‖gaussianThetaSeries j (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2
          ≤ min (C * T ^ 2 * u ^ (-2 * δ)) (9 * T ^ 2 * exp (-u) ^ 2 / u) := by
  obtain ⟨D, _, hd⟩ := exists_norm_gaussianMonomial_le_mul_rpow (s := 1 / 2 + δ) (by positivity)
  obtain ⟨E, _, he⟩ := exists_norm_gaussianMonomial_le_mul_rpow (s := 3 / 2 + δ) (by positivity)
  let d := ∑' p, thetaDiagonalWeight δ p
  let o := ∑' p : ℕ+ × ℕ+, ((p.1 : ℝ) * p.2) ^ (-1 - δ / 2)
  let K := E ^ 2 * (2 * (1 + 2 / δ))
  have hd₀ : 0 ≤ d := tsum_nonneg (thetaDiagonalWeight_nonneg δ)
  have ho₀ : 0 ≤ o := tsum_nonneg fun _ ↦ by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨D ^ 2 * d + K * o + 1, by positivity, fun j c hc T hT u hTu ↦ ?_⟩
  rcases hT.eq_or_lt with rfl | hT
  · simp
  have hu := (inv_pos.mpr hT).trans_le hTu
  refine le_min ?_ (sum_norm_sq_gaussianThetaSeries_mul_jacobiSym_le_exp hc hu)
  refine (gaussianTheta_jacobiSym_moment_le hδ hc hu (hd j) (he j) _).trans ?_
  have hX : (⌊T ^ 2⌋₊ : ℝ) ≤ T ^ 2 := Nat.floor_le (sq_nonneg T)
  have hi : u⁻¹ ≤ T := (inv_le_comm₀ hu hT).mpr hTu
  have hd' : u * u ^ (-2 * (1 / 2 + δ)) = u ^ (-2 * δ) := by
    rw [mul_comm, ← Real.rpow_add_one hu.ne', show -2 * (1 / 2 + δ) + 1 = -2 * δ by ring]
  have ho' : u * u ^ (-3 - 2 * δ) = u ^ (-2 * δ) * u⁻¹ ^ 2 := by
    rw [mul_comm, ← Real.rpow_add_one hu.ne', show -3 - 2 * δ + 1 = -2 * δ - 2 by ring,
      Real.rpow_sub hu, Real.rpow_two, div_eq_mul_inv, inv_pow]
  change u * ((D ^ 2 * u ^ (-2 * (1 / 2 + δ)) * _) * d + K * u ^ (-3 - 2 * δ) * o) ≤ _
  calc
    _ = (D ^ 2 * d * (⌊T ^ 2⌋₊ : ℝ) + K * o * u⁻¹ ^ 2) * u ^ (-2 * δ) := by
      linear_combination (D ^ 2 * (⌊T ^ 2⌋₊ : ℝ) * d) * hd' + (K * o) * ho'
    _ ≤ (D ^ 2 * d * T ^ 2 + K * o * T ^ 2) * u ^ (-2 * δ) := by
      exact mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_left hX (mul_nonneg (sq_nonneg D) hd₀))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hi 2) (mul_nonneg hK ho₀)))
        (by positivity)
    _ = (D ^ 2 * d + K * o) * T ^ 2 * u ^ (-2 * δ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (sq_nonneg T)) (by positivity)

/-- The summed joint tails (including the Möbius twists) of a Jacobi-symbol family are at most
`C T^(2+δ)` over the numerators `1 ≤ v ≤ T²`, uniformly in the parity and in the unit-bounded
coefficient sequence. -/
theorem exists_sum_quadraticTwistGaussianThetaTailIntegral_mul_jacobiSym_le
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) → ∀ T ≥ 0,
      ∑ v ∈ Icc 1 ⌊T ^ 2⌋₊, quadraticTwistGaussianThetaTailIntegral j
        (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) T ≤ C * T ^ (2 + δ) := by
  obtain ⟨C, hC, h⟩ := exists_sum_norm_sq_gaussianThetaSeries_mul_jacobiSym_le hδ
  refine ⟨2 * √C / δ, by positivity, fun j c hc T hT ↦ ?_⟩
  rcases hT.eq_or_lt with rfl | hT
  · have hpow : 2 + δ ≠ 0 := by positivity
    simp [Real.zero_rpow hpow]
  refine sum_quadraticTwistGaussianThetaTailIntegral_jacobiSym_le hT hδ hc (fun b hb ↦ ?_)
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦
    (h j b hb T hT.le u hu.le).trans (min_le_left _ _)

end TauCeti
