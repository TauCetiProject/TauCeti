/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import TauCeti.NumberTheory.LSeries.Quadratic.Theta.Tail
import TauCeti.Analysis.PSeries.Square
import TauCeti.MeasureTheory.Integral.Bochner.PowerTail
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.SeriesMeanSquare

/-!
# Mean square of Gaussian theta series twisted by Jacobi symbols

Average over the numerators of the Jacobi symbols. The pairs with square odd part are
controlled by a summable power weight; for the other pairs, Pólya–Vinogradov supplies the
saving. Integrating the resulting second moment bounds the sum of the joint theta tails.

This follows the diagonal/off-diagonal argument of `New.sum_sq_thetaSeries_jacobiSym_le`
and the tail averaging of `New.sum_thetaTailIntegral_le` in
`grh/src/Lib/Analytic/QuadraticTwist.lean` of
[grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Finset MeasureTheory Real Set
open scoped ArithmeticFunction.Moebius Nat

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
  let n : ℕ := (p.1 : ℕ) * p.2
  let b : ℕ := ordCompl[2] n
  have hb : 1 ≤ (b : ℝ) := Nat.one_le_cast.mpr (Nat.ordCompl_pos 2 (by dsimp [n]; positivity))
  have hbn : (b : ℝ) ≤ (p.1 : ℝ) * p.2 := by
    exact_mod_cast Nat.ordCompl_le n 2
  have hlog : 1 + log b ≤ (1 + 2 / δ) * (b : ℝ) ^ (δ / 2) := calc
    _ ≤ (b : ℝ) ^ (δ / 2) + (b : ℝ) ^ (δ / 2) / (δ / 2) :=
      add_le_add (one_le_rpow hb (by positivity)) (log_le_rpow_div (by positivity) (by positivity))
    _ = _ := by ring
  have hb' : 0 < (b : ℝ) := by linarith
  have hPV : 2 * √(b : ℝ) * (1 + log b) ≤
      2 * (1 + 2 / δ) * ((p.1 : ℝ) * p.2) ^ (1 / 2 + δ / 2) := calc
    _ ≤ 2 * √(b : ℝ) * ((1 + 2 / δ) * (b : ℝ) ^ (δ / 2)) := by gcongr
    _ = 2 * (1 + 2 / δ) * (b : ℝ) ^ (1 / 2 + δ / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_add hb']; ring
    _ ≤ _ := by gcongr
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

private theorem gaussianTheta_moment_scale {T u δ X D K d o : ℝ} (hT : 0 < T)
    (hTu : T⁻¹ ≤ u) (hX : X ≤ T ^ 2) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hd : 0 ≤ d) (ho : 0 ≤ o) :
    u * ((D * u ^ (-2 * (1 / 2 + δ)) * X) * d + K * u ^ (-3 - 2 * δ) * o) ≤
      (D * d + K * o + 1) * T ^ 2 * u ^ (-2 * δ) := by
  have hu := (inv_pos.mpr hT).trans_le hTu
  have hi : u⁻¹ ≤ T := (inv_le_comm₀ hu hT).mpr hTu
  have hr (s : ℝ) : u * u ^ s = u ^ (1 + s) := by rw [Real.rpow_add hu, Real.rpow_one]
  have hd' : u * u ^ (-2 * (1 / 2 + δ)) = u ^ (-2 * δ) := by
    rw [hr, show 1 + -2 * (1 / 2 + δ) = -2 * δ by ring]
  have ho' : u * u ^ (-3 - 2 * δ) = u⁻¹ ^ 2 * u ^ (-2 * δ) := by
    rw [hr, show 1 + (-3 - 2 * δ) = -2 + (-2 * δ) by ring, Real.rpow_add hu,
      Real.rpow_neg hu.le, Real.rpow_two, inv_pow]
  calc
    _ = (D * d * X + K * o * u⁻¹ ^ 2) * u ^ (-2 * δ) := by
      linear_combination (D * X * d) * hd' + (K * o) * ho'
    _ ≤ (D * d * T ^ 2 + K * o * T ^ 2) * u ^ (-2 * δ) := by
      gcongr
    _ = (D * d + K * o) * T ^ 2 * u ^ (-2 * δ) := by ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (sq_nonneg T)

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
  rfl

private theorem gaussianTheta_jacobi_moment_le {j : Fin 2} {c : ℕ → ℂ} {u δ D E : ℝ}
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
  have hf : Summable f := hs.of_nonneg_of_le (fun p ↦
    mul_nonneg (by positivity) ((norm_nonneg _).trans
      (norm_sum_mul_jacobiSym_ordCompl_le X p.1 p.2))) hmajor
  have hsum : ∑' p, f p ≤ A * (∑' p, thetaDiagonalWeight δ p) + B * (∑' p, o p) := by
    simpa only [((hds.mul_left A).tsum_add (hos.mul_left B)), tsum_mul_left] using
      hf.tsum_le_tsum hmajor hs
  have hnorm (v : ℕ) :
      ‖gaussianThetaSeries j (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2 =
        u * ‖∑' n : ℕ+, a n * (jacobiSym (-(v : ℤ)) (ordCompl[2] (n : ℕ)) : ℂ)‖ ^ 2 := by
    rw [gaussianThetaSeries_def, norm_mul, mul_pow, Complex.norm_real,
      norm_of_nonneg (sqrt_nonneg u), Real.sq_sqrt hu.le, gaussianTheta_def]
    simp only [a, mul_right_comm]
  simp_rw [hnorm, ← mul_sum]
  exact mul_le_mul_of_nonneg_left ((sum_norm_tsum_mul_jacobiSym_sq_le X ha).trans hsum) hu.le

/-- The Jacobi-symbol twists of a Gaussian theta series with unit-bounded coefficients have
second moment at most `C T² u^(-2δ)` over numerators `1 ≤ v ≤ T²`, at every scale `u ≥ 1/T`.
The constant is uniform in the coefficients and in the parity. -/
theorem exists_sum_sq_gaussianThetaSeries_jacobi_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) →
      ∀ T > 0, ∀ u ≥ T⁻¹,
        ∑ v ∈ Icc 1 ⌊T ^ 2⌋₊,
          ‖gaussianThetaSeries j (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2
          ≤ C * T ^ 2 * u ^ (-2 * δ) := by
  obtain ⟨D, _, hd⟩ := exists_norm_gaussianMonomial_le_mul_rpow (s := 1 / 2 + δ) (by positivity)
  obtain ⟨E, _, he⟩ := exists_norm_gaussianMonomial_le_mul_rpow (s := 3 / 2 + δ) (by positivity)
  let d := ∑' p, thetaDiagonalWeight δ p
  let o := ∑' p : ℕ+ × ℕ+, ((p.1 : ℝ) * p.2) ^ (-1 - δ / 2)
  let K := E ^ 2 * (2 * (1 + 2 / δ))
  have hd₀ : 0 ≤ d := tsum_nonneg (thetaDiagonalWeight_nonneg δ)
  have ho₀ : 0 ≤ o := tsum_nonneg fun _ ↦ by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨D ^ 2 * d + K * o + 1, by positivity, fun j c hc T hT u hTu ↦ ?_⟩
  have hu := (inv_pos.mpr hT).trans_le hTu
  exact (gaussianTheta_jacobi_moment_le hδ hc hu (hd j) (he j) _).trans
    (gaussianTheta_moment_scale hT hTu (Nat.floor_le (sq_nonneg T)) (sq_nonneg D) hK hd₀ ho₀)

/-- The summed joint tails (including the Möbius twists) of a Jacobi-symbol family are at most
`C T^(2+δ)` over the numerators `1 ≤ v ≤ T²`, uniformly in the parity and in the unit-bounded
coefficient sequence. -/
theorem exists_sum_quadraticTwistGaussianThetaTailIntegral_jacobi_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) → ∀ T > 0,
      ∑ v ∈ Icc 1 ⌊T ^ 2⌋₊, quadraticTwistGaussianThetaTailIntegral j
        (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) T ≤ C * T ^ (2 + δ) := by
  obtain ⟨C, hC, h⟩ := exists_sum_sq_gaussianThetaSeries_jacobi_le hδ
  refine ⟨2 * √C / δ, by positivity, fun j c hc T hT ↦ ?_⟩
  let J (v n : ℕ) : ℂ := jacobiSym (-(v : ℤ)) (ordCompl[2] n)
  let m (n : ℕ) : ℂ := c n * μ n
  let s := Finset.Icc 1 ⌊T ^ 2⌋₊
  have hm (n : ℕ+) : ‖m n‖ ≤ 1 := by
    unfold m
    rw [norm_mul]
    have hμ : ‖(μ n : ℂ)‖ ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)
    exact (mul_le_of_le_one_right (norm_nonneg _) hμ).trans (hc n)
  have hJ (v n : ℕ) : ‖J v n‖ ≤ 1 := by
    have hj := Int.abs_le_one_iff.mpr (jacobiSym.trichotomy (-(v : ℤ)) (ordCompl[2] n))
    dsimp only [J]
    rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hj
  have ht := inv_pos.mpr hT
  have htail (a : ℕ → ℂ) (ha : ∀ n : ℕ+, ‖a n‖ ≤ 1) :=
    sum_setIntegral_norm_div_le_of_sum_sq_le (s := s) (C := C * T ^ 2)
      (f := fun v ↦ gaussianThetaSeries j (fun n ↦ a n * J v n)) ht hδ
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ h j a ha T hT u hu.le)
  have hsplit (v : ℕ) : quadraticTwistGaussianThetaTailIntegral j (fun n ↦ c n * J v n) T =
      (∫ u in Ioi T⁻¹, ‖gaussianThetaSeries j (fun n ↦ c n * J v n) u‖ / u) +
      (∫ u in Ioi T⁻¹, ‖gaussianThetaSeries j (fun n ↦ m n * J v n) u‖ / u) := by
    have hInt (a : ℕ → ℂ) (ha : ∀ n : ℕ+, ‖a n‖ ≤ 1) :=
      integrableOn_norm_gaussianThetaSeries_div (j := j) (c := fun n ↦ a n * J v n)
        (fun n ↦ by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (hJ v n)).trans (ha n)) ht
    have hm' (n : ℕ) : c n * J v n * (μ n : ℂ) = m n * J v n := mul_right_comm ..
    rw [quadraticTwistGaussianThetaTailIntegral_def]
    simp_rw [add_div, hm']
    exact integral_add (hInt c hc) (hInt m hm)
  rw [Finset.sum_congr rfl (fun v _ ↦ hsplit v), Finset.sum_add_distrib]
  refine (add_le_add (htail c hc) (htail m hm)).trans ?_
  have hs : √(s.card : ℝ) ≤ T := by
    simpa only [s, Nat.card_Icc, Nat.add_sub_cancel, Real.sqrt_sq hT.le] using
      Real.sqrt_le_sqrt (Nat.floor_le (sq_nonneg T))
  have hr : (T⁻¹) ^ (-δ) = T ^ δ := by rw [Real.inv_rpow hT.le, Real.rpow_neg hT.le, inv_inv]
  rw [hr, Real.sqrt_mul hC.le, Real.sqrt_sq hT.le]
  calc
    _ ≤ T * (√C * T) * T ^ δ / δ + T * (√C * T) * T ^ δ / δ := by gcongr
    _ = _ := by rw [Real.rpow_add hT, Real.rpow_two]; ring

end TauCeti
