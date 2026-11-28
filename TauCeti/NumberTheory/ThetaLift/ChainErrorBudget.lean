/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Error budget for the Frobenius inequality of a theta chain

The errors from rank matching, division, type primes, source slopes, local gain, source losses,
and the two frame corrections fit into a single bound. The source spread contributes one factor
of `x ^ ε` (from the bound on `La`), and its logarithmic coefficient `log (1 + x ^ c)` in the
frame inequality contributes a second. A third factor of `x ^ ε` absorbs the constants before
the Frobenius comparison.

The decomposition into arithmetic and frame errors follows Levent Alpöge's
`Formalism.LFunctionChainParameters.LErr.ErrText` and `CErr` in
`Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

namespace TauCeti

private theorem thetaChainSourceLoss_le {P a m b b' k X C y : ℝ}
    (hP : 0 ≤ P) (hk : 0 < k) (hC : 0 ≤ C) (hy : 0 ≤ y)
    (hmb : m * b ≤ a) (hb' : k * b' ≤ a) (hX : X ≤ a) (hPa : a ≤ P * a) :
    C * (P * m * b + P * m ^ 2 * (a / k + b') * y + X) + 1 ≤
      C * (2 * (P * a) + 2 * (P * a * (m ^ 2 / k)) * y) + 1 := by
  have hb'' : b' ≤ a / k := (le_div_iff₀ hk).mpr (by rwa [mul_comm])
  have h₁ : P * m * b ≤ P * a := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmb hP
  have h₂ : P * m ^ 2 * (a / k + b') * y ≤ 2 * (P * a * (m ^ 2 / k)) * y := by
    calc
      _ ≤ P * m ^ 2 * (a / k + a / k) * y := by gcongr
      _ = _ := by ring
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ hC
  linarith only [h₁, h₂, hX, hPa]

private theorem thetaChainSlopeSpread_add_le {A R T b C y E₇ : ℝ}
    (hA₁ : 1 ≤ A) (hR : 0 ≤ R) (hT : 0 ≤ T) (hC : 0 ≤ C) (hy : 1 ≤ y) (hAb : b ≤ A)
    (hE₇ : E₇ ≤ C * (2 * A + 2 * R * y) + 1) :
    C * (6 * y * A + T + 2 * y * A) + E₇ + b ≤ 12 * (1 + C) * y * (A + R + T) := by
  have hA := zero_le_one.trans hA₁
  have hAy := le_mul_of_one_le_left hA hy
  have hTy := le_mul_of_one_le_left hT hy
  have hyT := hT.trans hTy
  have hyA := hA.trans hAy
  have hyR := mul_nonneg (zero_le_one.trans hy) hR
  have hcore : 6 * y * A + T + 2 * y * A + (2 * A + 2 * R * y) ≤
      10 * (y * A) + y * T + 2 * (y * R) := by linarith only [hAy, hTy]
  calc
    _ ≤ C * (10 * (y * A) + y * T + 2 * (y * R)) + 2 * A := by
      linarith only [mul_le_mul_of_nonneg_left hcore hC, hAb, hA₁, hE₇]
    _ ≤ _ := by
      linarith only [hAy, hyA, hyR, hyT, mul_nonneg hC hyA, mul_nonneg hC hyR, mul_nonneg hC hyT]

private theorem thetaChainSubtotal_le {A R T C y : ℝ} (hA₁ : 1 ≤ A) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hC : 0 ≤ C) (hy : 1 ≤ y) :
    4 * C * y * (A + R) + 2 * C * y * A + C * T * y + C * T + 4 * C * y * A + C * A +
        (C * (2 * A + 2 * R * y) + 1) + 12 * (A + R + T) ≤
      14 * (1 + C) * y * (A + R + T) := by
  have hA := zero_le_one.trans hA₁
  have hAy := le_mul_of_one_le_left hA hy
  have hRy := le_mul_of_one_le_left hR hy
  have hTy := le_mul_of_one_le_left hT hy
  have hcore : 4 * y * (A + R) + 2 * y * A + T * y + T + 4 * y * A + A +
        (2 * A + 2 * R * y) ≤ 14 * y * (A + R + T) := by
    linarith only [hAy, hTy, hA.trans hAy, hR.trans hRy, hT.trans hTy]
  linarith only [hA₁, hAy, hRy, hTy, hR, hT, mul_le_mul_of_nonneg_left hcore hC]

private theorem thetaChainFrameErrors_le {x c D F U b E C y : ℝ} (hx : 0 ≤ x)
    (hC : 0 ≤ C) (hy : 0 ≤ y) (hE : 0 ≤ E)
    (hb : 0 ≤ b) (hbE : b ≤ E) (hD₀ : 0 ≤ D) (hD : D ≤ 2) (hF : F ≤ 6)
    (hlog : Real.log (1 + x ^ c) ≤ (1 + c) * y) (hU : U + b ≤ 12 * (1 + C) * y * E) :
    D * 4 * Real.log (1 + x ^ c) * (U + b) + D * F * b ≤
      96 * (1 + C) * (1 + c) * y ^ 2 * E + 12 * E := by
  have hlog₀ : 0 ≤ Real.log (1 + x ^ c) := Real.log_nonneg (by linarith [Real.rpow_nonneg hx c])
  have hspread : D * 4 * Real.log (1 + x ^ c) * (U + b) ≤
      96 * (1 + C) * (1 + c) * y ^ 2 * E := by
    calc
      _ ≤ D * 4 * Real.log (1 + x ^ c) * (12 * (1 + C) * y * E) := by gcongr
      _ ≤ 2 * 4 * ((1 + c) * y) * (12 * (1 + C) * y * E) := by gcongr
      _ = _ := by ring
  have hdefect : D * F * b ≤ 12 * E := by
    calc
      _ ≤ D * 6 * b := by gcongr
      _ ≤ 2 * 6 * E := by gcongr
      _ = _ := by ring
  exact add_le_add hspread hdefect

private theorem thetaChainRankError_le {C A_top La y A v : ℝ}
    (hC : 0 ≤ C) (hA_top : 0 ≤ A_top) (hy : 0 ≤ y) (hv : 0 ≤ v)
    (hLa : La ≤ 2 * y) (hA : A_top ≤ 2 * A) :
    C * A_top * La * (1 + v) ≤ 4 * C * y * (A + A * v) := by
  calc
    _ ≤ (C * (2 * A) * (2 * y)) * (1 + v) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (mul_le_mul_of_nonneg_left hLa (by positivity)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hC) (by positivity))
    _ = _ := by ring

private theorem thetaChainBudget_absorb {C c y : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hlarge : 200 * (1 + C) * (1 + c) ≤ y) :
    14 * (1 + C) * y + 96 * (1 + C) * (1 + c) * y ^ 2 ≤ y ^ 3 := by
  have hprod : 1 ≤ (1 + C) * (1 + c) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  have hy : 1 ≤ y := by linarith only [hprod, hlarge]
  have hy₀ : 0 ≤ y := zero_le_one.trans hy
  have h₁ : (1 + C) * y ≤ (1 + C) * (1 + c) * y ^ 2 := by
    calc
      _ ≤ (1 + C) * y ^ 2 := by gcongr; nlinarith only [mul_nonneg hy₀ (sub_nonneg.mpr hy)]
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity) (by linarith)) (sq_nonneg y)
  linarith only [h₁, mul_le_mul_of_nonneg_right hlarge (sq_nonneg y),
    mul_nonneg (zero_le_one.trans hprod) (sq_nonneg y)]

/-- The nine errors of the Frobenius-restricted theta-chain inequality have total at most
`x ^ (3 * ε)` times the sum of the top-place and per-lift budgets,
`P * a * (1 + m ^ 2 / k) + m * (B + N)`.

The scale is `x`, and `y = x ^ ε` is the scale factor that absorbs logarithms and constants.
`P` is the number of top places, `A_top` sums their top weights, and `a` is the top weight of a
single place, with `A_top ≤ 2 * P * a`. `m` is the chain length, `k` is the initial rank, `b` is
the row unit and `b'` is the source slope bound. `B` and `N` are the per-lift budgets `B₀` and
`N_c`, and `X` is the extra colength `X''`. `La` is the logarithm of the reference weight times
the root discriminant. `D` is the inverse of the good-row fraction, `F` is the scaled frame
defect and `c` is the frame exponent `c_H`. `C` is the constant of the pointwise inequality.
The local names `E₇` and `U` are the source loss bound and the source spread bound.

The hypotheses are the size conditions of the chain; `hlarge` is the large-scale threshold,
saying that `x ^ ε` dominates the constants `C` and `c`. -/
theorem thetaChainErrorBudget_le {x ε c C P A_top a b b' m k La B N X D F : ℝ}
    (hx : 0 ≤ x) (hc : 0 ≤ c) (hC : 0 ≤ C) (hP : 1 ≤ P) (hb : 1 ≤ b) (hba : b ≤ a)
    (hm : 0 ≤ m) (hk : 0 < k) (hA_top : 0 ≤ A_top) (hBN : 0 ≤ B + N) (hN : 0 ≤ N)
    (hD₀ : 0 ≤ D) (hD : D ≤ 2) (hF : F ≤ 6)
    (hLa : La ≤ 2 * x ^ ε) (hlogk : Real.log k ≤ x ^ ε) (hA : A_top ≤ 2 * P * a)
    (hmb : m * b ≤ a) (hmk : m ≤ k) (hb' : k * b' ≤ a) (hX : X ≤ a)
    (hlog : Real.log (1 + x ^ c) ≤ (1 + c) * x ^ ε)
    (hlarge : 200 * (1 + C) * (1 + c) ≤ x ^ ε) :
    let y := x ^ ε
    let E₇ := C * (P * m * b + P * m ^ 2 * (a / k + b') * y + X) + 1
    let U := C * P * a * La * (2 + m / k) + C * m * B + C * A_top * Real.log k + E₇
    C * A_top * (La + m ^ 2 * La / k) + C * P * a * La + C * m * (B + N) * y +
      C * m * B + C * P * a * La * (1 + m / k) + C * P * m * b + E₇ +
      D * 4 * Real.log (1 + x ^ c) * (U + b) + D * F * b ≤
      x ^ (3 * ε) * (P * a * (1 + m ^ 2 / k) + m * (B + N)) := by
  intro y E₇ U
  let A := P * a
  let R := A * (m ^ 2 / k)
  let T := m * (B + N)
  let E := A + R + T
  have ha₀ := zero_le_one.trans (hb.trans hba)
  have hPa : a ≤ A := le_mul_of_one_le_left ha₀ hP
  have hA₁ := hb.trans (hba.trans hPa)
  have hA₀ := zero_le_one.trans hA₁
  have hR₀ : 0 ≤ R := by dsimp only [R]; positivity
  have hT₀ : 0 ≤ T := by dsimp only [T]; positivity
  have hE : A ≤ E := by dsimp only [E]; linarith
  have hy : 1 ≤ y := by
    have h : 1 ≤ (1 + C) * (1 + c) := one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    linarith only [h, hlarge]
  have hy₀ := zero_le_one.trans hy
  have hmk' : m / k ≤ 1 := (div_le_one hk).mpr hmk
  have hsize (j : ℝ) (hj : 0 ≤ j) : C * P * a * La * (j + m / k) ≤
      C * P * a * (2 * y) * (j + 1) := by gcongr
  have htop : A_top * Real.log k ≤ (2 * P * a) * y :=
    (mul_le_mul_of_nonneg_left hlogk hA_top).trans (mul_le_mul_of_nonneg_right hA hy₀)
  have htype : C * m * B ≤ C * T := by
    linarith only [mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (a := B) hN)
      (mul_nonneg hC hm)]
  have hloss : E₇ ≤ C * (2 * A + 2 * R * y) + 1 :=
    thetaChainSourceLoss_le (zero_le_one.trans hP) hk hC hy₀ hmb hb' hX hPa
  have hspread : U + b ≤ 12 * (1 + C) * y * E := by
    refine le_trans ?_ (thetaChainSlopeSpread_add_le hA₁ hR₀ hT₀ hC hy (hba.trans hPa) hloss)
    have h := hsize 2 (by norm_num)
    dsimp only [U, A]
    linarith only [h, mul_le_mul_of_nonneg_left htop hC, htype]
  have hE₀ := hA₀.trans hE
  have hframe := thetaChainFrameErrors_le hx hC hy₀ hE₀ (zero_le_one.trans hb)
    (hba.trans (hPa.trans hE)) hD₀ hD hF hlog hspread
  have hrank : C * A_top * (La + m ^ 2 * La / k) ≤ 4 * C * y * (A + R) := by
    calc
      _ = C * A_top * La * (1 + m ^ 2 / k) := by ring
      _ ≤ _ := thetaChainRankError_le hC hA_top hy₀ (by positivity) hLa (by linarith only [hA])
  have hsource : C * P * a * La * (1 + m / k) ≤ 4 * C * y * A := by
    linarith only [hsize 1 (by norm_num)]
  have hdivide := mul_le_mul_of_nonneg_left hLa (show 0 ≤ C * P * a by positivity)
  have hgain : C * P * m * b ≤ C * A := by
    linarith only [mul_le_mul_of_nonneg_left hmb (show 0 ≤ C * P by positivity)]
  have htotal := thetaChainSubtotal_le hA₁ hR₀ hT₀ hC hy
  have hcoeff : (14 * (1 + C) * y + 96 * (1 + C) * (1 + c) * y ^ 2) * E ≤ y ^ 3 * E :=
    mul_le_mul_of_nonneg_right (thetaChainBudget_absorb hC hc hlarge) hE₀
  have hpow : x ^ (3 * ε) = y ^ 3 := by rw [mul_comm, Real.rpow_mul hx]; norm_cast
  rw [hpow]
  dsimp only [E, A, R, T] at hrank hdivide htype hsource hgain hloss hframe htotal hcoeff
  linarith only [hrank, hdivide, htype, hsource, hgain, hloss, hframe, htotal, hcoeff]

end TauCeti
