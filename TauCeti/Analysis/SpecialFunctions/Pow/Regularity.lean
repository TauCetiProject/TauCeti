/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Basic.Real.Sign
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.InnerProductSpace.NormPow
import TauCeti.Basic.Real.Sign

/-!
# The sharp finite regularity of absolute powers

For `k < p`, the function `x ↦ |x| ^ p` is `C^k` (`TauCeti.contDiff_abs_rpow`), and for
`k < p < k + 1` it is not `C^(k+1)` at zero (`TauCeti.not_contDiffAt_abs_rpow`). This supplies
sharp obstructions to finite regularity for radial powers and their restrictions to real lines.

The derivatives are computed through the signed powers `|x|^r sgn(x)^j`, continuous for `r > 0`
(`TauCeti.continuous_abs_rpow_mul_sign_pow`) and, for `r > 1`, with derivative
`r |x|^(r - 1) sgn(x)^(j + 1)` everywhere (`TauCeti.hasDerivAt_abs_rpow_mul_sign_pow`), so that
`D^j |x|^p = p (p - 1) ⋯ (p - j + 1) |x|^(p - j) sgn(x)^j` for `j < p`
(`TauCeti.iteratedDeriv_abs_rpow`). Away from the origin the sign is locally constant
(`Real.eventually_sign_eq_nhds`).
-/

public section

open Set Filter Topology Real
open scoped ContDiff

namespace Real

/-- Away from the origin the real sign function is locally constant. -/
theorem eventually_sign_eq_nhds {x : ℝ} (hx : x ≠ 0) : ∀ᶠ y in 𝓝 x, sign y = sign x := by
  rcases hx.lt_or_gt with h | h
  · filter_upwards [Iio_mem_nhds h] with y hy
    rw [sign_of_neg hy, sign_of_neg h]
  · filter_upwards [Ioi_mem_nhds h] with y hy
    rw [sign_of_pos hy, sign_of_pos h]

end Real

namespace TauCeti

/-! ### Signed powers and the derivatives of `|x|^p` -/

/-- The signed power `|x|^r sgn(x)^j` is at most `|x|^r` in absolute value. -/
theorem abs_abs_rpow_mul_sign_pow_le {r : ℝ} (j : ℕ) (x : ℝ) :
    |(|x| ^ r * Real.sign x ^ j)| ≤ |x| ^ r := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) r)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (abs_nonneg x) r) (Real.abs_sign_pow_le_one x j)

/-- `|x|^(r - 2) x = |x|^(r - 1) sgn(x)`. -/
private theorem abs_rpow_sub_two_mul (r x : ℝ) :
    |x| ^ (r - 2) * x = |x| ^ (r - 1) * Real.sign x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.sign_zero]
  · -- `Real.rpow_add_one` peels a factor `|x|` off an exponent of the form `a + 1`, so the
    -- exponent `r - 1` is first written in that form, as `(r - 2) + 1`.
    rw [show r - 1 = r - 2 + 1 by ring, Real.rpow_add_one (abs_pos.2 hx).ne', mul_assoc,
      Real.abs_mul_sign]

/-- For `r > 1`, the signed power `|x|^r sgn(x)^j` is differentiable everywhere, with derivative
`r |x|^(r - 1) sgn(x)^(j + 1)`. At the origin both sides vanish, since `|x|^r = o(x)`. -/
theorem hasDerivAt_abs_rpow_mul_sign_pow {r : ℝ} (hr : 1 < r) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ |y| ^ r * Real.sign y ^ j)
      (r * (|x| ^ (r - 1) * Real.sign x ^ (j + 1))) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : r * (|(0 : ℝ)| ^ (r - 1) * Real.sign 0 ^ (j + 1)) = 0 := by simp [Real.sign_zero]
    rw [h0, hasDerivAt_iff_isLittleO]
    have hd := (hasDerivAt_abs_rpow (0 : ℝ) hr).hasFDerivAt.isLittleO
    have hr0 : r ≠ 0 := by linarith
    simp only [abs_zero, Real.zero_rpow hr0, sub_zero, mul_zero, zero_mul, smul_zero,
      ContinuousLinearMap.toSpanSingleton_apply] at hd ⊢
    refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1
      (Eventually.of_forall fun y ↦ ?_)) hd
    simpa only [Real.norm_eq_abs, one_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) r)]
      using abs_abs_rpow_mul_sign_pow_le (r := r) j y
  · have hd := (hasDerivAt_abs_rpow x hr).mul_const (Real.sign x ^ j)
    have heq : (fun y : ℝ ↦ |y| ^ r * Real.sign y ^ j) =ᶠ[𝓝 x]
        fun y ↦ |y| ^ r * Real.sign x ^ j := by
      filter_upwards [Real.eventually_sign_eq_nhds hx] with y hy
      rw [hy]
    refine (hd.congr_of_eventuallyEq heq).congr_deriv ?_
    rw [mul_assoc r, abs_rpow_sub_two_mul, pow_succ]
    ring

/-- For `r > 0`, the signed power `|x|^r sgn(x)^j` is continuous. -/
theorem continuous_abs_rpow_mul_sign_pow {r : ℝ} (hr : 0 < r) (j : ℕ) :
    Continuous fun x : ℝ ↦ |x| ^ r * Real.sign x ^ j := by
  have hpow : Continuous fun x : ℝ ↦ |x| ^ r :=
    continuous_abs.rpow_const fun _ ↦ Or.inr hr.le
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · have h0 : |(0 : ℝ)| ^ r * Real.sign 0 ^ j = 0 := by simp [Real.zero_rpow hr.ne']
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (a := fun y ↦ |y| ^ r) (fun y ↦ ?_) ?_
    · rw [Real.norm_eq_abs]
      exact abs_abs_rpow_mul_sign_pow_le j y
    · simpa [Real.zero_rpow hr.ne'] using hpow.tendsto 0
  · refine (hpow.mul (continuous_const (y := Real.sign x ^ j))).continuousAt.congr ?_
    filter_upwards [Real.eventually_sign_eq_nhds hx] with y hy
    rw [hy]
    rfl

/-- For `j < p`, the `j`-th derivative of `|x|^p` is `p (p - 1) ⋯ (p - j + 1) |x|^(p - j) sgn(x)^j`,
the falling factorial being `(descPochhammer ℝ j).eval p`. -/
theorem iteratedDeriv_abs_rpow {p : ℝ} {j : ℕ} (hj : (j : ℝ) < p) :
    iteratedDeriv j (fun x : ℝ ↦ |x| ^ p) =
      fun x ↦ (descPochhammer ℝ j).eval p * (|x| ^ (p - j) * Real.sign x ^ j) := by
  induction j with
  | zero => funext x; simp
  | succ j ih =>
    push_cast at hj
    rw [iteratedDeriv_succ, ih (by linarith)]
    funext x
    rw [((hasDerivAt_abs_rpow_mul_sign_pow (by linarith) j x).const_mul _).deriv,
      descPochhammer_succ_eval]
    push_cast
    rw [sub_sub]
    ring

/-- For `k < p`, the function `|x|^p` is `C^k`. -/
theorem contDiff_abs_rpow {k : ℕ} {p : ℝ} (hk : (k : ℝ) < p) :
    ContDiff ℝ k (fun x : ℝ ↦ |x| ^ p) := by
  rw [contDiff_nat_iff_iteratedDeriv]
  refine ⟨fun m hm ↦ ?_, fun m hm ↦ ?_⟩
  · have hmp : (m : ℝ) < p := lt_of_le_of_lt (by exact_mod_cast hm) hk
    rw [iteratedDeriv_abs_rpow hmp]
    exact continuous_const.mul (continuous_abs_rpow_mul_sign_pow (by linarith) m)
  · have hmk : ((m + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hm
    push_cast at hmk
    rw [iteratedDeriv_abs_rpow (by linarith)]
    exact fun x ↦
      ((hasDerivAt_abs_rpow_mul_sign_pow (by linarith) m x).const_mul _).differentiableAt

/-! ### The obstruction at the next order -/

/-- A nonintegral absolute power fails to have the next order of continuous differentiability
at the origin. -/
theorem not_contDiffAt_abs_rpow {k : ℕ} {p : ℝ} (hkp : (k : ℝ) < p)
    (hpk : p < k + 1) :
    ¬ ContDiffAt ℝ (k + 1) (fun x : ℝ ↦ |x| ^ p) 0 := by
  -- On the positive half-line the native derivative formula has a nonzero Pochhammer
  -- coefficient and a negative power, contradicting continuity of the highest derivative.
  intro h
  obtain ⟨s, hs, hfs⟩ := h.contDiffOn le_rfl (by simp)
  obtain ⟨u, hus, hu, h0u⟩ := mem_nhds_iff.mp hs
  have hc : ContinuousOn (iteratedDeriv (k + 1) (fun x : ℝ ↦ |x| ^ p)) u :=
    ((hfs.mono hus).continuousOn_iteratedDerivWithin le_rfl hu.uniqueDiffOn).congr
      (fun x hx ↦ (iteratedDerivWithin_of_isOpen hu hx).symm)
  have hlim := (hc.continuousAt (hu.mem_nhds h0u)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have heq : ∀ x > 0, iteratedDeriv (k + 1) (fun x : ℝ ↦ |x| ^ p) x =
      (descPochhammer ℝ (k + 1)).eval p * x ^ (p - (k + 1)) := by
    intro x hx
    have he : (fun t : ℝ ↦ |t| ^ p) =ᶠ[𝓝 x] (fun t : ℝ ↦ t ^ p) := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      rw [abs_of_pos ht]
    rw [iteratedDeriv_eq_iteratedFDeriv, (he.iteratedFDeriv ℝ (k + 1)).eq_of_nhds,
      ← iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iterate, iter_deriv_rpow_const]
    simp only [Nat.cast_add, Nat.cast_one]
  have hpos : 0 < (descPochhammer ℝ (k + 1)).eval p :=
    descPochhammer_pos (by simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hkp)
  have htop : Tendsto (fun x : ℝ ↦
      (descPochhammer ℝ (k + 1)).eval p * x ^ (p - (k + 1))) (𝓝[>] 0) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith)).const_mul_atTop hpos
  apply not_tendsto_nhds_of_tendsto_atTop htop _
  exact hlim.congr' (eventually_mem_nhdsWithin.mono fun x hx ↦ heq x hx)

end TauCeti
