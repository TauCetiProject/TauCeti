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
public import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Holder
import TauCeti.Basic.Real.Sign
import TauCeti.Topology.Instances.Real.Sign
import TauCeti.Topology.MetricSpace.Holder

/-!
# The sharp finite regularity of absolute powers

For `k < p < k + 1`, the function `x ↦ |x| ^ p` is not `C^(k+1)` at zero
(`TauCeti.not_contDiffAt_abs_rpow`); that it is `C^k` is the case `E = ℝ` of
`TauCeti.contDiff_norm_rpow_of_lt`. This supplies sharp obstructions to finite regularity for
radial powers and their restrictions to real lines.

The derivatives are computed through the signed powers `|x|^r sgn(x)^j`, which for `r > 1` have
derivative `r |x|^(r - 1) sgn(x)^(j + 1)` everywhere (`TauCeti.hasDerivAt_abs_rpow_mul_sign_pow`),
so that `D^j |x|^p = p (p - 1) ⋯ (p - j + 1) |x|^(p - j) sgn(x)^j` for `j < p`
(`TauCeti.iteratedDeriv_abs_rpow`). Away from the origin the sign is locally constant
(`Real.eventually_sign_eq_nhds`), and the signed power is at most `|x|^r` in absolute value
(`TauCeti.abs_abs_rpow_mul_sign_pow_le`).

Positive regularity is also read off from the derivative `p |x| ^ (p - 2) x` of `|x| ^ p`
(Mathlib's `hasDerivAt_abs_rpow`) and of the odd power `|x| ^ p x`, whose derivative is
`(p + 1) |x| ^ p` for `p ≥ 0` (`TauCeti.hasDerivAt_abs_rpow_mul_self`). Differentiation thus
alternates between the even powers `|x| ^ p` and the odd powers `|x| ^ (p - 2) x`, lowering the
exponent by one at each step. For `p > 3` the third derivative is
`p (p - 1) (p - 2) |x| ^ (p - 4) x` (`TauCeti.iteratedDeriv_three_abs_rpow`, and
`TauCeti.iteratedFDeriv_three_abs_rpow_three_add` for `p = 3 + β`); for `0 < β ≤ 1` it is
`β`-Hölder on the whole line (`TauCeti.memHolder_iteratedFDeriv_abs_rpow_three_add`).
-/

public section

open Set Filter Topology Real
open scoped ContDiff NNReal

namespace TauCeti

/-! ### Signed powers and the derivatives of `|x|^p` -/

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

/-! ### Odd powers and the third derivative of `|x|^p` -/

/-- The odd power `|x| ^ p * x`, that is `sign(x) |x| ^ (p + 1)`, has derivative `(p + 1) |x| ^ p`,
for `p ≥ 0`. This is the line case of `TauCeti.hasFDerivAt_norm_rpow_smul_self`. -/
theorem hasDerivAt_abs_rpow_mul_self {p : ℝ} (hp : 0 ≤ p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ p * x) ((p + 1) * |x| ^ p) x := by
  have hd := (hasFDerivAt_norm_rpow_smul_self (E := ℝ) hp x).hasDerivAt
  simp only [Real.norm_eq_abs, smul_eq_mul] at hd
  refine hd.congr_deriv ?_
  rcases eq_or_ne x 0 with rfl | hx
  · rcases hp.eq_or_lt with rfl | hp
    · simp
    · simp [Real.zero_rpow hp.ne']
  · have h : |x| ^ (p - 2) * (x * x) = |x| ^ p := by
      rw [← abs_mul_abs_self, ← sq, ← Real.rpow_natCast, ← Real.rpow_add (abs_pos.2 hx)]
      norm_num
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one,
      ContinuousLinearMap.smulRight_apply, coe_innerSL_apply, RCLike.inner_apply, conj_trivial,
      one_mul]
    linear_combination p * h

/-- The third derivative of `|x| ^ p`, for `p > 3`, is the odd power
`p (p - 1) (p - 2) |x| ^ (p - 4) x`. -/
theorem iteratedDeriv_three_abs_rpow {p : ℝ} (hp : 3 < p) :
    iteratedDeriv 3 (fun x : ℝ ↦ |x| ^ p) =
      fun x ↦ p * (p - 1) * (p - 2) * (|x| ^ (p - 4) * x) := by
  have h1 : iteratedDeriv 1 (fun x : ℝ ↦ |x| ^ p) = fun x ↦ p * (|x| ^ (p - 2) * x) := by
    funext x
    rw [iteratedDeriv_one, (hasDerivAt_abs_rpow x (by linarith)).deriv, mul_assoc]
  have h2 : iteratedDeriv 2 (fun x : ℝ ↦ |x| ^ p) = fun x ↦ p * (p - 1) * |x| ^ (p - 2) := by
    funext x
    rw [iteratedDeriv_succ, h1,
      ((hasDerivAt_abs_rpow_mul_self (p := p - 2) (by linarith) x).const_mul p).deriv]
    ring
  funext x
  rw [iteratedDeriv_succ, h2,
    ((hasDerivAt_abs_rpow x (p := p - 2) (by linarith)).const_mul (p * (p - 1))).deriv,
    show p - 2 - 2 = p - 4 by ring]
  ring

/-- The third derivative of `|x| ^ (3 + β)`, for `β > 0`, is the odd power
`(3 + β) (2 + β) (1 + β) |x| ^ (β - 1) x`, read as a trilinear map. -/
theorem iteratedFDeriv_three_abs_rpow_three_add {β : ℝ} (hβ : 0 < β) :
    iteratedFDeriv ℝ 3 (fun x : ℝ ↦ |x| ^ (3 + β)) = fun x ↦
      ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 3) ℝ
        ((3 + β) * (2 + β) * (1 + β) * (|x| ^ (β - 1) * x)) := by
  rw [iteratedFDeriv_eq_equiv_comp, iteratedDeriv_three_abs_rpow (by linarith)]
  funext x
  rw [Function.comp_apply, show (3 : ℝ) + β - 4 = β - 1 by ring]
  congr 1
  ring

/-- The third derivative of `|x| ^ (3 + β)` is globally `β`-Hölder, for `0 < β ≤ 1`. -/
theorem memHolder_iteratedFDeriv_abs_rpow_three_add {β : ℝ≥0} (hβ₀ : 0 < β) (hβ₁ : β ≤ 1) :
    MemHolder β (iteratedFDeriv ℝ 3 (fun x : ℝ ↦ |x| ^ (3 + (β : ℝ)))) := by
  rw [iteratedFDeriv_three_abs_rpow_three_add (NNReal.coe_pos.2 hβ₀)]
  exact ⟨_, (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 3) ℝ).isometry.comp_holderWith
    ((Real.holderWith_abs_rpow_sub_one_mul_self hβ₀ hβ₁).smul
      ((3 + (β : ℝ)) * (2 + β) * (1 + β)))⟩

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
