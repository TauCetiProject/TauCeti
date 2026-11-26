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
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Holder
import TauCeti.Analysis.SpecialFunctions.Pow.PowSign
import TauCeti.Analysis.SpecialFunctions.Pow.Real
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
(`TauCeti.abs_abs_rpow_mul_sign_pow_le`, in `TauCeti.Analysis.SpecialFunctions.Pow.PowSign`).
For `p > 1`, Mathlib's derivative `p |x| ^ (p - 2) x` of `|x| ^ p` (`hasDerivAt_abs_rpow`) is the
signed power `p |x| ^ (p - 1) sgn(x)` (`Real.abs_rpow_sub_two_mul_eq_mul_sign`, ibid.).

For `0 < β ≤ 1` the `k`-th derivative of `|x| ^ (k + β)` is `β`-Hölder on the whole line, with an
explicit constant (`TauCeti.holderWith_iteratedFDeriv_abs_rpow`). For `p > k` the `k`-th derivative
of `|x| ^ p` is `γ`-Hölder near the origin for no `γ > p - k`
(`TauCeti.not_holderOnWith_iteratedFDeriv_abs_rpow`). So for `0 < β ≤ 1` the function
`|x| ^ (k + β)` is `C^{k,β}` near the origin, and its `k`-th derivative is `γ`-Hölder there for
no `γ > β`.

The odd power `|x| ^ p x` has derivative `(p + 1) |x| ^ p` for `p ≥ 0`
(`TauCeti.hasDerivAt_abs_rpow_mul_self`).
-/

public section

open Set Filter Topology Real
open scoped ContDiff NNReal

namespace TauCeti

/-! ### Signed powers and the derivatives of `|x|^p` -/

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
    rw [mul_assoc r, Real.abs_rpow_sub_two_mul_eq_mul_sign, pow_succ]
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

/-- For `0 < β ≤ 1`, the `k`-th derivative of `|x|^(k + β)`, which is
`(k + β) (k + β - 1) ⋯ (1 + β) |x|^β sgn(x)^k`, is `β`-Hölder on `ℝ`. -/
theorem holderWith_iteratedFDeriv_abs_rpow (k : ℕ) {β : ℝ≥0} (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    HolderWith (2 * ‖(descPochhammer ℝ k).eval ((k : ℝ) + β)‖₊) β
      (iteratedFDeriv ℝ k fun x : ℝ ↦ |x| ^ ((k : ℝ) + β)) := by
  have hkp : (k : ℝ) < k + β := lt_add_of_pos_right _ hβ0
  rw [iteratedFDeriv_eq_equiv_comp, iteratedDeriv_abs_rpow hkp, add_sub_cancel_left]
  exact (LinearIsometryEquiv.isometry _).comp_holderWith
    ((holderWith_abs_rpow_mul_sign_pow hβ1 k).smul ((descPochhammer ℝ k).eval ((k : ℝ) + β)))

/-! ### Odd powers -/

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

/-- For `p > k` and `γ > p - k`, the `k`-th derivative of `x ↦ |x| ^ p` is not `γ`-Hölder on any
neighbourhood of the origin, whatever the constant: it vanishes at the origin and equals
`p (p - 1) ⋯ (p - k + 1) x ^ (p - k)` for `x > 0`. -/
theorem not_holderOnWith_iteratedFDeriv_abs_rpow {k : ℕ} {p : ℝ} (hp : (k : ℝ) < p) {γ C : ℝ≥0}
    (hγ : p - k < γ) {s : Set ℝ} (hs : s ∈ 𝓝 0) :
    ¬ HolderOnWith C γ (iteratedFDeriv ℝ k fun x : ℝ ↦ |x| ^ p) s := by
  intro hH
  set c : ℝ := (descPochhammer ℝ k).eval p
  have hc0 : 0 < c := descPochhammer_pos (by linarith)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  -- At `t > 0` the `k`-th derivative is `c t ^ (p - k)`, and at the origin it is `0`.
  have hD (t : ℝ) (ht : 0 < t) :
      iteratedDeriv k (fun x : ℝ ↦ |x| ^ p) t = c * t ^ (p - k) := by
    rw [iteratedDeriv_abs_rpow hp]
    dsimp only
    rw [abs_of_pos ht, Real.sign_of_pos ht, one_pow, mul_one]
  have hD0 : iteratedDeriv k (fun x : ℝ ↦ |x| ^ p) 0 = 0 := by
    simp [iteratedDeriv_abs_rpow hp, Real.zero_rpow (sub_pos.2 hp).ne']
  have hdist (t : ℝ) (ht : 0 < t) :
      dist (iteratedFDeriv ℝ k (fun x : ℝ ↦ |x| ^ p) t)
        (iteratedFDeriv ℝ k (fun x : ℝ ↦ |x| ^ p) 0) = c * t ^ (p - k) := by
    simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.dist_map,
      hD t ht, hD0, dist_zero_right, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  -- So the Hölder bound against the origin reads `c t ^ (p - k) ≤ C t ^ γ`, false for small `t`.
  refine (not_le.2 hγ) (le_of_forall_mem_Ioc_rpow_le_mul_rpow (C := C / c) (half_pos hε)
    fun t ht ↦ ?_)
  have hts : t ∈ s := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]; linarith [ht.2])
  have hd := hH.dist_le hts (mem_of_mem_nhds hs)
  rw [hdist t ht.1, Real.dist_eq, sub_zero, abs_of_pos ht.1] at hd
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  linarith

end TauCeti
