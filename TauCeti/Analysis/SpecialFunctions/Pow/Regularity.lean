/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Topology.MetricSpace.Holder

/-!
# The sharp finite regularity of absolute powers

For `k < p < k + 1`, the function `x ↦ |x| ^ p` is not `C^(k+1)` at zero. This supplies
sharp obstructions to finite regularity for radial powers and their restrictions to real lines.

Below that order the derivatives are explicit at every point, the origin included: the second and
third derivatives of `|x| ^ p` are `p (p - 1) |x| ^ (p - 2)` for `p > 2`
(`TauCeti.iteratedDeriv_two_abs_rpow`) and `p (p - 1) (p - 2) |x| ^ (p - 4) x` for `p > 3`
(`TauCeti.iteratedDeriv_three_abs_rpow`).

For `0 < β ≤ 1` the third derivative of `|x| ^ (3 + β)` is `β`-Hölder on all of `ℝ`
(`TauCeti.holderWith_iteratedFDeriv_three_abs_rpow_three_add`). For `p > 3` the third derivative of
`|x| ^ p` is `γ`-Hölder near the origin for no `γ > p - 3`
(`TauCeti.not_holderOnWith_iteratedFDeriv_three_abs_rpow`): `|x| ^ (3 + β)` is `C^{3,β}` near the
origin, and no better.
-/

public section

open Set Filter Topology Real
open scoped ContDiff NNReal

namespace TauCeti

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

/-- **The second derivative of `|x| ^ p`** is `p (p - 1) |x| ^ (p - 2)`, for `p > 2`. -/
theorem iteratedDeriv_two_abs_rpow {p : ℝ} (hp : 2 < p) :
    iteratedDeriv 2 (fun x : ℝ ↦ |x| ^ p) = fun x ↦ p * (p - 1) * |x| ^ (p - 2) := by
  have hd : deriv (fun x : ℝ ↦ |x| ^ p) = fun x ↦ p * (|x| ^ (p - 2) * x) := by
    funext x
    rw [(hasDerivAt_abs_rpow x (by linarith)).deriv, mul_assoc]
  -- The derivative of `|x| ^ q * x`, `q = p - 2 > 0`, is `|x| ^ q + q |x| ^ (q - 2) x²`, which is
  -- `(q + 1) |x| ^ q`.
  have hq : 0 < p - 2 := by linarith
  funext x
  have h := ((hasFDerivAt_norm_rpow_smul_self (E := ℝ) hq.le x).hasDerivAt).const_mul p
  simp only [Real.norm_eq_abs, smul_eq_mul] at h
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd, h.deriv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul, mul_one,
    RCLike.inner_apply, conj_trivial]
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow hq.ne']
  · have hsq : |x| ^ (p - 2 - 2) * (x * x) = |x| ^ (p - 2) := by
      rw [← abs_mul_abs_self x, ← sq, ← Real.rpow_natCast, ← Real.rpow_add (abs_pos.2 hx)]
      norm_num
    linear_combination p * (p - 2) * hsq

/-- **The third derivative of `|x| ^ p`** is `p (p - 1) (p - 2) |x| ^ (p - 4) x`, for `p > 3`. -/
theorem iteratedDeriv_three_abs_rpow {p : ℝ} (hp : 3 < p) :
    iteratedDeriv 3 (fun x : ℝ ↦ |x| ^ p) =
      fun x ↦ p * (p - 1) * (p - 2) * (|x| ^ (p - 4) * x) := by
  funext x
  rw [iteratedDeriv_succ, iteratedDeriv_two_abs_rpow (by linarith),
    ((hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).const_mul (p * (p - 1))).deriv]
  ring_nf

/-- For `0 < β ≤ 1`, the third derivative of `x ↦ |x| ^ (3 + β)`, which is
`(3 + β) (2 + β) (1 + β) |x| ^ (β - 1) x`, is `β`-Hölder on `ℝ`. -/
theorem holderWith_iteratedFDeriv_three_abs_rpow_three_add {β : ℝ≥0} (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) :
    HolderWith (2 * ((3 + β) * (2 + β) * (1 + β))) β
      (iteratedFDeriv ℝ 3 fun x : ℝ ↦ |x| ^ (3 + (β : ℝ))) := by
  have hβ : (0 : ℝ) < β := hβ0
  rw [iteratedFDeriv_eq_equiv_comp, (LinearIsometryEquiv.isometry _).holderWith_comp_iff,
    iteratedDeriv_three_abs_rpow (by linarith)]
  have h := (holderWith_abs_rpow_sub_one_mul_self hβ0 hβ1).smul
    (((3 + β) * (2 + β) * (1 + β) : ℝ≥0) : ℝ)
  rw [NNReal.nnNorm_eq] at h
  convert h using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat,
    NNReal.coe_one]
  rw [show (3 + (β : ℝ)) - 4 = β - 1 by ring]
  ring

/-- For `p > 3` and `γ > p - 3`, the third derivative of `x ↦ |x| ^ p` is not `γ`-Hölder on any
neighbourhood of the origin, whatever the constant: it vanishes at the origin and equals
`p (p - 1) (p - 2) x ^ (p - 3)` for `x > 0`. -/
theorem not_holderOnWith_iteratedFDeriv_three_abs_rpow {p : ℝ} (hp : 3 < p) {γ C : ℝ≥0}
    (hγ : p - 3 < γ) {s : Set ℝ} (hs : s ∈ 𝓝 0) :
    ¬ HolderOnWith C γ (iteratedFDeriv ℝ 3 fun x : ℝ ↦ |x| ^ p) s := by
  intro hH
  have hγp : (0 : ℝ) < γ - (p - 3) := sub_pos.2 hγ
  set c : ℝ := p * (p - 1) * (p - 2)
  have hc0 : 0 < c := by
    have : 0 < p - 2 := by linarith
    have : 0 < p - 1 := by linarith
    positivity
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  -- At `t > 0` the third derivative is `c t ^ (p - 3)`, and at the origin it is `0`.
  have hD (t : ℝ) (ht : 0 < t) :
      iteratedDeriv 3 (fun x : ℝ ↦ |x| ^ p) t = c * t ^ (p - 3) := by
    rw [iteratedDeriv_three_abs_rpow hp, show p - 4 = p - 3 - 1 by ring]
    dsimp only
    rw [abs_of_pos ht, ← Real.rpow_eq_rpow_sub_one_mul ht.le (by linarith)]
  have hD0 : iteratedDeriv 3 (fun x : ℝ ↦ |x| ^ p) 0 = 0 := by
    simp [iteratedDeriv_three_abs_rpow hp]
  have hdist (t : ℝ) (ht : 0 < t) :
      dist (iteratedFDeriv ℝ 3 (fun x : ℝ ↦ |x| ^ p) t)
        (iteratedFDeriv ℝ 3 (fun x : ℝ ↦ |x| ^ p) 0) = c * t ^ (p - 3) := by
    simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.dist_map,
      hD t ht, hD0, dist_zero_right, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  -- So the Hölder bound against the origin reads `c t ^ (p - 3) ≤ C t ^ γ`, false for small `t`.
  obtain ⟨t, hCt, ht⟩ := ((eventually_mul_rpow_lt_nhdsGT_zero hγp C hc0).and
    (Ioo_mem_nhdsGT hε)).exists
  have hts : t ∈ s := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht.1]; exact ht.2)
  have hd := hH.dist_le hts (mem_of_mem_nhds hs)
  rw [hdist t ht.1, Real.dist_eq, sub_zero, abs_of_pos ht.1] at hd
  have hsplit : t ^ (γ : ℝ) = t ^ ((γ : ℝ) - (p - 3)) * t ^ (p - 3) := by
    rw [← Real.rpow_add ht.1, sub_add_cancel]
  rw [hsplit, ← mul_assoc] at hd
  linarith [mul_lt_mul_of_pos_right hCt (Real.rpow_pos_of_pos ht.1 (p - 3))]

end TauCeti
