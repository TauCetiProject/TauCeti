/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.Pow.Holder
import TauCeti.Topology.MetricSpace.Holder

/-!
# The sharp finite regularity of absolute powers

For `k < p < k + 1`, the function `x ↦ |x| ^ p` is not `C^(k+1)` at zero. This supplies
sharp obstructions to finite regularity for radial powers and their restrictions to real lines.

Positive regularity is read off from the derivative `p |x| ^ (p - 2) x` of `|x| ^ p` (Mathlib's
`hasDerivAt_abs_rpow`) and of the odd power `|x| ^ p x`, whose derivative is `(p + 1) |x| ^ p`
for `p ≥ 0` (`TauCeti.hasDerivAt_abs_rpow_mul_self`). Differentiation thus alternates between the
even powers `|x| ^ p` and the odd powers `|x| ^ (p - 2) x`, lowering the exponent by one at each
step. For `p > 3` the third derivative is `p (p - 1) (p - 2) |x| ^ (p - 4) x`
(`TauCeti.iteratedDeriv_three_abs_rpow`, and `TauCeti.iteratedFDeriv_three_abs_rpow_three_add` for
`p = 3 + β`); for `0 < β ≤ 1` it is `β`-Hölder on the whole line
(`TauCeti.memHolder_iteratedFDeriv_abs_rpow_three_add`).
-/

public section

open Set Filter Topology Real
open scoped ContDiff NNReal

namespace TauCeti

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
