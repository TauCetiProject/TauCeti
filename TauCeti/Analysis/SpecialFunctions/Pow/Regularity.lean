/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.NormPow

/-!
# The sharp finite regularity of absolute powers

For `k < p < k + 1`, the function `x ↦ |x| ^ p` is not `C^(k+1)` at zero. This supplies
sharp obstructions to finite regularity for radial powers and their restrictions to real lines.

Positive regularity is read off from the derivative `p |x| ^ (p - 2) x` of `|x| ^ p` (Mathlib's
`hasDerivAt_abs_rpow`) and of the odd power `|x| ^ p x`, whose derivative is `(p + 1) |x| ^ p`
for `p > 1` (`TauCeti.hasDerivAt_abs_rpow_mul_self`). Differentiation thus alternates between the
even powers `|x| ^ p` and the odd powers `|x| ^ (p - 2) x`, lowering the exponent by one at each
step.
-/

public section

open Set Filter Topology Real
open scoped ContDiff

namespace TauCeti

/-- The odd power `|x| ^ p * x`, that is `sign(x) |x| ^ (p + 1)`, has derivative `(p + 1) |x| ^ p`,
for `p > 1`. -/
theorem hasDerivAt_abs_rpow_mul_self {p : ℝ} (hp : 1 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ p * x) ((p + 1) * |x| ^ p) x := by
  refine ((hasDerivAt_abs_rpow x hp).mul (hasDerivAt_id' x)).congr_deriv ?_
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow (by linarith : p ≠ 0)]
  · have h2 : |x| ^ (p - 2) * (x * x) = |x| ^ p := by
      rw [← abs_mul_abs_self x, ← sq, ← Real.rpow_two, ← Real.rpow_add (abs_pos.2 hx),
        sub_add_cancel]
    linear_combination p * h2

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
