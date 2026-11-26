/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Kernel
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.SlitPlane

/-!
# The incomplete beta kernel at vertical neighbours

For vertical neighbours `v` and `v + (0, 1)` the integrand of the incomplete beta kernel
`K_ξ(v₁; v₂) = (2πi)⁻¹ ∫ (1 - z)^(y₁ - y₂) z^(x₂ - x₁ - 1) dz` has an elementary primitive, so the
kernel is explicit.

* Going up, `K_ξ(v; v + (0, 1)) = (2πi)⁻¹ ∫ dz / (z (1 - z))`, along a path crossing the real axis
  in `(-∞, 0)`. The primitive `log (-z) - log (1 - z)` is holomorphic off `[0, ∞)`, which is
  star-convex about `-1`, so `K_ξ(v; v + (0, 1)) = (arg (-ξ) - arg (1 - ξ)) / π` for `ξ` off
  `[0, ∞)` (`TauCeti.incompleteBetaKernel_add_snd_one`). At `ξ = ξ(s, t)` this is
  `-(1 - s - t)`.
* Going down, `K_ξ(v + (0, 1); v) = (2πi)⁻¹ ∫ (1 - z) / z dz`, along a path crossing in `(0, 1)`,
  with primitive `log z - z` on the slit plane. So `K_ξ(v + (0, 1); v) = (arg ξ - Im ξ) / π`
  (`TauCeti.incompleteBetaKernel_add_snd_one_left`), which is `s - Im ξ / π` at `ξ = ξ(s, t)`.

## Main results

* `TauCeti.incompleteBetaKernel_add_snd_one`,
  `TauCeti.incompleteBetaKernel_complexSlope_add_snd_one`: the kernel from `v` to the point above
  it.
* `TauCeti.incompleteBetaKernel_add_snd_one_left`,
  `TauCeti.incompleteBetaKernel_complexSlope_add_snd_one_left`: the kernel from `v + (0, 1)` down
  to `v`.
-/

public section

open Complex Set
open scoped Real ComplexConjugate

namespace TauCeti

/-- **The incomplete beta kernel going up.** For `ξ` off `[0, ∞)`,
`K_ξ(v; v + (0, 1)) = (arg (-ξ) - arg (1 - ξ)) / π`. The integrand is `1 / (z (1 - z))`, with
primitive `log (-z) - log (1 - z)` off `[0, ∞)`, a region star-convex about the point `-1` where
the defining path crosses the real axis. -/
theorem incompleteBetaKernel_add_snd_one {ξ : ℂ} (hξ : -ξ ∈ slitPlane) (v : ℤ × ℤ) :
    incompleteBetaKernel ξ v (v + (0, 1)) = ((arg (-ξ) - arg (1 - ξ)) / π : ℝ) := by
  have h1S {z : ℂ} (hz : -z ∈ slitPlane) : 1 - z ∈ slitPlane := by
    simpa [sub_eq_add_neg] using ofReal_add_mem_slitPlane hz zero_le_one
  have h0 {z : ℂ} (hz : -z ∈ slitPlane) : z ≠ 0 := fun h => slitPlane_ne_zero hz (by simp [h])
  have h1 {z : ℂ} (hz : -z ∈ slitPlane) : 1 - z ≠ 0 := slitPlane_ne_zero (h1S hz)
  have hint := curveIntegral_conj_neg_one_add_eq_sub
    (F := fun z => log (-z) - log (1 - z)) (f := fun z => (1 - z) ^ (-1 : ℤ) * z ^ (-1 : ℤ))
    hξ (fun z hz => ?_) ?_
  · simp only [incompleteBetaKernel_def, Prod.fst_add, Prod.snd_add, add_zero, sub_add_cancel_left,
      sub_self, zero_sub]
    have hc : (if v.2 + 1 ≤ v.2 then (1 / 2 : ℂ) else -1) = -1 := by simp
    rw [hc, hint]
    have e₁ : log (-conj ξ) = conj (log (-ξ)) := by
      rw [← map_neg, log_conj _ (mem_slitPlane_iff_arg.1 hξ).1]
    have e₂ : log (1 - conj ξ) = conj (log (1 - ξ)) := by
      rw [show (1 : ℂ) - conj ξ = conj (1 - ξ) by simp,
        log_conj _ (mem_slitPlane_iff_arg.1 (h1S hξ)).1]
    rw [e₁, e₂, sub_sub_sub_comm, sub_conj, sub_conj, log_im, log_im]
    push_cast
    field_simp
  · convert ((hasDerivAt_neg z).clog hz).sub
      (((hasDerivAt_id' z).const_sub 1).clog (h1S hz)) using 1
    have := h0 hz
    have := h1 hz
    rw [zpow_neg_one, zpow_neg_one]
    field_simp
    ring
  · exact ((continuousOn_const.sub continuousOn_id).zpow₀ (-1) fun z hz => Or.inl (h1 hz)).mul
      (continuousOn_id.zpow₀ (-1) fun z hz => Or.inl (h0 hz))

/-- At the complex slope, the kernel going up is `K_ξ(v; v + (0, 1)) = -(1 - s - t)`. -/
theorem incompleteBetaKernel_complexSlope_add_snd_one {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t < 1) (v : ℤ × ℤ) :
    incompleteBetaKernel (complexSlope s t) v (v + (0, 1)) = ((-(1 - s - t) : ℝ) : ℂ) := by
  have hξ := im_complexSlope_pos hs ht hst
  rw [incompleteBetaKernel_add_snd_one (mem_slitPlane_iff.2 (Or.inr (by simpa using hξ.ne'))),
    arg_neg_eq_arg_sub_pi_of_im_pos hξ, arg_complexSlope hs ht hst,
    arg_one_sub_complexSlope hs ht hst]
  congr 1
  field_simp
  ring

/-- **The incomplete beta kernel going down.** For `ξ` in the slit plane,
`K_ξ(v + (0, 1); v) = (arg ξ - Im ξ) / π`. The integrand is `(1 - z) / z`, with primitive
`log z - z` on the slit plane. -/
theorem incompleteBetaKernel_add_snd_one_left {ξ : ℂ} (hξ : ξ ∈ slitPlane) (v : ℤ × ℤ) :
    incompleteBetaKernel ξ (v + (0, 1)) v = ((arg ξ - ξ.im) / π : ℝ) := by
  have hint := curveIntegral_conj_half_add_eq_sub
    (F := fun z => log z - z) (f := fun z => (1 - z) ^ (1 : ℤ) * z ^ (-1 : ℤ))
    hξ (fun z hz => ?_) ?_
  · simp only [incompleteBetaKernel_def, Prod.fst_add, Prod.snd_add, add_zero, add_sub_cancel_left,
      sub_self, zero_sub]
    have hc : (if v.2 ≤ v.2 + 1 then (1 / 2 : ℂ) else -1) = 1 / 2 := by simp
    rw [hc, hint, log_conj ξ (mem_slitPlane_iff_arg.1 hξ).1, sub_sub_sub_comm, sub_conj, sub_conj,
      log_im]
    push_cast
    field_simp
  · have := slitPlane_ne_zero hz
    convert ((hasDerivAt_id' z).clog hz).sub (hasDerivAt_id' z) using 1
    rw [zpow_one, zpow_neg_one]
    field_simp
  · exact ((continuousOn_const.sub continuousOn_id).zpow₀ 1 fun _ _ => Or.inr zero_le_one).mul
      (continuousOn_id.zpow₀ (-1) fun z hz => Or.inl (slitPlane_ne_zero hz))

/-- At the complex slope, the kernel going down is `K_ξ(v + (0, 1); v) = s - Im ξ / π`. -/
theorem incompleteBetaKernel_complexSlope_add_snd_one_left {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s + t < 1) (v : ℤ × ℤ) :
    incompleteBetaKernel (complexSlope s t) (v + (0, 1)) v =
      ((s - (complexSlope s t).im / π : ℝ) : ℂ) := by
  have hξ := im_complexSlope_pos hs ht hst
  rw [incompleteBetaKernel_add_snd_one_left (mem_slitPlane_iff.2 (Or.inr hξ.ne')),
    arg_complexSlope hs ht hst]
  congr 1
  field_simp

end TauCeti
