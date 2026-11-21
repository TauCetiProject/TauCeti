/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.CuspCoordinate
public import TauCeti.Analysis.Complex.UpperHalfPlane.Growth
public import TauCeti.NumberTheory.ModularForms.QExpansion.Laurent

/-!
# Exponential growth at `i∞` and meromorphic cusp functions

Let `h > 0` and let `f` be an `h`-periodic function on the upper half-plane, holomorphic at all
sufficiently large heights. Its cusp function `UpperHalfPlane.cuspFunction h f`, the function of
`q = exp (2 π i τ / h)` attached to `f`, is meromorphic at `q = 0` exactly when `f` has at most
exponential growth `O(exp (C · Im τ))` as `Im τ → ∞`
(`TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_iff_exists_isBigO_exp`).

If `f = O(exp (C · Im τ))` and `n ≥ C h / (2 π)`, then `qⁿ f` is bounded at `i∞`, so its cusp
function has a removable singularity at `0`, and the cusp function of `f` is `q⁻ⁿ` times an
analytic function. Conversely, if the cusp function has a pole of order at most `n`, then the cusp
function of `qⁿ f` is analytic at `0`, so `qⁿ f` is bounded at `i∞`, which is the exponential bound
of rate `2 π n / h`. The growth condition is the one in the definition of weakly holomorphic
modular forms; this equivalence identifies it with meromorphy of the cusp germ in the local
parameter.

## Main results

* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_isBigO_exp`: exponential growth gives a
  meromorphic cusp function.
* `TauCeti.UpperHalfPlane.exists_isBigO_exp_of_meromorphicAt_cuspFunction`: a meromorphic cusp
  function gives exponential growth.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_iff_exists_isBigO_exp`: the equivalence.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, Graduate Texts in
  Mathematics 228, Springer, 2005, §1.1 and §2.4.
-/

public section

open UpperHalfPlane Filter Topology Function Asymptotics
open scoped Manifold

namespace TauCeti.UpperHalfPlane

variable {h : ℝ} {f : ℍ → ℂ}

local notation "𝕢" => Function.Periodic.qParam

/-- Twisting a periodic function by a power of the `q`-parameter keeps it periodic. -/
private theorem periodic_qParam_pow_mul (hper : Periodic (f ∘ ofComplex) h) (n : ℕ) :
    Periodic ((fun τ : ℍ ↦ 𝕢 h τ ^ n * f τ) ∘ ofComplex) h :=
  ((periodic_qParam_comp_ofComplex (h := h)).comp (· ^ n)).mul hper

/-- An `h`-periodic function, holomorphic sufficiently high, with exponential growth
`O(exp (C · Im τ))` at `i∞`, has a cusp function meromorphic at `q = 0`. -/
theorem meromorphicAt_cuspFunction_of_isBigO_exp (hh : 0 < h)
    (hper : Periodic (f ∘ ofComplex) h)
    (hhol : ∀ᶠ τ in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ) {C : ℝ}
    (hC : f =O[atImInfty] fun τ ↦ Real.exp (C * τ.im)) :
    MeromorphicAt (cuspFunction h f) 0 := by
  obtain ⟨n, hn⟩ := exists_nat_ge (C * h / (2 * Real.pi))
  have hrate : C ≤ 2 * Real.pi * ((n : ℤ) : ℝ) / h := by
    rw [div_le_iff₀ (by positivity)] at hn
    rw [Int.cast_natCast, le_div_iff₀ hh]
    linarith
  have hbound : f =O[atImInfty] fun τ ↦ Real.exp (2 * Real.pi * ((n : ℤ) : ℝ) * τ.im / h) :=
    (isBigO_exp_mul_im_of_le hrate hC).congr_right fun τ ↦ by ring_nf
  have hbdd : IsBoundedAtImInfty fun τ ↦ 𝕢 h τ ^ n * f τ := by
    simpa only [zpow_natCast] using (isBoundedAtImInfty_qParam_zpow_mul_iff h n).2 hbound
  have hhol' : ∀ᶠ τ in atImInfty,
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ 𝕢 h τ ^ n * f τ) τ := by
    filter_upwards [hhol] with τ hτ
    exact ((Periodic.differentiable_qParam.mdifferentiable.comp mdifferentiable_coe).pow n τ).mul
      hτ
  have han : AnalyticAt ℂ (cuspFunction h fun τ ↦ 𝕢 h τ ^ n * f τ) 0 :=
    analyticAt_cuspFunction_zero_of_eventually_mdifferentiableAt hh
      (periodic_qParam_pow_mul hper n) hhol' hbdd
  have heq : cuspFunction h f =ᶠ[𝓝[≠] 0]
      fun q ↦ (q ^ n)⁻¹ * cuspFunction h (fun τ ↦ 𝕢 h τ ^ n * f τ) q := by
    filter_upwards [cuspFunction_qParam_pow_mul_eventuallyEq hh n f, self_mem_nhdsWithin]
      with q hq hq0
    rw [hq, inv_mul_cancel_left₀ (pow_ne_zero n hq0)]
  exact ((analyticAt_id.pow n).meromorphicAt.inv.mul han.meromorphicAt).congr heq.symm

/-- An `h`-periodic function whose cusp function is meromorphic at `q = 0` has exponential
growth `O(exp (C · Im τ))` at `i∞`. If the pole has order at most `n`, any `C ≥ 2 π n / h`
works. -/
theorem exists_isBigO_exp_of_meromorphicAt_cuspFunction (hh : 0 < h)
    (hper : Periodic (f ∘ ofComplex) h) (hf : MeromorphicAt (cuspFunction h f) 0) :
    ∃ C : ℝ, f =O[atImInfty] fun τ ↦ Real.exp (C * τ.im) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      ((-n : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 := by
    cases meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
    | top => exact ⟨0, le_top⟩
    | coe m => exact ⟨(-m).toNat, WithTop.coe_le_coe.mpr (by omega)⟩
  have han := analyticAt_cuspFunction_qParam_pow_mul hf hn
  have hbdd : IsBoundedAtImInfty fun τ ↦ 𝕢 h τ ^ n * f τ := by
    refine ((han.continuousAt.tendsto.comp (qParam_tendsto_atImInfty hh)).isBigO_one ℝ).congr_left
      fun τ ↦ ?_
    exact eq_cuspFunction τ hh.ne' (periodic_qParam_pow_mul hper n)
  refine ⟨2 * Real.pi * n / h, ?_⟩
  have hbound := (isBoundedAtImInfty_qParam_zpow_mul_iff h n).1 (by simpa only [zpow_natCast])
  refine hbound.congr_right fun τ ↦ ?_
  rw [Int.cast_natCast, mul_div_right_comm]

/-- **Meromorphy at `i∞` is exponential growth.** An `h`-periodic function holomorphic at all
sufficiently large heights has a cusp function meromorphic at `q = 0` exactly when it grows at
most exponentially, as `O(exp (C · Im τ))` for some real `C`, when `Im τ → ∞`. -/
theorem meromorphicAt_cuspFunction_iff_exists_isBigO_exp (hh : 0 < h)
    (hper : Periodic (f ∘ ofComplex) h)
    (hhol : ∀ᶠ τ in atImInfty, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f τ) :
    MeromorphicAt (cuspFunction h f) 0 ↔
      ∃ C : ℝ, f =O[atImInfty] fun τ ↦ Real.exp (C * τ.im) :=
  ⟨exists_isBigO_exp_of_meromorphicAt_cuspFunction hh hper, fun ⟨_, hC⟩ ↦
    meromorphicAt_cuspFunction_of_isBigO_exp hh hper hhol hC⟩

end TauCeti.UpperHalfPlane
