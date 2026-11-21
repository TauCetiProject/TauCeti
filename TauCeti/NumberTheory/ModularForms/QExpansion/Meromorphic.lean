/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import TauCeti.NumberTheory.ModularForms.QExpansion.BigO

/-!
# Cusp meromorphy, pole-order twisting, and descent from powers and period multiples

If the period-`h` cusp function of `f : ℍ → ℂ` is meromorphic at `0` with pole order at most
`k : ℕ`, then twisting `f` by `𝕢 h ^ k` produces a function whose cusp function is analytic at `0`
(`TauCeti.UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul`). Every function on `ℍ` admits
such a lower bound `-(k : ℤ)` on its cusp order
(`TauCeti.UpperHalfPlane.exists_neg_natCast_le_meromorphicOrderAt`). Consequently, cusp meromorphy
descends from any positive power `f ^ n`
(`TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_pow`) and from any positive period multiple
`d * h` (`TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_nat_mul`), without needing Laurent
series.

## Main declarations

* `TauCeti.UpperHalfPlane.neg_le_meromorphicOrderAt_cuspFunction_iff`: pole order at most `k`
  expressed as nonnegativity of the twisted cusp order.
* `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul`: twisting a cusp-meromorphic
  function by `𝕢 h ^ k` yields an analytic cusp function at `0`.
* `TauCeti.UpperHalfPlane.exists_neg_natCast_le_meromorphicOrderAt`: existence of a natural-number
  lower bound on the cusp pole order.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_pow`: cusp meromorphy descends from `f ^ n`
  (`0 < n`) to `f`.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_nat_mul`: cusp meromorphy descends from
  period `d * h` (`d ≠ 0`) to period `h`.
-/

public noncomputable section

open UpperHalfPlane Filter Topology Function
open scoped Manifold

namespace TauCeti.UpperHalfPlane

variable {h : ℝ} {f : ℍ → ℂ}

local notation "𝕢" => Function.Periodic.qParam

/-- The cusp function of `f` has a pole of order at most `k` at `0` exactly when twisting it by
`q ^ k` gives a nonnegative order. -/
theorem neg_le_meromorphicOrderAt_cuspFunction_iff {k : ℕ}
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 ↔
      0 ≤ meromorphicOrderAt (fun q ↦ q ^ k * cuspFunction h f q) 0 := by
  rw [meromorphicOrderAt_pow_mul_cuspFunction hf]
  cases meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    rw [WithTop.coe_le_coe, ← WithTop.coe_natCast, ← WithTop.coe_add, ← WithTop.coe_zero,
      WithTop.coe_le_coe]
    omega

/-- If the cusp function of `f` is meromorphic at `0` with a pole of order at most `k`, then the
cusp function of `𝕢 ^ k * f` is analytic at `0`. -/
theorem analyticAt_cuspFunction_qParam_pow_mul {k : ℕ}
    (hf : MeromorphicAt (cuspFunction h f) 0)
    (hk : ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0) :
    AnalyticAt ℂ (cuspFunction h (fun τ ↦ 𝕢 h τ ^ k * f τ)) 0 := by
  rcases le_or_gt h 0 with hh | hh
  · exact analyticAt_const.congr (cuspFunction_eventuallyEq_const_of_nonpos hh _).symm
  have hψ : MeromorphicAt (fun q ↦ q ^ k * cuspFunction h f q) 0 :=
    (analyticAt_id.pow k).meromorphicAt.mul hf
  have han := hψ.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.mp
    ((neg_le_meromorphicOrderAt_cuspFunction_iff hf).mp hk)
  refine han.congr (cuspFunction_eventuallyEq_nhds_of_continuousAt ?_ han.continuousAt).symm
  exact (cuspFunction_qParam_pow_mul_eventuallyEq hh k f).trans hψ.eq_nhdsNE_toMeromorphicNFAt

/-- For every function on `ℍ`, the meromorphic order of its cusp function at `0` is bounded below
by `-(k : ℤ)` for some `k : ℕ`. -/
theorem exists_neg_natCast_le_meromorphicOrderAt (h : ℝ) (f : ℍ → ℂ) :
    ∃ k : ℕ, ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 := by
  cases hn : meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe n => exact ⟨(-n).toNat, WithTop.coe_le_coe.mpr (by omega)⟩

/-- If `f` is holomorphic and `h`-periodic on `ℍ` (`h > 0`) and `f ^ n` (`n > 0`) has a meromorphic
cusp function at `0`, then so does `f`. -/
theorem meromorphicAt_cuspFunction_of_pow (hh : 0 < h) (hf : MDiff f)
    (hper : Periodic (f ∘ ofComplex) h) {n : ℕ} (hn : 0 < n)
    (hpow : MeromorphicAt (cuspFunction h (f ^ n)) 0) :
    MeromorphicAt (cuspFunction h f) 0 := by
  obtain ⟨k, hk⟩ := exists_neg_natCast_le_meromorphicOrderAt h (f ^ n)
  have htend_pow := tendsto_valueAtInfty hh
    ((hper.comp (· ^ n)).qParam_pow_mul_comp_ofComplex (f := f ^ n))
    (analyticAt_cuspFunction_qParam_pow_mul hpow hk)
  have hL : Tendsto ((fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ) ^ n) atImInfty
      (𝓝 ((0 : ℂ) ^ ((n - 1) * k) * valueAtInfty fun τ : ℍ ↦ 𝕢 h τ ^ k * (f ^ n) τ)) := by
    refine ((((continuous_pow ((n - 1) * k)).tendsto 0).comp
      (qParam_tendsto_atImInfty hh)).mul htend_pow).congr fun τ ↦ ?_
    simp only [Function.comp_apply, Pi.pow_apply, mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]
    exact congrArg (fun e ↦ 𝕢 h (τ : ℂ) ^ e * f τ ^ n)
      (by rw [← add_one_mul, Nat.sub_add_cancel (by omega : 1 ≤ n), mul_comm])
  exact meromorphicAt_cuspFunction_of_qParam_pow_mul_isBigO hh hf hper
    ((by rw [one_pow, Pi.one_def]; exact hL.isBigO_one ℝ :
      ((fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ) ^ n) =O[atImInfty] ((1 : ℍ → ℝ) ^ n)).of_pow hn.ne')

/-- **Period descent for cusp meromorphy.** A holomorphic `h`-periodic function (`h > 0`) whose
cusp function at period `d * h` (`d ≠ 0`) is meromorphic at `0` also has a meromorphic cusp
function at period `h`. -/
theorem meromorphicAt_cuspFunction_of_nat_mul (hh : 0 < h) (hf : MDiff f)
    (hper : Periodic (f ∘ ofComplex) h) {d : ℕ} [NeZero d]
    (hmer : MeromorphicAt (cuspFunction ((d : ℕ) * h) f) 0) :
    MeromorphicAt (cuspFunction h f) 0 := by
  obtain ⟨k, hk⟩ := exists_neg_natCast_le_meromorphicOrderAt ((d : ℕ) * h) f
  have hdk : ((-((d * k : ℕ) : ℤ)) : WithTop ℤ) ≤
      meromorphicOrderAt (cuspFunction ((d : ℕ) * h) f) 0 :=
    le_trans (WithTop.coe_le_coe.mpr
      (Int.neg_le_neg (Nat.cast_le.mpr (Nat.le_mul_of_pos_left k (NeZero.pos d))))) hk
  have hg_eq : (fun τ : ℍ ↦ 𝕢 ((d : ℕ) * h) τ ^ (d * k) * f τ) = fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ :=
    funext fun τ ↦ by simp only [pow_mul, TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne d)]
  exact meromorphicAt_cuspFunction_of_qParam_pow_mul_isBigO hh hf hper
    ((tendsto_valueAtInfty (mul_pos (Nat.cast_pos.mpr (NeZero.pos d)) hh)
      (by simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using
        hper.qParam_pow_mul_comp_ofComplex.nat_mul d)
      (hg_eq ▸ analyticAt_cuspFunction_qParam_pow_mul hmer hdk)).isBigO_one ℝ)

end TauCeti.UpperHalfPlane
