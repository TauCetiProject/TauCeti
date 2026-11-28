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
(`TauCeti.UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul`); in particular, a meromorphic
cusp function is analytic at `0` iff its order at `0` is nonnegative
(`TauCeti.UpperHalfPlane.meromorphicOrderAt_cuspFunction_nonneg_iff_analyticAt`). Every function on
`ℍ` admits such a canonical pole-order bound `-(cuspPoleOrder h f : ℤ)` on its cusp order
(`TauCeti.UpperHalfPlane.neg_cuspPoleOrder_le`,
`TauCeti.UpperHalfPlane.exists_neg_le_meromorphicOrderAt_cuspFunction`). Consequently, cusp
meromorphy descends from any positive power `f ^ n`
(`TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_pow`) and from any positive period multiple
`d * h` (`TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_nat_mul`), without needing Laurent
series.

## Main declarations

* `TauCeti.UpperHalfPlane.neg_le_meromorphicOrderAt_cuspFunction_iff`: pole order at most `k`
  expressed as nonnegativity of the twisted cusp order.
* `TauCeti.UpperHalfPlane.analyticAt_cuspFunction_qParam_pow_mul`: twisting a cusp-meromorphic
  function by `𝕢 h ^ k` yields an analytic cusp function at `0`.
* `TauCeti.UpperHalfPlane.meromorphicOrderAt_cuspFunction_nonneg_iff_analyticAt`: a meromorphic
  cusp function is analytic at `0` iff its meromorphic order at `0` is nonnegative.
* `TauCeti.UpperHalfPlane.cuspPoleOrder`, `TauCeti.UpperHalfPlane.cuspPoleOrder_def`,
  `TauCeti.UpperHalfPlane.cuspPoleOrder_congr`, `TauCeti.UpperHalfPlane.cuspPoleOrder_le_iff`,
  `TauCeti.UpperHalfPlane.cuspPoleOrder_eq_zero_of_analyticAt`,
  `TauCeti.UpperHalfPlane.neg_cuspPoleOrder_le`, and
  `TauCeti.UpperHalfPlane.exists_neg_le_meromorphicOrderAt_cuspFunction`: the canonical
  pole order at `i∞`, its characterizing lemmas, and lower bound on the cusp order.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_pow`: cusp meromorphy descends from `f ^ n`
  (`0 < n`) to `f`.
* `TauCeti.UpperHalfPlane.meromorphicAt_cuspFunction_of_nat_mul`: cusp meromorphy descends from
  period `d * h` (`d ≠ 0`) to period `h`.
* `TauCeti.UpperHalfPlane.meromorphicOrderAt_cuspFunction_pow`,
  `TauCeti.UpperHalfPlane.meromorphicOrderAt_cuspFunction_zpow`,
  `TauCeti.UpperHalfPlane.meromorphicOrderAt_cuspFunction_prod`: cusp-order formulas for powers,
  integer powers, and finite products.
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

/-- A meromorphic cusp function is analytic at `0` if and only if its meromorphic order at `0` is
nonnegative. -/
theorem meromorphicOrderAt_cuspFunction_nonneg_iff_analyticAt
    (hf : MeromorphicAt (cuspFunction h f) 0) :
    0 ≤ meromorphicOrderAt (cuspFunction h f) 0 ↔ AnalyticAt ℂ (cuspFunction h f) 0 :=
  ⟨fun h0 ↦ by simpa using analyticAt_cuspFunction_qParam_pow_mul hf (k := 0) (by simpa using h0),
    fun han ↦ han.meromorphicOrderAt_nonneg⟩

/-- The pole order of `f` at `i∞`, as a natural number: the order of the pole at `0` of the cusp
function of `f`, and `0` if there is no pole. -/
def cuspPoleOrder (h : ℝ) (f : ℍ → ℂ) : ℕ :=
  (-(meromorphicOrderAt (cuspFunction h f) 0).untop₀).toNat

/-- Defining formula for `cuspPoleOrder`. -/
theorem cuspPoleOrder_def (h : ℝ) (f : ℍ → ℂ) :
    cuspPoleOrder h f = (-(meromorphicOrderAt (cuspFunction h f) 0).untop₀).toNat :=
  (rfl)

/-- The pole order only depends on the cusp function off `q = 0`. -/
theorem cuspPoleOrder_congr {g : ℍ → ℂ} (hfg : cuspFunction h f =ᶠ[𝓝[≠] 0] cuspFunction h g) :
    cuspPoleOrder h f = cuspPoleOrder h g := by
  simp only [cuspPoleOrder, meromorphicOrderAt_congr hfg]

/-- The pole order of `f` at `i∞` is at most `k` if and only if the cusp order of `f` at `0` is
at least `-k`. -/
theorem cuspPoleOrder_le_iff {k : ℕ} :
    cuspPoleOrder h f ≤ k ↔
      ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 := by
  cases hn : meromorphicOrderAt (cuspFunction h f) 0 using WithTop.recTopCoe with
  | top => simp [cuspPoleOrder, hn]
  | coe n =>
    simp only [cuspPoleOrder, hn, WithTop.untop₀_coe, Int.toNat_le, WithTop.coe_le_coe]
    omega

/-- When the cusp function of `f` is analytic at `0`, the pole order at `i∞` is `0`. -/
theorem cuspPoleOrder_eq_zero_of_analyticAt (hf : AnalyticAt ℂ (cuspFunction h f) 0) :
    cuspPoleOrder h f = 0 :=
  Nat.le_zero.mp (cuspPoleOrder_le_iff.mpr (by simpa using hf.meromorphicOrderAt_nonneg))

/-- The pole order bounds the order of the cusp function from below. -/
theorem neg_cuspPoleOrder_le (h : ℝ) (f : ℍ → ℂ) :
    ((-(cuspPoleOrder h f : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 :=
  cuspPoleOrder_le_iff.mp le_rfl

/-- Some twisting exponent `k` bounds the order of the cusp function of `f` at `0` from below by
`-k`, so that `𝕢 ^ k * f` has an analytic cusp function when that of `f` is meromorphic. -/
theorem exists_neg_le_meromorphicOrderAt_cuspFunction (h : ℝ) (f : ℍ → ℂ) :
    ∃ k : ℕ, ((-k : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (cuspFunction h f) 0 :=
  ⟨cuspPoleOrder h f, neg_cuspPoleOrder_le h f⟩

/-- If `f` is holomorphic and `h`-periodic on `ℍ` (`h > 0`) and `f ^ n` (`n > 0`) has a meromorphic
cusp function at `0`, then so does `f`. -/
theorem meromorphicAt_cuspFunction_of_pow (hh : 0 < h) (hf : MDiff f)
    (hper : Periodic (f ∘ ofComplex) h) {n : ℕ} (hn : 0 < n)
    (hpow : MeromorphicAt (cuspFunction h (f ^ n)) 0) :
    MeromorphicAt (cuspFunction h f) 0 := by
  set k := cuspPoleOrder h (f ^ n)
  have hk := neg_cuspPoleOrder_le h (f ^ n)
  have htend_pow := tendsto_valueAtInfty hh
    (periodic_qParam_pow_mul_comp_ofComplex (hper.comp (· ^ n)) k)
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
  set k := cuspPoleOrder ((d : ℕ) * h) f
  have hk := neg_cuspPoleOrder_le ((d : ℕ) * h) f
  have hdk : ((-((d * k : ℕ) : ℤ)) : WithTop ℤ) ≤
      meromorphicOrderAt (cuspFunction ((d : ℕ) * h) f) 0 :=
    le_trans (WithTop.coe_le_coe.mpr
      (Int.neg_le_neg (Nat.cast_le.mpr (Nat.le_mul_of_pos_left k (NeZero.pos d))))) hk
  have hg_eq : (fun τ : ℍ ↦ 𝕢 ((d : ℕ) * h) τ ^ (d * k) * f τ) = fun τ : ℍ ↦ 𝕢 h τ ^ k * f τ :=
    funext fun τ ↦ by simp only [pow_mul, TauCeti.Periodic.qParam_nat_mul_pow (NeZero.ne d)]
  exact meromorphicAt_cuspFunction_of_qParam_pow_mul_isBigO hh hf hper
    ((tendsto_valueAtInfty (mul_pos (Nat.cast_pos.mpr (NeZero.pos d)) hh)
      (by simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using
        (periodic_qParam_pow_mul_comp_ofComplex hper k).nat_mul d)
      (hg_eq ▸ analyticAt_cuspFunction_qParam_pow_mul hmer hdk)).isBigO_one ℝ)

/-- The order at `0` of the cusp function of `f ^ n` is `n` times that of `f`. -/
theorem meromorphicOrderAt_cuspFunction_pow
    (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℕ) :
    meromorphicOrderAt (cuspFunction h (f ^ n)) 0 =
      n * meromorphicOrderAt (cuspFunction h f) 0 := by
  rw [Pi.pow_def, meromorphicOrderAt_congr (cuspFunction_map_eventuallyEq (· ^ n) f),
    fun_meromorphicOrderAt_pow hf]

/-- The order at `0` of the cusp function of `f ^ n` (`n : ℤ`) is `n` times that of `f`. -/
theorem meromorphicOrderAt_cuspFunction_zpow
    (hf : MeromorphicAt (cuspFunction h f) 0) (n : ℤ) :
    meromorphicOrderAt (cuspFunction h (f ^ n)) 0 =
      n * meromorphicOrderAt (cuspFunction h f) 0 := by
  rw [Pi.pow_def, meromorphicOrderAt_congr (cuspFunction_map_eventuallyEq (· ^ n) f),
    fun_meromorphicOrderAt_zpow hf]

/-- The order at `0` of the cusp function of a finite product is the sum of the cusp orders of
its factors. -/
theorem meromorphicOrderAt_cuspFunction_prod {ι : Type*} (s : Finset ι)
    {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, MeromorphicAt (cuspFunction h (f i)) 0) :
    meromorphicOrderAt (cuspFunction h (∏ i ∈ s, f i)) 0 =
      ∑ i ∈ s, meromorphicOrderAt (cuspFunction h (f i)) 0 := by
  rw [meromorphicOrderAt_congr (cuspFunction_prod_eventuallyEq s f),
    meromorphicOrderAt_fun_prod hf]

end TauCeti.UpperHalfPlane
