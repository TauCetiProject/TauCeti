/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.SpecialFunctions.Exp.Decay
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Examples of the order symbols (DLMF 2.1.4–2.1.9)

The order symbols `∼`, `o` and `O` of DLMF §2.1(i) are Mathlib's `Asymptotics.IsEquivalent`,
`Asymptotics.IsLittleO` and `Asymptotics.IsBigO`. This file records the examples that DLMF gives
for them, including the remark after 2.1.7 that `e^{-z} = o(1)` holds uniformly in a closed
sector `|ph z| ≤ π/2 - δ` with `δ > 0` but not in the open half-plane `|ph z| < π/2`.

The examples cite the general results. DLMF 2.1.4, `tanh z ∼ z` as `z → 0`, is
`TauCeti.isEquivalent_complexTanh` of `TauCeti.Analysis.SpecialFunctions.Hyperbolic`.
DLMF 2.1.5, `e^{-x} = o(1)` as `x → +∞`, is Mathlib's `Real.tendsto_exp_neg_atTop_nhds_zero`.
DLMF 2.1.6, `sin(πn + n⁻¹) = O(n⁻¹)` as `n → ±∞` in `ℤ`, follows from
`Int.abs_sin_pi_mul_intCast_add_le` of `TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds`.
The sector statements are `TauCeti.cexp_neg_isLittleO_one_sector` and
`TauCeti.not_cexp_neg_isLittleO_one_rightHalfPlane` of
`TauCeti.Analysis.SpecialFunctions.Exp.Decay`. DLMF 2.1.7, `e^{ix} = O(1)` on `ℝ`, is
`Complex.norm_exp_ofReal_mul_I`. DLMF 2.1.8, that the tail from index `n` of a power series
converging near `0` is `O(zⁿ)`, is `TauCeti.tsum_tail_isBigO_pow` of
`TauCeti.Analysis.Analytic.OfScalars`, recorded here for `𝕜 = ℂ`. DLMF 2.1.9,
`e^z = 1 + z + O(z²)` as `z → 0`, is the case `n = 2` of Mathlib's
`Complex.exp_sub_sum_range_isBigO_pow`.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/AsymptoticApproximations/Basics/OrderSymbols.lean`.
-/

public section

open Filter Asymptotics Complex
open scoped Topology Real

namespace TauCeti

/-- DLMF 2.1.4: `tanh z ∼ z` as `z → 0` in `ℂ`, the result `TauCeti.isEquivalent_complexTanh`. -/
example : (fun z : ℂ => tanh z) ~[𝓝 0] fun z => z :=
  isEquivalent_complexTanh

/-- DLMF 2.1.5: `e^{-x} = o(1)` as `x → +∞` in `ℝ`. -/
example : (fun x : ℝ => Real.exp (-x)) =o[atTop] fun _ => (1 : ℝ) :=
  (isLittleO_one_iff ℝ).mpr Real.tendsto_exp_neg_atTop_nhds_zero

/-- DLMF §2.1(i), after 2.1.7: `e^{-z} = o(1)` as `z → ∞` in the closed sector
`|ph z| ≤ π/2 - δ`, for every `δ > 0`, the result `TauCeti.cexp_neg_isLittleO_one_sector`. -/
example {δ : ℝ} (hδ : 0 < δ) :
    (fun z : ℂ => exp (-z)) =o[Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| ≤ π / 2 - δ}]
      fun _ => (1 : ℂ) :=
  cexp_neg_isLittleO_one_sector hδ

/-- DLMF §2.1(i), after 2.1.7: `e^{-z} = o(1)` fails as `z → ∞` in the open half-plane
`|ph z| < π/2`, the result `TauCeti.not_cexp_neg_isLittleO_one_rightHalfPlane`. -/
example :
    ¬ (fun z : ℂ => exp (-z)) =o[Bornology.cobounded ℂ ⊓ 𝓟 {z | |arg z| < π / 2}]
      fun _ => (1 : ℂ) :=
  not_cexp_neg_isLittleO_one_rightHalfPlane

/-- DLMF 2.1.6: `sin(πn + n⁻¹) = O(n⁻¹)` as `n → ±∞` in `ℤ`, with constant `1` for every `n` by
`Int.abs_sin_pi_mul_intCast_add_le`. -/
example : (fun n : ℤ => Real.sin (π * n + (n : ℝ)⁻¹)) =O[atTop ⊔ atBot] fun n => (n : ℝ)⁻¹ :=
  IsBigO.of_bound 1 (Eventually.of_forall fun n => by
    simpa [Real.norm_eq_abs] using n.abs_sin_pi_mul_intCast_add_le (n : ℝ)⁻¹)

/-- DLMF 2.1.7: `e^{ix} = O(1)` for `x ∈ ℝ`, on the whole real line (the filter `⊤`). -/
example : (fun x : ℝ => exp (x * I)) =O[⊤] fun _ => (1 : ℝ) :=
  isBigO_top.mpr ⟨1, fun x => by simp [norm_exp_ofReal_mul_I]⟩

/-- DLMF 2.1.8 over `ℂ`: if `∑ aₛ zˢ` converges for all sufficiently small `|z|`, then for each
`n`, `∑_{s ≥ n} aₛ zˢ = O(zⁿ)` as `z → 0`; the case `𝕜 = ℂ` of `TauCeti.tsum_tail_isBigO_pow`. -/
example {a : ℕ → ℂ} (ha : ∀ᶠ z in 𝓝 0, Summable fun s => a s * z ^ s) (n : ℕ) :
    (fun z : ℂ => ∑' s, a (s + n) * z ^ (s + n)) =O[𝓝 0] fun z => z ^ n :=
  tsum_tail_isBigO_pow ha n

/-- DLMF 2.1.9: `e^z = 1 + z + O(z²)` as `z → 0` in `ℂ`, the case `n = 2` of Mathlib's
`Complex.exp_sub_sum_range_isBigO_pow`. -/
example : (fun z : ℂ => exp z - 1 - z) =O[𝓝 0] fun z => z ^ 2 := by
  simpa [Finset.sum_range_succ, sub_sub] using Complex.exp_sub_sum_range_isBigO_pow 2

end TauCeti
