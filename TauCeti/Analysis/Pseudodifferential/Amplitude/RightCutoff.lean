/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Amplitude.Expansion

/-!
# Right quantizations cut off near the diagonal

Let `b` be a symbol of order `m` on `ℝⁿ`, with no support condition in the position and no
estimates uniform in the position. Its right quantization

`u ↦ (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) b(y, ξ) u(y) dy dξ`

has the amplitude `b(y, ξ)` (`TauCeti.Amplitude.ofRight`); formal adjoints of left quantizations
are of this form. Unless `b` has compact spatial support, in which case `TauCeti.Symbol.ofRight` is
its exact left symbol, this amplitude does not have proper input support, so
`TauCeti.Amplitude.leftSymbol` does not apply to it. Cutting its kernel off near the diagonal by
`χ(x - y)`, for a smooth compactly supported
`χ`, gives the amplitude `χ(x - y) b(y, ξ)` (`TauCeti.Amplitude.ofRightCutoff`), which has proper
input support. Its quantization

`u ↦ (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) χ(x - y) b(y, ξ) u(y) dy dξ`

is therefore the left quantization of a symbol `c` of order `m`, its left symbol. When `χ = 1` near
`0`, the terms of the expansion of `c` only see `b` near the diagonal, where the cutoff is `1`, so

`c ∼ ∑_k ((-i)^k / k!) ∑_{|w| = k} ∂_x^w ∂_ξ^w b = ∑_γ (1 / γ!) ∂_ξ^γ D_x^γ b`, `D_x = -i ∂_x`,

the expansion of the left symbol of a right quantization, with an actual remainder of order
`m - N` after `N` terms. Already when `χ 0 = 1`, `c - b` has order `m - 1`.

## Main declarations

* `TauCeti.Amplitude.ofRightCutoff χ hχ b`: the amplitude `χ(x - y) b(y, ξ)`, with proper input
  support when `χ` has compact support (`TauCeti.Amplitude.hasProperInputSupport_ofRightCutoff`).
* `TauCeti.Amplitude.quantizeSchwartzValue_leftSymbol_ofRightCutoff`: the quantization of its left
  symbol is the right quantization of `b` with kernel cut off by `χ(x - y)`.
* `TauCeti.Amplitude.leftTerm_ofRightCutoff`: for `χ = 1` near `0`, the terms of the expansion are
  those of `b(y, ξ)`, computed by `TauCeti.Amplitude.coefficient_leftTerm_ofRight`.
* `TauCeti.Amplitude.leftSymbol_ofRightCutoff_eq_sum_leftTerm_add_leftRemainder` and
  `TauCeti.Amplitude.isAsymptoticSum_leftSymbol_ofRightCutoff`: the expansion of the left symbol.
* `TauCeti.Amplitude.leftSymbol_ofRightCutoff_eq_add_leftRemainder_one`: the left symbol is `b` up
  to a symbol of order `m - 1`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Real FourierTransform Finset
open scoped ContDiff RealInnerProductSpace SchwartzMap Topology

namespace TauCeti

namespace Amplitude

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ} {χ : CoordinateSpace n → ℂ}

/-- The amplitude `χ(x - y) b(y, ξ)` of the right quantization of a symbol `b` with its kernel
cut off by `χ(x - y)`. For compactly supported `χ` it has proper input support
(`TauCeti.Amplitude.hasProperInputSupport_ofRightCutoff`), so it reduces to a left symbol. -/
def ofRightCutoff (χ : CoordinateSpace n → ℂ) (hχ : ContDiff ℝ ∞ χ) (b : Symbol n V W m) :
    Amplitude n V W m :=
  (ofRight b).smulPositions (fun p ↦ χ (p.1 - p.2)) (hχ.comp (contDiff_fst.sub contDiff_snd))

@[simp]
theorem coefficient_ofRightCutoff (hχ : ContDiff ℝ ∞ χ) (b : Symbol n V W m)
    (p : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n) :
    (ofRightCutoff χ hχ b).coefficient p = χ (p.1 - p.2.1) • b.coefficient p.2 := by
  simp [ofRightCutoff]

/-- For compactly supported `χ`, the amplitude `χ(x - y) b(y, ξ)` vanishes away from the diagonal,
so it has proper input support. -/
theorem hasProperInputSupport_ofRightCutoff (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (b : Symbol n V W m) : (ofRightCutoff χ hχ b).HasProperInputSupport := by
  obtain ⟨R, hR⟩ := hχs.isCompact.isBounded.subset_closedBall 0
  refine hasProperInputSupport_smulPositions_of_lt_dist _ (R := R) (fun x y hxy ↦ ?_) _
  refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
  have h := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at h
  exact (lt_irrefl _ (hxy.trans_le h))

/-- For `χ = 1` near `0`, the terms of the expansion of the left symbol of `χ(x - y) b(y, ξ)` are
those of `b(y, ξ)`: they only depend on the amplitude near the diagonal. -/
theorem leftTerm_ofRightCutoff (hχ : ContDiff ℝ ∞ χ) (hχ₁ : χ =ᶠ[𝓝 0] 1) (b : Symbol n V W m)
    (k : ℕ) : (ofRightCutoff χ hχ b).leftTerm k = (ofRight b).leftTerm k := by
  refine leftTerm_smulPositions _ (fun x ↦ ?_) _ k
  exact ((continuous_fst.sub continuous_snd).tendsto' (x, x) 0 (by simp)).eventually hχ₁

variable [CompleteSpace W]

/-- **The right quantization cut off near the diagonal is a left quantization.** For compactly
supported `χ`, the quantization of the left symbol of `χ(x - y) b(y, ξ)` at a Schwartz function `u`
is `(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) χ(x - y) b(y, ξ) u(y) dy dξ`, in the iterated form
`∫ exp(2πi ⟪ζ, x⟫) 𝓕(y ↦ χ(x - y) b(y, 2πζ) u(y))(ζ) dζ`. -/
theorem quantizeSchwartzValue_leftSymbol_ofRightCutoff [CompleteSpace V] (hχ : ContDiff ℝ ∞ χ)
    (hχs : HasCompactSupport χ) (b : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue ((ofRightCutoff χ hχ b).leftSymbol
        (hasProperInputSupport_ofRightCutoff hχ hχs b)).coefficient u x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ χ (x - y) • b.coefficient (y, (2 * π) • ζ) (u y)) ζ := by
  rw [quantizeSchwartzValue_leftSymbol, quantizeAmplitudeValue_def]
  simp only [coefficient_ofRightCutoff, smul_apply]

/-- **The expansion of the left symbol of a right quantization**, without compact spatial support.
For compactly supported `χ` with `χ = 1` near `0` and every `N`, the left symbol `c` of
`χ(x - y) b(y, ξ)` is `∑_{k < N} leftTerm (ofRight b) k` plus a symbol of order `m - N`, where
`leftTerm (ofRight b) k = ((-i)^k / k!) ∑_{|w| = k} ∂_x^w ∂_ξ^w b`
(`TauCeti.Amplitude.coefficient_leftTerm_ofRight`). -/
theorem leftSymbol_ofRightCutoff_eq_sum_leftTerm_add_leftRemainder (hχ : ContDiff ℝ ∞ χ)
    (hχs : HasCompactSupport χ) (hχ₁ : χ =ᶠ[𝓝 0] 1) (b : Symbol n V W m) (N : ℕ) :
    (ofRightCutoff χ hχ b).leftSymbol (hasProperInputSupport_ofRightCutoff hχ hχs b) =
      ∑ k ∈ range N,
          Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg k)) ((ofRight b).leftTerm k) +
        Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg N)) ((ofRightCutoff χ hχ b).leftRemainder
          (hasProperInputSupport_ofRightCutoff hχ hχs b) N) := by
  simp only [← leftTerm_ofRightCutoff hχ hχ₁ b]
  exact leftSymbol_eq_sum_leftTerm_add_leftRemainder _ N

/-- For compactly supported `χ` with `χ = 1` near `0`, the left symbol of `χ(x - y) b(y, ξ)` is an
asymptotic sum of the terms `leftTerm (ofRight b) k` of order `m - k`. -/
theorem isAsymptoticSum_leftSymbol_ofRightCutoff (hχ : ContDiff ℝ ∞ χ)
    (hχs : HasCompactSupport χ) (hχ₁ : χ =ᶠ[𝓝 0] 1) (b : Symbol n V W m) :
    (Symbol.inclusion (by simp)
      ((ofRightCutoff χ hχ b).leftSymbol (hasProperInputSupport_ofRightCutoff hχ hχs b)) :
        Symbol n V W (m - ((0 : ℕ) : ℝ))).IsAsymptoticSum (ofRight b).leftTerm := by
  simpa only [funext (leftTerm_ofRightCutoff hχ hχ₁ b)] using
    isAsymptoticSum_leftSymbol (hasProperInputSupport_ofRightCutoff hχ hχs b)

/-- For compactly supported `χ` with `χ 0 = 1`, the left symbol of `χ(x - y) b(y, ξ)` is `b` up to
a symbol of order `m - 1`. -/
theorem leftSymbol_ofRightCutoff_eq_add_leftRemainder_one (hχ : ContDiff ℝ ∞ χ)
    (hχs : HasCompactSupport χ) (hχ0 : χ 0 = 1) (b : Symbol n V W m) :
    (ofRightCutoff χ hχ b).leftSymbol (hasProperInputSupport_ofRightCutoff hχ hχs b) =
      b + Symbol.inclusion (by simp) ((ofRightCutoff χ hχ b).leftRemainder
        (hasProperInputSupport_ofRightCutoff hχ hχs b) 1) := by
  rw [leftSymbol_eq_diagonal_add_leftRemainder_one]
  congr 1
  ext1
  funext ⟨x, ξ⟩
  simp [hχ0]

end Amplitude

end TauCeti
