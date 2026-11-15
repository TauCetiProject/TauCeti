/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.Pseudodifferential.Recovery
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
import TauCeti.Analysis.Distribution.AELeOfIntegral

/-!
# Positive operators have positive principal symbols

A pseudodifferential operator `Op(a)` with a classical symbol `a` of order `m` is tested on
high-frequency wave packets

`u_t(y) = exp(i ⟪y, t ξ⟫) φ(y) v`, `t → ∞`,

with a fixed amplitude `φ`, frequency direction `ξ ≠ 0` and vector `v`. For a compactly supported
amplitude the rescaled pairings converge,

`t ^ (-m) ∫ ⟪Op(a) u_t (x), u_t (x)⟫ dx → ∫ |φ(x)|² ⟪σ(a)(x, ξ) v, v⟫ dx`,

where `σ(a)` is the principal symbol
(`TauCeti.ClassicalSymbol.tendsto_integral_inner_quantizeSchwartzValue_cutoffExponential`, in
`TauCeti.Analysis.Pseudodifferential.Recovery`).

If `Op(a)` is positive on the compactly supported Schwartz functions supported in an open set
`U`, that is `0 ≤ ∫ ⟪Op(a) u, u⟫` there (a complex number that is real and nonnegative), then
these limits are nonnegative for every amplitude supported in `U`. Concentrating the amplitude
near a point shows that the principal symbol is a positive operator on the fibre at every
position of `U` and every frequency
(`TauCeti.ClassicalSymbol.isPositive_coefficient_principal`). Where the principal symbol is
moreover invertible, it is strictly positive
(`TauCeti.ClassicalSymbol.isStrictlyPositive_coefficient_principal`); for an elliptic `a` this
holds at every nonzero frequency
(`TauCeti.ClassicalSymbol.IsElliptic.isStrictlyPositive_coefficient_principal`). This is the
positivity under which the powers `σ(a)(x, ξ) ^ z` of the principal symbol of a positive
elliptic operator are defined by the continuous functional calculus.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators acting on rapidly oscillating functions `exp(i t ⟪y, ξ⟫) φ(y)`).
-/

public section

open scoped FourierTransform SchwartzMap InnerProductSpace RealInnerProductSpace ComplexOrder
  ContDiff
open MeasureTheory Real FourierTransform Filter Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {m : ℝ}

namespace ClassicalSymbol

section Inner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **A positive operator has a positive principal symbol.** Let `a` be a classical symbol of
order `m` with values in the endomorphisms of a complex Hilbert space `H`, and `U` an open set of
positions. If `Op(a)` is positive on the compactly supported Schwartz functions supported in `U`,
`0 ≤ ∫ ⟪Op(a) u (x), u (x)⟫ dx` (a real nonnegative number), then its principal symbol
`σ(a)(x, ξ)` is a positive operator on `H` at every `x ∈ U` and every frequency `ξ`. -/
theorem isPositive_coefficient_principal (a : ClassicalSymbol n H H m)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (ha : ∀ u : 𝓢(CoordinateSpace n, H), HasCompactSupport u → tsupport u ⊆ U →
      0 ≤ ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient u x, u x⟫_ℂ)
    {x : CoordinateSpace n} (hx : x ∈ U) (ξ : CoordinateSpace n) :
    (a.principal.coefficient (x, ξ)).IsPositive := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [a.principal.zero_covector]
    exact ContinuousLinearMap.isPositive_zero
  refine (ContinuousLinearMap.isPositive_iff_complex _).2 fun v ↦ ?_
  suffices h : 0 ≤ ⟪a.principal.coefficient (x, ξ) v, v⟫_ℂ from
    ⟨(Complex.eq_re_of_ofReal_le (r := 0) (by simpa using h)).symm, (Complex.nonneg_iff.1 h).1⟩
  have hσ : Continuous fun y ↦ a.principal.coefficient (y, ξ) :=
    a.principal.contDiffOn_coefficient.continuousOn.comp_continuous
      (continuous_id.prodMk continuous_const) fun _ ↦ hξ
  refine nonneg_of_forall_integral_sq_smul_nonneg (μ := volume) hU
    ((hσ.clm_apply continuous_const).inner continuous_const).continuousOn (fun ψ hψ hψc hψU ↦ ?_) hx
  -- Test on wave packets with the amplitude `ψ`, viewed as a complex Schwartz function.
  have hφ : HasCompactSupport (fun y ↦ (ψ y : ℂ)) := hψc.comp_left Complex.ofReal_zero
  set φ : 𝓢(CoordinateSpace n, ℂ) := hφ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hψ)
  have hφφ : ⇑φ = fun y ↦ (ψ y : ℂ) := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
  have hφc : HasCompactSupport φ := hφφ ▸ hφ
  have hφU : tsupport φ ⊆ U := hφφ ▸ (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψU
  have hlim := a.tendsto_integral_inner_quantizeSchwartzValue_cutoffExponential hξ hφc v
  have hφψ : ∀ y, ‖φ y‖ ^ 2 = ψ y ^ 2 := fun y ↦ by simp [hφφ, sq_abs]
  simp_rw [hφψ] at hlim
  refine ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht ↦ ?_)
  -- The wave packet `y ↦ exp(i ⟪y, t ξ⟫) φ(y) v` is supported where `φ` is.
  have hsupp : Function.support (φ.cutoffExponential 1 (t • ξ) v) ⊆ Function.support φ :=
    fun y hy h0 ↦ hy (by simp [SchwartzMap.cutoffExponential_apply φ one_ne_zero, h0])
  rw [Complex.real_smul]
  exact mul_nonneg (Complex.zero_le_real.2 (Real.rpow_pos_of_pos ht _).le)
    (ha _ (hφc.mono hsupp) ((closure_mono hsupp).trans hφU))

/-- **A positive operator has a strictly positive principal symbol where it is invertible.** Let
`a` be a classical symbol of order `m` with values in the endomorphisms of a complex Hilbert space
`H`, and `U` an open set of positions. If `Op(a)` is positive on the compactly supported Schwartz
functions supported in `U`, `0 ≤ ∫ ⟪Op(a) u (x), u (x)⟫ dx`, then its principal symbol
`σ(a)(x, ξ)` is strictly positive at every `x ∈ U` and every frequency `ξ` where it is
invertible. -/
theorem isStrictlyPositive_coefficient_principal (a : ClassicalSymbol n H H m)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (ha : ∀ u : 𝓢(CoordinateSpace n, H), HasCompactSupport u → tsupport u ⊆ U →
      0 ≤ ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient u x, u x⟫_ℂ)
    {x : CoordinateSpace n} (hx : x ∈ U) {ξ : CoordinateSpace n}
    (hinv : (a.principal.coefficient (x, ξ)).IsInvertible) :
    IsStrictlyPositive (a.principal.coefficient (x, ξ)) := by
  obtain ⟨e, hee⟩ := hinv
  refine IsUnit.isStrictlyPositive ?_ (ContinuousLinearMap.nonneg_iff_isPositive.2
    (a.isPositive_coefficient_principal hU ha hx ξ))
  rw [← hee]
  exact e.toUnit.isUnit

/-- **A positive elliptic operator has a strictly positive principal symbol.** Let `a` be an
elliptic classical symbol of order `m` with values in the endomorphisms of a complex Hilbert space
`H`, and `U` an open set of positions. If `0 ≤ ∫ ⟪Op(a) u (x), u (x)⟫ dx` for every compactly
supported Schwartz function `u` supported in `U`, then its principal symbol `σ(a)(x, ξ)` is
strictly positive at every `x ∈ U` and every nonzero frequency `ξ`. -/
theorem IsElliptic.isStrictlyPositive_coefficient_principal {a : ClassicalSymbol n H H m}
    (he : a.IsElliptic) {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (ha : ∀ u : 𝓢(CoordinateSpace n, H), HasCompactSupport u → tsupport u ⊆ U →
      0 ≤ ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient u x, u x⟫_ℂ)
    {x : CoordinateSpace n} (hx : x ∈ U) {ξ : CoordinateSpace n} (hξ : ξ ≠ 0) :
    IsStrictlyPositive (a.principal.coefficient (x, ξ)) :=
  a.isStrictlyPositive_coefficient_principal hU ha hx (isElliptic_iff.1 he x ξ hξ)

end Inner

end ClassicalSymbol

end TauCeti
