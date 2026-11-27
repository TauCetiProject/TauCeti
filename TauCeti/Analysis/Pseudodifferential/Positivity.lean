/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.Pseudodifferential.Recovery
public import TauCeti.Analysis.Pseudodifferential.StrictlyPositive
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical.Basic
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
(`TauCeti.ClassicalSymbol.isPositive_coefficient_principal`). The same holds for the pairing
`∫ w(x) ⟪Op(a) u (x), u (x)⟫ dx` weighted by a function `w` that is continuous on `U`, at the
points where `w` is positive; `w` can be the density of a measure read in a chart
(`TauCeti.ClassicalSymbol.isPositive_coefficient_principal_of_weight`). Where the principal symbol
is moreover invertible, it is strictly positive
(`TauCeti.ClassicalSymbol.isStrictlyPositive_coefficient_principal`); for an elliptic `a` this
holds at every nonzero frequency
(`TauCeti.ClassicalSymbol.IsElliptic.isStrictlyPositive_coefficient_principal`). When `Op(a)` is
positive on all compactly supported Schwartz functions, the principal symbol is therefore a
strictly positive homogeneous symbol
(`TauCeti.ClassicalSymbol.IsElliptic.isStrictlyPositive_principal`), and for finite-dimensional
`H` its real powers `σ(a) ^ z` are again homogeneous symbols (`TauCeti.HomogeneousSymbol.rpow`).

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

/-- **A positive operator has a positive principal symbol, for a weighted pairing.** Let `a` be a
classical symbol of order `m` with values in the endomorphisms of a complex Hilbert space `H`,
`U` an open set of positions and `w` a weight that is continuous on `U`, such as the density of a
measure. If `Op(a)` is positive on the compactly supported Schwartz functions supported in `U` for
the weighted pairing, `0 ≤ ∫ w(x) ⟪Op(a) u (x), u (x)⟫ dx` (a real nonnegative number), then its
principal symbol `σ(a)(x, ξ)` is a positive operator on `H` at every `x ∈ U` where `w` is positive,
and every frequency `ξ`. -/
theorem isPositive_coefficient_principal_of_weight (a : ClassicalSymbol n H H m)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) {w : CoordinateSpace n → ℝ}
    (hw : ContinuousOn w U)
    (ha : ∀ u : 𝓢(CoordinateSpace n, H), HasCompactSupport u → tsupport u ⊆ U →
      0 ≤ ∫ x, w x • ⟪quantizeSchwartzValue a.toSymbol.coefficient u x, u x⟫_ℂ)
    {x : CoordinateSpace n} (hx : x ∈ U) (hwx : 0 < w x) (ξ : CoordinateSpace n) :
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
  -- The weighted pairing `w ⟪σ(a) v, v⟫` is nonnegative on `U`, and `w` is positive there.
  have hwσ : 0 ≤ w x • ⟪a.principal.coefficient (x, ξ) v, v⟫_ℂ := by
    refine nonneg_of_forall_integral_sq_smul_nonneg (μ := volume) hU
      (hw.smul ((hσ.clm_apply continuous_const).inner continuous_const).continuousOn)
      (fun ψ hψ hψc hψU ↦ ?_) hx
    -- Test on wave packets with the amplitude `ψ`, viewed as a complex Schwartz function.
    have hφ : HasCompactSupport (fun y ↦ (ψ y : ℂ)) := hψc.comp_left Complex.ofReal_zero
    set φ : 𝓢(CoordinateSpace n, ℂ) := hφ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hψ)
    have hφφ : ⇑φ = fun y ↦ (ψ y : ℂ) := funext (HasCompactSupport.toSchwartzMap_toFun _ _)
    have hφc : HasCompactSupport φ := hφφ ▸ hφ
    have hφU : tsupport φ ⊆ U := hφφ ▸ (tsupport_comp_subset Complex.ofReal_zero ψ).trans hψU
    have hlim := a.tendsto_integral_smul_inner_quantizeSchwartzValue_cutoffExponential hξ hφc hU
      hw hφU v
    have hφψ : ∀ y, (w y * ‖φ y‖ ^ 2) • ⟪a.principal.coefficient (y, ξ) v, v⟫_ℂ =
        ψ y ^ 2 • w y • ⟪a.principal.coefficient (y, ξ) v, v⟫_ℂ := fun y ↦ by
      simp only [hφφ, Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.real_smul,
        Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    simp_rw [hφψ] at hlim
    refine ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun t ht ↦ ?_)
    -- The wave packet `y ↦ exp(i ⟪y, t ξ⟫) φ(y) v` is supported where `φ` is.
    have hsupp : Function.support (φ.cutoffExponential 1 (t • ξ) v) ⊆ Function.support φ :=
      fun y hy h0 ↦ hy (by simp [SchwartzMap.cutoffExponential_apply φ one_ne_zero, h0])
    rw [Complex.real_smul]
    exact mul_nonneg (Complex.zero_le_real.2 (Real.rpow_pos_of_pos ht _).le)
      (ha _ (hφc.mono hsupp) ((closure_mono hsupp).trans hφU))
  exact nonneg_of_smul_nonneg_of_pos_left hwσ hwx

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
    (a.principal.coefficient (x, ξ)).IsPositive :=
  a.isPositive_coefficient_principal_of_weight hU continuousOn_const
    (fun u hu huU ↦ by simpa using ha u hu huU) hx one_pos ξ

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

/-- If `a` is an elliptic classical symbol with `0 ≤ ∫ ⟪Op(a) u (x), u (x)⟫ dx` for every compactly
supported Schwartz function `u`, then its principal symbol is a strictly positive homogeneous
symbol; in particular, when `H` is finite-dimensional, it has real powers
`HomogeneousSymbol.rpow`. -/
theorem IsElliptic.isStrictlyPositive_principal {a : ClassicalSymbol n H H m} (he : a.IsElliptic)
    (ha : ∀ u : 𝓢(CoordinateSpace n, H), HasCompactSupport u →
      0 ≤ ∫ x, ⟪quantizeSchwartzValue a.toSymbol.coefficient u x, u x⟫_ℂ) :
    a.principal.IsStrictlyPositive :=
  HomogeneousSymbol.isStrictlyPositive_iff.mpr fun _ _ hξ ↦
    he.isStrictlyPositive_coefficient_principal isOpen_univ (fun u hu _ ↦ ha u hu)
      (Set.mem_univ _) hξ

end Inner

end ClassicalSymbol

end TauCeti
