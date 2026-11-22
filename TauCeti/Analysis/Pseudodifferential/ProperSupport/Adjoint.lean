/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Classical
public import TauCeti.Analysis.Pseudodifferential.Amplitude.RightCutoff
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Distribution
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Pseudodifferential.OutputSupport.Basic
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Function.L2Space.Basic

/-!
# The adjoint symbol of a properly supported pseudodifferential operator

Let `a` be a symbol of order `m` on `ℝⁿ` with values in operators between complex Hilbert spaces,
whose quantization `Op(a)` has kernel supported within distance `R` of the diagonal
(`TauCeti.Symbol.HasNearDiagonalKernel a R`). No estimate uniform in the position and no compact
spatial support is assumed. The formal adjoint `Op(a)*` of `Op(a)` on test functions
(`TauCeti.Symbol.adjointTestFunctionCLM`) is the right quantization

`Op(a)* φ (x) = (2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(y, ξ)† φ(y) dy dξ`

of the pointwise adjoint `a(y, ξ)†`. This file shows that it is again a left quantization, of a
symbol of order `m`, the **adjoint symbol** `a*` (`TauCeti.Symbol.properAdjoint`):

`∫ ⟪Op(a) u, φ⟫ = ∫ ⟪u, Op(a*) φ⟫` for all test functions `u` and `φ`.

The kernel of the right quantization is supported within distance `R` of the diagonal, so it does
not change when it is cut off by `χ(x - y)` for a cutoff `χ` equal to `1` near the closed ball of
radius `R`. The cut-off right quantization has an amplitude with proper input support, hence a left
symbol (`TauCeti.Amplitude.ofRightCutoff`), and that left symbol is `a*`
(`TauCeti.Symbol.properAdjoint_eq_leftSymbol_ofRightCutoff`). Its expansion is the adjoint
expansion of the compactly supported case,

`a* ∼ ∑ₖ ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†`,

with remainders of order `m - N` (`TauCeti.Symbol.isAsymptoticSum_properAdjoint`). For a classical
symbol `a`, the adjoint symbol is classical with principal symbol `a_m†`
(`TauCeti.ClassicalSymbol.properAdjoint`).

The adjoint symbol is determined by its defining identity
(`TauCeti.Symbol.eq_properAdjoint_iff`). Consequently it does not depend on the radius `R`, it is
again properly supported, with kernel within every distance larger than `R` of the diagonal
(`TauCeti.Symbol.HasNearDiagonalKernel.properAdjoint`), taking adjoint symbols is an involution
(`TauCeti.Symbol.properAdjoint_properAdjoint`), and for a symbol that also has compact spatial
support it is the adjoint symbol `TauCeti.Symbol.adjoint` given by Fourier transforms of the
position slices (`TauCeti.Symbol.properAdjoint_eq_adjoint`).

## Explicit adjoints of properly cut-off symbols

For an arbitrary local symbol `a` of real order `m`, `TauCeti.Symbol.adjointKernelCutoff a χ hχ`
is the left symbol of the proper-input amplitude `conj(χ(y-x)) a(y,ξ)†`. Its quantization is the
actual native continuous adjoint of `kernelCutoff χ a` on compactly supported smooth tests, also
between each compact stage `K` and its closed `R`-thickening. Coefficient Hilbert spaces may have
zero or infinite dimension, and no uniform position estimates on `a` are assumed.

All truncation remainders are the native amplitude remainders. A cutoff equal to one near zero
gives their complete expansion; equality with the adjoint of an already local original operator
uses a cutoff equal to one on its entire propagation ball. Spatial pairings use the original
Euclidean volume and the angular frequency `ξ = 2πζ`.

The proof uses rapid Fourier decay of the compact proper-input slices before frequency
Fubini. It never treats the arbitrary-order oscillatory kernel as an absolutely integrable
triple integral.

## Main declarations

* `TauCeti.Symbol.properAdjoint a ha`: the adjoint symbol of a symbol `a` with kernel near the
  diagonal; its quantization is the formal adjoint `TauCeti.Symbol.adjointTestFunctionCLM`
  (`TauCeti.Symbol.quantizeTestFunctionCLM_properAdjoint`).
* `TauCeti.Symbol.integral_inner_quantizeTestFunctionCLM_properAdjoint`: the adjoint identity.
* `TauCeti.Symbol.properAdjoint_eq_leftSymbol_ofRightCutoff`: the formula as the left symbol of the
  right quantization of `a†` cut off near the diagonal.
* `TauCeti.Symbol.isAsymptoticSum_properAdjoint`: the adjoint expansion.
* `TauCeti.ClassicalSymbol.properAdjoint`: the adjoint of a properly supported classical symbol,
  with `TauCeti.ClassicalSymbol.principal_properAdjoint` and
  `TauCeti.ClassicalSymbol.isElliptic_properAdjoint_iff`.
* `TauCeti.Symbol.adjointKernelCutoff a χ hχ`: the explicit adjoint symbol of a properly cut-off
  symbol, identified with `TauCeti.Symbol.properAdjoint` by
  `TauCeti.Symbol.properAdjoint_kernelCutoff_eq`, with
  `TauCeti.Symbol.adjointTestFunctionCLM_kernelCutoff` and
  `TauCeti.Symbol.isAsymptoticSum_adjointKernelCutoff`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I,
  (1.21)–(1.28) and (2.3).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Set TopologicalSpace Filter
open scoped SchwartzMap ContDiff Distributions RealInnerProductSpace Topology
open ContinuousLinearMap (adjointRealCLM adjointRealCLM_apply)

namespace TauCeti

/-! ### The terms of the expansion -/

namespace Amplitude

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m : ℝ}

/-- The terms of the expansion of the left symbol of the right quantization of the pointwise
adjoint `a(y, ξ)†` are the terms `((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of the adjoint
expansion. -/
theorem leftTerm_ofRight_map_adjointRealCLM (a : Symbol n V W m) (k : ℕ) :
    (ofRight (a.map adjointRealCLM)).leftTerm k = a.adjointTerm k := by
  refine Symbol.ext (funext fun ⟨x, ξ⟩ ↦ ?_)
  have h : (a.map adjointRealCLM).coefficient = adjointRealCLM ∘ a.coefficient :=
    funext (Symbol.coefficient_map adjointRealCLM a)
  rw [coefficient_leftTerm_ofRight, Symbol.coefficient_adjointTerm, h]
  simp only [adjointRealCLM.mixedDeriv_comp_left a.contDiff_coefficient, adjointRealCLM_apply]

end Amplitude

namespace Symbol

/-! ### Right quantizations cut off near the diagonal -/

section RightCutoff

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {m R : ℝ}

/-- If `χ` vanishes outside the ball of radius `R` about the origin, the right quantization of `b`
with kernel cut off by `χ(x - y)`, the quantization of the left symbol of the amplitude
`χ(x - y) b(y, ξ)`, has kernel supported within distance `R` of the diagonal. -/
theorem hasNearDiagonalKernel_leftSymbol_ofRightCutoff {χ : CoordinateSpace n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ) (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (b : Symbol n V W m) :
    ((Amplitude.ofRightCutoff χ hχ b).leftSymbol
      (Amplitude.hasProperInputSupport_ofRightCutoff hχ hχs b)).HasNearDiagonalKernel R := by
  refine hasNearDiagonalKernel_iff.2 fun u x hu ↦ ?_
  rw [Amplitude.quantizeSchwartzValue_leftSymbol_ofRightCutoff hχ hχs]
  -- The cut-off integrand `y ↦ χ(x - y) b(y, ξ) u(y)` vanishes identically.
  have h (ζ : CoordinateSpace n) :
      (fun y ↦ χ (x - y) • b.coefficient (y, (2 * π) • ζ) (u y)) = 0 := by
    funext y
    by_cases hy : y ∈ Metric.ball x R
    · simp [hu y hy]
    · have hχy : χ (x - y) = 0 := Function.notMem_support.1 fun h ↦
        hy (mem_ball_iff_norm'.2 (mem_ball_zero_iff.1 (hχR h)))
      simp [hχy]
  refine (integral_congr_ae (.of_forall fun ζ ↦ ?_)).trans (integral_zero _ _)
  simp [h ζ, Real.fourier_eq]

end RightCutoff

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}
  {a : Symbol n V W m}

/-! ### Auxiliary facts -/

section Auxiliary

/-- For `0 ≤ r < r'`, a smooth complex cutoff equal to `1` near the closed ball of radius `r` about
the origin and vanishing outside the ball of radius `r'`. -/
private theorem exists_cutoff_ball {r r' : ℝ} (hr : 0 ≤ r) (hrr' : r < r') :
    ∃ χ : CoordinateSpace n → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[𝓝ˢ (Metric.closedBall 0 r)] 1 ∧ Function.support χ ⊆ Metric.ball 0 r' := by
  -- A bump equal to `1` on the closed ball of radius `(r + r') / 2`.
  let b : ContDiffBump (0 : CoordinateSpace n) := ⟨(r + r') / 2, r', by linarith, by linarith⟩
  refine ⟨fun z ↦ (b z : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero,
    eventually_of_mem (Metric.isOpen_ball.mem_nhdsSet.2
      (Metric.closedBall_subset_ball (by linarith : r < (r + r') / 2))) fun z hz ↦ by
        simp [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz)],
    fun z hz ↦ ?_⟩
  rw [← b.support_eq]
  exact Function.support_comp_subset Complex.ofReal_zero _ hz

/-- For a cutoff `χ` equal to `1` near the closed ball of radius `r ≥ max R 0`, the right
quantization of the pointwise adjoint `a(y, ξ)†` cut off by `χ(x - y)` is the formal adjoint of
`Op(a)`: the part of the kernel removed by the cutoff vanishes, since the kernel of the formal
adjoint lies within distance `R` of the diagonal. -/
private theorem quantizeSchwartzValue_leftSymbol_ofRightCutoff_eq
    (ha : a.HasNearDiagonalKernel R) {χ : CoordinateSpace n → ℂ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : HasCompactSupport χ) {r : ℝ} (hRr : R ≤ r) (hr : 0 ≤ r)
    (hχ₁ : χ =ᶠ[𝓝ˢ (Metric.closedBall 0 r)] 1)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) (x : CoordinateSpace n) :
    quantizeSchwartzValue ((Amplitude.ofRightCutoff χ hχ (a.map adjointRealCLM)).leftSymbol
        (Amplitude.hasProperInputSupport_ofRightCutoff hχ hχs _)).coefficient
      (φ.hasCompactSupport.toSchwartzMap φ.contDiff) x = adjointTestFunctionCLM ha φ x := by
  -- The test function `ψ = χ(x - ·) φ`, on which the formal adjoint gives the left side at `x`.
  let ψ : 𝓓((⊤ : Opens (CoordinateSpace n)), W) :=
    ⟨fun y ↦ χ (x - y) • φ y, (hχ.comp (contDiff_const.sub contDiff_id)).smul φ.contDiff,
      φ.hasCompactSupport.smul_left, subset_univ _⟩
  have hψ : quantizeSchwartzValue ((Amplitude.ofRightCutoff χ hχ (a.map adjointRealCLM)).leftSymbol
        (Amplitude.hasProperInputSupport_ofRightCutoff hχ hχs _)).coefficient
      (φ.hasCompactSupport.toSchwartzMap φ.contDiff) x = adjointTestFunctionCLM ha ψ x := by
    rw [Amplitude.quantizeSchwartzValue_leftSymbol_ofRightCutoff hχ hχs,
      adjointTestFunctionCLM_apply]
    simp [ψ, adjointRealCLM_apply]
  -- `χ = 1` on a ball of radius `R' > R`.
  obtain ⟨U, hU, hrU, hUχ⟩ := mem_nhdsSet_iff_exists.1 hχ₁
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall 0 r).exists_thickening_subset_open hU hrU
  rw [thickening_closedBall hδ hr] at hδU
  set R' := δ + r
  have hR : R < R' := by linarith
  have hR' : 0 < R' := by linarith
  -- `φ - ψ` vanishes on the ball of radius `R'` about `x`, so the formal adjoint kills it at `x`.
  have hsupp : tsupport (φ - ψ) ⊆ {y | R' ≤ dist x y} := by
    refine closure_minimal (fun y hy ↦ ?_) (isClosed_le continuous_const
      (continuous_const.dist continuous_id))
    by_contra hlt
    refine hy ?_
    have hχy : χ (x - y) = 1 :=
      hUχ (hδU (mem_ball_zero_iff.2 ((dist_eq_norm x y).symm.trans_lt (lt_of_not_ge hlt))))
    simp [ψ, hχy]
  have hx : x ∉ tsupport (adjointTestFunctionCLM ha (φ - ψ)) := fun hx ↦ by
    obtain ⟨y, hy, hxy⟩ := Metric.mem_thickening_iff.1
      (Metric.cthickening_subset_thickening' hR' hR _
        (tsupport_adjointTestFunctionCLM_subset ha _ hx))
    exact (hsupp hy).not_gt hxy
  have h0 := image_eq_zero_of_notMem_tsupport hx
  rw [map_sub, sub_apply, sub_eq_zero] at h0
  rw [hψ, h0]

/-- The formal adjoint of `Op(a)` is the quantization of a symbol of order `m`, the left symbol of
the right quantization of `a†` cut off near the diagonal. -/
private theorem HasNearDiagonalKernel.exists_quantizeSchwartzValue_eq
    (ha : a.HasNearDiagonalKernel R) :
    ∃ c : Symbol n W V m, ∀ (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) (x : CoordinateSpace n),
      quantizeSchwartzValue c.coefficient (φ.hasCompactSupport.toSchwartzMap φ.contDiff) x =
        adjointTestFunctionCLM ha φ x := by
  obtain ⟨χ, hχ, hχs, hχ₁, -⟩ := exists_cutoff_ball (le_max_right R 0) (lt_add_one _)
  exact ⟨_, quantizeSchwartzValue_leftSymbol_ofRightCutoff_eq ha hχ hχs (le_max_left R 0)
    (le_max_right R 0) hχ₁⟩

end Auxiliary

/-! ### The adjoint symbol -/

section ProperAdjoint

/-- **The adjoint symbol of a properly supported operator.** For a symbol `a` of order `m` whose
quantization has kernel supported within distance `R` of the diagonal, the symbol `a*` of order
`m` whose quantization is the formal adjoint of `Op(a)` on test functions
(`TauCeti.Symbol.quantizeSchwartzValue_properAdjoint`), so that
`∫ ⟪Op(a) u, φ⟫ = ∫ ⟪u, Op(a*) φ⟫`
(`TauCeti.Symbol.integral_inner_quantizeTestFunctionCLM_properAdjoint`). It is unique
(`TauCeti.Symbol.eq_properAdjoint_iff`), and it is the left symbol of the right quantization of the
pointwise adjoint `a(y, ξ)†` cut off near the diagonal
(`TauCeti.Symbol.properAdjoint_eq_leftSymbol_ofRightCutoff`). -/
def properAdjoint (a : Symbol n V W m) (ha : a.HasNearDiagonalKernel R) : Symbol n W V m :=
  ha.exists_quantizeSchwartzValue_eq.choose

/-- The quantization of the adjoint symbol `a*` is the formal adjoint of `Op(a)`:
`Op(a*) φ (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ a(y, 2πζ)† φ(y)) (ζ) dζ`
(`TauCeti.Symbol.adjointTestFunctionCLM_apply`). -/
@[simp]
theorem quantizeSchwartzValue_properAdjoint (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (properAdjoint a ha).coefficient
        (φ.hasCompactSupport.toSchwartzMap φ.contDiff) x =
      adjointTestFunctionCLM ha φ x :=
  ha.exists_quantizeSchwartzValue_eq.choose_spec φ x

/-- **The adjoint identity.** `∫ ⟪Op(a) u, φ⟫ = ∫ ⟪u, Op(a*) φ⟫` for all test functions `u` and
`φ`. -/
theorem integral_inner_quantizeTestFunctionCLM_properAdjoint (ha : a.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) :
    ∫ x, inner ℂ (quantizeTestFunctionCLM ha u x) (φ x) =
      ∫ x, inner ℂ (u x) (quantizeSchwartzValue (properAdjoint a ha).coefficient
        (φ.hasCompactSupport.toSchwartzMap φ.contDiff) x) := by
  simp only [quantizeSchwartzValue_properAdjoint]
  exact integral_inner_quantizeTestFunctionCLM ha u φ

/-- **Uniqueness of the adjoint symbol.** A symbol `c` is the adjoint symbol of `a` exactly when
`∫ ⟪Op(a) u, φ⟫ = ∫ ⟪u, Op(c) φ⟫` for all test functions `u` and `φ`. -/
theorem eq_properAdjoint_iff (ha : a.HasNearDiagonalKernel R) {c : Symbol n W V m} :
    c = properAdjoint a ha ↔ ∀ (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V))
      (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)),
      ∫ x, inner ℂ (quantizeTestFunctionCLM ha u x) (φ x) =
        ∫ x, inner ℂ (u x) (quantizeSchwartzValue c.coefficient
          (φ.hasCompactSupport.toSchwartzMap φ.contDiff) x) := by
  refine ⟨fun h ↦ h ▸ integral_inner_quantizeTestFunctionCLM_properAdjoint ha, fun h ↦ ?_⟩
  refine Symbol.ext <| coefficient_eq_of_forall_testFunction_quantizeSchwartzValue_eq fun φ ↦ ?_
  refine eq_of_forall_integral_inner_eq_of_continuous (𝕜 := ℂ) (μ := volume)
    (c.contDiff_quantizeSchwartzValue _).continuous
    ((properAdjoint a ha).contDiff_quantizeSchwartzValue _).continuous fun u ↦ ?_
  rw [← h, integral_inner_quantizeTestFunctionCLM_properAdjoint]

/-- The adjoint symbol does not depend on the radius of the kernel used to define it. -/
theorem properAdjoint_congr {R' : ℝ} (ha : a.HasNearDiagonalKernel R)
    (ha' : a.HasNearDiagonalKernel R') : properAdjoint a ha = properAdjoint a ha' :=
  Symbol.ext <| coefficient_eq_of_forall_testFunction_quantizeSchwartzValue_eq fun φ ↦
    funext fun x ↦ by
      rw [quantizeSchwartzValue_properAdjoint, quantizeSchwartzValue_properAdjoint,
        adjointTestFunctionCLM_apply, adjointTestFunctionCLM_apply]

/-- **The formula for the adjoint symbol.** For a smooth compactly supported cutoff `χ` equal to
`1` near the closed ball of radius `R`, the adjoint symbol `a*` is the left symbol of the amplitude
`χ(x - y) a(y, ξ)†`: the right quantization of the pointwise adjoint with kernel cut off by
`χ(x - y)`. -/
theorem properAdjoint_eq_leftSymbol_ofRightCutoff (ha : a.HasNearDiagonalKernel R)
    {χ : CoordinateSpace n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχs : HasCompactSupport χ)
    (hχ₁ : χ =ᶠ[𝓝ˢ (Metric.closedBall 0 R)] 1) :
    properAdjoint a ha = (Amplitude.ofRightCutoff χ hχ (a.map adjointRealCLM)).leftSymbol
      (Amplitude.hasProperInputSupport_ofRightCutoff hχ hχs _) := by
  refine Symbol.ext <| coefficient_eq_of_forall_testFunction_quantizeSchwartzValue_eq fun φ ↦
    funext fun x ↦ ?_
  rw [quantizeSchwartzValue_properAdjoint]
  rcases lt_or_ge R 0 with hR | hR
  · -- Over a negative radius `a` vanishes, and so do both sides.
    obtain rfl := ha.eq_zero_of_nonpos hR.le
    rw [adjointTestFunctionCLM_apply,
      Amplitude.quantizeSchwartzValue_leftSymbol_ofRightCutoff hχ hχs]
    simp
  · exact (quantizeSchwartzValue_leftSymbol_ofRightCutoff_eq ha hχ hχs le_rfl hR hχ₁ φ x).symm

/-- The adjoint symbol of the zero symbol is zero. -/
@[simp]
theorem properAdjoint_zero (ha : (0 : Symbol n V W m).HasNearDiagonalKernel R) :
    properAdjoint 0 ha = 0 :=
  Symbol.ext <| coefficient_eq_of_forall_testFunction_quantizeSchwartzValue_eq fun φ ↦
    funext fun x ↦ by
      rw [quantizeSchwartzValue_properAdjoint, adjointTestFunctionCLM_apply]
      simp [quantizeSchwartzValue_zero_left, Real.fourier_eq]

/-- **The adjoint symbol is properly supported**: its kernel is supported within every distance
`R' > R` of the diagonal. -/
theorem HasNearDiagonalKernel.properAdjoint (ha : a.HasNearDiagonalKernel R) {R' : ℝ}
    (hR : R < R') : (properAdjoint a ha).HasNearDiagonalKernel R' := by
  rcases le_or_gt R' 0 with hR' | hR'
  · -- Over a negative radius `a` vanishes, and so does `a*`.
    obtain rfl := ha.eq_zero_of_nonpos (hR.trans_le hR').le
    rw [properAdjoint_zero]
    exact hasNearDiagonalKernel_iff.2 fun u x _ ↦ by
      rw [coefficient_zero, quantizeSchwartzValue_zero_left]
  · -- A cutoff equal to `1` near the closed ball of radius `max R 0 < R'` and supported in the
    -- ball of radius `R'`.
    obtain ⟨χ, hχ, hχs, hχ₁, hχR⟩ := exists_cutoff_ball (le_max_right R 0) (max_lt hR hR')
    rw [properAdjoint_congr ha (ha.mono (le_max_left R 0)),
      properAdjoint_eq_leftSymbol_ofRightCutoff _ hχ hχs hχ₁]
    exact hasNearDiagonalKernel_leftSymbol_ofRightCutoff hχ hχs hχR _

/-- **The adjoint symbol quantizes to the formal adjoint**: as operators on test functions,
`Op(a*) = Op(a)*`. -/
theorem quantizeTestFunctionCLM_properAdjoint (ha : a.HasNearDiagonalKernel R) {R' : ℝ}
    (hR : R < R') : quantizeTestFunctionCLM (ha.properAdjoint hR) = adjointTestFunctionCLM ha :=
  ContinuousLinearMap.ext fun φ ↦ TestFunction.ext fun x ↦ by
    rw [quantizeTestFunctionCLM_apply, quantizeSchwartzValue_properAdjoint]

/-- **The adjoint is an involution**: the adjoint symbol of `a*` is `a`. -/
theorem properAdjoint_properAdjoint (ha : a.HasNearDiagonalKernel R) {R' : ℝ} (hR : R < R') :
    properAdjoint (properAdjoint a ha) (ha.properAdjoint hR) = a := by
  refine ((eq_properAdjoint_iff (ha.properAdjoint hR)).2 fun u φ ↦ ?_).symm
  -- Conjugate the adjoint identity of `a` with the roles of the test functions exchanged.
  have h := congrArg (starRingEnd ℂ) (integral_inner_quantizeTestFunctionCLM_properAdjoint ha φ u)
  rw [← integral_conj, ← integral_conj] at h
  simp only [inner_conj_symm, quantizeTestFunctionCLM_apply] at h ⊢
  exact h.symm

/-- **Compactly supported symbols.** If `a` also has compact spatial support, its adjoint symbol is
the adjoint symbol `TauCeti.Symbol.adjoint` given by the Fourier transforms of the position
slices. -/
theorem properAdjoint_eq_adjoint (ha : a.HasNearDiagonalKernel R)
    (ha' : a.HasCompactSpatialSupport) : properAdjoint a ha = adjoint a ha' :=
  ((eq_properAdjoint_iff ha).2 fun u φ ↦ by
    simpa only [quantizeTestFunctionCLM_apply, HasCompactSupport.toSchwartzMap_toFun] using
      integral_inner_quantizeSchwartzValue_adjoint a ha'
        (u.hasCompactSupport.toSchwartzMap u.contDiff)
        (φ.hasCompactSupport.toSchwartzMap φ.contDiff)).symm

/-- **The adjoint expansion.** The adjoint symbol is an asymptotic sum of the terms
`adjointTerm a k = ((-i)^k / k!) ∑_{|w| = k} (∂_x^w ∂_ξ^w a)†` of order `m - k`: for every `N`,
`a* - ∑_{k < N} adjointTerm a k` is a symbol of order `m - N`. -/
theorem isAsymptoticSum_properAdjoint (ha : a.HasNearDiagonalKernel R) :
    (inclusion (by simp) (properAdjoint a ha) :
      Symbol n W V (m - ((0 : ℕ) : ℝ))).IsAsymptoticSum a.adjointTerm := by
  obtain ⟨χ, hχ, hχs, hU, -⟩ := exists_cutoff_ball (le_max_right R 0) (lt_add_one _)
  have h0 : χ =ᶠ[𝓝 0] 1 :=
    nhds_le_nhdsSet (Metric.mem_closedBall_self (le_max_right R 0)) hU
  rw [properAdjoint_congr ha (ha.mono (le_max_left R 0)),
    properAdjoint_eq_leftSymbol_ofRightCutoff _ hχ hχs hU]
  rw [← funext (Amplitude.leftTerm_ofRight_map_adjointRealCLM a)]
  exact Amplitude.isAsymptoticSum_leftSymbol_ofRightCutoff hχ hχs h0 (a.map adjointRealCLM)

end ProperAdjoint

end Symbol

/-! ### The adjoint of a properly supported classical symbol -/

namespace ClassicalSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}

/-- **The adjoint of a properly supported classical symbol is classical.** For a classical symbol
`a` of order `m` between complex Hilbert spaces whose quantization has kernel supported within
distance `R` of the diagonal, the adjoint symbol `a*` (`TauCeti.Symbol.properAdjoint`), whose
quantization is the formal adjoint of `Op(a)`, is a classical symbol of order `m`. Its homogeneous
terms are the formal adjoint `adjointTerms a.term` of the expansion of `a`. -/
def properAdjoint (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasNearDiagonalKernel R) :
    ClassicalSymbol n W V m where
  toSymbol := a.toSymbol.properAdjoint ha
  term := adjointTerms a.term
  exists_remainder' := ⟨default, exists_remainder_adjointTerms_of_isAsymptoticSum a
    (Symbol.isAsymptoticSum_properAdjoint ha) default⟩

variable (a : ClassicalSymbol n V W m) (ha : a.toSymbol.HasNearDiagonalKernel R)

@[simp]
theorem toSymbol_properAdjoint : (a.properAdjoint ha).toSymbol = a.toSymbol.properAdjoint ha :=
  (rfl)

@[simp]
theorem term_properAdjoint (j : ℕ) : (a.properAdjoint ha).term j = adjointTerms a.term j :=
  (rfl)

/-- **The principal symbol of the adjoint** is the pointwise adjoint `a_m†` of the principal
symbol. -/
@[simp]
theorem principal_properAdjoint : (a.properAdjoint ha).principal = a.principal.adjoint := by
  ext1
  funext z
  simp

/-- **The adjoint of an elliptic symbol is elliptic**, and conversely. -/
@[simp]
theorem isElliptic_properAdjoint_iff : (a.properAdjoint ha).IsElliptic ↔ a.IsElliptic := by
  rw [isElliptic_def, isElliptic_def, principal_properAdjoint,
    HomogeneousSymbol.isElliptic_adjoint_iff]

end ClassicalSymbol

end TauCeti

/-! ### Explicit adjoints of properly cut-off symbols -/

open MeasureTheory Real FourierTransform TopologicalSpace ComplexConjugate Filter Finset
open scoped SchwartzMap RealInnerProductSpace ContDiff Distributions Topology

namespace TauCeti.Symbol

section Estimates

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] {m : ℝ}

/-- A Schwartz function as a native position symbol from scalars to its coefficient model. -/
private def spanSymbol (u : 𝓢(CoordinateSpace n, V)) : Symbol n ℂ V 0 :=
  Symbol.ofSpatial (fun x ↦ ContinuousLinearMap.toSpanSingleton ℂ (u x)) (by
    let L := (ContinuousLinearMap.toSpanSingletonLIE ℂ V).toLinearIsometry.toContinuousLinearMap
      |>.restrictScalars ℝ
    have h := L.contDiff.comp (u.smooth (⊤ : ℕ∞))
    have he : L ∘ u = fun x ↦ ContinuousLinearMap.toSpanSingleton ℂ (u x) := by
      funext x
      exact ContinuousLinearMap.toSpanSingletonLIE_apply ℂ V (u x)
    exact he ▸ h)

/-- Applying the scalar position symbol to one recovers its defining function. -/
@[simp]
private theorem spanSymbol_apply (u : 𝓢(CoordinateSpace n, V)) (x ξ : CoordinateSpace n) (z : ℂ) :
    (spanSymbol u).coefficient (x, ξ) z = z • u x := by
  unfold spanSymbol
  rw [Symbol.coefficient_ofSpatial]
  exact ContinuousLinearMap.toSpanSingleton_apply ℂ (u x) z

/-- The input slice whose Fourier transform occurs in the right cut-off quantization. -/
private def inputSlice (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x ξ y : CoordinateSpace n) : W :=
  χ (x - y) • a.coefficient (y, ξ) (u y)

/-- Encode the vector-valued input slice in a native scalar-source amplitude. -/
private def inputAmplitude (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) : Amplitude n ℂ W (m + 0) :=
  Amplitude.ofRightCutoff χ (χ.smooth (⊤ : ℕ∞)) (a.comp (spanSymbol u))

/-- The encoded amplitude evaluated at one is the original vector-valued slice. -/
@[simp]
private theorem inputAmplitude_apply (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x y ξ : CoordinateSpace n) :
    (inputAmplitude χ a u).coefficient (x, y, ξ) 1 = inputSlice χ a u x ξ y := by
  simp [inputAmplitude, inputSlice]

/-- Compact cutoffs make the actual vector-valued input slice integrable. -/
private theorem integrable_inputSlice {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ : HasCompactSupport χ)
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x ξ : CoordinateSpace n) :
    Integrable (inputSlice χ a u x ξ) := by
  have hs := (Amplitude.hasProperInputSupport_ofRightCutoff (χ.smooth (⊤ : ℕ∞)) hχ
    (a.comp (spanSymbol u))).hasCompactSupport_slice x ξ
  have hc : Continuous fun y ↦ (inputAmplitude χ a u).coefficient (x, y, ξ) :=
    (inputAmplitude χ a u).contDiff_coefficient.continuous.comp (by fun_prop)
  have he : Continuous fun y ↦ (inputAmplitude χ a u).coefficient (x, y, ξ) 1 :=
    hc.clm_apply continuous_const
  have hs₁ : HasCompactSupport fun y ↦ (inputAmplitude χ a u).coefficient (x, y, ξ) 1 :=
    hs.comp_left (g := fun T : ℂ →L[ℂ] W ↦ T 1) rfl
  have h := he.integrable_of_hasCompactSupport (μ := volume) hs₁
  simpa only [inputAmplitude_apply] using h

/-- Fourier evaluation at one transports the scalar-source amplitude to its vector slice. -/
private theorem fourier_inputAmplitude_apply {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ :
  HasCompactSupport χ)
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (x ξ θ : CoordinateSpace n) :
    𝓕 (fun y ↦ (inputAmplitude χ a u).coefficient (x, y, ξ)) θ 1 =
      𝓕 (inputSlice χ a u x ξ) θ := by
  have hs := (Amplitude.hasProperInputSupport_ofRightCutoff (χ.smooth (⊤ : ℕ∞)) hχ
    (a.comp (spanSymbol u))).hasCompactSupport_slice x ξ
  have hc : Continuous fun y ↦ (inputAmplitude χ a u).coefficient (x, y, ξ) :=
    (inputAmplitude χ a u).contDiff_coefficient.continuous.comp (by fun_prop)
  have hi := (Real.fourierIntegral_convergent_iff θ).2
    (hc.integrable_of_hasCompactSupport (μ := volume) hs)
  rw [Real.fourier_eq, ContinuousLinearMap.integral_apply hi, Real.fourier_eq]
  exact integral_congr_ae (.of_forall fun y ↦ by
    simp only [Circle.smul_def, smul_apply, inputAmplitude_apply])

/-- The cut-off slice Fourier transform is continuous in both positions and frequencies. -/
private theorem continuous_fourier_inputSlice {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (inputSlice χ a u q.2.1 q.2.2) q.1 := by
  have h := (Amplitude.hasProperInputSupport_ofRightCutoff (χ.smooth (⊤ : ℕ∞)) hχ
    (a.comp (spanSymbol u))).continuous_fourier_slice
  have he : Continuous fun q : CoordinateSpace n × CoordinateSpace n × CoordinateSpace n ↦
      (𝓕 (fun y ↦ (inputAmplitude χ a u).coefficient (q.2.1, y, q.2.2)) q.1) 1 :=
    h.clm_apply continuous_const
  simpa only [fourier_inputAmplitude_apply hχ] using he

/-- Existing amplitude estimates give arbitrary Fourier decay of the vector-valued input slice. -/
private theorem exists_norm_fourier_inputSlice_le {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ θ ξ,
      ‖𝓕 (inputSlice χ a u x ξ) θ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖θ‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC, hb⟩ := (Amplitude.hasProperInputSupport_ofRightCutoff (χ.smooth (⊤ : ℕ∞)) hχ
    (a.comp (spanSymbol u))).exists_norm_fourier_slice_le hK r
  refine ⟨C, hC, fun x hx θ ξ ↦ ?_⟩
  rw [← fourier_inputAmplitude_apply hχ]
  simpa only [inputAmplitude, norm_one, mul_one, add_zero] using
    (ContinuousLinearMap.le_opNorm _ (1 : ℂ)).trans
      (mul_le_mul_of_nonneg_right (hb x hx θ ξ) (norm_nonneg (1 : ℂ)))

/-- On the frequency diagonal the same estimates overcome every real symbol order. -/
private theorem exists_norm_fourier_inputSlice_diagonal_le {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ K, ∀ ζ,
      ‖𝓕 (inputSlice χ a u x ((2 * π) • ζ)) ζ‖ ≤
        C * (1 + ‖ζ‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC, hb⟩ := exists_norm_fourier_inputSlice_le hχ a u hK (m + r)
  refine ⟨C * (2 * π) ^ |m|, by positivity, fun x hx ζ ↦ (hb x hx ζ _).trans ?_⟩
  have hs := one_add_norm_smul_sq_rpow_le (by nlinarith [Real.two_le_pi] : 1 ≤ 2 * π) m ζ
  calc C * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) *
          (1 + ‖ζ‖ ^ 2) ^ (-(m + r) / 2)
      ≤ C * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) *
          (1 + ‖ζ‖ ^ 2) ^ (-(m + r) / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (by positivity)
    _ = C * (2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (-r / 2) := by
      calc _ = C * (2 * π) ^ |m| *
          ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * (1 + ‖ζ‖ ^ 2) ^ (-(m + r) / 2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by positivity)]
          have he : m / 2 + -(m + r) / 2 = -r / 2 := by ring
          rw [he]

/-- The actual right-cutoff Fourier integrand at a point. -/
private def rightIntegrand (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (x ζ : CoordinateSpace n) : W :=
  𝐞 ⟪ζ, x⟫ • 𝓕 (inputSlice χ a u x ((2 * π) • ζ)) ζ

/-- Joint continuity of the partially transformed right-cutoff integrand. -/
private theorem continuous_rightIntegrand {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ rightIntegrand χ a u q.1 q.2 := by
  have hf := (continuous_fourier_inputSlice hχ a u).comp
    (show Continuous (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (q.2, q.1, (2 * π) • q.2)) by fun_prop)
  exact (Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)).smul hf

/-- The right-cutoff integrand is integrable at every output, for every real symbol order. -/
private theorem integrable_rightIntegrand {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) : Integrable (rightIntegrand χ a u x) := by
  obtain ⟨C, -, hb⟩ := exists_norm_fourier_inputSlice_diagonal_le hχ a u
    (isCompact_singleton (x := x)) (n + 1)
  have hw : Integrable fun ζ : CoordinateSpace n ↦
      C * (1 + ‖ζ‖ ^ 2) ^ (-((n : ℝ) + 1) / 2) :=
    (integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).const_mul C
  refine hw.mono' ((continuous_rightIntegrand hχ a u).comp
    (continuous_const.prodMk continuous_id)).aestronglyMeasurable (.of_forall fun ζ ↦ ?_)
  simpa only [rightIntegrand, Circle.norm_smul] using hb x rfl ζ

section Pairing

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The partially transformed integrand of the adjoint's spatial pairing. -/
private def rightPairIntegrand (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V H m)
    (v : 𝓢(CoordinateSpace n, V)) (u : 𝓢(CoordinateSpace n, H))
    (q : CoordinateSpace n × CoordinateSpace n) : ℂ :=
  inner ℂ (u q.1) (rightIntegrand χ a v q.1 q.2)

omit [CompleteSpace H] in
/-- Compact output tests give absolute integrability after the input Fourier transform,
without restricting the real symbol order. -/
private theorem integrable_rightPairIntegrand {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V H m) (v : 𝓢(CoordinateSpace n, V))
    (u : 𝓢(CoordinateSpace n, H)) (hu : HasCompactSupport u) :
    Integrable (rightPairIntegrand χ a v u) (volume.prod volume) := by
  obtain ⟨C, -, hb⟩ := exists_norm_fourier_inputSlice_diagonal_le hχ a v
    hu.isCompact (n + 1)
  have hc : Continuous (rightPairIntegrand χ a v u) :=
    (u.continuous.comp continuous_fst).inner (continuous_rightIntegrand hχ a v)
  refine (u.integrable.norm.mul_prod
    ((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).const_mul C)).mono'
      hc.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  by_cases hx : q.1 ∈ tsupport u
  · exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (by
        simpa only [rightIntegrand, Circle.norm_smul] using hb q.1 hx q.2) (norm_nonneg _))
  · simp only [rightPairIntegrand, image_eq_zero_of_notMem_tsupport hx, inner_zero_left,
      norm_zero, zero_mul, le_refl]

/-- Fubini may be applied to the partially transformed pairing for every real order. -/
private theorem integral_inner_rightCutoff_eq {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V H m) (v : 𝓢(CoordinateSpace n, V))
    (u : 𝓢(CoordinateSpace n, H)) (hu : HasCompactSupport u) :
    (∫ x, inner ℂ (u x) (∫ ζ, rightIntegrand χ a v x ζ)) =
      ∫ ζ, ∫ x, inner ℂ (u x) (rightIntegrand χ a v x ζ) := by
  simp_rw [← integral_inner (integrable_rightIntegrand hχ a v _)]
  exact integral_integral_swap (integrable_rightPairIntegrand hχ a v u hu)

end Pairing

end Estimates

section HermitianAdjoint

variable {n : ℕ}

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m : ℝ}

/-- The pointwise adjoint coefficient applied to an output test, at a fixed frequency. -/
private def adjointSlice (a : Symbol n V W m) (v : 𝓢(CoordinateSpace n, W))
    (ζ y : CoordinateSpace n) : V :=
  ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (v y)

/-- The fixed-frequency adjoint slice is continuous. -/
private theorem continuous_adjointSlice (a : Symbol n V W m) (v : 𝓢(CoordinateSpace n, W))
    (ζ : CoordinateSpace n) : Continuous (adjointSlice a v ζ) := by
  have hc : ContDiff ℝ ∞ (fun y ↦ a.coefficient (y, (2 * π) • ζ)) :=
    a.contDiff_coefficient.comp (contDiff_id.prodMk contDiff_const)
  unfold adjointSlice
  exact hc.clm_adjoint.continuous.clm_apply v.continuous

/-- Compact output tests make the fixed-frequency adjoint slice compactly supported. -/
private theorem compact_adjointSlice (a : Symbol n V W m) (v : 𝓢(CoordinateSpace n, W))
    (hv : HasCompactSupport v) (ζ : CoordinateSpace n) : HasCompactSupport (adjointSlice a v ζ) :=
  hv.mono fun y hy hz ↦ hy (by simp [adjointSlice, hz])

/-- The scalar pairing integrand at a fixed frequency, before swapping the two positions. -/
private def fixedPairIntegrand (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W))
    (ζ : CoordinateSpace n) (q : CoordinateSpace n × CoordinateSpace n) : ℂ :=
  (𝐞 ⟪ζ, q.1⟫ : ℂ) * (𝐞 (-⟪q.2, ζ⟫) : ℂ) * conj (χ (q.2 - q.1)) *
    inner ℂ (u q.1) (adjointSlice a v ζ q.2)

/-- At each fixed frequency Fubini in the positions is justified by the compact tests.
The frequency integral is kept outside until the arbitrary-order estimates apply. -/
private theorem integrable_fixedPairIntegrand (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W))
    (hv : HasCompactSupport v) (ζ : CoordinateSpace n) :
    Integrable (fixedPairIntegrand χ a u v ζ) (volume.prod volume) := by
  have hg := (continuous_adjointSlice a v ζ).integrable_of_hasCompactSupport
    (μ := volume) (compact_adjointSlice a v hv ζ)
  have hc : Continuous (fixedPairIntegrand χ a u v ζ) := by
    have hg := continuous_adjointSlice a v ζ
    unfold fixedPairIntegrand
    fun_prop
  refine ((u.integrable.norm.mul_prod hg.norm).const_mul
    (SchwartzMap.seminorm ℂ 0 0 χ)).mono' hc.aestronglyMeasurable (.of_forall fun q ↦ ?_)
  calc ‖fixedPairIntegrand χ a u v ζ q‖
      = ‖χ (q.2 - q.1)‖ * ‖inner ℂ (u q.1) (adjointSlice a v ζ q.2)‖ := by
        simp only [fixedPairIntegrand, norm_mul, Circle.norm_coe, Complex.norm_conj, one_mul]
    _ ≤ SchwartzMap.seminorm ℂ 0 0 χ * (‖u q.1‖ * ‖adjointSlice a v ζ q.2‖) :=
      mul_le_mul (χ.norm_le_seminorm ℂ _) (norm_inner_le_norm _ _) (norm_nonneg _)
        (apply_nonneg _ _)
    _ = _ := by ring

/-- The partially transformed integrand of the kernel-cutoff left quantization. -/
private def kernelCutoffIntegrand (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (y ζ : CoordinateSpace n) : W :=
  𝐞 ⟪ζ, y⟫ • a.coefficient (y, (2 * π) • ζ)
    (𝓕 (inputSlice χ (Symbol.const (ContinuousLinearMap.id ℂ V)) u y ((2 * π) • ζ)) ζ)

omit [CompleteSpace V] [CompleteSpace W] in
/-- Continuity of the left integrand follows from the same native cut-off slice API. -/
private theorem continuous_kernelCutoffIntegrand {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ :
  HasCompactSupport χ)
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦ kernelCutoffIntegrand χ a u q.1
      q.2 := by
  have hc := a.contDiff_coefficient.continuous.comp
    (show Continuous (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (q.1, (2 * π) • q.2)) by fun_prop)
  have hf := (continuous_fourier_inputSlice hχ (Symbol.const (ContinuousLinearMap.id ℂ V)) u).comp
    (show Continuous (fun q : CoordinateSpace n × CoordinateSpace n ↦
      (q.2, q.1, (2 * π) • q.2)) by fun_prop)
  exact (Real.continuous_fourierChar.comp (continuous_snd.inner continuous_fst)).smul
    (hc.clm_apply hf)

omit [CompleteSpace V] [CompleteSpace W] in
/-- The left integrand also has arbitrary frequency decay locally in its output position. -/
private theorem exists_norm_kernelCutoffIntegrand_le {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ :
  HasCompactSupport χ)
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    {K : Set (CoordinateSpace n)} (hK : IsCompact K) (r : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ y ∈ K, ∀ ζ,
      ‖kernelCutoffIntegrand χ a u y ζ‖ ≤ C * (1 + ‖ζ‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨A, hA, ha⟩ := a.exists_bound_coefficient K hK
  obtain ⟨C, hC, hc⟩ := exists_norm_fourier_inputSlice_diagonal_le hχ
    (Symbol.const (ContinuousLinearMap.id ℂ V)) u hK (m + r)
  refine ⟨A * C * (2 * π) ^ |m|, by positivity, fun y hy ζ ↦ ?_⟩
  have hs := one_add_norm_smul_sq_rpow_le (by nlinarith [Real.two_le_pi] : 1 ≤ 2 * π) m ζ
  calc ‖kernelCutoffIntegrand χ a u y ζ‖
      ≤ A * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) *
          (C * (1 + ‖ζ‖ ^ 2) ^ (-(m + r) / 2)) := by
        rw [kernelCutoffIntegrand, Circle.norm_smul]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul (ha y hy _) (hc y hy ζ) (norm_nonneg _) (by positivity))
    _ ≤ A * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) *
          (C * (1 + ‖ζ‖ ^ 2) ^ (-(m + r) / 2)) := by gcongr
    _ = A * C * (2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (-r / 2) := by
      calc _ = A * C * (2 * π) ^ |m| *
          ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * (1 + ‖ζ‖ ^ 2) ^ (-(m + r) / 2)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (by positivity)]
          congr 2
          ring

omit [CompleteSpace V] [CompleteSpace W] in
/-- At every output the left-cutoff Fourier integrand is integrable. -/
private theorem integrable_kernelCutoffIntegrand {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ :
  HasCompactSupport χ)
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n) :
    Integrable (kernelCutoffIntegrand χ a u y) := by
  obtain ⟨C, -, hb⟩ := exists_norm_kernelCutoffIntegrand_le hχ a u (isCompact_singleton (x :=
    y)) (n + 1)
  refine ((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).const_mul C).mono'
    ((continuous_kernelCutoffIntegrand hχ a u).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable (.of_forall fun ζ ↦ ?_)
  exact hb y rfl ζ

omit [CompleteSpace V] [CompleteSpace W] in
/-- The left-cutoff pairing is integrable after its input Fourier transform for every order. -/
private theorem integrable_leftPairIntegrand {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ :
  HasCompactSupport χ)
    (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W))
    (hv : HasCompactSupport v) :
    Integrable (fun q : CoordinateSpace n × CoordinateSpace n ↦
      inner ℂ (kernelCutoffIntegrand χ a u q.1 q.2) (v q.1)) (volume.prod volume) := by
  obtain ⟨C, -, hb⟩ := exists_norm_kernelCutoffIntegrand_le hχ a u hv.isCompact (n + 1)
  refine (v.integrable.norm.mul_prod
    ((integrable_rpow_neg_one_add_norm_sq (r := n + 1) (by simp)).const_mul C)).mono'
      ((continuous_kernelCutoffIntegrand hχ a u).inner
        (v.continuous.comp continuous_fst)).aestronglyMeasurable (.of_forall fun q ↦ ?_)
  by_cases hy : q.1 ∈ tsupport v
  · exact (norm_inner_le_norm _ _).trans (by
      calc ‖kernelCutoffIntegrand χ a u q.1 q.2‖ * ‖v q.1‖
          ≤ (C * (1 + ‖q.2‖ ^ 2) ^ (-((n : ℝ) + 1) / 2)) * ‖v q.1‖ := by gcongr; exact hb q.1 hy q.2
        _ = _ := by ring)
  · simp [image_eq_zero_of_notMem_tsupport hy]

/-- The actual quantization of the kernel-cutoff symbol is the integral of the left integrand. -/
private theorem quantize_kernelCutoff_eq_integral_kernelCutoffIntegrand
    (χ : 𝓢(CoordinateSpace n, ℂ)) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n) :
    quantizeSchwartzValue (Symbol.kernelCutoff χ a).coefficient u y =
      ∫ ζ, kernelCutoffIntegrand χ a u y ζ := by
  rw [Symbol.quantizeSchwartzValue_kernelCutoff, quantizeSchwartzValue_def]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have hg : (fun x ↦ χ (y - x)).HasTemperateGrowth :=
    χ.hasTemperateGrowth.comp ((Function.HasTemperateGrowth.const y).sub
      Function.HasTemperateGrowth.id')
  have he : ⇑(SchwartzMap.smulLeftCLM V (fun x ↦ χ (y - x)) u) =
      inputSlice χ (Symbol.const (ContinuousLinearMap.id ℂ V)) u y ((2 * π) • ζ) := by
    funext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg, inputSlice,
      Symbol.coefficient_const, ContinuousLinearMap.id_apply]
  simp only [kernelCutoffIntegrand, he, SchwartzMap.fourier_coe]

/-- The original operator pairing has a justified frequency-first representation. -/
private theorem integral_inner_kernelCutoff_eq {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) (hv : HasCompactSupport v) :
    (∫ y, inner ℂ (quantizeSchwartzValue (Symbol.kernelCutoff χ a).coefficient u y) (v y)) =
      ∫ ζ, ∫ y, inner ℂ (kernelCutoffIntegrand χ a u y ζ) (v y) := by
  simp_rw [quantize_kernelCutoff_eq_integral_kernelCutoffIntegrand,
    ← integral_inner_left (integrable_kernelCutoffIntegrand hχ a u _)]
  exact integral_integral_swap (integrable_leftPairIntegrand hχ a u v hv)

/-- The other fixed-frequency position integral is the pairing with the left integrand. -/
private theorem integral_fixedPair_eq_inner_kernelCutoffIntegrand {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W))
    (y ζ : CoordinateSpace n) :
    (∫ x, fixedPairIntegrand χ a u v ζ (x, y)) =
      inner ℂ (kernelCutoffIntegrand χ a u y ζ) (v y) := by
  have hi := (Real.fourierIntegral_convergent_iff ζ).2
    (integrable_inputSlice hχ (Symbol.const (ContinuousLinearMap.id ℂ V)) u y ((2 * π) • ζ))
  rw [kernelCutoffIntegrand, Circle.smul_def, inner_smul_left, Real.fourier_eq,
    ← ContinuousLinearMap.integral_comp_comm _ hi,
    ← integral_inner_left ((a.coefficient (y, (2 * π) • ζ)).integrable_comp hi),
    ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [inputSlice, Symbol.coefficient_const, ContinuousLinearMap.id_apply,
    Circle.smul_def, map_smul, inner_smul_left,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg,
    fixedPairIntegrand, adjointSlice]
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm ζ y, real_inner_comm ζ x]
  ring

/-- Expanding only the input Fourier integral gives the fixed-frequency row pairing. -/
private theorem inner_rightIntegrand_eq_integral_fixedPair {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W))
    (x ζ : CoordinateSpace n) :
    inner ℂ (u x) (rightIntegrand (SchwartzMap.conjnegCLM χ) (a.map
      ContinuousLinearMap.adjointRealCLM) v x ζ) =
      ∫ y, fixedPairIntegrand χ a u v ζ (x, y) := by
  have hi := (Real.fourierIntegral_convergent_iff ζ).2
    (integrable_inputSlice (SchwartzMap.hasCompactSupport_conjnegCLM hχ) (a.map
      ContinuousLinearMap.adjointRealCLM)
      v x ((2 * π) • ζ))
  simp only [rightIntegrand, Circle.smul_def, inner_smul_right]
  rw [Real.fourier_eq, ← integral_inner hi, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  simp only [inputSlice, Circle.smul_def, inner_smul_right, Symbol.coefficient_map,
    ContinuousLinearMap.adjointRealCLM_apply, SchwartzMap.conjnegCLM_apply, neg_sub,
    fixedPairIntegrand, adjointSlice]
  ring

/-- The explicit left symbol of the right adjoint amplitude with reversed conjugate cutoff. -/
def adjointKernelCutoff (a : Symbol n V W m) (χ : 𝓢(CoordinateSpace n, ℂ))
    (hχ : HasCompactSupport χ) : Symbol n W V m :=
  (Amplitude.ofRightCutoff (SchwartzMap.conjnegCLM χ) ((SchwartzMap.conjnegCLM χ).smooth (⊤ : ℕ∞))
    (a.map ContinuousLinearMap.adjointRealCLM)).leftSymbol
      (Amplitude.hasProperInputSupport_ofRightCutoff ((SchwartzMap.conjnegCLM χ).smooth (⊤ : ℕ∞))
        (SchwartzMap.hasCompactSupport_conjnegCLM hχ) _)

/-- The proper-input amplitude formula identifies the explicit symbol with its actual cut-off
  right Fourier integral. -/
private theorem quantize_adjointKernelCutoff_eq_integral_rightIntegrand
    (χ : 𝓢(CoordinateSpace n, ℂ)) (hχ : HasCompactSupport χ) (a : Symbol n V W m)
    (v : 𝓢(CoordinateSpace n, W)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (adjointKernelCutoff a χ hχ).coefficient v x =
      ∫ ζ, rightIntegrand (SchwartzMap.conjnegCLM χ) (a.map ContinuousLinearMap.adjointRealCLM)
        v x ζ := by
  rw [adjointKernelCutoff, Amplitude.quantizeSchwartzValue_leftSymbol_ofRightCutoff _
    (SchwartzMap.hasCompactSupport_conjnegCLM hχ)]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  -- Fourier acts on the whole slice function; expose its eta expansion before rewriting.
  have he : inputSlice (SchwartzMap.conjnegCLM χ)
      (a.map ContinuousLinearMap.adjointRealCLM) v x ((2 * π) • ζ) =
      fun y ↦ (SchwartzMap.conjnegCLM χ) (x - y) •
        (a.map ContinuousLinearMap.adjointRealCLM).coefficient (y, (2 * π) • ζ) (v y) := by
    funext y
    rfl
  rw [rightIntegrand, he]

/-- The explicit adjoint symbol quantizes to the cut-off right Fourier integral.
This is a pointwise Schwartz-input formula; it does not assert a Schwartz endomorphism. -/
theorem quantizeSchwartzValue_adjointKernelCutoff (a : Symbol n V W m)
    (χ : 𝓢(CoordinateSpace n, ℂ)) (hχ : HasCompactSupport χ)
    (v : 𝓢(CoordinateSpace n, W)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.adjointKernelCutoff χ hχ).coefficient v x =
      ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ conj (χ (y - x)) •
        ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (v y)) ζ := by
  rw [quantize_adjointKernelCutoff_eq_integral_rightIntegrand]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have he : inputSlice (SchwartzMap.conjnegCLM χ)
      (a.map ContinuousLinearMap.adjointRealCLM) v x ((2 * π) • ζ) =
      fun y ↦ conj (χ (y - x)) •
        ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (v y) := by
    funext y
    rw [inputSlice, coefficient_map, ContinuousLinearMap.adjointRealCLM_apply,
      SchwartzMap.conjnegCLM_apply, neg_sub]
  rw [rightIntegrand, he]

/-- The explicit properly cut-off symbol is the actual spatial formal adjoint on compact tests,
for every real order and complete complex Hilbert coefficient models of arbitrary rank. -/
theorem integral_inner_quantizeSchwartzValue_adjointKernelCutoff
    (χ : 𝓢(CoordinateSpace n, ℂ)) (hχ : HasCompactSupport χ) (a : Symbol n V W m)
    (u : 𝓢(CoordinateSpace n, V)) (hu : HasCompactSupport u)
    (v : 𝓢(CoordinateSpace n, W)) (hv : HasCompactSupport v) :
    (∫ x, inner ℂ (quantizeSchwartzValue (Symbol.kernelCutoff χ a).coefficient u x) (v x)) =
      ∫ x, inner ℂ (u x) (quantizeSchwartzValue (adjointKernelCutoff a χ hχ).coefficient v x) := by
  rw [integral_inner_kernelCutoff_eq hχ a u v hv]
  simp_rw [quantize_adjointKernelCutoff_eq_integral_rightIntegrand]
  rw [integral_inner_rightCutoff_eq (SchwartzMap.hasCompactSupport_conjnegCLM hχ)
    (a.map ContinuousLinearMap.adjointRealCLM) v u hu]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  calc (∫ y, inner ℂ (kernelCutoffIntegrand χ a u y ζ) (v y))
      = ∫ y, ∫ x, fixedPairIntegrand χ a u v ζ (x, y) :=
        integral_congr_ae (.of_forall fun y ↦
          (integral_fixedPair_eq_inner_kernelCutoffIntegrand hχ a u v y ζ).symm)
    _ = ∫ x, ∫ y, fixedPairIntegrand χ a u v ζ (x, y) :=
      (integral_integral_swap
        (f := fun x y : CoordinateSpace n ↦ fixedPairIntegrand χ a u v ζ (x, y))
        (integrable_fixedPairIntegrand χ a u v hv ζ)).symm
    _ = ∫ x, inner ℂ (u x)
        (rightIntegrand (SchwartzMap.conjnegCLM χ) (a.map ContinuousLinearMap.adjointRealCLM) v
          x ζ) :=
      integral_congr_ae (.of_forall fun x ↦
        (inner_rightIntegrand_eq_integral_fixedPair hχ a u v x ζ).symm)

/-- The explicit adjoint is a native asymptotic sum of all right-amplitude terms. -/
theorem isAsymptoticSum_adjointKernelCutoff (a : Symbol n V W m)
    (χ : 𝓢(CoordinateSpace n, ℂ)) (hχ : HasCompactSupport χ)
    (hχ₁ : ⇑χ =ᶠ[𝓝 0] 1) :
    (inclusion (by simp) (a.adjointKernelCutoff χ hχ) :
      Symbol n W V (m - ((0 : ℕ) : ℝ))).IsAsymptoticSum
        (Amplitude.ofRight (a.map ContinuousLinearMap.adjointRealCLM)).leftTerm := by
  exact Amplitude.isAsymptoticSum_leftSymbol_ofRightCutoff
    ((SchwartzMap.conjnegCLM χ).smooth (⊤ : ℕ∞))
    (SchwartzMap.hasCompactSupport_conjnegCLM hχ) (SchwartzMap.conjnegCLM_eventually_one hχ₁)
    (a.map ContinuousLinearMap.adjointRealCLM)

/-- All truncation remainders are the native proper-input amplitude remainders of order `m - N`. -/
theorem adjointKernelCutoff_eq_sum_leftTerm_add_leftRemainder (a : Symbol n V W m)
    (χ : 𝓢(CoordinateSpace n, ℂ)) (hχ : HasCompactSupport χ)
    (hχ₁ : ⇑χ =ᶠ[𝓝 0] 1) (N : ℕ) :
    adjointKernelCutoff a χ hχ =
      ∑ k ∈ range N, Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg k))
          ((Amplitude.ofRight (a.map ContinuousLinearMap.adjointRealCLM)).leftTerm k) +
        Symbol.inclusion (sub_le_self _ (Nat.cast_nonneg N))
          ((Amplitude.ofRightCutoff (SchwartzMap.conjnegCLM χ) ((SchwartzMap.conjnegCLM
            χ).smooth (⊤ : ℕ∞))
            (a.map ContinuousLinearMap.adjointRealCLM)).leftRemainder
              (Amplitude.hasProperInputSupport_ofRightCutoff ((SchwartzMap.conjnegCLM χ).smooth
                (⊤ : ℕ∞))
                (SchwartzMap.hasCompactSupport_conjnegCLM hχ) _) N) := by
  exact Amplitude.leftSymbol_ofRightCutoff_eq_sum_leftTerm_add_leftRemainder
    ((SchwartzMap.conjnegCLM χ).smooth (⊤ : ℕ∞)) (SchwartzMap.hasCompactSupport_conjnegCLM hχ)
      (SchwartzMap.conjnegCLM_eventually_one hχ₁)
    (a.map ContinuousLinearMap.adjointRealCLM) N

/-- The first remainder has order `m - 1` under only the exact normalization `χ 0 = 1`. -/
theorem adjointKernelCutoff_eq_add_leftRemainder_one (a : Symbol n V W m)
    (χ : 𝓢(CoordinateSpace n, ℂ)) (hχ : HasCompactSupport χ) (hχ₀ : χ 0 = 1) :
    adjointKernelCutoff a χ hχ = a.map ContinuousLinearMap.adjointRealCLM +
      Symbol.inclusion (by simp)
        ((Amplitude.ofRightCutoff (SchwartzMap.conjnegCLM χ) ((SchwartzMap.conjnegCLM χ).smooth
          (⊤ : ℕ∞))
          (a.map ContinuousLinearMap.adjointRealCLM)).leftRemainder
            (Amplitude.hasProperInputSupport_ofRightCutoff ((SchwartzMap.conjnegCLM χ).smooth
              (⊤ : ℕ∞))
              (SchwartzMap.hasCompactSupport_conjnegCLM hχ) _) 1) := by
  exact Amplitude.leftSymbol_ofRightCutoff_eq_add_leftRemainder_one
    ((SchwartzMap.conjnegCLM χ).smooth (⊤ : ℕ∞)) (SchwartzMap.hasCompactSupport_conjnegCLM hχ)
    (by simp only [SchwartzMap.conjnegCLM_apply, neg_zero, hχ₀, map_one])
    (a.map ContinuousLinearMap.adjointRealCLM)

end HermitianAdjoint

section NativeTests

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}

/-- The explicit adjoint symbol has the same near-diagonal support radius as its scalar cutoff. -/
theorem hasNearDiagonalKernel_adjointKernelCutoff {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ :
  HasCompactSupport χ)
    (hχR : Function.support χ ⊆ Metric.ball 0 R) (a : Symbol n V W m) :
    (adjointKernelCutoff a χ hχ).HasNearDiagonalKernel R := by
  exact hasNearDiagonalKernel_leftSymbol_ofRightCutoff _
    (SchwartzMap.hasCompactSupport_conjnegCLM hχ)
    (SchwartzMap.support_conjnegCLM_subset_ball hχR) _

/-- The arbitrary-order Green identity holds on the actual native test-function operators. -/
theorem integral_inner_quantizeTestFunctionCLM_adjointKernelCutoff {χ : 𝓢(CoordinateSpace n,
  ℂ)} (hχ : HasCompactSupport χ)
    (hχR : Function.support χ ⊆ Metric.ball 0 R) (a : Symbol n V W m)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) (v : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) :
    (∫ x, inner ℂ (Symbol.quantizeTestFunctionCLM
      (Symbol.hasNearDiagonalKernel_kernelCutoff χ hχR a) u x) (v x)) =
      ∫ x, inner ℂ (u x)
        (Symbol.quantizeTestFunctionCLM (hasNearDiagonalKernel_adjointKernelCutoff hχ hχR a) v
          x) := by
  have hu : u.hasCompactSupport.toSchwartzMap u.contDiff = TestFunction.toSchwartzMapCLM ℂ u := by
    ext x
    rw [HasCompactSupport.toSchwartzMap_toFun, TestFunction.toSchwartzMapCLM_apply]
  have hv : v.hasCompactSupport.toSchwartzMap v.contDiff = TestFunction.toSchwartzMapCLM ℂ v := by
    ext x
    rw [HasCompactSupport.toSchwartzMap_toFun, TestFunction.toSchwartzMapCLM_apply]
  have h := Symbol.integral_inner_quantizeSchwartzValue_adjointKernelCutoff χ hχ a
    (TestFunction.toSchwartzMapCLM ℂ u) (TestFunction.hasCompactSupport_toSchwartzMapCLM (𝕜 := ℂ) u)
    (TestFunction.toSchwartzMapCLM ℂ v) (TestFunction.hasCompactSupport_toSchwartzMapCLM (𝕜 := ℂ) v)
  simpa only [Symbol.quantizeTestFunctionCLM_apply, hu, hv,
    TestFunction.toSchwartzMapCLM_apply] using h

/-- The canonical formal adjoint of a kernel-cutoff symbol is its explicit reversed-conjugate
cutoff symbol. The complex cutoff, real order and support radius are arbitrary. -/
theorem properAdjoint_kernelCutoff_eq {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (a : Symbol n V W m) :
    properAdjoint (kernelCutoff χ a) (hasNearDiagonalKernel_kernelCutoff χ hχR a) =
      adjointKernelCutoff a χ hχ := by
  symm
  refine (eq_properAdjoint_iff (hasNearDiagonalKernel_kernelCutoff χ hχR a)).2 fun u v ↦ ?_
  simpa only [quantizeTestFunctionCLM_apply] using
    integral_inner_quantizeTestFunctionCLM_adjointKernelCutoff hχ hχR a u v

/-- The quantization of the explicit adjoint symbol equals `adjointTestFunctionCLM`
of the kernel-cutoff operator. -/
theorem adjointTestFunctionCLM_kernelCutoff {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (a : Symbol n V W m) :
    Symbol.adjointTestFunctionCLM (Symbol.hasNearDiagonalKernel_kernelCutoff χ hχR a) =
      Symbol.quantizeTestFunctionCLM (hasNearDiagonalKernel_adjointKernelCutoff hχ hχR a) := by
  ext v x
  rw [quantizeTestFunctionCLM_apply, ← properAdjoint_kernelCutoff_eq hχ hχR a,
    quantizeSchwartzValue_properAdjoint]

namespace HasNearDiagonalKernel

/-- The same explicit symbol gives the actual adjoint of any already near-diagonal quantization,
provided the cutoff equals one on its complete propagation ball. -/
theorem adjointTestFunctionCLM_eq_quantizeTestFunctionCLM_adjointKernelCutoff
    {a : Symbol n V W m} (ha : a.HasNearDiagonalKernel R) {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) {R' : ℝ} (hχR' : Function.support χ ⊆ Metric.ball 0 R')
    (hχ₁ : Set.EqOn (χ : CoordinateSpace n → ℂ) 1 (Metric.ball 0 R)) :
    Symbol.adjointTestFunctionCLM ha =
      Symbol.quantizeTestFunctionCLM (hasNearDiagonalKernel_adjointKernelCutoff hχ hχR' a) := by
  have heq : Symbol.properAdjoint (kernelCutoff χ a)
      (hasNearDiagonalKernel_kernelCutoff χ hχR' a) = Symbol.properAdjoint a ha := by
    refine (eq_properAdjoint_iff ha).2 fun u v ↦ ?_
    simpa only [quantizeTestFunctionCLM_apply,
      ha.quantizeSchwartzValue_kernelCutoff_eq χ hχ₁] using
      integral_inner_quantizeTestFunctionCLM_properAdjoint
        (hasNearDiagonalKernel_kernelCutoff χ hχR' a) u v
  ext v x
  rw [quantizeTestFunctionCLM_apply, ← properAdjoint_kernelCutoff_eq hχ hχR' a, heq,
    quantizeSchwartzValue_properAdjoint]

end HasNearDiagonalKernel

/-- The explicit symbol gives the actual Riesz conjugacy square for the native dual-test
  transpose. -/
theorem rieszEquiv_symm_comp_transposeTestFunctionCLM_kernelCutoff
    {χ : 𝓢(CoordinateSpace n, ℂ)} (hχ : HasCompactSupport χ)
    (hχR : Function.support χ ⊆ Metric.ball 0 R) (a : Symbol n V W m) :
    (TestFunction.rieszEquiv (𝕜 := ℂ) (V := V)).symm.toContinuousLinearMap ∘L
        (transposeTestFunctionCLM (hasNearDiagonalKernel_kernelCutoff χ hχR a)).restrictScalars ℝ =
      (quantizeTestFunctionCLM (hasNearDiagonalKernel_adjointKernelCutoff hχ hχR a)).restrictScalars
        ℝ ∘L (TestFunction.rieszEquiv (𝕜 := ℂ) (V := W)).symm.toContinuousLinearMap := by
  ext φ
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearEquiv.coe_coe, transposeTestFunctionCLM_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [adjointTestFunctionCLM_kernelCutoff hχ hχR a]

end NativeTests

section FixedSupport

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m R : ℝ}

/-- The native fixed-stage continuous adjoint is exactly quantization of the explicit symbol. -/
theorem adjointSupportedInCLM_kernelCutoff {χ : 𝓢(CoordinateSpace n, ℂ)}
    (hχ : HasCompactSupport χ) (hχR : Function.support χ ⊆ Metric.ball 0 R)
    (a : Symbol n V W m) (K : Compacts (CoordinateSpace n)) :
    Symbol.adjointSupportedInCLM (Symbol.hasNearDiagonalKernel_kernelCutoff χ hχR a) K =
      Symbol.quantizeSupportedInCLM (hasNearDiagonalKernel_adjointKernelCutoff hχ hχR a) K := by
  apply ContinuousLinearMap.ext
  intro f
  apply ContDiffMapSupportedIn.ext
  intro x
  have hA := congrArg (fun L : 𝓓_{K}(CoordinateSpace n, W) →L[ℂ]
      𝓓((⊤ : Opens (CoordinateSpace n)), V) ↦ L f x)
    (Symbol.ofSupportedInCLM_comp_adjointSupportedInCLM
      (Symbol.hasNearDiagonalKernel_kernelCutoff χ hχR a) K)
  have hQ := congrArg (fun L : 𝓓_{K}(CoordinateSpace n, W) →L[ℂ]
      𝓓((⊤ : Opens (CoordinateSpace n)), V) ↦ L f x)
    (Symbol.ofSupportedInCLM_comp_quantizeSupportedInCLM
      (hasNearDiagonalKernel_adjointKernelCutoff hχ hχR a) K)
  simp only [ContinuousLinearMap.comp_apply, TestFunction.coe_ofSupportedInCLM,
    TestFunction.coe_ofSupportedIn] at hA hQ
  rw [hA, adjointTestFunctionCLM_kernelCutoff hχ hχR a, ← hQ]

end FixedSupport

end TauCeti.Symbol
