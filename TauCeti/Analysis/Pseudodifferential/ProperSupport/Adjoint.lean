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
