/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.InnerPairing
public import TauCeti.Analysis.Distribution.TestFunction.Inner
public import TauCeti.Analysis.Distribution.TestFunction.Schwartz
public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Basic
public import TauCeti.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.SupportedIn
import TauCeti.Analysis.Distribution.TestFunction.Postcomp

/-!
# Properly supported pseudodifferential operators on test functions and distributions

Let `a` be a symbol on `ℝⁿ` whose quantization `Op(a)` has kernel supported within distance `R`
of the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`), such as the kernel cutoff of any
symbol, which every symbol is up to a smoothing symbol
(`TauCeti.Symbol.exists_isSmoothing_sub_and_hasNearDiagonalKernel`). No estimate uniform in the
position is assumed. Such an operator is properly supported, and this file shows the two
consequences that make properly supported operators act on all of `𝓓'(ℝⁿ)`.

* **Test functions.** `Op(a)` sends a test function supported in `K` to a test function supported
  in the closed `R`-neighbourhood of `K`, continuously for the inductive limit topology of
  `𝓓(ℝⁿ)` (`TauCeti.Symbol.quantizeTestFunctionCLM`). The same holds for its formal adjoint
  `Op(a)*`, with values `Op(a)* φ (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ a(y, 2πζ)† φ(y)) (ζ) dζ`
  (`TauCeti.Symbol.adjointTestFunctionCLM`), and `∫ ⟪Op(a) u, φ⟫ = ∫ ⟪u, Op(a)* φ⟫`
  (`TauCeti.Symbol.integral_inner_quantizeTestFunctionCLM`).
* **Distributions.** For a symbol with values in `V →L[ℂ] W`, with `V` and `W` finite-dimensional
  complex inner product spaces, `Op(a)` extends by transposition to `V`-valued distributions
  (`TauCeti.Symbol.quantizeDistribution`): the component of `Op(a) T (φ)` along `w : W` is the
  pairing `⟪Op(a)* (φ • w), T⟫` of `T` with a `V`-valued test function
  (`TauCeti.Symbol.inner_quantizeDistribution_apply`, with the pairing
  `Distribution.innerPairing`). For a scalar symbol this is `(Op(a) T) (φ) = T (Op(a)ᵗ φ)`, with the
  transpose `Op(a)ᵗ φ = conj (Op(a)* φ)` on real test functions
  (`TauCeti.Symbol.quantizeDistribution_apply`). On the distribution of a test function it is the
  distribution of its quantization (`TauCeti.Symbol.quantizeDistribution_ofFun`), and it does not
  enlarge the support of a distribution by more than `R`
  (`TauCeti.Symbol.dsupport_quantizeDistribution_subset`). In a local frame, an operator between
  vector bundles has a matrix-valued symbol, so this is the action of a properly supported operator
  on distributional sections in a chart.
* **The transpose determines the action.** For a scalar symbol, on complex test functions, the
  transpose `Op(a)ᵗ φ = conj (Op(a)* (conj φ))` (`TauCeti.Symbol.scalarTransposeTestFunctionCLM`)
  satisfies
  `∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u` (`TauCeti.Symbol.integral_mul_quantizeTestFunctionCLM`), and it
  is the only continuous function with this property
  (`TauCeti.Symbol.coe_scalarTransposeTestFunctionCLM_eq`). Hence `Op(a)` on distributions only
  depends on the coefficient of `a` (`TauCeti.Symbol.quantizeDistribution_congr`), it is zero if
  `R ≤ 0` (`TauCeti.Symbol.HasNearDiagonalKernel.quantizeDistribution_eq_zero`), and if
  `Op(c) = Op(a) ∘ Op(b)` on test functions, then also on distributions
  (`TauCeti.Symbol.quantizeDistribution_comp`).

* **Fixed supports.** `TauCeti.Symbol.quantizeSupportedInCLM` and
  `TauCeti.Symbol.adjointSupportedInCLM` map stage `K` continuously to its closed `R`-thickening.
  Their `ofSupportedInCLM_comp_*` laws identify these maps with the global test operators.
* **Dual-valued tests.** `TauCeti.Symbol.transposeTestFunctionCLM` transports the formal adjoint
  through the real Riesz equivalence twice, yielding a complex-linear transpose with the spatial
  bilinear identity `TauCeti.Symbol.integral_apply_quantizeTestFunctionCLM`.

On test functions supported in a compact set `K`, the operator `Op(a)` agrees with `Op(ψ a)` for a
cutoff `ψ` equal to `1` near the `R`-neighbourhood of `K`. The symbol `ψ a` has compact spatial
support, so its quantization is continuous on Schwartz space
(`TauCeti.Symbol.quantizeUniformCLM`) and has an adjoint symbol
(`TauCeti.Symbol.adjoint`); this gives the estimates in the seminorms of the test functions
supported in `K`. That the adjoint does not enlarge supports by more than `R` is proved by duality
from the support property of `Op(a)`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §1.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform Set TopologicalSpace
open scoped SchwartzMap ContDiff ComplexConjugate Distributions RealInnerProductSpace
  InnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m R : ℝ}

/-! ### Spatial cutoffs -/

section Cutoff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

private theorem coefficient_cutoff_comp {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (a : Symbol n V W m) (p : CoordinateSpace n × CoordinateSpace n) :
    ((cutoff W hψ).comp a).coefficient p = (ψ p.1 : ℂ) • a.coefficient p := by
  simp [coefficient_comp, Complex.coe_smul]

private theorem hasCompactSpatialSupport_cutoff_comp {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (a : Symbol n V W m) :
    ((cutoff W hψ).comp a).HasCompactSpatialSupport :=
  (hasCompactSpatialSupport_cutoff hψ hψc).comp_right a

private theorem quantizeSchwartzValue_cutoff_comp_apply {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (a : Symbol n V W m) (u : 𝓢(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSchwartzValue ((cutoff W hψ).comp a).coefficient u x =
      (ψ x : ℂ) • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeSchwartzValue_congr_left (b := (ψ x : ℂ) • a.coefficient)
    (fun ξ ↦ coefficient_cutoff_comp hψ a (x, ξ)), quantizeSchwartzValue_smul_left]

/-- If `ψ = 1` on the closed `R`-neighbourhood of the support of `u`, cutting the symbol off by `ψ`
does not change `Op(a) u`: `Op(ψ a) u = Op(a) u`. -/
theorem HasNearDiagonalKernel.quantizeSchwartzValue_cutoff_comp {a : Symbol n V W m}
    (ha : a.HasNearDiagonalKernel R) {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {u : 𝓢(CoordinateSpace n, V)} (hψu : EqOn ψ 1 (Metric.cthickening R (tsupport u))) :
    quantizeSchwartzValue ((cutoff W hψ).comp a).coefficient u =
      quantizeSchwartzValue a.coefficient u := by
  funext x
  rw [Symbol.quantizeSchwartzValue_cutoff_comp_apply]
  by_cases hx : x ∈ Metric.cthickening R (tsupport u)
  · simp [hψu hx]
  · simp [ha.quantizeSchwartzValue_eq_zero_of_notMem hx]

/-- A compact set has a smooth compactly supported cutoff equal to `1` on it. -/
private theorem exists_cutoff (K : Set (CoordinateSpace n)) (hK : IsCompact K) :
    ∃ ψ : CoordinateSpace n → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ EqOn ψ 1 K := by
  obtain ⟨ψ, hψ, -, h1, hc, -⟩ := hK.exists_contDiff_cutoff isOpen_univ (subset_univ K)
  exact ⟨ψ, hψ, hc, fun x hx ↦ by simpa using interior_subset (h1 hx)⟩

end Cutoff

/-! ### The operator on test functions -/

section TestFunction

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-- **Estimates on smooth functions supported in `K`.** For a symbol `b` with estimates uniform in
the position and a compact set `K`, every seminorm `sup ‖D^i Op(b) f‖` of the quantization of
smooth functions `f` supported in `K` is bounded by finitely many of the seminorms `N_j` of
`f`. -/
private theorem IsUniform.exists_norm_iteratedFDeriv_quantize_le {m' : ℝ} {V' W' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W'] [NormedSpace ℂ W']
    {b : Symbol n V' W' m'} (hb : b.IsUniform) (K : Compacts (CoordinateSpace n)) (i : ℕ) :
    ∃ (s : Finset ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓓_{K}(CoordinateSpace n, V')) (x : CoordinateSpace n),
      ‖iteratedFDeriv ℝ i
          (quantizeSchwartzValue b.coefficient (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ f)) x‖ ≤
        C * (s.sup fun j ↦ N[ℂ]_{K, j}) f := by
  -- The seminorm `sup ‖D^i Op(b) f‖` is continuous on the functions supported in `K`.
  set L := quantizeUniformCLM b hb ∘L ContDiffMapSupportedIn.toSchwartzMapCLM ℂ
  set q : Seminorm ℂ 𝓓_{K}(CoordinateSpace n, V') :=
    (SchwartzMap.seminorm ℂ 0 i).comp L.toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ _ _).continuous_seminorm (0, i)).comp L.continuous
  obtain ⟨s, C, -, hC⟩ :=
    Seminorm.bound_of_continuous (ContDiffMapSupportedIn.withSeminorms ℂ _ _ ⊤ K) q hq
  refine ⟨s, C, C.property, fun f x ↦ ?_⟩
  rw [← coe_quantizeUniformCLM b hb]
  exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ _ i x).trans (hC f)

/-- The quantization of a symbol `b` on smooth functions supported in a compact set `K`, with
values in the smooth functions supported in `K'`, given that it vanishes outside `K'` and is
bounded in each seminorm by finitely many of the seminorms on `K`. -/
private def supportedInCLM {m' : ℝ} {V' W' : Type*}
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [NormedAddCommGroup W'] [NormedSpace ℂ W']
    (b : Symbol n V' W' m') {K K' : Compacts (CoordinateSpace n)}
    (hsupp : ∀ f : 𝓓_{K}(CoordinateSpace n, V'),
      EqOn (quantizeSchwartzValue b.coefficient (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ f)) 0
        (K' : Set (CoordinateSpace n))ᶜ)
    (hest : ∀ i : ℕ, ∃ (s : Finset ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (f : 𝓓_{K}(CoordinateSpace n, V')) (x : CoordinateSpace n),
        ‖iteratedFDeriv ℝ i
            (quantizeSchwartzValue b.coefficient (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ f)) x‖ ≤
          C * (s.sup fun j ↦ N[ℂ]_{K, j}) f) :
    𝓓_{K}(CoordinateSpace n, V') →L[ℂ] 𝓓_{K'}(CoordinateSpace n, W') :=
  ContDiffMapSupportedIn.mkCLM ℂ
    (fun f ↦ quantizeSchwartzValue b.coefficient (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ f))
    (fun f g x ↦ by
      obtain ⟨C, -, hC⟩ := b.exists_bound_coefficient_slice x
      rw [map_add, quantizeSchwartzValue_add_right
        (b.continuous_coefficient_slice x).aestronglyMeasurable hC])
    (fun c f x ↦ by rw [map_smul, quantizeSchwartzValue_smul_right])
    (fun f ↦ b.contDiff_quantizeSchwartzValue _) hsupp
    (fun i _ ↦ (hest i).imp fun _ ⟨C, hC0, h⟩ ↦ ⟨C, hC0, fun f x _ ↦ h f x⟩)

/-- The closed `R`-neighbourhood of the support of a function supported in `K`, read as a Schwartz
function, lies in the closed `R`-neighbourhood of `K`. -/
private theorem cthickening_tsupport_toSchwartzMapCLM_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {K : Compacts (CoordinateSpace n)} (f : 𝓓_{K}(CoordinateSpace n, E)) :
    Metric.cthickening R (tsupport (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ f)) ⊆
      K.cthickening R := by
  rw [Compacts.coe_cthickening]
  exact Metric.cthickening_subset_of_subset R (f.tsupport_toSchwartzMapCLM_subset ℂ)

/-- **Estimates on test functions supported in `K`.** On smooth functions supported in a compact
set `K`, the operator `Op(a)` agrees with the quantization of the symbol `ψ a` with compact
spatial support, for a cutoff `ψ` equal to `1` on the `R`-neighbourhood of `K`, so it satisfies
the estimates of `IsUniform.exists_norm_iteratedFDeriv_quantize_le`. -/
private theorem HasNearDiagonalKernel.exists_norm_iteratedFDeriv_le
    (ha : a.HasNearDiagonalKernel R) (K : Compacts (CoordinateSpace n)) (i : ℕ) :
    ∃ (s : Finset ℕ) (C : ℝ), 0 ≤ C ∧ ∀ (f : 𝓓_{K}(CoordinateSpace n, V)) (x : CoordinateSpace n),
      ‖iteratedFDeriv ℝ i
          (quantizeSchwartzValue a.coefficient (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ f)) x‖ ≤
        C * (s.sup fun j ↦ N[ℂ]_{K, j}) f := by
  obtain ⟨ψ, hψ, hψc, hψ1⟩ := exists_cutoff _ (K.cthickening R).isCompact
  obtain ⟨s, C, hC0, hC⟩ := (hasCompactSpatialSupport_cutoff_comp hψ hψc a).isUniform
    |>.exists_norm_iteratedFDeriv_quantize_le K i
  refine ⟨s, C, hC0, fun f x ↦ ?_⟩
  rw [← ha.quantizeSchwartzValue_cutoff_comp hψ (hψ1.mono ?_)]
  · exact hC f x
  · exact cthickening_tsupport_toSchwartzMapCLM_subset f

/-- `Op(a)` on smooth functions supported in a compact set `K`, with values in the smooth functions
supported in the closed `R`-neighbourhood of `K`. -/
def quantizeSupportedInCLM (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) :
    𝓓_{K}(CoordinateSpace n, V) →L[ℂ] 𝓓_{K.cthickening R}(CoordinateSpace n, W) :=
  supportedInCLM a
    (fun f _ hx ↦ ha.quantizeSchwartzValue_eq_zero_of_notMem fun h ↦
      hx (cthickening_tsupport_toSchwartzMapCLM_subset f h))
    (ha.exists_norm_iteratedFDeriv_le K)

/-- Evaluation of quantization between the native fixed-support stages. -/
@[simp]
theorem quantizeSupportedInCLM_apply (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) (f : 𝓓_{K}(CoordinateSpace n, V))
    (x : CoordinateSpace n) :
    quantizeSupportedInCLM ha K f x =
      quantizeSchwartzValue a.coefficient (ContDiffMapSupportedIn.toSchwartzMapCLM ℂ f) x := by
  rfl

/-- **A properly supported operator on test functions.** For a symbol `a` whose quantization has
kernel supported within distance `R` of the diagonal, `u ↦ Op(a) u` as a continuous linear map on
the test functions on `ℝⁿ`, for their inductive limit topology. It does not enlarge supports by
more than `R` (`TauCeti.Symbol.tsupport_quantizeTestFunctionCLM_subset`). -/
def quantizeTestFunctionCLM (ha : a.HasNearDiagonalKernel R) :
    𝓓((⊤ : Opens (CoordinateSpace n)), V) →L[ℂ] 𝓓((⊤ : Opens (CoordinateSpace n)), W) :=
  TestFunction.limitCLM ℂ
    (fun u ↦ ⟨quantizeSchwartzValue a.coefficient (u.hasCompactSupport.toSchwartzMap u.contDiff),
      a.contDiff_quantizeSchwartzValue _,
      u.hasCompactSupport.isCompact.cthickening.of_isClosed_subset (isClosed_tsupport _)
        (ha.tsupport_quantizeSchwartzValue_subset _), subset_univ _⟩)
    (fun K _ ↦ TestFunction.ofSupportedInCLM ℂ (subset_univ _) ∘L quantizeSupportedInCLM ha K)
    (fun _ hK f ↦ TestFunction.ext fun x ↦
      congrArg (quantizeSchwartzValue a.coefficient · x)
        (ContDiffMapSupportedIn.toSchwartzMap_ofSupportedIn ℂ hK f))

/-- The values of `Op(a) u` are the quantization of `u`, read as a Schwartz function. -/
@[simp]
theorem quantizeTestFunctionCLM_apply (ha : a.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) (x : CoordinateSpace n) :
    quantizeTestFunctionCLM ha u x =
      quantizeSchwartzValue a.coefficient (u.hasCompactSupport.toSchwartzMap u.contDiff) x :=
  (rfl)

/-- Fixed-support quantization commutes with the native inclusions into test functions. -/
theorem ofSupportedInCLM_comp_quantizeSupportedInCLM (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) :
    TestFunction.ofSupportedInCLM ℂ (subset_univ (K.cthickening R : Set (CoordinateSpace n))) ∘L
        quantizeSupportedInCLM ha K =
      quantizeTestFunctionCLM ha ∘L TestFunction.ofSupportedInCLM ℂ
        (subset_univ (K : Set (CoordinateSpace n))) := by
  ext f x
  simp only [ContinuousLinearMap.comp_apply, TestFunction.coe_ofSupportedInCLM,
    TestFunction.coe_ofSupportedIn, quantizeSupportedInCLM_apply,
    quantizeTestFunctionCLM_apply]
  exact congrArg (quantizeSchwartzValue a.coefficient · x)
    (ContDiffMapSupportedIn.toSchwartzMap_ofSupportedIn ℂ
      (Ω := (⊤ : Opens (CoordinateSpace n))) (subset_univ _) f).symm

/-- `Op(a) u` is supported in the closed `R`-neighbourhood of the support of `u`. -/
theorem tsupport_quantizeTestFunctionCLM_subset (ha : a.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) :
    tsupport (quantizeTestFunctionCLM ha u) ⊆ Metric.cthickening R (tsupport u) :=
  ha.tsupport_quantizeSchwartzValue_subset _

end TestFunction

/-! ### The formal adjoint on test functions -/

section Adjoint

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- The values `x ↦ ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ a(y, 2πζ)† φ(y)) (ζ) dζ` of the formal adjoint of
`Op(a)` on `φ`. -/
private def adjointValue (a : Symbol n V W m) (φ : CoordinateSpace n → W) (x : CoordinateSpace n) :
    V :=
  ∫ ζ, 𝐞 ⟪ζ, x⟫ • 𝓕 (fun y ↦ ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (φ y)) ζ

private theorem adjointValue_apply (a : Symbol n V W m) (φ : CoordinateSpace n → W)
    (x : CoordinateSpace n) :
    adjointValue a φ x = ∫ ζ, 𝐞 ⟪ζ, x⟫ •
      𝓕 (fun y ↦ ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (φ y)) ζ :=
  rfl

/-- On a Schwartz function `φ` supported where `ψ = 1`, the quantization of the adjoint symbol of
the cutoff `ψ a` is the right quantization of the pointwise adjoint `a(y, ξ)†`. -/
private theorem quantizeSchwartzValue_adjoint_cutoff_comp {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {φ : 𝓢(CoordinateSpace n, W)}
    (hψφ : EqOn ψ 1 (tsupport φ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (adjoint ((cutoff W hψ).comp a)
        (hasCompactSpatialSupport_cutoff_comp hψ hψc a)).coefficient φ x =
      adjointValue a φ x := by
  rw [adjointValue_apply, ← quantizeUniformCLM_apply _ (isUniform_adjoint _ _),
    quantizeUniformCLM_adjoint, quantizeRightUniformCLM_apply]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have h : (fun y ↦ (((cutoff W hψ).comp a).map ContinuousLinearMap.adjointRealCLM).coefficient
      (y, (2 * π) • ζ) (φ y)) =
        fun y ↦ ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (φ y) := by
    funext y
    rw [coefficient_map, ContinuousLinearMap.adjointRealCLM_apply, coefficient_cutoff_comp,
      map_smulₛₗ, Complex.conj_ofReal, smul_apply]
    by_cases hy : φ y = 0
    · simp [hy]
    · simp [hψφ (subset_tsupport _ hy)]
  simp only [h]

/-- **The formal adjoint.** For a compactly supported Schwartz function `φ`, the function
`x ↦ ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ a(y, 2πζ)† φ(y)) (ζ) dζ` is the formal adjoint of `Op(a)` applied
to `φ`. -/
private theorem integral_inner_quantizeSchwartzValue (u : 𝓢(CoordinateSpace n, V))
    {φ : 𝓢(CoordinateSpace n, W)} (hφ : HasCompactSupport φ) :
    ∫ x, inner ℂ (quantizeSchwartzValue a.coefficient u x) (φ x) =
      ∫ x, inner ℂ (u x) (adjointValue a φ x) := by
  obtain ⟨ψ, hψ, hψc, hψ1⟩ := exists_cutoff _ hφ
  -- Where `φ ≠ 0`, the cutoff `ψ` is `1`, so `Op(a) u` may be replaced by `Op(ψ a) u = ψ Op(a) u`.
  have h (x : CoordinateSpace n) : inner ℂ (quantizeSchwartzValue a.coefficient u x) (φ x) =
      inner ℂ (quantizeSchwartzValue ((cutoff W hψ).comp a).coefficient u x) (φ x) := by
    rw [quantizeSchwartzValue_cutoff_comp_apply]
    by_cases hx : φ x = 0
    · simp [hx]
    · simp [hψ1 (subset_tsupport _ hx)]
  simp_rw [h, integral_inner_quantizeSchwartzValue_adjoint _
    (hasCompactSpatialSupport_cutoff_comp hψ hψc a),
    quantizeSchwartzValue_adjoint_cutoff_comp hψ hψc hψ1]

/-- The formal adjoint of `Op(a)` on a compactly supported Schwartz function `φ` is smooth. -/
private theorem contDiff_adjointValue {φ : 𝓢(CoordinateSpace n, W)} (hφ : HasCompactSupport φ) :
    ContDiff ℝ ∞ (adjointValue a φ) := by
  obtain ⟨ψ, hψ, hψc, hψ1⟩ := exists_cutoff _ hφ
  rw [← funext (quantizeSchwartzValue_adjoint_cutoff_comp hψ hψc hψ1)]
  exact contDiff_quantizeSchwartzValue _ _

/-- **Proper support of the formal adjoint.** If the kernel of `Op(a)` is supported within distance
`R` of the diagonal, the formal adjoint of `Op(a)` vanishes outside the closed `R`-neighbourhood of
the support of `φ`. The proof is by duality: `Op(a) u` vanishes on the support of `φ` for every
`u` supported outside that neighbourhood. -/
private theorem HasNearDiagonalKernel.adjointValue_eq_zero (ha : a.HasNearDiagonalKernel R)
    {φ : 𝓢(CoordinateSpace n, W)} (hφ : HasCompactSupport φ) {x₀ : CoordinateSpace n}
    (hx₀ : x₀ ∉ Metric.cthickening R (tsupport φ)) : adjointValue a φ x₀ = 0 := by
  have hgc : Continuous (adjointValue a φ) := (contDiff_adjointValue hφ).continuous
  set U := (Metric.cthickening R (tsupport φ))ᶜ
  have hU : IsOpen U := Metric.isClosed_cthickening.isOpen_compl
  set f : CoordinateSpace n → ℂ := fun x ↦ inner ℂ (adjointValue a φ x₀) (adjointValue a φ x)
  have hfc : Continuous f := continuous_const.inner hgc
  -- `f` integrates to zero against every test function supported in `U`.
  have hzero (χ : CoordinateSpace n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
      (hχU : tsupport χ ⊆ U) : ∫ x, χ x • f x = 0 := by
    let u : 𝓢(CoordinateSpace n, V) := ((hχc.comp_left Complex.ofReal_zero).smul_right
      (f' := fun _ ↦ adjointValue a φ x₀)).toSchwartzMap
        ((Complex.ofRealCLM.contDiff.comp hχ).smul contDiff_const)
    have hu (x : CoordinateSpace n) : u x = (χ x : ℂ) • adjointValue a φ x₀ := rfl
    -- `Op(a) u` vanishes on the support of `φ`, since `u` vanishes near it.
    have hOp (x : CoordinateSpace n) :
        inner ℂ (quantizeSchwartzValue a.coefficient u x) (φ x) = 0 := by
      by_cases hx : x ∈ tsupport φ
      · rw [hasNearDiagonalKernel_iff.1 ha u x fun y hy ↦ ?_, inner_zero_left]
        have hyU : y ∉ tsupport χ := fun h ↦ hχU h
          (Metric.mem_cthickening_of_dist_le y x R _ hx (Metric.mem_ball.1 hy).le)
        rw [hu, image_eq_zero_of_notMem_tsupport hyU, Complex.ofReal_zero, zero_smul]
      · rw [image_eq_zero_of_notMem_tsupport hx, inner_zero_right]
    have h := integral_inner_quantizeSchwartzValue (a := a) u hφ
    simp only [hOp, integral_zero] at h
    refine Eq.trans (integral_congr_ae (.of_forall fun x ↦ ?_)) h.symm
    -- The integrand `χ x • f x` is a `fun` applied to `x`; reduce it to expose the inner product.
    beta_reduce
    rw [Complex.real_smul, hu, inner_smul_left, Complex.conj_ofReal]
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hfc.locallyIntegrable.locallyIntegrableOn U) hzero
  have hEq := Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hU.measurableSet).2 hae) hU
    hfc.continuousOn continuousOn_const
  have h0 : f x₀ = 0 := hEq hx₀
  simpa [f] using h0

/-- The formal adjoint of `Op(a)` does not enlarge supports by more than `R`. -/
private theorem HasNearDiagonalKernel.tsupport_adjointValue_subset (ha : a.HasNearDiagonalKernel R)
    {φ : 𝓢(CoordinateSpace n, W)} (hφ : HasCompactSupport φ) :
    tsupport (adjointValue a φ) ⊆ Metric.cthickening R (tsupport φ) :=
  closure_minimal (fun _ hx ↦ by_contra fun h ↦ hx (ha.adjointValue_eq_zero hφ h))
    Metric.isClosed_cthickening

/-- `Op(a)*` on smooth functions supported in a compact set `K`, through the adjoint symbol of
the cutoff `ψ a` for a `ψ` equal to `1` on `K`. -/
def adjointSupportedInCLM (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) :
    𝓓_{K}(CoordinateSpace n, W) →L[ℂ] 𝓓_{K.cthickening R}(CoordinateSpace n, V) :=
  have hψ := (exists_cutoff (n := n) K K.isCompact).choose_spec
  supportedInCLM
    (adjoint ((cutoff W hψ.1).comp a) (hasCompactSpatialSupport_cutoff_comp hψ.1 hψ.2.1 a))
    (fun f x hx ↦ by
      have hf := f.tsupport_toSchwartzMapCLM_subset ℂ
      rw [quantizeSchwartzValue_adjoint_cutoff_comp hψ.1 hψ.2.1 (hψ.2.2.mono hf)]
      refine ha.adjointValue_eq_zero (K.isCompact.of_isClosed_subset (isClosed_tsupport _) hf)
        fun h ↦ hx (cthickening_tsupport_toSchwartzMapCLM_subset f h))
    ((isUniform_adjoint _ _).exists_norm_iteratedFDeriv_quantize_le K)

/-- Evaluation of the formal adjoint between native fixed-support stages. -/
@[simp]
theorem adjointSupportedInCLM_apply (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) (f : 𝓓_{K}(CoordinateSpace n, W))
    (x : CoordinateSpace n) :
    adjointSupportedInCLM ha K f x = ∫ ζ, 𝐞 ⟪ζ, x⟫ •
      𝓕 (fun y ↦ ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (f y)) ζ := by
  have hψ := (exists_cutoff (n := n) K K.isCompact).choose_spec
  have hf := f.tsupport_toSchwartzMapCLM_subset ℂ
  have h := quantizeSchwartzValue_adjoint_cutoff_comp (a := a) hψ.1 hψ.2.1
    (hψ.2.2.mono hf) x
  rw [ContDiffMapSupportedIn.coe_toSchwartzMapCLM] at h
  exact h

/-- **The formal adjoint of a properly supported operator on test functions.** For a symbol `a`
whose quantization has kernel supported within distance `R` of the diagonal, the formal adjoint
`Op(a)*` of `Op(a)`, with values
`Op(a)* φ (x) = ∫ exp(2πi ⟪ζ, x⟫) 𝓕 (y ↦ a(y, 2πζ)† φ(y)) (ζ) dζ`
(`TauCeti.Symbol.adjointTestFunctionCLM_apply`), as a continuous linear map on the test functions
on `ℝⁿ`. In angular frequency it is the right quantization
`(2π)⁻ⁿ ∫∫ exp(i ⟪x - y, ξ⟫) a(y, ξ)† φ(y) dy dξ` of the pointwise adjoint. It is the formal
adjoint of `TauCeti.Symbol.quantizeTestFunctionCLM`
(`TauCeti.Symbol.integral_inner_quantizeTestFunctionCLM`) and does not enlarge supports by more
than `R` (`TauCeti.Symbol.tsupport_adjointTestFunctionCLM_subset`). -/
def adjointTestFunctionCLM (ha : a.HasNearDiagonalKernel R) :
    𝓓((⊤ : Opens (CoordinateSpace n)), W) →L[ℂ] 𝓓((⊤ : Opens (CoordinateSpace n)), V) :=
  TestFunction.limitCLM ℂ
    (fun φ ↦ ⟨adjointValue a φ,
      contDiff_adjointValue (φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff) φ.hasCompactSupport,
      φ.hasCompactSupport.isCompact.cthickening.of_isClosed_subset (isClosed_tsupport _)
        (ha.tsupport_adjointValue_subset (φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff)
          φ.hasCompactSupport),
      subset_univ _⟩)
    (fun K _ ↦ TestFunction.ofSupportedInCLM ℂ (subset_univ _) ∘L adjointSupportedInCLM ha K)
    (fun K _ f ↦ TestFunction.ext fun x ↦ by
      have hψ := (exists_cutoff (n := n) K K.isCompact).choose_spec
      have hf := f.tsupport_toSchwartzMapCLM_subset ℂ
      have h := quantizeSchwartzValue_adjoint_cutoff_comp (a := a) hψ.1 hψ.2.1 (hψ.2.2.mono hf) x
      rw [ContDiffMapSupportedIn.coe_toSchwartzMapCLM] at h
      -- Both sides are `Op(a)* f (x)`: `ofSupportedIn` does not change the function.
      exact h.symm)

/-- The values of the formal adjoint `Op(a)* φ`. -/
@[simp]
theorem adjointTestFunctionCLM_apply (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) (x : CoordinateSpace n) :
    adjointTestFunctionCLM ha φ x = ∫ ζ, 𝐞 ⟪ζ, x⟫ •
      𝓕 (fun y ↦ ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (φ y)) ζ :=
  adjointValue_apply a φ x

/-- Fixed-support adjunction commutes with the native inclusions into test functions. -/
theorem ofSupportedInCLM_comp_adjointSupportedInCLM (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) :
    TestFunction.ofSupportedInCLM ℂ (subset_univ (K.cthickening R : Set (CoordinateSpace n))) ∘L
        adjointSupportedInCLM ha K =
      adjointTestFunctionCLM ha ∘L TestFunction.ofSupportedInCLM ℂ
        (subset_univ (K : Set (CoordinateSpace n))) := by
  ext f x
  simp only [ContinuousLinearMap.comp_apply, TestFunction.coe_ofSupportedInCLM,
    TestFunction.coe_ofSupportedIn, adjointSupportedInCLM_apply,
    adjointTestFunctionCLM_apply]

/-- `Op(a)* φ` is supported in the closed `R`-neighbourhood of the support of `φ`. -/
theorem tsupport_adjointTestFunctionCLM_subset (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) :
    tsupport (adjointTestFunctionCLM ha φ) ⊆ Metric.cthickening R (tsupport φ) :=
  ha.tsupport_adjointValue_subset (φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff)
    φ.hasCompactSupport

/-- **`Op(a)*` is the formal adjoint of `Op(a)`**: `∫ ⟪Op(a) u, φ⟫ = ∫ ⟪u, Op(a)* φ⟫` for all test
functions `u` and `φ`. -/
theorem integral_inner_quantizeTestFunctionCLM (ha : a.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), W)) :
    ∫ x, inner ℂ (quantizeTestFunctionCLM ha u x) (φ x) =
      ∫ x, inner ℂ (u x) (adjointTestFunctionCLM ha φ x) :=
  integral_inner_quantizeSchwartzValue (u.hasCompactSupport.toSchwartzMap u.contDiff)
    (φ := φ.hasCompactSupport.toSchwartzMap φ.contDiff) φ.hasCompactSupport

/-- The complex-bilinear transpose on original dual-valued test functions.
Two conjugate-linear Riesz transports give complex linearity, using the existing native
formal adjoint and its original test-function topology. -/
def transposeTestFunctionCLM (ha : a.HasNearDiagonalKernel R) :
    𝓓((⊤ : Opens (CoordinateSpace n)), StrongDual ℂ W) →L[ℂ]
      𝓓((⊤ : Opens (CoordinateSpace n)), StrongDual ℂ V) where
  toFun φ := TestFunction.rieszEquiv (𝕜 := ℂ) (adjointTestFunctionCLM ha
    ((TestFunction.rieszEquiv (𝕜 := ℂ) (V := W)).symm φ))
  map_add' φ ψ := by rw [map_add, map_add, map_add]
  map_smul' c φ := by
    rw [TestFunction.rieszEquiv_symm_smul, map_smul, TestFunction.rieszEquiv_smul]
    simp only [starRingEnd_self_apply, RingHom.id_apply]
  cont := (TestFunction.rieszEquiv (𝕜 := ℂ) (V := V)).continuous.comp
    ((adjointTestFunctionCLM ha).continuous.comp
      (TestFunction.rieszEquiv (𝕜 := ℂ) (V := W)).symm.continuous)

/-- The native transpose is Riesz transport of the actual native formal adjoint. -/
@[simp]
theorem transposeTestFunctionCLM_apply (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), StrongDual ℂ W)) :
    transposeTestFunctionCLM ha φ = TestFunction.rieszEquiv (𝕜 := ℂ)
      (adjointTestFunctionCLM ha ((TestFunction.rieszEquiv (𝕜 := ℂ) (V := W)).symm φ)) := by
  rfl

/-- The dual-valued native transpose has the spatial complex-bilinear pairing identity. -/
theorem integral_apply_quantizeTestFunctionCLM (ha : a.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V))
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), StrongDual ℂ W)) :
    (∫ x, φ x (quantizeTestFunctionCLM ha u x)) =
      ∫ x, transposeTestFunctionCLM ha φ x (u x) := by
  have h := integral_inner_quantizeTestFunctionCLM ha u
    ((TestFunction.rieszEquiv (𝕜 := ℂ) (V := W)).symm φ)
  have hc := congrArg (starRingEnd ℂ) h
  rw [← integral_conj, ← integral_conj] at hc
  simp only [inner_conj_symm, TestFunction.rieszEquiv_symm_apply (V := W)] at hc
  simpa only [transposeTestFunctionCLM_apply, TestFunction.rieszEquiv_apply] using hc

end Adjoint

/-! ### Distributions -/

section Distribution

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W] {a : Symbol n V W m}

/-- **A properly supported operator on distributions.** For a symbol `a` with values in
`V →L[ℂ] W`, for finite-dimensional complex inner product spaces `V` and `W`, whose quantization
has kernel supported within distance `R` of the diagonal, `Op(a)` acts on all `V`-valued
distributions on `ℝⁿ` by transposition:

`⟪w, (Op(a) T) (φ)⟫ = ⟪Op(a)* (φ • w), T⟫`

for real test functions `φ` and vectors `w : W`, where `Op(a)*` is the formal adjoint
`TauCeti.Symbol.adjointTestFunctionCLM` and the right side is the pairing
`Distribution.innerPairing` of `T` with a `V`-valued test function
(`TauCeti.Symbol.inner_quantizeDistribution_apply`). It is complex linear, and it extends `Op(a)`
on test functions (`TauCeti.Symbol.quantizeDistribution_ofFun`). For a scalar symbol it is
`(Op(a) T) (φ) = T (Op(a)ᵗ φ)`, with the transpose `Op(a)ᵗ φ = conj (Op(a)* φ)` of `Op(a)` for the
bilinear pairing `∫ φ u` (`TauCeti.Symbol.quantizeDistribution_apply`). It is defined in an
orthonormal basis `(wₖ)` of `W`: the `k`-th coordinate of `Op(a) T` is the distribution
`φ ↦ ⟪Op(a)* (φ • wₖ), T⟫`. -/
def quantizeDistribution (ha : a.HasNearDiagonalKernel R) :
    𝓓'((⊤ : Opens (CoordinateSpace n)), V) →L[ℂ] 𝓓'((⊤ : Opens (CoordinateSpace n)), W) :=
  ∑ k, Distribution.smulRightCLM (stdOrthonormalBasis ℂ W k) ∘L
    Distribution.innerPairingCLM ((adjointTestFunctionCLM ha).restrictScalars ℝ ∘L
      TestFunction.postcompCLM (𝕜 := ℝ)
        (ContinuousLinearMap.toSpanSingleton ℝ (stdOrthonormalBasis ℂ W k)))

/-- **`Op(a)` on distributions is the transpose of the formal adjoint**: the component of
`Op(a) T (φ)` along `w` is the pairing of `T` with `Op(a)* (φ • w)`. -/
@[simp]
theorem inner_quantizeDistribution_apply (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ))
    (w : W) :
    ⟪w, quantizeDistribution ha T φ⟫_ℂ = T.innerPairing (adjointTestFunctionCLM ha
      (TestFunction.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ w) φ)) := by
  set b := stdOrthonormalBasis ℂ W
  -- Expand `φ • w` in the basis: `φ • w = ∑ₖ ⟪wₖ, w⟫ (φ • wₖ)`.
  have hw : TestFunction.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ w) φ =
      ∑ k, ⟪b k, w⟫_ℂ • TestFunction.postcompCLM (𝕜 := ℝ)
        (ContinuousLinearMap.toSpanSingleton ℝ (b k)) φ := by
    ext x
    simp only [TestFunction.postcompCLM_apply, Function.comp_apply, sum_apply, smul_apply,
      ContinuousLinearMap.toSpanSingleton_apply]
    conv_lhs => rw [← b.sum_repr' w, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ smul_comm _ _ _
  rw [hw, map_sum, Distribution.innerPairing_sum_right]
  simp only [quantizeDistribution, sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [b, inner_smul_right, inner_conj_symm, mul_comm]

/-- `Op(a) T (φ)` in an orthonormal basis `(wₖ)` of `W`: its coordinates are the pairings of `T`
with `Op(a)* (φ • wₖ)`. -/
theorem quantizeDistribution_apply_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ W)
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V))
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
    quantizeDistribution ha T φ = ∑ k, T.innerPairing (adjointTestFunctionCLM ha
      (TestFunction.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ (b k)) φ)) •
        b k := by
  conv_lhs => rw [← b.sum_repr' (quantizeDistribution ha T φ)]
  simp only [inner_quantizeDistribution_apply]

/-- **`Op(a)` on distributions extends `Op(a)` on test functions**: on the distribution of a test
function `u`, it is the distribution of `Op(a) u`. -/
@[simp]
theorem quantizeDistribution_ofFun (ha : a.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), V)) :
    quantizeDistribution ha (Distribution.ofFun ⊤ u volume ⊤) =
      Distribution.ofFun ⊤ (quantizeTestFunctionCLM ha u) volume ⊤ := by
  ext φ
  refine ext_inner_left ℂ fun w ↦ ?_
  set φw := TestFunction.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ w) φ
  have hint : Integrable fun x ↦ φ x • quantizeTestFunctionCLM ha u x :=
    (φ.continuous.smul (quantizeTestFunctionCLM ha u).continuous).integrable_of_hasCompactSupport
      φ.hasCompactSupport.smul_right
  rw [inner_quantizeDistribution_apply,
    Distribution.innerPairing_ofFun (u.continuous.locallyIntegrable.locallyIntegrableOn _),
    Distribution.ofFun_apply
      ((quantizeTestFunctionCLM ha u).continuous.locallyIntegrable.locallyIntegrableOn _),
    ← integral_inner hint]
  -- Conjugating the adjoint identity `∫ ⟪Op(a) u, φ • w⟫ = ∫ ⟪u, Op(a)* (φ • w)⟫`.
  have h := congrArg (starRingEnd ℂ) (integral_inner_quantizeTestFunctionCLM ha u φw)
  rw [← integral_conj, ← integral_conj] at h
  simp only [inner_conj_symm] at h
  refine h.symm.trans (integral_congr_ae (.of_forall fun x ↦ ?_))
  simp [φw, ← Complex.coe_smul, inner_smul_left, inner_smul_right]

/-- **Proper support on distributions.** `Op(a) T` is supported in the closed `R`-neighbourhood of
the support of `T`. -/
theorem dsupport_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    Distribution.dsupport (quantizeDistribution ha T) ⊆
      Metric.cthickening R (Distribution.dsupport T) := by
  have hU : IsOpen (Metric.cthickening R (Distribution.dsupport T))ᶜ :=
    Metric.isClosed_cthickening.isOpen_compl
  -- `Op(a) T` vanishes on test functions supported away from the `R`-neighbourhood of `supp T`.
  have h : Distribution.IsVanishingOn (quantizeDistribution ha T)
      (Metric.cthickening R (Distribution.dsupport T))ᶜ := by
    intro φ hφ
    refine ext_inner_left ℂ fun w ↦ ?_
    rw [inner_quantizeDistribution_apply, inner_zero_right]
    refine T.innerPairing_eq_zero_of_disjoint ?_
    have hψ : tsupport (adjointTestFunctionCLM ha
        (TestFunction.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ w) φ)) ⊆
          Metric.cthickening R (tsupport φ) := by
      refine (tsupport_adjointTestFunctionCLM_subset ha _).trans
        (Metric.cthickening_subset_of_subset R ?_)
      rw [TestFunction.postcompCLM_apply]
      exact tsupport_comp_subset (map_zero _) _
    exact (φ.hasCompactSupport.isCompact.disjoint_cthickening_left
      (subset_compl_iff_disjoint_right.1 hφ)).mono_left hψ
  simpa using (h.disjoint_dsupport hU).subset_compl_left

end Distribution

/-! ### Scalar symbols -/

section Scalar

variable {a : Symbol n ℂ ℂ m} {m' m'' R' R'' : ℝ}

/-- **The transpose of a properly supported operator** on complex test functions,
`Op(a)ᵗ φ = conj (Op(a)* (conj φ))`. It is the transpose of `Op(a)` for the bilinear pairing
`∫ φ u` (`TauCeti.Symbol.integral_mul_quantizeTestFunctionCLM`), and the only continuous function
with this property (`TauCeti.Symbol.coe_scalarTransposeTestFunctionCLM_eq`). `Op(a)` acts on
distributions by it (`TauCeti.Symbol.complexPairing_quantizeDistribution`). -/
def scalarTransposeTestFunctionCLM (ha : a.HasNearDiagonalKernel R) :
    𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) →L[ℂ] 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) where
  toFun φ := TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
    (adjointTestFunctionCLM ha
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap φ))
  map_add' φ ψ := by simp
  map_smul' c φ := by
    have h : TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap (c • φ) =
        conj c • TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap φ := by
      ext x
      simp
    rw [h, map_smul]
    ext x
    simp
  cont := (TestFunction.postcompCLM _).continuous.comp
    ((adjointTestFunctionCLM ha).continuous.comp (TestFunction.postcompCLM _).continuous)

/-- The transpose is `Op(a)ᵗ φ = conj (Op(a)* (conj φ))`, as test functions. -/
theorem scalarTransposeTestFunctionCLM_def (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    scalarTransposeTestFunctionCLM ha φ = TestFunction.postcompCLM (𝕜 := ℝ)
      Complex.conjCLE.toContinuousLinearMap (adjointTestFunctionCLM ha
        (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap φ)) :=
  (rfl)

/-- The values `Op(a)ᵗ φ (x) = conj (Op(a)* (conj φ) (x))` of the transpose. -/
@[simp]
theorem scalarTransposeTestFunctionCLM_apply (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) (x : CoordinateSpace n) :
    scalarTransposeTestFunctionCLM ha φ x = conj (adjointTestFunctionCLM ha
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap φ) x) := by
  simp [scalarTransposeTestFunctionCLM_def]

/-- For a scalar symbol, `Op(a) T` pairs with a real test function `φ` as `T` with the transpose
`conj (Op(a)* φ)`. -/
@[simp]
theorem quantizeDistribution_apply (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
    quantizeDistribution ha T φ = T.complexPairing
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
        (adjointTestFunctionCLM ha (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ))) := by
  have h := inner_quantizeDistribution_apply ha T φ 1
  have hφ : TestFunction.postcompCLM (𝕜 := ℝ) (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℂ)) φ =
      TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ := by
    ext x
    simp
  rw [hφ, Distribution.innerPairing_eq_complexPairing] at h
  simpa [RCLike.inner_apply] using h

/-- The complex-linear extension of `Op(a) T` pairs with a complex test function `ψ` as `T` with
the transpose `Op(a)ᵗ ψ = conj (Op(a)* (conj ψ))`
(`TauCeti.Symbol.scalarTransposeTestFunctionCLM`). -/
@[simp]
theorem complexPairing_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) (ψ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).complexPairing ψ =
      T.complexPairing (scalarTransposeTestFunctionCLM ha ψ) := by
  rw [scalarTransposeTestFunctionCLM_def]
  have hconj (φ φ' : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
      TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
          (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ +
            Complex.I • TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ') =
        TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ -
          Complex.I • TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ' := by
    ext x
    simp [sub_eq_add_neg]
  have hconj' (f g : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
      TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
          (f - Complex.I • g) =
        TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap f +
          Complex.I •
            TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap g := by
    ext x
    simp
  -- Split `ψ` into its real and imaginary parts, on which `Op(a) T` is given by its definition.
  rw [← TestFunction.postcompCLM_re_add_I_smul_im ψ, hconj, map_sub, map_smul, hconj']
  simp only [map_add, map_smul, Distribution.complexPairing_postcompCLM_ofRealCLM,
    quantizeDistribution_apply, smul_eq_mul]

/-- `Op(a) T` pairs with a real test function `φ` as `T` with the transpose `Op(a)ᵗ φ`
(`TauCeti.Symbol.scalarTransposeTestFunctionCLM`) of `φ` read as a complex test function. -/
theorem quantizeDistribution_apply_eq_complexPairing (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
    quantizeDistribution ha T φ =
      T.complexPairing (scalarTransposeTestFunctionCLM ha (TestFunction.postcompCLM (𝕜 := ℝ)
        Complex.ofRealCLM φ)) := by
  rw [← Distribution.complexPairing_postcompCLM_ofRealCLM, complexPairing_quantizeDistribution]

/-- **The transpose identity on test functions.** `∫ φ · Op(a) u = ∫ Op(a)ᵗ φ · u`. -/
theorem integral_mul_quantizeTestFunctionCLM (ha : a.HasNearDiagonalKernel R)
    (u φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    ∫ x, φ x * quantizeTestFunctionCLM ha u x =
      ∫ x, scalarTransposeTestFunctionCLM ha φ x * u x := by
  -- Pair `Op(a)` on the distribution of `u`, which is the distribution of `Op(a) u`, with `φ`.
  have hloc (f : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
      LocallyIntegrableOn f (⊤ : Opens (CoordinateSpace n)) volume :=
    f.continuous.locallyIntegrable.locallyIntegrableOn _
  have h := congrArg (Distribution.complexPairing · φ) (quantizeDistribution_ofFun ha u)
  simp only [complexPairing_quantizeDistribution, Distribution.complexPairing_ofFun (hloc _)] at h
  exact h.symm

/-- **Uniqueness of the transpose.** A continuous function `f` with `∫ φ · Op(a) u = ∫ f u` for
every test function `u` is the transpose `Op(a)ᵗ φ`. -/
theorem coe_scalarTransposeTestFunctionCLM_eq (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) {f : CoordinateSpace n → ℂ} (hf : Continuous f)
    (h : ∀ u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ),
      ∫ x, φ x * quantizeTestFunctionCLM ha u x = ∫ x, f x * u x) :
    ⇑(scalarTransposeTestFunctionCLM ha φ) = f := by
  refine (Continuous.ae_eq_iff_eq volume (scalarTransposeTestFunctionCLM ha φ).continuous hf).1
    (ae_eq_of_integral_contDiff_smul_eq
      (scalarTransposeTestFunctionCLM ha φ).continuous.locallyIntegrable
      hf.locallyIntegrable fun g hg hgc ↦ ?_)
  -- Test against the complex test function `g`.
  let u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
    ⟨fun x ↦ (g x : ℂ), Complex.ofRealCLM.contDiff.comp hg, hgc.comp_left Complex.ofReal_zero,
      subset_univ _⟩
  have hu : ⇑u = fun x ↦ (g x : ℂ) := TestFunction.coe_mk
  have h' := (integral_mul_quantizeTestFunctionCLM ha u φ).symm.trans (h u)
  simpa [hu, Complex.real_smul, mul_comm] using h'

/-- `Op(a)` on distributions only depends on the coefficient of `a`. -/
theorem quantizeDistribution_congr {b : Symbol n ℂ ℂ m'} (ha : a.HasNearDiagonalKernel R)
    (hb : b.HasNearDiagonalKernel R') (h : a.coefficient = b.coefficient) :
    quantizeDistribution ha = quantizeDistribution hb := by
  ext T φ
  simp only [quantizeDistribution_apply]
  congr 2
  exact TestFunction.ext fun x ↦ by simp [h]

/-- **A kernel supported within a nonpositive distance of the diagonal is zero**, also on
distributions: the operator `Op(a)` then vanishes on every test function. -/
theorem HasNearDiagonalKernel.quantizeDistribution_eq_zero (ha : a.HasNearDiagonalKernel R)
    (hR : R ≤ 0) : quantizeDistribution ha = 0 := by
  have h0 (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) : scalarTransposeTestFunctionCLM ha φ = 0 :=
    DFunLike.coe_injective <| coe_scalarTransposeTestFunctionCLM_eq ha φ continuous_const fun u ↦ by
      have hu (x : CoordinateSpace n) : quantizeTestFunctionCLM ha u x = 0 := by
        rw [quantizeTestFunctionCLM_apply]
        exact hasNearDiagonalKernel_iff.1 ha _ x fun y hy ↦
          absurd hy (by simp [Metric.ball_eq_empty.2 hR])
      simp [hu]
  ext T φ
  rw [quantizeDistribution_apply_eq_complexPairing, h0]
  simp

/-- **Composition on distributions.** If `Op(c) = Op(a) ∘ Op(b)` on test functions, then
`Op(c) = Op(a) ∘ Op(b)` on distributions. -/
theorem quantizeDistribution_comp {b : Symbol n ℂ ℂ m'} {c : Symbol n ℂ ℂ m''}
    (ha : a.HasNearDiagonalKernel R) (hb : b.HasNearDiagonalKernel R')
    (hc : c.HasNearDiagonalKernel R'')
    (h : ∀ u, quantizeTestFunctionCLM hc u =
      quantizeTestFunctionCLM ha (quantizeTestFunctionCLM hb u))
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    quantizeDistribution hc T = quantizeDistribution ha (quantizeDistribution hb T) := by
  -- The transposes compose in the opposite order: `Op(c)ᵗ = Op(b)ᵗ ∘ Op(a)ᵗ`.
  have ht (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
      scalarTransposeTestFunctionCLM hc φ =
        scalarTransposeTestFunctionCLM hb (scalarTransposeTestFunctionCLM ha φ) :=
    DFunLike.coe_injective <| coe_scalarTransposeTestFunctionCLM_eq hc φ
      (scalarTransposeTestFunctionCLM hb _).continuous fun u ↦ by
        rw [h, integral_mul_quantizeTestFunctionCLM, integral_mul_quantizeTestFunctionCLM]
  ext φ
  rw [quantizeDistribution_apply_eq_complexPairing, quantizeDistribution_apply_eq_complexPairing,
    complexPairing_quantizeDistribution, ht]

end Scalar

end Symbol

end TauCeti
