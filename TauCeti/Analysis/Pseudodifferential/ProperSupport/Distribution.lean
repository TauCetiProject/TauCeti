/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.SchwartzSpace.SupportedIn
import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import TauCeti.Topology.MetricSpace.Thickening

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
* **Distributions.** For a scalar symbol, `Op(a)` extends by transposition to distributions,
  `(Op(a) T) (φ) = T (Op(a)ᵗ φ)` with the transpose `Op(a)ᵗ φ = conj (Op(a)* φ)` on real test
  functions (`TauCeti.Symbol.quantizeDistribution`). On the distribution of a test function it is
  the distribution of its quantization (`TauCeti.Symbol.quantizeDistribution_ofFun`), and it does
  not enlarge the support of a distribution by more than `R`
  (`TauCeti.Symbol.dsupport_quantizeDistribution_subset`).

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
open scoped SchwartzMap ContDiff Distributions RealInnerProductSpace

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m R : ℝ}

/-! ### Spatial cutoffs -/

section Cutoff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

/-- If `ψ = 1` on the closed `R`-neighbourhood of the support of `u`, cutting the symbol off by `ψ`
does not change `Op(a) u`. -/
private theorem HasNearDiagonalKernel.quantizeSchwartzValue_smulLeft_eq {a : Symbol n V W m}
    (ha : a.HasNearDiagonalKernel R) {ψ : CoordinateSpace n → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {u : 𝓢(CoordinateSpace n, V)} (hψu : EqOn ψ 1 (Metric.cthickening R (tsupport u))) :
    quantizeSchwartzValue (smulLeft hψ a).coefficient u =
      quantizeSchwartzValue a.coefficient u := by
  funext x
  rw [Symbol.quantizeSchwartzValue_smulLeft]
  by_cases hx : x ∈ Metric.cthickening R (tsupport u)
  · simp [hψu hx]
  · simp [ha.quantizeSchwartzValue_eq_zero_of_notMem hx]

/-- A compact set has a smooth compactly supported cutoff equal to `1` on it. -/
private theorem exists_cutoff (K : Set (CoordinateSpace n)) (hK : IsCompact K) :
    ∃ ψ : CoordinateSpace n → ℂ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ EqOn ψ 1 K := by
  obtain ⟨ψ, hψ, -, h1, hc, -⟩ := hK.exists_contDiff_cutoff isOpen_univ (subset_univ K)
  exact ⟨fun x ↦ ψ x, Complex.ofRealCLM.contDiff.comp hψ, hc.comp_left Complex.ofReal_zero,
    fun x hx ↦ by simpa using interior_subset (h1 hx)⟩

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
  obtain ⟨s, C, hC0, hC⟩ := (hasCompactSpatialSupport_smulLeft hψ hψc a).isUniform
    |>.exists_norm_iteratedFDeriv_quantize_le K i
  refine ⟨s, C, hC0, fun f x ↦ ?_⟩
  rw [← ha.quantizeSchwartzValue_smulLeft_eq hψ (hψ1.mono ?_)]
  · exact hC f x
  · exact cthickening_tsupport_toSchwartzMapCLM_subset f

/-- `Op(a)` on smooth functions supported in a compact set `K`, with values in the smooth functions
supported in the closed `R`-neighbourhood of `K`. -/
private def quantizeSupportedInCLM (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) :
    𝓓_{K}(CoordinateSpace n, V) →L[ℂ] 𝓓_{K.cthickening R}(CoordinateSpace n, W) :=
  supportedInCLM a
    (fun f _ hx ↦ ha.quantizeSchwartzValue_eq_zero_of_notMem fun h ↦
      hx (cthickening_tsupport_toSchwartzMapCLM_subset f h))
    (ha.exists_norm_iteratedFDeriv_le K)

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
private theorem quantizeSchwartzValue_adjoint_smulLeft {ψ : CoordinateSpace n → ℂ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {φ : 𝓢(CoordinateSpace n, W)}
    (hψφ : EqOn ψ 1 (tsupport φ)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (adjoint (smulLeft hψ a)
        (hasCompactSpatialSupport_smulLeft hψ hψc a)).coefficient φ x =
      adjointValue a φ x := by
  rw [adjointValue_apply, ← quantizeUniformCLM_apply _ (isUniform_adjoint _ _),
    quantizeUniformCLM_adjoint, quantizeRightUniformCLM_apply]
  refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
  have h : (fun y ↦ ((smulLeft hψ a).map ContinuousLinearMap.adjointRealCLM).coefficient
      (y, (2 * π) • ζ) (φ y)) =
        fun y ↦ ContinuousLinearMap.adjoint (a.coefficient (y, (2 * π) • ζ)) (φ y) := by
    funext y
    rw [coefficient_map, ContinuousLinearMap.adjointRealCLM_apply, coefficient_smulLeft,
      map_smulₛₗ, smul_apply]
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
      inner ℂ (quantizeSchwartzValue (smulLeft hψ a).coefficient u x) (φ x) := by
    rw [quantizeSchwartzValue_smulLeft]
    by_cases hx : φ x = 0
    · simp [hx]
    · simp [hψ1 (subset_tsupport _ hx)]
  simp_rw [h, integral_inner_quantizeSchwartzValue_adjoint _
    (hasCompactSpatialSupport_smulLeft hψ hψc a),
    quantizeSchwartzValue_adjoint_smulLeft hψ hψc hψ1]

/-- The formal adjoint of `Op(a)` on a compactly supported Schwartz function `φ` is smooth. -/
private theorem contDiff_adjointValue {φ : 𝓢(CoordinateSpace n, W)} (hφ : HasCompactSupport φ) :
    ContDiff ℝ ∞ (adjointValue a φ) := by
  obtain ⟨ψ, hψ, hψc, hψ1⟩ := exists_cutoff _ hφ
  rw [← funext (quantizeSchwartzValue_adjoint_smulLeft hψ hψc hψ1)]
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
private def adjointSupportedInCLM (ha : a.HasNearDiagonalKernel R)
    (K : Compacts (CoordinateSpace n)) :
    𝓓_{K}(CoordinateSpace n, W) →L[ℂ] 𝓓_{K.cthickening R}(CoordinateSpace n, V) :=
  have hψ := (exists_cutoff (n := n) K K.isCompact).choose_spec
  supportedInCLM
    (adjoint (smulLeft hψ.1 a) (hasCompactSpatialSupport_smulLeft hψ.1 hψ.2.1 a))
    (fun f x hx ↦ by
      have hf := f.tsupport_toSchwartzMapCLM_subset ℂ
      rw [quantizeSchwartzValue_adjoint_smulLeft hψ.1 hψ.2.1 (hψ.2.2.mono hf)]
      refine ha.adjointValue_eq_zero (K.isCompact.of_isClosed_subset (isClosed_tsupport _) hf)
        fun h ↦ hx (cthickening_tsupport_toSchwartzMapCLM_subset f h))
    ((isUniform_adjoint _ _).exists_norm_iteratedFDeriv_quantize_le K)

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
      have h := quantizeSchwartzValue_adjoint_smulLeft (a := a) hψ.1 hψ.2.1 (hψ.2.2.mono hf) x
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

end Adjoint

/-! ### Distributions -/

section Distribution

variable {a : Symbol n ℂ ℂ m}

/-- The transpose `φ ↦ conj (Op(a)* φ)` of `Op(a)` for the bilinear pairing `∫ φ u`, on real test
functions. -/
private def transposeCLM (ha : a.HasNearDiagonalKernel R) :
    𝓓((⊤ : Opens (CoordinateSpace n)), ℝ) →L[ℝ] 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
  TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap ∘L
    (adjointTestFunctionCLM ha).restrictScalars ℝ ∘L
      TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

/-- `Op(a)` on distributions as a real linear map: `T` applied to the real and imaginary parts of
the transpose `conj (Op(a)* φ)` of a real test function `φ`. -/
private def quantizeDistributionReal (ha : a.HasNearDiagonalKernel R) :
    𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ) →L[ℝ] 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ) :=
  (TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM ∘L transposeCLM ha).precompCompactConvergenceCLM
      ℂ +
    Distribution.mapCLM (ContinuousLinearMap.mul ℝ ℂ Complex.I) ∘L
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.imCLM ∘L
        transposeCLM ha).precompCompactConvergenceCLM ℂ

private theorem quantizeDistributionReal_apply (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
    quantizeDistributionReal ha T φ = T.complexPairing
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
        (adjointTestFunctionCLM ha (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ))) := by
  rw [Distribution.complexPairing_apply]
  -- By definition, `Op(a) T` applies `T` to the real and imaginary parts of the transpose. The
  -- evaluation is by unfolding: `precompCompactConvergenceCLM_apply` produces a sum in the type
  -- synonym `UniformConvergenceCLM`, whose evaluation the lemma `add_apply` does not match.
  rfl

/-- **A properly supported operator on distributions.** For a scalar symbol `a` whose quantization
has kernel supported within distance `R` of the diagonal, `Op(a)` acts on all distributions on
`ℝⁿ` by transposition: `(Op(a) T) (φ) = T (Op(a)ᵗ φ)`, where `Op(a)ᵗ φ = conj (Op(a)* φ)` is the
transpose of `Op(a)` for the bilinear pairing `∫ φ u` and `T` is paired with complex test functions
by `Distribution.complexPairing` (`TauCeti.Symbol.quantizeDistribution_apply`; on complex test
functions, `TauCeti.Symbol.complexPairing_quantizeDistribution`). It is complex linear, and it
extends `Op(a)` on test functions (`TauCeti.Symbol.quantizeDistribution_ofFun`). -/
def quantizeDistribution (ha : a.HasNearDiagonalKernel R) :
    𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ) →L[ℂ] 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ) where
  toFun := quantizeDistributionReal ha
  map_add' := map_add _
  map_smul' c T := by
    ext φ
    rw [quantizeDistributionReal_apply, Distribution.complexPairing_smul,
      ← quantizeDistributionReal_apply, RingHom.id_apply, smul_apply, smul_eq_mul]
  cont := (quantizeDistributionReal ha).continuous

/-- `Op(a) T` pairs with a real test function `φ` as `T` with the transpose
`conj (Op(a)* φ)`. -/
@[simp]
theorem quantizeDistribution_apply (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
    quantizeDistribution ha T φ = T.complexPairing
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
        (adjointTestFunctionCLM ha (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ))) :=
  quantizeDistributionReal_apply ha T φ

/-- The complex-linear extension of `Op(a) T` pairs with a complex test function `ψ` as `T` with
the transpose `Op(a)ᵗ ψ = conj (Op(a)* (conj ψ))`. -/
@[simp]
theorem complexPairing_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) (ψ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).complexPairing ψ = T.complexPairing
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
        (adjointTestFunctionCLM ha
          (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap ψ))) := by
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

/-- **`Op(a)` on distributions extends `Op(a)` on test functions**: on the distribution of a test
function `u`, it is the distribution of `Op(a) u`. -/
@[simp]
theorem quantizeDistribution_ofFun (ha : a.HasNearDiagonalKernel R)
    (u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    quantizeDistribution ha (Distribution.ofFun ⊤ u volume ⊤) =
      Distribution.ofFun ⊤ (quantizeTestFunctionCLM ha u) volume ⊤ := by
  ext φ
  set φc := TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ
  have hloc (f : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
      LocallyIntegrableOn f (⊤ : Opens (CoordinateSpace n)) volume :=
    f.continuous.locallyIntegrable.locallyIntegrableOn _
  rw [quantizeDistribution_apply, Distribution.complexPairing_ofFun (hloc u),
    Distribution.ofFun_apply (hloc _)]
  -- Conjugating the adjoint identity `∫ conj (Op(a) u) φ = ∫ conj u (Op(a)* φ)`.
  have h := congrArg (starRingEnd ℂ) (integral_inner_quantizeTestFunctionCLM ha u φc)
  rw [← integral_conj, ← integral_conj] at h
  simp only [inner_conj_symm] at h
  refine Eq.trans ?_ (h.symm.trans ?_)
  · refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp [φc, mul_comm]
  · refine integral_congr_ae (.of_forall fun x ↦ ?_)
    simp [φc, Complex.real_smul, mul_comm]

/-- **Proper support on distributions.** `Op(a) T` is supported in the closed `R`-neighbourhood of
the support of `T`. -/
theorem dsupport_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    Distribution.dsupport (quantizeDistribution ha T) ⊆
      Metric.cthickening R (Distribution.dsupport T) := by
  have hU : IsOpen (Metric.cthickening R (Distribution.dsupport T))ᶜ :=
    Metric.isClosed_cthickening.isOpen_compl
  -- `Op(a) T` vanishes on test functions supported away from the `R`-neighbourhood of `supp T`.
  have h : Distribution.IsVanishingOn (quantizeDistribution ha T)
      (Metric.cthickening R (Distribution.dsupport T))ᶜ := by
    intro φ hφ
    rw [quantizeDistribution_apply]
    set ψ := TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
      (adjointTestFunctionCLM ha (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ))
    have hψ : tsupport ψ ⊆ Metric.cthickening R (tsupport φ) := by
      rw [TestFunction.postcompCLM_apply]
      refine (tsupport_comp_subset (map_zero _) _).trans
        ((tsupport_adjointTestFunctionCLM_subset ha _).trans
          (Metric.cthickening_subset_of_subset R ?_))
      rw [TestFunction.postcompCLM_apply]
      exact tsupport_comp_subset (map_zero _) _
    have hdisj : Disjoint (tsupport ψ) (Distribution.dsupport T) :=
      (φ.hasCompactSupport.isCompact.disjoint_cthickening_left
        (subset_compl_iff_disjoint_right.1 hφ)).mono_left hψ
    rw [T.complexPairing_eq_of_eventuallyEq (ψ := 0), map_zero]
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhdsSet.2
      hdisj.symm.subset_compl_right] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  simpa using (h.disjoint_dsupport hU).subset_compl_left

end Distribution

end Symbol

end TauCeti
