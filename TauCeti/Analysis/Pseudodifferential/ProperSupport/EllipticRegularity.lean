/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Smoothness
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.VectorValued
public import TauCeti.Analysis.Pseudodifferential.InteriorRegularity
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Distribution
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Sobolev.BesselPotential.Distribution
import TauCeti.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

/-!
# Elliptic regularity of properly supported pseudodifferential operators on distributions

Let `a` be a scalar symbol of order `m` on `ℝⁿ` whose quantization has kernel supported within
distance `R` of the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`), so that `Op(a)` acts on
all distributions `T ∈ 𝓓'(ℝⁿ)` by transposition (`TauCeti.Symbol.quantizeDistribution`). This
file proves **local elliptic regularity** for such operators, for arbitrary distributions and with
no a priori Sobolev regularity:

`Op(a) T ∈ H^s` near `x` ⟹ `T ∈ H^(s + m)` near `x`

whenever `a` has a formal left parametrix, `1 ∼ ∑ₖ sharpTerm b a k`
(`Distribution.IsLocallySobolevAt.of_quantizeDistribution`). Every symbol elliptic above some
radius has one (`TauCeti.Symbol.IsEllipticAbove.isLocallySobolevAt_of_quantizeDistribution`), and
so does every elliptic classical symbol
(`TauCeti.ClassicalSymbol.IsElliptic.isLocallySobolevAt_of_quantizeDistribution`). Consequently
`Op(a)` cannot remove singularities: `Op(a) T` is singular wherever `T` is. The `H^(s + m)`
singular support of `T` lies in the `H^s` singular support of `Op(a) T`, and the singular support
of `T` lies in that of `Op(a) T`. In particular every distributional solution of `Op(a) T = 0`, or
more generally of `Op(a) T = f` with `f` smooth, has empty singular support
(`Distribution.singularSupport_zero`, `Distribution.singularSupport_ofFun_eq_empty`): it is smooth
near every point.

Conversely, `Op(a)` maps `H^(s + m)_loc` to `H^s_loc`: if `T` is `H^(s + m)` near every point of
the closed `R`-neighbourhood of the support of a test function `ψ`, then `ψ Op(a) T ∈ H^s`
(`Distribution.memSobolev_cutoffTempered_quantizeDistribution`).

Elliptic regularity holds for **systems** as well. For a symbol `a` with values in `V →L[ℂ] W`,
with `V` and `W` finite-dimensional complex inner product spaces, and a matrix-valued formal left
parametrix, every `V`-valued distribution `T` is `H^(s + m)` wherever `Op(a) T` is `H^s`, in the
sense of the `H^s` singular supports of vector-valued distributions
(`vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution`).
Likewise the singular support of a `V`-valued `T` lies in that of `Op(a) T`
(`Distribution.singularSupport_subset_singularSupport_quantizeDistribution`), so every solution of
an elliptic system `Op(a) T = f` is smooth wherever `f` is. In a local frame, an operator between
vector bundles has such a symbol and acts on such distributions, so this is
`Pu ∈ H^s_loc ⟹ u ∈ H^(s + m)_loc` for bundle-valued `u` in a chart. The scalar regularity and
singular-support statements above are its case `V = W = ℂ`.

## The argument

Both directions reduce to the Bessel-potential spaces through one identity. Let `ψ` be a test
function, let `p(x, ξ) = ψ(x) a(x, ξ)` (`TauCeti.Symbol.smulLeft`), a symbol with compact
spatial support, and let `χ` be a test function equal to one on the closed `R`-neighbourhood of the
support of `ψ`. Then

`Op(p) (χ T) = ψ Op(a) T`

as tempered distributions (`TauCeti.Symbol.quantizeTempered_cutoffTempered`). Indeed the transpose
of `Op(p) = ψ Op(a)` sends a Schwartz function `f` to the transpose `Op(a)ᵗ (ψ f)` of the properly
supported operator, and this test function is supported in the `R`-neighbourhood of the support of
`ψ`, where `χ = 1`.

Every cut-off distribution `χ T` lies in some `H^r`
(`Distribution.exists_memSobolev_cutoffTempered`). So if `Op(a) T` is `H^s` near `x`, choosing
`ψ = 1` near the support of a cutoff `φ` at `x` shows that `u = χ T ∈ H^r` has
`Op(p) u ∈ H^s`, and interior elliptic regularity on `H^r`
(`TauCeti.Symbol.memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev`) gives
`φ T = φ u ∈ H^(s + m)`.

For systems the same argument runs on coordinates. In a basis `(e_j)` of `V` with dual basis
`(c_j)`, some `u ∈ H^r(ℝⁿ; V)` has the cut-off components `χ (c_j ∘ T)` as coordinates. The
component of `Op(ψ a) u` along a functional `ℓ` on `W` is a sum of scalar quantizations of the
entries `ℓ ∘ ψ a ∘ e_j` (`TauCeti.Symbol.postcomp_comp_quantizeSobolev`), and on distributions
`ℓ ∘ Op(a) T` is the same sum of the scalar operators `Op(ℓ ∘ a ∘ e_j)` applied to the components
`c_j ∘ T` (`TauCeti.Symbol.mapCLM_quantizeDistribution_eq_sum`). So the scalar identity above shows
that each component of `Op(ψ a) u` is `ψ (ℓ ∘ Op(a) T)`, which places `Op(ψ a) u` in `H^s`. The
matrix-valued interior regularity on `H^r` then gives `φ u ∈ H^(s + m)`, whose coordinates are
`φ (c_j ∘ T)`.

## Main results

* `TauCeti.Symbol.quantizeTempered_cutoffTempered`: `Op(ψ a) (χ T) = ψ Op(a) T`.
* `TauCeti.Symbol.exists_cutoffs_of_mem_nhds`: the nested cutoffs `φ`, `ψ` and `χ` at a point,
  for a symbol with values in any `V →L[ℂ] W`.
* `TauCeti.Symbol.HasNearDiagonalKernel.exists_cutoffs_of_mem_nhds`: the same cutoffs, reducing
  local elliptic regularity of a scalar operator to interior regularity on any regularity scale.
* `Distribution.memSobolev_cutoffTempered_quantizeDistribution`: properly supported operators of
  order `m` map `H^(s + m)_loc` to `H^s_loc`.
* `vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution`:
  **local elliptic regularity for systems**, in the namespace `Distribution`, with its corollaries
  of the same name in `TauCeti.Symbol.IsEllipticAbove` and `TauCeti.ClassicalSymbol.IsElliptic`.
* `Distribution.IsLocallySobolevAt.of_quantizeDistribution`: **local elliptic regularity**.
* `Distribution.sobolevSingularSupport_subset_sobolevSingularSupport_quantizeDistribution` and
  `Distribution.singularSupport_subset_singularSupport_quantizeDistribution`: elliptic operators
  do not shrink singular supports, the latter also for matrix-valued symbols acting on vector-valued
  distributions.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (4.6)–(4.11).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace TemperedDistribution
open scoped BesselPotentialSpace ComplexConjugate ContDiff Distributions SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m R : ℝ} {a p : Symbol n ℂ ℂ m} {ψ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}

/-- **The transpose of `ψ Op(a)`.** If `p(x, ξ) = ψ(x) a(x, ξ)` for a properly supported `Op(a)`,
the transpose of `Op(p)` on a Schwartz function `f` is the transpose
`Op(a)ᵗ g = conj (Op(a)* (conj g))` of `Op(a)` on the test function `g = ψ f`. -/
private theorem transposeUniformCLM_apply_eq_conj_adjointTestFunctionCLM
    (ha : a.HasNearDiagonalKernel R) (hp : p.IsUniform)
    (hpa : ∀ x ξ, p.coefficient (x, ξ) = ψ x • a.coefficient (x, ξ))
    (f : 𝓢(CoordinateSpace n, ℂ)) {g : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (hg : ∀ x, g x = ψ x * f x) (x : CoordinateSpace n) :
    transposeUniformCLM p hp f x = conj (adjointTestFunctionCLM ha
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap g) x) := by
  set A := adjointTestFunctionCLM ha
    (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap g)
  have hF : Continuous (transposeUniformCLM p hp f) := SchwartzMap.continuous _
  have hG : Continuous fun y ↦ conj (A y) := Complex.continuous_conj.comp A.continuous
  -- Both functions have the same integral against every real test function `w`.
  have key (w : CoordinateSpace n → ℝ) (hw : ContDiff ℝ ∞ w) (hwc : HasCompactSupport w) :
      ∫ y, w y • transposeUniformCLM p hp f y = ∫ y, w y • conj (A y) := by
    let wD : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
      ⟨fun y ↦ (w y : ℂ), Complex.ofRealCLM.contDiff.comp hw, hwc.comp_left Complex.ofReal_zero,
        subset_univ _⟩
    -- A test function built from its fields evaluates to its underlying function by definition;
    -- the rewrite `TestFunction.coe_mk` does not match the coerced smoothness index here.
    have hwD (y : CoordinateSpace n) : wD y = w y := rfl
    set wS := wD.hasCompactSupport.toSchwartzMap wD.contDiff
    have hwS (y : CoordinateSpace n) : wS y = w y := by
      rw [HasCompactSupport.toSchwartzMap_toFun, hwD]
    -- `Op(p) w = ψ Op(a) w`, so `∫ f Op(p) w = ∫ g Op(a) w`.
    have hOp (y : CoordinateSpace n) : f y * quantizeUniformCLM p hp wS y =
        g y * quantizeTestFunctionCLM ha wD y := by
      rw [quantizeUniformCLM_apply, quantizeTestFunctionCLM_apply,
        quantizeSchwartzValue_congr_left (b := ψ y • a.coefficient) (fun ξ ↦ hpa y ξ),
        quantizeSchwartzValue_smul_left, hg, smul_eq_mul]
      ring
    -- The adjoint identity `∫ ⟪Op(a) w, conj g⟫ = ∫ ⟪w, A⟫`, conjugated.
    have h := congrArg conj (integral_inner_quantizeTestFunctionCLM ha wD
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap g))
    rw [← integral_conj, ← integral_conj] at h
    simp only [inner_conj_symm] at h
    calc ∫ y, w y • transposeUniformCLM p hp f y
        = ∫ y, transposeUniformCLM p hp f y * wS y := by
          simp [hwS, Complex.real_smul, mul_comm]
      _ = ∫ y, f y * quantizeUniformCLM p hp wS y :=
          (integral_mul_quantizeUniformCLM p hp wS f).symm
      _ = ∫ y, g y * quantizeTestFunctionCLM ha wD y := by simp only [hOp]
      _ = ∫ y, inner ℂ ((TestFunction.postcompCLM (𝕜 := ℝ)
            Complex.conjCLE.toContinuousLinearMap g) y) (quantizeTestFunctionCLM ha wD y) := by
          simp [mul_comm]
      _ = ∫ y, inner ℂ (A y) (wD y) := h
      _ = ∫ y, w y • conj (A y) := by
          simp [hwD, A, Complex.real_smul, mul_comm]
  have hae := ae_eq_of_integral_contDiff_smul_eq hF.locallyIntegrable hG.locallyIntegrable key
  exact congrFun ((hF.ae_eq_iff_eq volume hG).1 hae) x

/-- **Cutting off a properly supported operator.** Let `Op(a)` have kernel supported within
distance `R` of the diagonal, let `p(x, ξ) = ψ(x) a(x, ξ)` for a test function `ψ`, and let `χ` be
a test function equal to one on the closed `R`-neighbourhood of the support of `ψ`. For every
distribution `T`, the quantization of `p` applied to the tempered distribution `χ T` is `ψ Op(a) T`:
`Op(p) (χ T) = ψ Op(a) T`. -/
theorem quantizeTempered_cutoffTempered (ha : a.HasNearDiagonalKernel R) (hp : p.IsUniform)
    (hpa : ∀ x ξ, p.coefficient (x, ξ) = ψ x • a.coefficient (x, ξ))
    {χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (hχ : ∀ x ∈ Metric.cthickening R (tsupport ψ), χ x = 1)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    quantizeTempered ℂ p hp (T.cutoffTempered χ) =
      (quantizeDistribution ha T).cutoffTempered ψ := by
  refine Distribution.eq_cutoffTempered_of_forall _ _ fun f g _ hg ↦ ?_
  rw [quantizeTempered_apply_apply, Distribution.cutoffTempered_def,
    complexPairing_quantizeDistribution]
  congr 1
  ext x
  simp only [TestFunction.bilinLeftCLM_apply, ContinuousLinearMap.mul_apply']
  rw [transposeUniformCLM_apply_eq_conj_adjointTestFunctionCLM ha hp hpa _ (g := g)
      (fun y ↦ by simpa using hg y), scalarTransposeTestFunctionCLM_apply]
  -- `Op(a)ᵗ g` is supported in the `R`-neighbourhood of the support of `g ⊆ tsupport ψ`.
  have hsupp : tsupport (adjointTestFunctionCLM ha
      (TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap g)) ⊆
        Metric.cthickening R (tsupport ψ) := by
    refine (tsupport_adjointTestFunctionCLM_subset ha _).trans
      (Metric.cthickening_subset_of_subset R ?_)
    rw [TestFunction.postcompCLM_apply]
    refine (tsupport_comp_subset (map_zero _) _).trans (closure_mono fun y hy ↦ ?_)
    rw [Function.mem_support] at hy ⊢
    exact left_ne_zero_of_mul (hg y ▸ hy)
  by_cases hx : x ∈ Metric.cthickening R (tsupport ψ)
  · simp only [hχ x hx, one_mul]
  · have h0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hsupp h)
    simp only [h0, map_zero, mul_zero]

/-- **Nested cutoffs at a point.** Let `U` be a neighbourhood of `x` and let `R` be a radius.
There are test functions `φ`, `ψ` and `χ`, with `φ = 1` near `x`, `ψ` supported in `U` and equal to
one near the support of `φ`, and `χ = 1` on the closed `R`-neighbourhood of the support of `ψ`,
together with the compactly supported Schwartz function `φS = φ`. For the given symbol `a`, `ψ a`
agrees with `a` near the support of `φS`. -/
theorem exists_cutoffs_of_mem_nhds {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] (a : Symbol n V W m) (R : ℝ)
    {U : Set (CoordinateSpace n)} {x : CoordinateSpace n} (hU : U ∈ 𝓝 x) :
    ∃ (φ ψ χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) (φS : 𝓢(CoordinateSpace n, ℂ)),
      (∀ᶠ y in 𝓝 x, φ y = 1) ∧ tsupport ψ ⊆ U ∧ tsupport φ ⊆ tsupport ψ ∧
      (∀ y ∈ Metric.cthickening R (tsupport ψ), χ y = 1) ∧
      (φS : CoordinateSpace n → ℂ) = φ ∧ HasCompactSupport φS ∧
      ∀ᶠ y in 𝓝ˢ (tsupport φS), ∀ ξ,
        (smulLeft ψ.contDiff a).coefficient (y, ξ) = a.coefficient (y, ξ) := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨φ, hφx, hφs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⊤) isCompact_singleton (Metric.isOpen_ball : IsOpen (Metric.ball x (ε / 2)))
    (singleton_subset_iff.2 (Metric.mem_ball_self (half_pos hε))) (by simp)
  obtain ⟨ψ, hψ1, hψs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    φ.hasCompactSupport.isCompact (Metric.isOpen_ball : IsOpen (Metric.ball x ε))
    (hφs.trans (Metric.ball_subset_ball (by linarith))) (by simp)
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    (ψ.hasCompactSupport.isCompact.cthickening (r := R)) isOpen_univ (subset_univ _) (by simp)
  have hφS : (φ.hasCompactSupport.toSchwartzMap φ.contDiff : CoordinateSpace n → ℂ) = φ :=
    funext (φ.hasCompactSupport.toSchwartzMap_toFun φ.contDiff)
  refine ⟨φ, ψ, χ, φ.hasCompactSupport.toSchwartzMap φ.contDiff,
    by rwa [nhdsSet_singleton] at hφx, hψs.trans hεU,
    fun y hy ↦ subset_tsupport _ (by simp [hψ1.self_of_nhdsSet y hy]),
    fun y hy ↦ hχ1.self_of_nhdsSet y hy, hφS, hφS ▸ φ.hasCompactSupport, ?_⟩
  -- Near the support of `φ`, `ψ = 1`, so `ψ a` agrees with `a` there.
  rw [hφS]
  filter_upwards [hψ1] with y hy ξ
  rw [coefficient_smulLeft, hy, one_smul]

/-- **Cutoffs for local elliptic regularity.** Let `Op(a)` have kernel supported within distance
`R` of the diagonal, and let `U` be a neighbourhood of `x`. There are test functions `φ`, `ψ` and
`χ`, with `φ = 1` near `x` and `ψ` supported in `U`, and a compactly supported Schwartz function
`φS`, such that `ψ a` agrees with `a` near the support of `φS` and, for every distribution `T`,
`Op(ψ a) (χ T) = ψ Op(a) T` and `φS (χ T) = φ T`. They reduce local elliptic regularity of
`Op(a)` at `x` to interior regularity for the tempered distribution `χ T`. -/
theorem HasNearDiagonalKernel.exists_cutoffs_of_mem_nhds (ha : a.HasNearDiagonalKernel R)
    {U : Set (CoordinateSpace n)} {x : CoordinateSpace n} (hU : U ∈ 𝓝 x) :
    ∃ (φ ψ χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) (φS : 𝓢(CoordinateSpace n, ℂ)),
      (∀ᶠ y in 𝓝 x, φ y = 1) ∧ tsupport ψ ⊆ U ∧ HasCompactSupport φS ∧
      (∀ᶠ y in 𝓝ˢ (tsupport φS), ∀ ξ,
        (smulLeft ψ.contDiff a).coefficient (y, ξ) = a.coefficient (y, ξ)) ∧
      ∀ T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ),
        quantizeTempered ℂ (smulLeft ψ.contDiff a)
            (hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a).isUniform
            (T.cutoffTempered χ) = (quantizeDistribution ha T).cutoffTempered ψ ∧
          smulLeftCLM ℂ (φS : CoordinateSpace n → ℂ) (T.cutoffTempered χ) =
            T.cutoffTempered φ := by
  obtain ⟨φ, ψ, χ, φS, hφx, hψU, hφψ, hχψ, hφS, hφSc, hpa⟩ :=
    Symbol.exists_cutoffs_of_mem_nhds a R hU
  refine ⟨φ, ψ, χ, φS, hφx, hψU, hφSc, hpa, fun T ↦ ⟨quantizeTempered_cutoffTempered ha _
    (fun y ξ ↦ coefficient_smulLeft ψ.contDiff a (y, ξ)) hχψ T, ?_⟩⟩
  rw [hφS]
  exact Distribution.smulLeftCLM_cutoffTempered T fun y hy ↦
    hχψ y (Metric.self_subset_cthickening _ (hφψ hy))

/-! ### Matrix-valued symbols -/

section Vector

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {a : Symbol n V W m}
  {ι : Type*}

/-- **Cutting off a matrix-valued properly supported operator.** Let `Op(a)` have kernel supported
within distance `R` of the diagonal, let `p(x, ξ) = ψ(x) a(x, ξ)`, and let `χ` be a test function
equal to one on the closed `R`-neighbourhood of the support of `ψ`. If the coordinates of
`u ∈ H^r(ℝⁿ; V)` in a basis are the cut-off components `χ (c_j ∘ T)` of a distribution `T`, then
the component of `Op(p) u` along any functional `ℓ` is `ψ (ℓ ∘ Op(a) T)`. -/
private theorem toDistr_postcomp_quantizeSobolev_smulLeft (b : Module.Basis ι ℂ V)
    (ha : a.HasNearDiagonalKernel R) {ψ χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (hχ : ∀ x ∈ Metric.cthickening R (tsupport ψ), χ x = 1)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) {r : ℝ} (u : H^{r}(CoordinateSpace n, V))
    (hu : ∀ j, (BesselPotentialSpace.postcomp _ r 2 (b.coord j).toContinuousLinearMap u).toDistr =
      (Distribution.mapCLM ((b.coord j).toContinuousLinearMap.restrictScalars ℝ) T).cutoffTempered
        χ)
    (ℓ : W →L[ℂ] ℂ) :
    (BesselPotentialSpace.postcomp _ _ 2 ℓ ((smulLeft ψ.contDiff a).quantizeSobolev
        (hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a) r u)).toDistr =
      (Distribution.mapCLM (ℓ.restrictScalars ℝ) (quantizeDistribution ha T)).cutoffTempered ψ := by
  have := FiniteDimensional.fintypeBasisIndex b
  have hp := hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  -- The entries `ℓ ∘ ψ a ∘ e_j` of `ψ a` are `ψ` times the entries of `a`.
  have hpa (j : ι) (x ξ : CoordinateSpace n) :
      ((smulLeft ψ.contDiff a).map (entryMap ℓ (b j))).coefficient (x, ξ) =
        ψ x • (a.map (entryMap ℓ (b j))).coefficient (x, ξ) := by
    simp [coefficient_smulLeft]
  have h := congrArg (fun L ↦ (L u).toDistr) (postcomp_comp_quantizeSobolev hp b ℓ r)
  simp only [ContinuousLinearMap.comp_apply, _root_.sum_apply] at h
  rw [h, mapCLM_quantizeDistribution_eq_sum ha b ℓ, Distribution.cutoffTempered_sum,
    ← BesselPotentialSpace.toDistrCLM_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [BesselPotentialSpace.toDistrCLM_apply, toDistr_quantizeSobolev, hu j,
    quantizeTempered_cutoffTempered (ha.map ℓ _ (entryMap_apply ℓ (b j)))
      (hp.map _).isUniform (hpa j) hχ]

/-- If the coordinates of `u ∈ H^r(ℝⁿ; V)` in a basis are the cut-off components `χ (c_j ∘ T)`,
and `χ = 1` on the support of `φ`, then the coordinates of `φ u` are `φ (c_j ∘ T)`. -/
private theorem postcomp_smulLeftCLM_toDistr (b : Module.Basis ι ℂ V)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) {φ χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (hχ : ∀ x ∈ tsupport φ, χ x = 1) {r : ℝ} (u : H^{r}(CoordinateSpace n, V))
    (hu : ∀ j, (BesselPotentialSpace.postcomp _ r 2 (b.coord j).toContinuousLinearMap u).toDistr =
      (Distribution.mapCLM ((b.coord j).toContinuousLinearMap.restrictScalars ℝ) T).cutoffTempered
        χ) (j : ι) :
    PointwiseConvergenceCLM.postcomp _ (b.coord j).toContinuousLinearMap
        (TemperedDistribution.smulLeftCLM V (φ : CoordinateSpace n → ℂ) u.toDistr) =
      (Distribution.mapCLM ((b.coord j).toContinuousLinearMap.restrictScalars ℝ) T).cutoffTempered
        φ := by
  rw [← Distribution.smulLeftCLM_cutoffTempered _ hχ, ← hu j]
  ext f
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    BesselPotentialSpace.toDistr_postcomp_apply, PointwiseConvergenceCLM.postcomp_apply_apply]

end Vector

end Symbol

end TauCeti

namespace Distribution

open TauCeti TauCeti.Symbol

variable {n : ℕ} {m R : ℝ} {a : Symbol n ℂ ℂ m} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)}

/-- **Properly supported operators map `H^(s + m)_loc` to `H^s_loc`.** If `Op(a)` has order `m`
and kernel supported within distance `R` of the diagonal, and `T` is `H^(s + m)` near every point
of the closed `R`-neighbourhood of the support of a test function `ψ`, then `ψ Op(a) T ∈ H^s`. -/
theorem memSobolev_cutoffTempered_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {ψ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)} {s : ℝ}
    (h : ∀ y ∈ Metric.cthickening R (tsupport ψ), T.IsLocallySobolevAt (s + m) y) :
    MemSobolev s 2 ((quantizeDistribution ha T).cutoffTempered ψ) := by
  obtain ⟨χ, hχ1, hχU⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    (ψ.hasCompactSupport.isCompact.cthickening (r := R)) (isOpen_setOf_isLocallySobolevAt _ T)
    h (by simp)
  have hp := hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  have hpa (x ξ : CoordinateSpace n) := coefficient_smulLeft ψ.contDiff a (x, ξ)
  rw [← quantizeTempered_cutoffTempered ha hp.isUniform hpa
    (fun x hx ↦ hχ1.self_of_nhdsSet x hx) T]
  simpa using memSobolev_quantizeTempered hp
    (memSobolev_cutoffTempered_of_forall_isLocallySobolevAt fun y hy ↦ hχU hy)

/-- **Local elliptic regularity of properly supported systems.** Let `a` be a symbol of order `m`
with values in `V →L[ℂ] W`, for finite-dimensional complex inner product spaces `V` and `W`, whose
quantization has kernel supported within distance `R` of the diagonal, and let `a` have a formal
left parametrix `b`, `1 ∼ ∑ₖ sharpTerm b a k`. Then for every `V`-valued distribution `T`, `T` is
`H^(s + m)` wherever `Op(a) T` is `H^s`: the `H^(s + m)` singular support of `T` lies in the `H^s`
singular support of `Op(a) T`. In a local frame this is `Pu ∈ H^s_loc ⟹ u ∈ H^(s + m)_loc` for an
operator between vector bundles. -/
theorem vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {a : Symbol n V W m}
    (ha : a.HasNearDiagonalKernel R) {b : Symbol n W V (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    T.vectorSobolevSingularSupport (s + m) ⊆
      (quantizeDistribution ha T).vectorSobolevSingularSupport s := by
  intro x hx
  by_contra hPx
  set bV := Module.finBasis ℂ V
  set bW := Module.finBasis ℂ W
  -- The coordinates of `Op(a) T` are `H^s` on a common neighbourhood `U` of `x`.
  have hk := (notMem_vectorSobolevSingularSupport_iff_forall_isLocallySobolevAt (mem_univ x)).1 hPx
  choose U hU hUs using fun k ↦
    (hk (bW.coord k).toContinuousLinearMap).exists_nhds_forall_memSobolev_cutoffTempered
  obtain ⟨φ, ψ, χ, φS, hφx, hψU, hφψ, hχψ, hφS, hφSc, hpa⟩ :=
    exists_cutoffs_of_mem_nhds a R (Filter.iInter_mem.2 hU)
  -- Some `u ∈ H^r` has the cut-off coordinates `χ (c_j ∘ T)`, and `Op(ψ a) u ∈ H^s`.
  obtain ⟨r, u, hu⟩ := exists_toDistr_postcomp_coord_eq_cutoffTempered bV T χ
  set p := smulLeft ψ.contDiff a
  have hp : p.HasCompactSpatialSupport :=
    hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  have hv : MemSobolev s 2 (p.quantizeSobolev hp r u).toDistr := by
    refine (memSobolev_iff_forall_postcomp_coord bW).2 fun k ↦ ?_
    have h := toDistr_postcomp_quantizeSobolev_smulLeft bV ha hχψ T u hu
      (bW.coord k).toContinuousLinearMap
    rw [← BesselPotentialSpace.toDistr_postcomp, h]
    exact hUs k ψ (hψU.trans (iInter_subset U k))
  -- Interior elliptic regularity gives `φ u ∈ H^(s + m)`; its coordinates are `φ (c_j ∘ T)`.
  have hreg := memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev hab hφSc hp hpa u hv
  rw [hφS] at hreg
  rw [vectorSobolevSingularSupport_eq_iUnion_basis _ bV T, mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  refine (mem_sobolevSingularSupport_iff.1 hj).2
    (isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
      ⟨φ, by simp [hφx.self_of_nhds], ?_⟩)
  rw [← postcomp_smulLeftCLM_toDistr bV T
    (fun y hy ↦ hχψ y (Metric.self_subset_cthickening _ (hφψ hy))) u hu j]
  exact hreg.postcomp _

/-- **Local elliptic regularity of properly supported operators.** Let `Op(a)` have order `m` and
kernel supported within distance `R` of the diagonal, and let `a` have a formal left parametrix
`b`, `1 ∼ ∑ₖ sharpTerm b a k`. If `Op(a) T` is `H^s` near `x` for a distribution `T`, then `T` is
`H^(s + m)` near `x`. This is the scalar case of the statement for systems,
`vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution`. -/
theorem IsLocallySobolevAt.of_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {b : Symbol n ℂ ℂ (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    {x : CoordinateSpace n} {s : ℝ} (h : (quantizeDistribution ha T).IsLocallySobolevAt s x) :
    T.IsLocallySobolevAt (s + m) x := by
  by_contra hT
  have hx := vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution
    ha hab s T (by
      rw [vectorSobolevSingularSupport_eq_sobolevSingularSupport]
      exact mem_sobolevSingularSupport_iff.2 ⟨mem_univ x, hT⟩)
  rw [vectorSobolevSingularSupport_eq_sobolevSingularSupport] at hx
  exact (mem_sobolevSingularSupport_iff.1 hx).2 h

/-- **Elliptic operators do not shrink `H^s` singular supports.** If `Op(a)` has order `m`, kernel
supported within distance `R` of the diagonal, and a formal left parametrix, then `T` is
`H^(s + m)` wherever `Op(a) T` is `H^s`. -/
theorem sobolevSingularSupport_subset_sobolevSingularSupport_quantizeDistribution
    (ha : a.HasNearDiagonalKernel R) {b : Symbol n ℂ ℂ (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    T.sobolevSingularSupport (s + m) ⊆ (quantizeDistribution ha T).sobolevSingularSupport s :=
  fun x hx ↦ mem_sobolevSingularSupport_iff.2 ⟨mem_univ x, fun h ↦
    (mem_sobolevSingularSupport_iff.1 hx).2 (h.of_quantizeDistribution ha hab)⟩

/-- **Elliptic regularity for smoothness.** If `Op(a)`, for a symbol `a` with values in
`V →L[ℂ] W`, has kernel supported within distance `R` of the diagonal and a formal left parametrix,
then a `V`-valued distribution `T` is smooth wherever `Op(a) T` is: the singular support of `T` lies
in that of `Op(a) T`. In particular every distributional solution of `Op(a) T = 0` has empty
singular support: it is smooth near every point. -/
theorem singularSupport_subset_singularSupport_quantizeDistribution {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] {a : Symbol n V W m}
    (ha : a.HasNearDiagonalKernel R) {b : Symbol n W V (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ V))) (b.sharpTerm a))
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    T.singularSupport ⊆ (quantizeDistribution ha T).singularSupport := by
  set bV := Module.finBasis ℂ V
  set bW := Module.finBasis ℂ W
  intro x hx
  by_contra hPx
  rw [singularSupport_eq_iUnion_basis bW, mem_iUnion, not_exists] at hPx
  rw [singularSupport_eq_iUnion_basis bV, mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  -- Near `x`, every coordinate of `Op(a) T` has every Sobolev order, hence so does `T`.
  have hev : ∀ᶠ y in 𝓝 x, ∀ k s,
      (mapCLM ((bW.coord k).toContinuousLinearMap.restrictScalars ℝ)
        (quantizeDistribution ha T)).IsLocallySobolevAt s y :=
    Filter.eventually_all.2 fun k ↦
      (notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt (mem_univ x)).1 (hPx k)
  refine (notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt (mem_univ x)).2 ?_ hj
  filter_upwards [hev] with y hy s
  have hy' : y ∉ (quantizeDistribution ha T).vectorSobolevSingularSupport (s - m) := by
    rw [vectorSobolevSingularSupport_eq_iUnion_basis _ bW, mem_iUnion, not_exists]
    exact fun k hk ↦ (mem_sobolevSingularSupport_iff.1 hk).2 (hy k _)
  have hT : y ∉ T.vectorSobolevSingularSupport (s - m + m) := fun h ↦ hy'
    (vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution
      ha hab (s - m) T h)
  rw [sub_add_cancel, vectorSobolevSingularSupport_eq_iUnion_basis _ bV, mem_iUnion,
    not_exists] at hT
  exact by_contra fun h ↦ hT j (mem_sobolevSingularSupport_iff.2 ⟨mem_univ y, h⟩)

end Distribution

namespace TauCeti

variable {n : ℕ} {m R : ℝ} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)} {x : CoordinateSpace n}
  {s : ℝ}

/-- **Local elliptic regularity for symbols elliptic above a radius.** If `a` is elliptic above
some radius and `Op(a)` has kernel supported within distance `R` of the diagonal, then
`Op(a) T ∈ H^s` near `x` implies `T ∈ H^(s + m)` near `x`. -/
theorem Symbol.IsEllipticAbove.isLocallySobolevAt_of_quantizeDistribution
    {a : Symbol n ℂ ℂ m} {R' : ℝ} (hell : a.IsEllipticAbove R') (ha : a.HasNearDiagonalKernel R)
    (h : (quantizeDistribution ha T).IsLocallySobolevAt s x) :
    T.IsLocallySobolevAt (s + m) x :=
  let ⟨_, hab, _⟩ := hell.exists_isAsymptoticSum_sharpTerm
  h.of_quantizeDistribution ha hab

/-- **Local elliptic regularity for elliptic classical symbols.** If the classical symbol `a` is
elliptic and `Op(a)` has kernel supported within distance `R` of the diagonal, then
`Op(a) T ∈ H^s` near `x` implies `T ∈ H^(s + m)` near `x`. -/
theorem ClassicalSymbol.IsElliptic.isLocallySobolevAt_of_quantizeDistribution
    {a : ClassicalSymbol n ℂ ℂ m} (hell : a.IsElliptic) (ha : a.toSymbol.HasNearDiagonalKernel R)
    (h : (Symbol.quantizeDistribution ha T).IsLocallySobolevAt s x) :
    T.IsLocallySobolevAt (s + m) x :=
  let ⟨_, hab⟩ := hell.exists_isAsymptoticSum_sharpTerm_left
  h.of_quantizeDistribution ha hab

section Vector

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]

namespace Symbol.IsEllipticAbove

/-- **Local elliptic regularity for systems elliptic above a radius.** If the matrix-valued symbol
`a` is elliptic above some radius and `Op(a)` has kernel supported within distance `R` of the
diagonal, then every `V`-valued distribution `T` is `H^(s + m)` wherever `Op(a) T` is `H^s`. -/
theorem vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution
    {a : Symbol n V W m} {R' : ℝ} (hell : a.IsEllipticAbove R') (ha : a.HasNearDiagonalKernel R)
    (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    T.vectorSobolevSingularSupport (s + m) ⊆
      (Symbol.quantizeDistribution ha T).vectorSobolevSingularSupport s :=
  let ⟨_, hab, _⟩ := hell.exists_isAsymptoticSum_sharpTerm
  Distribution.vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution
    ha hab s T

end Symbol.IsEllipticAbove

namespace ClassicalSymbol.IsElliptic

/-- **Local elliptic regularity for elliptic classical systems.** If the matrix-valued classical
symbol `a` is elliptic and `Op(a)` has kernel supported within distance `R` of the diagonal, then
every `V`-valued distribution `T` is `H^(s + m)` wherever `Op(a) T` is `H^s`. -/
theorem vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution
    {a : ClassicalSymbol n V W m} (hell : a.IsElliptic) (ha : a.toSymbol.HasNearDiagonalKernel R)
    (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    T.vectorSobolevSingularSupport (s + m) ⊆
      (Symbol.quantizeDistribution ha T).vectorSobolevSingularSupport s :=
  let ⟨_, hab⟩ := hell.exists_isAsymptoticSum_sharpTerm_left
  Distribution.vectorSobolevSingularSupport_subset_vectorSobolevSingularSupport_quantizeDistribution
    ha hab s T

end ClassicalSymbol.IsElliptic

end Vector

end TauCeti
