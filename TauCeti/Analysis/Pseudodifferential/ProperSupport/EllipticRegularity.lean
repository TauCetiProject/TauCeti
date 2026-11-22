/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Smoothness
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
public import TauCeti.Analysis.Pseudodifferential.InteriorRegularity
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Distribution
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

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

## Main results

* `TauCeti.Symbol.quantizeTempered_cutoffTempered`: `Op(ψ a) (χ T) = ψ Op(a) T`.
* `TauCeti.Symbol.HasNearDiagonalKernel.exists_cutoffs_of_mem_nhds`: the nested cutoffs `φ`, `ψ`
  and `χ` at a point, shared by the local regularity proofs on every regularity scale.
* `Distribution.memSobolev_cutoffTempered_quantizeDistribution`: properly supported operators of
  order `m` map `H^(s + m)_loc` to `H^s_loc`.
* `Distribution.IsLocallySobolevAt.of_quantizeDistribution`: **local elliptic regularity**.
* `Distribution.sobolevSingularSupport_subset_sobolevSingularSupport_quantizeDistribution` and
  `Distribution.singularSupport_subset_singularSupport_quantizeDistribution`: elliptic operators
  do not shrink singular supports.

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
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  -- Nested cutoffs: `φ = 1` near `x`, `ψ = 1` near the support of `φ`, and `χ = 1` on the closed
  -- `R`-neighbourhood of the support of `ψ`.
  obtain ⟨φ, hφx, hφs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤)
    (Ω := ⊤) isCompact_singleton (Metric.isOpen_ball : IsOpen (Metric.ball x (ε / 2)))
    (singleton_subset_iff.2 (Metric.mem_ball_self (half_pos hε))) (by simp)
  obtain ⟨ψ, hψ1, hψs⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    φ.hasCompactSupport.isCompact (Metric.isOpen_ball : IsOpen (Metric.ball x ε))
    (hφs.trans (Metric.ball_subset_ball (by linarith))) (by simp)
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    (ψ.hasCompactSupport.isCompact.cthickening (r := R)) isOpen_univ (subset_univ _) (by simp)
  have hχψ (y : CoordinateSpace n) (hy : y ∈ Metric.cthickening R (tsupport ψ)) : χ y = 1 :=
    hχ1.self_of_nhdsSet y hy
  have hφψ : tsupport φ ⊆ tsupport ψ := fun y hy ↦
    subset_tsupport _ (by simp [hψ1.self_of_nhdsSet y hy])
  have hφS : (φ.hasCompactSupport.toSchwartzMap φ.contDiff : CoordinateSpace n → ℂ) = φ :=
    funext (φ.hasCompactSupport.toSchwartzMap_toFun φ.contDiff)
  refine ⟨φ, ψ, χ, φ.hasCompactSupport.toSchwartzMap φ.contDiff,
    by rwa [nhdsSet_singleton] at hφx, hψs.trans hεU, hφS ▸ φ.hasCompactSupport, ?_,
    fun T ↦ ⟨quantizeTempered_cutoffTempered ha _
      (fun y ξ ↦ coefficient_smulLeft ψ.contDiff a (y, ξ)) hχψ T, ?_⟩⟩
  · -- Near the support of `φ`, `ψ = 1`, so `ψ a` agrees with `a` there.
    rw [hφS]
    filter_upwards [hψ1] with y hy ξ
    rw [coefficient_smulLeft, hy, one_smul]
  · rw [hφS]
    exact Distribution.smulLeftCLM_cutoffTempered T fun y hy ↦
      hχψ y (Metric.self_subset_cthickening _ (hφψ hy))

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

/-- **Local elliptic regularity of properly supported operators.** Let `Op(a)` have order `m` and
kernel supported within distance `R` of the diagonal, and let `a` have a formal left parametrix
`b`, `1 ∼ ∑ₖ sharpTerm b a k`. If `Op(a) T` is `H^s` near `x` for a distribution `T`, then `T` is
`H^(s + m)` near `x`. -/
theorem IsLocallySobolevAt.of_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {b : Symbol n ℂ ℂ (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    {x : CoordinateSpace n} {s : ℝ} (h : (quantizeDistribution ha T).IsLocallySobolevAt s x) :
    T.IsLocallySobolevAt (s + m) x := by
  obtain ⟨U, hU, hUs⟩ := h.exists_nhds_forall_memSobolev_cutoffTempered
  obtain ⟨φ, ψ, χ, φS, hφx, hψU, hφS, hpa, hT⟩ := ha.exists_cutoffs_of_mem_nhds hU
  obtain ⟨hpT, hφT⟩ := hT T
  -- `u = χ T` lies in some `H^r`, and `Op(ψ a) u = ψ Op(a) T ∈ H^s`.
  obtain ⟨r, hr⟩ := T.exists_memSobolev_cutoffTempered χ
  have hp := hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  have hu : MemSobolev s 2 ((smulLeft ψ.contDiff a).quantizeSobolev hp r
      hr.toBesselPotentialSpace).toDistr := by
    rw [toDistr_quantizeSobolev, hr.toBesselPotentialSpace_toDistr, hpT]
    exact hUs ψ hψU
  have hreg := memSobolev_smulLeftCLM_of_memSobolev_quantizeSobolev hab hφS hp hpa _ hu
  rw [hr.toBesselPotentialSpace_toDistr, hφT] at hreg
  exact isLocallySobolevAt_iff_exists_memSobolev_cutoffTempered.2
    ⟨φ, by simp [hφx.self_of_nhds], hreg⟩

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

/-- **Elliptic regularity for smoothness.** If `Op(a)` has kernel supported within distance `R` of
the diagonal and a formal left parametrix, then `T` is smooth wherever `Op(a) T` is: the singular
support of `T` lies in that of `Op(a) T`. In particular every distributional solution of
`Op(a) T = 0` has empty singular support: it is smooth near every point. -/
theorem singularSupport_subset_singularSupport_quantizeDistribution
    (ha : a.HasNearDiagonalKernel R) {b : Symbol n ℂ ℂ (-m)}
    (hab : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k)
      (inclusion (by simp) (const (.id ℂ ℂ))) (b.sharpTerm a))
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    T.singularSupport ⊆ (quantizeDistribution ha T).singularSupport := by
  intro x hx
  by_contra hPx
  rw [notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt (mem_univ x)] at hPx
  refine (notMem_singularSupport_iff_eventually_forall_isLocallySobolevAt (mem_univ x)).2 ?_ hx
  filter_upwards [hPx] with y hy s
  simpa using (hy (s - m)).of_quantizeDistribution ha hab

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

end TauCeti
