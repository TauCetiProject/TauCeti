/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.SingularSupport
public import TauCeti.Analysis.Pseudodifferential.CharacteristicSet
public import TauCeti.Analysis.Pseudodifferential.Microlocality
public import TauCeti.Analysis.Pseudodifferential.ProperSupport.Distribution
public import TauCeti.Analysis.Pseudodifferential.TemperedDistribution
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Closure
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Pseudodifferential.Microlocal
import TauCeti.Analysis.Pseudodifferential.ProperSupport.EllipticRegularity
import TauCeti.Topology.MetricSpace.Thickening

/-!
# Microlocality and elliptic regularity of properly supported pseudodifferential operators

Let `a` be a scalar symbol on `ℝⁿ` whose quantization has kernel supported within distance `R` of
the diagonal (`TauCeti.Symbol.HasNearDiagonalKernel a R`), acting on all distributions
`T ∈ 𝓓'(ℝⁿ)` by transposition (`TauCeti.Symbol.quantizeDistribution`). No compact spatial support
and no estimate uniform in the position is assumed. This file proves that such an operator does not
enlarge the wave front set,

`WF(Op(a) T) ⊆ WF(T)`

(`TauCeti.Symbol.waveFrontSet_quantizeDistribution_subset`), and hence not the singular support
either (`TauCeti.Symbol.singularSupport_quantizeDistribution_subset`). For symbols with compact
spatial support acting on a Bessel-potential space `H^t` this is
`TauCeti.Symbol.waveFrontSet_toDistribution_quantizeSobolev_subset`; the point here is that `T` is
an arbitrary distribution, with no global Sobolev regularity, and that the symbol is only properly
supported.

The same holds on the Sobolev scale, where `Op(a)` loses `m` orders of microlocal regularity: if
`T` is microlocally `H^s` at `(x, ξ)`, then `Op(a) T` is microlocally `H^{s - m}` there
(`TauCeti.Symbol.isMicrolocallySobolevAt_quantizeDistribution`), so

`WF_{s - m}(Op(a) T) ⊆ WF_s(T)` and `singsupp_{s - m}(Op(a) T) ⊆ singsupp_s(T)`

(`TauCeti.Symbol.sobolevWaveFrontSet_quantizeDistribution_subset`,
`TauCeti.Symbol.sobolevSingularSupport_quantizeDistribution_subset`). For symbols with compact
spatial support acting on `H^t` this is
`TauCeti.Symbol.HasCompactSpatialSupport.sobolevWaveFrontSet_toDistribution_quantizeSobolev_subset`.
Unlike `TauCeti.Symbol.sobolevSingularSupport_quantizeDistribution_subset_cthickening`, the
`H^{s - m}` singular support of `Op(a) T` lies in the `H^s` singular support of `T` itself, not
only in its closed `R`-neighbourhood.

For **systems**, symbols `a` with values in `V →L[ℂ] W` for finite-dimensional complex inner
product spaces `V` and `W`, acting on `V`-valued distributions, microlocality and microlocal
elliptic regularity hold for the wave front set of vector-valued distributions, the union of the
wave front sets of the components (`Distribution.vectorWaveFrontSet`):

`WF(Op(a) T) ⊆ WF(T) ⊆ WF(Op(a) T) ∪ Char(a)`

(`TauCeti.Symbol.vectorWaveFrontSet_quantizeDistribution_subset`,
`TauCeti.Symbol.vectorWaveFrontSet_subset_quantizeDistribution_union_characteristicSet`).
In a local frame this is how a properly supported operator between vector bundles acts on
distributional sections in a chart.

## Proof

The reduction to the Sobolev statement is by localization in the input and in the symbol.

* **Localizing the symbol.** For a test function `χ`, the cut-off distribution `χ T` is the
  tempered distribution `Distribution.cutoffTempered T χ`, supported in `tsupport χ ⊆ U` for an
  open set `U`. If `ψ = 1` on the closed `R`-neighbourhood of `U`, then `Op(a)` and the
  quantization of `ψ a`, a symbol with compact spatial support, agree on the test functions
  supported in `U`. By duality their transposes agree on `U`, so `Op(a) (χ T)` is the tempered
  quantization of `ψ a` applied to `χ T`
  (`TauCeti.Symbol.quantizeDistribution_toDistribution_cutoffTempered`).
* **Localizing the input.** Take `χ = 1` on a ball around `x₀` of radius larger than `R`. Then
  `T - χ T` vanishes on that ball, and by proper support `Op(a) (T - χ T)` vanishes near `x₀`
  (`TauCeti.Symbol.dsupport_quantizeDistribution_subset`). Since `χ T` lies in some `H^t`
  (`Distribution.exists_memSobolev_cutoffTempered`), the Sobolev statement applies to
  `Op(a) (χ T)`, and `χ T` agrees with `T` near `x₀`.

The `H^s` order shift is proved by the same two localizations, from
`TauCeti.Symbol.HasCompactSpatialSupport.isMicrolocallySobolevAt_toDistribution_quantizeSobolev`.

Conversely, an elliptic operator gains back these `m` orders: if `a` is elliptic in a conic
neighbourhood of `(x, ξ)` and `Op(a) T` is microlocally `H^s` at `(x, ξ)`, then `T` is microlocally
`H^{s + m}` there (`Distribution.IsMicrolocallySobolevAt.of_quantizeDistribution`). The same two
localizations reduce this to microlocal elliptic regularity on `H^t`,
`TauCeti.Symbol.HasCompactSpatialSupport.isMicrolocallySobolevAt_toDistribution_of_quantizeSobolev`,
for the cut-off symbol `ψ a`, which agrees with `a` near `x`. Letting `s` vary gives the `C^∞`
statement `WF(T) ⊆ WF(Op(a) T) ∪ Char(a)`, and for symbols elliptic everywhere the wave front set
and every `H^s` wave front set are preserved up to the shift by `m`.

## Main results

* `TauCeti.Symbol.quantizeDistribution_toDistribution_cutoffTempered`: on a cut-off distribution,
  `Op(a)` is the tempered quantization of a cut-off symbol with compact spatial support.
* `TauCeti.Symbol.waveFrontSet_quantizeDistribution_subset`: **microlocality**,
  `WF(Op(a) T) ⊆ WF(T)` for every distribution `T`.
* `TauCeti.Symbol.singularSupport_quantizeDistribution_subset`: **pseudolocality**,
  `singsupp (Op(a) T) ⊆ singsupp T`.
* `TauCeti.Symbol.isMicrolocallySobolevAt_quantizeDistribution`: if `T` is microlocally `H^s` at
  `(x, ξ)`, then `Op(a) T` is microlocally `H^{s - m}` there.
* `TauCeti.Symbol.sobolevWaveFrontSet_quantizeDistribution_subset`: **the order shift of the `H^s`
  wave front set**, `WF_{s - m}(Op(a) T) ⊆ WF_s(T)`.
* `TauCeti.Symbol.sobolevSingularSupport_quantizeDistribution_subset`:
  `singsupp_{s - m}(Op(a) T) ⊆ singsupp_s(T)`.
* `Distribution.IsMicrolocallySobolevAt.of_quantizeDistribution`: **microlocal elliptic
  regularity**, if `Op(a) T` is microlocally `H^s` at `(x, ξ)` and `a` is elliptic in a conic
  neighbourhood of `(x, ξ)`, then `T` is microlocally `H^{s + m}` there.
* `Distribution.IsMicrolocallySmoothAt.of_quantizeDistribution`: the same for microlocal
  smoothness, `WF(T) ⊆ WF(Op(a) T) ∪ Char(a)`.
* `TauCeti.Symbol.sobolevWaveFrontSet_quantizeDistribution_of_forall_isEllipticOn`,
  `TauCeti.Symbol.waveFrontSet_quantizeDistribution_of_forall_isEllipticOn`: for `a` elliptic near
  every position, `WF_s(Op(a) T) = WF_{s + m}(T)` and `WF(Op(a) T) = WF(T)`.
* `TauCeti.Symbol.IsEllipticAbove.sobolevWaveFrontSet_quantizeDistribution`,
  `TauCeti.ClassicalSymbol.IsElliptic.sobolevWaveFrontSet_quantizeDistribution`: for elliptic `a`,
  `WF_s(Op(a) T) = WF_{s + m}(T)`.
* `TauCeti.Symbol.IsEllipticAbove.waveFrontSet_quantizeDistribution`,
  `TauCeti.ClassicalSymbol.IsElliptic.waveFrontSet_quantizeDistribution`: for elliptic `a`,
  `WF(Op(a) T) = WF(T)`.
* `TauCeti.Symbol.vectorWaveFrontSet_quantizeDistribution_subset`: **microlocality of systems**,
  `WF(Op(a) T) ⊆ WF(T)` for `V`-valued `T`.
* `TauCeti.Symbol.vectorWaveFrontSet_inter_subset_quantizeDistribution_of_isEllipticOn`,
  `TauCeti.Symbol.vectorWaveFrontSet_subset_quantizeDistribution_union_characteristicSet`:
  **microlocal elliptic regularity of systems**, `WF(T) ⊆ WF(Op(a) T) ∪ Char(a)`.
* `TauCeti.Symbol.vectorWaveFrontSet_quantizeDistribution_sdiff_characteristicSet_eq`:
  `WF(Op(a) T) \ Char(a) = WF(T) \ Char(a)` for systems.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008, Lecture I,
  Proposition 7.3 (`WF(Pu) ⊆ WF(u)` for properly supported operators) and §7 (microlocal
  parametrices, `WF(u) ⊆ WF(Pu) ∪ Char(P)`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  §18.1 (properly supported pseudodifferential operators and wave front sets).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and its behaviour under pseudodifferential operators).
-/

public section

noncomputable section

open MeasureTheory Complex Set Metric TopologicalSpace Distribution TemperedDistribution
open scoped SchwartzMap Distributions ContDiff BesselPotentialSpace Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m R : ℝ} {a : Symbol n ℂ ℂ m}

/-- The transpose `Op(a)ᵗ φ = conj (Op(a)* φ)` of a properly supported operator on a real test
function `φ`, as in the definition of `TauCeti.Symbol.quantizeDistribution`. -/
private abbrev transposeTest (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
  TestFunction.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap
    (adjointTestFunctionCLM ha (TestFunction.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM φ))

/-- The transpose of `Op(a)` pairs with test functions as `Op(a)` does:
`∫ Op(a)ᵗ φ · u = ∫ φ · Op(a) u`. -/
private theorem integral_mul_transposeTest (ha : a.HasNearDiagonalKernel R)
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) (u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    ∫ x, transposeTest ha φ x * u x = ∫ x, (φ x : ℂ) * quantizeTestFunctionCLM ha u x := by
  have hloc (f : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
      LocallyIntegrableOn f (⊤ : Opens (CoordinateSpace n)) volume :=
    f.continuous.locallyIntegrable.locallyIntegrableOn _
  have h := congr($(quantizeDistribution_ofFun ha u) φ)
  rw [quantizeDistribution_apply, Distribution.complexPairing_ofFun (hloc u),
    Distribution.ofFun_apply (hloc _)] at h
  simpa [Complex.real_smul] using h

/-- The transpose of `Op(ψ a)` pairs with a test function `u` supported in `U` as `Op(a)` does,
when `ψ = 1` on the closed `R`-neighbourhood of `U`: `∫ Op(ψ a)ᵗ φ · u = ∫ φ · Op(a) u`. -/
private theorem integral_mul_transposeUniformCLM_cutoff_comp (ha : a.HasNearDiagonalKernel R)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {U : Set (CoordinateSpace n)} (hψU : EqOn ψ 1 (cthickening R U))
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) {u : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (huU : tsupport u ⊆ U) :
    ∫ x, transposeUniformCLM ((cutoff ℂ hψ).comp a)
        ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
        (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ)) x * u x =
      ∫ x, (φ x : ℂ) * quantizeTestFunctionCLM ha u x := by
  set hb := ((hasCompactSpatialSupport_cutoff (V := ℂ) hψ hψc).comp_right a).isUniform
  -- On `u`, `Op(ψ a) u = Op(a) u`, since `Op(a) u` is supported where `ψ = 1`.
  have hu : TestFunction.toSchwartzMapCLM ℝ u = u.hasCompactSupport.toSchwartzMap u.contDiff := by
    ext y
    rw [TestFunction.toSchwartzMapCLM_apply, HasCompactSupport.toSchwartzMap_toFun]
  have hop (x : CoordinateSpace n) :
      quantizeUniformCLM _ hb (TestFunction.toSchwartzMapCLM ℝ u) x =
        quantizeTestFunctionCLM ha u x := by
    rw [quantizeUniformCLM_apply, quantizeTestFunctionCLM_apply, hu,
      ha.quantizeSchwartzValue_cutoff_comp hψ (hψU.mono (cthickening_subset_of_subset R ?_))]
    rwa [← hu, TestFunction.coe_toSchwartzMapCLM]
  calc ∫ x, transposeUniformCLM _ hb
        (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ)) x * u x
      = ∫ x, transposeUniformCLM _ hb
          (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ)) x *
            TestFunction.toSchwartzMapCLM ℝ u x := by
        simp only [TestFunction.toSchwartzMapCLM_apply]
    _ = ∫ x, TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ) x *
          quantizeUniformCLM _ hb (TestFunction.toSchwartzMapCLM ℝ u) x :=
        (integral_mul_quantizeUniformCLM _ hb _ _).symm
    _ = ∫ x, (φ x : ℂ) * quantizeTestFunctionCLM ha u x := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        dsimp only
        rw [hop x, TestFunction.toSchwartzMapCLM_apply, TestFunction.postcompCLM_apply,
          Function.comp_apply, Complex.ofRealCLM_apply]

/-- **Transposes are local.** If `ψ = 1` on the closed `R`-neighbourhood of an open set `U`, then
the transposes of `Op(a)` and of `Op(ψ a)` agree on `U`: both operators agree on the test functions
supported in `U`, and the transposes are smooth. -/
private theorem eqOn_transposeTest (ha : a.HasNearDiagonalKernel R) {ψ : CoordinateSpace n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {U : Set (CoordinateSpace n)}
    (hU : IsOpen U) (hψU : EqOn ψ 1 (cthickening R U))
    (φ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℝ)) :
    EqOn (transposeTest ha φ) (transposeUniformCLM ((cutoff ℂ hψ).comp a)
      ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
      (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ))) U := by
  set b := transposeUniformCLM ((cutoff ℂ hψ).comp a)
    ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
    (TestFunction.toSchwartzMapCLM ℝ (TestFunction.postcompCLM Complex.ofRealCLM φ))
  -- Compare the multiplication operators by the two transposes, tested against every compactly
  -- supported Schwartz function `u` supported in `U`, viewed as a test function.
  have hK {g : CoordinateSpace n → ℂ} (hg : Continuous g) :
      ContinuousOn (fun y ↦ ContinuousLinearMap.mul ℂ ℂ (g y)) U :=
    ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp hg).continuousOn
  intro x hx
  have h := hU.eqOn_of_integral_clm_apply_eq (μ := volume) (hK (transposeTest ha φ).continuous)
    (hK b.continuous) (fun u hu huU ↦ ?_) hx
  · simpa using congr($h 1)
  set v : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) := u.toTestFunction hu (subset_univ _)
  have hv : ⇑v = u := SchwartzMap.coe_toTestFunction u hu _
  have h₁ := integral_mul_transposeTest ha φ v
  have h₂ := integral_mul_transposeUniformCLM_cutoff_comp ha hψ hψc hψU φ (u := v) (hv ▸ huU)
  rw [hv] at h₁ h₂
  simp only [ContinuousLinearMap.mul_apply']
  rw [h₁, h₂]

/-- **Localizing a properly supported operator.** Let `χ` be a test function supported in an open
set `U`, and `ψ` a compactly supported smooth function equal to `1` on the closed `R`-neighbourhood
of `U`. On the cut-off distribution `χ T`, the properly supported operator `Op(a)` is the
quantization on tempered distributions of the symbol `ψ a`, which has compact spatial support. -/
theorem quantizeDistribution_toDistribution_cutoffTempered (ha : a.HasNearDiagonalKernel R)
    {ψ : CoordinateSpace n → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U) (hψU : EqOn ψ 1 (cthickening R U))
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) {χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)}
    (hχU : tsupport χ ⊆ U) :
    quantizeDistribution ha (toDistribution ⊤ (T.cutoffTempered χ)) =
      toDistribution ⊤ (quantizeTempered ℂ ((cutoff ℂ hψ).comp a)
        ((hasCompactSpatialSupport_cutoff hψ hψc).comp_right a).isUniform
        (T.cutoffTempered χ)) := by
  ext φ
  rw [quantizeDistribution_apply, complexPairing_toDistribution, toDistribution_apply,
    quantizeTempered_apply_apply]
  refine T.cutoffTempered_apply_congr χ fun x hx ↦ ?_
  rw [TestFunction.toSchwartzMapCLM_apply, eqOn_transposeTest ha hψ hψc hU hψU φ (hχU hx)]

/-- **Reduction to the Sobolev case.** On a cut-off distribution `χ T`, which lies in some `H^t`,
`Op(a)` is the quantization on `H^t` of a symbol with compact spatial support: take the cut-off
symbol `ψ a`, with `ψ = 1` on the closed `R`-neighbourhood of a neighbourhood of `supp χ`. This
symbol agrees with `a` at the positions of `supp χ`. -/
private theorem exists_quantizeDistribution_toDistribution_cutoffTempered_eq
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ))
    (χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    ∃ (b : Symbol n ℂ ℂ (0 + m)) (hb : b.HasCompactSpatialSupport) (t : ℝ)
      (u : H^{t}(CoordinateSpace n, ℂ)), T.cutoffTempered χ = u.toDistr ∧
        quantizeDistribution ha (toDistribution ⊤ (T.cutoffTempered χ)) =
          toDistribution ⊤ (b.quantizeSobolev hb t u).toDistr ∧
        ∀ x ∈ tsupport χ, ∀ ξ, b.coefficient (x, ξ) = a.coefficient (x, ξ) := by
  -- A cutoff `ψ = 1` on the closed `R`-neighbourhood of the open set `U = thickening 1 (supp χ)`.
  have hK : IsCompact (cthickening R (cthickening 1 (tsupport χ))) :=
    χ.hasCompactSupport.isCompact.cthickening.cthickening
  obtain ⟨ψ, hψ, -, hψ1, hψc, -⟩ := hK.exists_contDiff_cutoff isOpen_univ (subset_univ _)
  have hψU : EqOn ψ 1 (cthickening R (thickening 1 (tsupport χ))) := fun x hx ↦ by
    simpa using interior_subset (hψ1 (cthickening_subset_of_subset R
      (thickening_subset_cthickening _ _) hx))
  have hb := (hasCompactSpatialSupport_cutoff (V := ℂ) hψ hψc).comp_right a
  -- `χ T ∈ H^t` for some `t`, and `Op(a) (χ T) = Op(ψ a) (χ T)` there.
  obtain ⟨t, ht⟩ := T.exists_memSobolev_cutoffTempered χ
  refine ⟨_, hb, t, ht.toBesselPotentialSpace, ht.toBesselPotentialSpace_toDistr.symm, ?_,
    fun x hx ξ ↦ ?_⟩
  · rw [toDistr_quantizeSobolev, ht.toBesselPotentialSpace_toDistr]
    exact quantizeDistribution_toDistribution_cutoffTempered ha hψ hψc isOpen_thickening hψU T
      (self_subset_thickening one_pos _)
  · have hx1 : ψ x = 1 :=
      hψU (self_subset_cthickening _ (self_subset_thickening one_pos _ hx))
    simp [hx1]

/-- Microlocality on cut-off distributions: if `χ T` is microlocally smooth at `(x₀, ξ₀)`, so is
`Op(a) (χ T)`. Since `χ T` lies in some `H^t` and `Op(a) (χ T) = Op(ψ a) (χ T)` for a cutoff `ψ`,
this is microlocality of operators with compact spatial support on `H^t`. -/
private theorem isMicrolocallySmoothAt_quantizeDistribution_toDistribution_cutoffTempered
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ))
    (χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) {x₀ ξ₀ : CoordinateSpace n} (hξ₀ : ξ₀ ≠ 0)
    (h : (toDistribution ⊤ (T.cutoffTempered χ)).IsMicrolocallySmoothAt x₀ ξ₀) :
    (quantizeDistribution ha (toDistribution ⊤ (T.cutoffTempered χ))).IsMicrolocallySmoothAt
      x₀ ξ₀ := by
  obtain ⟨b, hb, t, u, hu, hOp, -⟩ :=
    exists_quantizeDistribution_toDistribution_cutoffTempered_eq ha T χ
  by_contra hn
  have hmem := waveFrontSet_toDistribution_quantizeSobolev_subset hb t u
    (hOp ▸ mem_waveFrontSet_iff.2 ⟨trivial, hξ₀, hn⟩)
  exact (mem_waveFrontSet_iff.1 (hu ▸ hmem)).2.2 h

/-- **Localizing the input.** For every point `x₀` there is a test function `χ`, supported on a
neighbourhood of `x₀`, such that `T - χ T` vanishes near `x₀`, and so does `Op(a) (T - χ T)`: take
`χ = 1` on a ball about `x₀` of radius larger than `R`, so that `Op(a)`, which enlarges supports by
at most `R`, maps `T - χ T` to a distribution vanishing near `x₀`. -/
private theorem exists_notMem_dsupport_sub_cutoffTempered (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) (x₀ : CoordinateSpace n) :
    ∃ χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ),
      x₀ ∉ dsupport (T - toDistribution ⊤ (T.cutoffTempered χ)) ∧
        x₀ ∉ dsupport (quantizeDistribution ha (T - toDistribution ⊤ (T.cutoffTempered χ))) ∧
          tsupport χ ∈ 𝓝 x₀ := by
  -- A cutoff `χ = 1` on `ball x₀ r`, where `r > R`.
  set r : ℝ := |R| + 1
  have hr₀ : 0 < r := by positivity
  let ρ : ContDiffBump x₀ := ⟨r, 2 * r, hr₀, by linarith⟩
  let χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ) :=
    ⟨fun x ↦ (ρ x : ℂ), ofRealCLM.contDiff.comp ρ.contDiff,
      ρ.hasCompactSupport.comp_left ofReal_zero, subset_univ _⟩
  -- `χ` is the bump function `ρ`, viewed as a complex-valued test function.
  have hχx (x : CoordinateSpace n) : χ x = ρ x := (rfl)
  -- `T - χ T` vanishes on `ball x₀ r`.
  have hdsupp : dsupport (T - toDistribution ⊤ (T.cutoffTempered χ)) ⊆ (ball x₀ r)ᶜ := by
    refine subset_compl_comm.1 fun x hx hx' ↦
      ((T.isVanishingOn_sub_toDistribution_cutoffTempered fun y hy ↦ ?_).disjoint_dsupport
        isOpen_ball).ne_of_mem hx hx' rfl
    rw [hχx, ρ.one_of_mem_closedBall (ball_subset_closedBall hy), ofReal_one]
  exact ⟨χ, fun h ↦ hdsupp h (mem_ball_self hr₀), fun h ↦ notMem_cthickening_compl_ball
    (by linarith [le_abs_self R]) hr₀ (cthickening_subset_of_subset R hdsupp
      (dsupport_quantizeDistribution_subset ha _ h)),
    Filter.mem_of_superset (ball_mem_nhds x₀ hr₀) fun y hy ↦ subset_tsupport _ (by
      rw [Function.mem_support, hχx, ρ.one_of_mem_closedBall (ball_subset_closedBall hy)]
      exact one_ne_zero)⟩

/-- **Microlocality of properly supported pseudodifferential operators.** For a scalar symbol `a`
whose quantization has kernel supported within distance `R` of the diagonal, and every distribution
`T` on `ℝⁿ`, the wave front set of `Op(a) T` is contained in the wave front set of `T`:
`WF(Op(a) T) ⊆ WF(T)`. -/
theorem waveFrontSet_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).waveFrontSet ⊆ T.waveFrontSet := by
  rintro ⟨x₀, ξ₀⟩ hp
  obtain ⟨-, hξ₀, hnot⟩ := mem_waveFrontSet_iff.1 hp
  refine mem_waveFrontSet_iff.2 ⟨trivial, hξ₀, fun hT ↦ hnot ?_⟩
  obtain ⟨χ, hTD, hOpTD, -⟩ := exists_notMem_dsupport_sub_cutoffTempered ha T x₀
  set D := toDistribution ⊤ (T.cutoffTempered χ)
  -- `χ T` agrees with `T` near `x₀`, so it is microlocally smooth at `(x₀, ξ₀)`.
  have hD : D.IsMicrolocallySmoothAt x₀ ξ₀ := by
    convert hT.add ((isMicrolocallySmoothAt_of_notMem_dsupport trivial hTD ξ₀).smul (-1)) using 1
    module
  rw [← add_sub_cancel D T, map_add]
  exact (isMicrolocallySmoothAt_quantizeDistribution_toDistribution_cutoffTempered ha T χ hξ₀
    hD).add (isMicrolocallySmoothAt_of_notMem_dsupport trivial hOpTD ξ₀)

/-- **Pseudolocality of properly supported pseudodifferential operators.** For a scalar symbol
`a` whose quantization has kernel supported within distance `R` of the diagonal, and every
distribution `T` on `ℝⁿ`, `Op(a) T` is smooth wherever `T` is: the singular support of `Op(a) T` is
contained in that of `T`. -/
theorem singularSupport_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).singularSupport ⊆ T.singularSupport := by
  rw [← fst_image_waveFrontSet, ← fst_image_waveFrontSet]
  exact image_mono (waveFrontSet_quantizeDistribution_subset ha T)

/-! ### The order shift of the `H^s` wave front set -/

/-- The `H^s` order shift on cut-off distributions: if `χ T` is microlocally `H^s` at `(x₀, ξ₀)`,
then `Op(a) (χ T)` is microlocally `H^{s - m}` there. Since `χ T` lies in some `H^t` and
`Op(a) (χ T) = Op(ψ a) (χ T)` for a cutoff `ψ`, this is the order shift for operators with compact
spatial support on `H^t`. -/
private theorem isMicrolocallySobolevAt_quantizeDistribution_toDistribution_cutoffTempered
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ))
    (χ : 𝓓((⊤ : Opens (CoordinateSpace n)), ℂ)) {s : ℝ} {x₀ ξ₀ : CoordinateSpace n}
    (h : (toDistribution ⊤ (T.cutoffTempered χ)).IsMicrolocallySobolevAt s x₀ ξ₀) :
    (quantizeDistribution ha (toDistribution ⊤ (T.cutoffTempered χ))).IsMicrolocallySobolevAt
      (s - m) x₀ ξ₀ := by
  obtain ⟨b, hb, t, u, hu, hOp, -⟩ :=
    exists_quantizeDistribution_toDistribution_cutoffTempered_eq ha T χ
  rw [hOp]
  -- The cut-off symbol `b` has order `0 + m`.
  convert hb.isMicrolocallySobolevAt_toDistribution_quantizeSobolev (hu ▸ h) using 2
  rw [zero_add]

/-- **Microlocal Sobolev mapping of properly supported pseudodifferential operators.** For a scalar
symbol `a` of order `m` whose quantization has kernel supported within distance `R` of the
diagonal, if a distribution `T` on `ℝⁿ` is microlocally `H^s` at `(x₀, ξ₀)`, then `Op(a) T` is
microlocally `H^{s - m}` at `(x₀, ξ₀)`. -/
theorem isMicrolocallySobolevAt_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)} {s : ℝ} {x₀ ξ₀ : CoordinateSpace n}
    (hT : T.IsMicrolocallySobolevAt s x₀ ξ₀) :
    (quantizeDistribution ha T).IsMicrolocallySobolevAt (s - m) x₀ ξ₀ := by
  obtain ⟨χ, hTD, hOpTD, -⟩ := exists_notMem_dsupport_sub_cutoffTempered ha T x₀
  set D := toDistribution ⊤ (T.cutoffTempered χ)
  -- `χ T` agrees with `T` near `x₀`, so it is microlocally `H^s` at `(x₀, ξ₀)`.
  have hD : D.IsMicrolocallySobolevAt s x₀ ξ₀ := by
    convert hT.add (((isLocallySobolevAt_of_notMem_dsupport trivial hTD s).isMicrolocallySobolevAt
      ξ₀).smul (-1)) using 1
    module
  rw [← add_sub_cancel D T, map_add]
  exact (isMicrolocallySobolevAt_quantizeDistribution_toDistribution_cutoffTempered ha T χ
    hD).add ((isLocallySobolevAt_of_notMem_dsupport trivial hOpTD _).isMicrolocallySobolevAt ξ₀)

/-- **The order shift of the `H^s` wave front set.** A scalar pseudodifferential operator of order
`m` whose kernel is supported within distance `R` of the diagonal loses at most `m` orders of
microlocal Sobolev regularity: for every distribution `T` on `ℝⁿ` and every real `s`,
`WF_{s - m}(Op(a) T) ⊆ WF_s(T)`. -/
theorem sobolevWaveFrontSet_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R) (s : ℝ)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).sobolevWaveFrontSet (s - m) ⊆ T.sobolevWaveFrontSet s := by
  rintro ⟨x, ξ⟩ hp
  rw [mem_sobolevWaveFrontSet_iff] at hp ⊢
  exact ⟨hp.1, hp.2.1, fun hT ↦ hp.2.2 (isMicrolocallySobolevAt_quantizeDistribution ha hT)⟩

/-- **The order shift of the `H^s` singular support.** For a scalar symbol `a` of order `m` whose
quantization has kernel supported within distance `R` of the diagonal, `Op(a) T` is `H^{s - m}`
near every point near which the distribution `T` is `H^s`:
`singsupp_{s - m}(Op(a) T) ⊆ singsupp_s(T)`. -/
theorem sobolevSingularSupport_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).sobolevSingularSupport (s - m) ⊆ T.sobolevSingularSupport s := by
  rw [← fst_image_sobolevWaveFrontSet, ← fst_image_sobolevWaveFrontSet]
  exact image_mono (sobolevWaveFrontSet_quantizeDistribution_subset ha s T)

end Symbol

end TauCeti

/-! ### Microlocal elliptic regularity -/

namespace Distribution

open TauCeti TauCeti.Symbol Set Filter
open scoped Topology

variable {n : ℕ} {m R R' s : ℝ} {a : Symbol n ℂ ℂ m} {T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)}
  {x ξ : CoordinateSpace n} {U Γ : Set (CoordinateSpace n)}

/-- **Microlocal elliptic regularity of properly supported pseudodifferential operators.** Let `a`
be a scalar symbol of order `m` whose quantization has kernel supported within distance `R` of the
diagonal, and which is elliptic at the frequencies of norm at least `R'` in an open cone `Γ ∋ ξ`,
at all positions of a neighbourhood `U` of `x`. If `Op(a) T` is microlocally `H^s` at `(x, ξ)` for
a distribution `T` on `ℝⁿ`, then `T` is microlocally `H^{s + m}` at `(x, ξ)`. Thus
`WF_{s + m}(T) ⊆ WF_s(Op(a) T) ∪ Char(a)`, where `Char(a)` is the set of `(x, ξ)`, `ξ ≠ 0`, at which
`a` is not elliptic in this conic sense. No a priori regularity of `T` is assumed, and the symbol
needs neither compact spatial support nor estimates uniform in the position. -/
theorem IsMicrolocallySobolevAt.of_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    (hU : U ∈ 𝓝 x) (hΓ : IsOpen Γ) (hcone : ∀ r : ℝ, 0 < r → ∀ η ∈ Γ, r • η ∈ Γ) (hξ : ξ ∈ Γ)
    (hell : a.IsEllipticOn {p | p.1 ∈ U ∧ p.2 ∈ Γ ∧ R' ≤ ‖p.2‖})
    (h : (quantizeDistribution ha T).IsMicrolocallySobolevAt s x ξ) :
    T.IsMicrolocallySobolevAt (s + m) x ξ := by
  obtain ⟨χ, hTD, hOpTD, hχx⟩ := exists_notMem_dsupport_sub_cutoffTempered ha T x
  -- `Op(a) (χ T)` agrees with `Op(a) T` near `x`, so it is microlocally `H^s` at `(x, ξ)`.
  have hOpD : (quantizeDistribution ha
      (toDistribution ⊤ (T.cutoffTempered χ))).IsMicrolocallySobolevAt s x ξ := by
    convert h.add (((isLocallySobolevAt_of_notMem_dsupport trivial hOpTD s).isMicrolocallySobolevAt
      ξ).smul (-1)) using 1
    rw [map_sub]
    module
  -- `χ T = u ∈ H^t` and `Op(a) (χ T) = Op(b) u`, where `b` has compact spatial support and agrees
  -- with `a` on `tsupport χ`, a neighbourhood of `x`; so `b` is elliptic near `(x, ξ)`.
  obtain ⟨b, hb, t, u, hu, hOp, hba⟩ :=
    exists_quantizeDistribution_toDistribution_cutoffTempered_eq ha T χ
  have hellb : b.IsEllipticOn {p | p.1 ∈ U ∩ tsupport χ ∧ p.2 ∈ Γ ∧ R' ≤ ‖p.2‖} := by
    refine (hell.mono fun _ hp ↦ ?_).congr (zero_add m) fun p hp ↦ hba p.1 hp.1.2 p.2
    exact ⟨hp.1.1, hp.2⟩
  -- Microlocal elliptic regularity on `H^t` makes `χ T` microlocally `H^{s + m}` at `(x, ξ)`, and
  -- `T - χ T` vanishes near `x`.
  have hD := hb.isMicrolocallySobolevAt_toDistribution_of_quantizeSobolev (Ω := ⊤)
    (inter_mem hU hχx) hΓ hcone hξ hellb (hOp ▸ hOpD)
  rw [zero_add, ← hu] at hD
  convert hD.add ((isLocallySobolevAt_of_notMem_dsupport trivial hTD _).isMicrolocallySobolevAt ξ)
    using 1
  exact (add_sub_cancel _ _).symm

/-- **Microlocal elliptic regularity of properly supported pseudodifferential operators, for
smoothness.** Let `a` be a scalar symbol whose quantization has kernel supported within distance
`R` of the diagonal, and which is elliptic at the frequencies of norm at least `R'` in an open cone
`Γ ∋ ξ`, at all positions of a neighbourhood `U` of `x`. If `Op(a) T` is microlocally smooth at
`(x, ξ)` for a distribution `T` on `ℝⁿ`, then so is `T`: `WF(T) ⊆ WF(Op(a) T) ∪ Char(a)`. -/
theorem IsMicrolocallySmoothAt.of_quantizeDistribution (ha : a.HasNearDiagonalKernel R)
    (hU : U ∈ 𝓝 x) (hΓ : IsOpen Γ) (hcone : ∀ r : ℝ, 0 < r → ∀ η ∈ Γ, r • η ∈ Γ) (hξ : ξ ∈ Γ)
    (hell : a.IsEllipticOn {p | p.1 ∈ U ∧ p.2 ∈ Γ ∧ R' ≤ ‖p.2‖})
    (h : (quantizeDistribution ha T).IsMicrolocallySmoothAt x ξ) :
    T.IsMicrolocallySmoothAt x ξ := by
  refine isMicrolocallySmoothAt_of_eventually_forall_isMicrolocallySobolevAt ?_
  -- Near `(x, ξ)`, `Op(a) T` is microlocally `H^s` for every `s`, and `a` stays elliptic.
  filter_upwards [isMicrolocallySmoothAt_iff_eventually_forall_isMicrolocallySobolevAt.1 h,
    prod_mem_nhds (interior_mem_nhds.2 hU) (hΓ.mem_nhds hξ)] with p hp hpW s
  simpa using (hp (s - m)).of_quantizeDistribution ha (mem_interior_iff_mem_nhds.1 hpW.1) hΓ hcone
    hpW.2 hell

end Distribution

namespace TauCeti

open Distribution Set Metric
open scoped Topology

variable {n : ℕ} {m R R' : ℝ}

namespace Symbol

/-- **Locally elliptic operators shift the `H^s` wave front set by exactly their order.** If the
scalar symbol `a` of order `m` is elliptic near every position, at the frequencies of norm at least
a radius depending on the position, and `Op(a)` has kernel supported within distance `R` of the
diagonal, then `WF_s(Op(a) T) = WF_{s + m}(T)` for every distribution `T` on `ℝⁿ` and every real
`s`. -/
theorem sobolevWaveFrontSet_quantizeDistribution_of_forall_isEllipticOn {a : Symbol n ℂ ℂ m}
    (hell : ∀ x, ∃ U ∈ 𝓝 x, ∃ R' : ℝ, a.IsEllipticOn {p | p.1 ∈ U ∧ R' ≤ ‖p.2‖})
    (ha : a.HasNearDiagonalKernel R) (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet (s + m) := by
  refine Subset.antisymm
    (by simpa using sobolevWaveFrontSet_quantizeDistribution_subset ha (s + m) T) fun p hp ↦ ?_
  rw [mem_sobolevWaveFrontSet_iff] at hp ⊢
  obtain ⟨U, hU, R', hell⟩ := hell p.1
  exact ⟨hp.1, hp.2.1, fun h ↦ hp.2.2 (h.of_quantizeDistribution ha hU isOpen_univ
    (fun _ _ _ _ ↦ trivial) trivial (hell.mono fun q hq ↦ ⟨hq.1, hq.2.2⟩))⟩

/-- **Locally elliptic operators preserve the wave front set.** If the scalar symbol `a` is
elliptic near every position, at the frequencies of norm at least a radius depending on the
position, and `Op(a)` has kernel supported within distance `R` of the diagonal, then
`WF(Op(a) T) = WF(T)` for every distribution `T` on `ℝⁿ`. -/
theorem waveFrontSet_quantizeDistribution_of_forall_isEllipticOn {a : Symbol n ℂ ℂ m}
    (hell : ∀ x, ∃ U ∈ 𝓝 x, ∃ R' : ℝ, a.IsEllipticOn {p | p.1 ∈ U ∧ R' ≤ ‖p.2‖})
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (quantizeDistribution ha T).waveFrontSet = T.waveFrontSet := by
  refine Subset.antisymm (waveFrontSet_quantizeDistribution_subset ha T) fun p hp ↦ ?_
  rw [mem_waveFrontSet_iff] at hp ⊢
  obtain ⟨U, hU, R', hell⟩ := hell p.1
  exact ⟨hp.1, hp.2.1, fun h ↦ hp.2.2 (h.of_quantizeDistribution ha hU isOpen_univ
    (fun _ _ _ _ ↦ trivial) trivial (hell.mono fun q hq ↦ ⟨hq.1, hq.2.2⟩))⟩

end Symbol

/-- A symbol elliptic above a radius is elliptic near every position. -/
private theorem Symbol.IsEllipticAbove.forall_exists_isEllipticOn {a : Symbol n ℂ ℂ m}
    (hell : a.IsEllipticAbove R') :
    ∀ x : CoordinateSpace n, ∃ U ∈ 𝓝 x, ∃ R'' : ℝ, a.IsEllipticOn {p | p.1 ∈ U ∧ R'' ≤ ‖p.2‖} :=
  fun _ ↦ ⟨univ, Filter.univ_mem, R',
    (isEllipticAbove_iff_isEllipticOn.1 hell).mono fun _ hp ↦ hp.2⟩

/-- An elliptic classical symbol is elliptic near every position, above a radius depending on the
position. -/
private theorem ClassicalSymbol.IsElliptic.forall_exists_isEllipticOn
    {a : ClassicalSymbol n ℂ ℂ m} (hell : a.IsElliptic) :
    ∀ x : CoordinateSpace n, ∃ U ∈ 𝓝 x, ∃ R' : ℝ,
      a.toSymbol.IsEllipticOn {p | p.1 ∈ U ∧ R' ≤ ‖p.2‖} := fun x ↦
  ⟨closedBall x 1, closedBall_mem_nhds x one_pos,
    hell.exists_isEllipticOn (isCompact_closedBall x 1)⟩

/-- **Elliptic operators shift the `H^s` wave front set by exactly their order.** If the scalar
symbol `a` of order `m` is elliptic above some radius and `Op(a)` has kernel supported within
distance `R` of the diagonal, then `WF_s(Op(a) T) = WF_{s + m}(T)` for every distribution `T` on
`ℝⁿ` and every real `s`. -/
theorem Symbol.IsEllipticAbove.sobolevWaveFrontSet_quantizeDistribution {a : Symbol n ℂ ℂ m}
    (hell : a.IsEllipticAbove R') (ha : a.HasNearDiagonalKernel R) (s : ℝ)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (Symbol.quantizeDistribution ha T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet (s + m) :=
  Symbol.sobolevWaveFrontSet_quantizeDistribution_of_forall_isEllipticOn
    hell.forall_exists_isEllipticOn ha s T

/-- **Elliptic operators preserve the wave front set.** If the scalar symbol `a` is elliptic above
some radius and `Op(a)` has kernel supported within distance `R` of the diagonal, then
`WF(Op(a) T) = WF(T)` for every distribution `T` on `ℝⁿ`. -/
theorem Symbol.IsEllipticAbove.waveFrontSet_quantizeDistribution {a : Symbol n ℂ ℂ m}
    (hell : a.IsEllipticAbove R') (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (Symbol.quantizeDistribution ha T).waveFrontSet = T.waveFrontSet :=
  Symbol.waveFrontSet_quantizeDistribution_of_forall_isEllipticOn
    hell.forall_exists_isEllipticOn ha T

/-- **Elliptic classical operators shift the `H^s` wave front set by exactly their order.** If the
classical symbol `a` of order `m` is elliptic and `Op(a)` has kernel supported within distance `R`
of the diagonal, then `WF_s(Op(a) T) = WF_{s + m}(T)` for every distribution `T` on `ℝⁿ` and every
real `s`. -/
theorem ClassicalSymbol.IsElliptic.sobolevWaveFrontSet_quantizeDistribution
    {a : ClassicalSymbol n ℂ ℂ m} (hell : a.IsElliptic) (ha : a.toSymbol.HasNearDiagonalKernel R)
    (s : ℝ) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (Symbol.quantizeDistribution ha T).sobolevWaveFrontSet s = T.sobolevWaveFrontSet (s + m) :=
  Symbol.sobolevWaveFrontSet_quantizeDistribution_of_forall_isEllipticOn
    hell.forall_exists_isEllipticOn ha s T

/-- **Elliptic classical operators preserve the wave front set.** If the classical symbol `a` is
elliptic and `Op(a)` has kernel supported within distance `R` of the diagonal, then
`WF(Op(a) T) = WF(T)` for every distribution `T` on `ℝⁿ`. -/
theorem ClassicalSymbol.IsElliptic.waveFrontSet_quantizeDistribution
    {a : ClassicalSymbol n ℂ ℂ m} (hell : a.IsElliptic) (ha : a.toSymbol.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), ℂ)) :
    (Symbol.quantizeDistribution ha T).waveFrontSet = T.waveFrontSet :=
  Symbol.waveFrontSet_quantizeDistribution_of_forall_isEllipticOn
    hell.forall_exists_isEllipticOn ha T

end TauCeti

/-! ### Systems

A symbol `a` with values in `V →L[ℂ] W`, for finite-dimensional complex inner product spaces `V`
and `W`, whose quantization has kernel supported within distance `R` of the diagonal, acts on all
`V`-valued distributions on `ℝⁿ` (`TauCeti.Symbol.quantizeDistribution`). In a local frame this is
how a properly supported operator between vector bundles acts on distributional sections in a
chart. Both microlocality and microlocal elliptic regularity hold for these systems, for the wave
front sets of vector-valued distributions (`Distribution.vectorWaveFrontSet`). Microlocality
reduces to the scalar case entry by entry
(`TauCeti.Symbol.mapCLM_quantizeDistribution_eq_sum`). Microlocal elliptic regularity reduces to the
statement for systems on `H^r`,
`TauCeti.Symbol.vectorWaveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn`:
a cut-off distribution `χ T` lies in some `H^r(ℝⁿ; V)`, and the components of `Op(ψ a) (χ T)` are
`ψ (ℓ ∘ Op(a) T)` when `χ = 1` on the closed `R`-neighbourhood of the support of `ψ`
(`TauCeti.Symbol.toDistr_postcomp_quantizeSobolev_smulLeft`). -/

namespace TauCeti

namespace Symbol

open Distribution Set Metric
open scoped Topology

variable {n : ℕ} {m R R' : ℝ} {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [FiniteDimensional ℂ W] {a : Symbol n V W m}

/-- **Microlocality of properly supported systems.** For a symbol `a` with values in `V →L[ℂ] W`
whose quantization has kernel supported within distance `R` of the diagonal, and every `V`-valued
distribution `T` on `ℝⁿ`, `WF(Op(a) T) ⊆ WF(T)`, for the wave front sets of vector-valued
distributions. -/
theorem vectorWaveFrontSet_quantizeDistribution_subset (ha : a.HasNearDiagonalKernel R)
    (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    (quantizeDistribution ha T).vectorWaveFrontSet ⊆ T.vectorWaveFrontSet := by
  intro p hp
  obtain ⟨ℓ, hp⟩ := mem_vectorWaveFrontSet_iff.1 hp
  rw [mapCLM_quantizeDistribution_eq_sum ha (Module.finBasis ℂ V) ℓ] at hp
  obtain ⟨j, -, hj⟩ := mem_iUnion₂.1 (waveFrontSet_sum_subset _ _ hp)
  exact waveFrontSet_mapCLM_subset_vectorWaveFrontSet _ _
    (waveFrontSet_quantizeDistribution_subset _ _ hj)

/-- **Microlocal elliptic regularity of properly supported systems on a conic region.** Let `a` be
a symbol with values in `V →L[ℂ] W` whose quantization has kernel supported within distance `R` of
the diagonal, and which is elliptic on the points `(x, ξ)` with `x ∈ U`, `ξ ∈ Γ` and `‖ξ‖ ≥ R'`,
for an open set `U` and an open cone `Γ`. Then `Op(a)` keeps every singularity in `U × Γ` of a
`V`-valued distribution `T` on `ℝⁿ`: `WF(T) ∩ (U × Γ) ⊆ WF(Op(a) T)`. No a priori regularity of
`T` is assumed, and the symbol needs neither compact spatial support nor estimates uniform in the
position. -/
theorem vectorWaveFrontSet_inter_subset_quantizeDistribution_of_isEllipticOn
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V))
    {U Γ : Set (CoordinateSpace n)} (hU : IsOpen U) (hΓ : IsOpen Γ)
    (hcone : ∀ s : ℝ, 0 < s → ∀ η ∈ Γ, s • η ∈ Γ)
    (hell : a.IsEllipticOn {p | p.1 ∈ U ∧ p.2 ∈ Γ ∧ R' ≤ ‖p.2‖}) :
    T.vectorWaveFrontSet ∩ U ×ˢ Γ ⊆ (quantizeDistribution ha T).vectorWaveFrontSet := by
  rintro ⟨x, ξ⟩ ⟨hp, hx, hξ⟩
  -- A cutoff `ψ` equal to `1` on an open neighbourhood `O` of `x`, and a cutoff `χ` equal to `1`
  -- on the closed `R`-neighbourhood of the support of `ψ`.
  obtain ⟨ψ, O, hO, hxO, hψO, -⟩ := TestFunction.exists_eqOn_one_tsupport_subset (n := ⊤)
    (𝕜 := ℂ) (Ω := ⊤) Filter.univ_mem (mem_univ x)
  obtain ⟨χ, hχ1, -⟩ := TestFunction.exists_complex_cutoff_tsupport_subset (n := ⊤) (Ω := ⊤)
    (ψ.hasCompactSupport.isCompact.cthickening (r := R)) isOpen_univ (subset_univ _) (by simp)
  have hχψ (y : CoordinateSpace n) (hy : y ∈ cthickening R (tsupport ψ)) : χ y = 1 :=
    hχ1.self_of_nhdsSet y hy
  have hOψ : O ⊆ tsupport ψ := fun y hy ↦ subset_tsupport _ (by simp [hψO hy])
  -- Some `u ∈ H^r(ℝⁿ; V)` has the cut-off coordinates `χ (c_j ∘ T)`, so it agrees with `T` on
  -- `O` and is singular at `(x, ξ)`.
  set b := Module.finBasis ℂ V
  obtain ⟨r, u, hu⟩ := exists_toDistr_postcomp_coord_eq_cutoffTempered b T χ
  have hpu : (x, ξ) ∈ (toDistribution ⊤ u.toDistr).vectorWaveFrontSet := by
    rw [vectorWaveFrontSet_eq_iUnion_basis b] at hp ⊢
    obtain ⟨j, hj⟩ := mem_iUnion.1 hp
    refine mem_iUnion.2 ⟨j, ?_⟩
    rw [← BesselPotentialSpace.toDistribution_toDistr_postcomp, hu j]
    exact (mem_waveFrontSet_iff_of_isVanishingOn_sub hO hxO
      (isVanishingOn_sub_toDistribution_cutoffTempered _ fun y hy ↦
        hχψ y (self_subset_cthickening _ (hOψ hy)))).1 hj
  -- `ψ a` agrees with `a` on `O`, so it is elliptic on `(U ∩ O) × Γ` at large frequencies, and the
  -- statement on `H^r` puts `(x, ξ)` in the wave front set of `Op(ψ a) u`.
  have hb := hasCompactSpatialSupport_smulLeft ψ.contDiff ψ.hasCompactSupport a
  have hellb : (smulLeft ψ.contDiff a).IsEllipticOn
      {q | q.1 ∈ U ∩ O ∧ q.2 ∈ Γ ∧ R' ≤ ‖q.2‖} :=
    (hell.mono (S' := {q | q.1 ∈ U ∩ O ∧ q.2 ∈ Γ ∧ R' ≤ ‖q.2‖})
      fun _ hq ↦ ⟨hq.1.1, hq.2⟩).congr rfl fun q hq ↦ by
      rw [coefficient_smulLeft, hψO hq.1.2, Pi.one_apply, one_smul]
  obtain ⟨ℓ, hℓ⟩ := mem_vectorWaveFrontSet_iff.1
    (vectorWaveFrontSet_toDistribution_inter_subset_quantizeSobolev_of_isEllipticOn hb r u
      (hU.inter hO) hΓ hcone hellb ⟨hpu, ⟨hx, hxO⟩, hξ⟩)
  -- The component of `Op(ψ a) u` along `ℓ` is `ψ (ℓ ∘ Op(a) T)`, which agrees with `ℓ ∘ Op(a) T`
  -- on `O`.
  rw [← BesselPotentialSpace.toDistribution_toDistr_postcomp,
    toDistr_postcomp_quantizeSobolev_smulLeft b ha hχψ T u hu ℓ] at hℓ
  exact waveFrontSet_mapCLM_subset_vectorWaveFrontSet ℓ _
    ((mem_waveFrontSet_iff_of_isVanishingOn_sub hO hxO
      (isVanishingOn_sub_toDistribution_cutoffTempered _ fun y hy ↦ hψO hy)).2 hℓ)

/-- **Microlocal elliptic regularity of properly supported systems.** For a symbol `a` with values
in `V →L[ℂ] W` whose quantization has kernel supported within distance `R` of the diagonal, and
every `V`-valued distribution `T` on `ℝⁿ`, every singularity of `T` is a singularity of `Op(a) T`
or a characteristic point of `a`: `WF(T) ⊆ WF(Op(a) T) ∪ Char(a)`. -/
theorem vectorWaveFrontSet_subset_quantizeDistribution_union_characteristicSet
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    T.vectorWaveFrontSet ⊆
      (quantizeDistribution ha T).vectorWaveFrontSet ∪ a.characteristicSet :=
  subset_union_characteristicSet (fun _ hp ↦ (vectorWaveFrontSet_subset _ hp).2)
    fun hU hΓ hcone _ hell ↦
      vectorWaveFrontSet_inter_subset_quantizeDistribution_of_isEllipticOn ha T hU hΓ hcone hell

/-- Off the characteristic set of a symbol `a` with values in `V →L[ℂ] W` whose quantization has
kernel supported within distance `R` of the diagonal, `Op(a)` neither creates nor removes
singularities: `WF(Op(a) T) \ Char(a) = WF(T) \ Char(a)` for every `V`-valued distribution `T` on
`ℝⁿ`. -/
theorem vectorWaveFrontSet_quantizeDistribution_sdiff_characteristicSet_eq
    (ha : a.HasNearDiagonalKernel R) (T : 𝓓'((⊤ : Opens (CoordinateSpace n)), V)) :
    (quantizeDistribution ha T).vectorWaveFrontSet \ a.characteristicSet =
      T.vectorWaveFrontSet \ a.characteristicSet :=
  sdiff_characteristicSet_eq_of_subset (vectorWaveFrontSet_quantizeDistribution_subset ha T)
    (vectorWaveFrontSet_subset_quantizeDistribution_union_characteristicSet ha T)

end Symbol

end TauCeti
