/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
public import TauCeti.Analysis.Pseudodifferential.Manifold.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Pseudodifferential.CompactOperator

/-!
# Compact pseudodifferential operators on a compact manifold

Let `M` be a manifold modelled on `ℝⁿ`, with Sobolev spaces `H^s(M)` defined through chart
partitions: finitely many cutoffs `ψᵢ` in charts `cᵢ` whose readings `ψᵢ ∘ cᵢ` on `M` add up to `1`
(`TauCeti.chartSobolevSpace`), which forces `M` to be compact. A classical pseudodifferential
operator `P` of order `m` extends to a bounded operator `H^s(M) → H^{s - m}(M)`
(`TauCeti.chartSobolevExtension`). This file proves that this extension is **compact exactly when
the principal symbol of `P` vanishes** (`TauCeti.isCompactOperator_chartSobolevExtension_iff`),
for every real `s`. Equivalently, by `TauCeti.classicalPrincipalSymbol_eq_zero_iff`, the order-`m`
operators that are compact `H^s(M) → H^{s - m}(M)` are those of order `m - 1`. So compactness at
the critical order does not depend on `s`, nor on the chart partitions.

* If `σ_m(P) = 0`, then `P` has order `m - 1`, and Rellich's theorem makes its extension
  compact (`TauCeti.isCompactOperator_chartSobolevExtension_of_mem`).
* Conversely, suppose the extension `T` is compact, and let `x ∈ M`. In the preferred chart `c`
  at `x`, with a cutoff `χ` equal to `1` at `c x`, the chart compression
  `u ↦ χ · (P ((χ u) ∘ c)) ∘ c⁻¹` of `P` is the quantization `Op(a)` of a classical symbol `a`
  with compact spatial support. Its extension `Op(a) : H^s(ℝⁿ) → H^{s - m}(ℝⁿ)` factors as the
  pullback `H^s(ℝⁿ) → H^s(M)` through `χ` (`TauCeti.chartSobolevPullback`), then `T`, then the
  reading `H^{s - m}(M) → H^{s - m}(ℝⁿ)` through `χ` (`TauCeti.chartSobolevReading`). So `Op(a)`
  is compact, and its principal symbol vanishes by the Euclidean theorem
  (`TauCeti.ClassicalSymbol.principal_eq_zero_of_isCompactOperator`), which tests `Op(a)` on
  high-frequency wave packets. At `c x` that principal symbol is
  `χ(c x)² σ_m(P)(x, ξ) = σ_m(P)(x, ξ)`
  (`TauCeti.coefficient_principal_apply_eq_classicalPrincipalSymbol`).

## Main results

* `TauCeti.classicalPrincipalSymbol_eq_zero_of_isCompactOperator`: if the extension
  `H^s(M) → H^{s - m}(M)` of `P` is compact, then `σ_m(P) = 0`.
* `TauCeti.isCompactOperator_chartSobolevExtension_of_classicalPrincipalSymbol_eq_zero`: if
  `σ_m(P) = 0`, then the extension `H^s(M) → H^{s - m}(M)` is compact.
* `TauCeti.isCompactOperator_chartSobolevExtension_iff`: the extension is compact if and only if
  `σ_m(P) = 0`.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators I*, Ann. of Math. 87 (1968),
  (5.2) (on a compact manifold, the operators of order `m` with vanishing principal symbol are the
  compact ones `H^s → H^{s - m}`).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (testing
  pseudodifferential operators on high-frequency wave packets).
-/

public section

open OpenPartialHomeomorph
open scoped ContDiff Manifold Distributions SchwartzMap

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯} {m : ℝ}
  {ι κ : Type*} [Fintype ι] [Fintype κ] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {ψ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)}
  {c' : κ → OpenPartialHomeomorph M (CoordinateSpace n)}
  {hc' : ∀ j, c' j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {φ : ∀ j, 𝓓(⟨(c' j).target, (c' j).open_target⟩, ℝ)}

/-- **Compact operators have vanishing principal symbol.** Let `P` be a classical
pseudodifferential operator of order `m`, and `ψᵢ`, `φⱼ` two chart partitions. If for some real `s`
the extension of `P` to `H^s(M) → H^{s - m}(M)` is a compact operator, then the principal symbol
`σ_m(P)` vanishes at every covector. -/
theorem classicalPrincipalSymbol_eq_zero_of_isCompactOperator
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) {s : ℝ}
    (hT : IsCompactOperator (chartSobolevExtension hc ψ hc' φ P s (s - m))) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m P x ξ = 0 := by
  set e := chartAt (CoordinateSpace n) x
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ e.source := mem_chart_source _ x
  -- A cutoff `χ` in `e` with `χ (e x) = 1`, and the symbol `a` of the compression of `P` by `χ`.
  obtain ⟨χ, -, hχ⟩ := TestFunction.exists_tsupport_subset_apply_eq
    (Ω := ⟨e.target, e.open_target⟩) (n := ⊤) (e.open_target.mem_nhds (e.map_source hx))
    subset_rfl (1 : ℝ)
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he χ χ
  have has := hasCompactSpatialSupport_of_eq_complexChartCompression he ha
  -- `Op(a) : H^s(ℝⁿ) → H^{s - m}(ℝⁿ)` is the compact `T` between the pullback through `χ` and the
  -- reading through `χ`.
  have hfac : a.toSymbol.quantizeSobolev has s =
      chartSobolevReading hc' φ he χ (s - m) ∘L chartSobolevExtension hc ψ hc' φ P s (s - m) ∘L
        chartSobolevPullback hc ψ he χ s := by
    refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ ?_
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      chartSobolevPullback_toBesselPotentialSpaceCLM,
      chartSobolevExtension_toChartSobolevSpace_of_mem hP hψ le_rfl,
      chartSobolevReading_toChartSobolevSpace hc' φ he χ hφ,
      has.quantizeSobolev_toBesselPotentialSpaceCLM]
    congr 1
    ext y
    rw [HasCompactSupport.toSchwartzMap_toFun, ha, complexChartCompression_apply,
      cutoffPushforwardSchwartz_apply]
  have hcomp : IsCompactOperator (a.toSymbol.quantizeSobolev has s) := by
    rw [hfac]
    exact (hT.comp_clm _).clm_comp _
  have h0 := a.principal_eq_zero_of_isCompactOperator has hcomp
  have h := coefficient_principal_apply_eq_classicalPrincipalSymbol hP he χ χ ha hx ξ
  rw [h0, hχ] at h
  simpa using h.symm

/-- **Operators with vanishing principal symbol are compact.** Let `P` be a classical
pseudodifferential operator of order `m` whose principal symbol `σ_m(P)` vanishes, and `ψᵢ` a chart
partition. Then `P` has order `m - 1`, so for every real `s` its extension to
`H^s(M) → H^{s - m}(M)` is a compact operator, for any finite family of target cutoffs `φⱼ`. -/
theorem isCompactOperator_chartSobolevExtension_of_classicalPrincipalSymbol_eq_zero
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (h : ∀ x ξ, classicalPrincipalSymbol m P x ξ = 0) (s : ℝ) :
    IsCompactOperator (chartSobolevExtension hc ψ hc' φ P s (s - m)) :=
  isCompactOperator_chartSobolevExtension_of_mem ((classicalPrincipalSymbol_eq_zero_iff hP).1 h)
    hψ (by linarith)

/-- **Compactness and the principal symbol.** On a compact manifold, with the Sobolev spaces of two
chart partitions `ψᵢ` and `φⱼ`, the extension `H^s(M) → H^{s - m}(M)` of a classical
pseudodifferential operator `P` of order `m` is a compact operator if and only if the principal
symbol `σ_m(P)` vanishes. In particular this does not depend on `s`. -/
theorem isCompactOperator_chartSobolevExtension_iff
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hψ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ψ i) 1 x = 1)
    (hφ : ∀ x, ∑ j, (c' j).cutoffPullback (hc' j) (φ j) 1 x = 1) (s : ℝ) :
    IsCompactOperator (chartSobolevExtension hc ψ hc' φ P s (s - m)) ↔
      ∀ x ξ, classicalPrincipalSymbol m P x ξ = 0 :=
  ⟨classicalPrincipalSymbol_eq_zero_of_isCompactOperator hP hψ hφ,
    fun h ↦ isCompactOperator_chartSobolevExtension_of_classicalPrincipalSymbol_eq_zero hP hψ h s⟩

end TauCeti
