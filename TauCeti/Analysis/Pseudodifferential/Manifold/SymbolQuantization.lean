/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.PrincipalSymbol
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Quantization of principal symbols on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. The principal symbol `σ_m(P)` of a classical
pseudodifferential operator `P` of order `m` on `M` (`TauCeti.classicalPrincipalSymbol`) is a
smooth positively homogeneous function of degree `m` on the cotangent bundle
(`TauCeti.homogeneousCotangentSymbols`), and it vanishes exactly on the operators of order `m - 1`
(`TauCeti.ker_classicalPrincipalSymbolLinearMap`). This file shows that every such function which
vanishes over the complement of a compact set of `M` is a principal symbol
(`TauCeti.exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq`). On a
compact manifold this is every such function, which completes the **principal symbol exact
sequence**

`0 → Ψ^{m-1}(M) → Ψ^m(M) → S^m_hom(T*M \ 0) → 0`

(`TauCeti.classicalPrincipalSymbolLinearMap_surjective`).

The operator with principal symbol `s` is assembled from chart quantizations
(`OpenPartialHomeomorph.chartQuantization`). In one chart `e`, a smooth homogeneous function `s` on
the cotangent bundle is read as the homogeneous symbol `(y, η) ↦ ρ(y) s(e⁻¹ y, ⟪η, ·⟫ ∘ de)` on
`ℝⁿ`, localized by a cutoff `ρ` (`OpenPartialHomeomorph.chartHomogeneousSymbol`). Its cut-off
term `χ(η) ρ(y) s(e⁻¹ y, ⟪η, ·⟫ ∘ de)` is a classical symbol, and the principal symbol of its chart
quantization is `ρ(e x) s(x, ξ)` (`OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization`
computes the principal symbol of every chart quantization). Summing over finitely many chart
cutoffs whose pullbacks sum to `1` on the compact set
(`IsCompact.exists_sum_cutoffPullback_eq_one`) gives `s`.

## Main definitions

* `OpenPartialHomeomorph.chartHomogeneousSymbol`: a smooth homogeneous function on the cotangent
  bundle read in a chart and localized by a cutoff, as a homogeneous symbol on `ℝⁿ`.

## Main results

* `OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization`,
  `OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization_of_notMem`: the principal
  symbol of the chart quantization `Op_e(a)` localized by `φ` and `ψ` is
  `φ(e x) ψ(e x) σ(a)(e x, η)` on the chart source, at the chart frequency `η` of the covector, and
  `0` off it.
* `TauCeti.exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq`: every
  smooth positively homogeneous function of degree `m` on the cotangent bundle that vanishes over
  the complement of a compact set is the principal symbol of a classical pseudodifferential
  operator of order `m`.
* `TauCeti.classicalPrincipalSymbolLinearMap_surjective`: on a compact manifold, the principal
  symbol map onto the smooth positively homogeneous functions of degree `m` on the cotangent bundle
  is surjective.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Theorem 18.1.17
  and the discussion after Definition 18.1.20.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3, Proposition 5.2.
-/

public section

noncomputable section

open Filter Set TauCeti
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace OpenPartialHomeomorph

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M) {m : ℝ}

include he

/-! ### The principal symbol of a chart quantization -/

/-- **The principal symbol of a chart quantization.** At a point `x` of the chart source and a
covector `ξ ∈ T*ₓM`, the principal symbol of the chart quantization `Op_e(a)` localized by `φ` and
`ψ` is `φ(e x) ψ(e x) σ(a)(e x, η)`, where `η` is the frequency dual to `ξ ∘ (de_x)⁻¹`. -/
theorem classicalPrincipalSymbol_chartQuantization (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (a : ClassicalSymbol n ℂ ℂ m) {x : M} (hx : x ∈ e.source)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (e.chartQuantization he φ ψ a) x ξ =
      (φ (e x) * ψ (e x) : ℝ) * a.principal.coefficient (e x,
        (InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
          (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse)) 1 := by
  -- Compress `Op_e(a)` in the chart `e` itself, by a cutoff `χ` equal to `1` near `e x`.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhds (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) (e.map_source hx)
  have hχx : χ (e x) = 1 := hχ.self_of_nhds
  obtain ⟨b, hb, -, hop⟩ := exists_complexChartCompression_chartQuantization_eq he he φ ψ a χ χ
  have h₁ := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (chartQuantization_mem_classicalPseudodifferentialOperators he φ ψ a) he χ χ hop hx ξ
  have h₂ := hb (e x) (by simp [e.map_source hx, e.left_inv hx, hx])
    ((InnerProductSpace.toDual ℝ (CoordinateSpace n)).symm
      (ξ.comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e x).inverse))
  -- The transition from `e` to itself is the identity near `e x`.
  rw [adjoint_ringInverse_fderiv_comp_symm_eq_one (e.map_source hx), one_apply_eq_self,
    e.left_inv hx, hχx] at h₂
  rw [h₂, hχx] at h₁
  simpa using h₁.symm

/-- Off the chart source, the principal symbol of a chart quantization vanishes. -/
theorem classicalPrincipalSymbol_chartQuantization_of_notMem
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (a : ClassicalSymbol n ℂ ℂ m) {x : M}
    (hx : x ∉ e.source) (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (e.chartQuantization he φ ψ a) x ξ = 0 := by
  -- Compress `Op_e(a)` in the preferred chart at `x`, by a cutoff `χ` equal to `1` near its image.
  set e₂ := chartAt (CoordinateSpace n) x
  have hx₂ : x ∈ e₂.source := mem_chart_source _ x
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhds
    (Ω := ⟨e₂.target, e₂.open_target⟩) (n := ⊤) (e₂.map_source hx₂)
  have hχx : χ (e₂ x) = 1 := hχ.self_of_nhds
  obtain ⟨b, -, hb0, hop⟩ := exists_complexChartCompression_chartQuantization_eq he
    (IsManifold.chart_mem_maximalAtlas x) φ ψ a χ χ
  have h₁ := coefficient_principal_apply_eq_classicalPrincipalSymbol
    (chartQuantization_mem_classicalPseudodifferentialOperators he φ ψ a)
    (IsManifold.chart_mem_maximalAtlas x) χ χ hop hx₂ ξ
  rw [hb0 _ fun h ↦ hx (by simpa [e₂.left_inv hx₂] using h.2), hχx] at h₁
  simpa using h₁.symm

/-! ### Smooth homogeneous functions read in a chart -/

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- The function `(y, η) ↦ ρ(y) s(e⁻¹ y, ⟪η, ·⟫ ∘ de)` is smooth away from the zero frequency. -/
private theorem contDiffOn_chartHomogeneousSymbol (ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ}
    (hs : s ∈ homogeneousCotangentSymbols n M m) :
    ContDiffOn ℝ ∞ (fun p : CoordinateSpace n × CoordinateSpace n ↦
      ((ρ p.1 : ℂ) * s (e.symm p.1)
        ((innerSL ℝ p.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm p.1)))) •
          ContinuousLinearMap.id ℂ ℂ) {p | p.2 ≠ 0} := by
  rintro ⟨y, η⟩ hη
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hy : y ∈ e.target
  · -- On the chart target, `s` read in the chart is smooth.
    have hsA := ((mem_homogeneousCotangentSymbols_iff.1 hs).2.2 e he).contDiffAt
      ((e.open_target.prod isOpen_compl_singleton).mem_nhds ⟨hy, hη⟩)
    exact ((Complex.ofRealCLM.contDiff.comp (ρ.contDiff.comp contDiff_fst)).contDiffAt.mul
      hsA).smul contDiffAt_const
  · -- Off the chart target, `ρ` vanishes near `y`.
    have hρ : ρ =ᶠ[𝓝 y] 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hy (ρ.tsupport_subset h)
    refine (contDiffAt_const (c := (0 : ℂ →L[ℂ] ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [continuous_fst.continuousAt.eventually hρ] with p hp
    exact ContinuousLinearMap.ext_ring (by simp [hp])

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **A smooth homogeneous function on the cotangent bundle read in a chart.** For a smooth
positively homogeneous function `s` of degree `m` on the cotangent bundle of `M` and a cutoff `ρ`
with compact support in the target of the chart `e`, the homogeneous symbol
`(y, η) ↦ ρ(y) s(e⁻¹ y, ⟪η, ·⟫ ∘ de)` of degree `m` on `ℝⁿ`. -/
def chartHomogeneousSymbol (ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ}
    (hs : s ∈ homogeneousCotangentSymbols n M m) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) ℂ ℂ m where
  coefficient p := ((ρ p.1 : ℂ) * s (e.symm p.1)
    ((innerSL ℝ p.2).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm p.1)))) •
      ContinuousLinearMap.id ℂ ℂ
  zero_covector y := by simp [(mem_homogeneousCotangentSymbols_iff.1 hs).1]
  contDiffOn_coefficient := contDiffOn_chartHomogeneousSymbol he ρ hs
  homogeneous y η t ht := by
    have hη : innerSL ℝ (t • η) = t • innerSL ℝ η := by
      ext v
      simp
    refine ContinuousLinearMap.ext_ring ?_
    simp only [hη, ContinuousLinearMap.smul_comp,
      (mem_homogeneousCotangentSymbols_iff.1 hs).2.1 _ _ t ht, FunLike.coe_smul, Pi.smul_apply,
      ContinuousLinearMap.id_apply, Complex.real_smul, smul_eq_mul]
    ring

omit [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
@[simp]
theorem chartHomogeneousSymbol_coefficient (ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ}
    (hs : s ∈ homogeneousCotangentSymbols n M m) (y η : CoordinateSpace n) :
    (e.chartHomogeneousSymbol he ρ hs).coefficient (y, η) =
      ((ρ y : ℂ) * s (e.symm y)
        ((innerSL ℝ η).comp (mvfderiv 𝓘(ℝ, CoordinateSpace n) e (e.symm y)))) •
          ContinuousLinearMap.id ℂ ℂ :=
  (rfl)

end OpenPartialHomeomorph

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}

/-! ### Quantization of principal symbols -/

/-- **Quantization of principal symbols.** Every smooth positively homogeneous function `s` of
degree `m` on the cotangent bundle of `M` that vanishes over the complement of a compact set is
the principal symbol of a classical pseudodifferential operator of order `m`. -/
theorem exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ}
    (hs : s ∈ homogeneousCotangentSymbols n M m) {K : Set M} (hK : IsCompact K)
    (hsK : ∀ x ∉ K, s x = 0) :
    ∃ P ∈ classicalPseudodifferentialOperators m, classicalPrincipalSymbol m P = s := by
  -- The operator is the sum of the chart quantizations of the cut-off terms of the homogeneous
  -- symbols `ρᵢ(y) s(eᵢ⁻¹ y, ⟪η, ·⟫ ∘ deᵢ)`, for chart cutoffs `ρᵢ` whose pullbacks sum to `1` on
  -- the compact set.
  obtain ⟨N, c, ρ, hρ⟩ := hK.exists_sum_cutoffPullback_eq_one (E := CoordinateSpace n)
  -- For each chart, a cutoff `θᵢ` equal to `1` on the support of `ρᵢ`.
  choose θ hθ using fun i ↦ TestFunction.exists_eventually_eq_one
    (Ω := ⟨(chartAt (CoordinateSpace n) (c i)).target,
      (chartAt (CoordinateSpace n) (c i)).open_target⟩) (n := ⊤)
    (ρ i).hasCompactSupport.isCompact (ρ i).tsupport_subset
  set Q := fun i ↦ (chartAt (CoordinateSpace n) (c i)).chartQuantization
    (IsManifold.chart_mem_maximalAtlas (c i)) (θ i) (θ i)
    (ClassicalSymbol.ofHomogeneous default
      ((chartAt (CoordinateSpace n) (c i)).chartHomogeneousSymbol
        (IsManifold.chart_mem_maximalAtlas (c i)) (ρ i) hs))
  have hQ (i : Fin N) : Q i ∈ classicalPseudodifferentialOperators m :=
    OpenPartialHomeomorph.chartQuantization_mem_classicalPseudodifferentialOperators _ _ _ _
  refine ⟨∑ i, Q i, Submodule.sum_mem _ fun i _ ↦ hQ i, ?_⟩
  ext y ξ
  rw [classicalPrincipalSymbol_sum _ fun i _ ↦ hQ i]
  -- Each chart contributes `ρᵢ(chartAt cᵢ y) s(y, ξ)`, or `0` when `y` is outside its source.
  have hterm (i : Fin N) : classicalPrincipalSymbol m (Q i) y ξ =
      (chartAt (CoordinateSpace n) (c i)).cutoffPullback (IsManifold.chart_mem_maximalAtlas (c i))
        (ρ i) 1 y * s y ξ := by
    by_cases hy : y ∈ (chartAt (CoordinateSpace n) (c i)).source
    · rw [OpenPartialHomeomorph.cutoffPullback_one_apply_of_mem _ _ hy,
        OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization _ _ _ _ hy,
        ClassicalSymbol.principal_ofHomogeneous,
        OpenPartialHomeomorph.chartHomogeneousSymbol_coefficient,
        (chartAt (CoordinateSpace n) (c i)).left_inv hy,
        innerSL_toDual_symm_comp_inverse_mvfderiv
          (IsManifold.maximalAtlas_subset_of_le (by simp)
            (IsManifold.chart_mem_maximalAtlas (n := ∞) (c i))) hy]
      by_cases hρy : ρ i (chartAt (CoordinateSpace n) (c i) y) = 0
      · simp [hρy]
      · rw [(hθ i).1.self_of_nhdsSet _ (subset_tsupport _ hρy)]
        simp
    · rw [OpenPartialHomeomorph.cutoffPullback_apply_of_notMem _ _ _ hy,
        OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization_of_notMem _ _ _ _ hy]
      simp
  simp_rw [hterm, ← Finset.sum_mul, ← Complex.ofReal_sum]
  by_cases hy : y ∈ K
  · rw [hρ y hy, Complex.ofReal_one, one_mul]
  · rw [hsK y hy, Pi.zero_apply, mul_zero]

/-- **The principal symbol map is surjective on a compact manifold**: every smooth positively
homogeneous function of degree `m` on the cotangent bundle is the principal symbol of a classical
pseudodifferential operator of order `m`. With `TauCeti.ker_classicalPrincipalSymbolLinearMap`,
this is the exactness of `0 → Ψ^{m-1}(M) → Ψ^m(M) → S^m_hom(T*M \ 0) → 0`. -/
theorem classicalPrincipalSymbolLinearMap_surjective [CompactSpace M] :
    Function.Surjective (classicalPrincipalSymbolLinearMap n M m) := by
  rintro ⟨s, hs⟩
  obtain ⟨P, hP, hPs⟩ := exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq
    hs isCompact_univ fun x hx ↦ (hx (mem_univ x)).elim
  exact ⟨⟨P, hP⟩, Subtype.ext ((coe_classicalPrincipalSymbolLinearMap_apply _).trans hPs)⟩

end TauCeti
