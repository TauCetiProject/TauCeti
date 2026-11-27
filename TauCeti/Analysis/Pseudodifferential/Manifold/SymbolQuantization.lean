/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.PatchedQuantization
import TauCeti.Algebra.GroupWithZero.Indicator
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.MFDeriv.ModelChart

/-!
# Quantization of principal symbols on a manifold

Let `M` be a manifold modelled on `ℝⁿ`. The principal symbol `σ_m(P)` of a classical
pseudodifferential operator `P` of order `m` on `M` (`TauCeti.classicalPrincipalSymbol`) is a
smooth positively homogeneous function of degree `m` on the cotangent bundle
(`TauCeti.homogeneousCotangentSymbols`), and it vanishes exactly on the operators of order `m - 1`
(`TauCeti.ker_classicalPrincipalSymbolLinearMap`). This file shows that every such function is a
principal symbol when `M` is σ-compact, which completes the **principal symbol exact sequence**

`0 → Ψ^{m-1}(M) → Ψ^m(M) → S^m_hom(T*M \ 0) → 0`

(`TauCeti.classicalPrincipalSymbolLinearMap_surjective`). On any Hausdorff manifold, every such
function which vanishes over the complement of a compact set is a principal symbol
(`TauCeti.exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq`).

The operator with principal symbol `s` is assembled from chart quantizations
(`OpenPartialHomeomorph.chartQuantization`). In one chart `e`, a smooth homogeneous function `s` on
the cotangent bundle is read as the homogeneous symbol `(y, η) ↦ ρ(y) s(e⁻¹ y, ⟪η, ·⟫ ∘ de)` on
`ℝⁿ`, localized by a cutoff `ρ` (`OpenPartialHomeomorph.chartHomogeneousSymbol`). Its cut-off
term `χ(η) ρ(y) s(e⁻¹ y, ⟪η, ·⟫ ∘ de)` is a classical symbol, and the principal symbol of its chart
quantization is `ρ(e x) s(x, ξ)` (`OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization`
computes the principal symbol of every chart quantization). Summing over finitely many chart
cutoffs `ρᵢ`, with right cutoffs `θᵢ` equal to `1` on their supports, gives a quantization
`Q(s) = ∑ᵢ Op_{cᵢ}(χ(η) θᵢ(y) s(cᵢ⁻¹ y, ⟪η, ·⟫ ∘ dcᵢ))` linear in `s`
(`TauCeti.principalSymbolQuantization`) with principal symbol `(∑ᵢ ρᵢ ∘ cᵢ) s`; for cutoffs whose
pullbacks sum to `1` on the compact set (`IsCompact.exists_sum_cutoffPullback_eq_one`) this is
`s`. On a σ-compact manifold the operator is instead the symmetric patched quantization
`∑ᵢ χᵢ Op(aᵢ) χᵢ` (`TauCeti.patchedQuantization`) over a locally finite family of chart cutoffs
`χᵢ` whose squares sum to `1` (`TauCeti.exists_locallyFinite_finsum_sq_cutoffPullback_eq_one`);
its principal symbol is `∑ᵢ χᵢ(x)² s(x, ξ) = s(x, ξ)`
(`TauCeti.classicalPrincipalSymbol_patchedQuantization`).

## Main definitions

* `OpenPartialHomeomorph.chartHomogeneousSymbol`: a smooth homogeneous function on the cotangent
  bundle read in a chart and localized by a cutoff, as a homogeneous symbol on `ℝⁿ`.
* `TauCeti.principalSymbolQuantization`: the quantization of principal symbols for finitely many
  chart cutoffs, a linear map from the smooth homogeneous functions on the cotangent bundle to the
  classical pseudodifferential operators.

## Main results

* `OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization`,
  `OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization_of_notMem`: the principal
  symbol of the chart quantization `Op_e(a)` localized by `φ` and `ψ` is
  `φ(e x) ψ(e x) σ(a)(e x, η)` on the chart source, at the chart frequency `η` of the covector, and
  `0` off it.
* `OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization_ofHomogeneous`: for the
  cut-off term `a` of a smooth homogeneous function `s` read in the chart and localized by `ρ`,
  this is `φ ψ ρ s`, with the cutoffs read on `M`.
* `TauCeti.classicalPrincipalSymbol_principalSymbolQuantization_apply`,
  `TauCeti.classicalPrincipalSymbol_principalSymbolQuantization`: the principal symbol of `Q(s)` is
  `(∑ᵢ ρᵢ ∘ cᵢ) s`, hence `s` when the cutoffs add up to `1`.
* `TauCeti.exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq`: every
  smooth positively homogeneous function of degree `m` on the cotangent bundle that vanishes over
  the complement of a compact set is the principal symbol of a classical pseudodifferential
  operator of order `m`.
* `TauCeti.classicalPrincipalSymbolLinearMap_surjective`: on a σ-compact manifold, the principal
  symbol map onto the smooth positively homogeneous functions of degree `m` on the cotangent bundle
  is surjective.
* `TauCeti.classicalPrincipalSymbol_mulLeft_comp_comp_mulLeft`: localizing an operator by chart
  cutoffs `φ` and `ψ` multiplies its principal symbol by `φ ψ`.
* `TauCeti.sub_locallyFiniteSum_mulLeft_comp_comp_mulLeft_mem_classicalPseudodifferentialOperators`:
  the symmetric localization `∑ᵢ χᵢ P χᵢ` by chart cutoffs whose squares sum to `1` differs from
  `P` by an operator of order `m - 1`.

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

/-- **The principal symbol of a quantized homogeneous function.** The chart quantization, localized
by `φ` and `ψ`, of the cut-off term of a smooth homogeneous function `s` on the cotangent bundle
read in the chart `e` and localized by `ρ` has principal symbol `φ(e x) ψ(e x) ρ(e x) s(x, ξ)`,
with the cutoffs read on `M` through the chart and extended by `0`. -/
theorem classicalPrincipalSymbol_chartQuantization_ofHomogeneous
    (φ ψ ρ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (χ : FrequencyCutoff (CoordinateSpace n))
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ}
    (hs : s ∈ homogeneousCotangentSymbols n M m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (e.chartQuantization he φ ψ
        (ClassicalSymbol.ofHomogeneous χ (e.chartHomogeneousSymbol he ρ hs))) x ξ =
      ((e.cutoffPullback he φ 1 x * e.cutoffPullback he ψ 1 x * e.cutoffPullback he ρ 1 x : ℝ) :
        ℂ) * s x ξ := by
  by_cases hx : x ∈ e.source
  · rw [classicalPrincipalSymbol_chartQuantization he _ _ _ hx,
      ClassicalSymbol.principal_ofHomogeneous, chartHomogeneousSymbol_coefficient, e.left_inv hx,
      innerSL_toDual_symm_comp_inverse_mvfderiv
        (IsManifold.maximalAtlas_subset_of_le (by simp) he) hx]
    simp [cutoffPullback_one_apply_of_mem he _ hx, mul_assoc]
  · simp [cutoffPullback_apply_of_notMem he _ _ hx,
      classicalPrincipalSymbol_chartQuantization_of_notMem he _ _ _ hx]

end OpenPartialHomeomorph

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] {m : ℝ}

/-! ### A linear quantization of principal symbols -/

section Quantization

variable {ι : Type*} [Fintype ι] {c : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  (hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (ρ θ : ∀ i, 𝓓(⟨(c i).target, (c i).open_target⟩, ℝ)) (χ : FrequencyCutoff (CoordinateSpace n))

variable (m) in
/-- **A linear quantization of principal symbols.** For finitely many charts `cᵢ`, cutoffs `ρᵢ`
and `θᵢ` with compact supports in their targets and a frequency cutoff `χ`, the operator

`Q(s) = ∑ᵢ Op_{cᵢ}(aᵢ)`, `aᵢ(y, η) = χ(η) θᵢ(y) s(cᵢ⁻¹ y, ⟪η, ·⟫ ∘ dcᵢ)`,

where the chart quantization `Op_{cᵢ}` is localized by `ρᵢ` on the left and `θᵢ` on the right,
depends linearly on the smooth homogeneous function `s` of degree `m` on the cotangent bundle.
When `θᵢ = 1` on the support of `ρᵢ`, the principal symbol of `Q(s)` is `(∑ᵢ ρᵢ ∘ cᵢ) s`
(`TauCeti.classicalPrincipalSymbol_principalSymbolQuantization_apply`), hence `s` when the
`ρᵢ ∘ cᵢ` add up to `1` (`TauCeti.classicalPrincipalSymbol_principalSymbolQuantization`). -/
def principalSymbolQuantization :
    homogeneousCotangentSymbols n M m →ₗ[ℂ]
      (C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) where
  toFun s := ∑ i, (c i).chartQuantization (hc i) (ρ i) (θ i)
    (ClassicalSymbol.ofHomogeneous χ ((c i).chartHomogeneousSymbol (hc i) (θ i) s.property))
  map_add' s s' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ (c i).chartQuantization_eq_add (hc i) _ _ ?_
    funext ⟨y, η⟩
    refine ContinuousLinearMap.ext_ring ?_
    simp [mul_add]
  map_smul' a s := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ (c i).chartQuantization_eq_smul (hc i) _ _ a ?_
    funext ⟨y, η⟩
    refine ContinuousLinearMap.ext_ring ?_
    simp [mul_left_comm]

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- Unfolding `TauCeti.principalSymbolQuantization`. -/
theorem principalSymbolQuantization_apply (s : homogeneousCotangentSymbols n M m) :
    principalSymbolQuantization m hc ρ θ χ s = ∑ i, (c i).chartQuantization (hc i) (ρ i) (θ i)
      (ClassicalSymbol.ofHomogeneous χ ((c i).chartHomogeneousSymbol (hc i) (θ i) s.property)) :=
  (rfl)

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- The quantization of a principal symbol is a classical pseudodifferential operator of order
`m`. -/
theorem principalSymbolQuantization_mem_classicalPseudodifferentialOperators
    (s : homogeneousCotangentSymbols n M m) :
    principalSymbolQuantization m hc ρ θ χ s ∈ classicalPseudodifferentialOperators m :=
  Submodule.sum_mem _ fun i _ ↦
    (c i).chartQuantization_mem_classicalPseudodifferentialOperators (hc i) _ _ _

/-- **The principal symbol of the quantization.** If `θᵢ = 1` on the support of `ρᵢ`, then the
principal symbol of `Q(s)` at `(x, ξ)` is `(∑ᵢ ρᵢ(cᵢ x)) s(x, ξ)`, with the cutoffs read on `M`
through the charts and extended by `0`. -/
theorem classicalPrincipalSymbol_principalSymbolQuantization_apply
    (hθ : ∀ i, ∀ y ∈ tsupport (ρ i), θ i y = 1) (s : homogeneousCotangentSymbols n M m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (principalSymbolQuantization m hc ρ θ χ s) x ξ =
      ((∑ i, (c i).cutoffPullback (hc i) (ρ i) 1 x : ℝ) : ℂ) * (s : (x : M) →
        (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ) x ξ := by
  rw [principalSymbolQuantization_apply, classicalPrincipalSymbol_sum _ fun i _ ↦
    (c i).chartQuantization_mem_classicalPseudodifferentialOperators (hc i) _ _ _,
    Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  -- `θᵢ = 1` on the support of `ρᵢ` absorbs both cutoffs `θᵢ`.
  have h := (c i).cutoffPullback_one_mul_cutoffPullback_one_of_tsupport_subset (hc i)
    (fun z hz ↦ hθ i z hz) x
  rw [OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization_ofHomogeneous, h, h]

/-- **The quantization inverts the principal symbol map**: if `θᵢ = 1` on the support of `ρᵢ`
and the cutoffs `ρᵢ`, read on `M`, add up to `1`, then `σ_m(Q(s)) = s`. -/
theorem classicalPrincipalSymbol_principalSymbolQuantization
    (hθ : ∀ i, ∀ y ∈ tsupport (ρ i), θ i y = 1)
    (hρ : ∀ x, ∑ i, (c i).cutoffPullback (hc i) (ρ i) 1 x = 1)
    (s : homogeneousCotangentSymbols n M m) :
    classicalPrincipalSymbol m (principalSymbolQuantization m hc ρ θ χ s) = s := by
  ext x ξ
  rw [classicalPrincipalSymbol_principalSymbolQuantization_apply hc ρ θ χ hθ, hρ,
    Complex.ofReal_one, one_mul]

end Quantization

/-! ### Quantization of principal symbols -/

/-- **Quantization of principal symbols.** Every smooth positively homogeneous function `s` of
degree `m` on the cotangent bundle of `M` that vanishes over the complement of a compact set is
the principal symbol of a classical pseudodifferential operator of order `m`. -/
theorem exists_mem_classicalPseudodifferentialOperators_classicalPrincipalSymbol_eq
    {s : (x : M) → (TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) → ℂ}
    (hs : s ∈ homogeneousCotangentSymbols n M m) {K : Set M} (hK : IsCompact K)
    (hsK : ∀ x ∉ K, s x = 0) :
    ∃ P ∈ classicalPseudodifferentialOperators m, classicalPrincipalSymbol m P = s := by
  -- The operator is the quantization `principalSymbolQuantization` for chart cutoffs `ρᵢ` whose
  -- pullbacks sum to `1` on the compact set, and cutoffs `θᵢ` equal to `1` on their supports.
  obtain ⟨N, c, ρ, hρ⟩ := hK.exists_sum_cutoffPullback_eq_one (E := CoordinateSpace n)
  choose θ hθ using fun i ↦ TestFunction.exists_eventually_eq_one
    (Ω := ⟨(chartAt (CoordinateSpace n) (c i)).target,
      (chartAt (CoordinateSpace n) (c i)).open_target⟩) (n := ⊤)
    (ρ i).hasCompactSupport.isCompact (ρ i).tsupport_subset
  have hc (i : Fin N) := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, CoordinateSpace n)) (n := ∞)
    (c i)
  refine ⟨principalSymbolQuantization m hc ρ θ default ⟨s, hs⟩,
    principalSymbolQuantization_mem_classicalPseudodifferentialOperators hc ρ θ default _, ?_⟩
  ext y ξ
  rw [classicalPrincipalSymbol_principalSymbolQuantization_apply hc ρ θ default
    (fun i z hz ↦ (hθ i).1.self_of_nhdsSet z hz)]
  by_cases hy : y ∈ K
  · rw [hρ y hy, Complex.ofReal_one, one_mul]
  · simp [hsK y hy]

/-! ### Square partitions in charts -/

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- If the chart cutoffs `χᵢ`, read on `M`, have locally finite supports and squares adding up to
`1`, then `∑ᵢ χᵢ(x)² z = z`. -/
private theorem finsum_cutoffPullback_sq_mul {ι : Type*}
    {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    {χ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)}
    (hS : LocallyFinite fun i ↦ (e i).symm '' tsupport (χ i))
    (hsq : ∀ y, ∑ᶠ i, (e i).cutoffPullback (he i) (χ i) 1 y ^ 2 = 1) (x : M) (z : ℂ) :
    ∑ᶠ i, (((e i).cutoffPullback (he i) (χ i) 1 x ^ 2 : ℝ) : ℂ) * z = z := by
  -- Only the finitely many charts whose cutoff supports contain `x` contribute.
  have hfin := hS.point_finite x
  have hr : Function.support (fun i ↦ (e i).cutoffPullback (he i) (χ i) 1 x) ⊆ hfin.toFinset :=
    fun i hi ↦ hfin.mem_toFinset.2 <|
      ((e i).tsupport_cutoffPullback_one (he i) (χ i)).subset (subset_tsupport _ hi)
  have hsq' := hsq x
  rw [finsum_eq_sum_of_support_subset _ fun i hi ↦ hr (by simpa using hi)] at hsq'
  rw [finsum_eq_sum_of_support_subset _ fun i hi ↦ hr fun h ↦ hi (by simp [h]),
    ← Finset.sum_mul, ← Complex.ofReal_sum, hsq', Complex.ofReal_one, one_mul]

/-- **The principal symbol map is surjective on a σ-compact manifold**: every smooth positively
homogeneous function of degree `m` on the cotangent bundle is the principal symbol of a classical
pseudodifferential operator of order `m`. With `TauCeti.ker_classicalPrincipalSymbolLinearMap`,
this is the exactness of `0 → Ψ^{m-1}(M) → Ψ^m(M) → S^m_hom(T*M \ 0) → 0`. The operator is a
symmetric patched quantization `∑ᵢ χᵢ Op(aᵢ) χᵢ` over chart cutoffs `χᵢ` whose squares sum to `1`,
where `aᵢ` is the cut-off term of the function read in the `i`-th chart. -/
theorem classicalPrincipalSymbolLinearMap_surjective [SigmaCompactSpace M] :
    Function.Surjective (classicalPrincipalSymbolLinearMap n M m) := by
  rintro ⟨s, hs⟩
  -- Chart cutoffs `χᵢ` in the charts `eᵢ` whose squares sum to `1`, and cutoffs `θᵢ` equal to `1`
  -- on their supports.
  obtain ⟨ι, c, χ, hχ, hsq⟩ :=
    exists_locallyFinite_finsum_sq_cutoffPullback_eq_one (E := CoordinateSpace n) (M := M)
  set e := fun i ↦ chartAt (CoordinateSpace n) (c i)
  have he (i : ι) : e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    IsManifold.chart_mem_maximalAtlas (c i)
  choose θ hθ using fun i ↦ TestFunction.exists_eventually_eq_one
    (Ω := ⟨(e i).target, (e i).open_target⟩) (n := ⊤) (χ i).hasCompactSupport.isCompact
    (χ i).tsupport_subset
  have hS : LocallyFinite fun i ↦ (e i).symm '' (tsupport (χ i) ∪ tsupport (χ i)) := by
    simpa only [union_self] using hχ
  -- The operator is the patched quantization of the cut-off terms of the homogeneous symbols
  -- `θᵢ(y) s(eᵢ⁻¹ y, ⟪η, ·⟫ ∘ deᵢ)`, localized by `χᵢ` on both sides.
  set a := fun i ↦
    ClassicalSymbol.ofHomogeneous default ((e i).chartHomogeneousSymbol (he i) (θ i) hs)
  refine ⟨⟨patchedQuantization he χ χ a hS,
    patchedQuantization_mem_classicalPseudodifferentialOperators he χ χ a hS⟩, Subtype.ext ?_⟩
  rw [coe_classicalPrincipalSymbolLinearMap_apply]
  ext y ξ
  -- Each chart contributes `χᵢ(eᵢ y)² s(y, ξ)`, or `0` when `y` is outside its source.
  set r := fun i ↦ (e i).cutoffPullback (he i) (χ i) 1 y
  have hterm (i : ι) : classicalPrincipalSymbol m ((e i).chartQuantization (he i) (χ i) (χ i)
      (a i)) y ξ = ((r i ^ 2 : ℝ) : ℂ) * s y ξ := by
    -- `θᵢ = 1` on the support of `χᵢ` absorbs the cutoff of the symbol.
    rw [OpenPartialHomeomorph.classicalPrincipalSymbol_chartQuantization_ofHomogeneous, mul_assoc,
      (e i).cutoffPullback_one_mul_cutoffPullback_one_of_tsupport_subset (he i)
        (fun z hz ↦ (hθ i).1.self_of_nhdsSet z hz), sq]
  rw [classicalPrincipalSymbol_patchedQuantization, finsum_congr hterm,
    finsum_cutoffPullback_sq_mul he hχ hsq]

/-! ### Symmetric localization -/

/-- **The principal symbol of a localized operator.** For cutoffs `φ` and `ψ` in a chart `e`, read
on `M` through the chart and extended by `0`, the principal symbol of `u ↦ φ · P (ψ u)` is
`φ(x) ψ(x) σ_m(P)(x, ξ)`. -/
theorem classicalPrincipalSymbol_mulLeft_comp_comp_mulLeft
    {e : OpenPartialHomeomorph M (CoordinateSpace n)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
    (hP : P ∈ classicalPseudodifferentialOperators m) (x : M)
    (ξ : TangentSpace 𝓘(ℝ, CoordinateSpace n) x →L[ℝ] ℝ) :
    classicalPrincipalSymbol m (LinearMap.mulLeft ℂ (e.complexCutoffPullback he φ 1) ∘ₗ P ∘ₗ
        LinearMap.mulLeft ℂ (e.complexCutoffPullback he ψ 1)) x ξ =
      e.complexCutoffPullback he φ 1 x * e.complexCutoffPullback he ψ 1 x *
        classicalPrincipalSymbol m P x ξ := by
  -- `φ P ψ` is the chart quantization of the symbol `a` of the compression of `P` by `φ` and `ψ`,
  -- localized by a cutoff `θ` equal to `1` near their supports.
  obtain ⟨θ, hθ, -⟩ := TestFunction.exists_eventually_eq_one (Ω := ⟨e.target, e.open_target⟩)
    (n := ⊤) (φ.hasCompactSupport.isCompact.union ψ.hasCompactSupport.isCompact)
    (union_subset φ.tsupport_subset ψ.tsupport_subset)
  have hθ1 : EqOn θ 1 (tsupport φ ∪ tsupport ψ) := fun z hz ↦ hθ.self_of_nhdsSet z hz
  obtain ⟨a, ha⟩ := (mem_classicalPseudodifferentialOperators_iff.1 hP).2 e he φ ψ
  rw [← e.chartQuantization_eq_mulLeft_comp_comp_mulLeft he ha (hθ1.mono subset_union_left)
    (hθ1.mono subset_union_right)]
  by_cases hx : x ∈ e.source
  · rw [e.classicalPrincipalSymbol_chartQuantization he θ θ a hx,
      coefficient_principal_apply_eq_classicalPrincipalSymbol hP he φ ψ ha hx,
      e.complexCutoffPullback_apply_of_mem he _ _ hx,
      e.complexCutoffPullback_apply_of_mem he _ _ hx]
    -- `θ = 1` on the support of `φ`, so `θ φ = φ` absorbs the two cutoffs `θ` of the chart
    -- quantization: `θ² φ - φ = (θ + 1) (θ φ - φ)`.
    have hθφ : (θ (e x) : ℂ) * φ (e x) = φ (e x) := mod_cast congrFun
      (Set.EqOn.mul_eq_right (hθ1.mono ((subset_tsupport φ).trans subset_union_left))) (e x)
    simp only [Complex.ofReal_mul, ContMDiffMap.coe_one, Pi.one_apply, Complex.real_smul, mul_one]
    linear_combination (θ (e x) + 1 : ℂ) * ψ (e x) * classicalPrincipalSymbol m P x ξ * hθφ
  · rw [e.classicalPrincipalSymbol_chartQuantization_of_notMem he θ θ a hx,
      e.complexCutoffPullback_apply_of_notMem he _ _ hx]
    simp

section SquarePartition

variable {ι : Type*} {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {χ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}
  {hQ : ∀ f, LocallyFinite fun i ↦ Function.support
    ((LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (χ i) 1) ∘ₗ P ∘ₗ
      LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (χ i) 1)) f)}

/-- **Symmetric localization by a square partition.** Let `χᵢ` be cutoffs in charts `eᵢ` whose
chart preimages form a locally finite family and whose squares, read on `M`, add up to `1`. Then
every classical pseudodifferential operator `P` of order `m` differs from its symmetric
localization `∑ᵢ χᵢ P χᵢ` by an operator of order `m - 1`, so both have the same principal symbol.
Each `χᵢ P χᵢ` is the chart quantization of the symbol of the compression of `P` by `χᵢ`
(`OpenPartialHomeomorph.chartQuantization_eq_mulLeft_comp_comp_mulLeft`); for the ordinary
localization `∑ᵢ ρᵢ P χᵢ` by a finite partition of unity `ρᵢ`, with `χᵢ = 1` near the support of
`ρᵢ`, the difference has order `-∞` instead
(`TauCeti.sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`). -/
theorem sub_locallyFiniteSum_mulLeft_comp_comp_mulLeft_mem_classicalPseudodifferentialOperators
    (hP : P ∈ classicalPseudodifferentialOperators m)
    (hS : LocallyFinite fun i ↦ (e i).symm '' tsupport (χ i))
    (hsq : ∀ y, ∑ᶠ i, (e i).cutoffPullback (he i) (χ i) 1 y ^ 2 = 1) :
    P - ContMDiffMap.locallyFiniteSum (fun i ↦
        LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (χ i) 1) ∘ₗ P ∘ₗ
          LinearMap.mulLeft ℂ ((e i).complexCutoffPullback (he i) (χ i) 1)) hQ ∈
      classicalPseudodifferentialOperators (m - 1) := by
  set c := fun i ↦ (e i).complexCutoffPullback (he i) (χ i) 1
  have hc (i : ι) : tsupport (c i) ⊆ (e i).symm '' tsupport (χ i) :=
    (e i).tsupport_complexCutoffPullback_subset (he i) _ _
  have hPi (i : ι) : LinearMap.mulLeft ℂ (c i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (c i) ∈
      classicalPseudodifferentialOperators m :=
    mulLeft_comp_mem_classicalPseudodifferentialOperators
      (comp_mulLeft_mem_classicalPseudodifferentialOperators hP _) _
  have hsupp (i : ι) (f) : tsupport ((LinearMap.mulLeft ℂ (c i) ∘ₗ P ∘ₗ
      LinearMap.mulLeft ℂ (c i)) f) ⊆ (e i).symm '' tsupport (χ i) := by
    rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, ContMDiffMap.coe_mul]
    exact tsupport_mul_subset_left.trans (hc i)
  -- A function vanishing near the support of `χᵢ` is killed by the right factor `χᵢ`.
  have hloc (i : ι) (f) (hf : ∀ᶠ y in 𝓝ˢ ((e i).symm '' tsupport (χ i)), f y = 0) :
      (LinearMap.mulLeft ℂ (c i) ∘ₗ P ∘ₗ LinearMap.mulLeft ℂ (c i)) f = 0 := by
    have h0 : LinearMap.mulLeft ℂ (c i) f = 0 := by
      ext y
      by_cases hy : c i y = 0
      · simp [hy]
      · simp [hf.self_of_nhdsSet y (hc i (subset_tsupport _ hy))]
    simp [h0]
  have hQm := locallyFiniteSum_mem_classicalPseudodifferentialOperators (hP := hQ) hS
    (fun i ↦ (e i).isCompact_symm_image_tsupport (χ i)) hPi hsupp hloc
  -- The principal symbol of `∑ᵢ χᵢ P χᵢ` is `∑ᵢ χᵢ(x)² σ_m(P)(x, ξ) = σ_m(P)(x, ξ)`.
  refine sub_mem_classicalPseudodifferentialOperators_of_classicalPrincipalSymbol_eq hP hQm
    fun x ξ ↦ ?_
  rw [classicalPrincipalSymbol_locallyFiniteSum hS hsupp hPi hQm]
  refine (Eq.trans (finsum_congr fun i ↦ ?_) (finsum_cutoffPullback_sq_mul he hS hsq x _)).symm
  rw [classicalPrincipalSymbol_mulLeft_comp_comp_mulLeft (he i) _ _ hP,
    OpenPartialHomeomorph.complexCutoffPullback_one_apply]
  push_cast
  ring

end SquarePartition

end TauCeti
