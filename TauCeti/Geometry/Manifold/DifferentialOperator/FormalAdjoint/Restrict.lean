/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.FormalAdjoint.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Restrict.Section
public import TauCeti.Topology.VectorBundle.Pullback
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension
import TauCeti.MeasureTheory.Integral.Bochner.Subtype

/-!
# Formal adjoints of restricted differential operators between sections

Let `V` and `W` be smooth real vector bundles with fibre inner products over a finite-dimensional
Hausdorff smooth manifold `M`, let `μ` be a measure on `M`, and let `U ⊆ M` be an open subset,
carrying the restricted measure `μ.comap Subtype.val`. The restrictions `V|_U` and `W|_U` carry the
fibre inner products of `V` and `W`. If the differential operator `Q : Γ(W) → Γ(V)` is a formal
adjoint of the differential operator `P : Γ(V) → Γ(W)` with respect to `μ`, that is

`∫ ⟪P s, t⟫ dμ = ∫ ⟪s, Q t⟫ dμ`

whenever `s` or `t` has compact support (`LinearMap.IsFormalAdjoint`), then the restriction `Q|_U`
is a formal adjoint of `P|_U` with respect to the restricted measure
(`LinearMap.IsFormalAdjoint.restrictSectionDifferentialOperators`). So formal adjunction commutes
with restriction to open subsets, as formal transposition of operators on functions does
(`LinearMap.IsFormalTranspose.restrictDifferentialOperators`), and the formal adjoint of a global
operator can be computed on chart domains, in local frames.

For a section `s` of `V|_U` with compact support, its extension by zero `S` is a smooth section of
`V` with compact support (`ContMDiffSection.extendByZero`). Choose a smooth cutoff `σ`, equal to `1`
near the support of `s` and with compact support in `U`; the extension by zero `T` of `σ t` agrees
with `t` near the support of `s`. Differential operators are local, so `P|_U s = P S` on `U`, and
`Q|_U t = Q T` near the support of `s`. The two integrals over `U` are therefore the integrals over
`M` of `⟪P S, T⟫` and `⟪S, Q T⟫`, which agree by integration by parts on `M`. The case where `t`
has compact support follows by symmetry.

## Main results

* `LinearMap.IsFormalAdjoint.restrictSectionDifferentialOperators`: the restriction of a formal
  adjoint is a formal adjoint of the restriction.

## References

* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (differential operators between vector bundles and their adjoints).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19 (locality of linear differential operators).
-/

public section

noncomputable section

open MeasureTheory Bundle Filter Set TopologicalSpace TauCeti
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W I]
  [MeasurableSpace M] [OpensMeasurableSpace M] {μ : Measure M} {U : Opens M} {m k : ℕ}

/-- The integration by parts identity for the restrictions to `U`, when `s` has compact
support. -/
private theorem integral_inner_restrict_eq_of_isCompact
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
    {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ k}
    (h : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint Q μ)
    {s : Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯}
    {t : Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯}
    (hs : IsCompact s.tsupport) :
    ∫ x, ⟪(U.restrictSectionDifferentialOperators m P :
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
          Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯) s x, t x⟫
        ∂μ.comap Subtype.val =
      ∫ x, ⟪s x, (U.restrictSectionDifferentialOperators k Q :
        Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ →ₗ[ℝ]
          Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯) t x⟫
        ∂μ.comap Subtype.val := by
  set P₀ := (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯)
  set Q₀ := (Q : Cₛ^∞⟮I; F', W⟯ →ₗ[ℝ] Cₛ^∞⟮I; F, V⟯)
  set PU := (U.restrictSectionDifferentialOperators m P :
    Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯)
  set QU := (U.restrictSectionDifferentialOperators k Q :
    Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯ →ₗ[ℝ]
      Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯)
  -- `S` is the extension of `s` by zero, and `T` a global section agreeing with `t` near the
  -- support of `s` and supported in `U`.
  set S : Cₛ^∞⟮I; F, V⟯ :=
    ContMDiffSection.extendByZero ⟨s, ContMDiffSection.mem_compactlySupported.2 hs⟩
  obtain ⟨T, -, hTU, hTt⟩ :=
    ContMDiffSection.exists_eventuallyEq_isCompact_tsupport_subset_of_opens t hs
  have hS (x : U) : S x = s x := ContMDiffSection.extendByZero_apply_of_mem _ x
  have hT (x : U) (hx : x ∈ s.tsupport) := eventually_nhdsSet_iff_forall.1 hTt x hx
  have hSc : IsCompact S.tsupport := ContMDiffSection.mem_compactlySupported.1
    (ContMDiffSection.extendByZero_mem_compactlySupported _)
  -- `P|_U s = P S` on `U`, and `Q|_U t = Q T` near the support of `s`, since `P` and `Q` are local.
  have hP (x : U) : PU s x = P₀ S x :=
    Opens.restrictSectionDifferentialOperators_apply_of_eventuallyEq P (.of_forall hS)
  have hQ (x : U) (hx : x ∈ s.tsupport) : QU t x = Q₀ T x :=
    Opens.restrictSectionDifferentialOperators_apply_of_eventuallyEq Q (hT x hx)
  -- `P|_U s` vanishes off the support of `s`, since `P|_U` is local.
  have hPs (x : U) (hx : x ∉ s.tsupport) : PU s x = 0 :=
    (PU s).eq_zero_of_notMem_tsupport fun h ↦ hx <|
      tsupport_differentialOperators_section_apply_subset
        (U.restrictSectionDifferentialOperators m P).property s h
  have hU := U.isOpen.measurableSet
  -- Both integrands vanish off `U`, so the integrals over `U` are integrals over `M`.
  calc ∫ x, ⟪PU s x, t x⟫ ∂μ.comap Subtype.val
      = ∫ x : U, ⟪P₀ S x, T x⟫ ∂μ.comap Subtype.val := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ s.tsupport
        · exact congrArg₂ (fun a b ↦ ⟪a, b⟫) (hP x) (hT x hx).self_of_nhds.symm
        · dsimp only
          rw [← hP x, hPs x hx]
          -- The zero of the fibre of `W|_U` over `x` is the zero of the fibre of `W`.
          exact (inner_zero_left _).trans (inner_zero_left _).symm
    _ = ∫ x, ⟪P₀ S x, T x⟫ ∂μ :=
        integral_subtype_comap_of_ae_restrict_compl_eq_zero (f := fun x ↦ ⟪P₀ S x, T x⟫) hU
          (ae_restrict_of_forall_mem hU.compl fun x hx ↦ by
            simp [T.eq_zero_of_notMem_tsupport fun h ↦ hx (hTU h)])
    _ = ∫ x, ⟪S x, Q₀ T x⟫ ∂μ := h.integral_inner_eq (.inl hSc)
    _ = ∫ x : U, ⟪S x, Q₀ T x⟫ ∂μ.comap Subtype.val :=
        (integral_subtype_comap_of_ae_restrict_compl_eq_zero (f := fun x ↦ ⟪S x, Q₀ T x⟫) hU
          (ae_restrict_of_forall_mem hU.compl fun x hx ↦ by
            simp [S, ContMDiffSection.extendByZero_apply_of_notMem _ hx])).symm
    _ = ∫ x, ⟪s x, QU t x⟫ ∂μ.comap Subtype.val := by
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ s.tsupport
        · exact congrArg₂ (fun a b ↦ ⟪a, b⟫) (hS x) (hQ x hx).symm
        · dsimp only
          rw [hS x, s.eq_zero_of_notMem_tsupport hx]
          -- The zero of the fibre of `V|_U` over `x` is the zero of the fibre of `V`.
          exact (inner_zero_left _).trans (inner_zero_left _).symm

/-- **Formal adjoints commute with restriction to open subsets.** If the differential operator
`Q : Γ(W) → Γ(V)` is a formal adjoint of the differential operator `P : Γ(V) → Γ(W)` with respect to
`μ`, then on an open subset `U` the restriction `Q|_U` is a formal adjoint of `P|_U` with respect to
the restricted measure `μ.comap Subtype.val`, for the fibre inner products of `V` and `W`. -/
theorem IsFormalAdjoint.restrictSectionDifferentialOperators
    {P : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F, V⟯ Cₛ^∞⟮I; F', W⟯ m}
    {Q : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ Cₛ^∞⟮I; F', W⟯ Cₛ^∞⟮I; F, V⟯ k}
    (h : (P : Cₛ^∞⟮I; F, V⟯ →ₗ[ℝ] Cₛ^∞⟮I; F', W⟯).IsFormalAdjoint Q μ) (U : Opens M) :
    (U.restrictSectionDifferentialOperators m P :
        Cₛ^∞⟮I; F, (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ V⟯ →ₗ[ℝ]
          Cₛ^∞⟮I; F', (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M)) *ᵖ W⟯).IsFormalAdjoint
      (U.restrictSectionDifferentialOperators k Q) (μ.comap Subtype.val) := by
  rw [isFormalAdjoint_iff]
  rintro s t (hs | ht)
  · exact integral_inner_restrict_eq_of_isCompact h hs
  · simpa only [real_inner_comm] using (integral_inner_restrict_eq_of_isCompact h.symm ht).symm

end LinearMap
