/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.Restrict.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.Transpose.Basic
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.Metrizable
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.MeasureTheory.Integral.Bochner.Subtype
import TauCeti.MeasureTheory.Measure.Subtype

/-!
# Formal transposes of restricted differential operators

Let `μ` be a measure on a finite-dimensional Hausdorff smooth manifold `M` and `U ⊆ M` an open
subset, carrying the restricted measure `μ.comap Subtype.val`. If `D'` is a formal transpose of
the differential operator `D` with respect to `μ`, that is

`∫ (D f) g dμ = ∫ f (D' g) dμ`

whenever `f` or `g` has compact support (`LinearMap.IsFormalTranspose`), and `D'` is a
differential operator, then the restriction `D'|_U` is a formal transpose of `D|_U` with respect
to the restricted measure (`LinearMap.IsFormalTranspose.restrictDifferentialOperators`). So formal
transposition commutes with restriction to open subsets, and the transpose of a global operator
can be computed on chart domains, where differential operators are coordinate expressions.

For `f` with compact support in `U`, choose a smooth cutoff `σ`, equal to `1` near the support of
`f` and with compact support in `U` (`IsCompact.exists_contMDiff_one_nhds_tsupport_subset`). The
functions `σ f` and `σ g`, extended by zero off `U`, are smooth on `M`; they agree with `f` on `U`
and with `g` near the support of `f`. Differential operators are local, so the two integrals over
`U` are the integrals over `M` of `D (σ f) · σ g` and `σ f · D' (σ g)`, which agree by
integration by parts on `M`. The case where `g` has compact support follows by symmetry.

## Main results

* `LinearMap.IsFormalTranspose.restrictDifferentialOperators`: the restriction of a formal
  transpose is a formal transpose of the restriction.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §6.3 (distributions and differential operators on manifolds).
* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §19 (locality of linear differential operators).
-/

public section

noncomputable section

open MeasureTheory Filter Function Set TopologicalSpace TauCeti
open scoped ContDiff Manifold Topology

namespace LinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {U : Opens M}

/-- If `σ = 1` on the support of `f`, then the extension `σ f` restricts to `f` on `U`. -/
private theorem restrict_cutoffExtend {σ : M → ℝ} (hσ : ContMDiffOn I 𝓘(ℝ) ∞ σ U)
    (hσU : tsupport σ ⊆ U) {f : C^∞⟮I, U; ℝ⟯} (hσf : ∀ x ∈ tsupport f, σ x = 1) :
    (ContMDiffMap.cutoffExtend hσ hσU f).restrict U = f := by
  ext x
  rw [ContMDiffMap.restrict_apply, ContMDiffMap.cutoffExtend_apply_val]
  by_cases hx : x ∈ tsupport f
  · rw [hσf x hx, one_smul]
  · rw [image_eq_zero_of_notMem_tsupport hx, smul_zero]

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [OpensMeasurableSpace M] {μ : Measure M} {m k : ℕ}

/-- The integration by parts identity for the restrictions to `U`, when `f` has compact support. -/
private theorem integral_restrict_mul_eq_of_hasCompactSupport
    {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m}
    {D' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k}
    (h : (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D' μ)
    {f g : C^∞⟮I, U; ℝ⟯} (hf : HasCompactSupport f) :
    ∫ x, (U.restrictDifferentialOperators m D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) f x * g x
        ∂μ.comap Subtype.val =
      ∫ x, f x * (U.restrictDifferentialOperators k D' : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯) g x
        ∂μ.comap Subtype.val := by
  set D₀ := (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯)
  set D₀' := (D' : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯)
  set DU := (U.restrictDifferentialOperators m D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯)
  set DU' := (U.restrictDifferentialOperators k D' : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯)
  -- A cutoff `σ`, compactly supported in `U` and equal to `1` near the support of `f`.
  have hK : IsCompact (Subtype.val '' tsupport f : Set M) := hf.image continuous_subtypeVal
  obtain ⟨σ, hσ, hσ1, hσc, hσU, -⟩ := hK.exists_contMDiff_one_nhds_tsupport_subset I U.isOpen
    (by rintro _ ⟨x, -, rfl⟩; exact x.property)
  have hσf (x : U) (hx : x ∈ tsupport f) : ∀ᶠ y : U in 𝓝 x, σ y = 1 :=
    continuous_subtypeVal.continuousAt.eventually
      (hσ1.filter_mono (nhds_le_nhdsSet (mem_image_of_mem _ hx)))
  set F := ContMDiffMap.cutoffExtend hσ.contMDiffOn hσU f
  set G := ContMDiffMap.cutoffExtend hσ.contMDiffOn hσU g
  -- `F` restricts to `f` on `U`, and `G` agrees with `g` near the support of `f`.
  have hF : F.restrict U = f := restrict_cutoffExtend _ hσU fun x hx ↦ (hσf x hx).self_of_nhds
  have hDU (x : U) : DU f x = D₀ F x := by
    rw [← hF, Opens.restrictDifferentialOperators_apply_restrict, ContMDiffMap.restrict_apply]
  have hDU' (x : U) (hx : x ∈ tsupport f) : DU' g x = D₀' G x :=
    Opens.restrictDifferentialOperators_apply_of_eventuallyEq D' <|
      (hσf x hx).mono fun y hy ↦ by simp [G, hy]
  -- So both integrands on `U` are restrictions of functions on `M` vanishing off `U`.
  have h₁ (x : U) : DU f x * g x = D₀ F x * G x := by
    by_cases hx : x ∈ tsupport f
    · rw [hDU, ContMDiffMap.cutoffExtend_apply_val, (hσf x hx).self_of_nhds, one_smul]
    · have h0 : DU f x = 0 := by
        rw [differentialOperators_apply_eq_of_eventuallyEq
          (U.restrictDifferentialOperators m D).property (g := 0)
          (by simpa using notMem_tsupport_iff_eventuallyEq.1 hx), map_zero,
          ContMDiffMap.coe_zero, Pi.zero_apply]
      rw [← hDU, h0, zero_mul, zero_mul]
  have h₂ (x : U) : f x * DU' g x = F x * D₀' G x := by
    have hFx : F x = f x := by rw [← ContMDiffMap.restrict_apply, hF]
    by_cases hx : x ∈ tsupport f
    · rw [hDU' x hx, hFx]
    · rw [hFx, image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  have hU := U.isOpen.measurableSet
  calc ∫ x, DU f x * g x ∂μ.comap Subtype.val
      = ∫ x, D₀ F x * G x ∂μ := by
        simp_rw [h₁]
        refine integral_subtype_comap_of_ae_restrict_compl_eq_zero (f := fun x ↦ D₀ F x * G x) hU
          (ae_restrict_of_forall_mem hU.compl fun x hx ↦ ?_)
        simp [G, ContMDiffMap.cutoffExtend_apply_of_notMem hσ.contMDiffOn hσU g hx]
    _ = ∫ x, F x * D₀' G x ∂μ :=
        h.integral_mul_eq (.inl (by rw [ContMDiffMap.coe_cutoffExtend]; exact hσc.smul_right))
    _ = ∫ x, f x * DU' g x ∂μ.comap Subtype.val := by
        simp_rw [h₂]
        refine (integral_subtype_comap_of_ae_restrict_compl_eq_zero (f := fun x ↦ F x * D₀' G x)
          hU (ae_restrict_of_forall_mem hU.compl fun x hx ↦ ?_)).symm
        simp [F, ContMDiffMap.cutoffExtend_apply_of_notMem hσ.contMDiffOn hσU f hx]

/-- **Formal transposes commute with restriction to open subsets.** If the differential operator
`D'` is a formal transpose of the differential operator `D` with respect to `μ`, then on an open
subset `U` the restriction `D'|_U` is a formal transpose of `D|_U` with respect to the restricted
measure `μ.comap Subtype.val`. -/
theorem IsFormalTranspose.restrictDifferentialOperators
    {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m}
    {D' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k}
    (h : (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D' μ) (U : Opens M) :
    (U.restrictDifferentialOperators m D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯).IsFormalTranspose
      (U.restrictDifferentialOperators k D') (μ.comap Subtype.val) := by
  rw [isFormalTranspose_iff]
  rintro f g (hf | hg)
  · exact integral_restrict_mul_eq_of_hasCompactSupport h hf
  · simpa only [mul_comm] using (integral_restrict_mul_eq_of_hasCompactSupport h.symm hg).symm

/-- **The formal transpose of a restriction.** If the differential operator `D'` is a formal
transpose of the differential operator `D` with respect to a locally finite measure `μ` that is
positive on open sets of a σ-compact manifold, then on an open subset `U` the formal transpose of
`D|_U` with respect to the restricted measure `μ.comap Subtype.val` is `D'|_U`. -/
theorem IsFormalTranspose.formalTranspose_restrictDifferentialOperators [SigmaCompactSpace M]
    [BorelSpace M] [IsLocallyFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {D : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ m}
    {D' : differentialOperators ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ k}
    (h : (D : C^∞⟮I, M; ℝ⟯ →ₗ[ℝ] C^∞⟮I, M; ℝ⟯).IsFormalTranspose D' μ) (U : Opens M) :
    (U.restrictDifferentialOperators m D : C^∞⟮I, U; ℝ⟯ →ₗ[ℝ] C^∞⟮I, U; ℝ⟯).formalTranspose
      (μ.comap Subtype.val) = U.restrictDifferentialOperators k D' := by
  have := Manifold.sigmaCompactSpace_opens I U
  have := Measure.IsOpenPosMeasure.comap μ U.isOpen.isOpenEmbedding_subtypeVal
  exact (h.restrictDifferentialOperators U).formalTranspose_eq

end LinearMap
