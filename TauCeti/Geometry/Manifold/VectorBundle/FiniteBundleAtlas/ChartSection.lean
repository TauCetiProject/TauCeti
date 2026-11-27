/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Smooth sections from compactly supported chart functions

Let `A` be a finite bundle atlas of a smooth vector bundle `V → M` over a Hausdorff manifold
modelled on a finite-dimensional real normed space `E`. A smooth function `φ : E → F` with compact
support inside the image of chart `i` is the reading in chart `i` of a smooth section of `V`,
supported over the image of the support of `φ` under the inverse chart
(`TauCeti.FiniteBundleAtlas.exists_contMDiff_eqOn_coord`). The section is `ψ • A.chartSection i φ`
for a smooth cutoff `ψ` equal to `1` over the support of `φ` and supported in the domain of
chart `i`.

## Main results

* `TauCeti.FiniteBundleAtlas.exists_contMDiff_eqOn_coord`: a smooth function with compact support
  in a chart image is the reading of a smooth section, supported over its support.
-/

public section

open Bundle Set
open scoped Manifold ContDiff Topology

universe u

namespace TauCeti

namespace FiniteBundleAtlas

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] (A : FiniteBundleAtlas E M F V)

/-- **Smooth sections from chart functions.** A smooth function `φ` with compact support inside
the image of chart `i` is the reading in chart `i` of a smooth section, supported over the image
of the support of `φ` under the inverse chart. -/
theorem exists_contMDiff_eqOn_coord {i : Fin A.n} {φ : E → F} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφi : tsupport φ ⊆ A.image i) :
    ∃ ξ : Π x, V x, ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, F)) ∞ (T% ξ) ∧
      EqOn (A.coord i ξ) φ (A.image i) ∧
      closure {x | ξ x ≠ 0} ⊆ (A.chart i).symm '' tsupport φ := by
  set K := (A.chart i).symm '' tsupport φ
  have hK : IsCompact K := hφc.image_of_continuousOn ((A.continuousOn_chart_symm i).mono hφi)
  have hKi : K ⊆ A.dom i := by
    rintro _ ⟨z, hz, rfl⟩
    exact A.symm_mem_dom (hφi hz)
  -- A smooth cutoff equal to `1` near `K` and supported in the domain of chart `i`.
  obtain ⟨ψ, hψs, hψ1, -, hψi, -⟩ :=
    hK.exists_contMDiff_one_nhds_tsupport_subset 𝓘(ℝ, E) (A.isOpen_dom i) hKi
  have hψK : ∀ x ∈ K, ψ x = 1 := fun x hx ↦ hψ1.self_of_nhdsSet x hx
  refine ⟨fun x ↦ ψ x • A.chartSection i φ x, contMDiff_smul_chartSection hψs (A.image i).isOpen
    (fun x hx ↦ ⟨hψi hx, A.mem_image.2 ⟨x, hψi hx, rfl⟩⟩) hφ.contDiffOn, fun y hy ↦ ?_,
    closure_minimal (fun x hx ↦ ?_) hK.isClosed⟩
  · rw [A.coord_fun_smul i _ _ hy, coord_chartSection φ hy]
    by_cases hφy : φ y = 0
    · rw [hφy, smul_zero]
    · rw [hψK _ ⟨y, subset_tsupport φ hφy, rfl⟩, one_smul]
  · by_contra hxK
    refine hx ?_
    beta_reduce
    rw [chartSection_eq_zero fun hxi ↦ ?_, smul_zero]
    by_contra hφx
    refine hxK ⟨A.chart i x, subset_tsupport φ hφx, ?_⟩
    exact (A.chart i).left_inv (A.dom_subset_chart_source i hxi)

end FiniteBundleAtlas

end TauCeti
