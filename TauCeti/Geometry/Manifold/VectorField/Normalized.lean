/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.Regularity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Normalizing a descending vector field near a compact set

Let `f` be a smooth real function on a Hausdorff manifold `M` modelled on a finite-dimensional real
space, and let `Y` be a smooth vector field along which `f` strictly decreases on a compact set
`K`, that is `df(Y) < 0` on `K`. Rescaling `Y` by the positive function `1 / (-df(Y))` gives a
field along which `f` decreases at unit speed. Cut off away from `K`, this is a smooth vector field
`X` with compact support, a nonnegative multiple of `Y` at every point, which equals `Y / (-df(Y))`
near `K` (`TauCeti.exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero`).

## Main results

* `TauCeti.exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero`: the cut-off normalized field
  `Y / (-df(Y))` near a compact set on which `df(Y) < 0`.
-/

public section

open Bundle Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {f : M → ℝ} {Y : (x : M) → TangentSpace I x}

/-- **Normalizing a descending field near a compact set.** Let `f` be smooth and `Y` a smooth
vector field with `df(Y) < 0` on a compact set `K`. Then there is a smooth vector field `X`,
vanishing outside a compact set, which is a nonnegative multiple of `Y` at every point, along which
`f` never increases, and which equals the normalized field `Y / (-df(Y))` on an open neighbourhood
`U` of `K` on which `df(Y) < 0`. In particular `df(X) = -1` on `U`. -/
theorem exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hY : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hKY : ∀ x ∈ K, mvfderiv I f x (Y x) < 0) :
    ∃ X : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∀ x, ∃ c : ℝ, 0 ≤ c ∧ X x = c • Y x) ∧ (∀ x, mvfderiv I f x (X x) ≤ 0) ∧
      (∃ U, IsOpen U ∧ K ⊆ U ∧
        ∀ x ∈ U, mvfderiv I f x (Y x) < 0 ∧ X x = (-mvfderiv I f x (Y x))⁻¹ • Y x) ∧
      ∃ C, IsCompact C ∧ ∀ x ∉ C, X x = 0 := by
  -- The derivative `g = df(Y)` is smooth, and negative on an open set containing `K`.
  obtain ⟨g, hg⟩ : ∃ g : M → ℝ, ∀ y, g y = mvfderiv I f y (Y y) := ⟨_, fun _ ↦ rfl⟩
  have hgC : ContMDiff I 𝓘(ℝ) ∞ g := by
    rw [funext hg]
    exact (hf.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp hY
  have hW : IsOpen {y | g y < 0} := isOpen_lt hgC.continuous continuous_const
  obtain ⟨σ, hσC, hσ1, hσC_compact, hσW, hσ01⟩ := hK.exists_contMDiff_one_nhds_tsupport_subset I hW
    fun x hx ↦ by rw [mem_ofPred_eq, hg]; exact hKY x hx
  have hσg : ∀ y, σ y ≠ 0 → g y < 0 := fun y hy ↦ hσW (subset_tsupport _ hy)
  -- Off `{g < 0}` the cutoff vanishes, and on `{g < 0}` the normalized field is smooth.
  have hZ : ContMDiffOn I I.tangent ∞
      (fun y ↦ (⟨y, (-g y)⁻¹ • Y y⟩ : TangentBundle I M)) {y | g y < 0} :=
    (hgC.neg.contMDiffOn.inv₀ fun y (hy : g y < 0) ↦ neg_ne_zero.2 hy.ne).smul_section
      hY.contMDiffOn
  obtain ⟨X, hX⟩ : ∃ X : (x : M) → TangentSpace I x, ∀ y, X y = σ y • ((-g y)⁻¹ • Y y) :=
    ⟨_, fun _ ↦ rfl⟩
  have hdfX : ∀ y, mvfderiv I f y (X y) = -σ y := fun y ↦ by
    rw [hX, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hg]
    by_cases hy : σ y = 0
    · simp [hy]
    · field_simp [(hσg y hy).ne]
  refine ⟨X, ?_, fun y ↦ ⟨σ y * (-g y)⁻¹, ?_, by rw [hX, smul_smul]⟩,
    fun y ↦ by rw [hdfX]; linarith [(hσ01 y).1],
    ⟨interior {y | σ y = 1}, isOpen_interior, subset_interior_iff_mem_nhdsSet.2 hσ1,
      fun y hy ↦ ?_⟩, tsupport σ, hσC_compact, fun y hy ↦ ?_⟩
  · rw [funext hX]
    exact ContMDiffOn.smul_section_of_tsupport hσC.contMDiffOn hW hσW hZ
  · by_cases hy : σ y = 0
    · simp [hy]
    · exact mul_nonneg (hσ01 y).1 (inv_nonneg.2 (by linarith [hσg y hy]))
  · have hσy : σ y = 1 := interior_subset hy
    refine ⟨?_, by rw [hX, hσy, one_smul, hg]⟩
    rw [← hg]
    exact hσg y (by rw [hσy]; exact one_ne_zero)
  · rw [hX, image_eq_zero_of_notMem_tsupport hy, zero_smul]

end TauCeti
