/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Finite chart localization of compactly supported forms

A locally finite partition of unity has only finitely many terms meeting the compact support
of a form. These terms give an actual finite decomposition into forms supported in individual
charts. Only continuity of the partition is needed; no measurable structure on the manifold
is installed.
-/

public section

noncomputable section

open Set Function
open scoped Manifold

namespace TauCeti.RoughForm

variable {E H M F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- A partition of unity localizes any compactly supported rough form into finitely many
actual terms. All terms outside the chosen finite set vanish identically. -/
theorem exists_finset_partition_eq (φ : RoughForm I M F k) (hc : IsCompact φ.tsupport)
    (ρ : PartitionOfUnity ι M univ) :
    ∃ s : Finset ι,
      φ = (fun x ↦ ∑ i ∈ s, ρ i x • φ x) ∧
        ∀ i ∉ s, (fun x ↦ ρ i x • φ x : RoughForm I M F k) = 0 := by
  classical
  have hfin := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hc
  let s := hfin.toFinset
  have hmem (i : ι) (x : M) (hρ : ρ i x ≠ 0) (hφ : φ x ≠ 0) : i ∈ s := by
    exact hfin.mem_toFinset.mpr ⟨x, subset_tsupport (ρ i) hρ, mem_tsupport_of_ne_zero hφ⟩
  refine ⟨s, ?_, ?_⟩
  · funext x
    by_cases hx : φ x = 0
    · simp [hx]
    · have hs : ρ.finsupport x ⊆ s := by
        intro i hi
        exact hmem i x (by simpa only [PartitionOfUnity.mem_finsupport, mem_support] using hi) hx
      rw [← Finset.sum_smul, ρ.sum_finsupport' (mem_univ x) hs, one_smul]
  · intro i hi
    funext x
    by_cases hφ : φ x = 0
    · simp [hφ]
    · have hρ : ρ i x = 0 := by
        by_contra h
        exact hi (hmem i x h hφ)
      simp [hρ]

/-- A compactly supported form admits a finite continuous partition in preferred charts.
Local compactness of the finite-dimensional model suffices; no global paracompactness is
required. The weights are nonnegative, bounded by one, and compactly supported. -/
theorem exists_chart_partition [FiniteDimensional ℝ E] [T2Space M]
    (φ : RoughForm I M F k) (hc : IsCompact φ.tsupport) :
    ∃ n : ℕ, ∃ α : Fin n → M, ∃ ρ : Fin n → C(M, ℝ),
      (∀ i, _root_.tsupport (ρ i) ⊆ (chartAt H (α i)).source) ∧
        EqOn (∑ i, ρ i) 1 φ.tsupport ∧
        (∀ i x, ρ i x ∈ Icc (0 : ℝ) 1) ∧ ∀ i, HasCompactSupport (ρ i) := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun x : M ↦ (chartAt H x).source)
    (fun x ↦ (chartAt H x).open_source)
    (fun x _ ↦ mem_iUnion.mpr ⟨x, mem_chart_source H x⟩)
  let α : Fin s.card → M := fun i ↦ ((s.equivFin).symm i).val
  have hcover : φ.tsupport ⊆ ⋃ i, (chartAt H (α i)).source := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨s.equivFin ⟨y, hy⟩, by simpa [α] using hxy⟩
  obtain ⟨ρ, hρ⟩ := exists_continuous_sum_one_of_isOpen_isCompact
    (fun i ↦ (chartAt H (α i)).open_source) hc hcover
  exact ⟨s.card, α, ρ, hρ⟩

/-- Weights summing to one on the support give an actual finite form decomposition. -/
theorem eq_sum_fun_smul {n : ℕ} (φ : RoughForm I M F k) (ρ : Fin n → M → ℝ)
    (hρ : ∀ x ∈ φ.tsupport, ∑ i, ρ i x = 1) :
    φ = (fun x ↦ ∑ i, ρ i x • φ x) := by
  funext x
  by_cases hx : x ∈ φ.tsupport
  · rw [← Finset.sum_smul, hρ x hx, one_smul]
  · simp [eq_zero_of_notMem_tsupport hx]

/-- A compactly supported continuous form decomposes into finitely many continuous,
compactly supported forms in preferred charts, without global paracompactness. -/
theorem exists_chart_decomposition [IsManifold I 1 M] [FiniteDimensional ℝ E] [T2Space M]
    (φ : RoughForm I M F k) (hφ : IsSmoothForm I 0 φ) (hc : IsCompact φ.tsupport) :
    ∃ n : ℕ, ∃ α : Fin n → M, ∃ ψ : Fin n → RoughForm I M F k,
      φ = (fun x ↦ ∑ i, ψ i x) ∧
        ∀ i, IsSmoothForm I 0 (ψ i) ∧ IsCompact (ψ i).tsupport ∧
          (ψ i).tsupport ⊆ (chartAt H (α i)).source ∧ (ψ i).tsupport ⊆ φ.tsupport := by
  obtain ⟨n, α, ρ, hs, hsum, _, _⟩ := exists_chart_partition φ hc
  refine ⟨n, α, fun i x ↦ ρ i x • φ x, ?_, ?_⟩
  · exact eq_sum_fun_smul φ (fun i ↦ ρ i) (fun x hx ↦ by
      simpa only [ContinuousMap.coe_sum, Finset.sum_apply, Pi.one_apply] using hsum hx)
  · intro i
    exact ⟨hφ.fun_smul (contMDiff_zero_iff.mpr (ρ i).continuous),
      isCompact_tsupport_fun_smul hc (ρ i),
      (tsupport_fun_smul_subset_left (ρ i) φ).trans (hs i),
      tsupport_fun_smul_subset_right (ρ i) φ⟩

end TauCeti.RoughForm
