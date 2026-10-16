/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Support
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite

/-!
# Finite localization of compactly supported forms

A locally finite partition of unity has only finitely many terms meeting the compact support
of a form. These terms give a finite decomposition by partition weights. Containment of each
localized support in a chart requires a separate subordination hypothesis. Only continuity
of the partition is needed; no measurable structure on the manifold is installed.
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
theorem exists_finset_partition_eq (φ : RoughForm I M F k) (hc : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ))
    (ρ : PartitionOfUnity ι M univ) :
    ∃ s : Finset ι,
      φ = (fun x ↦ ∑ i ∈ s, ρ i x • φ x) ∧
        ∀ i ∉ s, (fun x ↦ ρ i x • φ x : RoughForm I M F k) = 0 := by
  classical
  have hfin := ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hc
  let s := hfin.toFinset
  have hmem (i : ι) (x : M) (hρ : ρ i x ≠ 0) (hφ : φ x ≠ 0) : i ∈ s := by
    exact hfin.mem_toFinset.mpr ⟨x, subset_tsupport (ρ i) hρ,
    _root_.subset_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ hφ⟩
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

/-- Weights summing to one on the support give an actual finite form decomposition. -/
theorem eq_sum_fun_smul {n : ℕ} (φ : RoughForm I M F k) (ρ : Fin n → M → ℝ)
    (hρ : ∀ x ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ), ∑ i, ρ i x = 1) :
    φ = (fun x ↦ ∑ i, ρ i x • φ x) := by
  funext x
  by_cases hx : x ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)
  · rw [← Finset.sum_smul, hρ x hx, one_smul]
  · have hz : φ x = 0 :=
      _root_.image_eq_zero_of_notMem_tsupport (α := E [⋀^Fin _]→L[ℝ] F) hx
    simp [hz]

end TauCeti.RoughForm
