/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Gluing local smooth extensions on a closed set

Vector-valued data on a closed subset of a smooth manifold extend globally if they
extend smoothly near every point of that subset. The extension can have topological
support inside any prescribed open neighbourhood. This is the partition-of-unity
step in extending velocities from an embedded submanifold to its ambient manifold.

The construction uses Mathlib's `SmoothPartitionOfUnity.contMDiff_finsum_smul`.
Reference: M. Hirsch, *Differential Topology*, Chapter 2, §2, and Chapter 8, §1.
-/

public section

open Set Function Topology
open scoped Manifold ContDiff

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {n : ℕ∞}

/-- Locally smoothly extendible vector-valued data on a closed set have a global
`C^n` extension supported inside any prescribed open neighbourhood of that set.
No regularity is required of the original function away from the closed set. -/
theorem IsClosed.exists_contMDiffMap_eqOn {s U : Set M} (hs : IsClosed s)
    {g : M → F} (hU : IsOpen U) (hsU : s ⊆ U)
    (hloc : ∀ x ∈ s, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∃ g' : M → F, ContMDiffOn I 𝓘(ℝ, F) n g' V ∧ EqOn g' g (s ∩ V)) :
    ∃ G : C^n⟮I, M; 𝓘(ℝ, F), F⟯, EqOn G g s ∧ tsupport G ⊆ U := by
  classical
  choose V hV hxV g' hg' heq using fun x : s => hloc x x.2
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hs
    (fun x : s => V x ∩ U) (fun x => (hV x).inter hU)
    (fun x hx => mem_iUnion_of_mem ⟨x, hx⟩ ⟨hxV ⟨x, hx⟩, hsU hx⟩)
  let G : M → F := fun x => ∑ᶠ i, ρ i x • g' i x
  have hG : ContMDiff I 𝓘(ℝ, F) n G :=
    ρ.contMDiff_finsum_smul fun i x hx =>
      (hg' i x (hρ i hx).1).contMDiffAt ((hV i).mem_nhds (hρ i hx).1)
  refine ⟨⟨G, hG⟩, ?_, ?_⟩
  · intro x hx
    calc
      G x = ∑ᶠ i, ρ i x • g x := by
        apply finsum_congr
        intro i
        by_cases hi : ρ i x = 0
        · simp [hi]
        · rw [heq i ⟨hx, (hρ i (subset_closure (mem_support.mpr hi))).1⟩]
      _ = (∑ᶠ i, ρ i x) • g x := (finsum_smul _ _).symm
      _ = g x := by rw [ρ.sum_eq_one hx, one_smul]
  · have hsupp : support G ⊆ ⋃ i, tsupport (ρ i) := by
      intro x hx
      by_contra h
      have hz : ∀ i, ρ i x = 0 := by
        intro i
        exact notMem_support.mp fun hi => h (mem_iUnion_of_mem i (subset_closure hi))
      exact hx (by simp [G, hz])
    have hc : IsClosed (⋃ i, tsupport (ρ i)) :=
      ρ.locallyFinite.closure.isClosed_iUnion (fun _ => isClosed_closure)
    exact (closure_minimal hsupp hc).trans (iUnion_subset fun i x hx => (hρ i hx).2)
