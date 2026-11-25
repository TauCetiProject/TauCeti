/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Local sections of a surjective submersion with a subordinate partition of unity

A surjective `C^n` submersion `f : M → N` with boundaryless source over a Hausdorff `σ`-compact
base admits global set-theoretic sections, each `C^n` on a member of an open cover of `N`, together
with a smooth partition of unity on `N` subordinate to that cover
(`Manifold.IsSubmersion.exists_smoothPartitionOfUnity_sections_of_surjective`). Gluing local
constructions along such sections is the standard way to pass from the local section theorem
(`Manifold.IsSubmersion.exists_contMDiffOn_section_of_surjective`) to global statements.
-/

public section

namespace Manifold

open Function Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [FiniteDimensional ℝ E'']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E'' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {n : ℕ∞ω} {f : M → N}

/-- **Local sections of a surjective submersion with a partition of unity.** A surjective `C^n`
submersion `f : M → N` with boundaryless source over a Hausdorff `σ`-compact base admits global
set-theoretic sections `s i` of `f`, each `C^n` on an open set `U i`, together with a smooth
partition of unity on `N` subordinate to the cover `U`. -/
theorem IsSubmersion.exists_smoothPartitionOfUnity_sections_of_surjective [I.Boundaryless]
    [T2Space N] [SigmaCompactSpace N] (h : IsSubmersion I J n f) (hsurj : Surjective f) :
    ∃ (ρ : SmoothPartitionOfUnity N J N univ) (U : N → Set N) (s : N → N → M),
      ρ.IsSubordinate U ∧ (∀ i, IsOpen (U i)) ∧ (∀ i y, f (s i y) = y) ∧
        ∀ i, ContMDiffOn J I n (s i) (U i) := by
  classical
  choose U hU hyU s₀ hs₀ hfs₀ using fun y ↦ h.exists_contMDiffOn_section_of_surjective hsurj y
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate J isClosed_univ U hU
    fun y _ ↦ mem_iUnion.2 ⟨y, hyU y⟩
  refine ⟨ρ, U, fun i z ↦ if z ∈ U i then s₀ i z else surjInv hsurj z, hρ, hU, fun i z ↦ ?_,
    fun i ↦ (hs₀ i).congr fun z hz ↦ ite_eq_left_iff.2 fun h ↦ (h hz).elim⟩
  dsimp only
  split_ifs with h
  · exact hfs₀ i z h
  · exact surjInv_eq hsurj z

end Manifold
