/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Finite localization of test functions

A test function can be written as a finite sum of tests subordinate to any open cover of its
support. Consequently, an additive map on test functions which vanishes locally vanishes globally;
continuity of the additive map is not required.

The decomposition uses Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`, applied to the
compact support. This is the partition-of-unity localization of distributions described in
Hörmander, *The Analysis of Linear Partial Differential Operators I*, §2.1.
-/

public section

open Set TopologicalSpace
open scoped Distributions ContDiff Manifold

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {n : ℕ∞}

/-- A test function is a finite sum of test functions supported in members of an open cover
of its topological support. -/
theorem exists_sum_subordinate (φ : 𝓓^{n}(Ω, F)) {ι : Type*} (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (hcover : tsupport φ ⊆ ⋃ i, U i) :
    ∃ (s : Finset ι) (ψ : s → 𝓓^{n}(Ω, F)),
      (∀ i, tsupport (ψ i) ⊆ U i) ∧ ∑ i, ψ i = φ := by
  classical
  obtain ⟨s, hs⟩ := φ.hasCompactSupport.elim_finite_subcover U hU hcover
  have hs' : tsupport φ ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E)
    (isClosed_tsupport φ) (fun i : s ↦ U i) (fun i ↦ hU i) hs'
  let ψ : s → 𝓓^{n}(Ω, F) := fun i ↦
    ⟨fun x ↦ ρ i x • φ x,
      ((ρ i).contMDiff.contDiff.of_le (by simp)).smul φ.contDiff,
      φ.hasCompactSupport.smul_left,
      (tsupport_smul_subset_right _ _).trans φ.tsupport_subset⟩
  refine ⟨s, ψ, fun i ↦ (tsupport_smul_subset_left _ _).trans (hρ i), ?_⟩
  ext x
  simp only [sum_apply]
  by_cases hx : x ∈ tsupport φ
  · have hsum : ∑ i : s, ρ i x = 1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hx
    exact (Finset.sum_smul ..).symm.trans (by rw [hsum, one_smul])
  · simp [ψ, image_eq_zero_of_notMem_tsupport hx]

end TestFunction

namespace AddMonoidHom

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [AddCommMonoid G] {Ω : Opens E} {n : ℕ∞}

/-- An additive map on test functions vanishes if every point of the domain has an open
neighborhood on whose supported tests it vanishes. -/
theorem eq_zero_of_locally_vanishing (T : 𝓓^{n}(Ω, F) →+ G)
    (h : ∀ x ∈ Ω, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ∀ φ : 𝓓^{n}(Ω, F), tsupport φ ⊆ U → T φ = 0) : T = 0 := by
  classical
  choose U hU hxU hT using fun x : Ω ↦ h x x.2
  ext φ
  obtain ⟨s, ψ, hψ, hsum⟩ := φ.exists_sum_subordinate U hU fun x hx ↦
    mem_iUnion.mpr ⟨⟨x, φ.tsupport_subset hx⟩, hxU _⟩
  rw [← hsum, map_sum]
  exact Finset.sum_eq_zero fun i _ ↦ hT i (ψ i) (hψ i)

end AddMonoidHom
