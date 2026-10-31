/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Connected.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
import TauCeti.Geometry.RealAlgebraic.CAD.Existence

/-!
# Decomposing semialgebraic sets into connected pieces

Every semialgebraic subset of a finite-dimensional real coordinate space `σ → ℝ` is the union of
finitely many pairwise disjoint connected semialgebraic sets
(`TauCeti.IsSemialgebraic.exists_finite_isConnected_partition`). The pieces are the cells, contained
in the set, of a cylindrical algebraic decomposition adapted to polynomials describing the set.

Such a decomposition reduces statements about a semialgebraic set to statements about connected
sets, for instance identity-theorem arguments for analytic functions defined near the set.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 5.1 (cylindrical decomposition).
-/

public section

open Function MvPolynomial Set

namespace TauCeti

/-- A semialgebraic subset of `ℝ ^ n` is the union of the cells of a cylindrical algebraic
decomposition that it contains. -/
private theorem IsSemialgebraic.exists_finite_isConnected_partition_fin {n : ℕ}
    {s : Set (Fin n → ℝ)} (hs : IsSemialgebraic s) :
    ∃ 𝒞 : Set (Set (Fin n → ℝ)), 𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧
      (∀ t ∈ 𝒞, IsConnected t ∧ IsSemialgebraic t) ∧ ⋃₀ 𝒞 = s := by
  classical
  obtain ⟨m, p, Φ, rfl⟩ := hs.exists_eq_setOf_sign_eval
  obtain ⟨𝒟, h𝒟, hp⟩ := exists_isCAD_signInvariant (Finset.univ.image p)
  -- each cell of `𝒟` lies in the set or misses it
  have hsub (E) (hE : E ∈ 𝒟) := subset_or_disjoint_setOf_sign (f := fun i x ↦ eval x (p i))
    (fun i ↦ hp _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) E hE) Φ
  refine ⟨{E ∈ 𝒟 | E ⊆ {x | Φ fun i ↦ SignType.sign (eval x (p i))}},
    h𝒟.finite.subset (sep_subset _ _),
    h𝒟.isPartition.pairwiseDisjoint.subset (sep_subset _ _),
    fun E hE ↦ ⟨h𝒟.isConnected hE.1, h𝒟.isSemialgebraic hE.1⟩,
    Subset.antisymm (sUnion_subset fun E hE ↦ hE.2) fun y hy ↦ ?_⟩
  obtain ⟨E, hE, hyE⟩ := mem_sUnion.1 (h𝒟.isPartition.sUnion_eq_univ ▸ mem_univ y)
  exact ⟨E, ⟨hE, (hsub E hE).resolve_right fun hd ↦ disjoint_left.1 hd hyE hy⟩, hyE⟩

/-- **Connected decomposition of semialgebraic sets.** A semialgebraic subset of `σ → ℝ`, for a
finite index type `σ`, is the union of finitely many pairwise disjoint connected semialgebraic
sets. -/
theorem IsSemialgebraic.exists_finite_isConnected_partition {σ : Type*} [Finite σ]
    {s : Set (σ → ℝ)} (hs : IsSemialgebraic s) :
    ∃ 𝒞 : Set (Set (σ → ℝ)), 𝒞.Finite ∧ 𝒞.PairwiseDisjoint id ∧
      (∀ t ∈ 𝒞, IsConnected t ∧ IsSemialgebraic t) ∧ ⋃₀ 𝒞 = s := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  -- transport a decomposition of the set read in the coordinates `Fin n`
  let φ : (Fin n → ℝ) → σ → ℝ := fun y ↦ y ∘ e
  have hφψ : LeftInverse φ (fun x ↦ x ∘ e.symm) := fun x ↦ by ext; simp [φ]
  have hψφ : RightInverse φ (fun x ↦ x ∘ e.symm) := fun y ↦ by ext; simp [φ]
  have hφ : Continuous φ := continuous_pi fun i ↦ continuous_apply (e i)
  obtain ⟨𝒟, h𝒟, hd, hc, hu⟩ :=
    IsSemialgebraic.exists_finite_isConnected_partition_fin (hs.preimage_comp e)
  refine ⟨image φ '' 𝒟, h𝒟.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨E, hE, rfl⟩ _ ⟨E', hE', rfl⟩ hne
    exact (disjoint_image_iff hψφ.injective).2 (hd hE hE' fun h ↦ hne (h ▸ rfl))
  · rintro _ ⟨E, hE, rfl⟩
    refine ⟨(hc E hE).1.image φ hφ.continuousOn, ?_⟩
    rw [image_eq_preimage_of_inverse hψφ hφψ]
    exact (hc E hE).2.preimage_comp e.symm
  · rw [← image_sUnion, hu, image_preimage_eq s hφψ.surjective]

end TauCeti
