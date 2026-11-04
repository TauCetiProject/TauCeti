/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.SmallFamily.Basic
public import TauCeti.Topology.Instances.CantorSpace
import TauCeti.MeasureTheory.Constructions.Polish.Analytic

/-!
# Extending witnesses in analytic families of assignments

Let `g : (ℕ → ℕ) → X × X` be continuous. A word `w` witnesses a tracked pair of coordinates
of an assignment `φ : ι → X` when that pair belongs to `g '' PiNat.wordCylinder w`.
For an analytic family that is not small, finitely many such words can be extended
simultaneously while retaining an analytic subfamily that is not small.

`SetRel.exists_subset_not_isSmallFamily_witness_append` extends every tracked word by one
letter. `SetRel.exists_subset_not_isSmallFamily_witness_extension` extends them by any specified
number of letters. These refinements keep witnesses coherent in fusion constructions of
continuous graph homomorphisms: repeated extensions determine a point of Baire space, and
continuity of `g` then identifies the limiting edge.

The relation defining smallness need not equal the range of `g`; in applications `g`
parametrizes that relation. Neither the index type of assignments nor the space of assignments
needs to be countable or Polish. Analyticity is retained by taking continuous preimages
*inside* the original analytic family.

## References

* B. D. Miller, *The graph-theoretic approach to descriptive set theory*, Bulletin of Symbolic
  Logic 18 (2012), 554–575, the witness refinement in the proof of the G₀ dichotomy.
-/

public section

open MeasureTheory Set PiNat

namespace SetRel

variable {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
  {G : SetRel X X} {Φ : Set (ι → X)} [Finite κ]
  {g : (ℕ → ℕ) → X × X} {e : κ → ι × ι} {w : κ → List ℕ}

/-- Finitely many tracked witness words can each be extended by one letter, on an analytic
subfamily that is still not small. The new letter for each pair is uniform over that subfamily. -/
theorem exists_subset_not_isSmallFamily_witness_append (hg : Continuous g)
    (hΦa : AnalyticSet Φ) (hΦ : ¬ G.IsSmallFamily Φ)
    (hw : ∀ φ ∈ Φ, ∀ k, (φ (e k).1, φ (e k).2) ∈ g '' wordCylinder (w k)) :
    ∃ c : κ → ℕ, ∃ Ψ ⊆ Φ, AnalyticSet Ψ ∧ ¬ G.IsSmallFamily Ψ ∧
      ∀ φ ∈ Ψ, ∀ k, (φ (e k).1, φ (e k).2) ∈ g '' wordCylinder (w k ++ [c k]) := by
  classical
  let F (c : κ → ℕ) : Set (ι → X) :=
    {φ | ∀ k, (φ (e k).1, φ (e k).2) ∈ g '' wordCylinder (w k ++ [c k])}
  have hcov : Φ ⊆ ⋃ c, F c := by
    intro φ hφ
    have hletter (k : κ) :
        ∃ n, (φ (e k).1, φ (e k).2) ∈ g '' wordCylinder (w k ++ [n]) := by
      have := hw φ hφ k
      rw [← iUnion_wordCylinder_append_singleton (w k), Set.image_iUnion] at this
      exact mem_iUnion.1 this
    choose c hc using hletter
    exact mem_iUnion.2 ⟨c, hc⟩
  obtain ⟨c, hc⟩ := exists_not_isSmallFamily_inter hΦ hcov
  refine ⟨c, Φ ∩ F c, inter_subset_left, ?_, hc, fun _ h ↦ h.2⟩
  -- Include `Φ` as the `none` term, so the intersection also works when no pairs are tracked.
  let A : Option κ → Set (ι → X)
    | none => Φ
    | some k => Φ ∩ (fun φ ↦ (φ (e k).1, φ (e k).2)) ⁻¹'
        (g '' wordCylinder (w k ++ [c k]))
  have heq : Φ ∩ F c = ⋂ k, A k := by
    rw [iInter_option]
    ext φ
    simp only [mem_inter_iff, mem_iInter, mem_ofPred_eq, A, F]
    exact ⟨fun ⟨h, h'⟩ ↦ ⟨h, fun k ↦ ⟨h, h' k⟩⟩,
      fun ⟨h, h'⟩ ↦ ⟨h, fun k ↦ (h' k).2⟩⟩
  rw [heq]
  refine AnalyticSet.iInter fun k ↦ ?_
  cases k with
  | none => exact hΦa
  | some k =>
    exact hΦa.inter_preimage (by fun_prop)
      ((measurableSet_wordCylinder _).analyticSet.image_of_continuous hg)

/-- Extend every word witnessing one of finitely many tracked coordinate pairs by exactly `n`
letters, retaining analyticity and non-smallness. The new words extend the old ones, not merely
their lengths. -/
theorem exists_subset_not_isSmallFamily_witness_extension (hg : Continuous g)
    (hΦa : AnalyticSet Φ) (hΦ : ¬ G.IsSmallFamily Φ)
    (hw : ∀ φ ∈ Φ, ∀ k, (φ (e k).1, φ (e k).2) ∈ g '' wordCylinder (w k)) (n : ℕ) :
    ∃ v : κ → List ℕ, (∀ k, w k <+: v k) ∧ (∀ k, (v k).length = (w k).length + n) ∧
      ∃ Ψ ⊆ Φ, AnalyticSet Ψ ∧ ¬ G.IsSmallFamily Ψ ∧
        ∀ φ ∈ Ψ, ∀ k, (φ (e k).1, φ (e k).2) ∈ g '' wordCylinder (v k) := by
  induction n with
  | zero => exact ⟨w, fun _ ↦ List.prefix_refl _, by simp, Φ, Subset.rfl, hΦa, hΦ, hw⟩
  | succ n ih =>
    obtain ⟨v, hv, hlen, Ψ, hΨΦ, hΨa, hΨ, hΨw⟩ := ih
    obtain ⟨c, Ω, hΩΨ, hΩa, hΩ, hΩw⟩ :=
      exists_subset_not_isSmallFamily_witness_append hg hΨa hΨ hΨw
    refine ⟨fun k ↦ v k ++ [c k], fun k ↦ (hv k).trans (List.prefix_append _ _),
      ?_, Ω, hΩΨ.trans hΨΦ, hΩa, hΩ, hΩw⟩
    intro k
    simp [hlen, Nat.add_assoc]

end SetRel
