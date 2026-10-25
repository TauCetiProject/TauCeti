/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
public import TauCeti.Topology.Category.TopCat.ClosedEmbedding

/-!
# Compact subsets of sequential colimits in `TopCat`

A compact subset of a sequential colimit of `T1` spaces with injective transition maps is
contained in the image of one stage. When the successor maps are closed embeddings, continuous
maps from compact spaces therefore factor continuously through one stage. These results apply to
weak topologies on skeletal filtrations.

Colimits of compactly generated spaces are compactly generated already in `TopCat`; no change
of the final topology is needed.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, Proposition A.1, for the closed discrete subset argument for compact subsets.
-/

public section

open CategoryTheory Limits Topology Set

universe w u

namespace TauCeti.TopCat

variable {F : ℕ ⥤ TopCat.{u}} {c : Cocone F}

/-- A compact subset of a sequential colimit of `T1` spaces with injective transition maps
is contained in the image of one stage. -/
theorem exists_subset_range_ι_of_isColimit
    (hF : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j), Function.Injective (F.map (homOfLE hij)))
    (hc : IsColimit c) [∀ n, T1Space (F.obj n)] {K : Set c.pt} (hK : IsCompact K) :
    ∃ n, K ⊆ range (c.ι.app n) := by
  classical
  by_contra h
  simp only [not_exists, not_subset] at h
  choose x hxK hx using h
  have hrange {i j : ℕ} (hij : i ≤ j) : range (c.ι.app i) ⊆ range (c.ι.app j) := by
    rintro _ ⟨y, rfl⟩
    exact ⟨F.map (homOfLE hij) y, ConcreteCategory.congr_hom (c.w (homOfLE hij)) y⟩
  have htail (n i : ℕ) (hi : n ≤ i) : x i ∉ range (c.ι.app n) :=
    fun hxi ↦ hx i (hrange hi hxi)
  -- Every subset of the selected range has finite traces on all stages, hence is closed.
  have hclosed (s : Set c.pt) (hs : s ⊆ range x) : IsClosed s := by
    apply (TopCat.isClosed_iff_of_isColimit c hc s).2
    intro n
    have hsub : c.ι.app n ⁻¹' s ⊆ c.ι.app n ⁻¹' (x '' Set.Iio n) := by
      intro y hy
      obtain ⟨i, hi⟩ := hs hy
      have hin : x i ∈ range (c.ι.app n) := ⟨y, hi.symm⟩
      exact ⟨i, lt_of_not_ge (fun hni ↦ htail n i hni hin), hi⟩
    exact (((Set.finite_Iio n).image x).preimage
      (injective_ι_of_isColimit hF hc n).injOn).subset hsub |>.isClosed
  have hdiscrete : IsDiscrete (range x) :=
    isDiscrete_iff_forall_mem_exists_isClosed.2 fun s hs ↦
      ⟨s, hclosed s hs, inter_eq_self_of_subset_left hs⟩
  have hfinite : (range x).Finite :=
    (hK.of_isClosed_subset (hclosed _ Subset.rfl) (range_subset_iff.2 hxK)).finite hdiscrete
  -- Each fiber of the sequence is finite too, since its value belongs to some stage.
  have hnat : (Set.univ : Set ℕ).Finite := by
    apply Set.Finite.of_finite_fibers x (by simpa using hfinite)
    intro y _
    obtain ⟨n, z, rfl⟩ :=
      Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget TopCat) hc) y
    apply (Set.finite_Iio n).subset
    rintro i ⟨_, hi⟩
    exact lt_of_not_ge fun hni ↦ htail n i hni ⟨z, hi.symm⟩
  exact Set.infinite_univ hnat

/-- A continuous map from a compact space into a sequential colimit of `T1` spaces along
closed embeddings factors continuously through one stage. -/
theorem exists_factorization_of_isColimit
    (hF : ∀ n : ℕ, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (hc : IsColimit c) [∀ n, T1Space (F.obj n)]
    {X : Type w} [TopologicalSpace X] [CompactSpace X] (f : C(X, c.pt)) :
    ∃ (n : ℕ) (g : C(X, F.obj n)), ∀ x, c.ι.app n (g x) = f x := by
  have hmaps : ∀ ⦃i j : ℕ⦄ (hij : i ≤ j), IsClosedEmbedding (F.map (homOfLE hij)) :=
    fun _ _ hij ↦ isClosedEmbedding_map_of_isWellOrderContinuous F (fun n _ ↦ hF n) hij
  obtain ⟨n, hn⟩ := exists_subset_range_ι_of_isColimit
    (fun _ _ hij ↦ (hmaps hij).injective) hc (isCompact_range f.continuous)
  choose g hg using fun x ↦ hn (mem_range_self x)
  refine ⟨n, ⟨g, ?_⟩, hg⟩
  apply (isClosedEmbedding_ι_of_isColimit hmaps hc n).isEmbedding.continuous_iff.2
  exact f.continuous.congr fun x ↦ (hg x).symm

/-- The colimit in `TopCat` of compactly generated spaces is compactly generated with its
original final topology. -/
theorem compactlyGeneratedSpace_of_isColimit {J : Type w} [SmallCategory J]
    {F : J ⥤ TopCat.{u}} {c : Cocone F} (hc : IsColimit c)
    [∀ j, CompactlyGeneratedSpace (F.obj j)] : CompactlyGeneratedSpace c.pt := by
  apply uCompactlyGeneratedSpace_of_coinduced.{u}
    (f := fun p : Σ j, F.obj j ↦ c.ι.app p.1 p.2)
    (continuous_sigma fun j ↦ (c.ι.app j).hom.continuous)
  rw [TopCat.coinduced_of_isColimit c hc, instTopologicalSpaceSigma, coinduced_iSup]
  simp only [coinduced_compose]
  rfl

end TauCeti.TopCat
