/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Spectral.ProConstructible
public import TauCeti.Topology.Category.TopCat.Limits.Compact
import Mathlib.Topology.WithTopology

/-!
# Finite-stage detection in spectral limits

Containment and equality between inverse images of compact opens in a cofiltered spectral
limit hold after some transition map. In particular, emptiness and covering the whole limit
are detected at a finite stage. Neither the transitions nor the limit projections need to be
surjective. The compactness argument works more generally for pro-constructible subsets.

Pass to the compact Hausdorff constructible topologies and use finite-stage emptiness there.
These detection results allow relations between finite-stage opens to be imposed simultaneously
when constructing maps out of spectral limits.

## References

* The Stacks Project, Tags 0A2Y and 0A30.
* P. Scholze, *Perfectoid spaces*, §6, Lemma 6.13(iv).
-/

public section

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits

namespace TopCat

universe v u

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
  (F : J ⥤ TopCat.{max v u}) [∀ j, SpectralSpace (F.obj j)]
  (hF : ∀ {i j} (f : i ⟶ j), IsSpectralMap (F.map f))
  (c : Cone F) (hc : IsLimit c)

include hF hc

/-- A pro-constructible subset of a stage that misses the spectral limit already misses a
later stage. -/
theorem exists_preimage_eq_empty_of_isProConstructible {i : J} {s : Set (F.obj i)}
    (hs : TauCeti.IsProConstructible s) (h : c.π.app i ⁻¹' s = ∅) :
    ∃ (j : J) (f : j ⟶ i), F.map f ⁻¹' s = ∅ := by
  let G : J ⥤ TopCat.{max v u} :=
    { obj := fun j ↦ TopCat.of (WithConstructibleTopology (F.obj j))
      map := fun {j k} f ↦ TopCat.ofHom
        ⟨WithTopology.toTopology _ ∘ F.map f ∘ WithTopology.ofTopology,
          (hF f).continuous_withConstructibleTopology⟩
      map_id := by intro j; ext x; simp
      map_comp := by intro j k l f g; ext x; simp }
  have : ∀ j, CompactSpace (G.obj j) := fun j ↦
    inferInstanceAs (CompactSpace (WithConstructibleTopology (F.obj j)))
  have : ∀ j, T2Space (G.obj j) := fun j ↦
    inferInstanceAs (T2Space (WithConstructibleTopology (F.obj j)))
  let α : G ⟶ F :=
    { app := fun j ↦ TopCat.ofHom
        ⟨WithTopology.ofTopology, TauCeti.continuous_ofTopology_withConstructibleTopology _⟩
      naturality := by intro j k f; ext x; rfl }
  let d := (Cone.postcompose α).obj (limitCone G)
  have hempty : (limitCone G).π.app i ⁻¹' (WithTopology.ofTopology ⁻¹' s) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have he : c.π.app i (hc.lift d x) = WithTopology.ofTopology ((limitCone G).π.app i x) :=
      ConcreteCategory.congr_hom (hc.fac d i) x
    have hm : hc.lift d x ∈ c.π.app i ⁻¹' s := by
      simpa only [mem_preimage, he] using hx
    rw [h] at hm
    exact hm
  have hs' : IsClosed (WithTopology.ofTopology ⁻¹' s :
      Set (WithConstructibleTopology (F.obj i))) :=
    WithConstructibleTopology.isClosed_iff.mpr (TauCeti.isProConstructible_iff_isClosed.mp hs)
  obtain ⟨j, f, hf⟩ := exists_preimage_eq_empty_of_isLimit G _ (limitConeIsLimit G) hs' hempty
  refine ⟨j, f, Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦ ?_⟩
  have hm : WithTopology.toTopology (constructibleTopology (F.obj j)) x ∈
      G.map f ⁻¹' (WithTopology.ofTopology ⁻¹' s) := hx
  rw [hf] at hm
  exact hm

/-- Containment of pullbacks of compact opens in a spectral limit is detected after a
transition map. -/
theorem exists_preimage_subset_of_isLimit {i : J} {s t : Set (F.obj i)}
    (hso : IsOpen s) (hsc : IsCompact s) (hto : IsOpen t) (htc : IsCompact t)
    (h : c.π.app i ⁻¹' s ⊆ c.π.app i ⁻¹' t) :
    ∃ (j : J) (f : j ⟶ i), F.map f ⁻¹' s ⊆ F.map f ⁻¹' t := by
  have hst : TauCeti.IsProConstructible (s \ t) := by
    apply TauCeti.isProConstructible_iff_isClosed.mpr
    have hscl := hsc.isClopen_constructibleTopology_of_isOpen hso
    have htcl := htc.isClopen_constructibleTopology_of_isOpen hto
    let : TopologicalSpace (F.obj i) := constructibleTopology (F.obj i)
    exact hscl.isClosed.sdiff htcl.isOpen
  have hempty : c.π.app i ⁻¹' (s \ t) = ∅ := by
    rw [preimage_sdiff, sdiff_eq_empty]
    exact h
  obtain ⟨j, f, hf⟩ := exists_preimage_eq_empty_of_isProConstructible F hF c hc hst hempty
  exact ⟨j, f, by rwa [preimage_sdiff, sdiff_eq_empty] at hf⟩

/-- Equality of pullbacks of compact opens in a spectral limit is detected at a single
common later stage. -/
theorem exists_preimage_eq_of_isLimit {i : J} {s t : Set (F.obj i)}
    (hso : IsOpen s) (hsc : IsCompact s) (hto : IsOpen t) (htc : IsCompact t)
    (h : c.π.app i ⁻¹' s = c.π.app i ⁻¹' t) :
    ∃ (j : J) (f : j ⟶ i), F.map f ⁻¹' s = F.map f ⁻¹' t := by
  obtain ⟨j, f, hf⟩ := exists_preimage_subset_of_isLimit F hF c hc hso hsc hto htc h.subset
  obtain ⟨k, g, hg⟩ := exists_preimage_subset_of_isLimit F hF c hc hto htc hso hsc h.symm.subset
  obtain ⟨l, a, b, hab⟩ := IsCofiltered.cospan f g
  refine ⟨l, a ≫ f, Subset.antisymm ?_ ?_⟩
  · simpa only [F.map_comp, coe_comp, preimage_comp] using preimage_mono (f := F.map a) hf
  · rw [hab]
    simpa only [F.map_comp, coe_comp, preimage_comp] using preimage_mono (f := F.map b) hg

/-- Finitely many containments between pullbacks of compact opens are detected at one
common stage. This applies in particular to finite lists of union and intersection relations. -/
theorem exists_preimage_subset_of_isLimit_finset {κ : Type*} (K : Finset κ) {i : J}
    (s t : κ → Set (F.obj i)) (hso : ∀ k ∈ K, IsOpen (s k))
    (hsc : ∀ k ∈ K, IsCompact (s k)) (hto : ∀ k ∈ K, IsOpen (t k))
    (htc : ∀ k ∈ K, IsCompact (t k))
    (h : ∀ k ∈ K, c.π.app i ⁻¹' s k ⊆ c.π.app i ⁻¹' t k) :
    ∃ (j : J) (f : j ⟶ i), ∀ k ∈ K, F.map f ⁻¹' s k ⊆ F.map f ⁻¹' t k := by
  classical
  induction K using Finset.induction_on with
  | empty => exact ⟨i, 𝟙 i, by simp⟩
  | @insert k K hk ih =>
    obtain ⟨j, f, hf⟩ := exists_preimage_subset_of_isLimit F hF c hc
      (hso k (by simp)) (hsc k (by simp)) (hto k (by simp)) (htc k (by simp)) (h k (by simp))
    obtain ⟨l, g, hg⟩ := ih (fun k hk ↦ hso k (by simp [hk]))
      (fun k hk ↦ hsc k (by simp [hk])) (fun k hk ↦ hto k (by simp [hk]))
      (fun k hk ↦ htc k (by simp [hk])) (fun k hk ↦ h k (by simp [hk]))
    obtain ⟨m, a, b, hab⟩ := IsCofiltered.cospan f g
    refine ⟨m, a ≫ f, fun r hr ↦ ?_⟩
    rcases Finset.mem_insert.mp hr with rfl | hr
    · simpa only [F.map_comp, coe_comp, preimage_comp] using preimage_mono (f := F.map a) hf
    · rw [hab]
      simpa only [F.map_comp, coe_comp, preimage_comp] using
        preimage_mono (f := F.map b) (hg r hr)

end TopCat
