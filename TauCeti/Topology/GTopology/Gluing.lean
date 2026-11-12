/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.GTopology.Restrict
import Mathlib.Data.Set.UnionLift

/-!
# Gluing continuous maps of G-topologies

For a saturated G-topology, admissibility of a covering family can be checked on an
admissible cover. Consequently a function is continuous if its restrictions to the members
of an admissible cover are continuous. Compatible continuous maps on such a cover glue to a
unique continuous map. Only the source G-topology must be saturated.

These are the local-to-global statements needed to paste maps of spaces equipped with
G-topologies. The underlying function is glued by Mathlib's `Set.liftCover`; its preimages
are admissible by (G1), and its preservation of covers follows from (G2).

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §§9.1.1–9.1.3.
-/

public section

namespace TauCeti.GTopology

universe u v u' v'

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B] {ι : B ↪o Set X}
  {G : GTopology ι}

namespace ContinuousMap

variable {Y : Type u'} {B' : Type v'} [SemilatticeInf B'] [OrderTop B']
  {ι' : B' ↪o Set Y} {G' : GTopology ι'}

/-- Continuity of a function from a saturated G-topology is local on an admissible cover
of the source. The local maps are defined on the induced G-topologies. -/
theorem exists_iff_restrict (hG : G.Saturated) {C : Set B} (hC : G.Covers ⊤ C)
    (f : X → Y) :
    (∃ g : G.ContinuousMap G', ∀ x, g x = f x) ↔
      ∀ U : C, ∃ g : (G.restrict U.1).ContinuousMap G', ∀ x, g x = f x := by
  constructor
  · rintro ⟨g, hg⟩ U
    exact ⟨g.comp (G.restrictInclusion U.1), fun x ↦ by simpa using hg x⟩
  · intro hlocal
    classical
    choose g hg using hlocal
    -- First construct the global preimages using local admissibility (G1).
    have hpre (V : B') : f ⁻¹' ι' V ∈ Set.range ι := by
      apply hG.mem_range_of_covers hC _ (by rw [G.map_top]; exact Set.subset_univ _)
      intro U hU
      refine ⟨((g ⟨U, hU⟩).comap V : B), ?_⟩
      rw [← image_restrictEmbedding, coe_comap]
      ext x
      simp [hg, and_comm]
    choose φ hφ using hpre
    -- Local preimages represent intersections of global preimages with the cover.
    have hφlocal (V : B') (U : C) :
        φ V ⊓ U.1 = ((g U).comap V : B) := by
      apply ι.injective
      rw [G.map_inf, hφ, ← image_restrictEmbedding, coe_comap]
      ext x
      simp [hg, and_comm]
    refine ⟨⟨f, φ, hφ, fun {V S} hS ↦ ?_⟩, fun _ ↦ rfl⟩
    apply (hG.covers_iff_restriction hC le_top).mpr
    refine ⟨?_, fun U hU ↦ ?_⟩
    · rintro _ ⟨W, hW, rfl⟩
      apply ι.le_iff_le.mp
      rw [hφ, hφ]
      exact Set.preimage_mono (ι'.monotone (G'.subset hS W hW))
    · have h := (g ⟨U, hU⟩).covers_comap hS
      rw [restrict_covers_iff, Set.image_image] at h
      simpa only [← hφlocal, Set.image_image, Function.comp_def] using h

/-- Compatible continuous maps on an admissible cover of a saturated G-topology glue
uniquely. Agreement is required at every point of each overlap; the target need not be
saturated or separated. -/
theorem existsUnique_glue (hG : G.Saturated) {C : Set B} (hC : G.Covers ⊤ C)
    (f : ∀ U : C, (G.restrict U.1).ContinuousMap G')
    (hf : ∀ (U V : C) (x : X) (hU : x ∈ ι U.1) (hV : x ∈ ι V.1),
      f U ⟨x, hU⟩ = f V ⟨x, hV⟩) :
    ∃! g : G.ContinuousMap G', ∀ (U : C) (x : ι U.1), g x = f U x := by
  have hcover : ⋃ U : C, ι U.1 = Set.univ := by
    simpa only [Set.iUnion_coe_set, Set.sUnion_image, G.map_top] using G.union_eq hC
  let F := Set.liftCover (fun U : C ↦ ι U.1) (fun U ↦ ⇑(f U)) hf hcover
  have hF (U : C) (x : ι U.1) : F x = f U x := by
    dsimp only [F]
    exact Set.liftCover_coe (S := fun U : C ↦ ι U.1) (f := fun U ↦ ⇑(f U))
      (hf := hf) (hS := hcover) x
  obtain ⟨g, hg⟩ := (exists_iff_restrict hG hC F).mpr fun U ↦
    ⟨f U, fun x ↦ (hF U x).symm⟩
  refine ⟨g, fun U x ↦ (hg x).trans (hF U x), fun g' hg' ↦ ?_⟩
  apply ext
  intro x
  have hx : x ∈ ⋃ U : C, ι U.1 := hcover ▸ Set.mem_univ x
  obtain ⟨U, hU⟩ := Set.mem_iUnion.mp hx
  exact (hg' U ⟨x, hU⟩).trans ((hF U ⟨x, hU⟩).symm.trans (hg x).symm)

end ContinuousMap

end TauCeti.GTopology
