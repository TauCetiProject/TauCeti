/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Konig
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Finite-stage emptiness in compact Hausdorff limits

If a closed subset of one stage has empty inverse image in a cofiltered limit of compact
Hausdorff spaces, its inverse image is already empty after a transition map. No surjectivity
is required. This is the compactness argument used to detect finite-stage relations in inverse
limits, including spectral limits after passage to constructible topologies.

## References

* The Stacks Project, Tag 0A2Y, Lemma 5.24.4.
-/

public section

open CategoryTheory CategoryTheory.Limits Set Topology

namespace TopCat

universe v u

variable {J : Type v} [SmallCategory J] [IsCofiltered J]
  (F : J ⥤ TopCat.{max v u}) [∀ j, CompactSpace (F.obj j)] [∀ j, T2Space (F.obj j)]
  (c : Cone F) (hc : IsLimit c)

include hc

/-- A closed subset of a compact Hausdorff stage that misses the limit already misses a
later stage. The transition maps need not be surjective. -/
theorem exists_preimage_eq_empty_of_isLimit {i : J} {s : Set (F.obj i)} (hs : IsClosed s)
    (h : c.π.app i ⁻¹' s = ∅) : ∃ (j : J) (f : j ⟶ i), F.map f ⁻¹' s = ∅ := by
  classical
  by_contra! hn
  -- Restrict to the compact closed preimages over the category of arrows into `i`.
  let G : Over i ⥤ TopCat.{max v u} :=
    { obj := fun j ↦ TopCat.of (F.map j.hom ⁻¹' s)
      map := fun {j k} a ↦ TopCat.ofHom
        ⟨fun x ↦ ⟨F.map a.left x.1, by
          simpa only [mem_preimage, ← ConcreteCategory.comp_apply, ← F.map_comp,
            Over.w a] using x.2⟩,
          by fun_prop⟩
      map_id := by intro j; ext x; simp
      map_comp := by intro j k l a b; ext x; simp }
  have : ∀ j, CompactSpace (G.obj j) := fun j ↦
    isCompact_iff_compactSpace.mp (hs.preimage (F.map j.hom).hom.continuous).isCompact
  have : ∀ j, T2Space (G.obj j) := fun j ↦ inferInstanceAs (T2Space (F.map j.hom ⁻¹' s))
  have : ∀ j, Nonempty (G.obj j) := fun j ↦ by
    obtain ⟨z, hz⟩ := hn j.left j.hom
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨x⟩ := nonempty_limitCone_of_compact_t2_cofiltered_system G
  -- The forgetful functor `Over i → J` is initial, so the compatible family gives a limit point.
  let d : Cone (Over.forget i ⋙ F) :=
    { pt := TopCat.of PUnit
      π :=
        { app := fun j ↦ TopCat.ofHom ⟨fun _ ↦ (x.1 j).1, continuous_const⟩
          naturality := by
            intro j k a
            ext
            exact (congrArg Subtype.val (x.2 a)).symm } }
  let hc' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  let y := hc'.lift d PUnit.unit
  have hy : c.π.app i y ∈ s := by
    have he : c.π.app i y = (x.1 (Over.mk (𝟙 i))).1 :=
      ConcreteCategory.congr_hom (hc'.fac d (Over.mk (𝟙 i))) PUnit.unit
    rw [he]
    simpa using (x.1 (Over.mk (𝟙 i))).2
  have hm : y ∈ c.π.app i ⁻¹' s := hy
  rw [h] at hm
  exact hm

end TopCat
