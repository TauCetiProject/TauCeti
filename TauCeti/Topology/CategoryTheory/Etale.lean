/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.IsLocalHomeomorph
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Finite local arrow charts for proper étale presentations

Give the objects and the total arrows of a quiver their own topologies. If the source is a
local homeomorphism and the source-target map is proper, there are finitely many arrows between
any two objects. In particular, the isotropy of a groupoid with these properties is finite.

If target is also a local homeomorphism and the arrow space is Hausdorff, the arrows at an
object admit pairwise disjoint open bisection neighborhoods. After shrinking the object
neighborhood, these bisections contain every arrow with both endpoints in that neighborhood.
This is the finite retained-arrow neighborhood needed to reconstruct local finite actions:
different isotropy arrows remain separate, even if their induced object maps coincide.
The result does not yet assert the multiplication identities of a local action.

No new groupoid carrier or topology on individual hom types is introduced. The results apply
to native categorical groupoids through `Quiver.Total`, and only use the displayed topological
hypotheses; composition and inversion are not needed for these neighborhood statements.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
* A. Adem, J. Leida and Y. Ruan, *Orbifolds and stringy topology*, Chapter 1.
-/

public section

open Set Topology

namespace TauCeti

variable {C : Type*} [Quiver C] [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]

/-- A proper source-target map and a locally homeomorphic source imply that each set of
arrows with prescribed endpoints is finite. No separation hypothesis is needed. -/
theorem finite_total_arrows_of_proper_source_target
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) (x y : C) :
    Set.Finite {a : Quiver.Total C | a.left = x ∧ a.right = y} := by
  have hc : IsCompact {a : Quiver.Total C | a.left = x ∧ a.right = y} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
      hp.isCompact_preimage (isCompact_singleton (x := (x, y)))
  apply hc.finite
  apply hs.isLocalHomeomorphOn.isDiscrete_of_image
  exact Set.subsingleton_singleton.isDiscrete.mono fun _ ⟨a, ha, h⟩ ↦ h ▸ ha.1

/-- Every hom type is finite in a quiver with proper source-target map and locally
homeomorphic source. Applied with equal endpoints, this gives finiteness of isotropy. -/
theorem finite_hom_of_proper_source_target
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C)) (x y : C) :
    Finite (x ⟶ y) := by
  have := (finite_total_arrows_of_proper_source_target hp hs x y).to_subtype
  exact Finite.of_injective (fun f : x ⟶ y ↦
    (⟨⟨x, y, f⟩, rfl, rfl⟩ : {a : Quiver.Total C // a.left = x ∧ a.right = y}))
    (by intro f g h; simpa using congrArg Subtype.val h)

/-- Near an object of a Hausdorff proper étale presentation, all arrows lie in finitely many
pairwise disjoint open bisections, one through each isotropy arrow. The bisections retain
actual arrows, not just the germs of the corresponding object maps. -/
theorem exists_disjoint_bisections_of_proper_source_target [T2Space (Quiver.Total C)]
    (hp : IsProperMap (fun a : Quiver.Total C ↦ (a.left, a.right)))
    (hs : IsLocalHomeomorph (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsLocalHomeomorph (Quiver.Total.right : Quiver.Total C → C)) (x : C) :
    ∃ (U : Set C) (W : (x ⟶ x) → Set (Quiver.Total C)),
      IsOpen U ∧ x ∈ U ∧
      (∀ f, IsOpen (W f) ∧ (⟨x, x, f⟩ : Quiver.Total C) ∈ W f ∧
        IsOpenEmbedding ((W f).domRestrict Quiver.Total.left) ∧
        IsOpenEmbedding ((W f).domRestrict Quiver.Total.right)) ∧
      Pairwise (fun f g ↦ Disjoint (W f) (W g)) ∧
      ∀ a : Quiver.Total C, a.left ∈ U → a.right ∈ U → ∃! f, a ∈ W f := by
  classical
  let A := {a : Quiver.Total C | a.left = x ∧ a.right = x}
  have hA : A.Finite := finite_total_arrows_of_proper_source_target hp hs x x
  obtain ⟨O, hO, hdisj⟩ := hA.t2_separation
  have hb (a : Quiver.Total C) : ∃ W : Set (Quiver.Total C),
      IsOpen W ∧ a ∈ W ∧ W ⊆ O a ∧
      IsOpenEmbedding (W.domRestrict Quiver.Total.left) ∧
      IsOpenEmbedding (W.domRestrict Quiver.Total.right) := by
    obtain ⟨S, hS, hsS⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp hs a
    obtain ⟨T, hT, htT⟩ := isLocalHomeomorph_iff_isOpenEmbedding_restrict.mp ht a
    obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp
      (Filter.inter_mem (Filter.inter_mem hS hT) ((hO a).2.mem_nhds (hO a).1))
    refine ⟨W, hW, haW, fun b hb ↦ (hWsub hb).2, ?_, ?_⟩
    · exact hsS.comp (.inclusion (fun b hb ↦ (hWsub hb).1.1)
        (hW.preimage continuous_subtype_val))
    · exact htT.comp (.inclusion (fun b hb ↦ (hWsub hb).1.2)
        (hW.preimage continuous_subtype_val))
  choose B hBopen hBmem hBsub hBs hBt using hb
  let W (f : x ⟶ x) := B ⟨x, x, f⟩
  have hcover : ∀ a : Quiver.Total C, a.left = x → a.right = x → a ∈ ⋃ f, W f := by
    rintro ⟨a, b, f⟩ ha hb
    dsimp only at ha hb
    subst a b
    exact mem_iUnion.mpr ⟨f, hBmem _⟩
  have hpair : Pairwise (fun f g ↦ Disjoint (W f) (W g)) := by
    intro f g hfg
    apply (hdisj (by exact ⟨rfl, rfl⟩) (by exact ⟨rfl, rfl⟩) ?_).mono (hBsub _) (hBsub _)
    intro h
    exact hfg (by simpa using h)
  -- Closedness excludes every arrow outside these bisections near the whole isotropy fiber.
  have hnear := hp.isClosedMap.eventually_nhds_fiber (p := fun a ↦ a ∈ ⋃ f, W f) (x, x)
    (by
      intro a ha
      exact (isOpen_iUnion fun f ↦ hBopen ⟨x, x, f⟩).mem_nhds
        (hcover a (Prod.mk.inj ha).1 (Prod.mk.inj ha).2))
  obtain ⟨U, V, hU, hxU, hV, hxV, hUV⟩ := mem_nhds_prod_iff'.mp hnear
  refine ⟨U ∩ V, W, hU.inter hV, ⟨hxU, hxV⟩,
    fun f ↦ ⟨hBopen _, hBmem _, hBs _, hBt _⟩, hpair, ?_⟩
  intro a ha hb
  obtain ⟨f, hf⟩ := mem_iUnion.mp (hUV ⟨ha.1, hb.2⟩ a rfl)
  exact ⟨f, hf, fun g hg ↦ by
    by_contra hgf
    exact Set.disjoint_left.mp (hpair hgf) hg hf⟩

end TauCeti
