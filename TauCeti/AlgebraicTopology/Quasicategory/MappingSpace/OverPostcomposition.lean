/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Postcomposition

/-!
# Composition triangles over a specified base edge

For a simplicial set `X` over the nerve of a category, fix an edge `g : y ⟶ z` of `X` and
an edge `e : p x ⟶ p y` of the base. The composition triangles with last edge `g` and first
edge lying over `e` form `SSet.rightMappingSpaceOver.postcompSpace g e`. Restriction to the
first edge is a trivial fibration when `X` is a quasicategory. Restriction to the long edge
lands over the composite of `e` and `p g`.

This span describes postcomposition on spaces of maps over an edge without fixing a choice
of composition triangles. The existing `SSet.rightMappingSpaceOver.postcomp` comes from a
section of its source projection, and every other section gives a homotopic map within the
same relative mapping space. This permits comparisons of products of postcomposition maps,
such as the mapping-space Segal maps of an infinity-operad, using compatible triangle choices.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.2 and Proposition 1.2.9.3.
* J. Lurie, *Higher Algebra*, Definition 2.1.1.10, for the mapping-space Segal maps.
-/

public section

universe u

open CategoryTheory Limits MorphismProperty Simplicial

namespace SSet.rightMappingSpaceOver

variable {X Y S : SSet.{u}} {p : X ⟶ S} {x y z : X _⦋0⦌}

/-- Composition triangles with last edge `g` whose first edge lies over `e`. -/
noncomputable def postcompSpace (g : Edge y z) (e : Edge (p.app _ x) (p.app _ y)) :
    (rightMappingSpace.postcompSpace x g : SSet.{u}).Subcomplex :=
  (rightMappingSpaceOver p e).preimage (rightMappingSpace.postcompSpace.src x g)

/-- A composition triangle belongs to the relative composition space precisely when its
first edge belongs to the mapping space over `e`. -/
@[simp]
lemma mem_postcompSpace_iff (g : Edge y z) (e : Edge (p.app _ x) (p.app _ y))
    {n : SimplexCategoryᵒᵖ} (v : (rightMappingSpace.postcompSpace x g : SSet.{u}).obj n) :
    v ∈ (postcompSpace g e).obj n ↔
      (rightMappingSpace.postcompSpace.src x g).app n v ∈ (rightMappingSpaceOver p e).obj n :=
  Iff.rfl

namespace postcompSpace

variable (g : Edge y z) (e : Edge (p.app _ x) (p.app _ y))

/-- Restriction of a composition triangle over `e` to its first edge. -/
noncomputable def src :
    (postcompSpace g e : SSet.{u}) ⟶ (rightMappingSpaceOver p e : SSet.{u}) :=
  Subcomplex.fromPreimage _ _

@[reassoc (attr := simp)]
lemma src_ι : src g e ≫ (rightMappingSpaceOver p e).ι =
    (postcompSpace g e).ι ≫ rightMappingSpace.postcompSpace.src x g :=
  Subcomplex.fromPreimage_ι _ _

/-- Source restriction on composition triangles over `e` is a trivial fibration. -/
theorem rlp_src [Quasicategory X] : (monomorphisms SSet.{u}).rlp (src g e) := by
  intro A B i hi
  have := rightMappingSpace.postcompSpace.rlp_src x g i hi
  exact inferInstanceAs (HasLiftingProperty i (Subcomplex.fromPreimage _ _))

/-- A family of composition triangles whose first edges lie over `e` factors through the
relative composition space. -/
noncomputable def lift {A : SSet.{u}}
    (a : A ⟶ (rightMappingSpaceOver p e : SSet.{u}))
    (b : A ⟶ (rightMappingSpace.postcompSpace x g : SSet.{u}))
    (h : b ≫ rightMappingSpace.postcompSpace.src x g = a ≫ (rightMappingSpaceOver p e).ι) :
    A ⟶ (postcompSpace g e : SSet.{u}) :=
  Subcomplex.lift b (by
    rw [postcompSpace, ← Subcomplex.image_le_iff, ← Subcomplex.range_comp, h]
    simpa only [Subcomplex.range_comp, Subfunctor.range_ι] using
      (Subcomplex.image_le_range (Subcomplex.range a) (rightMappingSpaceOver p e).ι))

@[reassoc (attr := simp)]
lemma lift_ι {A : SSet.{u}}
    (a : A ⟶ (rightMappingSpaceOver p e : SSet.{u}))
    (b : A ⟶ (rightMappingSpace.postcompSpace x g : SSet.{u}))
    (h : b ≫ rightMappingSpace.postcompSpace.src x g = a ≫ (rightMappingSpaceOver p e).ι) :
    lift g e a b h ≫ (postcompSpace g e).ι = b :=
  Subcomplex.lift_ι _ _

@[reassoc (attr := simp)]
lemma lift_src {A : SSet.{u}}
    (a : A ⟶ (rightMappingSpaceOver p e : SSet.{u}))
    (b : A ⟶ (rightMappingSpace.postcompSpace x g : SSet.{u}))
    (h : b ≫ rightMappingSpace.postcompSpace.src x g = a ≫ (rightMappingSpaceOver p e).ι) :
    lift g e a b h ≫ src g e = a := by
  rw [← cancel_mono (rightMappingSpaceOver p e).ι]
  simp [h]

/-- A map over the base sends relative composition triangles to their image triangles. -/
noncomputable def map {q : Y ⟶ S} (F : X ⟶ Y) (hF : F ≫ q = p)
    {eF : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ y))} (he : eF.edge = e.edge) :
    (postcompSpace g e : SSet.{u}) ⟶ (postcompSpace (g.map F) eF : SSet.{u}) :=
  lift (g.map F) eF (src g e ≫ rightMappingSpaceOver.map F hF he)
    ((postcompSpace g e).ι ≫ rightMappingSpace.postcompSpace.map x g F)
    (by simp only [Category.assoc, rightMappingSpace.postcompSpace.map_src,
      rightMappingSpaceOver.map_ι, src_ι_assoc])

@[reassoc (attr := simp)]
lemma map_ι {q : Y ⟶ S} (F : X ⟶ Y) (hF : F ≫ q = p)
    {eF : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ y))} (he : eF.edge = e.edge) :
    map g e F hF he ≫ (postcompSpace (g.map F) eF).ι =
      (postcompSpace g e).ι ≫ rightMappingSpace.postcompSpace.map x g F :=
  lift_ι _ _ _ _ _

@[reassoc (attr := simp)]
lemma map_src {q : Y ⟶ S} (F : X ⟶ Y) (hF : F ≫ q = p)
    {eF : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ y))} (he : eF.edge = e.edge) :
    map g e F hF he ≫ src (g.map F) eF = src g e ≫ rightMappingSpaceOver.map F hF he :=
  lift_src _ _ _ _ _

/-- The identity map acts identically on relative composition triangles. -/
@[simp]
lemma map_id : dsimp% map g e (𝟙 X) (Category.id_comp p) rfl = 𝟙 _ := by
  -- The images of vertices and edges under the identity have the same endpoints.
  apply (cancel_mono (postcompSpace g e).ι).1
  erw [map_ι (q := p) g e (𝟙 X) (Category.id_comp p) (eF := e) rfl,
    rightMappingSpace.postcompSpace.map_id, Category.comp_id]

/-- Applying two maps over the base successively agrees with applying their composite. -/
lemma map_comp {Z : SSet.{u}} {q : Y ⟶ S} {r : Z ⟶ S}
    (F : X ⟶ Y) (hF : F ≫ q = p) (G : Y ⟶ Z) (hG : G ≫ r = q)
    {eF : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ y))} (he : eF.edge = e.edge)
    {eG : Edge (r.app _ (G.app _ (F.app _ x))) (r.app _ (G.app _ (F.app _ y)))}
    (heG : eG.edge = eF.edge) :
    dsimp% map g e (F ≫ G) (by rw [Category.assoc, hG, hF]) (heG.trans he) =
      map g e F hF he ≫ map (g.map F) eF G hG heG := by
  -- The iterated image of the last edge has the same endpoints as its composite image.
  apply (cancel_mono (postcompSpace (g.map (F ≫ G)) eG).ι).1
  erw [map_ι (q := r) g e (F ≫ G) (by rw [Category.assoc, hG, hF])
      (eF := eG) (heG.trans he), Category.assoc,
    map_ι (g.map F) eF G hG heG, map_ι_assoc g e F hF he]
  exact congrArg ((postcompSpace g e).ι ≫ ·)
    (rightMappingSpace.postcompSpace.map_comp x g F G)

end postcompSpace

section Nerve

variable {C : Type u} [SmallCategory C] {p : X ⟶ nerve C}

namespace postcompSpace

variable (g : Edge y z) (e : Edge (p.app _ x) (p.app _ y))

/-- Restriction to the long edge of a composition triangle over `e`, landing over a specified
composite `e'` of `e` and `p g`. -/
noncomputable def tgt {e' : Edge (p.app _ x) (p.app _ z)}
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map p) = nerve.homEquiv e') :
    (postcompSpace g e : SSet.{u}) ⟶ (rightMappingSpaceOver p e' : SSet.{u}) :=
  Subcomplex.lift ((postcompSpace g e).ι ≫ rightMappingSpace.postcompSpace.tgt x g)
    ((range_le_iff _ _).2 fun v ↦ by
      have hc := nerve.homEquiv_comp
        ((rightMappingSpace.postcompSpace.obj₀Equiv x g v.val).2.2.map p)
      simp only [← rightMappingSpace.postcompSpace.obj₀Equiv_src_app,
        ← rightMappingSpace.postcompSpace.obj₀Equiv_tgt_app] at hc
      rw [(mem_obj₀_iff _ _).1 v.property] at hc
      apply nerve.homEquiv.injective
      rw [← h]
      exact hc.symm)

@[reassoc (attr := simp)]
lemma tgt_ι {e' : Edge (p.app _ x) (p.app _ z)}
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map p) = nerve.homEquiv e') :
    tgt g e h ≫ (rightMappingSpaceOver p e').ι =
      (postcompSpace g e).ι ≫ rightMappingSpace.postcompSpace.tgt x g :=
  Subcomplex.lift_ι _ _

/-- Long-edge restriction is natural for maps over the base. -/
@[reassoc (attr := simp)]
lemma map_tgt {q : Y ⟶ nerve C} (F : X ⟶ Y) (hF : F ≫ q = p)
    {eF : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ y))} (he : eF.edge = e.edge)
    {e' : Edge (p.app _ x) (p.app _ z)}
    {eF' : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ z))} (he' : eF'.edge = e'.edge)
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map p) = nerve.homEquiv e')
    (h' : nerve.homEquiv eF ≫ nerve.homEquiv ((g.map F).map q) = nerve.homEquiv eF') :
    map g e F hF he ≫ tgt (g.map F) eF h' =
      tgt g e h ≫ rightMappingSpaceOver.map F hF he' := by
  rw [← cancel_mono (rightMappingSpaceOver q eF').ι]
  simp only [Category.assoc, tgt_ι, map_ι_assoc, rightMappingSpace.postcompSpace.map_tgt,
    rightMappingSpaceOver.map_ι, tgt_ι_assoc]

end postcompSpace

/-- Postcomposition over a base edge is obtained from a section of relative source restriction. -/
theorem exists_section_postcomp [Quasicategory X] (g : Edge y z)
    {e : Edge (p.app _ x) (p.app _ y)} {e' : Edge (p.app _ x) (p.app _ z)}
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map p) = nerve.homEquiv e') :
    ∃ s : (rightMappingSpaceOver p e : SSet.{u}) ⟶ (postcompSpace g e : SSet.{u}),
      s ≫ postcompSpace.src g e = 𝟙 _ ∧ s ≫ postcompSpace.tgt g e h = postcomp g h := by
  obtain ⟨s, hs, ht⟩ := rightMappingSpace.exists_section_postcomp (x := x) g
  let s' := postcompSpace.lift g e (𝟙 _) ((rightMappingSpaceOver p e).ι ≫ s) (by simp [hs])
  refine ⟨s', by simp [s'], ?_⟩
  rw [← cancel_mono (rightMappingSpaceOver p e').ι]
  simp [s', ht]

/-- Every section of relative source restriction gives the same postcomposition map up to
homotopy within the relative mapping space. -/
theorem exists_homotopy_postcomp [Quasicategory X] (g : Edge y z)
    {e : Edge (p.app _ x) (p.app _ y)} {e' : Edge (p.app _ x) (p.app _ z)}
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map p) = nerve.homEquiv e')
    (s : (rightMappingSpaceOver p e : SSet.{u}) ⟶ (postcompSpace g e : SSet.{u}))
    (hs : s ≫ postcompSpace.src g e = 𝟙 _) :
    Nonempty (Homotopy (s ≫ postcompSpace.tgt g e h) (postcomp g h)) := by
  obtain ⟨s', hs', ht'⟩ := exists_section_postcomp g h
  obtain ⟨H, -⟩ := exists_homotopy_of_rlp_monomorphisms (postcompSpace.rlp_src g e) s s'
    (by rw [hs, hs'])
  rw [← ht']
  exact ⟨H.postcomp _⟩

/-- Postcomposition on mapping spaces over an edge commutes up to homotopy with a map over
the base. The homotopy stays in the mapping space over the specified composite edge. -/
theorem exists_homotopy_map_postcomp [Quasicategory X] [Quasicategory Y]
    {q : Y ⟶ nerve C} (F : X ⟶ Y) (hF : F ≫ q = p) (g : Edge y z)
    {e : Edge (p.app _ x) (p.app _ y)} {e' : Edge (p.app _ x) (p.app _ z)}
    {eF : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ y))} (he : eF.edge = e.edge)
    {eF' : Edge (q.app _ (F.app _ x)) (q.app _ (F.app _ z))} (he' : eF'.edge = e'.edge)
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map p) = nerve.homEquiv e')
    (h' : nerve.homEquiv eF ≫ nerve.homEquiv ((g.map F).map q) = nerve.homEquiv eF') :
    Nonempty (Homotopy (postcomp g h ≫ map F hF he')
      (map F hF he ≫ postcomp (g.map F) h')) := by
  obtain ⟨s, hs, ht⟩ := exists_section_postcomp g h
  obtain ⟨s', hs', ht'⟩ := exists_section_postcomp (g.map F) h'
  obtain ⟨H, -⟩ := exists_homotopy_of_rlp_monomorphisms
    (postcompSpace.rlp_src (g.map F) eF)
    (s ≫ postcompSpace.map g e F hF he) (map F hF he ≫ s') (by
      simp only [Category.assoc, postcompSpace.map_src, reassoc_of% hs, hs',
        Category.comp_id])
  have hl : (s ≫ postcompSpace.map g e F hF he) ≫ postcompSpace.tgt (g.map F) eF h' =
      postcomp g h ≫ map F hF he' := by
    simp only [Category.assoc, postcompSpace.map_tgt g e F hF he he' h h', reassoc_of% ht]
  have hr : (map F hF he ≫ s') ≫ postcompSpace.tgt (g.map F) eF h' =
      map F hF he ≫ postcomp (g.map F) h' := by rw [Category.assoc, ht']
  rw [← hl, ← hr]
  exact ⟨H.postcomp _⟩

end Nerve

end SSet.rightMappingSpaceOver
