/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import TauCeti.Topology.GTopology.Basic

/-!
# Continuous maps of G-topologies

A map `f : X → Y` between spaces with G-topologies is continuous if the preimage of every
admissible open is admissible and the preimage of every admissible cover is an admissible cover.
`GTopology.ContinuousMap` bundles such a map with its preimage map on admissible opens. The
preimage map is determined by `f`, so continuous maps are extensional in their underlying
function.

The preimage map preserves finite meets, so it is a representably flat functor between the
preorder categories of admissible opens. Together with the preservation of admissible covers,
this makes it a continuous functor of the associated sites
(`GTopology.ContinuousMap.isContinuous_comapFunctor`). Consequently Mathlib's
`Functor.sheafPushforwardContinuous` provides the direct image of sheaves along a continuous map
of G-topologies, compatibly with identities and composition.

For the G-topologies of ordinary open covers, continuous maps of G-topologies are exactly
continuous maps (`GTopology.ContinuousMap.topologicalEquiv`).

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §9.1.1.
-/

public section

namespace TauCeti

open CategoryTheory Opposite

universe u v u' v' u'' v''

namespace GTopology

variable {X : Type u} {B : Type v} [SemilatticeInf B] [OrderTop B] {ι : B ↪o Set X}
  {Y : Type u'} {B' : Type v'} [SemilatticeInf B'] [OrderTop B'] {ι' : B' ↪o Set Y}
  {Z : Type u''} {B'' : Type v''} [SemilatticeInf B''] [OrderTop B''] {ι'' : B'' ↪o Set Z}

/-- A continuous map of G-topologies: preimages of admissible opens are admissible, recorded by
`comap`, and preimages of admissible covers are admissible covers. -/
structure ContinuousMap (G : GTopology ι) (G' : GTopology ι') where
  /-- The underlying function. -/
  toFun : X → Y
  /-- The admissible open whose underlying set is the preimage of an admissible open. -/
  comap : B' → B
  /-- The preimage map on admissible opens represents preimages of sets. -/
  coe_comap' : ∀ V, ι (comap V) = toFun ⁻¹' ι' V
  /-- Preimages of admissible covers are admissible covers. -/
  covers_comap : ∀ {V S}, G'.Covers V S → G.Covers (comap V) (comap '' S)

namespace ContinuousMap

variable {G : GTopology ι} {G' : GTopology ι'} {G'' : GTopology ι''}

instance : FunLike (G.ContinuousMap G') X Y where
  coe := toFun
  coe_injective := by
    rintro ⟨f, φ, hφ, -⟩ ⟨g, ψ, hψ, -⟩ (rfl : f = g)
    obtain rfl : φ = ψ := funext fun V ↦ ι.injective ((hφ V).trans (hψ V).symm)
    rfl

@[simp]
theorem toFun_eq_coe (f : G.ContinuousMap G') : f.toFun = f := (rfl)

@[simp]
theorem coe_mk (f : X → Y) (φ : B' → B) (hφ) (hS) :
    ⇑(⟨f, φ, hφ, hS⟩ : G.ContinuousMap G') = f := (rfl)

@[ext]
theorem ext {f g : G.ContinuousMap G'} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

@[simp]
theorem coe_comap (f : G.ContinuousMap G') (V : B') : ι (f.comap V) = f ⁻¹' ι' V :=
  f.coe_comap' V

/-- The preimage map on admissible opens is determined by the underlying function. -/
theorem comap_eq_iff (f : G.ContinuousMap G') {U : B} {V : B'} :
    f.comap V = U ↔ f ⁻¹' ι' V = ι U := by
  rw [← f.coe_comap, ι.injective.eq_iff]

@[simp]
theorem comap_inf (f : G.ContinuousMap G') (V W : B') :
    f.comap (V ⊓ W) = f.comap V ⊓ f.comap W := by
  rw [comap_eq_iff, G.map_inf, G'.map_inf, Set.preimage_inter, coe_comap, coe_comap]

@[simp]
theorem comap_top (f : G.ContinuousMap G') : f.comap ⊤ = ⊤ := by
  rw [comap_eq_iff, G.map_top, G'.map_top, Set.preimage_univ]

theorem monotone_comap (f : G.ContinuousMap G') : Monotone f.comap := fun V W hVW ↦ by
  rw [← ι.le_iff_le, coe_comap, coe_comap]
  exact Set.preimage_mono (ι'.le_iff_le.mpr hVW)

/-- The preimage map on admissible opens, as a map preserving finite meets. -/
def comapInfTopHom (f : G.ContinuousMap G') : InfTopHom B' B where
  toFun := f.comap
  map_inf' := f.comap_inf
  map_top' := f.comap_top

@[simp]
theorem coe_comapInfTopHom (f : G.ContinuousMap G') : ⇑f.comapInfTopHom = f.comap := (rfl)

variable (G) in
/-- The identity map is a continuous map of G-topologies. -/
protected def id : G.ContinuousMap G where
  toFun := id
  comap := id
  coe_comap' _ := Set.preimage_id.symm
  covers_comap {V S} h := by rwa [Set.image_id]

@[simp]
theorem coe_id : ⇑(ContinuousMap.id G) = id := (rfl)

@[simp]
theorem comap_id : (ContinuousMap.id G).comap = id := (rfl)

/-- The composition of continuous maps of G-topologies. -/
def comp (g : G'.ContinuousMap G'') (f : G.ContinuousMap G') : G.ContinuousMap G'' where
  toFun := g ∘ f
  comap := f.comap ∘ g.comap
  coe_comap' V := by
    rw [Function.comp_apply, coe_comap, coe_comap, Set.preimage_comp]
  covers_comap h := by
    simpa only [Function.comp_def, Set.image_image] using f.covers_comap (g.covers_comap h)

@[simp]
theorem coe_comp (g : G'.ContinuousMap G'') (f : G.ContinuousMap G') : ⇑(g.comp f) = g ∘ f :=
  (rfl)

@[simp]
theorem comap_comp (g : G'.ContinuousMap G'') (f : G.ContinuousMap G') :
    (g.comp f).comap = f.comap ∘ g.comap := (rfl)

@[simp]
theorem id_comp (f : G.ContinuousMap G') : (ContinuousMap.id G').comp f = f := (rfl)

@[simp]
theorem comp_id (f : G.ContinuousMap G') : f.comp (ContinuousMap.id G) = f := (rfl)

theorem comp_assoc {W : Type*} {B''' : Type*} [SemilatticeInf B'''] [OrderTop B''']
    {ι''' : B''' ↪o Set W} {G''' : GTopology ι'''} (h : G''.ContinuousMap G''')
    (g : G'.ContinuousMap G'') (f : G.ContinuousMap G') :
    (h.comp g).comp f = h.comp (g.comp f) := (rfl)

section Site

/-- The functor of admissible opens induced by a continuous map: an admissible open is sent to
its preimage. -/
def comapFunctor (f : G.ContinuousMap G') : B' ⥤ B :=
  (OrderHom.ofClass f.comapInfTopHom).toFunctor

@[simp]
theorem comapFunctor_obj (f : G.ContinuousMap G') (V : B') :
    f.comapFunctor.obj V = f.comap V := (rfl)

@[simp]
theorem comapFunctor_id : (ContinuousMap.id G).comapFunctor = 𝟭 B := (rfl)

@[simp]
theorem comapFunctor_comp (g : G'.ContinuousMap G'') (f : G.ContinuousMap G') :
    (g.comp f).comapFunctor = g.comapFunctor ⋙ f.comapFunctor := (rfl)

/-- Meet-preserving maps of admissible opens are representably flat, since the preorder of
admissible opens has finite limits computed by finite meets. -/
instance representablyFlat_comapFunctor (f : G.ContinuousMap G') :
    RepresentablyFlat f.comapFunctor :=
  flat_of_preservesFiniteLimits (OrderHom.ofClass f.comapInfTopHom).toFunctor

/-- A continuous map sends covering sieves of admissible opens to covering sieves of their
preimages. -/
theorem coverPreserving_comapFunctor (f : G.ContinuousMap G') :
    CoverPreserving G'.grothendieckTopology G.grothendieckTopology f.comapFunctor where
  cover_preserve {V R} hR := by
    obtain ⟨S, hS, hSR⟩ := (mem_grothendieckTopology_iff G').mp hR
    refine (mem_grothendieckTopology_iff G).mpr ⟨_, f.covers_comap hS, ?_⟩
    intro _ g hg
    obtain ⟨W, hW, rfl⟩ := (coverPresieve_apply _ g).mp hg
    exact ⟨W, homOfLE (G'.subset hS W hW), 𝟙 _, hSR _ _ ((coverPresieve_apply _ _).mpr hW),
      Subsingleton.elim _ _⟩

/-- The preimage functor of a continuous map of G-topologies is a continuous functor of sites,
so it induces the direct image `Functor.sheafPushforwardContinuous` of sheaves. -/
instance isContinuous_comapFunctor (f : G.ContinuousMap G') :
    f.comapFunctor.IsContinuous G'.grothendieckTopology G.grothendieckTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    f.coverPreserving_comapFunctor

end Site

section Topological

open TopologicalSpace

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous map of topological spaces is a continuous map of the G-topologies of ordinary
open covers. -/
def ofContinuousMap (f : C(X, Y)) : (topological X).ContinuousMap (topological Y) where
  toFun := f
  comap := Opens.comap f
  coe_comap' _ := by simp only [opensEmbedding_apply, Opens.coe_comap]
  covers_comap {V S} h := by
    rw [topological_covers_iff] at h ⊢
    simp only [Set.sUnion_image, Set.biUnion_image, Opens.coe_comap, ← h, Set.preimage_iUnion]

@[simp]
theorem coe_ofContinuousMap (f : C(X, Y)) : ⇑(ofContinuousMap f) = f := (rfl)

@[simp]
theorem comap_ofContinuousMap (f : C(X, Y)) : (ofContinuousMap f).comap = Opens.comap f := (rfl)

@[simp]
theorem coe_comap_topological (f : (topological X).ContinuousMap (topological Y)) (V : Opens Y) :
    (f.comap V : Set X) = f ⁻¹' V := by
  rw [← opensEmbedding_apply, coe_comap, opensEmbedding_apply]

/-- For ordinary open covers, the preimage functor is Mathlib's `Opens.map`, so the direct image
of sheaves recovers the usual topological pushforward. -/
theorem comapFunctor_ofContinuousMap {X₁ X₂ : Type u} [TopologicalSpace X₁]
    [TopologicalSpace X₂] (f : C(X₁, X₂)) :
    (ofContinuousMap f).comapFunctor = Opens.map (TopCat.ofHom f) :=
  CategoryTheory.Functor.ext (fun _ ↦ (rfl)) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- A continuous map of the G-topologies of ordinary open covers is continuous. -/
theorem continuous (f : (topological X).ContinuousMap (topological Y)) : Continuous f :=
  continuous_def.mpr fun V hV ↦ by
    simpa using (f.comap ⟨V, hV⟩).isOpen

/-- Continuous maps of the G-topologies of ordinary open covers are exactly continuous maps. -/
def topologicalEquiv : C(X, Y) ≃ (topological X).ContinuousMap (topological Y) where
  toFun := ofContinuousMap
  invFun f := ⟨f, f.continuous⟩
  left_inv _ := (rfl)
  right_inv _ := ext fun _ ↦ (rfl)

@[simp]
theorem coe_topologicalEquiv (f : C(X, Y)) : ⇑(topologicalEquiv f) = f := (rfl)

@[simp]
theorem coe_topologicalEquiv_symm (f : (topological X).ContinuousMap (topological Y)) :
    ⇑(topologicalEquiv.symm f) = f := (rfl)

end Topological

end ContinuousMap

end GTopology

end TauCeti
