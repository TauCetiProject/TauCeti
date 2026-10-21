/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category
public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Basic

/-!
# Morphisms and isomorphisms of prestable maps

Fix a target `q : V ⟶ S`. A morphism of prestable maps `F ⟶ G` to `q` is a morphism of their
pointed source curves over `S` that commutes with the maps to `V`. With these morphisms the
prestable maps to `q` with `n` markings form a category. Its isomorphisms are the isomorphisms of
pointed source curves commuting with the maps, and the automorphism group of a prestable map is
the ordinary group `CategoryTheory.Aut F`. A morphism of prestable maps preserves evaluations.

Forgetting the map is a faithful functor to pointed prestable families that reflects
isomorphisms, so a morphism of prestable maps is an isomorphism exactly when its map of total
spaces is one. Automorphisms of a prestable map are thereby identified with the automorphisms of
its pointed source curve that commute with the map.

Postcomposition with a morphism of targets over `S`, base change along `g : T ⟶ S` and
reindexing the markings are functors. Postcomposition is faithful, it is full for a monomorphism
of targets, and it is an equivalence of categories for an isomorphism of targets: an isomorphism
of targets over `S` transports prestable maps and their isomorphisms.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap.Hom`: morphisms of prestable maps to a fixed target.
* `TauCeti.AlgebraicGeometry.PrestableMap.toCurve`: the functor forgetting the map.
* `TauCeti.AlgebraicGeometry.PrestableMap.isoMk`: an isomorphism of prestable maps from an
  isomorphism of pointed source curves commuting with the maps.
* `TauCeti.AlgebraicGeometry.PrestableMap.autToCurve`: the injective homomorphism from the
  automorphism group of a prestable map to that of its pointed source curve.
* `TauCeti.AlgebraicGeometry.PrestableMap.postcompFunctor`: postcomposition as a functor.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackFunctor`: base change as a functor.
* `TauCeti.AlgebraicGeometry.PrestableMap.reindexFunctor`: reindexing as a functor.

## Main results

* `TauCeti.AlgebraicGeometry.PrestableMap.ev_eq_of_hom`: morphisms of prestable maps preserve
  evaluations.
* `TauCeti.AlgebraicGeometry.PrestableMap.isIso_iff_isIso_hom`: a morphism of prestable maps is
  an isomorphism exactly when its map of total spaces is one.
* `TauCeti.AlgebraicGeometry.PrestableMap.mem_range_autToCurve_iff`: an automorphism of the
  pointed source curve comes from the prestable map exactly when it commutes with the map.
* The instances `(postcompFunctor h hh).Full` for a monomorphism `h` and
  `(postcompFunctor h hh).IsEquivalence` for an isomorphism `h`.

## Implementation notes

The morphisms, the category instance, the isomorphism criterion and the automorphism groups
follow the category API for pointed prestable families in
`TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Category`, to which they reduce.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, Definition 1.1 and Section 2, for prestable maps to a
  target over an arbitrary base and their isomorphisms.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  Proc. Sympos. Pure Math. 62 (1997), Part 2, 45–96, Section 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V W S T : Scheme.{u}} {q : V ⟶ S} {m n : ℕ}

/-- A **morphism of prestable maps** to the target `q`: a morphism of pointed source curves over
`S` that commutes with the maps to the target. -/
@[ext]
structure Hom (F G : PrestableMap q n) where
  /-- The morphism of pointed source curves. -/
  curve : F.curve ⟶ G.curve
  /-- The morphism of source curves commutes with the maps to the target. -/
  hom_comp_map : curve.hom ≫ G.map = F.map

attribute [reassoc (attr := simp)] Hom.hom_comp_map

/-- The prestable maps to `q` with `n` markings form a category. -/
instance category : Category (PrestableMap q n) where
  Hom := Hom
  id F := ⟨𝟙 F.curve, by simp⟩
  comp f g := ⟨f.curve ≫ g.curve, by simp⟩
  id_comp f := Hom.ext (Category.id_comp f.curve)
  comp_id f := Hom.ext (Category.comp_id f.curve)
  assoc f g h := Hom.ext (Category.assoc f.curve g.curve h.curve)

variable {F G H : PrestableMap q n}

/-- Morphisms of prestable maps are determined by their morphisms of source curves. -/
@[ext]
theorem hom_ext {f g : F ⟶ G} (h : f.curve = g.curve) : f = g :=
  Hom.ext h

@[simp]
theorem id_curve (F : PrestableMap q n) : Hom.curve (𝟙 F) = 𝟙 F.curve :=
  rfl

@[simp, reassoc]
theorem comp_curve (f : F ⟶ G) (g : G ⟶ H) : (f ≫ g).curve = f.curve ≫ g.curve :=
  rfl

/-- A morphism of prestable maps preserves the evaluation at every marking. -/
theorem ev_eq_of_hom (f : F ⟶ G) (i : Fin n) : F.ev i = G.ev i := by
  rw [← marking_comp_map, ← f.hom_comp_map, f.curve.marking_comp_hom_assoc, marking_comp_map]

/-- The functor sending a prestable map to its pointed source curve, forgetting the map. -/
@[expose, simps]
def toCurve : PrestableMap q n ⥤ PointedPrestableFamily S n where
  obj F := F.curve
  map f := f.curve

instance : (toCurve (q := q) (n := n)).Faithful where
  map_injective h := hom_ext h

/-- An isomorphism of prestable maps from an isomorphism of pointed source curves commuting with
the maps to the target. -/
def isoMk (e : F.curve ≅ G.curve) (he : e.hom.hom ≫ G.map = F.map) : F ≅ G where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, by
    rw [← he, ← PointedPrestableFamily.comp_hom_assoc, e.inv_hom_id,
      PointedPrestableFamily.id_hom, Category.id_comp]⟩

@[simp]
theorem isoMk_hom_curve (e : F.curve ≅ G.curve) (he : e.hom.hom ≫ G.map = F.map) :
    (isoMk e he).hom.curve = e.hom :=
  (rfl)

@[simp]
theorem isoMk_inv_curve (e : F.curve ≅ G.curve) (he : e.hom.hom ≫ G.map = F.map) :
    (isoMk e he).inv.curve = e.inv :=
  (rfl)

/-- A morphism of prestable maps is an isomorphism exactly when its morphism of pointed source
curves is an isomorphism. -/
theorem isIso_iff_isIso_curve (f : F ⟶ G) : IsIso f ↔ IsIso f.curve :=
  ⟨fun _ ↦ ⟨(inv f).curve, congr(($(IsIso.hom_inv_id f)).curve),
      congr(($(IsIso.inv_hom_id f)).curve)⟩,
    fun _ ↦ (isoMk (asIso f.curve) f.hom_comp_map).isIso_hom⟩

/-- A morphism of prestable maps is an isomorphism exactly when its map of total spaces is an
isomorphism. -/
theorem isIso_iff_isIso_hom (f : F ⟶ G) : IsIso f ↔ IsIso f.curve.hom :=
  (isIso_iff_isIso_curve f).trans (PointedPrestableFamily.isIso_iff_isIso_hom f.curve)

instance isIso_curve_of_isIso (f : F ⟶ G) [IsIso f] : IsIso f.curve :=
  (isIso_iff_isIso_curve f).1 ‹_›

instance isIso_of_isIso_curve (f : F ⟶ G) [IsIso f.curve] : IsIso f :=
  (isIso_iff_isIso_curve f).2 ‹_›

instance : (toCurve (q := q) (n := n)).ReflectsIsomorphisms where
  reflects f _ := (isIso_iff_isIso_curve f).2 ‹IsIso (toCurve.map f)›

/-- Forgetting the map, as a group homomorphism from the automorphisms of a prestable map to the
automorphisms of its pointed source curve. -/
def autToCurve (F : PrestableMap q n) : Aut F →* Aut F.curve :=
  toCurve.mapAut F

@[simp]
theorem autToCurve_apply_asIso_hom (e : Aut F) :
    (autToCurve F e).asIso.hom = e.asIso.hom.curve := by
  unfold autToCurve
  rfl

/-- An automorphism of a prestable map is determined by its automorphism of the pointed source
curve. -/
theorem autToCurve_injective (F : PrestableMap q n) : Function.Injective (autToCurve F) :=
  fun _ _ h ↦ Aut.ext (Iso.ext (toCurve.map_injective congr(($h).asIso.hom)))

/-- An automorphism of the pointed source curve of a prestable map comes from an automorphism of
the prestable map exactly when it commutes with the map to the target. -/
theorem mem_range_autToCurve_iff (e : Aut F.curve) :
    e ∈ (autToCurve F).range ↔ e.asIso.hom.hom ≫ F.map = F.map := by
  refine ⟨?_, fun h ↦ ⟨.of (isoMk e.asIso h), Aut.ext (Iso.ext ?_)⟩⟩
  · rintro ⟨e, rfl⟩
    simp
  · simp

/-! ### Postcomposition -/

/-- Postcomposition with a morphism of targets `h : V ⟶ W` over `S`, as a functor from prestable
maps to `q` to prestable maps to `r`. -/
@[expose, simps! obj_curve obj_map map_curve]
def postcompFunctor {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) :
    PrestableMap q n ⥤ PrestableMap r n where
  obj F := F.postcomp h hh
  -- The source curves and maps of `F.postcomp h hh` are `F.curve` and `F.map ≫ h` by definition.
  map f := ⟨f.curve, f.hom_comp_map_assoc h⟩

/-- Postcomposition is faithful: it does not change morphisms of source curves. -/
instance {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) :
    (postcompFunctor (n := n) h hh).Faithful where
  map_injective {_ _} _ _ hfg := hom_ext congr(($hfg).curve)

/-- Postcomposition with a monomorphism of targets is full: a morphism of source curves that
commutes with the postcomposed maps commutes with the original maps. -/
instance {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) [Mono h] :
    (postcompFunctor (n := n) h hh).Full where
  map_surjective f :=
    -- The source curves and maps of `F.postcomp h hh` are `F.curve` and `F.map ≫ h` by definition.
    ⟨⟨f.curve, (cancel_mono h).1 ((Category.assoc _ _ _).trans f.hom_comp_map)⟩, rfl⟩

/-- Postcomposition with an isomorphism of targets is an equivalence of categories: every
prestable map to `r` is the postcomposition of its postcomposition with the inverse. -/
instance {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) [IsIso h] :
    (postcompFunctor (n := n) h hh).IsEquivalence where
  essSurj := Functor.essSurj_of_surj fun G ↦
    ⟨G.postcomp (inv h) (by simp [← hh]), (G.postcomp_postcomp _ _ h hh).trans (by simp)⟩

/-! ### Base change and reindexing -/

/-- The base change along `g : T ⟶ S` of a morphism of prestable maps to `q`: the base change of
the morphism of pointed source curves. -/
def pullbackMap (g : T ⟶ S) (f : F ⟶ G) : F.pullback g ⟶ G.pullback g where
  curve := PointedPrestableFamily.pullbackMap g f.curve
  hom_comp_map := by
    simp only [PointedPrestableFamily.pullbackMap_hom]
    -- The total space of the base-changed source curve is only definitionally, not reducibly,
    -- the pullback `C ×_S T`, so the pullback API applies only after unfolding.
    dsimp only [pullback, PointedPrestableFamily.pullback]
    ext <;> simp

@[simp]
theorem pullbackMap_curve (g : T ⟶ S) (f : F ⟶ G) :
    (pullbackMap g f).curve = PointedPrestableFamily.pullbackMap g f.curve :=
  (rfl)

/-- Base change along `g : T ⟶ S` as a functor from prestable maps to `q` to prestable maps to
the base-changed target `V ×_S T ⟶ T`. -/
@[expose, simps]
def pullbackFunctor (g : T ⟶ S) :
    PrestableMap q n ⥤ PrestableMap (Limits.pullback.snd q g) n where
  obj F := F.pullback g
  map f := pullbackMap g f
  -- The source curve of `F.pullback g` is `F.curve.pullback g` by definition, so these reduce to
  -- the functoriality of base change of pointed prestable families.
  map_id F := by
    ext1
    rw [pullbackMap_curve, id_curve, id_curve]
    exact (PointedPrestableFamily.pullbackFunctor g).map_id F.curve
  map_comp f f' := by
    ext1
    rw [pullbackMap_curve, comp_curve, comp_curve, pullbackMap_curve, pullbackMap_curve]
    exact (PointedPrestableFamily.pullbackFunctor g).map_comp f.curve f'.curve

/-- Reindexing the markings along an injection `e : Fin m ↪ Fin n` as a functor; a morphism of
prestable maps preserves in particular the reindexed markings. -/
@[expose, simps]
def reindexFunctor (e : Fin m ↪ Fin n) : PrestableMap q n ⥤ PrestableMap q m where
  obj F := F.reindex e
  map f := ⟨(PointedPrestableFamily.reindexFunctor e).map f.curve, f.hom_comp_map⟩

end PrestableMap

end TauCeti.AlgebraicGeometry
