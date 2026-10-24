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

Base change also changes the target, from `q` to `V ×_S T ⟶ T`, so its coherence is stated after
transporting along the canonical isomorphisms of targets. Base change along the identity and along
a composite agree with the identity and with iterated base change up to canonical natural
isomorphisms. Base change does not depend on the chosen pullbacks: any prestable map over `T`
whose source curve and target are fibre products, compatibly with the markings and the maps, is
canonically isomorphic to the chosen base change.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap.Hom`: morphisms of prestable maps to a fixed target.
* `TauCeti.AlgebraicGeometry.PrestableMap.toCurve`: the functor forgetting the map.
* `TauCeti.AlgebraicGeometry.PrestableMap.isoMk`: an isomorphism of prestable maps from an
  isomorphism of pointed source curves commuting with the maps.
* `TauCeti.AlgebraicGeometry.PrestableMap.autToCurve`: the injective homomorphism from the
  automorphism group of a prestable map to that of its pointed source curve.
* `TauCeti.AlgebraicGeometry.PrestableMap.postcompFunctor`: postcomposition as a functor.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackFunctor`: base change as a functor.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackAut`: base change of automorphisms.
* `TauCeti.AlgebraicGeometry.PrestableMap.reindexFunctor`: reindexing as a functor.
* `TauCeti.AlgebraicGeometry.PrestableMap.isoPullback`: the canonical isomorphism from a prestable
  map over `T` presented by fibre products to the chosen base change.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackIdIso`,
  `TauCeti.AlgebraicGeometry.PrestableMap.pullbackCompIso`: the canonical isomorphisms for base
  change along the identity and along a composite.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullbackFunctorId`,
  `TauCeti.AlgebraicGeometry.PrestableMap.pullbackFunctorComp`: the corresponding natural
  isomorphisms of functors.

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

variable {V W S T U : Scheme.{u}} {q : V ⟶ S} {m n : ℕ}

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
  -- `simp` cannot use `Functor.mapAut_apply_asIso` directly: the codomain `Aut F.curve` of
  -- `autToCurve F` is `Aut (toCurve.obj F)` only after unfolding `toCurve`.
  exact congr(Iso.hom $(Functor.mapAut_apply_asIso F toCurve e))

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
    exact (PointedPrestableFamily.pullbackFunctor g).map_id F.curve
  map_comp f f' := by
    ext1
    exact (PointedPrestableFamily.pullbackFunctor g).map_comp f.curve f'.curve

/-- Base change along `g : T ⟶ S`, as a group homomorphism from the automorphisms of a prestable
map to the automorphisms of its base change. -/
def pullbackAut (F : PrestableMap q n) (g : T ⟶ S) : Aut F →* Aut (F.pullback g) :=
  (pullbackFunctor g).mapAut F

@[simp]
theorem pullbackAut_apply_asIso_hom (F : PrestableMap q n) (g : T ⟶ S) (e : Aut F) :
    (F.pullbackAut g e).asIso.hom = pullbackMap g e.asIso.hom :=
  (rfl)

/-- Reindexing the markings along an injection `e : Fin m ↪ Fin n` as a functor; a morphism of
prestable maps preserves in particular the reindexed markings. -/
@[expose, simps]
def reindexFunctor (e : Fin m ↪ Fin n) : PrestableMap q n ⥤ PrestableMap q m where
  obj F := F.reindex e
  -- The total spaces and maps of `F.reindex e` are those of `F` by definition, and the reindexed
  -- morphism of source curves has the same map of total spaces `f.curve.hom`.
  map f := ⟨(PointedPrestableFamily.reindexFunctor e).map f.curve, f.hom_comp_map⟩


/-! ### Canonical isomorphisms of base change

Base change along `g : T ⟶ S` also changes the target, from `q` to `V ×_S T ⟶ T`. The canonical
isomorphisms below therefore compare prestable maps after postcomposing with the corresponding
canonical isomorphism of targets.

The total space of a base-changed source curve is only definitionally, not reducibly, the chosen
pullback `C ×_S T`, so a compatibility goal mixes several spellings of the same object and the
pullback API does not match it. The proofs below therefore first unfold `postcomp`, `pullback`
and `PointedPrestableFamily.pullback` with `dsimp only`, which writes every such object as the
chosen pullback, and then close the goal with `simp`. -/

/-- **Base change does not depend on the chosen pullbacks.** Let `G` be a prestable map to
`q' : V' ⟶ T`, where `V'` with `b : V' ⟶ V` is a fibre product of `q` and `g : T ⟶ S`. Suppose
that the total space of `G` with `a : G.total ⟶ F.total` is a fibre product of the structure
morphism of `F` and `g`, that `a` carries the markings of `G` to `g` followed by those of `F`,
and that `a` and `b` intertwine the maps. Then `G` is canonically isomorphic to the chosen base
change `F.pullback g`, transported to the target `q'` along the canonical isomorphism
`V ×_S T ≅ V'`. -/
def isoPullback (F : PrestableMap q n) (g : T ⟶ S) {V' : Scheme.{u}} {q' : V' ⟶ T}
    (b : V' ⟶ V) (hb : IsPullback b q' q g) (G : PrestableMap q' n)
    (a : G.curve.total ⟶ F.curve.total) (ha : IsPullback a G.curve.toBase F.curve.toBase g)
    (hm : ∀ i, G.curve.marking i ≫ a = g ≫ F.curve.marking i) (hab : G.map ≫ b = a ≫ F.map) :
    G ≅ (F.pullback g).postcomp hb.isoPullback.inv hb.isoPullback_inv_snd :=
  isoMk (F.curve.isoPullback g G.curve a ha hm) (by
    dsimp only [postcomp, pullback, PointedPrestableFamily.pullback]
    apply hb.hom_ext <;> simp [hab])

@[simp]
theorem isoPullback_hom_curve (F : PrestableMap q n) (g : T ⟶ S) {V' : Scheme.{u}}
    {q' : V' ⟶ T} (b : V' ⟶ V) (hb : IsPullback b q' q g) (G : PrestableMap q' n)
    (a : G.curve.total ⟶ F.curve.total) (ha : IsPullback a G.curve.toBase F.curve.toBase g)
    (hm : ∀ i, G.curve.marking i ≫ a = g ≫ F.curve.marking i) (hab : G.map ≫ b = a ≫ F.map) :
    (isoPullback F g b hb G a ha hm hab).hom.curve = (F.curve.isoPullback g G.curve a ha hm).hom :=
  (rfl)

@[simp]
theorem isoPullback_inv_curve (F : PrestableMap q n) (g : T ⟶ S) {V' : Scheme.{u}}
    {q' : V' ⟶ T} (b : V' ⟶ V) (hb : IsPullback b q' q g) (G : PrestableMap q' n)
    (a : G.curve.total ⟶ F.curve.total) (ha : IsPullback a G.curve.toBase F.curve.toBase g)
    (hm : ∀ i, G.curve.marking i ≫ a = g ≫ F.curve.marking i) (hab : G.map ≫ b = a ≫ F.map) :
    (isoPullback F g b hb G a ha hm hab).inv.curve = (F.curve.isoPullback g G.curve a ha hm).inv :=
  (rfl)

/-- The canonical isomorphism from the base change of a prestable map along the identity of `S`,
transported back to the target `q` along the first projection `V ×_S S ⟶ V`, to the map itself;
on total spaces it is the first projection `C ×_S S ⟶ C`. -/
def pullbackIdIso (F : PrestableMap q n) :
    (F.pullback (𝟙 S)).postcomp (Limits.pullback.fst q (𝟙 S))
      (Limits.pullback.condition.trans (Category.comp_id _)) ≅ F :=
  isoMk F.curve.pullbackIdIso (by
    dsimp only [postcomp, pullback, PointedPrestableFamily.pullback]
    simp)

@[simp]
theorem pullbackIdIso_hom_curve (F : PrestableMap q n) :
    (pullbackIdIso F).hom.curve = F.curve.pullbackIdIso.hom :=
  (rfl)

@[simp]
theorem pullbackIdIso_inv_curve (F : PrestableMap q n) :
    (pullbackIdIso F).inv.curve = F.curve.pullbackIdIso.inv :=
  (rfl)

/-- The canonical isomorphism `pullbackIdIso` is natural in the prestable map. -/
@[reassoc]
theorem pullbackIdIso_hom_naturality (f : F ⟶ G) :
    (postcompFunctor (Limits.pullback.fst q (𝟙 S))
        (Limits.pullback.condition.trans (Category.comp_id _))).map
        (pullbackMap (𝟙 S) f) ≫ (pullbackIdIso G).hom =
      (pullbackIdIso F).hom ≫ f :=
  hom_ext (PointedPrestableFamily.pullbackIdIso_hom_naturality f.curve)

/-- Base change along the identity of `S`, followed by postcomposition with the first projection
`V ×_S S ⟶ V`, is canonically isomorphic to the identity functor. -/
def pullbackFunctorId :
    pullbackFunctor (𝟙 S) ⋙ postcompFunctor (Limits.pullback.fst q (𝟙 S))
        (Limits.pullback.condition.trans (Category.comp_id _)) ≅ 𝟭 (PrestableMap q n) :=
  NatIso.ofComponents pullbackIdIso pullbackIdIso_hom_naturality

@[simp]
theorem pullbackFunctorId_app (F : PrestableMap q n) :
    (pullbackFunctorId (q := q)).app F = pullbackIdIso F :=
  (rfl)

/-- The canonical isomorphism from the iterated base change of a prestable map along
`g : T ⟶ S` and `h : U ⟶ T`, transported to the target `V ×_S U ⟶ U` along the canonical
isomorphism `(V ×_S T) ×_T U ≅ V ×_S U`, to its base change along `h ≫ g`; on total spaces it is
the canonical isomorphism `(C ×_S T) ×_T U ≅ C ×_S U`. -/
def pullbackCompIso (F : PrestableMap q n) (g : T ⟶ S) (h : U ⟶ T) :
    ((F.pullback g).pullback h).postcomp (pullbackLeftPullbackSndIso q g h).hom
        (pullbackLeftPullbackSndIso_hom_snd q g h) ≅ F.pullback (h ≫ g) :=
  isoMk (F.curve.pullbackCompIso g h) (by
    dsimp only [postcomp, pullback, PointedPrestableFamily.pullback]
    apply Limits.pullback.hom_ext <;> simp)

@[simp]
theorem pullbackCompIso_hom_curve (F : PrestableMap q n) (g : T ⟶ S) (h : U ⟶ T) :
    (pullbackCompIso F g h).hom.curve = (F.curve.pullbackCompIso g h).hom :=
  (rfl)

@[simp]
theorem pullbackCompIso_inv_curve (F : PrestableMap q n) (g : T ⟶ S) (h : U ⟶ T) :
    (pullbackCompIso F g h).inv.curve = (F.curve.pullbackCompIso g h).inv :=
  (rfl)

/-- The canonical isomorphism `pullbackCompIso` is natural in the prestable map. -/
@[reassoc]
theorem pullbackCompIso_inv_naturality (g : T ⟶ S) (h : U ⟶ T) (f : F ⟶ G) :
    pullbackMap (h ≫ g) f ≫ (pullbackCompIso G g h).inv =
      (pullbackCompIso F g h).inv ≫
        (postcompFunctor (pullbackLeftPullbackSndIso q g h).hom
          (pullbackLeftPullbackSndIso_hom_snd q g h)).map (pullbackMap h (pullbackMap g f)) :=
  hom_ext (PointedPrestableFamily.pullbackCompIso_inv_naturality g h f.curve)

/-- Base change along a composite `h ≫ g` is canonically isomorphic to base change along `g`
followed by base change along `h` and postcomposition with the canonical isomorphism
`(V ×_S T) ×_T U ≅ V ×_S U` of targets. -/
def pullbackFunctorComp (g : T ⟶ S) (h : U ⟶ T) :
    pullbackFunctor (q := q) (n := n) (h ≫ g) ≅
      pullbackFunctor g ⋙ pullbackFunctor h ⋙
        postcompFunctor (pullbackLeftPullbackSndIso q g h).hom
          (pullbackLeftPullbackSndIso_hom_snd q g h) :=
  NatIso.ofComponents (fun F ↦ (pullbackCompIso F g h).symm)
    (pullbackCompIso_inv_naturality g h)

@[simp]
theorem pullbackFunctorComp_app (g : T ⟶ S) (h : U ⟶ T) (F : PrestableMap q n) :
    (pullbackFunctorComp g h).app F = (pullbackCompIso F g h).symm :=
  (rfl)

end PrestableMap

end TauCeti.AlgebraicGeometry
