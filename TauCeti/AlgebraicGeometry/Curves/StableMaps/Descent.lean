/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableMaps.Category
public import TauCeti.AlgebraicGeometry.Descent.Contraction
public import TauCeti.AlgebraicGeometry.Morphisms.Epi

/-!
# Descent of prestable maps along contractions of their source curves

Let `F : C ⟶ V` be a prestable map to a target `q : V ⟶ S`, and let `c : C ⟶ C'` be a morphism
of `n`-pointed prestable families over `S` that contracts its source: `c` is surjective and
`𝒪_{C'} → c_* 𝒪_C` is an isomorphism. The map of total spaces of `c` is proper, since both
families are proper over `S`, so it is a topological quotient map. If `F` is constant on the
fibres of `c`, that is on the subcurves contracted by `c`, then `F` factors uniquely as `c`
followed by a map `C' ⟶ V`, and this map lies over `S`. This file packages that factorization as
the prestable map `F.descend c hc hF` with source `C'`, together with a morphism of prestable maps
`F.toDescend c hc hF : F ⟶ F.descend c hc hF` whose morphism of source curves is `c`.

The descended map is unique: any prestable map receiving a morphism from `F` along `c` is the
descent (`TauCeti.AlgebraicGeometry.PrestableMap.descend_eq`). Conversely, the map of a prestable
map is always constant on the fibres of the morphisms of source curves out of it
(`TauCeti.AlgebraicGeometry.PrestableMap.Hom.factorsThrough_map`), so a prestable map descends
along `c` exactly when it is constant on the fibres of `c`. Constancy on fibres can be tested on
geometric fibres
(`AlgebraicGeometry.Scheme.Hom.factorsThrough_iff_subsingleton_range_geometricFiber`).
No separatedness of the target, no genus or connectedness condition on the fibres of `c` and no
local Noetherianity of the base is needed.

Descent commutes with the operations on prestable maps. Postcomposition with a morphism of
targets and reindexing of the markings commute with descent on the nose. Base change along
`g : T ⟶ S` commutes with descent whenever the base change of `c` is again a contraction, that is,
when `𝒪_{C'} → c_* 𝒪_C` is still an isomorphism after base change along `g`, for instance when
this holds universally. Surjectivity of `c`, and constancy of `F` on the fibres of `c`, survive
base change automatically.

## Main definitions

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `descend F c hc hF`: the prestable map with source `C'` through which `F` factors.
* `toDescend F c hc hF`: the morphism of prestable maps `F ⟶ F.descend c hc hF` along `c`.
* `descendHom`: a morphism `F ⟶ G` whose morphism of source curves factors through `c` induces a
  morphism `F.descend c hc hF ⟶ G`.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.PrestableMap`:

* `hom_comp_descend_map`: the descended map factors the map of `F` through `c`.
* `mk_eq_descend` and `descend_eq`: a prestable map with source `C'` whose map factors the map of
  `F` through `c`, for instance one receiving a morphism from `F` along `c`, is the descent of `F`.
* `toDescend_comp_descendHom` and the instance `Epi (F.toDescend c hc hF)`: the universal
  property of `F.toDescend c hc hF` among morphisms out of `F` whose morphism of source curves
  factors through `c`.
* `ev_descend`: descent preserves evaluations.
* `postcomp_descend`, `reindex_descend` and `pullback_descend`: descent commutes with
  postcomposition, reindexing and base change.
* `factorsThrough_pullback_map`: the base change of `F` is constant on the fibres of the base
  change of `c`.

## References

* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, Section 3, where stable maps are descended along contractions
  of their source curves.
* The Stacks Project, Tags 0E7B and 0E8A, for contractions of nodal curves and the descent of
  morphisms along them.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

namespace PrestableMap

variable {V W S T : Scheme.{u}} {q : V ⟶ S} {m n : ℕ}

variable (F : PrestableMap q n) {Q : PointedPrestableFamily S n} (c : F.curve ⟶ Q)
  [hs : Surjective c.hom] (hc : ∀ U, IsIso (c.hom.app U)) (hF : Function.FactorsThrough F.map c.hom)

/-- The **descent** of a prestable map `F` along a contraction `c : C ⟶ C'` of its pointed source
curve, that is, a surjective morphism of pointed prestable families with `𝒪_{C'} ≅ c_* 𝒪_C`,
when `F` is constant on the fibres of `c`. Its source curve is `C'` and its map is the unique map
`C' ⟶ V` through which `F` factors (`TauCeti.AlgebraicGeometry.PrestableMap.hom_comp_descend_map`).
The map of total spaces of `c` is proper, hence a topological quotient map. -/
@[expose, simps curve]
def descend : PrestableMap q n where
  curve := Q
  map := c.hom.descOfIsQuotientMap (c.hom.isClosedMap.isQuotientMap c.hom.continuous
    c.hom.surjective) hc F.map hF
  w := Scheme.Hom.descOfIsQuotientMap_comp_eq _ _ hc F.map hF (by simp)

/-- The descended map factors the map of `F` through the contraction. -/
@[simp, reassoc]
theorem hom_comp_descend_map : c.hom ≫ (F.descend c hc hF).map = F.map :=
  Scheme.Hom.comp_descOfIsQuotientMap ..

/-- The descended map is the only map through which the map of `F` factors. -/
theorem eq_descend_map {g : Q.total ⟶ V} (hg : c.hom ≫ g = F.map) :
    g = (F.descend c hc hF).map :=
  Scheme.Hom.eq_descOfIsQuotientMap _ _ _ _ _ hg

/-- The morphism of prestable maps from `F` to its descent along `c`, whose morphism of source
curves is `c`. -/
def toDescend : F ⟶ F.descend c hc hF :=
  ⟨c, F.hom_comp_descend_map c hc hF⟩

@[simp]
theorem toDescend_curve : (F.toDescend c hc hF).curve = c :=
  (rfl)

/-- **Uniqueness of the descent.** A prestable map with source curve `C'` whose map factors the map
of `F` through `c` is the descent of `F` along `c`. -/
theorem mk_eq_descend {g : Q.total ⟶ V} (hw : g ≫ q = Q.toBase) (hg : c.hom ≫ g = F.map) :
    PrestableMap.mk Q g hw = F.descend c hc hF := by
  dsimp only [descend]
  congr 1
  exact F.eq_descend_map c hc hF hg

/-- **Uniqueness of the descent**, as a morphism of prestable maps. If `f : F ⟶ G` is a morphism
of prestable maps whose morphism of source curves is a contraction, then `G` is the descent of `F`
along it. -/
theorem descend_eq {G : PrestableMap q n} (f : F ⟶ G) [Surjective f.curve.hom]
    (hf : ∀ U, IsIso (f.curve.hom.app U)) (hFf : Function.FactorsThrough F.map f.curve.hom) :
    F.descend f.curve hf hFf = G := by
  obtain ⟨_, _, _⟩ := G
  exact (F.mk_eq_descend f.curve hf hFf _ f.hom_comp_map).symm

/-- The morphism to the descent is an epimorphism: the map of total spaces of a contraction is
an epimorphism of schemes. -/
instance epi_toDescend : Epi (F.toDescend c hc hF) where
  left_cancellation g₁ g₂ e := by
    have := c.hom.epi_of_surjective_of_app_injective fun U ↦
      (ConcreteCategory.bijective_of_isIso _).1
    ext1
    ext1
    exact (cancel_epi c.hom).1 congr(($e).curve.hom)

/-- **The universal property of the descent.** A morphism of prestable maps `f : F ⟶ G` whose
morphism of source curves factors as `c ≫ d` induces the morphism `F.descend c hc hF ⟶ G` with
morphism of source curves `d`. -/
def descendHom {G : PrestableMap q n} (f : F ⟶ G) (d : Q ⟶ G.curve) (hd : c ≫ d = f.curve) :
    F.descend c hc hF ⟶ G where
  curve := d
  hom_comp_map := F.eq_descend_map c hc hF <| by
    have h := f.hom_comp_map
    rw [← hd, PointedPrestableFamily.comp_hom, Category.assoc] at h
    exact h

@[simp]
theorem descendHom_curve {G : PrestableMap q n} (f : F ⟶ G) (d : Q ⟶ G.curve)
    (hd : c ≫ d = f.curve) : (F.descendHom c hc hF f d hd).curve = d :=
  (rfl)

/-- The induced morphism out of the descent recovers the original morphism. -/
@[reassoc (attr := simp)]
theorem toDescend_comp_descendHom {G : PrestableMap q n} (f : F ⟶ G) (d : Q ⟶ G.curve)
    (hd : c ≫ d = f.curve) : F.toDescend c hc hF ≫ F.descendHom c hc hF f d hd = f :=
  hom_ext hd

/-- Descent preserves the evaluation at every marking. -/
@[simp]
theorem ev_descend (i : Fin n) : (F.descend c hc hF).ev i = F.ev i :=
  (ev_eq_of_hom (F.toDescend c hc hF) i).symm

/-- **Descent commutes with postcomposition** with a morphism of targets `h : V ⟶ W` over `S`. -/
theorem postcomp_descend {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q)
    (hF' : Function.FactorsThrough (F.postcomp h hh).map c.hom) :
    (F.postcomp h hh).descend (hs := hs) c hc hF' = (F.descend c hc hF).postcomp h hh :=
  -- The source curve of `F.postcomp h hh` is that of `F`, and its map is `F.map ≫ h`
  -- (`postcomp_curve`, `postcomp_map`); typeclass search does not see this, so the surjectivity
  -- of `c` is passed explicitly.
  ((F.postcomp h hh).mk_eq_descend (hs := hs) c hc hF' _
    (F.hom_comp_descend_map_assoc c hc hF h)).symm

/-- **Descent commutes with reindexing the markings** along an injection `e : Fin m ↪ Fin n`. -/
theorem reindex_descend (e : Fin m ↪ Fin n)
    (hF' : Function.FactorsThrough (F.reindex e).map c.hom) :
    (F.reindex e).descend (hs := hs) ((PointedPrestableFamily.reindexFunctor e).map c) hc hF' =
      (F.descend c hc hF).reindex e :=
  -- Reindexing keeps the total spaces and the map, and the reindexed morphism of source curves
  -- has the same map of total spaces `c.hom` (`reindex_curve`, `reindex_map`, `reindexFunctor`);
  -- typeclass search does not see this, so the surjectivity of `c` is passed explicitly.
  ((F.reindex e).mk_eq_descend (hs := hs) _ hc hF' _ (F.hom_comp_descend_map c hc hF)).symm

/-- The base change of a prestable map along `g : T ⟶ S` factors through the base change of a
contraction along which it descends. -/
theorem pullbackMap_hom_comp_pullback_descend_map (g : T ⟶ S) :
    (PointedPrestableFamily.pullbackMap g c).hom ≫ ((F.descend c hc hF).pullback g).map =
      (F.pullback g).map := by
  -- This is the base change of the morphism `F ⟶ F.descend c hc hF` along `g`.
  have h := (pullbackMap g (F.toDescend c hc hF)).hom_comp_map
  rw [pullbackMap_curve, toDescend_curve] at h
  exact h

include hc hF in
/-- The base change of a prestable map along `g : T ⟶ S` is constant on the fibres of the base
change of a contraction along which it descends. -/
theorem factorsThrough_pullback_map (g : T ⟶ S) :
    Function.FactorsThrough (F.pullback g).map (PointedPrestableFamily.pullbackMap g c).hom := by
  -- This is the base change of the morphism `F ⟶ F.descend c hc hF` along `g`.
  have h := (pullbackMap g (F.toDescend c hc hF)).factorsThrough_map
  rw [pullbackMap_curve, toDescend_curve] at h
  exact h

/-- **Descent commutes with base change** along `g : T ⟶ S`, whenever the base change of the
contraction `c` is again a contraction, that is, `𝒪_{C'} → c_* 𝒪_C` remains an isomorphism after
base change along `g`. The base change of `c` is automatically surjective
(`TauCeti.AlgebraicGeometry.PointedPrestableFamily.surjective_pullbackMap_hom`), and `F` is
automatically constant on its fibres (`factorsThrough_pullback_map`). -/
theorem pullback_descend (g : T ⟶ S)
    (hcg : ∀ U, IsIso ((PointedPrestableFamily.pullbackMap g c).hom.app U))
    (hFg :
      Function.FactorsThrough (F.pullback g).map (PointedPrestableFamily.pullbackMap g c).hom) :
    (F.pullback g).descend
        (hs := inferInstanceAs <| Surjective (PointedPrestableFamily.pullbackMap g c).hom)
        (PointedPrestableFamily.pullbackMap g c) hcg hFg =
      (F.descend c hc hF).pullback g :=
  -- The source curve of `F.pullback g` is `F.curve.pullback g` (`pullback_curve`); typeclass search
  -- does not see this, so the surjectivity of the base change of `c` is passed explicitly.
  ((F.pullback g).mk_eq_descend
    (hs := inferInstanceAs <| Surjective (PointedPrestableFamily.pullbackMap g c).hom)
    (PointedPrestableFamily.pullbackMap g c) hcg hFg _
    (F.pullbackMap_hom_comp_pullback_descend_map c hc hF g)).symm

end PrestableMap

end TauCeti.AlgebraicGeometry
