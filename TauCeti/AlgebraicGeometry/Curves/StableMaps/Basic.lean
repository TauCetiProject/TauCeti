/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.PointedPrestable.Basic

/-!
# Prestable maps

Let `q : V ⟶ S` be a morphism of schemes, the target. A **prestable map** to `q` with `n`
markings is an `n`-pointed prestable family of curves `π : C ⟶ S` together with a morphism
`F : C ⟶ V` over `S`, that is, with `F ≫ q = π`. These are the objects whose stability is the
subject of the theory of stable maps. Stability is a condition on the components of the
geometric fibres of `π` that `F` contracts, and it is not part of the data. In particular
the pointed source curve need not be stable, and no projectivity of the target and no choice
of polarization is part of the data.

The **evaluation** at the `i`th marking `sᵢ` is the section `evᵢ = sᵢ ≫ F` of `q`.

Prestable maps pull back along an arbitrary morphism `g : T ⟶ S`: the source family is the base
change of `π`, the target is the base change `V ×_S T ⟶ T` of `q`, and the map is the base
change of `F`. Base change commutes with evaluation, and both the base-changed map and the
base-changed evaluations form pullback squares with the original ones. Markings can be
reindexed along an injection, the map can be postcomposed with a morphism of targets over `S`,
and every section of the target gives a constant prestable map.

## Main definitions

* `TauCeti.AlgebraicGeometry.PrestableMap q n`: a prestable map to `q` with `n` markings.
* `TauCeti.AlgebraicGeometry.PrestableMap.ev`: the evaluation at a marking.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullback`: base change along `T ⟶ S`.
* `TauCeti.AlgebraicGeometry.PrestableMap.reindex`: reindexing the markings.
* `TauCeti.AlgebraicGeometry.PrestableMap.postcomp`: postcomposition with a morphism of targets.
* `TauCeti.AlgebraicGeometry.PrestableMap.const`: the constant map through a section of the
  target.

## Main results

* `TauCeti.AlgebraicGeometry.PrestableMap.isPullback_pullback_map`: the base change of `F` is
  the pullback of `F` along `C ×_S T ⟶ C` and `V ×_S T ⟶ V`.
* `TauCeti.AlgebraicGeometry.PrestableMap.isPullback_pullback_ev`: the base-changed evaluations
  are the base changes of the evaluations.
* `TauCeti.AlgebraicGeometry.PrestableMap.pullback_const`: base change of a constant map is the
  constant map through the base-changed section.

## References

* M. Kontsevich, *Enumeration of rational curves via torus actions*, in *The moduli space of
  curves*, Progr. Math. 129 (1995), 335–368, where stable maps were introduced.
* K. Behrend and Yu. Manin, *Stacks of stable maps and Gromov–Witten invariants*,
  Duke Math. J. 85 (1996), 1–60, Definition 1.1 and Section 2, for prestable maps to a
  target over an arbitrary base.
* W. Fulton and R. Pandharipande, *Notes on stable maps and quantum cohomology*,
  Proc. Sympos. Pure Math. 62 (1997), Part 2, 45–96, Section 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- A **prestable map** to the target `q : V ⟶ S` with `n` markings: an `n`-pointed prestable
family of curves over `S` together with a morphism from its total space to `V` over `S`.
No stability condition is part of the data. -/
structure PrestableMap {V S : Scheme.{u}} (q : V ⟶ S) (n : ℕ) where
  /-- The pointed prestable source curve. -/
  curve : PointedPrestableFamily S n
  /-- The map from the source curve to the target. -/
  map : curve.total ⟶ V
  /-- The map lies over the base. -/
  w : map ≫ q = curve.toBase

attribute [reassoc (attr := simp)] PrestableMap.w

namespace PrestableMap

variable {V W S T : Scheme.{u}} {q : V ⟶ S} {m n : ℕ} (F : PrestableMap q n)

/-- The **evaluation** at the `i`th marking: the composite `sᵢ ≫ F : S ⟶ V`. -/
def ev (i : Fin n) : S ⟶ V :=
  F.curve.marking i ≫ F.map

/-- The map carries the `i`th marking to the `i`th evaluation. -/
@[reassoc (attr := simp)]
theorem marking_comp_map (i : Fin n) : F.curve.marking i ≫ F.map = F.ev i :=
  (rfl)

/-- Each evaluation is a section of the target. -/
@[reassoc (attr := simp)]
theorem ev_comp (i : Fin n) : F.ev i ≫ q = 𝟙 S := by
  rw [← marking_comp_map, Category.assoc, w, PointedPrestableFamily.marking_comp_toBase]

/-- The map of a prestable map is locally of finite type: its composite with the target is the
structure morphism of the source curve, which is proper. -/
instance locallyOfFiniteType_map : LocallyOfFiniteType F.map :=
  have : LocallyOfFiniteType (F.map ≫ q) := F.w ▸ inferInstance
  locallyOfFiniteType_of_comp F.map q

/-- The base change of a prestable map along `g : T ⟶ S`. Its source is the base change of
the pointed source curve, its target is the second projection `V ×_S T ⟶ T`, and its map is
the base change `C ×_S T ⟶ V ×_S T` of the map. -/
@[expose, simps curve]
def pullback (g : T ⟶ S) : PrestableMap (Limits.pullback.snd q g) n where
  curve := F.curve.pullback g
  -- The ascription keeps the chosen pullback `C ×_S T` as the source, so that the compatibility
  -- obligation is elaborated in terms of its projections.
  map := (Limits.pullback.lift (Limits.pullback.fst F.curve.toBase g ≫ F.map)
    (Limits.pullback.snd F.curve.toBase g)
      (by rw [Category.assoc, F.w, Limits.pullback.condition]) :
    Limits.pullback F.curve.toBase g ⟶ Limits.pullback q g)
  w := Limits.pullback.lift_snd _ _ _

/-- The base change of the map lies over the original map. -/
@[reassoc (attr := simp)]
theorem pullback_map_fst (g : T ⟶ S) :
    (F.pullback g).map ≫ Limits.pullback.fst q g =
      Limits.pullback.fst F.curve.toBase g ≫ F.map :=
  Limits.pullback.lift_fst _ _ _

/-- The base change of the map is the pullback of the map along the first projections:
`C ×_S T` is the fibre product of `C` and `V ×_S T` over `V`. -/
theorem isPullback_pullback_map (g : T ⟶ S) :
    IsPullback (F.pullback g).map (Limits.pullback.fst F.curve.toBase g)
      (Limits.pullback.fst q g) F.map :=
  -- Paste with the pullback square of `q` and `g`; the outer rectangle is the pullback square
  -- of the structure morphism of the source and `g`.
  .of_right (by rw [w, F.w]; exact (IsPullback.of_hasPullback _ g).flip)
    (F.pullback_map_fst g) (IsPullback.of_hasPullback q g).flip

/-- The base-changed evaluations lie over the original evaluations. -/
@[reassoc (attr := simp)]
theorem pullback_ev_fst (g : T ⟶ S) (i : Fin n) :
    (F.pullback g).ev i ≫ Limits.pullback.fst q g = g ≫ F.ev i := by
  rw [← marking_comp_map, Category.assoc, pullback_map_fst]
  exact F.curve.pullback_marking_fst_assoc g i F.map

/-- The base-changed evaluations and the original evaluations form pullback squares with the
first projection `V ×_S T ⟶ V`. -/
theorem isPullback_pullback_ev (g : T ⟶ S) (i : Fin n) :
    IsPullback ((F.pullback g).ev i) g (Limits.pullback.fst q g) (F.ev i) :=
  -- Paste with the pullback square of `q` and `g`; both horizontal composites are identities.
  .of_right (by simpa only [ev_comp] using IsPullback.id_horiz g) (F.pullback_ev_fst g i)
    (IsPullback.of_hasPullback q g).flip

/-- Reindex the markings of a prestable map along an injection `e : Fin m ↪ Fin n`, keeping the
map. Reindexing along an equivalence reorders the markings, and reindexing along
`Fin.castSuccEmb` forgets the last marking. -/
@[expose, simps curve map]
def reindex (e : Fin m ↪ Fin n) : PrestableMap q m where
  curve := F.curve.reindex e
  map := F.map
  w := F.w

/-- Reindexing the markings reindexes the evaluations. -/
@[simp]
theorem reindex_ev (e : Fin m ↪ Fin n) (i : Fin m) : (F.reindex e).ev i = F.ev (e i) :=
  (rfl)

/-- Postcompose a prestable map with a morphism of targets `h : V ⟶ W` over `S`. -/
@[expose, simps curve map]
def postcomp {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) : PrestableMap r n where
  curve := F.curve
  map := F.map ≫ h
  w := by simp [hh]

/-- The evaluations of a postcomposed map are the postcomposed evaluations. -/
@[simp]
theorem postcomp_ev {r : W ⟶ S} (h : V ⟶ W) (hh : h ≫ r = q) (i : Fin n) :
    (F.postcomp h hh).ev i = F.ev i ≫ h :=
  -- By definition, the evaluation is `sᵢ ≫ F ≫ h`.
  (Category.assoc (F.curve.marking i) F.map h).symm

/-- Postcomposition with the identity of the target does nothing. -/
@[simp]
theorem postcomp_id : F.postcomp (𝟙 V) (Category.id_comp q) = F := by
  cases F
  simp [postcomp]

/-- Postcomposing twice is postcomposing with the composite. -/
@[simp]
theorem postcomp_postcomp {X : Scheme.{u}} {r : W ⟶ S} {t : X ⟶ S} (h : V ⟶ W)
    (hh : h ≫ r = q) (h' : W ⟶ X) (hh' : h' ≫ t = r) :
    (F.postcomp h hh).postcomp h' hh' = F.postcomp (h ≫ h') (by simp [hh', hh]) := by
  simp [postcomp]

/-- The **constant** prestable map on the pointed prestable family `P` through the section `σ`
of the target: the composite of the structure morphism of `P` with `σ`. -/
@[expose, simps curve map]
def const (P : PointedPrestableFamily S n) (σ : S ⟶ V) (hσ : σ ≫ q = 𝟙 S) :
    PrestableMap q n where
  curve := P
  map := P.toBase ≫ σ
  w := by simp [hσ]

/-- Every evaluation of a constant map is the section it is constant through. -/
@[simp]
theorem const_ev (P : PointedPrestableFamily S n) (σ : S ⟶ V) (hσ : σ ≫ q = 𝟙 S) (i : Fin n) :
    (const P σ hσ).ev i = σ :=
  -- By definition, the evaluation is `sᵢ ≫ π ≫ σ`.
  (P.marking_comp_toBase_assoc i σ).trans (Category.id_comp σ)

/-- The base change of a constant map is the constant map through the base change of the
section. -/
theorem pullback_const (P : PointedPrestableFamily S n) (σ : S ⟶ V) (hσ : σ ≫ q = 𝟙 S)
    (g : T ⟶ S) :
    (const P σ hσ).pullback g =
      const (P.pullback g) (Limits.pullback.lift (g ≫ σ) (𝟙 T) (by simp [hσ])) (by simp) := by
  dsimp only [pullback, const]
  congr 1
  -- The structure morphism of `P.pullback g` is only definitionally the second projection, so
  -- the reassociations are stated as explicit terms rather than left to `simp`.
  apply Limits.pullback.hom_ext
  · rw [Limits.pullback.lift_fst]
    exact (Limits.pullback.condition_assoc σ).trans
      ((Category.assoc (P.pullback g).toBase _ _).trans
        (by rw [Limits.pullback.lift_fst]; exact congrArg (· ≫ g ≫ σ) (P.pullback_toBase g))).symm
  · rw [Limits.pullback.lift_snd]
    exact ((Category.assoc (P.pullback g).toBase _ _).trans
      (by rw [Limits.pullback.lift_snd, Category.comp_id]; exact P.pullback_toBase g)).symm

end PrestableMap

end TauCeti.AlgebraicGeometry
