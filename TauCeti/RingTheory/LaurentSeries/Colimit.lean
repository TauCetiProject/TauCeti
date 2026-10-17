/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux
public import TauCeti.RingTheory.LaurentSeries.RamificationIndex

/-!
# Puiseux series as a colimit of ramified Laurent fields

Ramified Laurent levels are indexed by `TauCeti.RamificationIndex`, the positive natural numbers
ordered by divisibility. The transition from level `n` to level `m`, for `n ∣ m`, substitutes
`X ^ (m / n)` for `X`. These transitions form a filtered diagram of commutative algebras over the
coefficient field.

The level embeddings into the Puiseux series field form a cocone on this diagram. This file
proves its universal property: a compatible family of algebra maps out of all ramified levels
factors uniquely through the Puiseux field. Thus the bounded-denominator carrier of Puiseux
series is not merely the union of the levels; it is their colimit in commutative algebras.

## Main definitions

* `TauCeti.puiseuxField.levelDiagram`: the diagram whose transition maps are ramified
  substitutions.
* `TauCeti.puiseuxField.levelCocone`: the level embeddings into the Puiseux field.
* `TauCeti.puiseuxField.levelCoconeIsColimit`: the universal property of that cocone.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped LaurentSeries

namespace TauCeti

namespace puiseuxField

variable (K : Type*) [Field K]

/-- The filtered diagram of ramified Laurent fields.  Its object at `n` is a copy of `K⸨X⸩`,
and its map along `n ≤ m` substitutes `X ^ (m / n)` for `X`. -/
@[expose]
noncomputable def levelDiagram : RamificationIndex ⥤ CommAlgCat K where
  obj _ := CommAlgCat.of K (LaurentSeries K)
  map {n m} f := CommAlgCat.ofHom
    (LaurentSeries.expand K (RamificationIndex.transitionDegree f.le))
  map_id n := by
    apply CommAlgCat.hom_ext
    ext x
    simp [RamificationIndex.transitionDegree_refl]
  map_comp {n m l} f g := by
    apply CommAlgCat.hom_ext
    ext x
    simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.coe_comp, Function.comp_apply]
    rw [LaurentSeries.expand_expand, mul_comm,
      RamificationIndex.transitionDegree_trans f.le g.le]

/-- The object at every ramification index is the Laurent-series `K`-algebra. -/
@[simp]
theorem levelDiagram_obj (n : RamificationIndex) :
    (levelDiagram K).obj n = CommAlgCat.of K (LaurentSeries K) := rfl

/-- The transition map along `n ≤ m` is the substitution `X ↦ X ^ (m / n)`. -/
@[simp]
theorem levelDiagram_map_hom {n m : RamificationIndex} (f : n ⟶ m) :
    ((levelDiagram K).map f).hom =
      LaurentSeries.expand K (RamificationIndex.transitionDegree f.le) := rfl

variable {K} in
/-- Moving a level-`n` series to level `m` along `X ↦ X ^ (m / n)` does not change its image in
the Puiseux field. -/
theorem levelEmbedding_expand_transitionDegree {n m : RamificationIndex} (h : n ≤ m)
    (f : LaurentSeries K) :
    levelEmbedding K m.toPNat
      (LaurentSeries.expand K (RamificationIndex.transitionDegree h) f) =
        levelEmbedding K n.toPNat f := by
  rw [← RamificationIndex.mul_transitionDegree h]
  exact levelEmbedding_expand n.toPNat (RamificationIndex.transitionDegree h) f

/-- The level embeddings into the Puiseux field, as a cocone on the ramified-level diagram. -/
@[expose]
noncomputable def levelCocone : Cocone (levelDiagram K) where
  pt := CommAlgCat.of K (puiseuxField K)
  ι :=
    { app := fun n ↦ CommAlgCat.ofHom (levelEmbedding K n.toPNat)
      naturality := fun {n m} f ↦ by
        apply CommAlgCat.hom_ext
        -- Unfold the objects to their carriers so that the `CommAlgCat` hom lemmas typecheck.
        dsimp only [levelDiagram, Functor.const_obj_obj]
        simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, Functor.const_obj_map,
          CommAlgCat.hom_id, AlgHom.id_comp]
        exact AlgHom.ext (levelEmbedding_expand_transitionDegree f.le) }

/-- The point of the level cocone is the Puiseux field. -/
@[simp]
theorem levelCocone_pt : (levelCocone K).pt = CommAlgCat.of K (puiseuxField K) := rfl

/-- The component of the level cocone at `n` is the level-`n` embedding. -/
@[simp]
theorem levelCocone_ι_app_hom (n : RamificationIndex) :
    ((levelCocone K).ι.app n).hom = levelEmbedding K n.toPNat := rfl

variable {K}

private theorem cocone_app_eq_of_levelEmbedding_eq (s : Cocone (levelDiagram K))
    {n m : RamificationIndex} {f g : LaurentSeries K}
    (hfg : levelEmbedding K n.toPNat f = levelEmbedding K m.toPNat g) :
    s.ι.app n f = s.ι.app m g := by
  obtain ⟨l, hnl, hml⟩ := exists_ge_ge n m
  have heq : LaurentSeries.expand K (RamificationIndex.transitionDegree hnl) f =
      LaurentSeries.expand K (RamificationIndex.transitionDegree hml) g := by
    apply (levelEmbedding K l.toPNat).injective
    exact (levelEmbedding_expand_transitionDegree hnl f).trans
      (hfg.trans (levelEmbedding_expand_transitionDegree hml g).symm)
  rw [← s.w_apply (homOfLE hnl) f, ← s.w_apply (homOfLE hml) g]
  dsimp only [levelDiagram]
  simp only [ConcreteCategory.hom_ofHom]
  exact congrArg (s.ι.app l) heq

private noncomputable def chosenIndex (x : puiseuxField K) : RamificationIndex :=
  ⟨Classical.choose (exists_mem_range_levelEmbedding x)⟩

private noncomputable def chosenPreimage (x : puiseuxField K) : LaurentSeries K :=
  Classical.choose (Classical.choose_spec (exists_mem_range_levelEmbedding x))

private theorem levelEmbedding_chosenPreimage (x : puiseuxField K) :
    levelEmbedding K (chosenIndex x).toPNat (chosenPreimage x) = x :=
  Classical.choose_spec (Classical.choose_spec (exists_mem_range_levelEmbedding x))

private noncomputable def levelDescFun (s : Cocone (levelDiagram K))
    (x : puiseuxField K) : s.pt :=
  s.ι.app (chosenIndex x) (chosenPreimage x)

private theorem levelDescFun_levelEmbedding (s : Cocone (levelDiagram K))
    (n : RamificationIndex) (f : LaurentSeries K) :
    levelDescFun s (levelEmbedding K n.toPNat f) = s.ι.app n f := by
  apply cocone_app_eq_of_levelEmbedding_eq s
  exact levelEmbedding_chosenPreimage _

private theorem levelDescFun_zero (s : Cocone (levelDiagram K)) : levelDescFun s 0 = 0 := by
  rw [← map_zero (levelEmbedding K (1 : ℕ+)), levelDescFun_levelEmbedding]
  exact map_zero (s.ι.app ⟨1⟩).hom

private theorem levelDescFun_one (s : Cocone (levelDiagram K)) : levelDescFun s 1 = 1 := by
  rw [← map_one (levelEmbedding K (1 : ℕ+)), levelDescFun_levelEmbedding]
  exact map_one (s.ι.app ⟨1⟩).hom

/-- Any two Puiseux series come from a common ramified level. -/
private theorem exists_levelEmbedding_eq_and_eq (x y : puiseuxField K) :
    ∃ (l : RamificationIndex) (f g : LaurentSeries K),
      levelEmbedding K l.toPNat f = x ∧ levelEmbedding K l.toPNat g = y := by
  obtain ⟨l, hl⟩ := exists_forall_mem_range_levelEmbedding ![x, y]
  obtain ⟨f, hf⟩ := hl 0
  obtain ⟨g, hg⟩ := hl 1
  exact ⟨⟨l⟩, f, g, hf, hg⟩

private theorem levelDescFun_add (s : Cocone (levelDiagram K)) (x y : puiseuxField K) :
    levelDescFun s (x + y) = levelDescFun s x + levelDescFun s y := by
  obtain ⟨l, f, g, rfl, rfl⟩ := exists_levelEmbedding_eq_and_eq x y
  rw [← map_add, levelDescFun_levelEmbedding, levelDescFun_levelEmbedding,
    levelDescFun_levelEmbedding]
  exact map_add _ _ _

private theorem levelDescFun_mul (s : Cocone (levelDiagram K)) (x y : puiseuxField K) :
    levelDescFun s (x * y) = levelDescFun s x * levelDescFun s y := by
  obtain ⟨l, f, g, rfl, rfl⟩ := exists_levelEmbedding_eq_and_eq x y
  rw [← map_mul, levelDescFun_levelEmbedding, levelDescFun_levelEmbedding,
    levelDescFun_levelEmbedding]
  exact map_mul _ _ _

private theorem levelDescFun_commutes (s : Cocone (levelDiagram K)) (r : K) :
    levelDescFun s (algebraMap K (puiseuxField K) r) = algebraMap K s.pt r := by
  rw [← (levelEmbedding K (1 : ℕ+)).commutes r, levelDescFun_levelEmbedding]
  exact (s.ι.app ⟨1⟩).hom.commutes r

private noncomputable def levelDesc (s : Cocone (levelDiagram K)) :
    puiseuxField K →ₐ[K] s.pt where
  toFun := levelDescFun s
  map_zero' := levelDescFun_zero s
  map_one' := levelDescFun_one s
  map_add' := levelDescFun_add s
  map_mul' := levelDescFun_mul s
  commutes' := levelDescFun_commutes s

@[simp]
private theorem levelDesc_levelEmbedding (s : Cocone (levelDiagram K))
    (n : RamificationIndex) (f : LaurentSeries K) :
    levelDesc s (levelEmbedding K n.toPNat f) = s.ι.app n f :=
  levelDescFun_levelEmbedding s n f

/-- The Puiseux field is the colimit of the ramified Laurent levels in `CommAlgCat K`.

Equivalently, every compatible family of `K`-algebra maps from the levels factors uniquely
through the bounded-denominator Puiseux series field. -/
noncomputable def levelCoconeIsColimit : IsColimit (levelCocone K) where
  desc s := CommAlgCat.ofHom (levelDesc s)
  fac s n := by
    apply CommAlgCat.hom_ext
    dsimp only [levelCocone, levelDiagram, Functor.const_obj_obj]
    rw [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, CommAlgCat.hom_ofHom]
    exact AlgHom.ext (levelDesc_levelEmbedding s n)
  uniq s g hg := by
    apply CommAlgCat.hom_ext
    ext x
    obtain ⟨n, f, rfl⟩ := exists_mem_range_levelEmbedding x
    let ri : RamificationIndex := ⟨n⟩
    calc
      -- The left side is `((levelCocone K).ι.app ri ≫ g) f` with the cocone leg unfolded.
      g (levelEmbedding K n f) = s.ι.app ri f := ConcreteCategory.congr_hom (hg ri) f
      _ = levelDesc s (levelEmbedding K n f) := (levelDesc_levelEmbedding s ri f).symm

end puiseuxField

end TauCeti
