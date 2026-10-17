/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux

/-!
# Puiseux series as a colimit of ramified Laurent fields

Ramified Laurent levels are indexed by positive natural numbers ordered by divisibility. The
transition from level `n` to level `m`, for `n ∣ m`, substitutes `X ^ (m / n)` for `X`. These
transitions form a filtered diagram of commutative algebras over the coefficient field.

The level embeddings into the Puiseux series field form a cocone on this diagram. This file
proves its universal property: a compatible family of algebra maps out of all ramified levels
factors uniquely through the Puiseux field. Thus the bounded-denominator carrier of Puiseux
series is not merely the union of the levels; it is their colimit in commutative algebras.

## Main definitions

* `TauCeti.RamificationIndex`: positive natural numbers ordered by divisibility.
* `TauCeti.puiseuxField.levelDiagram`: the diagram whose transition maps are ramified
  substitutions.
* `TauCeti.puiseuxField.levelCocone`: the level embeddings into the Puiseux field.
* `TauCeti.puiseuxField.levelCoconeIsColimit`: the universal property of that cocone.
-/

public section

open CategoryTheory CategoryTheory.Limits
open scoped LaurentSeries

namespace TauCeti

/-- Positive ramification indices, ordered by divisibility rather than by their usual order. -/
@[ext]
structure RamificationIndex where
  /-- The positive natural number underlying a ramification index. -/
  toPNat : ℕ+

namespace RamificationIndex

instance : LE RamificationIndex := ⟨fun n m ↦ n.toPNat ∣ m.toPNat⟩

/-- Comparison of ramification indices is divisibility of the underlying positive integers. -/
@[simp]
theorem le_iff_dvd {n m : RamificationIndex} : n ≤ m ↔ n.toPNat ∣ m.toPNat := Iff.rfl

instance : PartialOrder RamificationIndex where
  le := (· ≤ ·)
  le_refl n := dvd_refl n.toPNat
  le_trans _ _ _ := dvd_trans
  le_antisymm _ _ hnm hmn := RamificationIndex.ext (PNat.dvd_antisymm hnm hmn)

instance : IsDirectedOrder RamificationIndex where
  directed n m := ⟨⟨n.toPNat * m.toPNat⟩, ⟨m.toPNat, rfl⟩,
    ⟨n.toPNat, mul_comm _ _⟩⟩

/-- The quotient `m / n` attached to a divisibility relation `n ≤ m`. -/
def transitionDegree {n m : RamificationIndex} (_h : n ≤ m) : ℕ+ :=
  PNat.divExact m.toPNat n.toPNat

/-- Multiplying an index by its transition degree recovers the target index. -/
theorem mul_transitionDegree {n m : RamificationIndex} (h : n ≤ m) :
    n.toPNat * transitionDegree h = m.toPNat :=
  PNat.mul_div_exact h

@[simp]
theorem transitionDegree_refl (n : RamificationIndex) :
    transitionDegree (le_refl n) = 1 := by
  apply mul_left_cancel (a := n.toPNat)
  rw [mul_transitionDegree, mul_one]

/-- Transition degrees multiply along a chain of ramification indices. -/
theorem transitionDegree_trans {n m l : RamificationIndex} (hnm : n ≤ m) (hml : m ≤ l) :
    transitionDegree hnm * transitionDegree hml = transitionDegree (hnm.trans hml) := by
  apply mul_left_cancel (a := n.toPNat)
  calc
    n.toPNat * (transitionDegree hnm * transitionDegree hml) =
        (n.toPNat * transitionDegree hnm) * transitionDegree hml := (mul_assoc _ _ _).symm
    _ = m.toPNat * transitionDegree hml := by rw [mul_transitionDegree hnm]
    _ = l.toPNat := mul_transitionDegree hml
    _ = n.toPNat * transitionDegree (hnm.trans hml) :=
      (mul_transitionDegree (hnm.trans hml)).symm

end RamificationIndex

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
        ext x
        exact levelEmbedding_expand_transitionDegree f.le x }

/-- The point of the level cocone is the Puiseux field. -/
@[simp]
theorem levelCocone_pt : (levelCocone K).pt = CommAlgCat.of K (puiseuxField K) := rfl

/-- The component of the level cocone at `n` is the level-`n` embedding. -/
@[simp]
theorem levelCocone_ι_app_hom (n : RamificationIndex) :
    ((levelCocone K).ι.app n).hom = levelEmbedding K n.toPNat := rfl

variable {K}

private theorem cocone_app_transition (s : Cocone (levelDiagram K))
    {n m : RamificationIndex} (h : n ≤ m) (f : LaurentSeries K) :
    s.ι.app n f =
      s.ι.app m (LaurentSeries.expand K (RamificationIndex.transitionDegree h) f) := by
  have hw := congrArg CommAlgCat.Hom.hom (s.w (homOfLE h))
  exact (DFunLike.congr_fun hw f).symm

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
  rw [cocone_app_transition s hnl f, cocone_app_transition s hml g, heq]

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
    ext f
    exact levelDesc_levelEmbedding s n f
  uniq s g hg := by
    apply CommAlgCat.hom_ext
    ext x
    obtain ⟨n, f, rfl⟩ := exists_mem_range_levelEmbedding x
    let ri : RamificationIndex := ⟨n⟩
    calc
      g (levelEmbedding K n f) = s.ι.app ri f := by
        have h := congrArg CommAlgCat.Hom.hom (hg ri)
        exact DFunLike.congr_fun h f
      _ = levelDesc s (levelEmbedding K n f) := (levelDesc_levelEmbedding s ri f).symm

end puiseuxField

end TauCeti
