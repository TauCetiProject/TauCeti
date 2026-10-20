/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Basic
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
@[simp]
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

variable (K) in
/-- The image of level `n` in the Puiseux field, as a `K`-subalgebra. -/
private noncomputable abbrev levelRange (n : RamificationIndex) : Subalgebra K (puiseuxField K) :=
  (levelEmbedding K n.toPNat).range

private theorem directed_levelRange : Directed (· ≤ ·) (levelRange K) :=
  Monotone.directed_le fun _ _ h ↦ range_levelEmbedding_le_of_dvd h

private theorem top_le_iSup_levelRange :
    (⊤ : Subalgebra K (puiseuxField K)) ≤ ⨆ n, levelRange K n := fun x _ ↦
  have ⟨n, hn⟩ := exists_mem_range_levelEmbedding x
  le_iSup (levelRange K) (⟨n⟩ : RamificationIndex) hn

variable (K) in
/-- The level-`n` embedding, as an isomorphism onto its image. -/
private noncomputable abbrev levelRangeEquiv (n : RamificationIndex) :
    LaurentSeries K ≃ₐ[K] levelRange K n :=
  AlgEquiv.ofInjective _ (levelEmbedding K n.toPNat).injective

private theorem levelEmbedding_levelRangeEquiv_symm {n : RamificationIndex} (x : levelRange K n) :
    levelEmbedding K n.toPNat ((levelRangeEquiv K n).symm x) = x :=
  congrArg Subtype.val ((levelRangeEquiv K n).apply_symm_apply x)

/-- The leg of a cocone at `n`, transported to the image of level `n`. -/
private noncomputable def levelRangeLift (s : Cocone (levelDiagram K)) (n : RamificationIndex) :
    levelRange K n →ₐ[K] s.pt :=
  (s.ι.app n).hom.comp (levelRangeEquiv K n).symm.toAlgHom

private noncomputable def levelDesc (s : Cocone (levelDiagram K)) :
    puiseuxField K →ₐ[K] s.pt :=
  (Subalgebra.iSupLift (levelRange K) directed_levelRange (levelRangeLift s)
      (fun _ _ h ↦ AlgHom.ext fun x ↦ cocone_app_eq_of_levelEmbedding_eq s
        ((levelEmbedding_levelRangeEquiv_symm x).trans
          (levelEmbedding_levelRangeEquiv_symm (Subalgebra.inclusion h x)).symm))
      ⊤ top_le_iSup_levelRange).comp
    Subalgebra.topEquiv.symm.toAlgHom

private theorem levelDesc_levelEmbedding (s : Cocone (levelDiagram K))
    (n : RamificationIndex) (f : LaurentSeries K) :
    levelDesc s (levelEmbedding K n.toPNat f) = s.ι.app n f := by
  rw [levelDesc, AlgHom.comp_apply]
  refine (Subalgebra.iSupLift_of_mem (levelRange K) (i := n) _ ⟨f, rfl⟩).trans ?_
  exact cocone_app_eq_of_levelEmbedding_eq s (levelEmbedding_levelRangeEquiv_symm _)

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
