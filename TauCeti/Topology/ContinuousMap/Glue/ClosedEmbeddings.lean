/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Gluing continuous maps along two closed embeddings

Let `i : X₁ → Y` and `j : X₂ → Y` be closed embeddings whose ranges cover `Y`. Continuous maps
`a : C(X₁, Z)` and `b : C(X₂, Z)` that agree wherever `i x = j p` glue to a continuous map on `Y`,
`ContinuousMap.glueClosedEmbeddings`, restricting to `a` along `i` and to `b` along `j`. It is the
only such map (`ContinuousMap.eq_glueClosedEmbeddings`), since a continuous map on `Y` is
determined by its restrictions to the two pieces (`ContinuousMap.ext_of_range_union_range`).

This is the universal property of a space recorded as the union of two closed pieces, as in
`TauCeti.DehnFilling` and `TauCeti.SphereSurgery`. Mathlib's `ContinuousMap.liftCover` needs a
cover by neighbourhoods of every point, which two closed sets need not be.

## Main definitions

* `ContinuousMap.glueClosedEmbeddings`: the glued map, with the evaluation lemmas
  `ContinuousMap.glueClosedEmbeddings_apply_left` and
  `ContinuousMap.glueClosedEmbeddings_apply_right`.

## Main results

* `ContinuousMap.ext_of_range_union_range`: continuous maps agreeing along two maps whose ranges
  cover are equal.
* `ContinuousMap.eq_glueClosedEmbeddings`: uniqueness of the glued map.
-/

public section

noncomputable section

open Set Topology

namespace ContinuousMap

variable {X₁ X₂ Y Z : Type*} [TopologicalSpace Y] {i : X₁ → Y} {j : X₂ → Y}

/-- **Continuous maps agreeing along two maps whose ranges cover are equal.** -/
theorem ext_of_range_union_range [TopologicalSpace Z] {f g : C(Y, Z)}
    (hij : range i ∪ range j = univ) (hi : ∀ x, f (i x) = g (i x)) (hj : ∀ p, f (j p) = g (j p)) :
    f = g := by
  ext y
  obtain ⟨x, rfl⟩ | ⟨p, rfl⟩ := hij.symm ▸ mem_univ y
  exacts [hi x, hj p]

variable [TopologicalSpace X₁] [TopologicalSpace X₂]

/-- The function underlying `ContinuousMap.glueClosedEmbeddings`: `a` on the range of `i` and `b`
on the range of `j`, glued over the cover of `Y` by the two ranges. -/
private def glueFun {a : X₁ → Z} {b : X₂ → Z} (hi : IsEmbedding i) (hj : IsEmbedding j)
    (hij : range i ∪ range j = univ) (hab : ∀ x p, i x = j p → a x = b p) : Y → Z :=
  liftCover (fun k ↦ cond k (range i) (range j))
    (fun k ↦ match k with
      | true => a ∘ hi.toHomeomorph.symm
      | false => b ∘ hj.toHomeomorph.symm)
    (by
      have key (y : Y) (hy : y ∈ range i) (hy' : y ∈ range j) :
          a (hi.toHomeomorph.symm ⟨y, hy⟩) = b (hj.toHomeomorph.symm ⟨y, hy'⟩) :=
        hab _ _ ((congrArg Subtype.val (hi.toHomeomorph.apply_symm_apply ⟨y, hy⟩)).trans
          (congrArg Subtype.val (hj.toHomeomorph.apply_symm_apply ⟨y, hy'⟩)).symm)
      rintro (_ | _) (_ | _) y hk hk'
      exacts [rfl, (key y hk' hk).symm, key y hk hk', rfl])
    (union_eq_iUnion.symm.trans hij)

private theorem glueFun_apply_left {a : X₁ → Z} {b : X₂ → Z} (hi : IsEmbedding i)
    (hj : IsEmbedding j) (hij : range i ∪ range j = univ) (hab : ∀ x p, i x = j p → a x = b p)
    (x : X₁) : glueFun hi hj hij hab (i x) = a x :=
  (liftCover_of_mem (i := true) (mem_range_self x)).trans
    (congrArg a (IsEmbedding.toHomeomorph_symm_apply _ x))

private theorem glueFun_apply_right {a : X₁ → Z} {b : X₂ → Z} (hi : IsEmbedding i)
    (hj : IsEmbedding j) (hij : range i ∪ range j = univ) (hab : ∀ x p, i x = j p → a x = b p)
    (p : X₂) : glueFun hi hj hij hab (j p) = b p :=
  (liftCover_of_mem (i := false) (mem_range_self p)).trans
    (congrArg b (IsEmbedding.toHomeomorph_symm_apply _ p))

variable [TopologicalSpace Z]

/-- **Gluing along two closed embeddings.** Continuous maps `a` and `b` on the sources of closed
embeddings `i` and `j` whose ranges cover `Y`, agreeing wherever `i x = j p`, glue to a continuous
map on `Y` (`ContinuousMap.eq_glueClosedEmbeddings`). -/
def glueClosedEmbeddings (a : C(X₁, Z)) (b : C(X₂, Z)) (hi : IsClosedEmbedding i)
    (hj : IsClosedEmbedding j) (hij : range i ∪ range j = univ)
    (hab : ∀ x p, i x = j p → a x = b p) : C(Y, Z) where
  toFun := glueFun hi.isEmbedding hj.isEmbedding hij hab
  continuous_toFun := by
    have hI : ContinuousOn (glueFun hi.isEmbedding hj.isEmbedding hij hab) (range i) := by
      rw [← image_univ, hi.isInducing.continuousOn_image_iff]
      exact (continuous_congr (glueFun_apply_left _ _ hij hab)).2 a.continuous |>.continuousOn
    have hJ : ContinuousOn (glueFun hi.isEmbedding hj.isEmbedding hij hab) (range j) := by
      rw [← image_univ, hj.isInducing.continuousOn_image_iff]
      exact (continuous_congr (glueFun_apply_right _ _ hij hab)).2 b.continuous |>.continuousOn
    rw [← continuousOn_univ, ← hij]
    exact hI.union_of_isClosed hJ hi.isClosed_range hj.isClosed_range

variable (a : C(X₁, Z)) (b : C(X₂, Z)) (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j)
  (hij : range i ∪ range j = univ) (hab : ∀ x p, i x = j p → a x = b p)

/-- The glued map restricts to `a` along `i`. -/
@[simp]
theorem glueClosedEmbeddings_apply_left (x : X₁) :
    glueClosedEmbeddings a b hi hj hij hab (i x) = a x :=
  glueFun_apply_left hi.isEmbedding hj.isEmbedding hij hab x

/-- The glued map restricts to `b` along `j`. -/
@[simp]
theorem glueClosedEmbeddings_apply_right (p : X₂) :
    glueClosedEmbeddings a b hi hj hij hab (j p) = b p :=
  glueFun_apply_right hi.isEmbedding hj.isEmbedding hij hab p

variable {a b hi hj hij hab} in
/-- **Uniqueness of the glued map**: a continuous map on `Y` restricting to `a` along `i` and to
`b` along `j` is `ContinuousMap.glueClosedEmbeddings`. -/
theorem eq_glueClosedEmbeddings {f : C(Y, Z)} (hfi : ∀ x, f (i x) = a x)
    (hfj : ∀ p, f (j p) = b p) : f = glueClosedEmbeddings a b hi hj hij hab :=
  ext_of_range_union_range hij (by simpa using hfi) (by simpa using hfj)

end ContinuousMap
