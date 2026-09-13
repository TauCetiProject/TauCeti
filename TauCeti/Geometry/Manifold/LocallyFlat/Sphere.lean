/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Brown's bicollaring theorem for locally flat spheres

A locally flat codimension-one sphere in a sphere has a global bicollar.  This is the global
collaring theorem that turns the local product charts in `TauCeti.IsLocallyFlat` into one product
neighbourhood of the entire embedded sphere.  It is the structural input to the annulus theorem:
the collar presents a whole neighbourhood of the sphere as a product, which is what identifies
the regions adjacent to it.  It is that global bicollar that wild embeddings such as the
Alexander horned sphere fail to admit.

This file records Brown's theorem as the dimension-indexed proposition
`TauCeti.BrownBicollaring`.  The theorem is stated rather than proved.

The indexing uses an `n`-sphere in `EuclideanSpace ℝ (Fin (n + 1))` embedded in the
`(n + 1)`-sphere in `EuclideanSpace ℝ (Fin (n + 2))`.  Local flatness is read in the split
ambient model `EuclideanSpace ℝ (Fin n) × ℝ`: the first factor is the model of the source
sphere, and the second is its one-dimensional normal direction.  No orientation or choice of
side is included in the statement.

## Main definitions

* `TauCeti.BrownBicollaring`: every locally flat embedding `Sⁿ → Sⁿ⁺¹` is globally
  bicollared.

## Main results

* `TauCeti.brownBicollaring_iff`: the defining characterization of Brown's theorem.
* `TauCeti.BrownBicollaring.exists_isOpen_sdiff_range_eq_union`: granting Brown's theorem, a
  locally flat sphere is two-sided, so it separates a neighbourhood of itself into two disjoint
  nonempty open sides.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* R. J. Daverman and G. A. Venema, *Embeddings in Manifolds*, Graduate Studies in Mathematics
  106, American Mathematical Society (2009), Chapter 2.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set
open Topology
open scoped EuclideanSpace

/-- **Brown's bicollaring theorem in dimension `n`:** every locally flat embedding of the
standard `n`-sphere in the standard `(n + 1)`-sphere admits a global bicollar.

The local-flatness model is `EuclideanSpace ℝ (Fin n) × ℝ`: its zero slice has dimension
`n`, and its complementary factor has dimension one.  Thus the hypothesis says precisely that
the embedding is locally a codimension-one coordinate slice.  The conclusion is the existence of
an open embedding `Sⁿ × ℝ → Sⁿ⁺¹` whose zero slice is the original embedding. -/
def BrownBicollaring (n : ℕ) : Prop :=
  ∀ f :
      sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
        sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
    IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f → IsBicollared f

/-- The defining characterization of Brown's bicollaring theorem.  The module system does not
expose the body of `TauCeti.BrownBicollaring`, so a downstream file cannot unfold it; this lemma
is how the proposition is introduced and eliminated there. -/
@[simp]
theorem brownBicollaring_iff {n : ℕ} :
    BrownBicollaring n ↔
      ∀ f :
          sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
            sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1,
        IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f → IsBicollared f :=
  by rfl

/-- Granting Brown's theorem, a locally flat `n`-sphere in the `(n + 1)`-sphere is **two-sided**:
it has an open neighbourhood whose complement in that neighbourhood is the union of two disjoint
nonempty open sets, the two sides of the collar the theorem provides.  This is the separation
statement the annulus theorem consumes.  What local flatness supplies is the collar, not the
separation on its own: a wild embedding such as the Alexander horned sphere admits no global
bicollar, even though its complement is still a union of two open regions. -/
theorem BrownBicollaring.exists_isOpen_sdiff_range_eq_union {n : ℕ} (h : BrownBicollaring n)
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 →
      sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1)
    (hf : IsLocallyFlat (EuclideanSpace ℝ (Fin n)) ℝ f) :
    ∃ U V W : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1),
      IsOpen U ∧ IsOpen V ∧ IsOpen W ∧ range f ⊆ U ∧ V.Nonempty ∧ W.Nonempty ∧
        Disjoint V W ∧ U \ range f = V ∪ W := by
  obtain ⟨b, hb⟩ := isBicollared_iff.mp (h f hf)
  obtain ⟨x, hx⟩ : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).Nonempty :=
    NormedSpace.sphere_nonempty.2 zero_le_one
  exact ⟨range b, b '' (univ ×ˢ Ioi 0), b '' (univ ×ˢ Iio 0),
    hb.isOpenEmbedding.isOpen_range,
    hb.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Ioi),
    hb.isOpenEmbedding.isOpenMap _ (isOpen_univ.prod isOpen_Iio),
    hb.range_subset_range,
    ⟨b (⟨x, hx⟩, 1), mem_image_of_mem _ ⟨mem_univ _, mem_Ioi.2 one_pos⟩⟩,
    ⟨b (⟨x, hx⟩, -1), mem_image_of_mem _ ⟨mem_univ _, mem_Iio.2 (by norm_num)⟩⟩,
    hb.disjoint_image_Ioi_Iio, hb.range_diff_range_eq_union⟩

end TauCeti
