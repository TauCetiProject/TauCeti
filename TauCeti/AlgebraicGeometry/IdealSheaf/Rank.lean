/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.Rank

/-!
# Ranks of finite flat closed subschemes

An inclusion of closed subschemes finite and flat over the same base is equality when their
rank functions agree. In ideal-sheaf notation the direction of containment is reversed:
`I ≤ J` gives the closed immersion `J.subscheme ⟶ I.subscheme`.

The intersection of two closed subschemes `V(I)` and `V(J)` of `X` can be cut out inside either
of them: as the inverse image `V(I) ∩ V(J) = V(I.comap ι_J)` of `V(I)` in `V(J)`, or as the inverse
image `V(J.comap ι_I)` of `V(J)` in `V(I)`. Both are the fibre product `V(I) ×_X V(J)`, so when
`V(I)` and `V(J)` map to a base compatibly on their intersection, the two descriptions have the
same rank over the base (`Scheme.IdealSheafData.finrank_comap_subschemeι_comm`). For two curves on
a surface, this is the symmetry of the length of their scheme-theoretic intersection.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.eq_of_le_of_finrank_eq`: comparable ideal sheaves
  cutting out finite flat schemes of the same rank are equal;
* `AlgebraicGeometry.Scheme.IdealSheafData.finrank_comap_subschemeι_comm`: the rank of
  `V(I) ∩ V(J)` does not depend on which of the two subschemes it is cut out in.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X S : Scheme.{u}}

/-- Comparable ideal sheaves cutting out finite flat schemes of the same rank over the base
are equal. -/
theorem eq_of_le_of_finrank_eq {I J : X.IdealSheafData} (h : I ≤ J) (f : X ⟶ S)
    [IsFinite (I.subschemeι ≫ f)] [Flat (I.subschemeι ≫ f)]
    [Flat (J.subschemeι ≫ f)]
    (hrank : (I.subschemeι ≫ f).finrank = (J.subschemeι ≫ f).finrank) : I = J := by
  have : IsClosedImmersion (inclusion h ≫ I.subschemeι) := by
    rw [inclusion_subschemeι]; infer_instance
  have : IsClosedImmersion (inclusion h) :=
    IsClosedImmersion.of_comp_isClosedImmersion (inclusion h) I.subschemeι
  have : Flat (inclusion h ≫ I.subschemeι ≫ f) := by
    rw [← Category.assoc, inclusion_subschemeι]; infer_instance
  have : IsIso (inclusion h) :=
    ((inclusion h).isIso_iff_finrank_comp_eq (I.subschemeι ≫ f)).mpr (by
      rw [← Category.assoc, inclusion_subschemeι]; exact hrank.symm)
  rw [← ker_subschemeι I, ← ker_subschemeι J, ← inclusion_subschemeι h,
    Hom.ker_comp_of_isIso]

/-- **The intersection of two closed subschemes is symmetric.** Let `V(I)` and `V(J)` be closed
subschemes of `X` mapping to a base `S` by `f` and `g`, compatibly on their fibre product. Then the
inverse image of `V(I)` in `V(J)` and the inverse image of `V(J)` in `V(I)`, both the intersection
`V(I) ∩ V(J)`, have the same rank over `S` when one of them is finite and flat over `S`. -/
theorem finrank_comap_subschemeι_comm {I J : X.IdealSheafData} (f : I.subscheme ⟶ S)
    (g : J.subscheme ⟶ S)
    (w : pullback.fst J.subschemeι I.subschemeι ≫ g = pullback.snd J.subschemeι I.subschemeι ≫ f)
    [IsFinite ((J.comap I.subschemeι).subschemeι ≫ f)]
    [Flat ((J.comap I.subschemeι).subschemeι ≫ f)] :
    ((I.comap J.subschemeι).subschemeι ≫ g).finrank =
      ((J.comap I.subschemeι).subschemeι ≫ f).finrank := by
  -- Both inverse images are identified with the fibre product `V(J) ×_X V(I)`.
  let e := (I.comapIso J.subschemeι).hom ≫ (pullbackSymmetry _ _).hom ≫
    (J.comapIso I.subschemeι).inv
  have he : e ≫ (J.comap I.subschemeι).subschemeι ≫ f =
      (I.comap J.subschemeι).subschemeι ≫ g := by
    simp only [e, Category.assoc, comapIso_inv_subschemeι_assoc,
      pullbackSymmetry_hom_comp_fst_assoc, ← w, comapIso_hom_fst_assoc]
  rw [← he, Hom.finrank_comp_left_of_isIso]

end AlgebraicGeometry.Scheme.IdealSheafData
