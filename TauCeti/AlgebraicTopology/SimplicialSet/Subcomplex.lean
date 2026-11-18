/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Subcomplexes transported along isomorphisms

An isomorphism `e : X ≅ Y` of simplicial sets carries a subcomplex `A` of `X` to the subcomplex
`A.preimage e.inv` of `Y`, and the inclusions of the two subcomplexes are isomorphic arrows. Hence
any class of morphisms that respects isomorphisms, such as the (inner) anodyne extensions, contains
one inclusion exactly when it contains the other.

## Main results

* `SSet.Subcomplex.isoOfPreimageEq`: for `A.preimage e.inv = B`, the restriction of `e` to an
  isomorphism `(A : SSet) ≅ B`, compatible with the inclusions.
* `SSet.Subcomplex.morphismProperty_ι_iff_of_preimage_eq`: for `A.preimage e.inv = B` and a class
  `W` of morphisms respecting isomorphisms, `W A.ι ↔ W B.ι`.
-/

public section

open CategoryTheory

universe u

namespace SSet.Subcomplex

variable {X Y : SSet.{u}}

/-- If an isomorphism `e : X ≅ Y` carries a subcomplex `A` of `X` to a subcomplex `B` of `Y`, it
restricts to an isomorphism between `A` and `B`. -/
def isoOfPreimageEq (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex} (h : A.preimage e.inv = B) :
    (A : SSet) ≅ B where
  hom := homOfLE (by rw [← h, ← preimage_comp, e.hom_inv_id, preimage_id]) ≫ fromPreimage _ e.hom
  inv := homOfLE h.ge ≫ fromPreimage _ e.inv
  hom_inv_id := by
    rw [← cancel_mono A.ι]
    simp
  inv_hom_id := by
    rw [← cancel_mono B.ι]
    simp

section

variable (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex} (h : A.preimage e.inv = B)

/-- The restriction of `e` to `A ≅ B` commutes with the inclusions and `e.hom`. -/
@[reassoc (attr := simp)]
lemma isoOfPreimageEq_hom_ι : (isoOfPreimageEq e h).hom ≫ B.ι = A.ι ≫ e.hom := by
  simp [isoOfPreimageEq]

/-- The restriction of `e` to `A ≅ B` commutes with the inclusions and `e.inv`. -/
@[reassoc (attr := simp)]
lemma isoOfPreimageEq_inv_ι : (isoOfPreimageEq e h).inv ≫ A.ι = B.ι ≫ e.inv := by
  simp [isoOfPreimageEq]

end

/-- If an isomorphism `e : X ≅ Y` carries a subcomplex `A` of `X` to a subcomplex `B` of `Y`, then a
class of morphisms respecting isomorphisms contains the inclusion of `A` exactly when it contains
the inclusion of `B`. -/
lemma morphismProperty_ι_iff_of_preimage_eq (W : MorphismProperty SSet.{u}) [W.RespectsIso]
    (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex} (h : A.preimage e.inv = B) :
    W A.ι ↔ W B.ι :=
  W.arrow_mk_iso_iff (Arrow.isoMk (isoOfPreimageEq e h) e (isoOfPreimageEq_hom_ι e h))

end SSet.Subcomplex
