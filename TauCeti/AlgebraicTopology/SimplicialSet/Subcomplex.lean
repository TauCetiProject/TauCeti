/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Subcomplexes transported along isomorphisms, and the empty subcomplex

An isomorphism `e : X ≅ Y` of simplicial sets carries a subcomplex `A` of `X` to the subcomplex
`A.preimage e.inv` of `Y`, and the inclusions of the two subcomplexes are isomorphic arrows. Hence
any class of morphisms that respects isomorphisms, such as the (inner) anodyne extensions, contains
one inclusion exactly when it contains the other. Likewise, two monomorphisms into the same
simplicial set with the same range have isomorphic sources, compatibly with the monomorphisms.

The empty subcomplex `⊥` has no simplices, so it is not `Nonempty`; for instance, slices and
coslices over a diagram restricted to `⊥` are the whole simplicial set.

## Main results

* `SSet.Subcomplex.isoOfPreimageEq`: for `A.preimage e.inv = B`, the restriction of `e` to an
  isomorphism `(A : SSet) ≅ B`, compatible with the inclusions.
* `SSet.Subcomplex.morphismProperty_ι_iff_of_preimage_eq`: for `A.preimage e.inv = B` and a class
  `W` of morphisms respecting isomorphisms, `W A.ι ↔ W B.ι`.
* `SSet.Subcomplex.isoOfRangeEq`: for monomorphisms `f : X ⟶ Z` and `g : Y ⟶ Z` with the same
  range, the isomorphism `X ≅ Y` through which `f` factors as `g`.
* `SSet.Subcomplex.not_nonempty_bot`: the empty subcomplex `⊥` is not nonempty.
-/

public section

open CategoryTheory

universe u

namespace SSet.Subcomplex

variable {X Y Z : SSet.{u}}

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

section range

variable (f : X ⟶ Z) (g : Y ⟶ Z) [Mono f] [Mono g] (h : range f = range g)

/-- Two monomorphisms into the same simplicial set with the same range have isomorphic sources:
both sources are isomorphic to the common range. -/
noncomputable def isoOfRangeEq : X ≅ Y :=
  asIso (toRange f) ≪≫ Subcomplex.eqToIso h ≪≫ (asIso (toRange g)).symm

/-- The isomorphism of sources of two monomorphisms with the same range is compatible with the
monomorphisms. -/
@[reassoc (attr := simp)]
lemma isoOfRangeEq_hom_comp : (isoOfRangeEq f g h).hom ≫ g = f := by
  have hg : inv (toRange g) ≫ g = (range g).ι := by
    rw [IsIso.inv_comp_eq, toRange_ι]
  simp only [isoOfRangeEq, Iso.trans_hom, asIso_hom, Subcomplex.eqToIso_hom, Iso.symm_hom,
    asIso_inv, Category.assoc, hg, homOfLE_ι, toRange_ι]

/-- The inverse of the isomorphism of sources of two monomorphisms with the same range is
compatible with the monomorphisms. -/
@[reassoc (attr := simp)]
lemma isoOfRangeEq_inv_comp : (isoOfRangeEq f g h).inv ≫ f = g := by
  rw [Iso.inv_comp_eq, isoOfRangeEq_hom_comp]

end range

/-- The empty subcomplex has no simplices: it has dimension `< 0`. -/
@[simp]
lemma not_nonempty_bot : ¬ ((⊥ : X.Subcomplex) : SSet.{u}).Nonempty :=
  (notNonempty_iff_hasDimensionLT_zero _).2 inferInstance

end SSet.Subcomplex
