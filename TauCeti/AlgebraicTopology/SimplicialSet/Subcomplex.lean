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

* `SSet.Subcomplex.morphismProperty_ι_iff_of_preimage_eq`: for `A.preimage e.inv = B` and a class
  `W` of morphisms respecting isomorphisms, `W A.ι ↔ W B.ι`.
-/

public section

open CategoryTheory

universe u

namespace SSet.Subcomplex

variable {X Y : SSet.{u}}

/-- If an isomorphism `e : X ≅ Y` carries a subcomplex `A` of `X` to a subcomplex `B` of `Y`, then a
class of morphisms respecting isomorphisms contains the inclusion of `A` exactly when it contains
the inclusion of `B`. -/
lemma morphismProperty_ι_iff_of_preimage_eq (W : MorphismProperty SSet.{u}) [W.RespectsIso]
    (e : X ≅ Y) {A : X.Subcomplex} {B : Y.Subcomplex} (h : A.preimage e.inv = B) :
    W A.ι ↔ W B.ι := by
  subst h
  have : Mono ((A.preimage e.inv).toImage e.inv) := mono_of_mono_fac (toImage_ι _ _)
  have : IsIso ((A.preimage e.inv).toImage e.inv) := isIso_of_mono_of_epi _
  have hA := preimage_image_of_isIso e.inv A
  have hw : ((A.preimage e.inv).toImage e.inv ≫ homOfLE hA.le) ≫ A.ι =
      (A.preimage e.inv).ι ≫ e.inv := by
    rw [Category.assoc, homOfLE_ι, toImage_ι]
  exact (W.arrow_mk_iso_iff (Arrow.isoMk (asIso ((A.preimage e.inv).toImage e.inv) ≪≫
    Subcomplex.eqToIso hA) e.symm hw)).symm

end SSet.Subcomplex
