/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Glue

/-!
# Checks for gluing central sections

* For every section `s ∈ ZF(U)` and every covering sieve, gluing the restrictions of `s` recovers
  `s` itself, with all its components at arrows `a : V ⟶ U`, not only its component at `𝟙 U`.
* The identity family glues to the identity section, and the inverse family to the inverse.
* Over an arrow `a : V ⟶ U` whose fibre over `V` is empty, the descended centre unit is the
  identity, whatever the family.
* For a prestack all of whose fibres have only identity endomorphisms, the sheaf
  `U ↦ Additive ZF(U)` has a single section over every `U`.
* The coefficient group of the sheaf of central sections over `U` is `Additive ZF(U)`, and its
  restriction maps are restrictions of sections.
-/

public section

namespace TauCeti.Examples.BandCenterGlue

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open IntrinsicBandSections

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {U : C}
  {J : GrothendieckTopology C} [F.IsPrestack J] {R : Sieve U}

/-- Gluing the restrictions of `s` recovers every component of `s`. -/
example (hR : R ∈ J U) (s : IntrinsicBandSections F U) {V : C} (a : V ⟶ U) :
    (glue hR (isCompatible_restrict s)).val V a = s.val V a := by
  simp

/-- The identity family glues to the identity, and the inverse family to the inverse. -/
example (hR : R ∈ J U) {z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left}
    (hz : IsCompatible z) :
    glue (F := F) hR isCompatible_one = 1 ∧ glue hR hz.inv * glue hR hz = 1 :=
  ⟨glue_one hR, by rw [glue_inv hR hz, inv_mul_cancel]⟩

/-- Over an arrow `a : V ⟶ U` whose source `V` has empty fibre, the descended centre unit is the
identity. -/
example (hR : R ∈ J U) {z : ∀ i : R.arrows.category, IntrinsicBandSections F i.obj.left}
    (hz : IsCompatible z) {V : C} (a : V ⟶ U) [IsEmpty (F.obj (.mk (op V)))] :
    coverCenterAt hR hz a = 1 :=
  Units.ext (CatCenter.ext _ _ fun x ↦ isEmptyElim x)

/-- With only identity endomorphisms in the fibres, the sheaf has a single section. -/
example (h : ∀ (V : C) (x : F.obj (.mk (op V))), Subsingleton (x ⟶ x)) (V : Cᵒᵖ) :
    Subsingleton ((presheaf F).obj V) :=
  have := subsingleton_of_subsingleton_end (U := V.unop) h
  inferInstanceAs (Subsingleton (Additive (IntrinsicBandSections F V.unop)))

/-- The coefficient group over `U` is `Additive ZF(U)`. -/
example (U : C) :
    (sheaf F J).obj.obj (op U) = AddCommGrpCat.of (Additive (IntrinsicBandSections F U)) :=
  presheaf_obj F (op U)

/-- The restriction maps of the coefficient sheaf are restrictions of sections. -/
example {U V : C} (f : V ⟶ U) (s : IntrinsicBandSections F U) :
    (sheaf F J).obj.map f.op (Additive.ofMul s) = Additive.ofMul (restrict f s) :=
  presheaf_map_apply f.op _

end TauCeti.Examples.BandCenterGlue
