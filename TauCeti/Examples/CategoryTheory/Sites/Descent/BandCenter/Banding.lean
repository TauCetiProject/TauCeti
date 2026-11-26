/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Banding

/-!
# Checks for central sections from an abelian banding

For every banding of a pseudofunctor with groupoid fibres:

* the zero coefficient gives the identity central unit and the identity central section;
* the central unit of `-a` has component the inverse of `b(U, x)(a)`, not `b(U, x)(a)` itself;
* evaluating the central section of `a` at the identity arrow recovers `b(U, x)(a)`.
-/

public section

namespace TauCeti.Examples.BandCenterBanding

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat} {J : GrothendieckTopology C}
  {A : Sheaf J AddCommGrpCat} (b : F.AbelianBanding J A)
  (hF : ∀ U : C, IsGroupoid (F.obj (.mk (op U))))

/-- The zero coefficient gives the identity central unit. -/
example (U : C) : b.coefficientCenter hF U 1 = 1 :=
  map_one _

/-- The zero coefficient gives the identity central section. -/
example (U : C) : b.centerFromBanding hF U 1 = 1 :=
  map_one _

/-- The central unit of the inverse coefficient has the inverse band automorphism as component. -/
example (U : C) (a : Multiplicative (A.obj.obj (op U))) (x : F.obj (.mk (op U))) :
    (b.coefficientCenter hF U a⁻¹).val.app x = (b.mulEquiv U x a).asIso.inv := by
  rw [AbelianBanding.coefficientCenter_app, map_inv, Aut.inv_asIso, Iso.symm_hom]

/-- Evaluating the central section of `a` at the identity arrow recovers `b(U, x)(a)`. -/
example (U : C) (a : Multiplicative (A.obj.obj (op U))) (x : F.obj (.mk (op U))) :
    IntrinsicBandSections.evaluation (𝟙 U) x (b.centerFromBanding hF U a) = b.mulEquiv U x a := by
  simp

end TauCeti.Examples.BandCenterBanding
