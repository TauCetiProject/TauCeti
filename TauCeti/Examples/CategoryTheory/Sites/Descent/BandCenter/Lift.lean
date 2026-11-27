/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Lift

/-!
# Checks for lifting automorphisms to central sections

For a gerbe with abelian inertia and an object `x` over `U`:

* the lift sends the identity automorphism to the unit section;
* the lift of an automorphism other than the identity is not the unit section;
* evaluation of `L_x(a)` at `(f, y)` with a supplied isomorphism `f^* x ≅ y` is the conjugate of
  `f^* a` along it;
* restricting `L_x(a)` along `g ≫ f` is lifting the restriction of `a` along `g ≫ f`, and agrees
  with restricting twice, through the composite pullback object;
* evaluation of `L_x(a)` at `(𝟙, x)` returns `a`, and every central section is the lift of its
  evaluation.
-/

public section

namespace TauCeti.Examples.BandCenterLift

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open IntrinsicBandSections

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  {J : GrothendieckTopology C} [F.IsGerbe J]
  (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)
  {U : C} (x : F.obj (.mk (op U)))

/-- The lift of the identity is the unit section. -/
example : lift J hF x 1 = 1 :=
  map_one _

/-- The lift of an automorphism other than the identity is not the unit section. -/
example (a : Aut x) (ha : a ≠ 1) : lift J hF x a ≠ 1 :=
  fun h ↦ ha (lift_injective J hF x (h.trans (map_one _).symm))

/-- Evaluation at `(f, y)` with a supplied isomorphism is the labelled conjugate. -/
example (a : Aut x) {V : C} (f : V ⟶ U) {y : F.obj (.mk (op V))}
    (d : (F.map f.op.toLoc).toFunctor.obj x ≅ y) :
    evaluation f y (lift J hF x a) =
      Aut.autMulEquivOfIso d ((F.map f.op.toLoc).toFunctor.mapAut x a) :=
  evaluation_lift_of_iso J hF x a f d

/-- Restricting twice is restricting along the composite. -/
example (a : Aut x) {V W : C} (f : V ⟶ U) (g : W ⟶ V) :
    restrict g (restrict f (lift J hF x a)) =
      lift J hF ((F.map (g ≫ f).op.toLoc).toFunctor.obj x)
        ((F.map (g ≫ f).op.toLoc).toFunctor.mapAut x a) := by
  rw [restrict_comp, restrict_lift]

/-- Evaluation at the identity recovers the automorphism, and every section is a lift. -/
example (a : Aut x) (s : IntrinsicBandSections F U) :
    evaluation (𝟙 U) x (lift J hF x a) = a ∧ lift J hF x (evaluation (𝟙 U) x s) = s :=
  ⟨evaluation_lift_id J hF x a, lift_evaluation_id J hF x s⟩

end TauCeti.Examples.BandCenterLift
