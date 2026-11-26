/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.IntrinsicBand

/-!
# Checks for the intrinsic band of a gerbe with abelian inertia

For a prestack `F` and a gerbe with abelian inertia:

* the coefficient group of the sheaf of central sections over `U` is `Additive ZF(U)`, and its
  restriction maps are restrictions of sections;
* the band automorphism of a section at `x` is its evaluation at `(𝟙, x)`, and the band
  automorphism of the lift `L_x(a)` at `x` is `a`;
* the band automorphism of a section other than the unit is not the identity, at every object;
* the banding is compatible with pullback, as an instance of the `AbelianBanding` field;
* the central section of a coefficient of the intrinsic banding is the coefficient itself.
-/

public section

namespace TauCeti.Examples.BandCenterIntrinsicBand

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open IntrinsicBandSections

variable {C : Type*} [Category* C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  {J : GrothendieckTopology C}

/-- The coefficient group over `U` is `Additive ZF(U)`. -/
example [F.IsPrestack J] (U : C) :
    (sheaf F J).obj.obj (op U) = AddCommGrpCat.of (Additive (IntrinsicBandSections F U)) :=
  sheaf_obj_obj F J U

/-- The restriction maps of the coefficient sheaf are restrictions of sections. -/
example [F.IsPrestack J] {U V : C} (f : V ⟶ U) (s : IntrinsicBandSections F U) :
    (sheaf F J).obj.map f.op (Additive.ofMul s) = Additive.ofMul (restrict f s) :=
  sheaf_obj_map_apply F J f _

variable [F.IsGerbe J] (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)
  {U : C} (x : F.obj (.mk (op U)))

/-- The band automorphism of a section is its evaluation, and that of the lift `L_x(a)` is `a`. -/
example (s : IntrinsicBandSections F U) (a : Aut x) :
    (banding J hF).mulEquiv U x (Multiplicative.ofAdd (Additive.ofMul s)) = evaluation (𝟙 U) x s ∧
      (banding J hF).mulEquiv U x (Multiplicative.ofAdd (Additive.ofMul (lift J hF x a))) = a :=
  ⟨banding_mulEquiv_apply J hF x s, by
    rw [banding_mulEquiv_apply, evaluation_lift_id]⟩

/-- A section other than the unit has a band automorphism other than the identity at every
object, so the banding does not collapse to the trivial band. -/
example (s : IntrinsicBandSections F U) (hs : s ≠ 1) :
    (banding J hF).mulEquiv U x (Multiplicative.ofAdd (Additive.ofMul s)) ≠ 1 := by
  rw [banding_mulEquiv_apply]
  exact fun h ↦ hs (evaluation_injective (J := J) x (h.trans (map_one _).symm))

/-- The banding is compatible with pullback along `f : V ⟶ U`: the band automorphism of the
restriction of `s` at `f^* x` is the pullback of the band automorphism of `s` at `x`. -/
example (s : IntrinsicBandSections F U) {V : C} (f : V ⟶ U) :
    (F.map f.op.toLoc).toFunctor.mapAut x
        ((banding J hF).mulEquiv U x (Multiplicative.ofAdd (Additive.ofMul s))) =
      (banding J hF).mulEquiv V ((F.map f.op.toLoc).toFunctor.obj x)
        (Multiplicative.ofAdd (Additive.ofMul (restrict f s))) :=
  (banding J hF).mapAut_mulEquiv f x _

/-- The central section of a coefficient of the intrinsic banding is the coefficient itself. -/
example (s : IntrinsicBandSections F U) :
    (banding J hF).centerFromBanding U (Multiplicative.ofAdd (Additive.ofMul s)) = s :=
  centerFromBanding_banding J hF s

end TauCeti.Examples.BandCenterIntrinsicBand
