/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Glue
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Lift
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Banding

/-!
# The intrinsic band of a gerbe with abelian inertia

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a prestack for a Grothendieck topology `J` and `ZF(U)` its
group of intrinsic central sections over `U` (`CategoryTheory.Pseudofunctor.IntrinsicBandSections`).
The presheaf `U ↦ Additive ZF(U)` with restriction as transition maps is a sheaf of abelian groups
(`IntrinsicBandSections.isSheaf_of_prestack`, `BandCenter/Glue.lean`); `IntrinsicBandSections.sheaf`
packages it as an object of `Sheaf J AddCommGrpCat`.

If `F` is moreover a gerbe all of whose automorphism groups are commutative, evaluation at an object
`x` over `U` is a group isomorphism `ZF(U) ≃* Aut x` (`IntrinsicBandSections.evaluationMulEquiv`,
`BandCenter/Lift.lean`). These isomorphisms are compatible with pullback and with conjugation along
isomorphisms of objects, so they form an abelian banding of `F` by the sheaf of central sections
(`IntrinsicBandSections.banding`): the intrinsic band of `F`. It is defined over every `U` at once,
including those over which the fibre of `F` is empty, and uses no terminal object, no fibre products
and no global object. This is the varying-base step of the Stacks Project, Lemma 8.11.8 (06NY).

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.IntrinsicBandSections`:

* `sheaf`: the sheaf of abelian groups `U ↦ Additive ZF(U)` of a prestack.
* `banding`: the abelian banding of a gerbe with abelian inertia by `sheaf`, whose band
  automorphisms are evaluations.

## Main results

* `sheaf_obj`, `sheaf_obj_obj`, `sheaf_obj_map_apply`: the sections and restrictions of `sheaf`.
* `banding_mulEquiv_apply`: the band automorphism of a section `s` at `x` over `U` is the
  evaluation `ev_(𝟙, x)(s)`.
* `banding_mulEquiv_symm_apply`: its inverse is the lift `L_x`.
* `centerFromBanding_banding`: the central section of a coefficient `s` of the intrinsic banding
  is `s`.

## References

* [The Stacks Project, Lemma 8.11.8 (06NY)](https://stacks.math.columbia.edu/tag/06NY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.IntrinsicBandSections

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (J : GrothendieckTopology C)

/-! ### The sheaf of intrinsic central sections -/

section Sheaf

variable (F) [F.IsPrestack J]

/-- **The sheaf of intrinsic central sections** of a prestack: `U ↦ Additive ZF(U)`, with
restriction along `f : V ⟶ U` as transition map. -/
@[expose]
def sheaf : Sheaf J AddCommGrpCat.{max u v u' v'} :=
  ⟨presheaf F, isSheaf_of_prestack⟩

/-- The underlying presheaf of `sheaf F J` is `presheaf F`. -/
theorem sheaf_obj : (sheaf F J).obj = presheaf F :=
  rfl

theorem sheaf_obj_obj (U : C) :
    (sheaf F J).obj.obj (op U) = AddCommGrpCat.of (Additive (IntrinsicBandSections F U)) :=
  rfl

/-- The restriction maps of `sheaf F J` are `restrict` through the `Additive` wrapper. -/
theorem sheaf_obj_map_apply {U V : C} (f : V ⟶ U) (s : Additive (IntrinsicBandSections F U)) :
    (sheaf F J).obj.map f.op s = Additive.ofMul (restrict f (Additive.toMul s)) :=
  rfl

end Sheaf

/-! ### The intrinsic banding -/

variable [F.IsGerbe J] (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)

/-- **The intrinsic band of a gerbe with abelian inertia**: the abelian banding of `F` by the sheaf
of intrinsic central sections whose band automorphism of a section `s` at `x` over `U` is the
evaluation `ev_(𝟙, x)(s)`. -/
noncomputable def banding : F.AbelianBanding J (sheaf F J) where
  mulEquiv U x :=
    { toFun a := evaluation (𝟙 U) x (Additive.toMul (Multiplicative.toAdd a))
      invFun a := Multiplicative.ofAdd (Additive.ofMul (lift J hF x a))
      left_inv a := congrArg (fun s ↦ Multiplicative.ofAdd (Additive.ofMul s))
        (lift_evaluation_id J hF x _)
      right_inv := evaluation_lift_id J hF x
      map_mul' _ _ := map_mul (evaluation (𝟙 U) x) _ _ }
  mapAut_mulEquiv {U V} f x a := by
    change _ = evaluation (𝟙 V) _ (restrict f (Additive.toMul (Multiplicative.toAdd a)))
    rw [evaluation_restrict, Category.id_comp]
    exact (mapAut_evaluation (𝟙 U) f x _).trans (by rw [Category.comp_id])
  autMulEquivOfIso_mulEquiv e a := autMulEquivOfIso_evaluation (𝟙 _) e _

/-- The band automorphism of a section `s` at `x` over `U` is its evaluation at `(𝟙, x)`. -/
@[simp]
theorem banding_mulEquiv_apply {U : C} (x : F.obj (.mk (op U))) (s : IntrinsicBandSections F U) :
    (banding J hF).mulEquiv U x (Multiplicative.ofAdd (Additive.ofMul s)) =
      evaluation (𝟙 U) x s :=
  (rfl)

/-- The inverse of the band isomorphism at `x` is the lift `L_x`. -/
@[simp]
theorem banding_mulEquiv_symm_apply {U : C} (x : F.obj (.mk (op U))) (a : Aut x) :
    ((banding J hF).mulEquiv U x).symm a =
      Multiplicative.ofAdd (Additive.ofMul (lift J hF x a)) :=
  (rfl)

/-- **The central sections of the intrinsic band are the sections themselves**: the central
section `c_b(U)(s)` attached by `AbelianBanding.centerFromBanding` to a coefficient `s` of the
intrinsic banding is `s`. -/
theorem centerFromBanding_banding {U : C} (s : IntrinsicBandSections F U) :
    (banding J hF).centerFromBanding U (Multiplicative.ofAdd (Additive.ofMul s)) = s := by
  refine (AbelianBanding.eq_centerFromBanding _ _ s fun V f x ↦ ?_).symm
  change _ = (banding J hF).mulEquiv V x (Multiplicative.ofAdd (Additive.ofMul (restrict f s)))
  rw [banding_mulEquiv_apply, evaluation_restrict, Category.id_comp]

end CategoryTheory.Pseudofunctor.IntrinsicBandSections
