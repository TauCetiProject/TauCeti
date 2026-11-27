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
(`IntrinsicBandSections.isSheaf_of_prestack`), packaged as the object `IntrinsicBandSections.sheaf`
of `Sheaf J AddCommGrpCat` (both in `BandCenter/Glue.lean`).

If `F` is moreover a gerbe all of whose automorphism groups are commutative, evaluation at an object
`x` over `U` is a group isomorphism `ZF(U) ≃* Aut x` (`IntrinsicBandSections.evaluationMulEquiv`,
`BandCenter/Lift.lean`). These isomorphisms are compatible with pullback and with conjugation along
isomorphisms of objects, so they form an abelian banding of `F` by the sheaf of central sections
(`IntrinsicBandSections.banding`): the intrinsic band of `F`. It is defined over every `U` at once,
including those over which the fibre of `F` is empty, and uses no terminal object, no fibre products
and no global object. This is the varying-base step of the Stacks Project, Lemma 8.11.8 (06NY).

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.IntrinsicBandSections`:

* `banding`: the abelian banding of a gerbe with abelian inertia by `sheaf`, whose band
  automorphisms are evaluations.

## Main results

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

/-! ### The intrinsic banding -/

variable [F.IsGerbe J] (hF : ∀ (V : C) (z : F.obj (.mk (op V))) (a b : Aut z), a * b = b * a)

/-- **The intrinsic band of a gerbe with abelian inertia**: the abelian banding of `F` by the sheaf
of intrinsic central sections whose band automorphism of a section `s` at `x` over `U` is the
evaluation `ev_(𝟙, x)(s)`. -/
noncomputable def banding : F.AbelianBanding J (sheaf F J) where
  mulEquiv U x :=
    (MulEquiv.multiplicativeAdditive (IntrinsicBandSections F U)).trans (evaluationMulEquiv J hF x)
  -- The coefficients of `sheaf F J` are `Additive ZF(U)` and its restriction maps are `restrict`
  -- (`sheaf_obj_obj`, `sheaf_obj_map_apply`) only up to unfolding `sheaf`, so rewriting these
  -- goals with `sheaf_obj_map_apply` or `MulEquiv.trans_apply` fails: the motive does not
  -- typecheck. Both fields therefore restate their goal with `change`, in terms of sections of
  -- `ZF`, before rewriting with `evaluationMulEquiv_apply`.
  mapAut_mulEquiv {U V} f x a := by
    change (F.map f.op.toLoc).toFunctor.mapAut x
        (evaluationMulEquiv J hF x (Additive.toMul a.toAdd)) =
      evaluationMulEquiv J hF _ (restrict f (Additive.toMul a.toAdd))
    rw [evaluationMulEquiv_apply, evaluationMulEquiv_apply, mapAut_evaluation, evaluation_restrict,
      Category.id_comp, Category.comp_id]
  autMulEquivOfIso_mulEquiv {U x y} e a := by
    change Aut.autMulEquivOfIso e (evaluationMulEquiv J hF x (Additive.toMul a.toAdd)) =
      evaluationMulEquiv J hF y (Additive.toMul a.toAdd)
    rw [evaluationMulEquiv_apply, evaluationMulEquiv_apply, autMulEquivOfIso_evaluation]

/-- The band automorphism of a section `s` at `x` over `U` is its evaluation at `(𝟙, x)`. -/
@[simp]
theorem banding_mulEquiv_apply {U : C} (x : F.obj (.mk (op U))) (s : IntrinsicBandSections F U) :
    (banding J hF).mulEquiv U x (Multiplicative.ofAdd (Additive.ofMul s)) =
      evaluation (𝟙 U) x s :=
  evaluationMulEquiv_apply J hF x s

/-- The inverse of the band isomorphism at `x` is the lift `L_x`. -/
@[simp]
theorem banding_mulEquiv_symm_apply {U : C} (x : F.obj (.mk (op U))) (a : Aut x) :
    ((banding J hF).mulEquiv U x).symm a =
      Multiplicative.ofAdd (Additive.ofMul (lift J hF x a)) :=
  congrArg (fun s ↦ Multiplicative.ofAdd (Additive.ofMul s))
    (evaluationMulEquiv_symm_apply J hF x a)

/-- **The central sections of the intrinsic band are the sections themselves**: the central
section `c_b(U)(s)` attached by `AbelianBanding.centerFromBanding` to a coefficient `s` of the
intrinsic banding is `s`. -/
@[simp]
theorem centerFromBanding_banding {U : C} (s : IntrinsicBandSections F U) :
    (banding J hF).centerFromBanding U (Multiplicative.ofAdd (Additive.ofMul s)) = s := by
  refine (AbelianBanding.eq_centerFromBanding _ _ s fun V f x ↦ ?_).symm
  -- As in `banding`, the restriction in the coefficient sheaf is `restrict` only up to unfolding
  -- `sheaf`, so `change` states it as a section of `ZF(V)` rather than `rw [sheaf_obj_map_apply]`.
  change _ = (banding J hF).mulEquiv V x (Multiplicative.ofAdd (Additive.ofMul (restrict f s)))
  rw [banding_mulEquiv_apply, evaluation_restrict, Category.id_comp]

end CategoryTheory.Pseudofunctor.IntrinsicBandSections
