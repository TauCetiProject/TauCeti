/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward

/-!
# Comparing the tensor maps of restriction and pushforward

Restriction to a slice has a monoidal structure obtained by localization. It is also a
pushforward along the forgetful functor of the slice, with its canonical pushforward tensor
comparison. These tensor maps agree: both carry a pure tensor of sections to the same pure
tensor in the restricted sheaf tensor product. This identifies the selected comparison data,
so restriction formulas can be transported through the composition isomorphisms of pushforward.
-/

public section

open CategoryTheory MonoidalCategory

noncomputable section

universe u

namespace TauCeti.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u}) (X : C)

/-- The sheafified tensor product on modules over the slice ring sheaf. -/
local instance monoidalCategoryRestrictionPushforward :
    MonoidalCategory (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

/-- The tensor map of slice restriction sends a pure tensor of sections to the same pure
tensor in the tensor product sheaf. -/
theorem _root_.SheafOfModules.overFunctor_μ_app_tmul
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) (V : (Over X)ᵒᵖ)
    (m : M.val.obj ((Over.forget X).op.obj V))
    (n : N.val.obj ((Over.forget X).op.obj V)) :
    (Functor.LaxMonoidal.μ (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N).val.app V
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf (R.over X)))
          (M.over X) (N.over X)).app V (m ⊗ₜ[(R.over X).obj.obj V] n)) =
      (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
        ((Over.forget X).op.obj V) (m ⊗ₜ[R.obj.obj ((Over.forget X).op.obj V)] n) := by
  have h := _root_.SheafOfModules.overFunctor_comp_forget_μ (R := R) (X := X) M N
  dsimp only [Functor.LaxMonoidal.comp_μ] at h
  have hh := congrArg (fun f ↦ (f.app V).hom (m ⊗ₜ[(R.over X).obj.obj V] n)) h
  have hs := congrArg (fun f ↦ (f.app ((Over.forget X).op.obj V)).hom
    (m ⊗ₜ[R.obj.obj ((Over.forget X).op.obj V)] n))
    (_root_.SheafOfModules.sheafificationAdjunction_μ_eq_forget_μ (R := R) M N)
  have ht := congrArg (fun f ↦ (f.app V).hom (m ⊗ₜ[(R.over X).obj.obj V] n))
    (_root_.SheafOfModules.sheafificationAdjunction_μ_eq_forget_μ
      (R := R.over X) (M.over X) (N.over X))
  let Fs := _root_.SheafOfModules.forget (ringCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)
  have hp := TauCeti.PresheafOfModules.pushforward₀_μ_app_tmul (Over.forget X)
    R.obj (Fs.obj M) (Fs.obj N) V m n
  let As := PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)
  let Ls := As.rightAdjointLaxMonoidal
  let rawSourceMu := @Functor.LaxMonoidal.μ _ _ _ _ _ _ Fs Ls M N
  have hp' := congrArg (fun z ↦ (rawSourceMu.app ((Over.forget X).op.obj V)).hom z) hp
  exact (congrArg ((Functor.LaxMonoidal.μ
    (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N).val.app V) ht).symm.trans
    (hh.trans (hp'.trans hs))

/-- The tensor comparison obtained by localization for slice restriction agrees with its
canonical pushforward tensor comparison. -/
theorem _root_.SheafOfModules.overFunctor_μ_eq_pushforward_μ
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    Functor.LaxMonoidal.μ (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N =
      letI : (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).LaxMonoidal :=
        pushforwardLaxMonoidal (S := R.over X) (R := R) (𝟙 ((ringCatSheaf R).over X))
      Functor.LaxMonoidal.μ (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X) M N := by
  let : (_root_.SheafOfModules.overFunctor (ringCatSheaf R) X).LaxMonoidal :=
    pushforwardLaxMonoidal (S := R.over X) (R := R) (𝟙 ((ringCatSheaf R).over X))
  apply tensor_hom_ext (R := R.over X)
  ext V : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact (_root_.SheafOfModules.overFunctor_μ_app_tmul (R := R) (X := X) M N V m n).trans
    (pushforward_μ_app_tmul (S := R.over X) (R := R) (F := Over.forget X)
      (𝟙 ((ringCatSheaf R).over X)) M N V m n).symm

end TauCeti.SheafOfModules

end
