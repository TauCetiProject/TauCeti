/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.MonoidalClosed
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.TensorFreeYoneda

/-!
# Sections of the internal Hom of presheaves of modules

Let `R` be a presheaf of commutative rings on a small category `C`, and let `M` and `N` be
presheaves of `R`-modules. The internal Hom `𝓗om(M, N)` of presheaves of modules is only
characterized by the tensor--Hom adjunction (it is produced by the adjoint functor theorem in
`TauCeti.PresheafOfModules.monoidalClosed`). This file computes its sections: a section of
`𝓗om(M, N)` over `U` is a morphism of presheaves of modules `M|_U ⟶ N|_U` on the slice over `U`,
where restriction to the slice is `PresheafOfModulesOfCommRing.pushforward₀ (Over.forget U) R`.

By Mathlib's `PresheafOfModules.freeYonedaEquiv`, a section over `U` is a morphism out of the
free presheaf of modules `TauCeti.PresheafOfModules.freeYoneda R U` on the presheaf represented by
`U`; by the tensor--Hom adjunction it is a morphism `M ⊗ freeYoneda R U ⟶ N`; and by the
restriction--extension correspondence `TauCeti.PresheafOfModules.tensorFreeYonedaHomEquiv` these
are the morphisms of restrictions. The identification is compatible with restriction along
morphisms of `C` and natural in both arguments. This is the sectionwise description of the
internal Hom which restriction and stalk comparisons of internal Homs of sheaves of modules rest
on.

## Main declarations

* `TauCeti.PresheafOfModules.ihomObjEquiv`: the sections of `𝓗om(M, N)` over `U` are the
  morphisms `M|_U ⟶ N|_U`, characterized by `TauCeti.PresheafOfModules.ihomObjEquiv_apply_app`
  (a section acts by evaluation of its restrictions), compatible with restriction along
  morphisms of `C` by `TauCeti.PresheafOfModules.ihomObjEquiv_map_app`, and natural in the target
  and in the source by `TauCeti.PresheafOfModules.ihomObjEquiv_ihom_map_app` and
  `TauCeti.PresheafOfModules.ihomObjEquiv_pre_app_app`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 1.15, for the
  sectionwise description of sheaf Hom which this file establishes for the categorical internal
  Hom of presheaves of modules.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

universe v u

noncomputable section

namespace TauCeti

namespace PresheafOfModules

open _root_.PresheafOfModules PresheafOfModulesOfCommRing

section Sections

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
variable (U : C) (M N : PresheafOfModulesOfCommRing.{u} R)

/-- The sections over `U` of the internal Hom `𝓗om(M, N)` are the morphisms of presheaves of
modules `M|_U ⟶ N|_U` on the slice over `U`: a section corresponds to a morphism out of the free
presheaf represented by `U`, hence, by the tensor--Hom adjunction, to a morphism out of
`M ⊗ freeYoneda R U`, and these are the morphisms of restrictions. -/
def ihomObjEquiv :
    ((ihom M).obj N).obj (op U) ≃
      ((pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :=
  freeYonedaEquiv.symm.trans
    ((((ihom.adjunction M).homEquiv (freeYoneda R U) N).symm).trans
      (tensorFreeYonedaHomEquiv U M N))

/-- The morphism of restrictions corresponding to a section of `𝓗om(M, N)` is obtained by
uncurrying the corresponding morphism out of the free presheaf represented by `U` and
restricting. -/
theorem ihomObjEquiv_apply (s : ((ihom M).obj N).obj (op U)) :
    ihomObjEquiv U M N s =
      restrictOfTensorFreeYoneda U M N (uncurry (freeYonedaEquiv.symm s)) :=
  (Equiv.trans_apply _ _ _).trans ((Equiv.trans_apply _ _ _).trans
    ((congrArg (tensorFreeYonedaHomEquiv U M N) (homEquiv_symm_apply_eq _)).trans
      (tensorFreeYonedaHomEquiv_apply U M N _)))

/-- The section of `𝓗om(M, N)` corresponding to a morphism of restrictions is obtained by
extending it to the tensor product with the free presheaf represented by `U` and currying. -/
theorem ihomObjEquiv_symm_apply
    (φ : (pushforward₀ (Over.forget U) R).obj M ⟶ (pushforward₀ (Over.forget U) R).obj N) :
    (ihomObjEquiv U M N).symm φ = freeYonedaEquiv (curry (tensorFreeYonedaOfRestrict U M N φ)) :=
  (Equiv.symm_trans_apply _ _ _).trans ((Equiv.symm_symm_apply _ _).trans
    (congrArg freeYonedaEquiv ((Equiv.symm_trans_apply _ _ _).trans
      ((Equiv.symm_symm_apply _ _).trans ((homEquiv_apply_eq _).trans
        (congrArg (fun f ↦ curry f) (tensorFreeYonedaHomEquiv_symm_apply U M N φ)))))))

/-- The morphism of restrictions corresponding to a section `s` of `𝓗om(M, N)` over `U` acts at
`g : V ⟶ U` by evaluating the restriction of `s` along `g`.

This is not a simp lemma, for the same reason as
`TauCeti.PresheafOfModules.restrictOfTensorFreeYoneda_app_apply`: simp rewrites the base ring of
the component inside the implicit arguments of the coercion. -/
theorem ihomObjEquiv_apply_app (s : ((ihom M).obj N).obj (op U)) {V : C} (g : V ⟶ U)
    (m : M.obj (op V)) :
    (ihomObjEquiv U M N s).app' (op (Over.mk g)) m =
      ((ihom.ev M).app N).app' (op V)
        (TensorProduct.tmul (R.obj (op V)) (N := PresheafOfModulesOfCommRing.obj ((ihom M).obj N)
          (op V)) m (((ihom M).obj N).map g.op s)) := by
  rw [ihomObjEquiv_apply]
  -- The restriction formula applies at the slice object `Over.mk g`, whose underlying object is
  -- `V` and whose structure morphism is `g`; the basis element indexed by `g` is then sent to the
  -- restriction of `s` along `g`.
  exact (restrictOfTensorFreeYoneda_app_apply U M N _ (Over.mk g) m).trans
    (congrArg (fun x : PresheafOfModulesOfCommRing.obj ((ihom M).obj N) (op V) ↦
      ((ihom.ev M).app N).app' (op V) (TensorProduct.tmul (R.obj (op V)) m x))
      (freeYonedaEquiv_symm_app_freeMk (P := (ihom M).obj N) s g))

/-- Restricting a section of `𝓗om(M, N)` along `g : V ⟶ U` restricts the corresponding morphism
of restrictions to the slice over `V`. -/
theorem ihomObjEquiv_map_app (s : ((ihom M).obj N).obj (op U)) {V : C} (g : V ⟶ U) {W : C}
    (h : W ⟶ V) (m : M.obj (op W)) :
    (ihomObjEquiv V M N (((ihom M).obj N).map g.op s)).app' (op (Over.mk h)) m =
      (ihomObjEquiv U M N s).app' (op (Over.mk (h ≫ g))) m := by
  refine (ihomObjEquiv_apply_app V M N _ h m).trans ?_
  rw [ihomObjEquiv_apply_app]
  exact congrArg (fun x : PresheafOfModulesOfCommRing.obj ((ihom M).obj N) (op W) ↦
    ((ihom.ev M).app N).app' (op W) (TensorProduct.tmul (R.obj (op W)) m x))
    (map_comp_apply ((ihom M).obj N) g.op h.op s).symm

/-- The sections equivalence is natural in the target: applying `𝓗om(M, α)` to a section
corresponds to postcomposing the morphism of restrictions with the restriction of `α`. -/
theorem ihomObjEquiv_ihom_map_app {N' : PresheafOfModulesOfCommRing.{u} R} (α : N ⟶ N')
    (s : ((ihom M).obj N).obj (op U)) :
    ihomObjEquiv U M N' (((ihom M).map α).app (op U) s) =
      ihomObjEquiv U M N s ≫ (pushforward₀ (Over.forget U) R).map α := by
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, ← tensorFreeYonedaHomEquiv_apply,
    ← tensorFreeYonedaHomEquiv_apply, ← tensorFreeYonedaHomEquiv_comp]
  exact congrArg (tensorFreeYonedaHomEquiv U M N')
    ((congrArg (fun f ↦ uncurry f) (freeYonedaEquiv_symm_comp s ((ihom M).map α)).symm).trans
      (uncurry_natural_right _ _))

/-- The sections equivalence is natural in the source: applying `𝓗om(β, N)` to a section
corresponds to precomposing the morphism of restrictions with the restriction of `β`. -/
theorem ihomObjEquiv_pre_app_app {M' : PresheafOfModulesOfCommRing.{u} R} (β : M' ⟶ M)
    (s : ((ihom M).obj N).obj (op U)) :
    ihomObjEquiv U M' N (((pre β).app N).app (op U) s) =
      (pushforward₀ (Over.forget U) R).map β ≫ ihomObjEquiv U M N s := by
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, ← tensorFreeYonedaHomEquiv_apply,
    ← tensorFreeYonedaHomEquiv_apply, ← tensorFreeYonedaHomEquiv_whiskerRight_comp]
  exact congrArg (tensorFreeYonedaHomEquiv U M' N)
    ((congrArg (fun f ↦ uncurry f) (freeYonedaEquiv_symm_comp s ((pre β).app N)).symm).trans
      (uncurry_pre_app _ _ _))

end Sections

end PresheafOfModules

end TauCeti

end
