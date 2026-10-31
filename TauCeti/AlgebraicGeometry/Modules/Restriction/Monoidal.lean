/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Pushforward
import TauCeti.CategoryTheory.Monoidal.Functor

/-!
# Tensor products under the slice equivalence for an open subscheme

Modules on the slice site over an open are equivalent to modules on its open subscheme.
The canonical pushforward tensor comparison of this equivalence is invertible, and the
comparison with ordinary restriction respects tensor products. These compatibilities allow
restriction formulas expressed on slices to be used on open subschemes.

The site equivalence and its coefficient maps are Mathlib's `Scheme.Modules.overEquiv` and
`TopologicalSpace.Opens.sheafOfModulesEquivOver`. Tensor invertibility uses the adjunction of
the two site-equivalence functors through
`TauCeti.SheafOfModules.isIso_pushforward_μ_of_adjunction`.
-/

public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- The canonical tensor product on module sheaves on the slice over an open. -/
local instance monoidalCategoryRestrictionEquivalence :
    MonoidalCategory (SheafOfModules.{u} (X.ringCatSheaf.over U)) :=
  TauCeti.SheafOfModules.monoidalCategory (X.sheaf.over U)

/-- Identifying module sheaves on the slice over an open with module sheaves on its open
subscheme is lax monoidal, through the canonical pushforward tensor comparison. -/
instance overEquivFunctorLaxMonoidal : (overEquiv U).functor.LaxMonoidal :=
  TauCeti.SheafOfModules.pushforwardLaxMonoidal
    (S := U.sheafRestrict.obj X.sheaf) (R := X.sheaf.over U)
    (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv

/-- The tensor comparison for the equivalence from the slice to the open subscheme is
invertible. -/
instance isIso_overEquivFunctor_μ (M N : SheafOfModules.{u} (X.ringCatSheaf.over U)) :
    IsIso (Functor.LaxMonoidal.μ (overEquiv U).functor M N) := by
  apply TauCeti.SheafOfModules.isIso_pushforward_μ_of_adjunction
    (S := U.sheafRestrict.obj X.sheaf) (R := X.sheaf.over U)
    U.overEquivalence.symm.toAdjunction
    (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv
    (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
    (by rfl)
    (by
      ext V r
      -- Read the coefficient maps on the native commutative structure-sheaf carrier;
      -- they are restrictions along the site equivalence.
      change X.presheaf.map _ (X.presheaf.map _ r) = r
      refine (ConcreteCategory.congr_hom (X.presheaf.map_comp _ _).symm r).trans ?_
      exact (congrArg (fun i ↦ X.presheaf.map i r)
        (Subsingleton.elim _ (𝟙 _))).trans
          (ConcreteCategory.congr_hom (X.presheaf.map_id _) r))

/-- The comparison between restriction to a slice and restriction to the open subscheme
respects the canonical pushforward tensor comparisons. -/
private theorem overFunctorEquiv_hom_tensor_direct (M N : X.Modules) :
    let F : X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
      SheafOfModules.overFunctor X.ringCatSheaf U
    letI : F.LaxMonoidal :=
      TauCeti.SheafOfModules.pushforwardLaxMonoidal
        (S := X.sheaf.over U) (R := X.sheaf) (𝟙 (X.ringCatSheaf.over U))
    Functor.LaxMonoidal.μ
        (F ⋙ (overEquiv U).functor) M N ≫
        (overFunctorEquiv U).hom.app (M ⊗ N : X.Modules) =
      ((overFunctorEquiv U).hom.app M ⊗ₘ (overFunctorEquiv U).hom.app N) ≫
        Functor.LaxMonoidal.μ (restrictFunctor U.ι) M N := by
  let F : X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
    SheafOfModules.overFunctor X.ringCatSheaf U
  let : F.LaxMonoidal :=
    TauCeti.SheafOfModules.pushforwardLaxMonoidal
      (S := X.sheaf.over U) (R := X.sheaf) (𝟙 (X.ringCatSheaf.over U))
  let : (restrictFunctor U.ι).LaxMonoidal := restrictFunctorLaxMonoidal U.ι
  have hα : NatTrans.IsMonoidal (C := X.Modules) (D := (U : Scheme).Modules)
      (F₁ := F ⋙ (overEquiv U).functor) (F₂ := restrictFunctor U.ι)
      (overFunctorEquiv U).hom := by
    have : ((TopologicalSpace.Opens.overEquivalence U).symm.functor ⋙ Over.forget U).IsContinuous
        (_root_.Opens.grothendieckTopology ↥U)
        (_root_.Opens.grothendieckTopology ↥X) :=
      Functor.isContinuous_comp _ _ _
        ((_root_.Opens.grothendieckTopology ↥X).over U) _
    -- The coefficient congruence presents this same functor using `.inverse`.
    have : ((TopologicalSpace.Opens.overEquivalence U).inverse ⋙ Over.forget U).IsContinuous
        (_root_.Opens.grothendieckTopology ↥U)
        (_root_.Opens.grothendieckTopology ↥X) :=
      inferInstanceAs (((TopologicalSpace.Opens.overEquivalence U).symm.functor ⋙
        Over.forget U).IsContinuous _ _)
    -- Mathlib constructs this comparison by composition and coefficient-map congruence
    -- for pushforwards, both of which respect the canonical tensor comparisons.
    unfold overFunctorEquiv
    refine @NatTrans.IsMonoidal.comp
      X.Modules _ (Scheme.Modules.instMonoidalCategory X)
      (U : Scheme).Modules _ (Scheme.Modules.instMonoidalCategory (U : Scheme)) _ _ _ _ _
      (TauCeti.SheafOfModules.pushforwardLaxMonoidal
        (S := U.sheafRestrict.obj X.sheaf) (R := X.sheaf)
        (F := (TopologicalSpace.Opens.overEquivalence U).symm.functor ⋙ Over.forget U) _)
      (restrictFunctorLaxMonoidal U.ι) _ ?_ ?_
    · exact TauCeti.SheafOfModules.isMonoidal_pushforwardComp_hom
        (S := U.sheafRestrict.obj X.sheaf) (R := X.sheaf.over U) (T := X.sheaf)
        (U.overPullbackSheafEquivOver.app X.ringCatSheaf).inv
        (𝟙 (X.ringCatSheaf.over U))
    · exact TauCeti.SheafOfModules.isMonoidal_pushforwardCongr_hom
        (S := U.sheafRestrict.obj X.sheaf) (R := X.sheaf) _
  exact hα.tensor M N

/-- The slice-to-open comparison preserves the tensor maps from the selected monoidal
restriction functor and the canonical restriction functor on schemes. -/
theorem overFunctorEquiv_hom_tensor (M N : X.Modules) :
    let F : X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
      SheafOfModules.overFunctor X.ringCatSheaf U
    letI : F.Monoidal := SheafOfModules.overFunctorMonoidal (R := X.sheaf) (X := U)
    Functor.LaxMonoidal.μ (F ⋙ (overEquiv U).functor) M N ≫
        (overFunctorEquiv U).hom.app (M ⊗ N : X.Modules) =
      ((overFunctorEquiv U).hom.app M ⊗ₘ (overFunctorEquiv U).hom.app N) ≫
        Functor.LaxMonoidal.μ (restrictFunctor U.ι) M N := by
  let F : X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
    SheafOfModules.overFunctor X.ringCatSheaf U
  let : F.Monoidal := SheafOfModules.overFunctorMonoidal (R := X.sheaf) (X := U)
  have h := overFunctorEquiv_hom_tensor_direct U M N
  have hμ := SheafOfModules.overFunctor_μ_eq_pushforward_μ (R := X.sheaf) (X := U) M N
  dsimp only at h ⊢
  have hcomp := Functor.LaxMonoidal.comp_μ_congr F (overEquiv U).functor
    (SheafOfModules.overFunctorMonoidal (R := X.sheaf) (X := U)).toLaxMonoidal
    (TauCeti.SheafOfModules.pushforwardLaxMonoidal
      (S := X.sheaf.over U) (R := X.sheaf) (𝟙 (X.ringCatSheaf.over U))) M N hμ
  rw [hcomp]
  exact h

end AlgebraicGeometry.Scheme.Modules

end
