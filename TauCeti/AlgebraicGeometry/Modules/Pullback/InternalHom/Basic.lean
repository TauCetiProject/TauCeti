/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.CategoryTheory.Monoidal.Rigid.Functor

/-!
# Pullback of internal Hom

For arbitrary sheaves of modules `M` and `F` on `Y`, construct the canonical comparison
`f* 𝓗om(M, F) ⟶ 𝓗om(f* M, f* F)` for every scheme morphism `f : X ⟶ Y`.
It is invertible whenever `M` has a left dual. In particular,
this applies to finite locally free sources, without flatness of `f` or finiteness of the target.

The comparison is the mate of the inverse tensor comparison with left factor `M`.
It is characterized by evaluation, is natural in every target sheaf of modules, and is
natural in the source.
Use `TauCeti.AlgebraicGeometry.pullbackIhomComparison M f` for the comparison.
Invertibility follows from the general strong monoidal functor result
`CategoryTheory.Functor.ihomComparison_isIso_of_exactPairing`, after identifying this
comparison with the internal Hom comparison of module pullback.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (M : Y.Modules) (f : X ⟶ Y)

/-- The canonical base-change comparison for internal Hom from an arbitrary module sheaf.
It is natural in arbitrary target sheaves of modules. -/
def pullbackIhomComparison :
    ihom M ⋙ Scheme.Modules.pullback f ⟶
      Scheme.Modules.pullback f ⋙ ihom ((Scheme.Modules.pullback f).obj M) :=
  (mateEquiv (ihom.adjunction M)
    (ihom.adjunction ((Scheme.Modules.pullback f).obj M))
    (.mk _ _ _ _ (Functor.Monoidal.commTensorLeft (Scheme.Modules.pullback f) M).hom))

/-- Evaluation after the base-change comparison is the pullback of evaluation, preceded by
the inverse canonical tensor comparison. This characterizes the base-change map. -/
@[reassoc (attr := simp)]
theorem whiskerLeft_pullbackIhomComparison_app_comp_ev (F : Y.Modules) :
    (Scheme.Modules.pullback f).obj M ◁ (pullbackIhomComparison M f).app F ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj M)).app
          ((Scheme.Modules.pullback f).obj F) =
      inv (δ (Scheme.Modules.pullback f) M ((ihom M).obj F)) ≫
        (Scheme.Modules.pullback f).map ((ihom.ev M).app F) := by
  have h := mateEquiv_counit (ihom.adjunction M)
    (ihom.adjunction ((Scheme.Modules.pullback f).obj M))
    (.mk _ _ _ _ (Functor.Monoidal.commTensorLeft (Scheme.Modules.pullback f) M).hom) F
  -- Express the mate equation using module whiskering and evaluation, rather than
  -- `tensorLeft.map`, `TwoSquare.app`, and the adjunction counits.
  change (Scheme.Modules.pullback f).obj M ◁
      (pullbackIhomComparison M f).app F ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj M)).app
          ((Scheme.Modules.pullback f).obj F) =
    (Functor.Monoidal.commTensorLeft (Scheme.Modules.pullback f) M).hom.app
      ((ihom M).obj F) ≫ (Scheme.Modules.pullback f).map ((ihom.ev M).app F) at h
  have hd : (Functor.Monoidal.commTensorLeft (Scheme.Modules.pullback f) M).hom.app
      ((ihom M).obj F) = inv (δ (Scheme.Modules.pullback f) M
        ((ihom M).obj F)) := (Functor.Monoidal.inv_δ _ _ _).symm
  exact h.trans (congrArg (· ≫ (Scheme.Modules.pullback f).map
    ((ihom.ev M).app F)) hd)

/-- The base-change comparison is obtained by currying the pullback of evaluation, after
inverting the canonical tensor comparison. -/
theorem pullbackIhomComparison_app_eq_curry (F : Y.Modules) :
    (pullbackIhomComparison M f).app F =
      curry (inv (δ (Scheme.Modules.pullback f) M ((ihom M).obj F)) ≫
        (Scheme.Modules.pullback f).map ((ihom.ev M).app F)) := by
  exact (curry_uncurry _).symm.trans
    (congrArg curry (whiskerLeft_pullbackIhomComparison_app_comp_ev M f F))

/-- The base-change comparison is natural in the source: precomposition with
`g : M₁ ⟶ M₂` corresponds to precomposition with its pullback. -/
@[reassoc]
theorem pullback_map_pre_app_comp_pullbackIhomComparison_app {M₁ M₂ : Y.Modules}
    (g : M₁ ⟶ M₂) (F : Y.Modules) :
    (Scheme.Modules.pullback f).map ((pre g).app F) ≫ (pullbackIhomComparison M₁ f).app F =
      (pullbackIhomComparison M₂ f).app F ≫
        (pre ((Scheme.Modules.pullback f).map g)).app ((Scheme.Modules.pullback f).obj F) := by
  apply uncurry_injective
  simp only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    whiskerLeft_pullbackIhomComparison_app_comp_ev, id_tensor_pre_app_comp_ev]
  -- Read the comparison's target as an internal Hom so that the whiskers can be exchanged.
  dsimp only [Functor.comp_obj]
  rw [whisker_exchange_assoc, whiskerLeft_pullbackIhomComparison_app_comp_ev,
    ← cancel_epi (δ (Scheme.Modules.pullback f) M₁ ((ihom M₂).obj F)),
    δ_natural_right_assoc, IsIso.hom_inv_id_assoc, ← Functor.map_comp,
    id_tensor_pre_app_comp_ev, δ_natural_left_assoc, IsIso.hom_inv_id_assoc,
    Functor.map_comp]

/-- The canonical internal-Hom base-change comparison is invertible for every scheme morphism
when its source has a left dual, without any condition on the target. -/
theorem isIso_pullbackIhomComparison_of_exactPairing
    (D : Y.Modules) [ExactPairing D M] :
    IsIso (pullbackIhomComparison M f) := by
  have h : pullbackIhomComparison M f = (Scheme.Modules.pullback f).ihomComparison M := by
    apply NatTrans.ext
    funext F
    have hμ : inv (δ (Scheme.Modules.pullback f) M ((ihom M).obj F)) =
        μ (Scheme.Modules.pullback f) M ((ihom M).obj F) :=
      Functor.Monoidal.inv_δ (Scheme.Modules.pullback f) M ((ihom M).obj F)
    rw [pullbackIhomComparison_app_eq_curry, Functor.ihomComparison_app_eq_curry, hμ]
  rw [h]
  exact (Scheme.Modules.pullback f).ihomComparison_isIso_of_exactPairing D M

end

end TauCeti.AlgebraicGeometry
