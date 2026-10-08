/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal

/-!
# Pullback of internal Hom from a finite locally free sheaf

For a finite locally free sheaf `E` and a quasicoherent sheaf `F` on `Y`, the canonical
comparison `f* 𝓗om(E, F) ⟶ 𝓗om(f* E, f* F)` is an isomorphism for every scheme morphism
`f : X ⟶ Y`. No flatness assumption on `f` or finiteness assumption on `F` is needed.

The comparison is the internal-Hom comparison of the strong monoidal functor from
quasicoherent sheaves on `Y` to all modules on `X`. It is characterized by evaluation and
is natural in the target. Its invertibility follows from the exact pairing of `E` with
its internal-Hom dual, using `CategoryTheory.Functor.ihomComparison_isIso_of_exactPairing`.
The target is the ordinary sheaf internal Hom, not a quasicoherent replacement of it.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (E : FiniteLocallyFreeSheaf Y) (f : X ⟶ Y)

/-- The canonical base-change comparison for internal Hom from a finite locally free sheaf.
It is natural in quasicoherent targets, and takes values in ordinary sheaves of modules. -/
def pullbackInternalHomComparison :
    internalHom E ⋙ (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
        Scheme.Modules.pullback f ⟶
      (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
        Scheme.Modules.pullback f ⋙
          ihom ((Scheme.Modules.pullback f).obj E.obj) :=
  (((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
    Scheme.Modules.pullback f).ihomComparison ((toQuasicoherent Y).obj E)).natTrans

/-- Evaluation after the base-change comparison is the pullback of evaluation, preceded by
the inverse canonical tensor comparison. This characterizes the base-change map. -/
@[reassoc (attr := simp)]
theorem pullbackInternalHomComparison_ev (F : QuasicoherentSheaf Y) :
    (Scheme.Modules.pullback f).obj E.obj ◁ (pullbackInternalHomComparison E f).app F ≫
        (ihom.ev ((Scheme.Modules.pullback f).obj E.obj)).app
          ((Scheme.Modules.pullback f).obj F.obj) =
      μ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
        Scheme.Modules.pullback f) ((toQuasicoherent Y).obj E) ((internalHom E).obj F) ≫
        (Scheme.Modules.pullback f).map
          (E.obj ◁ eqToHom (internalHom_obj_obj E F) ≫ (ihom.ev E.obj).app F.obj) := by
  have h := Functor.ihomComparison_ev
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)
    ((toQuasicoherent Y).obj E) F
  -- Express the composite functor on underlying module maps. Rewriting through the full
  -- subcategory would mix the `Y.Modules` and `SheafOfModules` category instances.
  change _ = μ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
    Scheme.Modules.pullback f) ((toQuasicoherent Y).obj E) ((internalHom E).obj F) ≫
      (Scheme.Modules.pullback f).map (((ihom.ev ((toQuasicoherent Y).obj E)).app F).hom) at h
  exact h.trans (congrArg (fun g ↦ μ
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)
    ((toQuasicoherent Y).obj E) ((internalHom E).obj F) ≫ (Scheme.Modules.pullback f).map g)
    (ihom_ev_toQuasicoherent_app_hom E F))

/-- The base-change comparison is obtained by currying the pullback of evaluation, after
inverting the canonical tensor comparison. -/
theorem pullbackInternalHomComparison_app_eq_curry (F : QuasicoherentSheaf Y) :
    (pullbackInternalHomComparison E f).app F =
      curry (inv (δ ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
        Scheme.Modules.pullback f) ((toQuasicoherent Y).obj E) ((internalHom E).obj F)) ≫
          (Scheme.Modules.pullback f).map
            (E.obj ◁ eqToHom (internalHom_obj_obj E F) ≫ (ihom.ev E.obj).app F.obj)) := by
  erw [Functor.Monoidal.inv_δ]
  exact (curry_uncurry _).symm.trans
    (congrArg curry (pullbackInternalHomComparison_ev E f F))

/-- The canonical internal-Hom base-change comparison is invertible for every scheme morphism
when its source is finite locally free. -/
instance isIso_pullbackInternalHomComparison : IsIso (pullbackInternalHomComparison E f) := by
  let : ExactPairing (dual E).obj E.obj := exactPairingOfIsIsoDualTensorIhom (Y := E.obj)
  let : ExactPairing ((toQuasicoherent Y).obj (dual E)) ((toQuasicoherent Y).obj E) :=
    @ObjectProperty.exactPairingFullSubcategory Y.Modules _ _ _
      (Scheme.Modules.isMonoidal_isQuasicoherent Y) _ _ this
  exact Functor.ihomComparison_isIso_of_exactPairing
    ((ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙ Scheme.Modules.pullback f)
    ((toQuasicoherent Y).obj (dual E)) ((toQuasicoherent Y).obj E)

/-- Arbitrary pullback commutes with internal Hom from a finite locally free sheaf, naturally
in the quasicoherent target. -/
def pullbackInternalHomIso :
    internalHom E ⋙ (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
        Scheme.Modules.pullback f ≅
      (ObjectProperty.ι _ : QuasicoherentSheaf Y ⥤ Y.Modules) ⋙
        Scheme.Modules.pullback f ⋙
          ihom ((Scheme.Modules.pullback f).obj E.obj) :=
  asIso (pullbackInternalHomComparison E f)

/-- The forward map of the base-change isomorphism is the canonical comparison. -/
@[simp]
theorem pullbackInternalHomIso_hom :
    (pullbackInternalHomIso E f).hom = pullbackInternalHomComparison E f :=
  (rfl)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
