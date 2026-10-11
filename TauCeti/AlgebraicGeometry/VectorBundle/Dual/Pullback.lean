/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.VectorBundle.InternalHom.Pullback

/-!
# Pullback of dual vector bundles

For a finite locally free sheaf `E`, pulling back its dual agrees with taking the dual of
its pullback. The comparison uses the canonical base-change map for internal Hom and the
canonical identification of the pullback of the structure sheaf with the structure sheaf.

## References

* The Stacks Project, Tag 0C6I (base change for sheaf Hom).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y)

/-- Pulling back a finite locally free sheaf's dual is canonically isomorphic to the dual
of its pullback. -/
def pullbackDualIso :
    (pullback f).obj (dual E) ≅ dual ((pullback f).obj E) :=
  ObjectProperty.isoMk _
    (eqToIso (pullback_obj_obj f (dual E)) ≪≫
      (pullbackIhomIso E f).app (𝟙_ Y.Modules) ≪≫
      (ihom ((Scheme.Modules.pullback f).obj E.obj)).mapIso
        (Scheme.Modules.pullbackObjUnitIso f) ≪≫
      eqToIso (congrArg (fun M : X.Modules ↦ (ihom M).obj (𝟙_ X.Modules))
        (pullback_obj_obj f E).symm))

/-- The underlying map is the canonical internal-Hom base-change comparison, followed by
the identification `f* 𝒪_Y ≅ 𝒪_X`. -/
@[simp]
theorem pullbackDualIso_hom_hom :
    (pullbackDualIso f E).hom.hom =
      eqToHom (pullback_obj_obj f (dual E)) ≫
        (pullbackIhomComparison E.obj f).app (𝟙_ Y.Modules) ≫
          (ihom ((Scheme.Modules.pullback f).obj E.obj)).map
            (Scheme.Modules.pullbackObjUnitIso f).hom ≫
              eqToHom (congrArg (fun M : X.Modules ↦ (ihom M).obj (𝟙_ X.Modules))
                (pullback_obj_obj f E).symm) := by
  simp only [pullbackDualIso, ObjectProperty.isoMk_hom, ObjectProperty.homMk_hom,
    Iso.trans_hom, Iso.app_hom, pullbackIhomIso_hom, Functor.mapIso_hom,
    eqToIso.hom]

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
