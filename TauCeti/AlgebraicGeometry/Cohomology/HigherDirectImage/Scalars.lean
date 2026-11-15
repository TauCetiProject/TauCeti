/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Presheaf
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Opens
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import TauCeti.Algebra.Homology.HomologicalComplex.PresheafOfModules

/-!
# Scalars on higher direct image presheaves

For `f : X ⟶ Y`, derived pushforward with values in module presheaves carries
multiplication by the pullback of a global function to multiplication by its
restriction. The result is
`Scheme.Hom.higherDirectImagePresheaf_map_globalSectionsSmul_app`.

This computes the scalar action on the module presheaf whose sheafification is
`Rⁿ f_* M`. Under the identification of its sections over `U` with `Hⁿ(f⁻¹ U, M)`, the
action of a global function `r` on `Y` is the action of its pullback `f^* r` on cohomology
through coefficient multiplication
(`Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_smul`). This is how localization
criteria for cohomology apply to higher direct images.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Propositions 8.1 and 8.5.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Derived pushforward with values in module presheaves sends multiplication by
the pullback of a global function to multiplication by its restriction. -/
-- The explicit scalar type identifies the structure presheaf with the ring presheaf
-- of the module category; typeclass search does not unfold this identification.
@[simp]
lemma higherDirectImagePresheaf_map_globalSectionsSmul_app (M : X.Modules) (n : ℕ)
    (r : Γ(Y, ⊤)) (U : Y.Opens)
    (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op U)) :
    ((f.higherDirectImagePresheaf n).map (M.globalSectionsSmul (f.appTop r))).app (.op U) x =
      (show Y.ringCatSheaf.obj.obj (.op U) from Y.presheaf.map U.leTop.op r) • x := by
  let := Functor.additive_of_preserves_binary_products
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y)
  let F := Scheme.Modules.pushforward f ⋙ Scheme.Modules.toPresheafOfModules Y
  let P := injectiveResolution M
  let ψ : P.cocomplex ⟶ P.cocomplex :=
    { f i := (P.cocomplex.X i).globalSectionsSmul (f.appTop r)
      comm' i j _ := globalSectionsSmul_naturality (P.cocomplex.d i j) _ }
  have hψ : P.ι.f 0 ≫ ψ.f 0 = M.globalSectionsSmul (f.appTop r) ≫ P.ι.f 0 :=
    (globalSectionsSmul_naturality (P.ι.f 0) _).symm
  let e := P.isoRightDerivedObj F n
  have : IsIso (e.hom.app (.op U)) := inferInstanceAs
    (IsIso ((PresheafOfModules.evaluation Y.ringCatSheaf.obj (.op U)).map e.hom))
  apply (ModuleCat.mono_iff_injective (e.hom.app (.op U))).mp inferInstance
  have h := congrArg (fun g ↦ g.app (.op U))
    (InjectiveResolution.isoRightDerivedObj_hom_naturality
      (M.globalSectionsSmul (f.appTop r)) P P ψ hψ F n)
  rw [PresheafOfModules.comp_app, PresheafOfModules.comp_app] at h
  have hx := ((ConcreteCategory.comp_apply _ _ x).symm.trans
    (ConcreteCategory.congr_hom h x)).trans (ConcreteCategory.comp_apply _ _ x)
  refine hx.trans (Eq.trans ?_ ((e.hom.app (.op U)).hom.map_smul _ _).symm)
  apply HomologicalComplex.homologyMap_app_eq_smul
  intro z
  -- The composite functor forgets the sheaf condition after pushforward, so its
  -- components are those of pushforward with their module structures retained.
  change ((pushforward f).map
    ((P.cocomplex.X n).globalSectionsSmul (f.appTop r))).app U z = _
  rw [pushforward_map_globalSectionsSmul, globalSectionsSmul_app]
  exact ((pushforward f).obj (P.cocomplex.X n)).smul_apply _ _

/-- Under the identification of the sections over `U` of the derived module presheaf with
`Hⁿ(f⁻¹ U, M)`, multiplication by the restriction of a global function `r` on `Y` is
multiplication by its pullback `f^* r`, acting on cohomology through `M`. -/
-- The cohomology presheaf evaluated at `U` is the cohomology of `f⁻¹ U`; typeclass search does not
-- unfold this identification to find the module structure over global functions.
-- Apply before simp normalizes the source and target presheaf section types.
@[simp↓]
lemma higherDirectImagePresheafToPresheafIso_hom_app_smul (M : X.Modules) (n : ℕ)
    (r : Γ(Y, ⊤)) (U : Y.Opens) (x : ((f.higherDirectImagePresheaf n).obj M).obj (.op U)) :
    (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op U)
        ((show Y.ringCatSheaf.obj.obj (.op U) from Y.presheaf.map U.leTop.op r) • x) =
      f.appTop r • (show TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyOn M n (f ⁻¹ᵁ U) from
        (f.higherDirectImagePresheafToPresheafIso M n).hom.app (.op U) x) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (f.higherDirectImagePresheafToPresheafIso_naturality (M.globalSectionsSmul (f.appTop r)) n)
    (.op U)) x
  simp only [NatTrans.comp_app] at h
  rw [← higherDirectImagePresheaf_map_globalSectionsSmul_app, cohomologyOn_smul_def]
  exact h

end AlgebraicGeometry.Scheme.Hom
