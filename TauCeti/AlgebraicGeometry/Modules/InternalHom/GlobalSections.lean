/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.InternalHom.Basic
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Global functions acting on internal Hom

For modules on a scheme, precomposing a local linear map with multiplication by a global
function is the same as postcomposing with that multiplication. This identifies the two
scalar actions needed when passing between linear functionals and sections of a dual bundle.
-/

public section

open CategoryTheory MonoidalClosed

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- A global function acts on internal Hom equally by precomposition on the source and
postcomposition on the target. -/
@[simp]
theorem pre_globalSectionsSmul (M N : X.Modules) (c : Γ(X, ⊤)) :
    (pre (globalSectionsSmul M c)).app N = (ihom M).map (globalSectionsSmul N c) := by
  apply hom_ext
  intro U
  ext s
  apply (SheafOfModules.ihomObjEquiv M N U).injective
  -- The scheme-level `app` is additively bundled; the slice formulas use `val.app`.
  change SheafOfModules.ihomObjEquiv M N U
      ((((pre (globalSectionsSmul M c)).app N).val.app (.op U)) s) =
    SheafOfModules.ihomObjEquiv M N U
      ((((ihom M).map (globalSectionsSmul N c)).val.app (.op U)) s)
  refine (SheafOfModules.ihomObjEquiv_pre_app_app (R := X.sheaf) M N
    (globalSectionsSmul M c) U s).trans ?_
  refine Eq.trans ?_ (SheafOfModules.ihomObjEquiv_ihom_map_app (R := X.sheaf) M N
    (globalSectionsSmul N c) U s).symm
  ext ⟨V, ⟨⟨⟩⟩, f⟩ m
  -- Restriction to the slice site evaluates both scalar maps on the same open `V`.
  let : CommRing (X.ringCatSheaf.obj.obj (.op V)) :=
    inferInstanceAs (CommRing (X.presheaf.obj (.op V)))
  let l : M.val.obj (.op V) →ₗ[X.ringCatSheaf.obj.obj (.op V)] N.val.obj (.op V) :=
    ((SheafOfModules.ihomObjEquiv M N U s).val.app (.op (Over.mk f))).hom
  change l (((globalSectionsSmul M c).val.app (.op V)).hom m) =
    ((globalSectionsSmul N c).val.app (.op V)).hom (l m)
  have hM := ConcreteCategory.congr_hom (globalSectionsSmul_app M c V) m
  have hN := ConcreteCategory.congr_hom (globalSectionsSmul_app N c V) (l m)
  exact (congrArg l hM).trans ((l.map_smul _ m).trans hN.symm)

/-- Applying internal Hom to multiplication on its target is multiplication on the sheaf of
local linear maps. -/
@[simp]
theorem ihom_map_globalSectionsSmul (M N : X.Modules) (c : Γ(X, ⊤)) :
    (ihom M).map (globalSectionsSmul N c) = globalSectionsSmul ((ihom M).obj N) c := by
  apply hom_ext
  intro U
  ext s
  apply (SheafOfModules.ihomObjEquiv M N U).injective
  -- As above, expose the module-valued components rather than the additive scheme wrappers.
  change SheafOfModules.ihomObjEquiv M N U
      ((((ihom M).map (globalSectionsSmul N c)).val.app (.op U)) s) =
    SheafOfModules.ihomObjEquiv M N U
      (((globalSectionsSmul ((ihom M).obj N) c).val.app (.op U)) s)
  refine (SheafOfModules.ihomObjEquiv_ihom_map_app (R := X.sheaf) M N
    (globalSectionsSmul N c) U s).trans ?_
  have h := ConcreteCategory.congr_hom (globalSectionsSmul_app ((ihom M).obj N) c U) s
  refine Eq.trans ?_ (congrArg (SheafOfModules.ihomObjEquiv M N U) h).symm
  ext ⟨V, ⟨⟨⟩⟩, f⟩ m
  refine Eq.trans ?_ (SheafOfModules.ihomObjEquiv_smul_app (R := X.sheaf) M N U
    (X.presheaf.map U.leTop.op c) s f m).symm
  have hN := ConcreteCategory.congr_hom (globalSectionsSmul_app N c V)
    ((SheafOfModules.ihomObjEquiv M N U s).val.app (.op (Over.mk f)) m)
  refine hN.trans ?_
  have hc : X.presheaf.map f.op (X.presheaf.map U.leTop.op c) =
      X.presheaf.map V.leTop.op c := by
    rw [← Functor.map_comp_apply]
    rfl
  exact congrArg (fun r ↦ (N.smul r).asHom.hom
    ((SheafOfModules.ihomObjEquiv M N U s).val.app (.op (Over.mk f)) m)) hc.symm

end

end AlgebraicGeometry.Scheme.Modules
