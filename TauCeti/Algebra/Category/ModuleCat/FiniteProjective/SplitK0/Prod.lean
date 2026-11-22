/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Module.Projective.RingHom
public import TauCeti.RingTheory.Finiteness.Basic

import TauCeti.Algebra.Group.Prod

/-!
# Split `K₀` of finitely generated projective modules over a binary product ring

For two possibly noncommutative rings `R` and `S`, this file proves the binary product
decomposition `TauCeti.finiteProjectiveModulesProdSplitK0Equiv` identifying `SplitK0` over `R × S`
with the product of the `SplitK0` groups over `R` and `S`.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Prop. 2.4 and §2.8.
-/

public section

open CategoryTheory

universe u

namespace TauCeti

variable (R S : Type u) [Ring R] [Ring S]

/-- **`SplitK0` of finite projective modules commutes with binary products of rings.** The forward
map sends a class over `R × S` to its extensions of scalars along the projections `RingHom.fst R S`
and `RingHom.snd R S`; the inverse sends a pair `(x, y)` to the sum of the restrictions of scalars
of `x` along `RingHom.fst R S` and of `y` along `RingHom.snd R S`. -/
noncomputable def finiteProjectiveModulesProdSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ×
        SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddEquiv.ofProdCoprod
    (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars
      (RingHom.finite_fst R S) (RingHom.projective_fst R S)))
    (SplitK0.map.{u, u} ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars
      (RingHom.finite_snd R S) (RingHom.projective_snd R S)))
    (SplitK0.hom_ext fun P ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply,
        SplitK0.map_of, AddMonoidHom.id_apply]
      let e {A : Type u} [Ring A] (p : R × S →+* A) hfin hproj :=
        (((ModuleCat.restrictScalars.{u} p).mapIso
          (eqToIso (p.finiteProjectiveModulesExtendScalars_obj_obj P).symm)) ≪≫ eqToIso
            (p.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj _).symm).toLinearEquiv
      rw [← SplitK0.of_biprod.{u}]
      exact (SplitK0.of_congr.{u} ((finiteProjectiveModules (R × S)).fullyFaithfulι.preimageIso
        (((BalancedExtension.prodModuleLinearEquiv R S P.obj).trans
          (LinearEquiv.prodCongr (e _ _ _) (e _ _ _))).trans
          (FiniteProjectiveModules.biprodLinearEquiv _ _).symm).toModuleIso)).symm)
    (SplitK0.map_extendScalars_comp_restrictScalars_self _ Prod.fst_surjective _ _)
    (SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (1, 0) rfl rfl)
    (SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (0, 1) rfl rfl)
    (SplitK0.map_extendScalars_comp_restrictScalars_self _ Prod.snd_surjective _ _)

@[simp] theorem finiteProjectiveModulesProdSplitK0Equiv_apply (x) :
    finiteProjectiveModulesProdSplitK0Equiv R S x =
      (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars x,
        SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars x) :=
  AddEquiv.ofProdCoprod_apply _ _ _ _ _ _ _ _ _ x

@[simp] theorem finiteProjectiveModulesProdSplitK0Equiv_symm_apply (x) :
    (finiteProjectiveModulesProdSplitK0Equiv R S).symm x =
      SplitK0.map.{u, u} ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_fst R S) (RingHom.projective_fst R S)) x.1 +
        SplitK0.map.{u, u} ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_snd R S) (RingHom.projective_snd R S)) x.2 :=
  AddEquiv.ofProdCoprod_symm_apply _ _ _ _ _ _ _ _ _ x

end TauCeti
