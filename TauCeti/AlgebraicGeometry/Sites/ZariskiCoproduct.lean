/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# Gluing morphisms out of a coproduct of schemes into a Zariski sheaf

A presheaf `F` on schemes that is a sheaf for the big Zariski topology sends coproducts of schemes
to products. Hence morphisms `a i : h_{U i} ⟶ F` from the functors of points of schemes `U i` glue
to a morphism `h_{∐ U i} ⟶ F` restricting to each `a i`.

## Main results

* `TauCeti.AlgebraicGeometry.exists_yoneda_sigma_desc`: morphisms `h_{U i} ⟶ F` to a Zariski
  sheaf glue to a morphism `h_{∐ U i} ⟶ F`.
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- Morphisms `a i : h_{U i} ⟶ F` from schemes to a sheaf for the Zariski topology glue to a
morphism `h_{∐ U i} ⟶ F` restricting to each `a i`. -/
theorem exists_yoneda_sigma_desc {F : Scheme.{u}ᵒᵖ ⥤ Type u} {ι : Type u} {U : ι → Scheme.{u}}
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F) (a : ∀ i, yoneda.obj (U i) ⟶ F) :
    ∃ b : yoneda.obj (∐ U) ⟶ F, ∀ i, yoneda.map (Sigma.ι U i) ≫ b = a i := by
  have := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology (ι := ι) hF
  let t := isLimitFanMkObjOfIsLimit F _ _ (Cofan.IsColimit.op (coproductIsCoproduct U))
  let f i : PUnit.{u + 1} ⟶ F.obj (op (U i)) := TypeCat.ofHom fun _ ↦ yonedaEquiv (a i)
  let x := Fan.IsLimit.lift t f PUnit.unit
  refine ⟨yonedaEquiv.symm x, fun i ↦ ?_⟩
  have h := ConcreteCategory.congr_hom (Fan.IsLimit.fac t f i) PUnit.unit
  rw [yonedaEquiv_symm_naturality_left, Equiv.symm_apply_eq]
  simpa [x, f] using h

end TauCeti.AlgebraicGeometry
