/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Big.Module

/-!
# Restricting a big-site module to the small Zariski site

Let `S` be a scheme and `F` an `𝒪_S`-module. The big presheaf
`F^a = AlgebraicGeometry.Scheme.Modules.bigPresheaf F : (T, h) ↦ Γ(T, h^* F)` restricts to the
small Zariski site of `S`, the opens `V` of `S` viewed as `S`-schemes through their inclusions, and
there it gives back `F`: `F^a(V) ≃+ Γ(F, V)`
(`AlgebraicGeometry.Scheme.Modules.bigPresheafOpensAddEquiv`), compatibly with the restriction maps
(`AlgebraicGeometry.Scheme.Modules.bigPresheaf_map_bigPresheafOpensAddEquiv`). The identification
is the composite of `h^* F ≅ F` for `h = 𝟙 S` (`Scheme.Modules.pullbackId`) with the bijection
from the sections of `h^* F` over `V` to the global sections of the pullback of `F` to `V`
(`AlgebraicGeometry.Scheme.Modules.bijective_bigSectionsRestrictLE_ι`).
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (F : S.Modules)

/-- The local restriction map `bigSectionsRestrictLE` along the inclusion of an open `V`, as an
additive map from the sections of `h^* F` over `V` to the global sections of the pullback of `F`
to `V`. -/
noncomputable def bigSectionsRestrictLEOpensAddHom {X : Scheme.{u}} (h : X ⟶ S) (V : X.Opens) :
    Γ((pullback h).obj F, V) →+ Γ((pullback (V.ι ≫ h)).obj F, ⊤) where
  toFun := bigSectionsRestrictLE F V.ι rfl V ⊤ (by simp)
  map_zero' := by simp [bigSectionsRestrictLE_apply]
  map_add' s t := by simp [bigSectionsRestrictLE_apply]

/-- **The big presheaf restricted to the small Zariski site is `F`.** For an open `V` of `S`, the
value of `F^a` on the `S`-scheme `V` is `Γ(F, V)`. -/
noncomputable def bigPresheafOpensAddEquiv (V : S.Opens) :
    Γ(F, V) ≃+ F.bigPresheaf.obj (op (Over.mk (V.ι ≫ 𝟙 S))) :=
  AddEquiv.ofBijective ((bigSectionsRestrictLEOpensAddHom F (𝟙 S) V).comp
      (Hom.app ((pullbackId S).inv.app F) V).hom)
    ((bijective_bigSectionsRestrictLE_ι F (𝟙 S) V).comp
      (ConcreteCategory.bijective_of_isIso (Hom.app ((pullbackId S).inv.app F) V)))

lemma bigPresheafOpensAddEquiv_apply (V : S.Opens) (s : Γ(F, V)) :
    F.bigPresheafOpensAddEquiv V s =
      bigSectionsRestrictLE F V.ι rfl V ⊤ (by simp) (((pullbackId S).inv.app F).app V s) :=
  (rfl)

/-- The identifications `bigPresheafOpensAddEquiv` are compatible with restriction: for opens
`W ≤ V` of `S`, restricting along `W ⟶ V` in the big site is restricting sections of `F`. -/
lemma bigPresheaf_map_bigPresheafOpensAddEquiv {V W : S.Opens} (hWV : W ≤ V) (s : Γ(F, V)) :
    F.bigPresheaf.map (Over.homMk (S.homOfLE hWV) (by simp) :
        Over.mk (W.ι ≫ 𝟙 S) ⟶ Over.mk (V.ι ≫ 𝟙 S)).op (F.bigPresheafOpensAddEquiv V s) =
      F.bigPresheafOpensAddEquiv W (F.presheaf.map (homOfLE hWV).op s) := by
  rw [bigPresheafOpensAddEquiv_apply, bigPresheafOpensAddEquiv_apply, bigPresheaf_map_apply]
  refine (bigSectionsRestrict_homMk_homOfLE F (Over.mk (𝟙 S)) hWV _).trans ?_
  congr 1
  exact (Hom.naturality_apply ((pullbackId S).inv.app F) (homOfLE hWV) s).symm

end AlgebraicGeometry.Scheme.Modules
