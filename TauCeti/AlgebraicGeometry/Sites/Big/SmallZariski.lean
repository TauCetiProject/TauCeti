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

Let `S` be a scheme and `F` an `𝒪_S`-module, with big presheaf
`F^a = AlgebraicGeometry.Scheme.Modules.bigPresheaf F : (T, h) ↦ Γ(T, h^* F)`. On the small
Zariski site of `S`, the opens `V` of `S` viewed as `S`-schemes through their inclusions, this file
gives additive identifications `Γ(F, V) ≃+ F^a(V)` for each open `V`
(`AlgebraicGeometry.Scheme.Modules.bigPresheafOpensAddEquiv`), compatible with the restriction maps
(`AlgebraicGeometry.Scheme.Modules.bigPresheaf_map_bigPresheafOpensAddEquiv`). The identification
is the composite of `F ≅ h^* F` for `h = 𝟙 S` (`Scheme.Modules.pullbackId`) with the local
restriction map `AlgebraicGeometry.Scheme.Modules.bigSectionsRestrictLE` from the sections of
`h^* F` over `V` to the global sections of the pullback of `F` to `V`.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (F : S.Modules)

/-- For an open `V` of `S`, the sections of `F^a` over the `S`-scheme `V` are additively
identified with `Γ(F, V)`. -/
noncomputable def bigPresheafOpensAddEquiv (V : S.Opens) :
    Γ(F, V) ≃+ F.bigPresheaf.obj (op (Over.mk V.ι)) :=
  (sectionsLinearEquiv ((pullbackId S).app F).symm V).toAddEquiv.trans
    (AddEquiv.ofBijective ((sectionsLinearEquiv ((pullbackComp V.ι (𝟙 S)).app F ≪≫
        (pullbackCongr (Category.comp_id V.ι)).app F) ⊤).toAddMonoidHom.comp
          (V.ι.pullbackSectionsLE ((pullback (𝟙 S)).obj F) V ⊤ (by simp)).toAddMonoidHom)
      (by
        refine (congrArg Function.Bijective (funext fun s ↦ ?_)).mpr
          (bijective_bigSectionsRestrictLE_ι F (𝟙 S) V (Category.comp_id V.ι))
        exact (sectionsLinearEquiv_apply _ ⊤ _).trans (bigSectionsRestrictLE_apply ..).symm))

lemma bigPresheafOpensAddEquiv_apply (V : S.Opens) (s : Γ(F, V)) :
    F.bigPresheafOpensAddEquiv V s = bigSectionsRestrictLE F V.ι (Category.comp_id V.ι) V ⊤
      (by simp) (((pullbackId S).inv.app F).app V s) := by
  rw [bigSectionsRestrictLE_apply]
  exact (sectionsLinearEquiv_apply _ ⊤ _).trans
    (congrArg _ (congrArg _ (sectionsLinearEquiv_apply _ V s)))

/-- The identifications `bigPresheafOpensAddEquiv` are compatible with restriction: for opens
`W ≤ V` of `S`, restricting along `W ⟶ V` in the big site is restricting sections of `F`. -/
lemma bigPresheaf_map_bigPresheafOpensAddEquiv {V W : S.Opens} (hWV : W ≤ V) (s : Γ(F, V)) :
    F.bigPresheaf.map (Over.homMk (S.homOfLE hWV) (by simp) :
        Over.mk W.ι ⟶ Over.mk V.ι).op (F.bigPresheafOpensAddEquiv V s) =
      F.bigPresheafOpensAddEquiv W (F.presheaf.map (homOfLE hWV).op s) := by
  rw [bigPresheafOpensAddEquiv_apply, bigPresheafOpensAddEquiv_apply, bigPresheaf_map_apply]
  exact (bigSectionsRestrict_homMk_homOfLE F (Over.mk (𝟙 S)) hWV (Category.comp_id V.ι)
    (Category.comp_id W.ι) _).trans (congrArg _ (Hom.naturality_apply _ (homOfLE hWV) s).symm)

end AlgebraicGeometry.Scheme.Modules
