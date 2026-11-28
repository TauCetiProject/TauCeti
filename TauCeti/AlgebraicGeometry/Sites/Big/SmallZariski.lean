/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Module

/-!
# Restricting a big-site module to the small Zariski site

Let `S` be a scheme and `F` an `𝒪_S`-module, with big presheaf
`F^a = AlgebraicGeometry.Scheme.Modules.bigPresheaf F : (T, h) ↦ Γ(T, h^* F)`. On the small
Zariski site of `S`, the opens `V` of `S` viewed as `S`-schemes through their inclusions, this file
gives additive identifications `Γ(F, V) ≃+ F^a(V) = Γ(V, ι_V^* F)` for each open `V`
(`AlgebraicGeometry.Scheme.Modules.bigPresheafOpensAddEquiv`), compatible with the restriction maps
(`AlgebraicGeometry.Scheme.Modules.bigPresheaf_map_bigPresheafOpensAddEquiv`) and with morphisms
of modules (`AlgebraicGeometry.Scheme.Modules.bigPresheafOpensAddEquiv_naturality`). The
identification pulls a section of `F` over `V` back along the inclusion `ι_V : V ⟶ S`
(`AlgebraicGeometry.Scheme.Hom.pullbackSectionsLE`).

For an `S`-scheme `(T, h)`, the pullback of a section of `F` over `V` to the open `h⁻¹ V` of `T`,
read on the `S`-scheme `h⁻¹ V`, is the restriction of the corresponding section of `F^a` along
`h⁻¹ V ⟶ V` (`AlgebraicGeometry.Scheme.Modules.bigOpenAddEquiv_pullbackSections`).
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}} (F : S.Modules)

/-- For an open `V` of `S`, the sections of `F^a` over the `S`-scheme `V`, the global sections of
the pullback of `F` to `V`, are additively identified with `Γ(F, V)` by pulling sections back. -/
noncomputable def bigPresheafOpensAddEquiv (V : S.Opens) :
    Γ(F, V) ≃+ Γ((pullback V.ι).obj F, ⊤) :=
  AddEquiv.ofBijective (V.ι.pullbackSectionsLE F V ⊤ (by simp)).toAddMonoidHom
    (bijective_pullbackSectionsLE_ι F V ⊤ rfl)

lemma bigPresheafOpensAddEquiv_apply (V : S.Opens) (s : Γ(F, V)) :
    F.bigPresheafOpensAddEquiv V s = V.ι.pullbackSectionsLE F V ⊤ (by simp) s :=
  (rfl)

lemma bigPresheafOpensAddEquiv_smul (V : S.Opens) (r : Γ(S, V)) (s : Γ(F, V)) :
    F.bigPresheafOpensAddEquiv V (r • s) =
      (V.ι.appLE V ⊤ (by simp)).hom r • F.bigPresheafOpensAddEquiv V s := by
  rw [bigPresheafOpensAddEquiv_apply, bigPresheafOpensAddEquiv_apply, map_smulₛₗ]

/-- The identifications `bigPresheafOpensAddEquiv` are compatible with restriction: for opens
`W ≤ V` of `S`, restricting along `W ⟶ V` in the big site is restricting sections of `F`. -/
lemma bigPresheaf_map_bigPresheafOpensAddEquiv {V W : S.Opens} (hWV : W ≤ V) (s : Γ(F, V)) :
    F.bigPresheaf.map (Over.homMk (S.homOfLE hWV) (by simp) :
        Over.mk W.ι ⟶ Over.mk V.ι).op (F.bigPresheafOpensAddEquiv V s) =
      F.bigPresheafOpensAddEquiv W (F.presheaf.map (homOfLE hWV).op s) := by
  rw [bigPresheafOpensAddEquiv_apply, bigPresheafOpensAddEquiv_apply, bigPresheaf_map_apply,
    Hom.pullbackSectionsLE_map]
  · exact bigSectionsRestrict_pullbackSectionsLE F _ V _ _ s
  · exact fun x _ ↦ hWV x.property

variable {F} in
/-- The identifications `bigPresheafOpensAddEquiv` commute with a morphism `φ : F ⟶ G`, which acts
on the global sections of the pullbacks to `V` through its pullback. -/
@[simp]
lemma bigPresheafOpensAddEquiv_naturality {G : S.Modules} (φ : F ⟶ G) (V : S.Opens)
    (s : Γ(F, V)) :
    ((pullback V.ι).map φ).app ⊤ (F.bigPresheafOpensAddEquiv V s) =
      G.bigPresheafOpensAddEquiv V (φ.app V s) := by
  rw [bigPresheafOpensAddEquiv_apply, bigPresheafOpensAddEquiv_apply]
  exact Hom.pullbackSectionsLE_naturality V.ι F V ⊤ _ φ s

/-- For an `S`-scheme `(T, h)` and an open `V` of `S`, the `S`-morphism from the open
subscheme `h⁻¹ V` of `T` to the open subscheme `V` of `S`. -/
noncomputable abbrev bigPreimageHom (T : Over S) (V : S.Opens) :
    Over.mk ((T.hom ⁻¹ᵁ V).ι ≫ T.hom) ⟶ Over.mk V.ι :=
  Over.homMk (T.hom.resLE V (T.hom ⁻¹ᵁ V) le_rfl) (Scheme.Hom.resLE_comp_ι _ _)

/-- The pullback to `h⁻¹ V` of a section of `F` over `V`, read on the `S`-scheme `h⁻¹ V`, is the
restriction of that section from the `S`-scheme `V`. -/
lemma bigOpenAddEquiv_pullbackSections (T : Over S) (V : S.Opens) (s : Γ(F, V)) :
    bigOpenAddEquiv F T (T.hom ⁻¹ᵁ V) (T.hom.pullbackSections F V s) =
      bigSectionsRestrict F (bigPreimageHom T V) (F.bigPresheafOpensAddEquiv V s) := by
  have hV : ⊤ ≤ ((T.hom ⁻¹ᵁ V).ι ≫ T.hom) ⁻¹ᵁ V := by simp
  rw [bigOpenAddEquiv_apply, ← Hom.pullbackSectionsLE_self,
    bigSectionsRestrictLE_pullbackSectionsLE F _ rfl V _ ⊤ le_rfl _ hV,
    bigPresheafOpensAddEquiv_apply]
  exact (bigSectionsRestrict_pullbackSectionsLE F (bigPreimageHom T V) V (by simp) hV s).symm

end AlgebraicGeometry.Scheme.Modules
