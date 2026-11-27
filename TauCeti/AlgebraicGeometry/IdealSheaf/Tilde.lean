/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import TauCeti.AlgebraicGeometry.IdealSheaf.Sequence

/-!
# The ideal sheaf of an ideal on an affine scheme

For an ideal `J` of a commutative ring `R`, transport `J` along the isomorphism
`Scheme.ΓSpecIso R : Γ(Spec R, ⊤) ≅ R` to an ideal of global sections. Its ideal sheaf
`ofIdealTop (J.map (Scheme.ΓSpecIso R).inv.hom)` on `Spec R`, viewed as an `𝒪`-module, is the
quasi-coherent sheaf `J~` associated with the `R`-module `J` (`ofIdealTopSheafIsoTilde`). Its
global sections are `J` (`ofIdealTopSectionsEquiv`), and a quasi-coherent module on `Spec R` is
the sheaf associated with its global sections.

## Main declarations

* `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTopSectionsEquiv`: the `R`-linear isomorphism
  between `J` and the global sections of the ideal sheaf of `J` on `Spec R`.
* `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTopSheafIsoTilde`: the ideal sheaf of `J` on
  `Spec R` is `J~`.
-/

public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {R : CommRingCat.{u}} (J : Ideal R)

/-- The global section of the ideal sheaf of `J` on `Spec R` given by an element `a` of `J`. -/
noncomputable def ofIdealTopSectionsMk (a : J) :
    Γ((ofIdealTop (J.map (Scheme.ΓSpecIso R).inv.hom)).sheaf, ⊤) :=
  sectionMk _ ((Scheme.ΓSpecIso R).inv a.val) (by
    rw [sections_ofIdealTop_top]; exact Ideal.mem_map_of_mem _ a.property)

/-- The global section `ofIdealTopSectionsMk J a` is the function `a` on `Spec R`. -/
@[simp]
theorem sheafι_app_ofIdealTopSectionsMk (a : J) :
    Scheme.Modules.Hom.app (ofIdealTop (J.map (Scheme.ΓSpecIso R).inv.hom)).sheafι ⊤
        (ofIdealTopSectionsMk J a) =
      (Scheme.ΓSpecIso R).inv a.val :=
  sheafι_app_sectionMk _ _ _

/-- The global sections of the ideal sheaf of `J` on `Spec R` are `J`, as `R`-modules. -/
noncomputable def ofIdealTopSectionsEquiv :
    J ≃ₗ[R] Γ((ofIdealTop (J.map (Scheme.ΓSpecIso R).inv.hom)).sheaf, ⊤) :=
  LinearEquiv.ofBijective
    { toFun := ofIdealTopSectionsMk J
      map_add' a b := by
        simp only [ofIdealTopSectionsMk, Submodule.coe_add, map_add]
        exact sectionMk_add _ _ _
      map_smul' r a := by
        -- `R` acts on the global sections through `Γ(Spec R, ⊤) ≅ R` (`smul_Spec_def`).
        rw [RingHom.id_apply, Scheme.Modules.smul_Spec_def, ofIdealTopSectionsMk,
          ofIdealTopSectionsMk, smul_sectionMk]
        simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
        rw [Subsingleton.elim (⊤ : (Spec R).Opens).leTop (𝟙 ⊤), op_id,
          CategoryTheory.Functor.map_id, CommRingCat.id_apply] }
    ⟨fun a b h ↦ by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, ofIdealTopSectionsMk, sectionMk_inj] at h
        exact Subtype.ext
          (ConcreteCategory.injective_of_mono_of_preservesPullback (Scheme.ΓSpecIso R).inv h),
      fun t ↦ by
        -- `J.map φ⁻¹ ≤ J.comap φ` for the ring isomorphism `φ : Γ(Spec R, ⊤) ≅ R`.
        have key (x : Γ(Spec R, ⊤)) (hx : x ∈ J.map (Scheme.ΓSpecIso R).inv.hom) :
            (Scheme.ΓSpecIso R).hom x ∈ J :=
          Ideal.map_le_comap_of_inverse _ _ J
            (fun r ↦ (Scheme.ΓSpecIso R).inv_hom_id_apply r) hx
        have ht := sheafι_app_mem _ ⊤ t
        rw [sections_ofIdealTop_top] at ht
        exact ⟨⟨_, key _ ht⟩, ((sectionMk_inj _ _ _).mpr
          ((Scheme.ΓSpecIso R).hom_inv_id_apply _)).trans (sectionMk_sheafι_app _ t)⟩⟩

/-- `ofIdealTopSectionsEquiv J` sends `a ∈ J` to the global section `a` of the ideal sheaf. -/
@[simp]
theorem ofIdealTopSectionsEquiv_apply (a : J) :
    ofIdealTopSectionsEquiv J a = ofIdealTopSectionsMk J a :=
  (rfl)

/-- The ideal sheaf of an ideal `J` of `R` on `Spec R` is canonically isomorphic to the sheaf `J~`
associated with the `R`-module `J`. -/
noncomputable def ofIdealTopSheafIsoTilde :
    (ofIdealTop (J.map (Scheme.ΓSpecIso R).inv.hom)).sheaf ≅ tilde (ModuleCat.of R J) :=
  -- The ideal sheaf is quasi-coherent, hence the sheaf associated with its global sections, and
  -- these are `J` (`ofIdealTopSectionsEquiv`).
  (asIso (Scheme.Modules.fromTildeΓ _)).symm ≪≫
    (tilde.functor R).mapIso (ofIdealTopSectionsEquiv J).toModuleIso.symm

/-- The inverse of `ofIdealTopSheafIsoTilde J` is `J~ ≅ Γ(I)~ ⟶ I`, the counit of the
tilde–global sections adjunction preceded by `ofIdealTopSectionsEquiv J`. -/
theorem ofIdealTopSheafIsoTilde_inv :
    (ofIdealTopSheafIsoTilde J).inv =
      (tilde.functor R).map (ModuleCat.ofHom (ofIdealTopSectionsEquiv J).toLinearMap) ≫
        Scheme.Modules.fromTildeΓ _ :=
  (rfl)

end AlgebraicGeometry.Scheme.IdealSheafData
