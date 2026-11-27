/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# Restriction of ideal sheaves

Along an open immersion, the module sheaf of the inverse-image ideal is the restriction of
the original ideal module. The comparison respects their inclusions into the structure sheaf.
-/

public section

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}} (I : Y.IdealSheafData) (j : X ⟶ Y) [IsOpenImmersion j]

/-- Restriction and inverse image give the same ideal module along an open immersion. -/
def restrictSheafIso : I.sheaf.restrict j ≅ (I.comap j).sheaf :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app I.sheaf ≪≫ asIso (I.pullbackSheafHom j)

/-- The restriction comparison respects the ideal inclusions into the structure sheaf. -/
@[simp, reassoc]
theorem restrictSheafIso_hom_sheafι :
    (I.restrictSheafIso j).hom ≫ (I.comap j).sheafι =
      (Scheme.Modules.restrictFunctor j).map I.sheafι ≫
        (Scheme.Modules.restrictUnitIso j).hom := by
  simp only [restrictSheafIso, Iso.trans_hom, asIso_hom]
  -- The module unit is definitionally the structure sheaf; after composing the two
  -- comparison isomorphisms, elaborated rewriting identifies those presentations.
  erw [Category.assoc, I.pullbackSheafHom_sheafι, ← Category.assoc,
    ← (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality I.sheafι,
    Category.assoc, Scheme.Modules.restrictFunctorIsoPullback_unit]

private theorem restrictSheafIso_hom_sheafι_app (V : X.Opens)
    (t : Γ(I.sheaf.restrict j, V)) :
    (I.comap j).sheafι.app V ((I.restrictSheafIso j).hom.app V t) =
      (j.appIso V).hom
        (I.sheafι.app (j ''ᵁ V) ((I.sheaf.restrictAppIso j V).hom t)) := by
  have h := congrArg (fun φ : I.sheaf.restrict j ⟶ 𝟙_ X.Modules ↦ φ.app V t)
    (I.restrictSheafIso_hom_sheafι j)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at h
  rw [Scheme.Modules.restrictUnitIso_hom_app] at h
  exact h.trans (congrArg (j.appIso V).hom
    (ConcreteCategory.congr_hom
      (Scheme.Modules.restrictFunctor_map_app_restrictAppIso_hom j I.sheafι V) t))

/-- On an arbitrary open, membership in an inverse-image ideal along an open immersion is
membership in the original ideal after the canonical section-ring isomorphism. -/
theorem mem_sections_comap_iff (V : X.Opens) (s : Γ(X, V)) :
    s ∈ (I.comap j).sections V ↔ (j.appIso V).inv s ∈ I.sections (j ''ᵁ V) := by
  have : IsIso ((I.restrictSheafIso j).hom.app V) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance V
  constructor
  · intro hs
    obtain ⟨t, ht⟩ :=
      (ConcreteCategory.bijective_of_isIso ((I.restrictSheafIso j).hom.app V)).surjective
        ((I.comap j).sectionMk s hs)
    have h := I.restrictSheafIso_hom_sheafι_app j V t
    rw [ht, sheafι_app_sectionMk] at h
    have he := congrArg (j.appIso V).inv h
    have he' := he.trans (Iso.hom_inv_id_apply (j.appIso V) _)
    exact he'.symm ▸ I.sheafι_app_mem _ _
  · intro hs
    let t := (I.sheaf.restrictAppIso j V).inv (I.sectionMk ((j.appIso V).inv s) hs)
    have h := I.restrictSheafIso_hom_sheafι_app j V t
    simp only [t, Iso.inv_hom_id_apply, sheafι_app_sectionMk] at h
    exact h ▸ (I.comap j).sheafι_app_mem V _

end AlgebraicGeometry.Scheme.IdealSheafData
