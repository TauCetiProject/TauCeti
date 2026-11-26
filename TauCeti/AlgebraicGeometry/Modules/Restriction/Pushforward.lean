/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic

/-!
# Restriction maps of pushforwards of module sheaves

For open immersions `i : W ⟶ U` and `j : U ⟶ X` with composite `k`, this file constructs the
restriction map `j_* M ⟶ k_* (M|_W)` of module sheaves on `X`
(`AlgebraicGeometry.Scheme.Modules.pushforwardRestriction`), which on sections restricts sections
of `M` from `j⁻¹ T` to the image of `k⁻¹ T`.

* `Scheme.Modules.restrictFunctorComp_inv_app_comp_restrictFunctor_map_pushforwardRestriction_app`:
  restricted to `W`, the restriction map followed by the counit of `k` is the restriction of the
  counit of `j`.
* `Scheme.Modules.isIso_restrictFunctor_map_pushforwardRestriction_app`: for
  opens `W ≤ V` and `U` of `X` with `U ⊓ V ≤ W`, the restriction map
  `(V.ι)_* M ⟶ (W.ι)_* (M|_W)` becomes an isomorphism after restriction to `U`.

These are the termwise inputs of the restriction maps of total direct images in
`TauCeti.AlgebraicGeometry.Modules.Derived.OpenImmersion`.
-/

public section

noncomputable section

open CategoryTheory Functor

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Restriction

variable {W U X : Scheme.{u}} (i : W ⟶ U) (j : U ⟶ X) (k : W ⟶ X) (w : i ≫ j = k)
  [IsOpenImmersion i]

/-- For open immersions `i : W ⟶ U` and `j : U ⟶ X` with composite `k`, the restriction map
`j_* M ⟶ k_* (M|_W)` of module sheaves on `X`: the pushforward along `j` of the unit
`M ⟶ i_* (M|_W)` of the adjunction between restriction and pushforward along `i`, followed by
the identification `j_* i_* = k_*`. On sections over an open `T` of `X` it restricts sections of
`M` over `j⁻¹ T` to the image under `i` of `k⁻¹ T`. -/
def pushforwardRestriction : pushforward j ⟶ restrictFunctor i ⋙ pushforward k :=
  whiskerRight (restrictAdjunction i).unit (pushforward j) ≫
    whiskerLeft (restrictFunctor i) ((pushforwardComp i j).hom ≫ (pushforwardCongr w).hom)

@[simp]
lemma pushforwardRestriction_app_app (M : U.Modules) (T : X.Opens) :
    ((pushforwardRestriction i j k w).app M).app T =
      M.presheaf.map (homOfLE (show i ''ᵁ (k ⁻¹ᵁ T) ≤ j ⁻¹ᵁ T by
        subst w; exact i.image_preimage_le (j ⁻¹ᵁ T))).op := by
  subst w
  simp only [pushforwardRestriction, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app]
  -- Both sides restrict sections of `M`. The sections of `k_* (M|_W)` are sections of `M` only
  -- after unfolding `pushforward` and `restrict`, hence `erw`; morphisms of opens are unique.
  erw [← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

/-- Restricted to `W` along `k`, the restriction map `j_* M ⟶ k_* (M|_W)` followed by the counit of
`k` is the restriction to `W` of the counit `(j_* M)|_U ⟶ M` of `j`, up to the comparison
`((j_* M)|_U)|_W ≅ (j_* M)|_W`. -/
lemma restrictFunctorComp_inv_app_comp_restrictFunctor_map_pushforwardRestriction_app
    [IsOpenImmersion j] [IsOpenImmersion k] (M : U.Modules) :
    ((restrictFunctorComp i j).inv.app _ ≫ (restrictFunctorCongr w).hom.app _) ≫
      (restrictFunctor k).map ((pushforwardRestriction i j k w).app M) ≫
        (restrictAdjunction k).counit.app ((restrictFunctor i).obj M) =
      (restrictFunctor i).map ((restrictAdjunction j).counit.app M) := by
  refine hom_ext _ _ fun T ↦ ?_
  -- On sections, restriction acts on a morphism as the morphism over the image.
  have h₁ : ((restrictFunctor k).map ((pushforwardRestriction i j k w).app M)).app T =
      ((pushforwardRestriction i j k w).app M).app (k ''ᵁ T) := rfl
  have h₂ : ((restrictFunctor i).map ((restrictAdjunction j).counit.app M)).app T =
      ((restrictAdjunction j).counit.app M).app (i ''ᵁ T) := rfl
  simp only [Hom.comp_app, h₁, h₂, restrictFunctorComp_inv_app_app,
    restrictFunctorCongr_hom_app_app, restrictAdjunction_counit_app_app,
    pushforwardRestriction_app_app, restrict_map, eqToHom_map]
  -- The sections of `j_* M` and of `M|_W` are sections of `M`, and their restriction maps are
  -- those of `M`, but only after unfolding `pushforward` and `restrict`, hence `erw`. Merge the
  -- two pairs of restriction maps, write the first as a restriction map of `M` and merge again;
  -- the composite restriction maps agree since morphisms of opens are unique.
  erw [← Functor.map_comp, ← Functor.map_comp]
  simp only [← op_comp]
  erw [pushforward_obj_presheaf_map, ← Functor.map_comp]
  exact congrArg M.presheaf.map (Subsingleton.elim _ _)

/-- For opens `W ≤ V` and `U` of `X` with `U ⊓ V ≤ W`, the restriction map
`(V.ι)_* M ⟶ (W.ι)_* (M|_W)` becomes an isomorphism after restriction to `U`: over an open
contained in `U`, both sides are the sections of `M` over its intersection with `V`. -/
lemma isIso_restrictFunctor_map_pushforwardRestriction_app {X : Scheme.{u}} {U V W : X.Opens}
    (hWV : W ≤ V) (hUVW : U ⊓ V ≤ W) (M : V.toScheme.Modules) :
    IsIso ((restrictFunctor U.ι).map
      ((pushforwardRestriction (X.homOfLE hWV) V.ι W.ι (X.homOfLE_ι hWV)).app M)) := by
  refine isIso_restrictFunctor_map_of_isIso_app _ U fun T hT ↦ ?_
  rw [pushforwardRestriction_app_app]
  have e : (X.homOfLE hWV) ''ᵁ (W.ι ⁻¹ᵁ T) = V.ι ⁻¹ᵁ T := by
    rw [← X.homOfLE_ι hWV, Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.opensRange_homOfLE, inf_eq_right]
    intro x hx
    exact hUVW ⟨hT hx, x.property⟩
  -- Morphisms of opens are unique, so the restriction is along the equality `e`.
  rw [show homOfLE _ = eqToHom e from rfl]
  exact (M.presheaf.mapIso (eqToIso e).op).isIso_hom

end Restriction

end AlgebraicGeometry.Scheme.Modules
