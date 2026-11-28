/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
import TauCeti.AlgebraicGeometry.AffineScheme.Basic

/-!
# Factorization through a split projection on an affine open

`Scheme.Hom.comp_eq_comp_section_of_preimage_le` factors a map into an affine open using
`Scheme.Hom.toSpecΓ_SpecMap_appLE_fromSpec` and the pullback square for restriction.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Let `a` be a section of `p : X ⟶ Y` and let `p` induce an isomorphism on functions over an
open `U` of `Y`. If `f : X ⟶ Z` maps `p ⁻¹ᵁ U` into an affine open `V`, its restriction
to `p ⁻¹ᵁ U` agrees with `p ≫ a ≫ f`. -/
theorem comp_eq_comp_section_of_preimage_le {X Y Z : Scheme}
    (p : X ⟶ Y) {a : Y ⟶ X} (ha : a ≫ p = 𝟙 Y) (f : X ⟶ Z)
    {U : Y.Opens} {V : Z.Opens} [IsIso (p ∣_ U).appTop]
    (hV : IsAffineOpen V) (hf : p ⁻¹ᵁ U ≤ f ⁻¹ᵁ V) :
    (p ⁻¹ᵁ U).ι ≫ f = (p ⁻¹ᵁ U).ι ≫ p ≫ a ≫ f := by
  let r := p ∣_ U
  let q := (p ⁻¹ᵁ U).ι ≫ f
  have hq : (⊤ : (p ⁻¹ᵁ U).toScheme.Opens) ≤ q ⁻¹ᵁ V := fun x _ ↦ hf x.property
  let g := U.toScheme.toSpecΓ ≫ Spec.map (q.appLE V ⊤ hq ≫ inv r.appTop) ≫ hV.fromSpec
  have hg : r ≫ g = q := by
    dsimp only [g]
    rw [Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id]
    exact q.toSpecΓ_SpecMap_appLE_fromSpec hV hq
  have hpb := isPullback_morphismRestrict p U
  have hcomm : (𝟙 U.toScheme) ≫ U.ι = (U.ι ≫ a) ≫ p := by
    rw [Category.id_comp, Category.assoc, ha, Category.comp_id]
  have hsection : U.ι ≫ a ≫ f = g := by
    let b := hpb.lift (𝟙 U.toScheme) (U.ι ≫ a) hcomm
    have hbr : b ≫ r = 𝟙 _ := hpb.lift_fst _ _ _
    have hbi : b ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ a := hpb.lift_snd _ _ _
    calc
      _ = b ≫ q := by simp only [q, ← Category.assoc, hbi]
      _ = g := by rw [← hg, ← Category.assoc, hbr, Category.id_comp]
  calc
    _ = r ≫ g := hg.symm
    _ = _ := by rw [← hsection, ← Category.assoc, morphismRestrict_ι, Category.assoc]

end AlgebraicGeometry.Scheme.Hom
