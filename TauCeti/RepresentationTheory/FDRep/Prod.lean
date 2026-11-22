/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.Intertwining
public import TauCeti.RepresentationTheory.Rep.Prod

/-!
# Products of finite representations through universe shrinking

`FDRep.ofShrinkProdIso` identifies the componentwise product on module-finite carriers with
the categorical biproduct of their shrunk objects. This permits direct-sum arguments for
carriers in different universes, retaining their actual actions. The comparison uses Mathlib's
concrete product in `Rep` and the fully faithful forgetful functor, with its object endpoints
identified explicitly by `FDRep.forget₂_obj`.
For commutative coefficients, the target endpoints are fixed as the native `FDRep.ρ` objects
when specializing the general-ring formula, so the comparisons do not need to unfold `ofShrink`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace FDRep

variable {R G V W : Type*} [CommRing R] [Monoid G]
  [AddCommGroup V] [Module R V] [Module.Finite R V]
  [AddCommGroup W] [Module R W] [Module.Finite R W]

/-- Shrinking a product of module-finite representations gives the biproduct of the
shrunk representations. -/
noncomputable def ofShrinkProdIso (π : Representation R G V) (ρ : Representation R G W)
    [HasBinaryBiproduct (ofShrink π) (ofShrink ρ)] :
    ofShrink (π.prod ρ) ≅ ofShrink π ⊞ ofShrink ρ := by
  let F := forget₂ (FDRep R G) (Rep R G)
  let e := (ofShrinkEquiv (π.prod ρ)).trans
    ((ofShrinkEquiv π).symm.prodCongr (ofShrinkEquiv ρ).symm)
  exact F.preimageIso (
    eqToIso (Y := Rep.of (ofShrink (π.prod ρ)).ρ)
      (forget₂_obj (ofShrink (π.prod ρ))) ≪≫ Rep.mkIso e ≪≫
      Rep.prodIsoProduct (Rep.of (ofShrink π).ρ) (Rep.of (ofShrink ρ).ρ) ≪≫
      (biprod.isoProd (Rep.of (ofShrink π).ρ) (Rep.of (ofShrink ρ).ρ)).symm ≪≫
      biprod.mapIso (eqToIso (Y := Rep.of (ofShrink π).ρ) (forget₂_obj (ofShrink π))).symm
        (eqToIso (Y := Rep.of (ofShrink ρ).ρ) (forget₂_obj (ofShrink ρ))).symm ≪≫
      (F.mapBiprod (ofShrink π) (ofShrink ρ)).symm)

variable (π : Representation R G V) (ρ : Representation R G W)
  [HasBinaryBiproduct (ofShrink π) (ofShrink ρ)]

/-- After restoring the original carriers, the first biproduct projection is the first
coordinate. -/
@[simp]
theorem ofShrinkProdIso_hom_fst_apply (v : ofShrink (π.prod ρ)) :
    ofShrinkEquiv π ((biprod.fst : ofShrink π ⊞ ofShrink ρ ⟶ ofShrink π).hom.hom.hom
      ((ofShrinkProdIso π ρ).hom.hom.hom v)) =
      (ofShrinkEquiv (π.prod ρ) v).1 := by
  rw [← comp_hom_hom_hom_apply]
  let F := forget₂ (FDRep R G) (Rep R G)
  let e := (ofShrinkEquiv (π.prod ρ)).trans
    ((ofShrinkEquiv π).symm.prodCongr (ofShrinkEquiv ρ).symm)
  have hf : (F.mapBiprod (ofShrink π) (ofShrink ρ)).hom ≫ biprod.fst = F.map biprod.fst := by
    rw [Functor.mapBiprod_hom, biprod.lift_fst]
  have h : F.map ((ofShrinkProdIso π ρ).hom ≫ biprod.fst) =
      (eqToIso (Y := Rep.of (ofShrink (π.prod ρ)).ρ)
        (forget₂_obj (ofShrink (π.prod ρ)))).hom ≫ (Rep.mkIso e).hom ≫
        Rep.ofHom (.fst R (ofShrink π).ρ (ofShrink ρ).ρ) ≫
        (eqToIso (Y := Rep.of (ofShrink π).ρ) (forget₂_obj (ofShrink π))).inv := by
    rw [Functor.map_comp, ← hf]
    simp [ofShrinkProdIso, F, e,
      -biprod.uniqueUpToIso_hom, -biprod.uniqueUpToIso_inv]
  -- Specialize the ring-level evaluation to the explicit native representation endpoints.
  have heval :
      ((eqToIso (Y := Rep.of (ofShrink (π.prod ρ)).ρ)
        (forget₂_obj (ofShrink (π.prod ρ)))).inv ≫
        F.map ((ofShrinkProdIso π ρ).hom ≫ biprod.fst) ≫
        (eqToIso (Y := Rep.of (ofShrink π).ρ) (forget₂_obj (ofShrink π))).hom).hom v =
      ((ofShrinkProdIso π ρ).hom ≫ biprod.fst).hom.hom.hom v :=
    eqToIso_inv_forget₂_map_hom_apply _ _
  rw [← heval, h]
  simp [e]

/-- After restoring the original carriers, the second biproduct projection is the second
coordinate. -/
@[simp]
theorem ofShrinkProdIso_hom_snd_apply (v : ofShrink (π.prod ρ)) :
    ofShrinkEquiv ρ ((biprod.snd : ofShrink π ⊞ ofShrink ρ ⟶ ofShrink ρ).hom.hom.hom
      ((ofShrinkProdIso π ρ).hom.hom.hom v)) =
      (ofShrinkEquiv (π.prod ρ) v).2 := by
  rw [← comp_hom_hom_hom_apply]
  let F := forget₂ (FDRep R G) (Rep R G)
  let e := (ofShrinkEquiv (π.prod ρ)).trans
    ((ofShrinkEquiv π).symm.prodCongr (ofShrinkEquiv ρ).symm)
  have hf : (F.mapBiprod (ofShrink π) (ofShrink ρ)).hom ≫ biprod.snd = F.map biprod.snd := by
    rw [Functor.mapBiprod_hom, biprod.lift_snd]
  have h : F.map ((ofShrinkProdIso π ρ).hom ≫ biprod.snd) =
      (eqToIso (Y := Rep.of (ofShrink (π.prod ρ)).ρ)
        (forget₂_obj (ofShrink (π.prod ρ)))).hom ≫ (Rep.mkIso e).hom ≫
        Rep.ofHom (.snd R (ofShrink π).ρ (ofShrink ρ).ρ) ≫
        (eqToIso (Y := Rep.of (ofShrink ρ).ρ) (forget₂_obj (ofShrink ρ))).inv := by
    rw [Functor.map_comp, ← hf]
    simp [ofShrinkProdIso, F, e,
      -biprod.uniqueUpToIso_hom, -biprod.uniqueUpToIso_inv]
  -- Specialize the ring-level evaluation to the explicit native representation endpoints.
  have heval :
      ((eqToIso (Y := Rep.of (ofShrink (π.prod ρ)).ρ)
        (forget₂_obj (ofShrink (π.prod ρ)))).inv ≫
        F.map ((ofShrinkProdIso π ρ).hom ≫ biprod.snd) ≫
        (eqToIso (Y := Rep.of (ofShrink ρ).ρ) (forget₂_obj (ofShrink ρ))).hom).hom v =
      ((ofShrinkProdIso π ρ).hom ≫ biprod.snd).hom.hom.hom v :=
    eqToIso_inv_forget₂_map_hom_apply _ _
  rw [← heval, h]
  simp [e]

/-- The first biproduct inclusion, followed by the inverse comparison, restores `(v, 0)`
on the original carriers. -/
@[simp]
theorem ofShrinkProdIso_inl_inv_apply (v : ofShrink π) :
    ofShrinkEquiv (π.prod ρ) ((ofShrinkProdIso π ρ).inv.hom.hom.hom
      ((biprod.inl : ofShrink π ⟶ ofShrink π ⊞ ofShrink ρ).hom.hom.hom v)) =
      (ofShrinkEquiv π v, 0) := by
  apply Prod.ext
  · rw [← ofShrinkProdIso_hom_fst_apply]
    rw [← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply, Iso.inv_hom_id_assoc, biprod.inl_fst]
    simp
  · rw [← ofShrinkProdIso_hom_snd_apply]
    rw [← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply, Iso.inv_hom_id_assoc, biprod.inl_snd]
    simp

/-- The second biproduct inclusion, followed by the inverse comparison, restores `(0, v)`
on the original carriers. -/
@[simp]
theorem ofShrinkProdIso_inr_inv_apply (v : ofShrink ρ) :
    ofShrinkEquiv (π.prod ρ) ((ofShrinkProdIso π ρ).inv.hom.hom.hom
      ((biprod.inr : ofShrink ρ ⟶ ofShrink π ⊞ ofShrink ρ).hom.hom.hom v)) =
      (0, ofShrinkEquiv ρ v) := by
  apply Prod.ext
  · rw [← ofShrinkProdIso_hom_fst_apply]
    rw [← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply, Iso.inv_hom_id_assoc, biprod.inr_fst]
    simp
  · rw [← ofShrinkProdIso_hom_snd_apply]
    rw [← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply,
      ← comp_hom_hom_hom_apply, Iso.inv_hom_id_assoc, biprod.inr_snd]
    simp

end FDRep
