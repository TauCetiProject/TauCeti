/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.SymmetricPower
import TauCeti.RepresentationTheory.FDRep.Basic

/-!
# The standard two-dimensional representation of subgroups of `SU(2)`

Restricting `TauCeti.stdRep ℂ 2` along `H → SU(2) → GL₂(ℂ)` (`TauCeti.SU2.toGL`) equips every
subgroup `H : Subgroup SU2` with its faithful two-dimensional complex representation
`TauCeti.SU2.stdRep H` on `Fin 2 → ℂ` of determinant `1`, bundled in `FDRep ℂ H` as
`TauCeti.SU2.stdFDRep H`.

## Main definitions and results

* `TauCeti.SU2.stdRep` and `TauCeti.SU2.stdFDRep`: the tautological representation of
  `H : Subgroup SU2` on `Fin 2 → ℂ` and its `FDRep ℂ H` bundling, with faithfulness, determinant
  `1`, dimension `2`, and trace character lemmas.
* `TauCeti.SU2.stdFDRepConjIso`: isomorphism between the conjugation restriction of
  `stdFDRep K` and `stdFDRep H` when `K = H.map (MulAut.conj g : SU2 →* SU2)`.
-/

public section

open scoped Matrix

namespace TauCeti.SU2

/-- The tautological two-dimensional complex representation of `H : Subgroup SU2` on `Fin 2 → ℂ`. -/
def stdRep (H : Subgroup SU2) : Representation ℂ H (Fin 2 → ℂ) :=
  (TauCeti.stdRep ℂ 2).comp (toGL.comp H.subtype)

@[simp]
theorem stdRep_apply (H : Subgroup SU2) (h : H) :
    stdRep H h = Matrix.mulVecLin (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    TauCeti.stdRep_apply, coe_toGL]

theorem stdRep_apply_apply (H : Subgroup SU2) (h : H) (v : Fin 2 → ℂ) :
    stdRep H h v = (h.val : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdRep_apply, Matrix.mulVecLin_apply]

theorem stdRep_injective (H : Subgroup SU2) : Function.Injective (stdRep H) :=
  (TauCeti.stdRep_injective ℂ 2).comp (toGL_injective.comp H.subtype_injective)

-- Match before `stdRep_apply` unfolds `stdRep H h`.
@[simp↓]
theorem det_stdRep (H : Subgroup SU2) (h : H) : LinearMap.det (stdRep H h) = 1 := by
  rw [stdRep_apply, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  exact (Matrix.mem_specialUnitaryGroup_iff.mp h.val.property).right

@[simp]
theorem char_stdRep (H : Subgroup SU2) (h : H) :
    (stdRep H).character h = Matrix.trace (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, _root_.Representation.character, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← _root_.Representation.character, TauCeti.char_stdRep, coe_toGL]

/-- The tautological two-dimensional complex representation of `H : Subgroup SU2` in `FDRep ℂ H`. -/
noncomputable def stdFDRep (H : Subgroup SU2) : FDRep ℂ H := FDRep.of (stdRep H)

/-- The bundled standard representation is `FDRep.of (stdRep H)`. -/
theorem stdFDRep_def (H : Subgroup SU2) : stdFDRep H = FDRep.of (stdRep H) := (rfl)

@[simp]
theorem finrank_stdFDRep (H : Subgroup SU2) : Module.finrank ℂ (stdFDRep H) = 2 := by
  rw [stdFDRep_def, FDRep.finrank_of]; simp

theorem ρ_stdFDRep_injective (H : Subgroup SU2) : Function.Injective (stdFDRep H).ρ := by
  rw [stdFDRep_def, FDRep.of_ρ']; exact stdRep_injective H

@[simp]
theorem det_ρ_stdFDRep (H : Subgroup SU2) (h : H) : LinearMap.det ((stdFDRep H).ρ h) = 1 := by
  rw [stdFDRep_def, FDRep.of_ρ']; exact det_stdRep H h

@[simp]
theorem character_stdFDRep (H : Subgroup SU2) (h : H) :
    (stdFDRep H).character h = Matrix.trace (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdFDRep_def, FDRep.character_of, char_stdRep]

private theorem coe_mul (a b : SU2) :
    ((a * b : SU2) : Matrix (Fin 2) (Fin 2) ℂ) =
      (a : Matrix (Fin 2) (Fin 2) ℂ) * (b : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← coe_toGL, ← coe_toGL, ← coe_toGL, map_mul, Units.val_mul]

private theorem coe_mul_coe_inv (g : SU2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) * ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [← coe_toGL, ← coe_toGL, map_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]

private theorem coe_inv_mul_coe (g : SU2) :
    ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) * (g : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  rw [← coe_toGL, ← coe_toGL, map_inv, ← Units.val_mul, inv_mul_cancel, Units.val_one]

open CategoryTheory in
/-- Conjugation by `g : SU2` induces an isomorphism in `FDRep ℂ H` from the restriction of
`stdFDRep K` along conjugation `H ≃* K` (where `K = H.map (MulAut.conj g : SU2 →* SU2)`) to
`stdFDRep H`. -/
noncomputable def stdFDRepConjIso {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) :
    (Action.res (FGModuleCat ℂ)
        ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)) :
          H →* K)).obj
        (stdFDRep K) ≅
      stdFDRep H :=
  let φ : H →* K :=
    (((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm) : H ≃* K)
  let e : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
    { __ := Matrix.mulVecLin ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ)
      invFun := fun v ↦ (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v
      left_inv := fun v ↦ by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec, coe_mul_coe_inv, Matrix.one_mulVec]
      right_inv := fun v ↦ by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec] }
  let mid : (Action.res (FGModuleCat ℂ) φ).obj (FDRep.of (stdRep K)) ≅ FDRep.of (stdRep H) :=
    LinearEquiv.toFDRepIso (X := (Action.res (FGModuleCat ℂ) φ).obj (FDRep.of (stdRep K)))
      (Y := FDRep.of (stdRep H)) e fun h v ↦ by
      have hres :
          FDRep.ρ ((Action.res (FGModuleCat ℂ) φ).obj (FDRep.of (stdRep K))) h =
            (FDRep.of (stdRep K)).ρ (φ h) := by
        rw [← FDRep.hom_hom_action_ρ, ← FDRep.hom_hom_action_ρ, Action.res_obj_ρ]
        exact congrArg (fun f : End (FDRep.of (stdRep K)).V ↦ f.asHom.hom.hom)
          (MonoidHom.comp_apply (Action.ρ (FDRep.of (stdRep K))) φ h)
      have he (x : Fin 2 → ℂ) : e x = ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x := by
        simp only [e, LinearEquiv.coe_mk, Matrix.mulVecLin_apply]
      have hval : ((φ h : K) : SU2) = g * h.val * g⁻¹ := by
        simp only [φ, MonoidHom.coe_ofClass, MulEquiv.trans_apply,
          MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
      have hconj (x : Fin 2 → ℂ) :
          ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ stdRep K (φ h) x =
            stdRep H h (((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ x) := by
        rw [stdRep_apply_apply, stdRep_apply_apply, hval, coe_mul, coe_mul, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, coe_inv_mul_coe,
          Matrix.one_mul]
      rw [LinearMap.congr_fun hres v, FDRep.of_ρ', FDRep.of_ρ']
      calc e (stdRep K (φ h) v)
        _ = ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (stdRep K (φ h) v) := he _
        _ = stdRep H h (((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v) := hconj v
        _ = stdRep H h (e v) := congrArg (stdRep H h) (he v).symm
  (Action.res (FGModuleCat ℂ) φ).mapIso (eqToIso (stdFDRep_def K)) ≪≫
    mid ≪≫
    (eqToIso (stdFDRep_def H)).symm

end TauCeti.SU2
