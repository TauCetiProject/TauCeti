/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Restriction
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.SU2.Basic

/-!
# The standard two-dimensional representation of subgroups of `SU(2)`

Restricting `TauCeti.stdSLRep ℂ 2` along `H → SU(2) → SL₂(ℂ)` (`Matrix.specialUnitaryGroup.toSL`)
equips every subgroup `H : Subgroup SU2` with its faithful two-dimensional complex representation
`TauCeti.SU2.stdRep H` on `Fin 2 → ℂ` of determinant `1`, bundled in `FDRep ℂ H` as
`TauCeti.SU2.stdFDRep H`.

## Main definitions and results

* `TauCeti.SU2.stdRep` and `TauCeti.SU2.stdFDRep`: the tautological representation of
  `H : Subgroup SU2` on `Fin 2 → ℂ` and its `FDRep ℂ H` bundling, with faithfulness, determinant
  `1`, dimension `2`, and trace character lemmas.
* `TauCeti.SU2.stdFDRepConjIso`: isomorphism between the conjugation restriction of
  `stdFDRep K` and `stdFDRep H` when `K = H.map (MulAut.conj g : SU2 →* SU2)`, with vector
  evaluation lemmas `TauCeti.SU2.isoToLinearEquiv_stdFDRepConjIso_apply` and
  `TauCeti.SU2.isoToLinearEquiv_stdFDRepConjIso_symm_apply`.
-/

public section

open scoped Matrix

namespace TauCeti.SU2

/-- The tautological two-dimensional complex representation of `H : Subgroup SU2` on `Fin 2 → ℂ`. -/
def stdRep (H : Subgroup SU2) : Representation ℂ H (Fin 2 → ℂ) :=
  (TauCeti.stdSLRep ℂ 2).comp (Matrix.specialUnitaryGroup.toSL.comp H.subtype)

/-- `TauCeti.SU2.stdRep H` acts by matrix-vector multiplication on `Fin 2 → ℂ`. -/
@[simp]
theorem stdRep_apply (H : Subgroup SU2) (h : H) :
    stdRep H h = Matrix.mulVecLin (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    TauCeti.stdSLRep_apply, Matrix.specialUnitaryGroup.coe_toSL]

/-- Evaluating `TauCeti.SU2.stdRep H h` on a vector multiplies on the left by the underlying matrix
of `h`. -/
theorem stdRep_apply_apply (H : Subgroup SU2) (h : H) (v : Fin 2 → ℂ) :
    stdRep H h v = (h.val : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdRep, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    TauCeti.stdSLRep_apply_apply, Matrix.specialUnitaryGroup.coe_toSL]

/-- `TauCeti.SU2.stdRep H` is faithful for every subgroup `H : Subgroup SU2`. -/
theorem stdRep_injective (H : Subgroup SU2) : Function.Injective (stdRep H) :=
  (TauCeti.stdSLRep_injective ℂ 2).comp
    (Matrix.specialUnitaryGroup.toSL_injective.comp H.subtype_injective)

-- Match before `stdRep_apply` unfolds `stdRep H h`.
/-- Every element of `H : Subgroup SU2` acts with determinant `1` under `TauCeti.SU2.stdRep H`. -/
@[simp↓]
theorem det_stdRep (H : Subgroup SU2) (h : H) : LinearMap.det (stdRep H h) = 1 := by
  rw [stdRep, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    TauCeti.stdSLRep_apply, ← Matrix.toLin'_apply', LinearMap.det_toLin',
    (Matrix.specialUnitaryGroup.toSL h.val).property]

/-- The character of `TauCeti.SU2.stdRep H` at `h : H` is the matrix trace of `h`. -/
@[simp]
theorem char_stdRep (H : Subgroup SU2) (h : H) :
    (stdRep H).character h = Matrix.trace (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, _root_.Representation.character, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← _root_.Representation.character, TauCeti.char_stdSLRep,
    Matrix.specialUnitaryGroup.coe_toSL]

/-- The tautological two-dimensional complex representation of `H : Subgroup SU2` in `FDRep ℂ H`. -/
noncomputable def stdFDRep (H : Subgroup SU2) : FDRep ℂ H := FDRep.of (stdRep H)

/-- The bundled standard representation is `FDRep.of (stdRep H)`. -/
theorem stdFDRep_def (H : Subgroup SU2) : stdFDRep H = FDRep.of (stdRep H) := (rfl)

/-- The bundled standard representation `TauCeti.SU2.stdFDRep H` has dimension `2`. -/
@[simp]
theorem finrank_stdFDRep (H : Subgroup SU2) : Module.finrank ℂ (stdFDRep H) = 2 := by
  rw [stdFDRep_def, FDRep.finrank_of]; simp

/-- The action carried by `TauCeti.SU2.stdFDRep H` is faithful. -/
theorem ρ_stdFDRep_injective (H : Subgroup SU2) : Function.Injective (stdFDRep H).ρ := by
  rw [stdFDRep_def, FDRep.of_ρ']; exact stdRep_injective H

/-- Every element of `H : Subgroup SU2` acts with determinant `1` on `TauCeti.SU2.stdFDRep H`. -/
@[simp]
theorem det_ρ_stdFDRep (H : Subgroup SU2) (h : H) : LinearMap.det ((stdFDRep H).ρ h) = 1 := by
  rw [stdFDRep_def, FDRep.of_ρ']; exact det_stdRep H h

/-- The character of `TauCeti.SU2.stdFDRep H` at `h : H` is the matrix trace of `h`. -/
@[simp]
theorem character_stdFDRep (H : Subgroup SU2) (h : H) :
    (stdFDRep H).character h = Matrix.trace (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdFDRep_def, FDRep.character_of, char_stdRep]

private noncomputable def stdFDRepConjLinearEquiv (g : SU2) :
    (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.GeneralLinearGroup.toLinearEquiv
    (_root_.Representation.asGroupHom
      ((TauCeti.stdSLRep ℂ 2).comp Matrix.specialUnitaryGroup.toSL) g⁻¹)

private theorem stdFDRepConjLinearEquiv_apply (g : SU2) (v : Fin 2 → ℂ) :
    stdFDRepConjLinearEquiv g v =
      ((TauCeti.stdSLRep ℂ 2).comp Matrix.specialUnitaryGroup.toSL) g⁻¹ v := by
  rw [stdFDRepConjLinearEquiv, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    _root_.Representation.asGroupHom_apply]

private theorem stdFDRepConjLinearEquiv_symm_apply (g : SU2) (v : Fin 2 → ℂ) :
    (stdFDRepConjLinearEquiv g).symm v =
      ((TauCeti.stdSLRep ℂ 2).comp Matrix.specialUnitaryGroup.toSL) g v := by
  rw [stdFDRepConjLinearEquiv, ← LinearEquiv.coe_inv,
    ← LinearMap.GeneralLinearGroup.toLinearEquiv_inv,
    LinearMap.GeneralLinearGroup.coe_toLinearEquiv, ← map_inv,
    _root_.Representation.asGroupHom_apply, inv_inv]

private theorem stdFDRepConjLinearEquiv_equivariant {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (h : H) (v : Fin 2 → ℂ) :
    stdFDRepConjLinearEquiv g
        (stdRep K (((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm) h) v) =
      stdRep H h (stdFDRepConjLinearEquiv g v) := by
  have hval : ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm) h : K) :
      SU2) = g * h.val * g⁻¹ := by
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  dsimp only [stdRep, MonoidHom.comp_apply, Subgroup.coe_subtype]
  rw [stdFDRepConjLinearEquiv_apply, stdFDRepConjLinearEquiv_apply, hval,
    ← MonoidHom.comp_apply (TauCeti.stdSLRep ℂ 2) Matrix.specialUnitaryGroup.toSL,
    ← MonoidHom.comp_apply (TauCeti.stdSLRep ℂ 2) Matrix.specialUnitaryGroup.toSL,
    ← mul_apply_eq_comp, ← map_mul, ← mul_apply_eq_comp, ← map_mul,
    ← mul_assoc, inv_mul_cancel_left]

open CategoryTheory in
private noncomputable def stdFDRepConjEquiv {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) :
    ((Action.res (FGModuleCat ℂ)
        ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)) :
          H →* K)).obj
        (stdFDRep K)) ≃ₗ[ℂ]
      stdFDRep H :=
  (FGModuleCat.isoToLinearEquiv (eqToIso (Action.res_obj_V (FGModuleCat ℂ) _ (stdFDRep K)))).trans
    ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).trans
      ((stdFDRepConjLinearEquiv g).trans
        (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm))

open CategoryTheory in
/-- The carrier identification `Action.res_obj_V` is definitionally the identity, so its
`eqToIso` transport acts as the identity on underlying vectors. -/
private theorem fgModuleCat_eqToIso_res_obj_V_apply {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]
    (φ : G₁ →* G₂) (V : FDRep ℂ G₂) (x : V) :
    FGModuleCat.isoToLinearEquiv (eqToIso (Action.res_obj_V (FGModuleCat ℂ) φ V)) x = x :=
  (rfl)

open CategoryTheory in
/-- Inverse form of `fgModuleCat_eqToIso_res_obj_V_apply`. -/
private theorem fgModuleCat_eqToIso_res_obj_V_symm_apply {G₁ G₂ : Type*} [Monoid G₁] [Monoid G₂]
    (φ : G₁ →* G₂) (V : FDRep ℂ G₂) (x : V) :
    (FGModuleCat.isoToLinearEquiv (eqToIso (Action.res_obj_V (FGModuleCat ℂ) φ V))).symm x = x :=
  (rfl)

open CategoryTheory in
private theorem stdFDRepConjEquiv_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (stdFDRepConjEquiv hK ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v)) =
      stdFDRepConjLinearEquiv g v := by
  let φ : H →* K := ((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)
  have hv : ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v :
      ((Action.res (FGModuleCat ℂ) φ).obj (stdFDRep K)).V) =
      (FGModuleCat.isoToLinearEquiv
          (eqToIso (Action.res_obj_V (FGModuleCat ℂ) φ (stdFDRep K)))).symm
        ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v) :=
    (fgModuleCat_eqToIso_res_obj_V_symm_apply φ (stdFDRep K) _).symm
  rw [hv]
  dsimp only [stdFDRepConjEquiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

open CategoryTheory in
private theorem stdFDRepConjEquiv_symm_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))
        ((stdFDRepConjEquiv hK).symm
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v)) =
      (stdFDRepConjLinearEquiv g).symm v := by
  dsimp only [stdFDRepConjEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm]
  rw [fgModuleCat_eqToIso_res_obj_V_symm_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

open CategoryTheory in
private theorem stdFDRep_def_intertwine (H : Subgroup SU2) (h : H) (x : stdFDRep H) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H)) ((stdFDRep H).ρ h x) =
      stdRep H h (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H)) x) := by
  have hc := LinearMap.congr_fun (FDRep.Iso.conj_ρ (eqToIso (stdFDRep_def H)) h)
    (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H)) x)
  simpa [FDRep.of_ρ', LinearEquiv.conj_apply] using hc.symm

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
  LinearEquiv.toFDRepIso (stdFDRepConjEquiv hK) fun h v ↦ by
    apply (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).injective
    let φ : H →* K := ((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)
    have hres :
        FDRep.ρ ((Action.res (FGModuleCat ℂ) φ).obj (stdFDRep K)) h v =
          (FGModuleCat.isoToLinearEquiv
              (eqToIso (Action.res_obj_V (FGModuleCat ℂ) φ (stdFDRep K)))).symm
            ((stdFDRep K).ρ (φ h)
              (FGModuleCat.isoToLinearEquiv
                (eqToIso (Action.res_obj_V (FGModuleCat ℂ) φ (stdFDRep K))) v)) :=
      LinearMap.congr_fun (FDRep.res_ρ φ (stdFDRep K) h) v
    rw [stdFDRep_def_intertwine, hres]
    dsimp only [stdFDRepConjEquiv, LinearEquiv.trans_apply]
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, stdFDRep_def_intertwine]
    exact stdFDRepConjLinearEquiv_equivariant hK h _

open CategoryTheory in
/-- Evaluating `stdFDRepConjIso hK` on a vector multiplies on the left by `(g⁻¹ : Matrix ...)`. -/
theorem isoToLinearEquiv_stdFDRepConjIso_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v)) =
      ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdFDRepConjIso, FDRep.isoToLinearEquiv_toFDRepIso, stdFDRepConjEquiv_apply,
    stdFDRepConjLinearEquiv_apply, MonoidHom.comp_apply, TauCeti.stdSLRep_apply_apply,
    Matrix.specialUnitaryGroup.coe_toSL]

open CategoryTheory in
/-- Evaluating the inverse of `stdFDRepConjIso hK` on a vector multiplies on the left by
`(g : Matrix ...)`. -/
theorem isoToLinearEquiv_stdFDRepConjIso_symm_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))
        ((FDRep.isoToLinearEquiv (stdFDRepConjIso hK)).symm
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v)) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdFDRepConjIso, FDRep.isoToLinearEquiv_toFDRepIso, stdFDRepConjEquiv_symm_apply,
    stdFDRepConjLinearEquiv_symm_apply, MonoidHom.comp_apply, TauCeti.stdSLRep_apply_apply,
    Matrix.specialUnitaryGroup.coe_toSL]

end TauCeti.SU2
