/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Standard
public import TauCeti.RepresentationTheory.FDRep.Basic
public import TauCeti.RepresentationTheory.SU2.Basic

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
  `stdFDRep K` and `stdFDRep H` when `K = H.map (MulAut.conj g : SU2 →* SU2)`, with vector
  evaluation lemmas `TauCeti.SU2.isoToLinearEquiv_stdFDRepConjIso_apply` and
  `TauCeti.SU2.isoToLinearEquiv_stdFDRepConjIso_symm_apply`.
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

open CategoryTheory in
private noncomputable def stdFDRepConjMidEquiv {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) :
    ↥((Action.res (FGModuleCat ℂ)
        ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)) :
          H →* K)).obj
        (FDRep.of (stdRep K))).V ≃ₗ[ℂ]
      ↥(FDRep.of (stdRep H)).V :=
  LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin (toGL g⁻¹))

private theorem stdFDRepConjMidEquiv_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    stdFDRepConjMidEquiv hK v = TauCeti.stdRep ℂ 2 (toGL g⁻¹) v :=
  -- `stdFDRepConjMidEquiv` is defined as `toLinearEquiv (toLin (toGL g⁻¹))` across the
  -- definitional equality between `Action.res` / `FDRep.of` carriers and `Fin 2 → ℂ`.
  (LinearMap.GeneralLinearGroup.coe_toLinearEquiv
      (Matrix.GeneralLinearGroup.toLin (toGL g⁻¹))).symm ▸
    by rw [Matrix.GeneralLinearGroup.toLin_apply, ← TauCeti.stdRep_apply]

open CategoryTheory in
private noncomputable def stdFDRepConjMid {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) :
    (Action.res (FGModuleCat ℂ)
        ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)) :
          H →* K)).obj
        (FDRep.of (stdRep K)) ≅
      FDRep.of (stdRep H) :=
  let φ : H →* K :=
    (((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm) : H ≃* K)
  LinearEquiv.toFDRepIso (X := (Action.res (FGModuleCat ℂ) φ).obj (FDRep.of (stdRep K)))
    (Y := FDRep.of (stdRep H)) (stdFDRepConjMidEquiv hK) fun h v ↦ by
    have hval : ((φ h : K) : SU2) = g * h.val * g⁻¹ := by
      simp only [φ, MonoidHom.coe_ofClass, MulEquiv.trans_apply,
        MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
    rw [LinearMap.congr_fun (FDRep.res_ρ φ (FDRep.of (stdRep K)) h) v, FDRep.of_ρ', FDRep.of_ρ']
    -- View `v` in `Fin 2 → ℂ` (definitionally equal to the `Action.res` / `FDRep.of` carrier)
    -- so `stdFDRepConjMidEquiv_apply` and `TauCeti.stdRep` composition lemmas apply directly.
    let x : Fin 2 → ℂ := v
    change stdFDRepConjMidEquiv hK (stdRep K (φ h) x) = stdRep H h (stdFDRepConjMidEquiv hK x)
    rw [stdFDRepConjMidEquiv_apply, stdFDRepConjMidEquiv_apply hK x,
      stdRep_apply_apply, stdRep_apply_apply, TauCeti.stdRep_apply_apply,
      TauCeti.stdRep_apply_apply, coe_toGL, hval, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Submonoid.coe_mul, ← Submonoid.coe_mul, ← mul_assoc, inv_mul_cancel_left]

open CategoryTheory in
private theorem isoToLinearEquiv_stdFDRepConjMid_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (stdFDRepConjMid hK) v =
      ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdFDRepConjMid, FDRep.isoToLinearEquiv_toFDRepIso, stdFDRepConjMidEquiv_apply,
    TauCeti.stdRep_apply_apply, coe_toGL]

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
  (Action.res (FGModuleCat ℂ)
      ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)) : H →* K)).mapIso
      (eqToIso (stdFDRep_def K)) ≪≫
    stdFDRepConjMid hK ≪≫
    (eqToIso (stdFDRep_def H)).symm

open CategoryTheory in
private theorem isoToLinearEquiv_stdFDRepConjIso_eq {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v)) =
      FDRep.isoToLinearEquiv (stdFDRepConjMid hK) v := by
  -- `Action.res.mapIso` preserves the underlying linear map (`Action.res_map_hom`) and each
  -- `eqToIso (stdFDRep_def _)` cancels with its inverse on the underlying `Fin 2 → ℂ`.
  rfl

open CategoryTheory in
/-- Evaluating `stdFDRepConjIso hK` on a vector multiplies on the left by `(g⁻¹ : Matrix ...)`. -/
theorem isoToLinearEquiv_stdFDRepConjIso_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v)) =
      ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [isoToLinearEquiv_stdFDRepConjIso_eq, isoToLinearEquiv_stdFDRepConjMid_apply]

open CategoryTheory in
private theorem isoToLinearEquiv_stdFDRepConjIso_symm_eq {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))
        ((FDRep.isoToLinearEquiv (stdFDRepConjIso hK)).symm
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v)) =
      (FDRep.isoToLinearEquiv (stdFDRepConjMid hK)).symm v := by
  -- `Action.res.mapIso` preserves the underlying linear map (`Action.res_map_hom`) and each
  -- `eqToIso (stdFDRep_def _)` cancels with its inverse on the underlying `Fin 2 → ℂ`.
  rfl

open CategoryTheory in
/-- Evaluating the inverse of `stdFDRepConjIso hK` on a vector multiplies on the left by
`(g : Matrix ...)`. -/
theorem isoToLinearEquiv_stdFDRepConjIso_symm_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))
        ((FDRep.isoToLinearEquiv (stdFDRepConjIso hK)).symm
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v)) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [isoToLinearEquiv_stdFDRepConjIso_symm_eq]
  apply (FDRep.isoToLinearEquiv (stdFDRepConjMid hK)).injective
  rw [LinearEquiv.apply_symm_apply, isoToLinearEquiv_stdFDRepConjMid_apply,
    Matrix.mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one,
    Matrix.one_mulVec]

end TauCeti.SU2
