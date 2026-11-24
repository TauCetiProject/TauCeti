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
  let e : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (Matrix.GeneralLinearGroup.toLin (toGL g⁻¹))
  LinearEquiv.toFDRepIso (X := (Action.res (FGModuleCat ℂ) φ).obj (FDRep.of (stdRep K)))
    (Y := FDRep.of (stdRep H)) (stdFDRepConjMidEquiv hK) fun h v ↦ by
    have he (x : Fin 2 → ℂ) : e x = TauCeti.stdRep ℂ 2 (toGL g⁻¹) x := by
      dsimp only [e]
      rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
        Matrix.GeneralLinearGroup.toLin_apply, ← TauCeti.stdRep_apply]
    have hval : ((φ h : K) : SU2) = g * h.val * g⁻¹ := by
      simp only [φ, MonoidHom.coe_ofClass, MulEquiv.trans_apply,
        MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
    rw [LinearMap.congr_fun (FDRep.res_ρ φ (FDRep.of (stdRep K)) h) v, FDRep.of_ρ', FDRep.of_ρ']
    let x : Fin 2 → ℂ := v
    change e (stdRep K (φ h) x) = stdRep H h (e x)
    calc
      e (stdRep K (φ h) x)
        = TauCeti.stdRep ℂ 2 (toGL g⁻¹) (TauCeti.stdRep ℂ 2 (toGL (g * h.val * g⁻¹)) x) := by
          rw [he, stdRep, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, hval]
      _ = TauCeti.stdRep ℂ 2 (toGL (g⁻¹ * (g * h.val * g⁻¹))) x := by
          rw [← mul_apply_eq_comp, ← map_mul, ← map_mul]
      _ = TauCeti.stdRep ℂ 2 (toGL (h.val * g⁻¹)) x := by
          rw [← mul_assoc, inv_mul_cancel_left]
      _ = stdRep H h (e x) := by
          rw [map_mul, map_mul, mul_apply_eq_comp, ← he x, stdRep, MonoidHom.comp_apply,
            MonoidHom.comp_apply, Subgroup.coe_subtype]

open CategoryTheory in
private theorem isoToLinearEquiv_stdFDRepConjMid_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (stdFDRepConjMid hK) v =
      (LinearMap.GeneralLinearGroup.toLinearEquiv
        (Matrix.GeneralLinearGroup.toLin (toGL g⁻¹))) v := by
  rw [stdFDRepConjMid, FDRep.isoToLinearEquiv_toFDRepIso]
  rfl

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
/-- Evaluating `stdFDRepConjIso hK` on a vector multiplies on the left by `(g⁻¹ : Matrix ...)`. -/
theorem isoToLinearEquiv_stdFDRepConjIso_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v)) =
      ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  let φ : H →* K :=
    (((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm) : H ≃* K)
  let x : (Action.res (FGModuleCat ℂ) φ).obj (stdFDRep K) :=
    (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v
  have hx :
      FDRep.isoToLinearEquiv ((Action.res (FGModuleCat ℂ) φ).mapIso (eqToIso (stdFDRep_def K))) x =
        v :=
    (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).apply_symm_apply v
  have hmid :
      FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
          (FDRep.isoToLinearEquiv (stdFDRepConjIso hK) x) =
        (LinearMap.GeneralLinearGroup.toLinearEquiv
          (Matrix.GeneralLinearGroup.toLin (toGL g⁻¹))) v := by
    simp only [stdFDRepConjIso, FDRep.isoToLinearEquiv_trans, LinearEquiv.trans_apply,
      FDRep.isoToLinearEquiv_symm, LinearEquiv.apply_symm_apply]
    change FDRep.isoToLinearEquiv (stdFDRepConjMid hK) _ = _
    rw [hx, isoToLinearEquiv_stdFDRepConjMid_apply]
  change FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
      (FDRep.isoToLinearEquiv (stdFDRepConjIso hK) x) = _
  rw [hmid, LinearMap.GeneralLinearGroup.coe_toLinearEquiv,
    Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply, coe_toGL]

open CategoryTheory in
/-- Evaluating the inverse of `stdFDRepConjIso hK` on a vector multiplies on the left by
`(g : Matrix ...)`. -/
theorem isoToLinearEquiv_stdFDRepConjIso_symm_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))
        ((FDRep.isoToLinearEquiv (stdFDRepConjIso hK)).symm
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v)) =
      (g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  let φ : H →* K :=
    (((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm) : H ≃* K)
  let y : (Action.res (FGModuleCat ℂ) φ).obj (stdFDRep K) :=
    (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)).symm
      ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v)
  let x : (Action.res (FGModuleCat ℂ) φ).obj (stdFDRep K) :=
    (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm
      ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)
  have hxy : FDRep.isoToLinearEquiv (stdFDRepConjIso hK) x =
      FDRep.isoToLinearEquiv (stdFDRepConjIso hK) y := by
    apply (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).injective
    have hy :
        FDRep.isoToLinearEquiv (stdFDRepConjIso hK) y =
          (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v :=
      (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)).apply_symm_apply _
    rw [hy, LinearEquiv.apply_symm_apply]
    change FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm
            ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v))) = v
    rw [isoToLinearEquiv_stdFDRepConjIso_apply]
    calc
      ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ ((g : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v)
        = TauCeti.stdRep ℂ 2 (toGL g⁻¹) (TauCeti.stdRep ℂ 2 (toGL g) v) := by
            rw [TauCeti.stdRep_apply_apply, TauCeti.stdRep_apply_apply, coe_toGL, coe_toGL]
      _ = TauCeti.stdRep ℂ 2 (toGL (g⁻¹ * g)) v := by
            rw [← mul_apply_eq_comp, ← map_mul, ← map_mul]
      _ = v := by simp
  have hxy' : x = y := (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)).injective hxy
  change FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K)) y = _
  have hxy'' : (y : stdFDRep K) = (x : stdFDRep K) := hxy'.symm
  rw [hxy'']
  exact (FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).apply_symm_apply _

end TauCeti.SU2
