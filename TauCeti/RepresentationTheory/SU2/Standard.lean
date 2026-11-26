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

/-- `TauCeti.SU2.stdRep H` acts by matrix-vector multiplication on `Fin 2 → ℂ`. -/
@[simp]
theorem stdRep_apply (H : Subgroup SU2) (h : H) :
    stdRep H h = Matrix.mulVecLin (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    TauCeti.stdRep_apply, coe_toGL]

/-- Evaluating `TauCeti.SU2.stdRep H h` on a vector multiplies on the left by the underlying matrix
of `h`. -/
theorem stdRep_apply_apply (H : Subgroup SU2) (h : H) (v : Fin 2 → ℂ) :
    stdRep H h v = (h.val : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdRep_apply, Matrix.mulVecLin_apply]

/-- `TauCeti.SU2.stdRep H` is faithful for every subgroup `H : Subgroup SU2`. -/
theorem stdRep_injective (H : Subgroup SU2) : Function.Injective (stdRep H) :=
  (TauCeti.stdRep_injective ℂ 2).comp (toGL_injective.comp H.subtype_injective)

-- Match before `stdRep_apply` unfolds `stdRep H h`.
/-- Every element of `H : Subgroup SU2` acts with determinant `1` under `TauCeti.SU2.stdRep H`. -/
@[simp↓]
theorem det_stdRep (H : Subgroup SU2) (h : H) : LinearMap.det (stdRep H h) = 1 := by
  rw [stdRep_apply, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  exact (Matrix.mem_specialUnitaryGroup_iff.mp h.val.property).right

/-- The character of `TauCeti.SU2.stdRep H` at `h : H` is the matrix trace of `h`. -/
@[simp]
theorem char_stdRep (H : Subgroup SU2) (h : H) :
    (stdRep H).character h = Matrix.trace (h.val : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, _root_.Representation.character, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← _root_.Representation.character, TauCeti.char_stdRep, coe_toGL]

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
  let ρSU2 : SU2 →* Module.End ℂ (Fin 2 → ℂ) := (TauCeti.stdRep ℂ 2).comp toGL
  LinearEquiv.ofLinearMap (ρSU2 g⁻¹) (ρSU2 g)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])

private theorem stdFDRepConjLinearEquiv_apply (g : SU2) (v : Fin 2 → ℂ) :
    stdFDRepConjLinearEquiv g v = ((TauCeti.stdRep ℂ 2).comp toGL) g⁻¹ v :=
  rfl

private theorem stdFDRepConjLinearEquiv_symm_apply (g : SU2) (v : Fin 2 → ℂ) :
    (stdFDRepConjLinearEquiv g).symm v = ((TauCeti.stdRep ℂ 2).comp toGL) g v :=
  rfl

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
    ← MonoidHom.comp_apply (TauCeti.stdRep ℂ 2) toGL,
    ← MonoidHom.comp_apply (TauCeti.stdRep ℂ 2) toGL,
    ← mul_apply_eq_comp, ← map_mul, ← mul_apply_eq_comp, ← map_mul,
    ← mul_assoc, inv_mul_cancel_left]

private noncomputable def stdFDRepConjEquiv {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) :
    ((Action.res (FGModuleCat ℂ)
        ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)) :
          H →* K)).obj
        (stdFDRep K)) ≃ₗ[ℂ]
      stdFDRep H :=
  stdFDRepConjLinearEquiv g

open CategoryTheory in
private theorem stdFDRepConjEquiv_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (stdFDRepConjEquiv hK ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v)) =
      stdFDRepConjLinearEquiv g v :=
  rfl

open CategoryTheory in
private theorem stdFDRepConjEquiv_symm_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))
        ((stdFDRepConjEquiv hK).symm
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))).symm v)) =
      (stdFDRepConjLinearEquiv g).symm v :=
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
  LinearEquiv.toFDRepIso (stdFDRepConjEquiv hK) fun h v ↦ by
    rw [LinearMap.congr_fun
      (FDRep.res_ρ ((((MulAut.conj g).subgroupMap H).trans (MulEquiv.subgroupCongr hK.symm)) :
        H →* K) (stdFDRep K) h) v]
    exact stdFDRepConjLinearEquiv_equivariant hK h v

open CategoryTheory in
/-- Evaluating `stdFDRepConjIso hK` on a vector multiplies on the left by `(g⁻¹ : Matrix ...)`. -/
theorem isoToLinearEquiv_stdFDRepConjIso_apply {H K : Subgroup SU2} {g : SU2}
    (hK : K = H.map (MulAut.conj g : SU2 →* SU2)) (v : Fin 2 → ℂ) :
    FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def H))
        (FDRep.isoToLinearEquiv (stdFDRepConjIso hK)
          ((FDRep.isoToLinearEquiv (eqToIso (stdFDRep_def K))).symm v)) =
      ((g⁻¹ : SU2) : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdFDRepConjIso, FDRep.isoToLinearEquiv_toFDRepIso, stdFDRepConjEquiv_apply,
    stdFDRepConjLinearEquiv_apply, MonoidHom.comp_apply, TauCeti.stdRep_apply_apply, coe_toGL]

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
    stdFDRepConjLinearEquiv_symm_apply, MonoidHom.comp_apply, TauCeti.stdRep_apply_apply, coe_toGL]

end TauCeti.SU2
