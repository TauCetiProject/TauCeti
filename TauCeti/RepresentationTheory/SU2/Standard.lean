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
-/

public section

open scoped Matrix

namespace TauCeti.SU2

/-- The tautological two-dimensional complex representation of `H : Subgroup SU2` on `Fin 2 → ℂ`. -/
def stdRep (H : Subgroup SU2) : Representation ℂ H (Fin 2 → ℂ) :=
  (TauCeti.stdRep ℂ 2).comp (toGL.comp H.subtype)

@[simp]
theorem stdRep_apply (H : Subgroup SU2) (h : H) :
    stdRep H h = Matrix.mulVecLin (h.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, MonoidHom.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    TauCeti.stdRep_apply, coe_toGL]

theorem stdRep_apply_apply (H : Subgroup SU2) (h : H) (v : Fin 2 → ℂ) :
    stdRep H h v = (h.1 : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v := by
  rw [stdRep_apply, Matrix.mulVecLin_apply]

theorem stdRep_injective (H : Subgroup SU2) : Function.Injective (stdRep H) :=
  (TauCeti.stdRep_injective ℂ 2).comp (toGL_injective.comp H.subtype_injective)

theorem det_stdRep (H : Subgroup SU2) (h : H) : LinearMap.det (stdRep H h) = 1 := by
  rw [stdRep_apply, ← Matrix.toLin'_apply', LinearMap.det_toLin']
  exact (Matrix.mem_specialUnitaryGroup_iff.mp h.1.2).2

@[simp]
theorem char_stdRep (H : Subgroup SU2) (h : H) :
    (stdRep H).character h = Matrix.trace (h.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [stdRep, _root_.Representation.character, MonoidHom.comp_apply, MonoidHom.comp_apply,
    Subgroup.coe_subtype, ← _root_.Representation.character, TauCeti.char_stdRep, coe_toGL]

/-- The tautological two-dimensional complex representation of `H : Subgroup SU2` in `FDRep ℂ H`. -/
noncomputable abbrev stdFDRep (H : Subgroup SU2) : FDRep ℂ H := FDRep.of (stdRep H)

theorem finrank_stdFDRep (H : Subgroup SU2) : Module.finrank ℂ (stdFDRep H) = 2 := by
  rw [FDRep.finrank_of (stdRep H)]; simp

theorem ρ_stdFDRep_injective (H : Subgroup SU2) : Function.Injective (stdFDRep H).ρ := by
  rw [FDRep.of_ρ' (stdRep H)]; exact stdRep_injective H

theorem det_ρ_stdFDRep (H : Subgroup SU2) (h : H) : LinearMap.det ((stdFDRep H).ρ h) = 1 := by
  rw [FDRep.of_ρ' (stdRep H)]; exact det_stdRep H h

theorem character_stdFDRep (H : Subgroup SU2) (h : H) :
    (stdFDRep H).character h = Matrix.trace (h.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [FDRep.character_of (stdRep H), char_stdRep]

end TauCeti.SU2
