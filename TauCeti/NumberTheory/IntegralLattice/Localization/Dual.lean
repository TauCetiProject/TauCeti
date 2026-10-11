/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Localization commutes with integral lattice duality

The dual of a nondegenerate integral lattice need not have an integral form, so its localization
is formed from its carrier rather than by treating it as another integral lattice. The canonical map
from
`ℤ_p ⊗[ℤ] L.dualCarrier` to the completed rational space has image exactly the dual of the
localized carrier with respect to the completed rational form. This identifies the embedded local
dual, including at the prime `2`, with both carriers in the same completed ambient space and
with the same pairing.

The perfect integral pairing `TauCeti.IntegralLattice.dualPairingEquiv` is scalar-extended using
`TauCeti.Module.Dual.baseChangeEvaluationEquiv`. The localized dual carrier therefore represents
every `ℤ_p`-linear functional on the localized carrier.

## Main results

* `TauCeti.IntegralLattice.isBaseChange_localizationDualToCompletion`: the completed ambient
  space is the scalar extension of the localized dual carrier.
* `TauCeti.IntegralLattice.localDualPairingEquiv`: the perfect pairing after localization.
* `TauCeti.IntegralLattice.completedRationalForm_localizationDualToCompletion`: compatibility
  with the completed rational form.
* `TauCeti.IntegralLattice.range_localizationDualToCompletion`: equality of the localized dual
  and the dual of the localized carrier.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Chapter VIII.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

open Module TensorProduct

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (p : ℕ) [Fact p.Prime]

/-- The scalar extension to `ℤ_p` of the dual carrier of an integral lattice. -/
abbrev LocalDualCarrier := ℤ_[p] ⊗[ℤ] L.dualCarrier

/-- The canonical embedding map from the localized dual carrier into the completed ambient
rational space, sending `a ⊗ x` to `a ⊗ x`. -/
noncomputable def localizationDualToCompletion :
    L.LocalDualCarrier p →ₗ[ℤ_[p]] ℚ_[p] ⊗[ℚ] V :=
  (((TensorProduct.mk ℚ ℚ_[p] V 1).restrictScalars ℤ).comp
    L.dualCarrier.subtype).liftBaseChange ℤ_[p]

/-- The localized dual-carrier map on pure tensors. -/
@[simp]
theorem localizationDualToCompletion_tmul (a : ℤ_[p]) (x : L.dualCarrier) :
    L.localizationDualToCompletion p (a ⊗ₜ x) = (a : ℚ_[p]) ⊗ₜ (x : V) := by
  rw [localizationDualToCompletion, LinearMap.liftBaseChange_tmul]
  simp [TensorProduct.smul_tmul', Algebra.smul_def]

/-- Extending the localized dual carrier from `ℤ_p` to `ℚ_p` recovers the completed ambient
space. This requires no nondegeneracy: the dual carrier contains the original full carrier. -/
theorem isBaseChange_localizationDualToCompletion :
    IsBaseChange ℚ_[p] (L.localizationDualToCompletion p) := by
  have hL : IsLocalizedModule (nonZeroDivisors ℤ) L.carrier.subtype :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ _).mpr
      (Submodule.IsLattice.isBaseChange_subtype L.carrier)
  let : IsLocalizedModule (nonZeroDivisors ℤ) L.dualCarrier.subtype :=
    { map_units := hL.map_units
      surj := fun v ↦ by
        obtain ⟨⟨x, s⟩, hs⟩ := hL.surj v
        exact ⟨(⟨x, L.le_dualCarrier x.property⟩, s), hs⟩
      exists_of_eq := fun h ↦ ⟨1, by simpa using L.dualCarrier.subtype_injective h⟩ }
  refine (TensorProduct.isBaseChange ℤ L.dualCarrier ℤ_[p]).of_comp ?_
  convert (IsLocalizedModule.isBaseChange (nonZeroDivisors ℤ) ℚ L.dualCarrier.subtype).comp
    (TensorProduct.isBaseChange ℚ V ℚ_[p])
  ext x
  simp

/-- The localization of the dual carrier embeds injectively in the completed rational space. -/
theorem localizationDualToCompletion_injective :
    Function.Injective (L.localizationDualToCompletion p) := by
  let : IsAddTorsionFree V := .of_module_rat V
  exact (L.isBaseChange_localizationDualToCompletion p).injective_of_tensorProduct_mk_injective
    (Module.Flat.tensorProduct_mk_injective ℤ_[p] (L.LocalDualCarrier p) ℚ_[p])

variable [L.IsNondegenerate]

/-- The perfect pairing between the localized dual carrier and the localized carrier. -/
noncomputable def localDualPairingEquiv :
    L.LocalDualCarrier p ≃ₗ[ℤ_[p]] Module.Dual ℤ_[p] (L.LocalCarrier p) :=
  (LinearEquiv.baseChange ℤ ℤ_[p] _ _ L.dualPairingEquiv).trans
    (TauCeti.Module.Dual.baseChangeEvaluationEquiv (R := ℤ) (A := ℤ_[p]) (M := L))

/-- The localized perfect pairing on pure tensors. -/
@[simp]
theorem localDualPairingEquiv_tmul (a b : ℤ_[p]) (x : L.dualCarrier) (y : L) :
    L.localDualPairingEquiv p (a ⊗ₜ x) (b ⊗ₜ y) =
      a * b * (L.dualPairing x y : ℤ_[p]) := by
  rw [localDualPairingEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    TauCeti.Module.Dual.baseChangeEvaluationEquiv_apply,
    TauCeti.Module.Dual.baseChangeEvaluation_tmul]
  rw [← LinearEquiv.coe_toLinearMap, L.dualPairingEquiv_toLinearMap]
  simp only [algebraMap_int_eq, Int.coe_castRingHom]

/-- The completed rational pairing restricts to the localized perfect integral pairing between
localizations of the dual carrier and the original carrier. -/
@[simp]
theorem completedRationalForm_localizationDualToCompletion
    (x : L.LocalDualCarrier p) (y : L.LocalCarrier p) :
    L.completedRationalForm p (L.localizationDualToCompletion p x)
        (L.localizationToCompletion p y) =
      algebraMap ℤ_[p] ℚ_[p] (L.localDualPairingEquiv p x y) := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul b y =>
      rw [localizationDualToCompletion_tmul, localizationToCompletion_tmul,
        completedRationalForm_tmul, localDualPairingEquiv_tmul, ← L.dualPairing_cast x y,
        Rat.cast_intCast, PadicInt.algebraMap_apply]
      push_cast
      ring

/-- Localization commutes with duality as embedded carriers in the completed rational space.
This equality uses the completed rational form on both sides and holds at every prime. -/
@[simp]
theorem range_localizationDualToCompletion :
    LinearMap.range (L.localizationDualToCompletion p) =
      (L.completedRationalForm p).dualSubmodule
        (LinearMap.range (L.localizationToCompletion p)) := by
  apply le_antisymm
  · rintro v ⟨x, rfl⟩
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    rintro w ⟨y, rfl⟩
    rw [completedRationalForm_localizationDualToCompletion]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩
  · intro v hv
    let f : Module.Dual ℤ_[p] (L.LocalCarrier p) :=
      ((L.completedRationalForm p).dualSubmoduleToDual
        (LinearMap.range (L.localizationToCompletion p)) ⟨v, hv⟩).comp
          (L.localizationToCompletion p).rangeRestrict
    obtain ⟨x, hx⟩ := (L.localDualPairingEquiv p).surjective f
    refine ⟨x, ?_⟩
    have hpair (y : L.LocalCarrier p) :
        L.completedRationalForm p (L.localizationDualToCompletion p x)
            (L.localizationToCompletion p y) =
          L.completedRationalForm p v (L.localizationToCompletion p y) := by
      rw [completedRationalForm_localizationDualToCompletion, hx]
      exact (L.completedRationalForm p).dualSubmodulePairing_spec
        ⟨v, hv⟩ ((L.localizationToCompletion p).rangeRestrict y)
    apply LinearMap.ker_eq_bot.mp
      ((L.nondegenerate_completedRationalForm_iff p).mpr L.form_nondegenerate).ker_eq_bot
    apply LinearMap.ext_on (L.span_range_localizationToCompletion p)
    rintro w ⟨y, rfl⟩
    exact hpair y

end TauCeti.IntegralLattice
