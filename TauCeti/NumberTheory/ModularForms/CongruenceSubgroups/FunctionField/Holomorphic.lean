/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.FunctionField.CoeffAction
import TauCeti.Analysis.Complex.Fuchsian.Compactification.FiniteHolomorphicMap
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Integral

/-!
# Coefficient conjugation preserves holomorphic modular functions

A meromorphic function on `X(N)` has no poles on the open modular curve exactly when it is
integral over `ℂ[j]`. Since coefficient conjugation is semilinear on constants and fixes `j`,
it preserves this integral closure. Consequently the conjugate Laurent expansion of a modular
function holomorphic on the upper half-plane again represents such a function.

This supplies the holomorphy input for constructing coefficient conjugates of positive-weight
modular forms by division by powers of the discriminant.

## References

* Goro Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*,
  §§6.1–6.2, for coefficient conjugation on modular functions.
-/

public noncomputable section

open CongruenceSubgroup Subgroup.CompactifiedQuotient TauCeti.RiemannSurface UpperHalfPlane
open MeromorphicFunction OnePoint
open scoped MatrixGroups

namespace TauCeti

variable {N : ℕ} [NeZero N]

/-- For a finite-index subgroup `H` of `SL(2, ℤ)`, a meromorphic function on `X_H` is integral
over `ℂ[j]` exactly when it has no poles on the upper half-plane. Poles at the cusps are
allowed. -/
theorem _root_.Subgroup.isIntegral_adjoin_jMeromorphicFunction_iff (H : Subgroup SL(2, ℤ))
    [H.FiniteIndex] (F : MeromorphicFunction (H.map sl2zToPSL2R).CompactifiedQuotient) :
    IsIntegral (Algebra.adjoin ℂ
      {Subgroup.compactifiedQuotientComap H.map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction}) F ↔
      ∀ τ : ℍ, F (ofQuotient (Quotient.mk _ τ)) ≠ ∞ := by
  let := (Subgroup.isCofinite_map_sl2zToPSL2R H).compactSpace_compactifiedQuotient
  let β := ModularGroup.jFiniteHolomorphicMap.comp
    (Fuchsian.compactifiedQuotientFiniteHolomorphicMap H.map_sl2zToPSL2R_le_range_psl2zToPSL2R)
  have hj : comapₐ β β.holomorphic β.nonconstant coordinate =
      Subgroup.compactifiedQuotientComap H.map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction := by
    ext x
    simp [β, ModularGroup.coe_jMeromorphicFunction]
  rw [← hj, isIntegral_adjoin_comap_coordinate_iff]
  constructor
  · intro h τ
    apply h _
    simp [β]
  · intro h x hx
    cases x with
    | ofQuotient p =>
      induction p using Quotient.inductionOn with
      | h τ => exact h τ
    | ofCusp C => exact (hx (by simp [β])).elim

/-- Coefficient conjugation preserves the modular functions of level `N` integral over `ℂ[j]`. -/
private theorem isIntegral_adjoin_jMeromorphicFunction_coeffAction
    (σ : ℂ ≃+* ℂ)
    {F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient}
    (hF : IsIntegral (Algebra.adjoin ℂ
      {Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction}) F) :
    IsIntegral (Algebra.adjoin ℂ
      {Subgroup.compactifiedQuotientComap (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R
        ModularGroup.jMeromorphicFunction}) (modularFunctionCoeffAction N σ F) := by
  let J := Subgroup.compactifiedQuotientComap
    (Gamma N).map_sl2zToPSL2R_le_range_psl2zToPSL2R ModularGroup.jMeromorphicFunction
  let A := Algebra.adjoin ℂ ({J} : Set _)
  let ψ := (modularFunctionCoeffAction N σ).toRingHom
  have hA : ∀ a ∈ A, ψ a ∈ A := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      rw [Set.mem_singleton_iff.mp ha]
      have hJ : ψ J = J :=
        modularFunctionCoeffAction_compactifiedQuotientComap_jMeromorphicFunction (N := N) σ
      rw [hJ]
      exact Algebra.subset_adjoin (Set.mem_singleton J)
    | algebraMap c =>
      simpa only [ψ, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        modularFunctionCoeffAction_algebraMap] using
        A.algebraMap_mem (σ c)
    | add a b _ _ ha hb => exact (map_add ψ a b) ▸ A.add_mem ha hb
    | mul a b _ _ ha hb => exact (map_mul ψ a b) ▸ A.mul_mem ha hb
  let φ : A →+* A := (ψ.comp A.val.toRingHom).codRestrict A.toSubring
    (fun a ↦ hA a a.property)
  exact hF.map_of_comp_eq φ ψ (by ext a; rfl)

/-- Applying an arbitrary automorphism of `ℂ` to the Fourier coefficients preserves
holomorphy on the upper half-plane for meromorphic modular functions. -/
@[simp]
theorem forall_ne_infty_modularFunctionCoeffAction_iff (σ : ℂ ≃+* ℂ)
    (F : MeromorphicFunction ((Gamma N).map sl2zToPSL2R).CompactifiedQuotient) :
    (∀ τ : ℍ, modularFunctionCoeffAction N σ F (ofQuotient (Quotient.mk _ τ)) ≠ ∞) ↔
      ∀ τ : ℍ, F (ofQuotient (Quotient.mk _ τ)) ≠ ∞ := by
  rw [← (Gamma N).isIntegral_adjoin_jMeromorphicFunction_iff,
    ← (Gamma N).isIntegral_adjoin_jMeromorphicFunction_iff]
  refine ⟨fun h ↦ ?_, isIntegral_adjoin_jMeromorphicFunction_coeffAction σ⟩
  have h := isIntegral_adjoin_jMeromorphicFunction_coeffAction σ.symm h
  rwa [modularFunctionCoeffAction_symm_apply_apply] at h

end TauCeti
