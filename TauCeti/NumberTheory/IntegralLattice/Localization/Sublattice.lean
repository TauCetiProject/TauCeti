/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Localizing a sublattice of index prime to `p`

Let `L ≤ M` be integral lattices on the same rational quadratic space. If the index `[M : L]` is
not divisible by the prime `p`, then the inclusion becomes an isometry of the integral
localizations `ℤ_p ⊗[ℤ] L ≃ ℤ_p ⊗[ℤ] M`. Indeed multiplication by the index maps `M` into `L`,
and after base change to `ℤ_p` the index is a unit, which inverts the inclusion.

This is the local input for comparing the genera of lattices that agree up to index prime to
`p`, for instance Kneser neighbors.

## Main results

* `TauCeti.IntegralLattice.localInclusionIsometryEquiv`: the localized inclusion of a sublattice
  of index prime to `p`, as an isometry of the integral local forms.
* `TauCeti.IntegralLattice.localIntegralForm_equivalent_of_le`: such a sublattice has an
  integrally isometric localization at `p`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §82.
-/

public section

open Module TensorProduct

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (L M : IntegralLattice V) (p : ℕ) [Fact p.Prime]

/-- Multiplication by the index `[M : L]`, as a map from the carrier of `M` to that of `L`. -/
private noncomputable def relIndexSMul : M →ₗ[ℤ] L :=
  ((L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup : ℤ) •
    M.carrier.subtype).codRestrict L.carrier fun x ↦ by
      simpa only [LinearMap.smul_apply, Submodule.subtype_apply, natCast_zsmul,
        Submodule.mem_toAddSubgroup] using
        L.carrier.toAddSubgroup.nsmul_relIndex_mem x.property

private theorem inclusion_comp_relIndexSMul (hle : L.carrier ≤ M.carrier) :
    Submodule.inclusion hle ∘ₗ relIndexSMul L M =
      (L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup : ℤ) • LinearMap.id := by
  ext x
  simp [relIndexSMul]

private theorem relIndexSMul_comp_inclusion (hle : L.carrier ≤ M.carrier) :
    relIndexSMul L M ∘ₗ Submodule.inclusion hle =
      (L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup : ℤ) • LinearMap.id := by
  ext x
  simp [relIndexSMul]

/-- **The localized inclusion of a sublattice of index prime to `p` is an isometry.** If two
integral lattices share their ambient form, the carrier of `L` lies in that of `M`, and `p`
does not divide the index `[M : L]`, then the base change to `ℤ_p` of the inclusion is an
isometry of the integral local forms. -/
noncomputable def localInclusionIsometryEquiv (hform : L.form = M.form)
    (hle : L.carrier ≤ M.carrier)
    (hp : ¬p ∣ L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup) :
    (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p) :=
  let u : ℤ_[p]ˣ := (PadicInt.isUnit_natCast_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hp)).unit
  let i := (Submodule.inclusion hle).baseChange ℤ_[p]
  let j := (relIndexSMul L M).baseChange ℤ_[p]
  have hij : i ∘ₗ j = (u : ℤ_[p]) • LinearMap.id := by
    simp only [i, j, ← LinearMap.baseChange_comp, inclusion_comp_relIndexSMul,
      LinearMap.baseChange_smul, LinearMap.baseChange_id, u, IsUnit.unit_spec]
    exact LinearMap.ext fun x ↦ by simp [Nat.cast_smul_eq_nsmul]
  have hji : j ∘ₗ i = (u : ℤ_[p]) • LinearMap.id := by
    simp only [i, j, ← LinearMap.baseChange_comp, relIndexSMul_comp_inclusion,
      LinearMap.baseChange_smul, LinearMap.baseChange_id, u, IsUnit.unit_spec]
    exact LinearMap.ext fun x ↦ by simp [Nat.cast_smul_eq_nsmul]
  { toLinearEquiv := LinearEquiv.ofLinearMap i ((↑u⁻¹ : ℤ_[p]) • j)
      (by rw [LinearMap.comp_smul, hij, smul_smul, Units.inv_mul, one_smul])
      (by rw [LinearMap.smul_comp, hji, smul_smul, Units.inv_mul, one_smul])
    map_app' := fun x y ↦ by
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        LinearEquiv.coe_ofLinearMap]
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]
      | tmul a x =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
        | tmul b y =>
          simp only [i, LinearMap.baseChange_tmul,
            localIntegralForm_tmul, L.integralForm_inclusion M hform hle] }

/-- The localized inclusion on pure tensors. -/
@[simp]
theorem localInclusionIsometryEquiv_tmul (hform : L.form = M.form)
    (hle : L.carrier ≤ M.carrier)
    (hp : ¬p ∣ L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup) (a : ℤ_[p]) (x : L) :
    L.localInclusionIsometryEquiv M p hform hle hp (a ⊗ₜ x) = a ⊗ₜ Submodule.inclusion hle x :=
  (rfl)

/-- **A sublattice of index prime to `p` has an isometric localization at `p`.** -/
theorem localIntegralForm_equivalent_of_le (hform : L.form = M.form)
    (hle : L.carrier ≤ M.carrier)
    (hp : ¬p ∣ L.carrier.toAddSubgroup.relIndex M.carrier.toAddSubgroup) :
    (L.localIntegralForm p).Equivalent (M.localIntegralForm p) :=
  ⟨L.localInclusionIsometryEquiv M p hform hle hp⟩

end TauCeti.IntegralLattice
