/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Ideal.SchematicClosure
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-!
# Checks for the schematic closure

Let `O` be a domain with fraction field `K` and `ϖ ∈ O` a nonzero nonunit (for instance a
uniformizer of a discrete valuation ring). Two examples of the schematic closure:

* a non-integral point: for `A = O[x]` and the ideal `I = (x - ϖ⁻¹)` of the generic fibre
  `K[x] = K ⊗[O] O[x]`, the closure ideal is `I^♮ = (ϖx - 1)`
  (`TauCeti.Examples.closureIdeal_span_X_sub_inv`). The closure `O[x] ⧸ (ϖx - 1)` has no section
  (`TauCeti.Examples.isEmpty_algHom_closure_span_X_sub_inv`) and, over a local ring, an empty
  special fibre (`TauCeti.Examples.subsingleton_residueField_tensorProduct_closure_span_X_sub_inv`):
  the `K`-point `x = ϖ⁻¹` does not extend to an `O`-point.
* the failure of `(0)^♮ = 0` without flatness: the closure of the zero ideal is the `O`-torsion
  ideal, which for `A = O × O ⧸ (ϖ)` is `0 × O ⧸ (ϖ)`, not `0` when `ϖ` is a nonunit
  (`TauCeti.Examples.mem_closureIdeal_bot_prod_iff`).
-/

public section

namespace TauCeti.Examples

open Polynomial TensorProduct Algebra.TensorProduct SchematicClosure

variable {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  {ϖ : O}

/-- In `K ⊗[O] O[x]`, the element `1 ⊗ (ϖx - 1)` is the unit `ϖ ⊗ 1` times `1 ⊗ x - ϖ⁻¹ ⊗ 1`. -/
private theorem includeRight_C_mul_X_sub_one (hϖ0 : ϖ ≠ 0) :
    (includeRight : O[X] →ₐ[O] K ⊗[O] O[X]) (C ϖ * X - 1) =
      (algebraMap O K ϖ ⊗ₜ[O] (1 : O[X])) *
        ((1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])) := by
  rw [mul_sub, tmul_mul_tmul, tmul_mul_tmul,
    mul_inv_cancel₀ (IsFractionRing.to_map_eq_zero_iff.not.mpr hϖ0)]
  simp only [mul_one, one_mul, map_sub, map_one, includeRight_apply, ← smul_eq_C_mul,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, Algebra.TensorProduct.one_def]

/-- **The closure of the non-integral point `x = ϖ⁻¹`.** For `A = O[x]` and the ideal
`I = (x - ϖ⁻¹)` of `K[x] = K ⊗[O] O[x]`, the closure ideal is `I^♮ = (ϖx - 1)`: the quotient
`O[x] ⧸ (ϖx - 1)` is the localization `O[1/ϖ]`, torsion-free over `O`, and `ϖx - 1` generates `I`
in the generic fibre. -/
theorem closureIdeal_span_X_sub_inv (hϖ0 : ϖ ≠ 0) :
    closureIdeal K (Ideal.span
        {(1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])}) =
      Ideal.span {C ϖ * X - 1} := by
  have : IsLocalization.Away ϖ (O[X] ⧸ Ideal.span {C ϖ * X - 1}) := IsLocalization.adjoin_inv ϖ
  have : Module.Flat O (O[X] ⧸ Ideal.span {C ϖ * X - 1}) :=
    IsLocalization.flat _ (Submonoid.powers ϖ)
  refine (closure_unique ?_).symm
  have hu : IsUnit (algebraMap O K ϖ ⊗ₜ[O] (1 : O[X])) :=
    (isUnit_iff_ne_zero.mpr (IsFractionRing.to_map_eq_zero_iff.not.mpr hϖ0)).map
      (algebraMap K (K ⊗[O] O[X]))
  rw [Ideal.map_span, Set.image_singleton, includeRight_C_mul_X_sub_one hϖ0]
  exact Ideal.span_singleton_mul_left_unit hu _

/-- `ϖ` is invertible in the closure of `x = ϖ⁻¹`, with inverse the class of `x`. -/
private theorem algebraMap_mul_mk_X_eq_one (hϖ0 : ϖ ≠ 0) :
    algebraMap O (closure K (Ideal.span
        {(1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])})) ϖ *
      Ideal.Quotient.mk _ X = 1 := by
  -- `ϖx - 1` lies in the closure ideal, so its class vanishes.
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((closureIdeal_span_X_sub_inv (K := K) hϖ0).ge (Ideal.mem_span_singleton_self (C ϖ * X - 1)))
  rwa [map_sub, map_mul, map_one, sub_eq_zero, Polynomial.C_eq_algebraMap,
    Ideal.Quotient.mk_algebraMap] at h

/-- **The closure of `x = ϖ⁻¹` has no section**: an `O`-point of `O[x] ⧸ (ϖx - 1)` would make
`ϖ` a unit. -/
theorem isEmpty_algHom_closure_span_X_sub_inv (hϖ0 : ϖ ≠ 0) (hϖ : ¬IsUnit ϖ) :
    IsEmpty (closure K (Ideal.span
        {(1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])}) →ₐ[O] O) := by
  refine ⟨fun f ↦ hϖ (IsUnit.of_mul_eq_one (f (Ideal.Quotient.mk _ X)) ?_)⟩
  simpa only [map_mul, map_one, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
    using congrArg f (algebraMap_mul_mk_X_eq_one (K := K) hϖ0)

/-- **The closure of `x = ϖ⁻¹` has empty special fibre**: over a local ring `O` with `ϖ` in the
maximal ideal, `κ ⊗[O] O[x] ⧸ (ϖx - 1)` is the zero ring. -/
theorem subsingleton_residueField_tensorProduct_closure_span_X_sub_inv [IsLocalRing O] (hϖ0 : ϖ ≠ 0)
    (hϖ : ¬IsUnit ϖ) :
    Subsingleton (IsLocalRing.ResidueField O ⊗[O] closure K (Ideal.span
        {(1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])})) := by
  refine subsingleton_of_zero_eq_one ?_
  -- `ϖ` acts invertibly on the closure but as zero on the residue field.
  rw [Algebra.TensorProduct.one_def, ← algebraMap_mul_mk_X_eq_one (K := K) hϖ0,
    ← Algebra.smul_def, ← TensorProduct.smul_tmul]
  simp [Algebra.smul_def, (IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖ]

/-- **The closure of the zero ideal is the torsion, without flatness.** For `A = O × O ⧸ (ϖ)`,
`(a, b) ∈ (0)^♮` exactly when `a = 0`: the closure of the zero ideal of the generic fibre is
`0 × O ⧸ (ϖ)`. When `ϖ` is a nonunit, `A` is not torsion-free and this closure is not `0`. -/
theorem mem_closureIdeal_bot_prod_iff (hϖ0 : ϖ ≠ 0) (a : O) (b : O ⧸ Ideal.span {ϖ}) :
    (a, b) ∈ closureIdeal K (⊥ : Ideal (K ⊗[O] (O × O ⧸ Ideal.span {ϖ}))) ↔ a = 0 := by
  have : IsDomain O := (IsFractionRing.isDomain_iff_isField (K := K)).mpr (Field.toIsField K)
  rw [closureIdeal_bot_eq_scalarTorsionIdeal, mem_scalarTorsionIdeal]
  constructor
  · rintro ⟨s, h⟩
    have h1 := congrArg Prod.fst h
    simp only [Prod.smul_fst, Prod.fst_zero, Submonoid.smul_def, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero s)
  · rintro rfl
    refine ⟨⟨ϖ, mem_nonZeroDivisors_of_ne_zero hϖ0⟩, Prod.ext (smul_zero _) ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ))

end TauCeti.Examples
