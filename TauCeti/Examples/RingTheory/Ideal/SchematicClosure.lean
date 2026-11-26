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
uniformizer of a discrete valuation ring). Two Checks of `ReductiveGroupsPartII` RG2.3.1
*schematic-closure*:

* *closure_nonIntegralPoint*: for `A = O[x]` and the ideal `I = (x - ϖ⁻¹)` of the generic fibre
  `K[x] = K ⊗[O] O[x]`, the closure ideal is `I^♮ = (ϖx - 1)`
  (`TauCeti.Examples.closureIdeal_span_X_sub_inv`). The closure `O[x] ⧸ (ϖx - 1)` has no section
  (`TauCeti.Examples.isEmpty_algHom_closure_span_X_sub_inv`) and, over a local ring, an empty
  special fibre (`TauCeti.Examples.subsingleton_residueField_tensor_closure_span_X_sub_inv`):
  the `K`-point `x = ϖ⁻¹` does not extend to an `O`-point.
* *closureIdeal_bot_eq_torsion*: without flatness the closure of the zero ideal is the `O`-torsion
  ideal, which for `A = O × O ⧸ (ϖ)` is `0 × O ⧸ (ϖ)`, not `0`
  (`TauCeti.Examples.mem_closureIdeal_bot_prod_iff`).
-/

public section

namespace TauCeti.Examples

open Polynomial TensorProduct Algebra.TensorProduct SchematicClosure

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {ϖ : O}

/-- In `K ⊗[O] O[x]`, the element `1 ⊗ (ϖx - 1)` is the unit `ϖ ⊗ 1` times `1 ⊗ x - ϖ⁻¹ ⊗ 1`. -/
private theorem includeRight_C_mul_X_sub_one (hϖ0 : ϖ ≠ 0) :
    (includeRight : O[X] →ₐ[O] K ⊗[O] O[X]) (C ϖ * X - 1) =
      (algebraMap O K ϖ ⊗ₜ[O] (1 : O[X])) *
        ((1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])) := by
  have hne : algebraMap O K ϖ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ0)
  rw [mul_sub, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, mul_inv_cancel₀ hne, map_sub, map_one, includeRight_apply,
    ← smul_eq_C_mul, mul_one, ← Algebra.TensorProduct.one_def]
  congr 1
  rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

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
  have hne : algebraMap O K ϖ ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hϖ0)
  have hu : IsUnit (algebraMap O K ϖ ⊗ₜ[O] (1 : O[X])) :=
    (isUnit_iff_ne_zero.mpr hne).map (algebraMap K (K ⊗[O] O[X]))
  rw [Ideal.map_span, Set.image_singleton, includeRight_C_mul_X_sub_one hϖ0]
  exact Ideal.span_singleton_mul_left_unit hu _

/-- `ϖx - 1` vanishes in the closure of `x = ϖ⁻¹`. -/
private theorem mk_C_mul_X_sub_one_eq_zero (hϖ0 : ϖ ≠ 0) :
    Ideal.Quotient.mk (closureIdeal K (Ideal.span
        {(1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])}))
      (C ϖ * X - 1) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, closureIdeal_span_X_sub_inv hϖ0]
  exact Ideal.subset_span rfl

/-- **The closure of `x = ϖ⁻¹` has no section**: an `O`-point of `O[x] ⧸ (ϖx - 1)` would make
`ϖ` a unit. -/
theorem isEmpty_algHom_closure_span_X_sub_inv (hϖ0 : ϖ ≠ 0) (hϖ : ¬IsUnit ϖ) :
    IsEmpty (closure K (Ideal.span
        {(1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])}) →ₐ[O] O) := by
  refine ⟨fun f ↦ hϖ (IsUnit.of_mul_eq_one (f (Ideal.Quotient.mk _ X)) ?_)⟩
  have h := congrArg f (mk_C_mul_X_sub_one_eq_zero (K := K) hϖ0)
  rw [← Polynomial.algebraMap_eq] at h
  simp only [map_sub, map_mul, map_one, map_zero, Ideal.Quotient.mk_algebraMap, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply] at h
  exact sub_eq_zero.mp h

/-- **The closure of `x = ϖ⁻¹` has empty special fibre**: over a local ring `O` with `ϖ` in the
maximal ideal, `κ ⊗[O] O[x] ⧸ (ϖx - 1)` is the zero ring. -/
theorem subsingleton_residueField_tensor_closure_span_X_sub_inv [IsLocalRing O] (hϖ0 : ϖ ≠ 0)
    (hϖ : ¬IsUnit ϖ) :
    Subsingleton (IsLocalRing.ResidueField O ⊗[O] closure K (Ideal.span
        {(1 : K) ⊗ₜ[O] (X : O[X]) - (algebraMap O K ϖ)⁻¹ ⊗ₜ[O] (1 : O[X])})) := by
  refine subsingleton_of_zero_eq_one ?_
  have h := mk_C_mul_X_sub_one_eq_zero (K := K) hϖ0
  rw [map_sub, map_one, sub_eq_zero, map_mul, ← Polynomial.algebraMap_eq,
    Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def] at h
  rw [Algebra.TensorProduct.one_def, ← h, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_one, IsLocalRing.ResidueField.algebraMap_eq,
    (IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖ, TensorProduct.zero_tmul]

/-- **The closure of the zero ideal is the torsion, not `0`, without flatness.** For
`A = O × O ⧸ (ϖ)`, which is not torsion-free, `(a, b) ∈ (0)^♮` exactly when `a = 0`: the closure
of the zero ideal of the generic fibre is `0 × O ⧸ (ϖ)`. -/
theorem mem_closureIdeal_bot_prod_iff (hϖ0 : ϖ ≠ 0) (a : O) (b : O ⧸ Ideal.span {ϖ}) :
    (a, b) ∈ closureIdeal K (⊥ : Ideal (K ⊗[O] (O × O ⧸ Ideal.span {ϖ}))) ↔ a = 0 := by
  rw [closureIdeal_bot_eq_scalarTorsionIdeal, mem_scalarTorsionIdeal]
  constructor
  · rintro ⟨s, h⟩
    have h1 := congrArg Prod.fst h
    simp only [Prod.smul_fst, Prod.fst_zero, Submonoid.smul_def, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero s)
  · rintro rfl
    refine ⟨⟨ϖ, mem_nonZeroDivisors_of_ne_zero hϖ0⟩, Prod.ext (smul_zero _) ?_⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    change ϖ • Ideal.Quotient.mk (Ideal.span {ϖ}) b = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

end TauCeti.Examples
