/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Graded quotients of a scalar-power filtration

Multiplication by `a^i` sends `aM` into `a^{i+1} M` and induces a surjection from `M / aM`
onto the ordinary graded piece `a^i M / a^{i+1} M`. The inclusion into `M / a^{i+1} M`
identifies this graded piece with the image of `QuotSMulTop.mulPow`. This multiplication map
and the projection to `M / a^i M` form an exact sequence, and multiplication is injective
when `a` is regular on `M`.
-/

public section

open Function
open scoped Pointwise

namespace QuotSMulTop

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (M) in
/-- Multiplication by `xᵏ`, as a map `M ⧸ x M → M ⧸ xᵏ⁺¹ M`. -/
noncomputable def mulPow (x : R) (k : ℕ) :
    QuotSMulTop x M →ₗ[R] QuotSMulTop (x ^ (k + 1)) M :=
  Submodule.mapQ _ _ (LinearMap.lsmul R M (x ^ k)) fun _ hm ↦ by
    obtain ⟨m, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    simpa [smul_smul, ← pow_succ'] using
      Submodule.smul_mem_pointwise_smul m (x ^ (k + 1)) (⊤ : Submodule R M) Submodule.mem_top

@[simp]
theorem mulPow_mk (x : R) (k : ℕ) (m : M) :
    mulPow M x k (Submodule.Quotient.mk m) = Submodule.Quotient.mk (x ^ k • m) :=
  (rfl)

/-- If `x` is regular on `M`, multiplication by `xᵏ` is injective from `M ⧸ x M` to
`M ⧸ xᵏ⁺¹ M`. -/
theorem mulPow_injective {x : R} (hx : IsSMulRegular M x) (k : ℕ) :
    Injective (mulPow M x k) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  induction y using Submodule.Quotient.induction_on with | H m => ?_
  rw [mulPow_mk, Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨m', -, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
  rw [pow_succ, mul_smul] at hm'
  rw [(hx.pow k).eq_iff.1 hm'.symm, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_pointwise_smul _ _ ⊤ Submodule.mem_top

/-- The sequence `M ⧸ x M → M ⧸ xᵏ⁺¹ M → M ⧸ xᵏ M`, whose first map is multiplication by `xᵏ`
and whose second map is the projection, is exact at `M ⧸ xᵏ⁺¹ M`. -/
theorem exact_mulPow (x : R) (k : ℕ) :
    Exact (mulPow M x k) (Submodule.factor
      (Submodule.smul_top_le_smul_top_of_dvd (M := M) (pow_dvd_pow x (k.le_add_right 1)))) := by
  intro y
  induction y using Submodule.Quotient.induction_on with | H m => ?_
  rw [← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  refine ⟨fun hm ↦ ?_, ?_⟩
  · obtain ⟨m', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
    exact ⟨Submodule.Quotient.mk m', mulPow_mk x k m'⟩
  · rintro ⟨y, hy⟩
    induction y using Submodule.Quotient.induction_on with | H m' => ?_
    rw [mulPow_mk, Submodule.mkQ_apply, Submodule.Quotient.eq] at hy
    have := sub_mem (Submodule.smul_mem_pointwise_smul m' (x ^ k) ⊤ Submodule.mem_top)
      (Submodule.smul_top_le_smul_top_of_dvd (pow_dvd_pow x (k.le_add_right 1)) hy)
    rwa [sub_sub_cancel] at this

end QuotSMulTop

namespace TauCeti

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

local notation "P" => (fun (a : A) (i : ℕ) ↦ a ^ i • (⊤ : Submodule A M))

private def gradedInclusion (a : A) (i : ℕ) :
    (P a i ⧸ (P a (i + 1)).comap (P a i).subtype) →ₗ[A] QuotSMulTop (a ^ (i + 1)) M :=
  ((P a (i + 1)).comap (P a i).subtype).mapQ (P a (i + 1)) (P a i).subtype le_rfl

private theorem gradedInclusion_injective (a : A) (i : ℕ) :
    Injective (gradedInclusion (M := M) a i) :=
  (Submodule.mapQ_injective_iff _ _ _ _).mpr le_rfl

private theorem mulPow_mem_range_gradedInclusion (a : A) (i : ℕ) (z : QuotSMulTop a M) :
    QuotSMulTop.mulPow M a i z ∈ (gradedInclusion a i).range := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  refine ⟨Submodule.Quotient.mk
    ⟨a ^ i • x, Submodule.smul_mem_pointwise_smul x _ _ Submodule.mem_top⟩, ?_⟩
  rw [gradedInclusion, Submodule.mapQ_apply, QuotSMulTop.mulPow_mk, Submodule.subtype_apply]

/-- Multiplication by `a^i` induces a map from `M / aM` to `a^i M / a^{i+1} M`. -/
noncomputable def smulPowQuotientMap (a : A) (i : ℕ) :
    M ⧸ (a • (⊤ : Submodule A M)) →ₗ[A] (P a i ⧸ (P a (i + 1)).comap (P a i).subtype) :=
  (QuotSMulTop.mulPow M a i).codLift (gradedInclusion a i) (gradedInclusion_injective a i)
    (mulPow_mem_range_gradedInclusion a i)

/-- On a quotient class, `smulPowQuotientMap` multiplies its representative by `a^i`. -/
@[simp]
theorem smulPowQuotientMap_mk (a : A) (i : ℕ) (x : M) :
    smulPowQuotientMap a i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨a ^ i • x, Submodule.smul_mem_pointwise_smul x _ _ Submodule.mem_top⟩ := by
  apply gradedInclusion_injective a i
  simp only [smulPowQuotientMap, ← LinearMap.comp_apply, LinearMap.comp_codLift,
    QuotSMulTop.mulPow_mk, gradedInclusion, Submodule.mapQ_apply, Submodule.subtype_apply]

/-- Every class in `a^i M / a^{i+1} M` comes from multiplication by `a^i` on `M / aM`. -/
theorem smulPowQuotientMap_surjective (a : A) (i : ℕ) :
    Function.Surjective (smulPowQuotientMap (M := M) a i) := by
  intro z
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  exact ⟨Submodule.Quotient.mk y, smulPowQuotientMap_mk a i y⟩

end TauCeti
