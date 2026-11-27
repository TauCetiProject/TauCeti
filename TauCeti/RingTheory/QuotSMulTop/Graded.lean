/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.LinearAlgebra.Quotient.Basic

/-!
# Graded quotients of a scalar-power filtration

Multiplication by `a^i` sends `aM` into `a^{i+1} M` and induces a surjection from `M / aM`
onto the ordinary graded piece `a^i M / a^{i+1} M`.
-/

public section

namespace TauCeti

open scoped Pointwise

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

local notation "P" => (fun (a : A) (i : ℕ) ↦ a ^ i • (⊤ : Submodule A M))

private theorem range_smulPow (a : A) (i : ℕ) :
    (DistribSMul.toLinearMap A M (a ^ i)).range = a ^ i • (⊤ : Submodule A M) := by
  rw [Submodule.pointwise_smul_def, Submodule.map_top]

private def smulPowToSubmodule (a : A) (i : ℕ) : M →ₗ[A] P a i :=
  let f := DistribSMul.toLinearMap A M (a ^ i)
  (LinearEquiv.ofEq f.range (P a i) (range_smulPow a i)).toLinearMap ∘ₗ f.rangeRestrict

private theorem smulPowToSubmodule_apply (a : A) (i : ℕ) (x : M) :
    smulPowToSubmodule a i x =
      ⟨a ^ i • x, Submodule.smul_mem_pointwise_smul x _ _ Submodule.mem_top⟩ := by
  apply Subtype.ext
  simp only [smulPowToSubmodule, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_ofEq_apply, LinearMap.rangeRestrict, LinearMap.codRestrict_apply,
    DistribSMul.toLinearMap_apply]

private theorem le_comap_smulPowToSubmodule (a : A) (i : ℕ) :
    a • (⊤ : Submodule A M) ≤ ((P a (i + 1)).comap (P a i).subtype).comap
      (smulPowToSubmodule a i) := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  simp only [Submodule.mem_comap, Submodule.subtype_apply, smulPowToSubmodule_apply,
    ← mul_smul, ← pow_succ]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- Multiplication by `a^i` induces a map from `M / aM` to `a^i M / a^{i+1} M`. -/
noncomputable def smulPowQuotientMap (a : A) (i : ℕ) :
    M ⧸ (a • (⊤ : Submodule A M)) →ₗ[A] (P a i ⧸ (P a (i + 1)).comap (P a i).subtype) :=
  (a • (⊤ : Submodule A M)).mapQ _ (smulPowToSubmodule a i) (le_comap_smulPowToSubmodule a i)

/-- On a quotient class, `smulPowQuotientMap` multiplies its representative by `a^i`. -/
@[simp]
theorem smulPowQuotientMap_mk (a : A) (i : ℕ) (x : M) :
    smulPowQuotientMap a i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        ⟨a ^ i • x, Submodule.smul_mem_pointwise_smul x _ _ Submodule.mem_top⟩ :=
  (Submodule.mapQ_apply _ _ (smulPowToSubmodule a i) x).trans
    (congrArg Submodule.Quotient.mk (smulPowToSubmodule_apply a i x))

/-- Every class in `a^i M / a^{i+1} M` comes from multiplication by `a^i` on `M / aM`. -/
theorem smulPowQuotientMap_surjective (a : A) (i : ℕ) :
    Function.Surjective (smulPowQuotientMap (M := M) a i) :=
  Submodule.mapQ_surjective _ _ _ _ ((LinearEquiv.ofEq _ _ (range_smulPow a i)).surjective.comp
    (DistribSMul.toLinearMap A M (a ^ i)).surjective_rangeRestrict)

end TauCeti
