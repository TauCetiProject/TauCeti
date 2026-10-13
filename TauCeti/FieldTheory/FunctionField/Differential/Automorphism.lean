/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.CanonicalDivisor
public import TauCeti.FieldTheory.FunctionField.Differential.LocalComponent
public import TauCeti.FieldTheory.FunctionField.Repartition.Automorphism

/-!
# The automorphism group acting on Weil differentials

Let `F' / F` be an extension of fields and `k` a subfield of `F`. An `F`-automorphism `σ` of
`F'` acts on the repartition space `A_F` of `F' / k` (`TauCeti.repartitionRepresentation`), and
hence, contragrediently, on the `k`-linear forms on `A_F`:

`(σ • ω) a = ω (σ⁻¹ • a)`.

This is Mathlib's dual representation `Representation.dual`. Since the action on repartitions
carries `A_F(D)` onto `A_F(σ • D)` and preserves the diagonal copy of `F'`, it carries the Weil
differentials bounded by `D` onto those bounded by `σ • D`. So it preserves the space `Ω_F` of
Weil differentials, which becomes a `k`-linear representation of `F' ≃ₐ[F] F'`.

The action is compatible with all the structure of `Ω_F`. It is `σ`-semilinear for the
`F'`-vector space structure: `σ • (f · ω) = σ f · (σ • ω)`. It moves local components with the
places: `(σ • ω)_{σ • P} (σ x) = ω_P (x)`. The divisor of a Weil differential is equivariant,
`(σ • ω) = σ • (ω)`. In particular the canonical class is fixed by every automorphism.

## Main definitions

* `TauCeti.weilDifferentialRepresentation`: the representation of `F' ≃ₐ[F] F'` on the space
  `Ω_F` of Weil differentials.

## Main results

* `TauCeti.dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul_iff`: the action
  carries `Ω_F(D)` onto `Ω_F(σ • D)`.
* `TauCeti.dual_repartitionRepresentation_repartitionDualMul` and
  `TauCeti.weilDifferentialRepresentation_weilDifferentialSpaceMul`: the action is `σ`-semilinear
  over `F'`.
* `TauCeti.weilDifferentialDivisor_dual_repartitionRepresentation`: **the divisor of a Weil
  differential is equivariant**, `(σ • ω) = σ • (ω)`, with its coefficient form
  `TauCeti.weilDifferentialOrder_dual_repartitionRepresentation`.
* `TauCeti.smul_canonicalClass`: **automorphisms fix the canonical class**.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.5 and I.7 for Weil differentials and Section III.5 for the automorphism action on
  places.
* G. D. Villa Salvador, *Topics in the Theory of Algebraic Function Fields*, Birkhäuser, 2006,
  Chapter 9, for automorphism groups of function fields.
-/

public section

namespace TauCeti

open AlgebraicGeometry

universe u v v'

variable {k : Type u} {F : Type v} {F' : Type v'}
variable [Field k] [Field F] [Field F']
variable [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
variable (σ : F' ≃ₐ[F] F')

/-! ### The action on linear forms on repartitions -/

/-- The action of an automorphism on linear forms is injective. -/
theorem dual_repartitionRepresentation_eq_zero_iff {ω : Module.Dual k ↥(repartitionSpace k F')} :
    (repartitionRepresentation k F F').dual σ ω = 0 ↔ ω = 0 :=
  map_eq_zero_iff _ (((repartitionRepresentation k F F').dual).apply_bijective σ).injective

/-- The action of an automorphism on linear forms sends a form bounded by `D` to one bounded by
`σ • D`: it pulls back along `σ⁻¹`, which carries `A_F(σ • D)` into `A_F(D)` and constants to
constants. -/
private theorem dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul
    {D : Divisor k F'} {ω : Module.Dual k ↥(repartitionSpace k F')}
    (hω : ω ∈ weilDifferentialFiltration D) :
    (repartitionRepresentation k F F').dual σ ω ∈ weilDifferentialFiltration (σ • D) := by
  refine mem_weilDifferentialFiltration_of_apply_eq_zero (fun a ha ↦ ?_) (fun a ha ↦ ?_) <;>
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
  · refine weilDifferentialFiltration_apply_eq_zero_of_mem_adeleFiltration hω _ ?_
    rw [coe_repartitionRepresentation_apply, ← inv_smul_smul σ D,
      placeFamilyRepresentation_mem_adeleFiltration_smul_iff]
    exact ha
  · refine weilDifferentialFiltration_apply_eq_zero_of_mem_diagonalRepartitions hω _ ?_
    rw [coe_repartitionRepresentation_apply,
      placeFamilyRepresentation_mem_diagonalRepartitions_iff]
    exact ha

/-- **The action carries `Ω_F(D)` onto `Ω_F(σ • D)`**: a linear form on `A_F` vanishes on
`A_F(D) + F'` exactly when its image under `σ` vanishes on `A_F(σ • D) + F'`. -/
theorem dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul_iff
    {D : Divisor k F'} {ω : Module.Dual k ↥(repartitionSpace k F')} :
    (repartitionRepresentation k F F').dual σ ω ∈ weilDifferentialFiltration (σ • D) ↔
      ω ∈ weilDifferentialFiltration D := by
  refine ⟨fun h ↦ ?_, dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul σ⟩
  have h' := dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul σ⁻¹ h
  rwa [Representation.inv_self_apply, inv_smul_smul] at h'

/-- **The action preserves the space `Ω_F` of Weil differentials.** -/
theorem dual_repartitionRepresentation_mem_weilDifferentialSpace_iff
    {ω : Module.Dual k ↥(repartitionSpace k F')} :
    (repartitionRepresentation k F F').dual σ ω ∈ weilDifferentialSpace k F' ↔
      ω ∈ weilDifferentialSpace k F' := by
  simp only [mem_weilDifferentialSpace_iff]
  constructor
  · rintro ⟨D, hD⟩
    rw [← smul_inv_smul σ D,
      dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul_iff] at hD
    exact ⟨_, hD⟩
  · rintro ⟨D, hD⟩
    exact ⟨σ • D, (dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul_iff σ).mpr hD⟩

/-- **The action on linear forms is `σ`-semilinear over `F'`**: `σ • (f · ω) = σ f · (σ • ω)`. -/
theorem dual_repartitionRepresentation_repartitionDualMul (hF : IsFunctionField k F') (f : F')
    (ω : Module.Dual k ↥(repartitionSpace k F')) :
    (repartitionRepresentation k F F').dual σ (repartitionDualMul hF f ω) =
      repartitionDualMul hF (σ f) ((repartitionRepresentation k F F').dual σ ω) := by
  ext a
  simp [Module.Dual.transpose_apply, repartitionRepresentation_repartitionMul, AlgEquiv.aut_inv]

/-! ### The action on Weil differentials -/

variable (k F F') in
/-- **The automorphism group acting on the Weil differentials** of `F' / k`: the restriction of
the dual of `TauCeti.repartitionRepresentation` to the stable subspace `Ω_F`, so that
`(σ • ω) a = ω (σ⁻¹ • a)`. -/
noncomputable def weilDifferentialRepresentation :
    Representation k (F' ≃ₐ[F] F') ↥(weilDifferentialSpace k F') where
  toFun σ := ((repartitionRepresentation k F F').dual σ).restrict fun _ hω ↦
    (dual_repartitionRepresentation_mem_weilDifferentialSpace_iff σ).mpr hω
  map_one' := LinearMap.ext fun ω ↦
    Subtype.ext (LinearMap.congr_fun (map_one (repartitionRepresentation k F F').dual) ω.1)
  map_mul' σ τ := LinearMap.ext fun ω ↦
    Subtype.ext (LinearMap.congr_fun (map_mul (repartitionRepresentation k F F').dual σ τ) ω.1)

/-- The action on Weil differentials is the action on the underlying linear forms. -/
@[simp]
theorem coe_weilDifferentialRepresentation_apply (ω : ↥(weilDifferentialSpace k F')) :
    ((weilDifferentialRepresentation k F F' σ ω : ↥(weilDifferentialSpace k F')) :
      Module.Dual k ↥(repartitionSpace k F')) = (repartitionRepresentation k F F').dual σ ω :=
  (rfl)

/-- **The action on Weil differentials is `σ`-semilinear over `F'`**, for the multiplication
`TauCeti.weilDifferentialSpaceMul` that makes `Ω_F` an `F'`-vector space. -/
theorem weilDifferentialRepresentation_weilDifferentialSpaceMul (hF : IsFunctionField k F')
    (f : F') (ω : ↥(weilDifferentialSpace k F')) :
    weilDifferentialRepresentation k F F' σ (weilDifferentialSpaceMul hF f ω) =
      weilDifferentialSpaceMul hF (σ f) (weilDifferentialRepresentation k F F' σ ω) :=
  Subtype.ext <| by
    simp only [coe_weilDifferentialRepresentation_apply, coe_weilDifferentialSpaceMul_apply,
      dual_repartitionRepresentation_repartitionDualMul]

/-! ### The divisor of a moved Weil differential -/

/-- **The divisor of a Weil differential is equivariant**: `(σ • ω) = σ • (ω)`. The action
carries the divisors bounding `ω` bijectively onto those bounding `σ • ω`, preserving the order,
so it carries the greatest one to the greatest one. -/
@[simp]
theorem weilDifferentialDivisor_dual_repartitionRepresentation (hF : IsFunctionField k F')
    (hex : IsIntegrallyClosedIn k F') {ω : Module.Dual k ↥(repartitionSpace k F')}
    (hmem : ω ∈ weilDifferentialSpace k F') (hω : ω ≠ 0) :
    weilDifferentialDivisor hF hex
        ((dual_repartitionRepresentation_mem_weilDifferentialSpace_iff σ).mpr hmem)
        ((dual_repartitionRepresentation_eq_zero_iff σ).not.mpr hω) =
      σ • weilDifferentialDivisor hF hex hmem hω := by
  refine (isGreatest_weilDifferentialDivisor hF hex _ _).unique ⟨?_, fun D hD ↦ ?_⟩
  · exact (dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul_iff σ).mpr
      (isGreatest_weilDifferentialDivisor hF hex hmem hω).1
  · rw [Set.mem_ofPred_eq, ← smul_inv_smul σ D,
      dual_repartitionRepresentation_mem_weilDifferentialFiltration_smul_iff,
      mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor hF hex hmem hω] at hD
    rw [← smul_inv_smul σ D]
    exact (WeilDivisor.smul_le_smul_iff σ).mpr hD

/-- The order of `σ • ω` at a place `Q` is the order of `ω` at `σ⁻¹ • Q`. This is the
coefficient form of `TauCeti.weilDifferentialDivisor_dual_repartitionRepresentation`. -/
@[simp]
theorem weilDifferentialOrder_dual_repartitionRepresentation (hF : IsFunctionField k F')
    (hex : IsIntegrallyClosedIn k F') {ω : Module.Dual k ↥(repartitionSpace k F')}
    (hmem : ω ∈ weilDifferentialSpace k F') (hω : ω ≠ 0) (Q : Place k F') :
    weilDifferentialOrder hF hex
        ((dual_repartitionRepresentation_mem_weilDifferentialSpace_iff σ).mpr hmem)
        ((dual_repartitionRepresentation_eq_zero_iff σ).not.mpr hω) Q =
      weilDifferentialOrder hF hex hmem hω (σ⁻¹ • Q) := by
  rw [← coeff_weilDifferentialDivisor, ← coeff_weilDifferentialDivisor,
    weilDifferentialDivisor_dual_repartitionRepresentation, WeilDivisor.coeff_smul]

/-- **Automorphisms fix the canonical class**: moving a nonzero Weil differential by `σ` gives a
nonzero Weil differential, whose divisor is the moved divisor. -/
@[simp]
theorem smul_canonicalClass (hF : IsFunctionField k F') (hex : IsIntegrallyClosedIn k F') :
    σ • canonicalClass hF hex = canonicalClass hF hex := by
  obtain ⟨ω, hmem, hω⟩ := (Submodule.ne_bot_iff _).mp (weilDifferentialSpace_ne_bot hF hex)
  conv_lhs => rw [← divisorClass_weilDifferentialDivisor hF hex hmem hω]
  rw [Divisor.smul_divisorClass,
    ← weilDifferentialDivisor_dual_repartitionRepresentation σ hF hex hmem hω,
    divisorClass_weilDifferentialDivisor]

end TauCeti
