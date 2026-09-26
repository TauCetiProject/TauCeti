/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IsGaloisGroup.Basic
public import Mathlib.RingTheory.Valuation.RamificationGroup
public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
public import TauCeti.NumberTheory.LocalField.IntegerRing
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Automorphisms of finite extensions acting on integral and residue data

An automorphism of a finite extension of a nonarchimedean local field preserves the unique
extended valuation. Consequently it restricts to the ring of integers and its maximal ideal,
and descends to the residue field. This file constructs those three actions and records their
compatibility with inclusion and reduction.

The induced residue-field automorphism is linear over the residue field of the base. It therefore
gives the canonical homomorphism between the corresponding automorphism groups. When the field
extension is Galois, the kernel of this homomorphism is the inertia group in ramification theory.

## Main definitions

* `AlgEquiv.integerRingAlgEquiv`: restriction of a field automorphism to the ring of integers.
* `AlgEquiv.maximalIdealEquiv`: restriction to the maximal ideal.
* `AlgEquiv.residueFieldEquiv`: the induced automorphism of the residue field.

The homomorphism from field automorphisms to residue-field automorphisms is Mathlib's generic
`MulSemiringAction.toAlgAut` applied to the action constructed here.

## Main results

* `TauCeti.decompositionSubgroup_valuationSubring_eq_top`: every automorphism preserves the
  valuation subring of `L`, so Mathlib's `ValuationSubring.decompositionSubgroup` is everything.
* `TauCeti.integerRingFaithfulSMul`: an automorphism is determined by its action on `𝒪[L]`.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §§7–8 and Chapter IV, §1.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

variable [Module.Finite K L]

/-- The ring of integers is stable under every automorphism of a finite extension of a
nonarchimedean local field. -/
instance integerRingIsInvariantSubring : IsInvariantSubring (L ≃ₐ[K] L) 𝒪[L] where
  smul_mem σ x hx := by
    rw [Valuation.mem_integer_iff] at hx ⊢
    simpa only [AlgEquiv.smul_def, σ.valuation_eq] using hx

variable (K L) in
omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
open scoped Pointwise in
/-- Every automorphism of `L/K` preserves the valuation subring of `L`, so its decomposition
subgroup is the whole automorphism group. -/
theorem decompositionSubgroup_valuationSubring_eq_top :
    (valuation L).valuationSubring.decompositionSubgroup K = ⊤ := by
  ext σ
  simp only [Subgroup.mem_top, iff_true, MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, Valuation.mem_valuationSubring_iff,
    Valuation.mem_valuationSubring_iff, AlgEquiv.smul_def, σ⁻¹.valuation_eq]

/-- Scalar multiplication by an extension automorphism is compatible with multiplication by an
integer of the extension. -/
noncomputable instance integerRingSMulDistribClass :
    SMulDistribClass (L ≃ₐ[K] L) 𝒪[L] L :=
  ⟨fun σ x y ↦ by
    -- Unfolding the two scalar actions identifies the assertion with multiplicativity in `L`.
    change σ ((x : L) * y) = ((σ • x : 𝒪[L]) : L) * σ y
    rw [map_mul]
    rfl⟩

/-- The Galois action on a finite extension restricts to a Galois-group action on its ring of
integers. -/
noncomputable instance integerRingIsGaloisGroup [IsGalois K L] :
    IsGaloisGroup (L ≃ₐ[K] L) 𝒪[K] 𝒪[L] := by
  apply IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) 𝒪[K] 𝒪[L] K L

end TauCeti

namespace AlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- The automorphism induced on the ring of integers fixes the ring of integers of the base. -/
noncomputable def integerRingAlgEquiv (σ : L ≃ₐ[K] L) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L] where
  __ := MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] σ
  commutes' x := by
    apply Subtype.ext
    calc
      ((MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] σ
          (algebraMap 𝒪[K] 𝒪[L] x) : 𝒪[L]) : L) =
          σ (((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L)) := rfl
      _ = σ (algebraMap K L (x : K)) := by rw [TauCeti.coe_algebraMap_integerRing]
      _ = algebraMap K L (x : K) := σ.commutes (x : K)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The integer-ring algebra equivalence agrees with the canonical action. -/
@[simp]
theorem integerRingAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    σ.integerRingAlgEquiv x = σ • x :=
  (rfl)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- Coercing the action on the integer ring to `L` recovers the field automorphism. -/
@[simp]
theorem coe_smul_integerRing (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    ((σ • x : 𝒪[L]) : L) = σ (x : L) :=
  (rfl)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- Restricting the scalars of an automorphism along a tower `L/K'/K` does not change its action
on the ring of integers of `L`. -/
@[simp]
theorem restrictScalars_smul_integerRing {K' : Type*} [Field K'] [ValuativeRel K']
    [TopologicalSpace K'] [IsNonarchimedeanLocalField K'] [Algebra K K'] [Algebra K' L]
    [IsScalarTower K K' L] [ValuativeExtension K' L] [Module.Finite K' L]
    (σ : L ≃ₐ[K'] L) (x : 𝒪[L]) :
    σ.restrictScalars K • x = σ • x :=
  Subtype.ext (by rw [coe_smul_integerRing, coe_smul_integerRing, restrictScalars_apply])

/-- The automorphism induced on the maximal ideal of the ring of integers. -/
noncomputable def maximalIdealEquiv (σ : L ≃ₐ[K] L) : 𝓂[L] ≃+* 𝓂[L] where
  toFun x := ⟨MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] σ x, by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hx
    have hx' : ¬IsUnit (x : 𝒪[L]) := x.2
    exact hx' ((isUnit_map_iff (MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] σ)
      (x : 𝒪[L])).mp hx)⟩
  invFun x := ⟨MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] σ.symm x, by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hx
    have hx' : ¬IsUnit (x : 𝒪[L]) := x.2
    exact hx' ((isUnit_map_iff
      (MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] σ.symm) (x : 𝒪[L])).mp hx)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact σ.symm_apply_apply (x : L)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact σ.apply_symm_apply (x : L)
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    simp

/-- Coercing the induced maximal-ideal automorphism to `L` recovers the field automorphism. -/
@[simp]
theorem coe_maximalIdealEquiv (σ : L ≃ₐ[K] L) (x : 𝓂[L]) :
    ((σ.maximalIdealEquiv x : 𝒪[L]) : L) = σ (x : L) :=
  (rfl)

/-- The automorphism induced on the residue field by a field automorphism. It fixes the residue
field of the base extension. -/
noncomputable def residueFieldEquiv (σ : L ≃ₐ[K] L) : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] :=
  IsLocalRing.ResidueField.mapAlgEquiv' σ.integerRingAlgEquiv

/-- The induced residue-field equivalence agrees with the canonical residue-field action. -/
@[simp]
theorem residueFieldEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝓀[L]) :
    σ.residueFieldEquiv x = σ • x := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  rw [residueFieldEquiv, IsLocalRing.ResidueField.mapAlgEquiv'_residue, integerRingAlgEquiv_apply,
    IsLocalRing.ResidueField.residue_smul]

end AlgEquiv

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- The residue-field action of extension automorphisms fixes the base residue field. -/
noncomputable instance residueFieldSMulCommClass :
    SMulCommClass (L ≃ₐ[K] L) 𝓀[K] 𝓀[L] where
  smul_comm σ x y := by
    rw [← AlgEquiv.residueFieldEquiv_apply]
    rw [map_smul, AlgEquiv.residueFieldEquiv_apply]

/-- Field automorphisms act on the maximal ideal by restriction of their action on the ring of
integers. -/
noncomputable instance maximalIdealDistribMulAction :
    DistribMulAction (L ≃ₐ[K] L) (𝓂[L]) where
  smul σ := σ.maximalIdealEquiv
  one_smul x := by
    -- These laws define the same structure as `smul`, so its characterization lemma is not
    -- available until this instance has been constructed.
    change (1 : L ≃ₐ[K] L).maximalIdealEquiv x = x
    apply Subtype.ext
    apply Subtype.ext
    rw [AlgEquiv.coe_maximalIdealEquiv, AlgEquiv.one_apply]
  mul_smul σ τ x := by
    -- As above, expose the supplied `smul` field before the action instance exists.
    change (σ * τ).maximalIdealEquiv x =
      σ.maximalIdealEquiv (τ.maximalIdealEquiv x)
    apply Subtype.ext
    apply Subtype.ext
    rw [AlgEquiv.coe_maximalIdealEquiv, AlgEquiv.coe_maximalIdealEquiv,
      AlgEquiv.coe_maximalIdealEquiv, AlgEquiv.mul_apply]
  smul_add σ x y := σ.maximalIdealEquiv.map_add x y
  smul_zero σ := σ.maximalIdealEquiv.map_zero

/-- The maximal-ideal action is the restriction represented by `AlgEquiv.maximalIdealEquiv`. -/
@[simp]
theorem smul_maximalIdeal_eq (σ : L ≃ₐ[K] L) (x : 𝓂[L]) :
    σ • x = σ.maximalIdealEquiv x :=
  (rfl)

/-- Evaluating the canonical residue-field automorphism homomorphism gives the induced
residue-field equivalence. -/
theorem residueField_toAlgAut_apply (σ : L ≃ₐ[K] L) (x : 𝓀[L]) :
    MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L] σ x =
      σ.residueFieldEquiv x := by
  simpa only [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply] using
    (AlgEquiv.residueFieldEquiv_apply σ x).symm

/-- An automorphism of a finite extension is determined by its action on the ring of integers,
since every element of `L` becomes integral after multiplication by a nonzero integer of `K`. -/
instance integerRingFaithfulSMul : FaithfulSMul (L ≃ₐ[K] L) 𝒪[L] where
  eq_of_smul_eq_smul {σ τ} h := AlgEquiv.ext fun y ↦ by
    obtain ⟨a, ha, hay⟩ := exists_algebraMap_mul_mem_integerRing K L y
    have hσ : ((σ • ⟨_, hay⟩ : 𝒪[L]) : L) = ((τ • ⟨_, hay⟩ : 𝒪[L]) : L) := by rw [h]
    have ha' : algebraMap K L (a : K) ≠ 0 :=
      (map_ne_zero _).2 (Subtype.coe_ne_coe.2 ha)
    rw [AlgEquiv.coe_smul_integerRing, AlgEquiv.coe_smul_integerRing, map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes] at hσ
    exact mul_left_cancel₀ ha' hσ

end TauCeti
