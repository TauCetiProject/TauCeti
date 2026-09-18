/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.NumberTheory.LocalField.FiniteExtension
public import TauCeti.RingTheory.Valuation.ValuativeRel.Extension

/-!
# Automorphisms of finite extensions acting on integral and residue data

An automorphism of a finite extension of a nonarchimedean local field preserves the unique
extended valuation. Consequently it restricts to the ring of integers and its maximal ideal,
and descends to the residue field. This file constructs those three actions and records their
compatibility with inclusion and reduction.

The induced residue-field automorphism is linear over the residue field of the base. It therefore
gives the canonical homomorphism from the Galois group of the extension to the Galois group of
the residue extension; its kernel is the inertia group in ramification theory.

## Main definitions

* `AlgEquiv.integerRingEquiv`: restriction of a field automorphism to the ring of integers.
* `AlgEquiv.maximalIdealEquiv`: restriction to the maximal ideal.
* `AlgEquiv.residueFieldEquiv`: the induced automorphism of the residue field.
* `TauCeti.residueFieldAut`: the homomorphism from field automorphisms to residue-field
  automorphisms.

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

/-- The structure map of a compatible extension restricts to its rings of integers. -/
noncomputable instance integerRingAlgebra : Algebra 𝒪[K] 𝒪[L] := inferInstance

/-- The local map on rings of integers induces the residue-field extension. -/
noncomputable instance residueFieldAlgebra : Algebra 𝓀[K] 𝓀[L] := inferInstance

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] in
/-- Coercing the integer-ring structure map to `L` gives the field structure map. -/
@[simp]
theorem coe_algebraMap_integerRing (x : 𝒪[K]) :
    ((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L) = algebraMap K L (x : K) :=
  rfl

/-- Reduction commutes with the structure map between the rings of integers. -/
@[simp]
theorem algebraMap_residueField_residue (x : 𝒪[K]) :
    algebraMap 𝓀[K] 𝓀[L] (IsLocalRing.residue 𝒪[K] x) =
      IsLocalRing.residue 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) :=
  rfl

variable [Module.Finite K L]

/-- The ring of integers is stable under every automorphism of a finite extension of a
nonarchimedean local field. -/
instance integerRingIsInvariantSubring : IsInvariantSubring (L ≃ₐ[K] L) 𝒪[L] where
  smul_mem σ x hx := by
    rw [Valuation.mem_integer_iff] at hx ⊢
    simpa only [AlgEquiv.smul_def, σ.valuation_eq] using hx

end TauCeti

namespace AlgEquiv

open TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- The automorphism of the ring of integers induced by a field automorphism. -/
noncomputable def integerRingEquiv (σ : L ≃ₐ[K] L) : 𝒪[L] ≃+* 𝒪[L] :=
  MulSemiringAction.toRingAut (L ≃ₐ[K] L) 𝒪[L] σ

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The restricted automorphism agrees with the canonical action on the integer ring. -/
theorem integerRingEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    σ.integerRingEquiv x = σ • x :=
  (rfl)

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- Coercing the restricted integer-ring automorphism to `L` recovers the field automorphism. -/
@[simp]
theorem coe_integerRingEquiv (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    ((σ.integerRingEquiv x : 𝒪[L]) : L) = σ (x : L) :=
  (rfl)

/-- The automorphism induced on the ring of integers fixes the ring of integers of the base. -/
noncomputable def integerRingAlgEquiv (σ : L ≃ₐ[K] L) : 𝒪[L] ≃ₐ[𝒪[K]] 𝒪[L] where
  __ := σ.integerRingEquiv
  commutes' x := by
    apply Subtype.ext
    calc
      ((σ.integerRingEquiv (algebraMap 𝒪[K] 𝒪[L] x) : 𝒪[L]) : L) =
          σ ((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L) :=
        coe_integerRingEquiv σ _
      _ = σ (algebraMap K L (x : K)) := by
        rw [TauCeti.coe_algebraMap_integerRing]
      _ = algebraMap K L (x : K) := σ.commutes (x : K)
      _ = ((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L) :=
        (TauCeti.coe_algebraMap_integerRing x).symm

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- The integer-ring algebra equivalence has the same underlying map as the restricted ring
equivalence. -/
@[simp]
theorem integerRingAlgEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    σ.integerRingAlgEquiv x = σ.integerRingEquiv x :=
  (rfl)

/-- The automorphism induced on the maximal ideal of the ring of integers. -/
noncomputable def maximalIdealEquiv (σ : L ≃ₐ[K] L) : 𝓂[L] ≃+ 𝓂[L] where
  toFun x := ⟨σ.integerRingEquiv x, by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hx
    have hx' : ¬IsUnit (x : 𝒪[L]) := x.2
    exact hx' ((isUnit_map_iff σ.integerRingEquiv (x : 𝒪[L])).mp hx)⟩
  invFun x := ⟨σ.symm.integerRingEquiv x, by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hx
    have hx' : ¬IsUnit (x : 𝒪[L]) := x.2
    exact hx' ((isUnit_map_iff σ.symm.integerRingEquiv (x : 𝒪[L])).mp hx)⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_integerRingEquiv, coe_integerRingEquiv, σ.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rw [coe_integerRingEquiv, coe_integerRingEquiv, σ.apply_symm_apply]
  map_add' x y := by
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

/-- The induced residue-field automorphism commutes with reduction from the integer ring. -/
@[simp]
theorem residueFieldEquiv_residue (σ : L ≃ₐ[K] L) (x : 𝒪[L]) :
    σ.residueFieldEquiv (IsLocalRing.residue 𝒪[L] x) =
      IsLocalRing.residue 𝒪[L] (σ.integerRingEquiv x) := by
  simpa only [residueFieldEquiv, integerRingAlgEquiv_apply] using
    IsLocalRing.ResidueField.mapAlgEquiv'_residue σ.integerRingAlgEquiv x

/-- The induced residue-field equivalence agrees with the canonical residue-field action. -/
theorem residueFieldEquiv_apply (σ : L ≃ₐ[K] L) (x : 𝓀[L]) :
    σ.residueFieldEquiv x = σ • x := by
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  rw [residueFieldEquiv_residue, integerRingEquiv_apply,
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

/-- The canonical homomorphism from the Galois group of a finite extension to the Galois group
of its residue-field extension. -/
noncomputable def residueFieldAut : (L ≃ₐ[K] L) →* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L]

/-- Evaluating the residue-field automorphism homomorphism gives the induced residue-field
equivalence. -/
@[simp]
theorem residueFieldAut_apply (σ : L ≃ₐ[K] L) (x : 𝓀[L]) :
    residueFieldAut σ x = σ.residueFieldEquiv x := by
  simpa only [residueFieldAut, MulSemiringAction.toAlgAut_apply,
    MulSemiringAction.toAlgEquiv_apply] using (AlgEquiv.residueFieldEquiv_apply σ x).symm

end TauCeti
