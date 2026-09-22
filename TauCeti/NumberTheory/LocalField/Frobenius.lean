/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence

/-!
# Frobenius in towers of unramified local fields

The arithmetic Frobenius of a finite unramified extension is compatible with restriction through
a normal intermediate field. This identifies the Frobenius elements at different finite levels
of an unramified tower, rather than merely identifying arbitrary generators of their cyclic Galois
groups.

## Main result

* `TauCeti.frobeniusAlgEquiv_restrictNormal`: restricting arithmetic Frobenius to a normal
  intermediate field gives arithmetic Frobenius there.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable {K L M : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M] [ValuativeExtension K M]
  [FiniteDimensional K M] [Normal K L] [IsGalois K M] [IsUnramified K M]

/-- Arithmetic Frobenius restricts to arithmetic Frobenius through a normal intermediate field
of a finite unramified extension of nonarchimedean local fields. -/
@[simp]
theorem frobeniusAlgEquiv_restrictNormal :
    letI : FiniteDimensional K L :=
      FiniteDimensional.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
        (IsScalarTower.toAlgHom K L M).injective
    letI : Algebra.IsSeparable K L :=
      Algebra.isSeparable_tower_bot_of_isSeparable K L M
    letI : IsGalois K L := ⟨⟩
    letI := IsUnramified.tower_bot K L M
    (frobeniusAlgEquiv (K := K) (L := M)).restrictNormal L =
      frobeniusAlgEquiv (K := K) (L := L) := by
  let _ : FiniteDimensional K L :=
    FiniteDimensional.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
      (IsScalarTower.toAlgHom K L M).injective
  let _ : Algebra.IsSeparable K L :=
    Algebra.isSeparable_tower_bot_of_isSeparable K L M
  let _ : IsGalois K L := ⟨⟩
  let _ : IsUnramified K L := IsUnramified.tower_bot K L M
  let σ := frobeniusAlgEquiv (K := K) (L := M)
  apply eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one
  intro y
  let d : 𝒪[L] := (σ.restrictNormal L).integerRingAlgEquiv y - y ^ Nat.card 𝓀[K]
  have hdcoe : (d : L) =
      (σ.restrictNormal L) (y : L) - (y : L) ^ Nat.card 𝓀[K] := by
    -- Expose the field-valued expression represented by the integer-ring difference `d`.
    change ((((σ.restrictNormal L).integerRingAlgEquiv y : 𝒪[L]) : L) -
      (y : L) ^ Nat.card 𝓀[K]) = _
    rw [AlgEquiv.integerRingAlgEquiv_apply, AlgEquiv.coe_smul_integerRing]
  have hd : d ∈ IsLocalRing.maximalIdeal 𝒪[L] := by
    have hσ := valuation_frobeniusAlgEquiv_sub_pow (K := K) (L := M)
      (algebraMap 𝒪[L] 𝒪[M] y)
    have hdM : algebraMap 𝒪[L] 𝒪[M] d ∈ IsLocalRing.maximalIdeal 𝒪[M] := by
      apply (Valuation.mem_maximalIdeal_iff (v := valuation M)).2
      rw [coe_algebraMap_integerRing, hdcoe, map_sub, map_pow,
        AlgEquiv.restrictNormal_commutes]
      exact hσ
    exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
      (valuation L) (valuation M)).mp hdM
  have hv := (Valuation.mem_maximalIdeal_iff (v := valuation L)).1 hd
  rw [hdcoe] at hv
  simpa only [σ] using hv

end TauCeti
