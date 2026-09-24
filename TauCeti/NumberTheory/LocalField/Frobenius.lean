/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.ResidueCorrespondence
public import TauCeti.NumberTheory.LocalField.Teichmuller

/-!
# Frobenius in unramified local fields

The arithmetic Frobenius of a finite unramified extension is compatible with restriction through
a normal intermediate field. This identifies the Frobenius elements at different finite levels
of an unramified tower, rather than merely identifying arbitrary generators of their cyclic Galois
groups. It acts on Teichmüller representatives and prime-to-residue-characteristic roots of unity
by raising their residue classes to the cardinality of the base residue field.

## Main result

* `TauCeti.frobeniusAlgEquiv_restrictNormal`: restricting arithmetic Frobenius to a normal
  intermediate field gives arithmetic Frobenius there.
* `TauCeti.frobeniusAlgEquiv_teichmullerLift`: arithmetic Frobenius acts on Teichmüller
  representatives by the `q`-th power map on the residue field.
* `TauCeti.frobeniusAlgEquiv_rootsOfUnity`: on prime-to-residue-characteristic roots of
  unity, arithmetic Frobenius acts by the `q`-th power map.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

section Teichmuller

variable {K L : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]

/-- Arithmetic Frobenius sends the Teichmüller representative of `a` to that of `a ^ q`,
where `q` is the cardinality of the residue field of the base. -/
@[simp]
theorem frobeniusAlgEquiv_teichmullerLift [IsUnramified K L] (a : 𝓀[L]) :
    teichmullerLift L (frobeniusAlgEquiv (K := K) (L := L) • a) =
      teichmullerLift L (a ^ Nat.card 𝓀[K]) := by
  congr 1
  have h := congrArg (fun e : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] ↦ e a)
    (residueField_toAlgEquiv_frobeniusAlgEquiv (K := K) (L := L))
  simpa only [MulSemiringAction.toAlgEquiv_apply,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    Fintype.card_eq_nat_card] using h

/-- Arithmetic Frobenius raises every `(q_L - 1)`-st root of unity in an unramified extension
to the `q_K`-th power. -/
@[simp]
theorem frobeniusAlgEquiv_rootsOfUnity [IsUnramified K L]
    (ζ : rootsOfUnity (Nat.card 𝓀[L] - 1) L) :
    frobeniusAlgEquiv (K := K) (L := L) ((ζ : Lˣ) : L) =
      (((ζ : Lˣ) : L) ^ Nat.card 𝓀[K]) := by
  let a := rootsOfUnityAlgebraMulEquivUnitsResidueField 𝒪[L] L ζ
  have hζ : ((ζ : Lˣ) : L) = ((teichmullerLift L (a : 𝓀[L]) : 𝒪[L]) : L) := by
    rw [← coe_teichmuller_apply]
    exact (algebraMap_teichmuller_rootsOfUnityAlgebraMulEquivUnitsResidueField
      𝒪[L] L ζ).symm
  rw [hζ]
  rw [← AlgEquiv.coe_smul_integerRing, AlgEquiv.smul_teichmullerLift,
    frobeniusAlgEquiv_teichmullerLift,
    map_pow]
  exact (map_pow (algebraMap 𝒪[L] L) (teichmullerLift L (a : 𝓀[L]))
    (Nat.card 𝓀[K])).symm

end Teichmuller

variable {K L M : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [ValuativeExtension K L] [ValuativeExtension L M]

variable [FiniteDimensional K M] [Normal K L] [IsGalois K M]

/-- Arithmetic Frobenius restricts to arithmetic Frobenius through a normal intermediate field
of a finite unramified extension of nonarchimedean local fields. -/
@[simp]
theorem frobeniusAlgEquiv_restrictNormal :
    letI : ValuativeExtension K M := ValuativeExtension.trans K L M
    ∀ [IsUnramified K M],
    letI : FiniteDimensional K L :=
      FiniteDimensional.of_injective (IsScalarTower.toAlgHom K L M).toLinearMap
        (IsScalarTower.toAlgHom K L M).injective
    letI : Algebra.IsSeparable K L :=
      Algebra.isSeparable_tower_bot_of_isSeparable K L M
    letI : IsGalois K L := ⟨⟩
    letI := IsUnramified.tower_bot K L M
    (frobeniusAlgEquiv (K := K) (L := M)).restrictNormal L =
      frobeniusAlgEquiv (K := K) (L := L) := by
  let _ : ValuativeExtension K M := ValuativeExtension.trans K L M
  intro
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
