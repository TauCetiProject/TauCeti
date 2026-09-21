/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.NumberTheory.LocalField.Unramified
public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.NumberTheory.RamificationInertia.Galois

/-!
# Residue correspondence for unramified local extensions

For a finite unramified Galois extension `L / K` of nonarchimedean local fields, reduction gives
an isomorphism from the Galois group of `L / K` to the Galois group of the residue-field
extension. Its inverse carries the finite-field Frobenius to the Frobenius automorphism of
`L / K`.

The kernel of reduction is the inertia group. Unramifiedness makes this group trivial, and the
equality of the two finite group orders then gives the residue correspondence. This also shows
that Frobenius generates the Galois group and has order equal to the inertia degree.

## Main definitions

* `TauCeti.residueFieldAutEquiv`: the residue correspondence for an unramified Galois extension.
* `TauCeti.frobeniusAlgEquiv`: the lift of finite-field Frobenius to the extension.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The finite residue field of the base, equipped with a local `Fintype` instance. -/
local instance residueFieldFintype : Fintype 𝓀[K] := Fintype.ofFinite 𝓀[K]

omit [IsGalois K L] in
/-- The kernel of the action of the extension Galois group on the residue field is the inertia
group. -/
theorem ker_residueField_toAlgAut :
    (MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L]).ker =
      𝓂[L].inertia (L ≃ₐ[K] L) := by
  ext σ
  rw [MonoidHom.mem_ker, Ideal.mem_inertia]
  constructor
  · intro h x
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub,
      IsLocalRing.ResidueField.residue_smul]
    exact sub_eq_zero.mpr (by
      simpa using DFunLike.congr_fun h (IsLocalRing.residue 𝒪[L] x))
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    -- Expose the induced action after reducing to a representative of the residue class.
    change σ • IsLocalRing.residue 𝒪[L] x = IsLocalRing.residue 𝒪[L] x
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact h x

/-- The inertia group of an unramified finite Galois extension of local fields is trivial. -/
theorem IsUnramified.inertia_eq_bot [IsUnramified K L] :
    𝓂[L].inertia (L ≃ₐ[K] L) = ⊥ := by
  have hunder : 𝓂[L].under 𝒪[K] = 𝓂[K] := Ideal.LiesOver.over.symm
  have hfinite : Finite (𝒪[K] ⧸ 𝓂[K]) := inferInstanceAs (Finite 𝓀[K])
  let _ : Finite (𝒪[K] ⧸ 𝓂[L].under 𝒪[K]) := hunder.symm ▸ hfinite
  let _ : Finite (𝓂[L].under 𝒪[K]).ResidueField := inferInstance
  let _ := Fintype.ofFinite (𝓂[L].under 𝒪[K]).ResidueField
  let _ : PerfectField (𝓂[L].under 𝒪[K]).ResidueField := inferInstance
  apply Subgroup.eq_bot_of_card_eq
  rw [Ideal.card_inertia_eq_ramificationIdx 𝒪[K] (L ≃ₐ[K] L) 𝓂[L],
    ← ramificationIndex_eq_ramificationIdx, IsUnramified.ramificationIndex_eq_one]

/-- Reduction is a bijection from the Galois group of an unramified extension to the Galois
group of its residue-field extension. -/
theorem residueField_toAlgAut_bijective [IsUnramified K L] :
    Function.Bijective (MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L]) := by
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff, ker_residueField_toAlgAut,
      IsUnramified.inertia_eq_bot]
  · calc
      Nat.card (L ≃ₐ[K] L) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
      _ = inertiaDegree K L := IsUnramified.inertiaDegree_eq_finrank.symm
      _ = Module.finrank 𝓀[K] 𝓀[L] := inertiaDegree_def K L
      _ = Nat.card (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) := by
        simpa using Nat.card_eq_of_bijective _
          (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow 𝓀[K] 𝓀[L])

/-- The residue correspondence between the Galois groups of an unramified local extension and
its residue-field extension. -/
noncomputable def residueFieldAutEquiv [IsUnramified K L] :
    (L ≃ₐ[K] L) ≃* (𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :=
  MulEquiv.ofBijective (MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L])
    residueField_toAlgAut_bijective

/-- The residue correspondence is the canonical action on the residue field. -/
@[simp]
theorem residueFieldAutEquiv_apply [IsUnramified K L] (σ : L ≃ₐ[K] L) :
    residueFieldAutEquiv σ =
      MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L] σ :=
  MulEquiv.ofBijective_apply _ _ σ

/-- The inverse residue correspondence induces the given residue-field automorphism. -/
@[simp]
theorem residueField_toAlgEquiv_residueFieldAutEquiv_symm_apply [IsUnramified K L]
    (τ : 𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L]) :
    MulSemiringAction.toAlgEquiv 𝓀[K] 𝓀[L]
      ((residueFieldAutEquiv (K := K) (L := L)).symm τ) = τ := by
  change residueFieldAutEquiv (K := K) (L := L)
    ((residueFieldAutEquiv (K := K) (L := L)).symm τ) = τ
  exact (residueFieldAutEquiv (K := K) (L := L)).apply_symm_apply τ

/-- The Frobenius automorphism of an unramified local extension is the unique lift of the
finite-field Frobenius on its residue field. -/
noncomputable def frobeniusAlgEquiv [IsUnramified K L] : L ≃ₐ[K] L := by
  exact (residueFieldAutEquiv (K := K) (L := L)).symm
    (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L])

/-- The residue-field action sends local Frobenius to finite-field Frobenius. -/
@[simp]
theorem residueField_toAlgEquiv_frobeniusAlgEquiv [IsUnramified K L] :
    MulSemiringAction.toAlgEquiv 𝓀[K] 𝓀[L]
        (frobeniusAlgEquiv (K := K) (L := L)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L] := by
  exact (residueFieldAutEquiv (K := K) (L := L)).apply_symm_apply _

/-- The order of Frobenius is the inertia degree of an unramified local extension. -/
theorem orderOf_frobeniusAlgEquiv [IsUnramified K L] :
    orderOf (frobeniusAlgEquiv (K := K) (L := L)) = inertiaDegree K L := by
  rw [← (residueFieldAutEquiv (K := K) (L := L)).orderOf_eq,
    residueFieldAutEquiv_apply, MulSemiringAction.toAlgAut_apply,
    residueField_toAlgEquiv_frobeniusAlgEquiv,
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, inertiaDegree_def]

/-- Frobenius generates the Galois group of an unramified local extension. -/
theorem zpowers_frobeniusAlgEquiv [IsUnramified K L] :
    Subgroup.zpowers (frobeniusAlgEquiv (K := K) (L := L)) = ⊤ := by
  rw [← (Subgroup.zpowers _).card_eq_iff_eq_top, Nat.card_zpowers,
    orderOf_frobeniusAlgEquiv, IsGalois.card_aut_eq_finrank,
    IsUnramified.inertiaDegree_eq_finrank]

/-- The Galois group of an unramified local extension is cyclic. -/
noncomputable instance galoisGroupIsCyclic [IsUnramified K L] : IsCyclic (L ≃ₐ[K] L) :=
  (residueFieldAutEquiv (K := K) (L := L)).isCyclic.mpr inferInstance

/-- Frobenius satisfies its characteristic congruence modulo the maximal ideal. -/
theorem valuation_frobeniusAlgEquiv_sub_pow [IsUnramified K L] (y : 𝒪[L]) :
    valuation L (frobeniusAlgEquiv (K := K) (L := L) (y : L) -
      (y : L) ^ Nat.card 𝓀[K]) < 1 := by
  let z : 𝒪[L] :=
    (frobeniusAlgEquiv (K := K) (L := L)).integerRingAlgEquiv y -
      y ^ Nat.card 𝓀[K]
  have hres :
      IsLocalRing.residue 𝒪[L]
          ((frobeniusAlgEquiv (K := K) (L := L)).integerRingAlgEquiv y) =
        (IsLocalRing.residue 𝒪[L] y) ^ Nat.card 𝓀[K] := by
    calc
      IsLocalRing.residue 𝒪[L]
          ((frobeniusAlgEquiv (K := K) (L := L)).integerRingAlgEquiv y) =
          (frobeniusAlgEquiv (K := K) (L := L)).residueFieldEquiv
            (IsLocalRing.residue 𝒪[L] y) := by
              rw [AlgEquiv.residueFieldEquiv_apply, AlgEquiv.integerRingAlgEquiv_apply,
                IsLocalRing.ResidueField.residue_smul]
      _ = residueFieldAutEquiv (frobeniusAlgEquiv (K := K) (L := L))
          (IsLocalRing.residue 𝒪[L] y) := by
            rw [residueFieldAutEquiv_apply, residueField_toAlgAut_apply]
      _ = FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]
          (IsLocalRing.residue 𝒪[L] y) := by
            rw [residueFieldAutEquiv_apply, MulSemiringAction.toAlgAut_apply,
              residueField_toAlgEquiv_frobeniusAlgEquiv]
      _ = (IsLocalRing.residue 𝒪[L] y) ^ Nat.card 𝓀[K] := by
        rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
          Fintype.card_eq_nat_card]
  have hz : z ∈ 𝓂[L] := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simp only [z, map_sub, map_pow, hres, sub_self]
  have hv := (Valuation.mem_maximalIdeal_iff (v := valuation L)).1 hz
  dsimp only [z] at hv
  -- Coercing the integral congruence to `L` exposes the field-valued statement.
  change valuation L
    ((((frobeniusAlgEquiv (K := K) (L := L)).integerRingAlgEquiv y : 𝒪[L]) : L) -
      (y : L) ^ Nat.card 𝓀[K]) < 1 at hv
  rw [AlgEquiv.integerRingAlgEquiv_apply, AlgEquiv.coe_smul_integerRing] at hv
  exact hv

end TauCeti
