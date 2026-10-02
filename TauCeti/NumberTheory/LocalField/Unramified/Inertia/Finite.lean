/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Unramified.Inertia.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Conjugation

/-!
# Absolute inertia and Frobenius lifts at finite level

Restriction to a finite Galois subextension `L/K` of the algebraic closure sends the absolute
inertia subgroup onto the zeroth lower ramification group of `L/K`. Thus every finite inertia
automorphism lifts to an automorphism fixing the entire maximal unramified extension. This
surjectivity is needed to pass Sylow subgroups of absolute inertia to finite wild inertia.

The proof uses the unramifiedness criterion for fields fixed by absolute inertia, the identity
`e · f = [L : K]`, and the order formula `#G₀ = e`. The finite fixed field is embedded in the
algebraic closure to apply the absolute inertia criterion; its degree is preserved by
`IntermediateField.liftAlgEquiv`.

The restriction `σ_L` of an arithmetic Frobenius lift to `L` acts on the residue field of `L` as
the `q`-th power map, so conjugation by `σ_L` raises the tame character of `G_0(L/K)` to the
`q`-th power: `θ_0(σ_L τ σ_L⁻¹) = θ_0(τ) ^ q`. This is the finite-level form of the relation
`σ τ σ⁻¹ = τ ^ q` in the tame quotient of the absolute Galois group.

## Main results

* `TauCeti.map_inertiaSubgroup_restrictNormalHom`: the image of `I_K` in `Gal(L/K)` is `G_0`.
* `TauCeti.exists_mem_inertiaSubgroup_restrictNormal_eq`: every element of `G_0` lifts to `I_K`.
* `TauCeti.IsArithFrobeniusLift.tameCharacter_conj_restrictNormal`: the finite-level Frobenius
  twist of the tame character.

## References

* J.-P. Serre, *Local Fields*, Chapter I, §7 and Chapter IV, §§1–2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §9.
-/

public section
noncomputable section

open ValuativeRel IntermediateField TauCeti.LocalFieldsRamification

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : IntermediateField K (AlgebraicClosure K)) [Module.Finite K L] [IsGalois K L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

/-- **Absolute inertia maps onto finite inertia.** For every compatible local-field structure
on a finite Galois subextension `L/K`, the image of `I_K` under restriction is `G₀(L/K)`. -/
@[simp]
theorem map_inertiaSubgroup_restrictNormalHom :
    (inertiaSubgroup K).map (AlgEquiv.restrictNormalHom L) =
      lowerRamificationGroup K L 0 := by
  have hle : (inertiaSubgroup K).map (AlgEquiv.restrictNormalHom L) ≤
      lowerRamificationGroup K L 0 := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact restrictNormal_mem_lowerRamificationGroup_zero L hσ
  let H := (inertiaSubgroup K).map (AlgEquiv.restrictNormalHom L)
  let E := fixedField H
  let E' := lift E
  have : Module.Finite K E' :=
    Module.Finite.of_surjective (liftAlgEquiv E).toLinearMap (liftAlgEquiv E).surjective
  let := finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) E'
  let := finiteIntermediateFieldTopology K (AlgebraicClosure K) E'
  have := finiteIntermediateField_isNonarchimedeanLocalField K (AlgebraicClosure K) E'
  have := finiteIntermediateField_valuativeExtension K (AlgebraicClosure K) E'
  have : Algebra.IsSeparable K E' :=
    Algebra.IsSeparable.of_algHom (f := inclusion (lift_le E))
  have hfix : inertiaSubgroup K ≤ E'.fixingSubgroup := by
    intro σ hσ
    apply (mem_fixingSubgroup_iff _ _).2
    intro x hx
    -- An element of the lifted fixed field is represented by an element of `E` inside `L`.
    obtain ⟨y, hy, rfl⟩ := hx
    have hyfix : AlgEquiv.restrictNormal σ L y = y :=
      (mem_fixedField_iff _ _).1 hy _ ⟨σ, hσ, rfl⟩
    exact (AlgEquiv.restrictNormal_commutes σ L y).symm.trans
      (congrArg (fun z : L ↦ (z : AlgebraicClosure K)) hyfix)
  have : IsUnramified K E' := (inertiaSubgroup_le_fixingSubgroup_iff E').1 hfix
  let ι : E' →ₐ[K] L := inclusion (lift_le E)
  let := ι.toRingHom.toAlgebra
  have : IsScalarTower K E' L := IsScalarTower.of_algHom ι
  have : ValuativeExtension E' L := ι.valuativeExtension
  have hrank : Module.finrank E' L = Module.finrank E L := by
    apply Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := K) (M := E'))
    rw [Module.finrank_mul_finrank K E' L,
      ← (liftAlgEquiv E).toLinearEquiv.finrank_eq, Module.finrank_mul_finrank K E L]
  have he : ramificationIndex K L ≤ Module.finrank E' L := by
    rw [← IsUnramified.ramificationIndex_tower_eq K E' L]
    calc
      ramificationIndex E' L ≤ ramificationIndex E' L * inertiaDegree E' L :=
        Nat.le_mul_of_pos_right _ inertiaDegree_pos
      _ = Module.finrank E' L := ramificationIndex_mul_inertiaDegree E' L
  apply Subgroup.eq_of_le_of_card_ge hle
  calc
    Nat.card (lowerRamificationGroup K L 0) = ramificationIndex K L :=
      natCard_lowerRamificationGroup_zero K L
    _ ≤ Module.finrank E' L := he
    _ = Module.finrank E L := hrank
    _ = Nat.card H := finrank_fixedField_eq_card H

/-- Every element of finite inertia lifts to an element of absolute inertia. -/
theorem exists_mem_inertiaSubgroup_restrictNormal_eq {τ : Gal(L/K)}
    (hτ : τ ∈ lowerRamificationGroup K L 0) :
    ∃ σ ∈ inertiaSubgroup K, AlgEquiv.restrictNormal σ L = τ := by
  rw [← map_inertiaSubgroup_restrictNormalHom L] at hτ
  exact hτ

/-- **The finite-level Frobenius twist.** Let `σ` be an arithmetic Frobenius lift and `σ_L` its
restriction to a finite Galois subextension `L/K`. For every `τ` in the inertia group `G_0` of
`L/K`, the tame character satisfies `θ_0(σ_L τ σ_L⁻¹) = θ_0(τ) ^ q`, where `q` is the
cardinality of the residue field of `K`. -/
theorem IsArithFrobeniusLift.tameCharacter_conj_restrictNormal {σ : Gal(AlgebraicClosure K/K)}
    (hσ : IsArithFrobeniusLift K σ) {π : 𝒪[L]} (hπ : Irreducible π)
    (τ : IsLocalRing.ramificationGroup Gal(L/K) 𝒪[L] 0) :
    tameCharacter hπ (MulAut.conjNormal (AlgEquiv.restrictNormal σ L) τ) =
      tameCharacter hπ τ ^ Nat.card 𝓀[K] :=
  tameCharacter_conj_of_smul_eq_pow hπ (hσ.restrictNormal_smul_residueField_eq_pow L) τ

end TauCeti
