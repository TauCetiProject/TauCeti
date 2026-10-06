/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import TauCeti.NumberTheory.LocalField.Unramified.Basic
public import TauCeti.NumberTheory.LocalField.RamificationGroup

/-!
# Residue correspondence for unramified local extensions

For a finite unramified Galois extension `L / K` of nonarchimedean local fields, reduction gives
an isomorphism from the Galois group of `L / K` to the Galois group of the residue-field
extension. Its inverse carries the finite-field Frobenius to the Frobenius automorphism of
`L / K`.

The residue action is surjective, and its kernel is the inertia group. Unramifiedness makes this
kernel trivial, giving the residue correspondence. This also shows that Frobenius generates the
Galois group and has order equal to the inertia degree. Without assuming unramifiedness, the
quotient by inertia is cyclic because it embeds into the residue-field Galois group.

## Main definitions

* `TauCeti.residueFieldAutEquiv`: the residue correspondence for an unramified Galois extension.
* `TauCeti.frobeniusAlgEquiv`: the lift of finite-field Frobenius to the extension.
* `TauCeti.LocalFieldsRamification.isCyclic_quotient_lowerRamificationGroup_zero`: the quotient
  of the Galois group by inertia is cyclic.

## References

* J.-P. Serre, *Local Fields*, Chapter III, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section
noncomputable section

open ValuativeRel
open scoped Pointwise

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
  let σ' : MulAction.stabilizer (L ≃ₐ[K] L) 𝓂[L] := ⟨σ, by
    rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_eq_comap]
    exact IsLocalRing.eq_maximalIdeal inferInstance⟩
  have haction :
      MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L] σ =
        Ideal.Quotient.stabilizerHom 𝓂[L] 𝓂[K] (L ≃ₐ[K] L) σ' := by
    ext x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply]
    -- Mathlib's generic action is on the quotient, definitionally the residue field.
    change σ • IsLocalRing.residue 𝒪[L] x =
      IsLocalRing.residue 𝒪[L] (σ' • x)
    rw [IsLocalRing.ResidueField.residue_smul]
    rfl
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have hgeneric :
        Ideal.Quotient.stabilizerHom 𝓂[L] 𝓂[K] (L ≃ₐ[K] L) σ' = 1 :=
      haction.symm.trans h
    have hmem : σ' ∈ 𝓂[L].inertia (MulAction.stabilizer (L ≃ₐ[K] L) 𝓂[L]) := by
      rw [← Ideal.Quotient.ker_stabilizerHom 𝓂[L] 𝓂[K] (L ≃ₐ[K] L),
        MonoidHom.mem_ker]
      exact hgeneric
    exact Ideal.coe_mem_inertia.mpr hmem
  · intro h
    have hmem : σ' ∈ 𝓂[L].inertia (MulAction.stabilizer (L ≃ₐ[K] L) 𝓂[L]) :=
      Ideal.coe_mem_inertia.mp h
    have hgeneric :
        Ideal.Quotient.stabilizerHom 𝓂[L] 𝓂[K] (L ≃ₐ[K] L) σ' = 1 := by
      rw [← MonoidHom.mem_ker, Ideal.Quotient.ker_stabilizerHom]
      exact hmem
    exact haction.trans hgeneric

namespace LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]

/-- The quotient `G / G_0` of the Galois group by inertia is cyclic: the action on the residue
field identifies it with a subgroup of the Galois group of the finite residue field extension,
which is cyclic. -/
theorem isCyclic_quotient_lowerRamificationGroup_zero :
    IsCyclic ((L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0) := by
  let f := MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L]
  have hf : f.ker = lowerRamificationGroup K L 0 := by
    rw [ker_residueField_toAlgAut, lowerRamificationGroup_zero]
  let e :=
    (QuotientGroup.quotientMulEquivOfEq hf.symm).trans (QuotientGroup.quotientKerEquivRange f)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end LocalFieldsRamification

/-- The inertia group of an unramified finite Galois extension of local fields is trivial. -/
theorem IsUnramified.inertia_eq_bot [IsUnramified K L] :
    𝓂[L].inertia (L ≃ₐ[K] L) = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ <| by
    rw [← LocalFieldsRamification.lowerRamificationGroup_zero,
      LocalFieldsRamification.natCard_lowerRamificationGroup_zero,
      IsUnramified.ramificationIndex_eq_one]

/-- Reduction from the Galois group to the residue-field Galois group is surjective. -/
theorem residueField_toAlgAut_surjective :
    Function.Surjective (MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L]) := by
  intro τ
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective
    (L ≃ₐ[K] L) 𝓂[K] 𝓂[L] τ
  refine ⟨σ.1, ?_⟩
  ext x
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
  have hx := DFunLike.congr_fun hσ (IsLocalRing.residue 𝒪[L] x)
  -- Identify the quotient in `stabilizerHom` with the local ring's residue field.
  change IsLocalRing.residue 𝒪[L] (σ.1 • x) =
    τ (IsLocalRing.residue 𝒪[L] x) at hx
  rw [IsLocalRing.ResidueField.residue_smul] at hx
  rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply]
  exact hx

/-- Reduction is a bijection from the Galois group of an unramified extension to the Galois
group of its residue-field extension. -/
theorem residueField_toAlgAut_bijective [IsUnramified K L] :
    Function.Bijective (MulSemiringAction.toAlgAut (L ≃ₐ[K] L) 𝓀[K] 𝓀[L]) := by
  refine ⟨?_, residueField_toAlgAut_surjective⟩
  rw [← MonoidHom.ker_eq_bot_iff, ker_residueField_toAlgAut,
    IsUnramified.inertia_eq_bot]

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
  rw [← MulSemiringAction.toAlgAut_apply, ← residueFieldAutEquiv_apply]
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
noncomputable instance isCyclic_algEquiv [IsUnramified K L] : IsCyclic (L ≃ₐ[K] L) :=
  (residueFieldAutEquiv (K := K) (L := L)).isCyclic.mpr inferInstance

/-- Frobenius satisfies its characteristic congruence modulo the maximal ideal. -/
theorem valuation_frobeniusAlgEquiv_sub_pow [IsUnramified K L] (y : 𝒪[L]) :
    valuation L (frobeniusAlgEquiv (K := K) (L := L) (y : L) -
      (y : L) ^ Nat.card 𝓀[K]) < 1 := by
  let z : 𝒪[L] :=
    (frobeniusAlgEquiv (K := K) (L := L)).integerRingEquiv y -
      y ^ Nat.card 𝓀[K]
  have hres :
      IsLocalRing.residue 𝒪[L]
          ((frobeniusAlgEquiv (K := K) (L := L)).integerRingEquiv y) =
        (IsLocalRing.residue 𝒪[L] y) ^ Nat.card 𝓀[K] := by
    calc
      IsLocalRing.residue 𝒪[L]
          ((frobeniusAlgEquiv (K := K) (L := L)).integerRingEquiv y) =
          (frobeniusAlgEquiv (K := K) (L := L)).residueFieldEquiv
            (IsLocalRing.residue 𝒪[L] y) := by
              rw [AlgEquiv.residueFieldEquiv_apply, AlgEquiv.integerRingEquiv_apply,
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
    ((((frobeniusAlgEquiv (K := K) (L := L)).integerRingEquiv y : 𝒪[L]) : L) -
      (y : L) ^ Nat.card 𝓀[K]) < 1 at hv
  rw [AlgEquiv.integerRingEquiv_apply, AlgEquiv.coe_smul_integerRing] at hv
  exact hv

/-- An automorphism satisfying the characteristic Frobenius congruence is Frobenius. -/
theorem eq_frobeniusAlgEquiv_of_valuation_sub_pow_lt_one [IsUnramified K L]
    (σ : L ≃ₐ[K] L)
    (hσ : ∀ y : 𝒪[L],
      valuation L (σ (y : L) - (y : L) ^ Nat.card 𝓀[K]) < 1) :
    σ = frobeniusAlgEquiv (K := K) (L := L) := by
  apply (residueFieldAutEquiv (K := K) (L := L)).injective
  ext x
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
  simp only [residueFieldAutEquiv_apply, MulSemiringAction.toAlgAut_apply,
    residueField_toAlgEquiv_frobeniusAlgEquiv,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Fintype.card_eq_nat_card,
    MulSemiringAction.toAlgEquiv_apply]
  rw [← IsLocalRing.ResidueField.residue_smul]
  rw [← sub_eq_zero, ← map_pow, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  apply (Valuation.mem_maximalIdeal_iff (v := valuation L)).2
  have hsubtype :
      valuation L (𝒪[L].subtype (σ • y - y ^ Nat.card 𝓀[K])) < 1 := by
    rw [map_sub, map_pow]
    have hcoe : 𝒪[L].subtype (σ • y) = σ (y : L) :=
      AlgEquiv.coe_smul_integerRing σ y
    rw [hcoe]
    exact hσ y
  exact hsubtype

end TauCeti
