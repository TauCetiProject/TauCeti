/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import TauCeti.NumberTheory.NumberField.Units.SUnit.Basic

/-!
# Fundamental systems of S-units

For a finite set `S` of finite places of a number field, the group of `S`-units modulo its
torsion subgroup is free of rank `NumberField.Units.rank K + Nat.card S`. Choosing a basis and
lifting it gives a fundamental system of `S`-units. Every `S`-unit then has a unique expression
as a torsion element times a product of integral powers of the fundamental system.

This is the decomposition form of Dirichlet's S-unit theorem. It supplies the generators whose
logarithms form a basis of the S-unit lattice and on which the S-regulator is evaluated.

The construction follows Mathlib's ordinary-unit API in
`Mathlib.NumberTheory.NumberField.Units.DirichletTheorem`, especially
`NumberField.Units.basisModTorsion`, `NumberField.Units.fundSystem`, and
`NumberField.Units.exist_unique_eq_mul_prod`. The corresponding S-unit formalization also appears
in Ralf Stephan's `ArithmeticHeights/SUnitTheorem.lean` in `rwst/Subspace-Theorems`, commit
`e443c2479e19f7665b31d8e94e2317c8ced1ca06`, released under Apache 2.0.

## Main definitions and results

* `TauCeti.NumberField.SUnit.basisModTorsion`: a basis of the S-units modulo torsion.
* `TauCeti.NumberField.SUnit.fundSystem`: arbitrary lifts of that basis to S-units.
* `TauCeti.NumberField.SUnit.exist_unique_eq_mul_prod`: unique decomposition of an S-unit into
  its torsion and free parts.
* `TauCeti.NumberField.SUnit.closure_fundSystem_sup_torsion_eq_top`: the fundamental system and
  torsion generate all S-units.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Theorem 1.5.13.
-/

public section

open IsDedekindDomain Module NumberField

namespace TauCeti.NumberField.SUnit

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
  (S : Set (HeightOneSpectrum (RingOfIntegers K))) [Finite S]

private instance instModuleFiniteAdditiveUnit : Module.Finite ℤ (Additive (S.unit K)) := by
  rw [Module.Finite.iff_addGroup_fg]
  infer_instance

omit [Finite S] in
private theorem ofMul_mem_torsion_iff {x : S.unit K} :
    Additive.ofMul x ∈ Submodule.torsion ℤ (Additive (S.unit K)) ↔
      x ∈ CommGroup.torsion (S.unit K) := by
  rw [← Submodule.mem_toAddSubgroup, Submodule.torsion_int, AddCommGroup.mem_torsion,
    isOfFinAddOrder_ofMul_iff, CommGroup.mem_torsion]

/-- A basis of the group of S-units modulo its torsion submodule. -/
def basisModTorsion :
    Basis (Fin (NumberField.Units.rank K + Nat.card S)) ℤ
      (Additive (S.unit K) ⧸ Submodule.torsion ℤ (Additive (S.unit K))) :=
  Module.finBasisOfFinrankEq ℤ _ <|
    (finrank_quotient_eq_of_le_torsion le_rfl).trans (finrank_sUnits_numberField K S)

/-- A fundamental system of S-units, obtained by lifting `basisModTorsion` through the quotient
by torsion. -/
def fundSystem : Fin (NumberField.Units.rank K + Nat.card S) → S.unit K :=
  fun i ↦ (Quotient.out (basisModTorsion S i)).toMul

/-- The image of a fundamental S-unit in the quotient by torsion is the corresponding basis
vector. -/
@[simp]
theorem fundSystem_mk (i : Fin (NumberField.Units.rank K + Nat.card S)) :
    Submodule.Quotient.mk (Additive.ofMul (fundSystem S i)) = basisModTorsion S i := by
  rw [fundSystem, ofMul_toMul]
  exact Quotient.out_eq' _

/-- The image in the quotient by torsion of a product of integral powers of the fundamental
system is the corresponding integral combination of basis vectors. -/
private theorem mk_prod_fundSystem_zpow (f : Fin (NumberField.Units.rank K + Nat.card S) → ℤ) :
    Submodule.Quotient.mk (Additive.ofMul (∏ i, fundSystem S i ^ f i)) =
      ∑ i, f i • basisModTorsion S i := by
  simp only [ofMul_prod, ofMul_zpow, ← Submodule.mkQ_apply, map_sum, map_zsmul]
  simp only [Submodule.mkQ_apply, fundSystem_mk]

/-- The exponents in any torsion-times-fundamental-system expression are the basis coordinates
of the S-unit modulo torsion. -/
theorem fun_eq_repr {x ζ : S.unit K} {f : Fin (NumberField.Units.rank K + Nat.card S) → ℤ}
    (hζ : ζ ∈ CommGroup.torsion (S.unit K))
    (h : x = ζ * ∏ i, fundSystem S i ^ f i) :
    f = (basisModTorsion S).repr (Submodule.Quotient.mk (Additive.ofMul x)) := by
  rw [h, ofMul_mul, Submodule.Quotient.mk_add,
    (Submodule.Quotient.mk_eq_zero _).mpr ((ofMul_mem_torsion_iff S).mpr hζ), zero_add,
    mk_prod_fundSystem_zpow, (basisModTorsion S).repr_sum_self f]

/-- Every S-unit has a unique expression as a torsion S-unit times a product of integral powers
of the fundamental system. -/
theorem exist_unique_eq_mul_prod (x : S.unit K) :
    ∃! ζe : CommGroup.torsion (S.unit K) ×
        (Fin (NumberField.Units.rank K + Nat.card S) → ℤ),
      x = ζe.1 * ∏ i, fundSystem S i ^ ζe.2 i := by
  let e := (basisModTorsion S).repr (Submodule.Quotient.mk (Additive.ofMul x))
  let ζ := x * (∏ i, fundSystem S i ^ e i)⁻¹
  have h_tors : ζ ∈ CommGroup.torsion (S.unit K) := by
    rw [← ofMul_mem_torsion_iff, ← Submodule.Quotient.mk_eq_zero, ofMul_mul, ofMul_inv,
      Submodule.Quotient.mk_add, Submodule.Quotient.mk_neg, mk_prod_fundSystem_zpow,
      (basisModTorsion S).sum_repr, add_neg_cancel]
  refine ⟨⟨⟨ζ, h_tors⟩, (e : Fin (NumberField.Units.rank K + Nat.card S) → ℤ)⟩, ?_, ?_⟩
  · simp only [ζ, _root_.inv_mul_cancel_right]
  · rintro ⟨⟨ζ', h_tors'⟩, η⟩ hf
    simp only [ζ, e, ← fun_eq_repr S h_tors' hf, Prod.mk.injEq, Subtype.mk.injEq, and_true]
    nth_rewrite 1 [hf]
    rw [_root_.mul_inv_cancel_right]

/-- The fundamental system and the torsion subgroup generate the full group of S-units. -/
theorem closure_fundSystem_sup_torsion_eq_top :
    Subgroup.closure (Set.range (fundSystem S)) ⊔ CommGroup.torsion (S.unit K) = ⊤ := by
  rw [Subgroup.eq_top_iff', sup_comm]
  intro x
  obtain ⟨c, rfl, _⟩ := exist_unique_eq_mul_prod S x
  exact Subgroup.mul_mem_sup (SetLike.coe_mem c.1) <| Subgroup.prod_mem _
    fun i _ ↦ Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

end

end TauCeti.NumberField.SUnit
