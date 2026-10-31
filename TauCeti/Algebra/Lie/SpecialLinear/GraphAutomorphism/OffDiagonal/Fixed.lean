/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism.OffDiagonal.Cycles
public import TauCeti.LinearAlgebra.WeightedCycle.Family.Signed

/-!
# Fixed off-diagonal matrices for the type-A graph automorphism

The actual zero-diagonal fixed submodule has one scalar coordinate on each positive
cycle and one `2`-torsion coordinate on each negative cycle. The coordinates read native
matrix entries. In particular, negative singleton cycles are retained in characteristic two.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ)

/-- Cycles whose integral sign product is positive. -/
abbrev TypeAOffDiagonalPositiveCycle :=
  {c : TypeAOffDiagonalCycle r // (∏ i, typeAOffDiagonalCycleSign r c i) = 1}

/-- Cycles whose integral sign product is negative. -/
abbrev TypeAOffDiagonalNegativeCycle :=
  {c : TypeAOffDiagonalCycle r // (∏ i, typeAOffDiagonalCycleSign r c i) = -1}

variable (A : Type*) [CommRing A]

/-- Zero-diagonal trace-zero matrices fixed by the native graph automorphism. -/
def typeASpecialLinearFixedOffDiagonal : Submodule A (sl (Fin (r + 1)) A) :=
  specialLinearOffDiagonal (Fin (r + 1)) A ⊓
    (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap.fixedSubmodule

/-- Membership means zero diagonal and fixedness in the native special linear algebra. -/
@[simp]
theorem mem_typeASpecialLinearFixedOffDiagonal_iff (X : sl (Fin (r + 1)) A) :
    X ∈ typeASpecialLinearFixedOffDiagonal r A ↔
      (∀ i, X.val i i = 0) ∧ typeASpecialLinearGraphAutomorphism r A X = X := by
  rw [typeASpecialLinearFixedOffDiagonal, Submodule.mem_inf,
    mem_specialLinearOffDiagonal_iff, LinearMap.mem_fixedSubmodule_iff]
  rfl

private theorem offDiagonalGraphLinearMap_mem (X : sl (Fin (r + 1)) A)
    (hX : X ∈ specialLinearOffDiagonal (Fin (r + 1)) A) :
    (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap X ∈
      specialLinearOffDiagonal (Fin (r + 1)) A :=
  typeASpecialLinearGraphAutomorphism_mem_specialLinearOffDiagonal r A X hX

private theorem offDiagonalGraphEquiv_toLinearMap :
    (typeAOffDiagonalGraphEquiv r A).toLinearMap =
      ((typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap).restrict
        (offDiagonalGraphLinearMap_mem r A) := by
  ext X : 1
  apply Subtype.ext
  exact typeAOffDiagonalGraphEquiv_apply r A X

private theorem fixedOffDiagonal_eq :
    typeASpecialLinearFixedOffDiagonal r A =
      specialLinearOffDiagonal (Fin (r + 1)) A ⊓
        (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap.fixedSubmodule :=
  rfl

private def offDiagonalFixedRestrictEquiv :
    typeASpecialLinearFixedOffDiagonal r A ≃ₗ[A]
      (typeAOffDiagonalGraphEquiv r A).toLinearMap.fixedSubmodule :=
  (LinearEquiv.ofEq (typeASpecialLinearFixedOffDiagonal r A)
    (specialLinearOffDiagonal (Fin (r + 1)) A ⊓
      (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap.fixedSubmodule)
    (fixedOffDiagonal_eq r A)).trans
    ((LinearMap.infFixedSubmoduleEquivRestrict
      (typeASpecialLinearGraphAutomorphism r A).toLinearEquiv.toLinearMap
      (offDiagonalGraphLinearMap_mem r A)).trans
      (LinearEquiv.ofEq _ _ (congrArg LinearMap.fixedSubmodule
        (offDiagonalGraphEquiv_toLinearMap r A).symm)))

private theorem offDiagonalFixedRestrictEquiv_symm_apply
    (X : (typeAOffDiagonalGraphEquiv r A).toLinearMap.fixedSubmodule) :
    ((offDiagonalFixedRestrictEquiv r A).symm X).val = X.val.val := by
  simp [offDiagonalFixedRestrictEquiv]

private theorem offDiagonalCycle_action (c : TypeAOffDiagonalCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c + 1)) :
    (typeAOffDiagonalGraphEquiv r A).toLinearMap
      (specialLinearOffDiagonalBasis (Fin (r + 1)) A
        (typeAOffDiagonalCycleEquiv r ⟨c, i⟩)) =
      (typeAOffDiagonalCycleSign r c i : A) •
        specialLinearOffDiagonalBasis (Fin (r + 1)) A
          (typeAOffDiagonalCycleEquiv r
            ⟨c, finRotate (typeAOffDiagonalCyclePredLength r c + 1) i⟩) := by
  rw [LinearEquiv.coe_coe, typeAOffDiagonalGraphEquiv_basis,
    typeAOffDiagonalCycleEquiv_rotate, typeAOffDiagonalCycleSign_eq]
  congr 2
  rw [typeAOffDiagonalCycleEquiv_apply]
  split_ifs <;> simp

/-- The native fixed submodule is classified by scalar and `2`-torsion cycle coordinates. -/
noncomputable def typeASpecialLinearFixedOffDiagonalEquiv :
    typeASpecialLinearFixedOffDiagonal r A ≃ₗ[A]
      (TypeAOffDiagonalPositiveCycle r → A) ×
        (TypeAOffDiagonalNegativeCycle r → Submodule.torsionBy A A 2) := by
  classical
  exact (offDiagonalFixedRestrictEquiv r A).trans
    ((specialLinearOffDiagonalBasis (Fin (r + 1)) A).fixedEquivSignedFamily
      (typeAOffDiagonalCycleEquiv r) (typeAOffDiagonalCycleSign r)
      (typeAOffDiagonalCycleSign_eq_one_or_neg_one r)
      (typeAOffDiagonalGraphEquiv r A).toLinearMap (offDiagonalCycle_action r A))

/-- A positive coordinate is the matrix entry at its canonical representative. -/
@[simp]
theorem typeASpecialLinearFixedOffDiagonalEquiv_apply_pos
    (X : typeASpecialLinearFixedOffDiagonal r A) (c : TypeAOffDiagonalPositiveCycle r) :
    (typeASpecialLinearFixedOffDiagonalEquiv r A X).1 c =
      X.val.val c.val.val.val.1 c.val.val.val.2 := by
  simp [typeASpecialLinearFixedOffDiagonalEquiv, offDiagonalFixedRestrictEquiv,
    specialLinearOffDiagonalBasis_repr, typeAOffDiagonalCycleEquiv_apply]

/-- A negative coordinate retains the actual matrix entry as a `2`-torsion scalar. -/
@[simp]
theorem typeASpecialLinearFixedOffDiagonalEquiv_apply_neg
    (X : typeASpecialLinearFixedOffDiagonal r A) (c : TypeAOffDiagonalNegativeCycle r) :
    ((typeASpecialLinearFixedOffDiagonalEquiv r A X).2 c : A) =
      X.val.val c.val.val.val.1 c.val.val.val.2 := by
  simp [typeASpecialLinearFixedOffDiagonalEquiv, offDiagonalFixedRestrictEquiv,
    specialLinearOffDiagonalBasis_repr, typeAOffDiagonalCycleEquiv_apply]

/-- Reconstruction on a positive cycle uses the signed prefix of its scalar coordinate. -/
@[simp]
theorem typeASpecialLinearFixedOffDiagonalEquiv_symm_apply_pos
    (t : (TypeAOffDiagonalPositiveCycle r → A) ×
      (TypeAOffDiagonalNegativeCycle r → Submodule.torsionBy A A 2))
    (c : TypeAOffDiagonalPositiveCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c.val + 1)) :
    let p := typeAOffDiagonalCycleEquiv r ⟨c.val, i⟩
    ((typeASpecialLinearFixedOffDiagonalEquiv r A).symm t).val.val p.val.1 p.val.2 =
      Fin.partialProd (Fin.init (fun k ↦ (typeAOffDiagonalCycleSign r c.val k : A))) i *
        t.1 c := by
  simpa only [typeASpecialLinearFixedOffDiagonalEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, offDiagonalFixedRestrictEquiv_symm_apply,
    specialLinearOffDiagonalBasis_repr] using
    (specialLinearOffDiagonalBasis (Fin (r + 1)) A).fixedEquivSignedFamily_symm_repr_pos
      (typeAOffDiagonalCycleEquiv r) (typeAOffDiagonalCycleSign r)
      (typeAOffDiagonalCycleSign_eq_one_or_neg_one r)
      (typeAOffDiagonalGraphEquiv r A).toLinearMap (offDiagonalCycle_action r A) t c i

/-- Reconstruction on a negative cycle keeps the full `2`-torsion coordinate. -/
@[simp]
theorem typeASpecialLinearFixedOffDiagonalEquiv_symm_apply_neg
    (t : (TypeAOffDiagonalPositiveCycle r → A) ×
      (TypeAOffDiagonalNegativeCycle r → Submodule.torsionBy A A 2))
    (c : TypeAOffDiagonalNegativeCycle r)
    (i : Fin (typeAOffDiagonalCyclePredLength r c.val + 1)) :
    let p := typeAOffDiagonalCycleEquiv r ⟨c.val, i⟩
    ((typeASpecialLinearFixedOffDiagonalEquiv r A).symm t).val.val p.val.1 p.val.2 =
      Fin.partialProd (Fin.init (fun k ↦ (typeAOffDiagonalCycleSign r c.val k : A))) i *
        (t.2 c).val := by
  simpa only [typeASpecialLinearFixedOffDiagonalEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, offDiagonalFixedRestrictEquiv_symm_apply,
    specialLinearOffDiagonalBasis_repr] using
    (specialLinearOffDiagonalBasis (Fin (r + 1)) A).fixedEquivSignedFamily_symm_repr_neg
      (typeAOffDiagonalCycleEquiv r) (typeAOffDiagonalCycleSign r)
      (typeAOffDiagonalCycleSign_eq_one_or_neg_one r)
      (typeAOffDiagonalGraphEquiv r A).toLinearMap (offDiagonalCycle_action r A) t c i

/-- The inverse is an explicit sum of native matrix units with signed prefix coefficients. -/
theorem typeASpecialLinearFixedOffDiagonalEquiv_symm_apply
    (t : (TypeAOffDiagonalPositiveCycle r → A) ×
      (TypeAOffDiagonalNegativeCycle r → Submodule.torsionBy A A 2)) :
    ((typeASpecialLinearFixedOffDiagonalEquiv r A).symm t).val =
      (∑ c : TypeAOffDiagonalPositiveCycle r, ∑ i,
        (Fin.partialProd (Fin.init (fun k ↦ (typeAOffDiagonalCycleSign r c.val k : A))) i *
          t.1 c) •
        let p := typeAOffDiagonalCycleEquiv r ⟨c.val, i⟩
        single p.val.1 p.val.2 p.property (1 : A)) +
      ∑ c : TypeAOffDiagonalNegativeCycle r, ∑ i,
        (Fin.partialProd (Fin.init (fun k ↦ (typeAOffDiagonalCycleSign r c.val k : A))) i *
          (t.2 c).val) •
        let p := typeAOffDiagonalCycleEquiv r ⟨c.val, i⟩
        single p.val.1 p.val.2 p.property (1 : A) := by
  classical
  have h := (specialLinearOffDiagonalBasis (Fin (r + 1)) A).fixedEquivSignedFamily_symm_apply
    (typeAOffDiagonalCycleEquiv r) (typeAOffDiagonalCycleSign r)
    (typeAOffDiagonalCycleSign_eq_one_or_neg_one r)
    (typeAOffDiagonalGraphEquiv r A).toLinearMap (offDiagonalCycle_action r A) t
  simpa only [typeASpecialLinearFixedOffDiagonalEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, offDiagonalFixedRestrictEquiv_symm_apply,
    Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
    specialLinearOffDiagonalBasis_apply] using congrArg Subtype.val h

/-- Positive cycles give an integral basis of the native fixed off-diagonal submodule. -/
noncomputable def typeASpecialLinearFixedOffDiagonalBasis :
    Module.Basis (TypeAOffDiagonalPositiveCycle r) ℤ
      (typeASpecialLinearFixedOffDiagonal r ℤ) :=
  ((specialLinearOffDiagonalBasis (Fin (r + 1)) ℤ).fixedBasisSignedFamily
    (typeAOffDiagonalCycleEquiv r) (typeAOffDiagonalCycleSign r)
    (typeAOffDiagonalCycleSign_eq_one_or_neg_one r)
    (typeAOffDiagonalGraphEquiv r ℤ).toLinearMap (offDiagonalCycle_action r ℤ)).map
      (offDiagonalFixedRestrictEquiv r ℤ).symm

/-- Integral basis coordinates read the matrix entry at the positive-cycle representative. -/
@[simp]
theorem typeASpecialLinearFixedOffDiagonalBasis_repr
    (X : typeASpecialLinearFixedOffDiagonal r ℤ) (c : TypeAOffDiagonalPositiveCycle r) :
    (typeASpecialLinearFixedOffDiagonalBasis r).repr X c =
      X.val.val c.val.val.val.1 c.val.val.val.2 := by
  simp [typeASpecialLinearFixedOffDiagonalBasis, offDiagonalFixedRestrictEquiv,
    typeAOffDiagonalCycleEquiv_apply]

/-- Each integral fixed basis vector is the signed native matrix-unit sum along its cycle. -/
theorem typeASpecialLinearFixedOffDiagonalBasis_apply (c : TypeAOffDiagonalPositiveCycle r) :
    (typeASpecialLinearFixedOffDiagonalBasis r c).val =
      ∑ i, Fin.partialProd (Fin.init (typeAOffDiagonalCycleSign r c.val)) i •
        let p := typeAOffDiagonalCycleEquiv r ⟨c.val, i⟩
        single p.val.1 p.val.2 p.property (1 : ℤ) := by
  classical
  have h := (specialLinearOffDiagonalBasis (Fin (r + 1)) ℤ).fixedBasisSignedFamily_apply
    (typeAOffDiagonalCycleEquiv r) (typeAOffDiagonalCycleSign r)
    (typeAOffDiagonalCycleSign_eq_one_or_neg_one r)
    (typeAOffDiagonalGraphEquiv r ℤ).toLinearMap (offDiagonalCycle_action r ℤ) c
  simpa only [typeASpecialLinearFixedOffDiagonalBasis, Module.Basis.map_apply,
    offDiagonalFixedRestrictEquiv_symm_apply, Submodule.coe_sum, Submodule.coe_smul,
    specialLinearOffDiagonalBasis_apply] using congrArg Subtype.val h

/-- Integral fixed matrices vanish on the negative-cycle representatives. -/
theorem typeASpecialLinearFixedOffDiagonal_entry_neg
    (X : typeASpecialLinearFixedOffDiagonal r ℤ) (c : TypeAOffDiagonalNegativeCycle r) :
    X.val.val c.val.val.val.1 c.val.val.val.2 = 0 := by
  have h := (specialLinearOffDiagonalBasis (Fin (r + 1)) ℤ).fixedSignedFamily_repr_neg
    (typeAOffDiagonalCycleEquiv r) (typeAOffDiagonalCycleSign r)
    (typeAOffDiagonalCycleSign_eq_one_or_neg_one r)
    (typeAOffDiagonalGraphEquiv r ℤ).toLinearMap (offDiagonalCycle_action r ℤ)
    (offDiagonalFixedRestrictEquiv r ℤ X) c
  simpa [typeAOffDiagonalCycleEquiv_apply, offDiagonalFixedRestrictEquiv] using h

end TauCeti
