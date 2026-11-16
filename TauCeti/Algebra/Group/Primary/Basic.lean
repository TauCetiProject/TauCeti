/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Torsion

/-!
# Basic properties of primary components of additive commutative groups

This file records foundational properties of Mathlib's `AddCommGroup.primaryComponent A n`, the
subgroup of elements of an additive commutative group `A` annihilated by a power of `n`: every
`n`-primary component is an additive `n`-group, and taking `n`-primary components commutes with
binary products.

## Main definitions and statements

* `AddCommGroup.primaryComponentProdAddEquiv`: `(A × B)[n^∞] ≃+ A[n^∞] × B[n^∞]`.
* `AddCommGroup.primaryComponent.isAddPGroup`: `IsAddPGroup n (AddCommGroup.primaryComponent A n)`.
-/

public section

namespace AddCommGroup

/-- The `n`-primary component of a binary product of additive commutative groups splits as the
product of their `n`-primary components. -/
def primaryComponentProdAddEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    AddCommGroup.primaryComponent (A × B) n ≃+
      AddCommGroup.primaryComponent A n × AddCommGroup.primaryComponent B n where
  toFun x :=
    ⟨⟨x.1.1, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, congrArg Prod.fst hk⟩⟩,
     ⟨x.1.2, by
        obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp x.2
        exact AddCommGroup.mem_primaryComponent.mpr ⟨k, congrArg Prod.snd hk⟩⟩⟩
  invFun y :=
    ⟨(y.1.1, y.2.1), by
      obtain ⟨k₁, hk₁⟩ := AddCommGroup.mem_primaryComponent.mp y.1.2
      obtain ⟨k₂, hk₂⟩ := AddCommGroup.mem_primaryComponent.mp y.2.2
      refine AddCommGroup.mem_primaryComponent.mpr ⟨k₁ + k₂, ?_⟩
      rw [Prod.smul_mk, Prod.mk_eq_zero]
      exact ⟨by rw [add_comm, pow_add, ← smul_smul, hk₁, nsmul_zero],
        by rw [pow_add, ← smul_smul, hk₂, nsmul_zero]⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem primaryComponentProdAddEquiv_apply_fst (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (x : AddCommGroup.primaryComponent (A × B) n) :
    ((primaryComponentProdAddEquiv A B n x).1 : A) = x.1.1 := by
  rfl

@[simp]
theorem primaryComponentProdAddEquiv_apply_snd (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (x : AddCommGroup.primaryComponent (A × B) n) :
    ((primaryComponentProdAddEquiv A B n x).2 : B) = x.1.2 := by
  rfl

@[simp]
theorem coe_primaryComponentProdAddEquiv_symm_apply (A B : Type*) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (x : AddCommGroup.primaryComponent A n) (y : AddCommGroup.primaryComponent B n) :
    ((primaryComponentProdAddEquiv A B n).symm (x, y) : A × B) = (x.1, y.1) := by
  rfl

/-- Every element of `AddCommGroup.primaryComponent A n` is annihilated by a power of `n`. -/
theorem primaryComponent.isAddPGroup (A : Type*) [AddCommGroup A] (n : ℕ) :
    IsAddPGroup n (AddCommGroup.primaryComponent A n) := by
  intro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.mp hx
  exact ⟨k, Subtype.ext hk⟩

end AddCommGroup
