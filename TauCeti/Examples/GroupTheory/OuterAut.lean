/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Automorphism.Outer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Outer automorphism groups of small groups

Checks for `TauCeti.OuterAut`, the automorphisms of a group modulo the inner automorphisms:

* the outer automorphism groups of the trivial group and of `S₃` are trivial: every automorphism
  of `S₃` is conjugation by an element (`S₃` has trivial centre, and an automorphism is determined
  by the images of a 3-cycle and a transposition, which leaves at most `2 · 3 = 6` automorphisms);
* `OuterAut ℤ` has exactly two elements, `±id`;
* `OuterAut ℤ² ≅ GL₂(ℤ)`: for the abelian `ℤ²` there are no nontrivial inner automorphisms, and
  the automorphisms of `ℤ²` are the invertible integer matrices.

The groups `ℤ` and `ℤ²` are written multiplicatively, as `Multiplicative ℤ` and
`Multiplicative (Fin 2 → ℤ)`.
-/

public section

namespace TauCeti.OuterAutExamples

open TauCeti

/-- The outer automorphism group of the trivial group is trivial. -/
instance subsingleton_outerAut_unit : Subsingleton (OuterAut Unit) :=
  Quotient.instSubsingletonQuotient _

/-- In `S₃`, the 3-cycle `finRotate 3` and the transposition `swap 0 1` generate. -/
theorem closure_finRotate_swap :
    Subgroup.closure ({finRotate 3, Equiv.swap 0 1} : Set (Equiv.Perm (Fin 3))) = ⊤ := by
  have := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 1))
    (support_finRotate (n := 1)) 0
  simpa using this

/-- An automorphism of `S₃` is determined by the images of `finRotate 3` and `swap 0 1`. -/
theorem injective_mulAut_perm_fin_three :
    Function.Injective fun φ : MulAut (Equiv.Perm (Fin 3)) ↦
      ((⟨φ (finRotate 3), by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · rw [← map_pow, show finRotate 3 ^ 3 = 1 by decide, map_one]
          · rw [Ne, map_eq_one_iff φ φ.injective]; decide⟩ :
          {x // x ∈ Finset.univ.filter fun x : Equiv.Perm (Fin 3) ↦ x ^ 3 = 1 ∧ x ≠ 1}),
        (⟨φ (Equiv.swap 0 1), by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · rw [← map_pow, show Equiv.swap (0 : Fin 3) 1 ^ 2 = 1 by decide, map_one]
          · rw [Ne, map_eq_one_iff φ φ.injective]; decide⟩ :
          {x // x ∈ Finset.univ.filter fun x : Equiv.Perm (Fin 3) ↦ x ^ 2 = 1 ∧ x ≠ 1})) := by
  intro φ ψ h
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
  have := MonoidHom.eq_of_eqOn_dense closure_finRotate_swap
    (f := φ.toMonoidHom) (g := ψ.toMonoidHom) (by
      rintro x (rfl | rfl)
      · exact h.1
      · exact h.2)
  exact MulEquiv.ext fun x ↦ DFunLike.congr_fun this x

/-- **Every automorphism of `S₃` is inner**, so `OuterAut S₃` is trivial. -/
instance subsingleton_outerAut_perm_fin_three : Subsingleton (OuterAut (Equiv.Perm (Fin 3))) := by
  have hconj : Function.Injective (MulAut.conj : Equiv.Perm (Fin 3) →* MulAut _) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : ∀ x, g * x = x * g := fun x ↦ by
      have := DFunLike.congr_fun hg x
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [this]
    have key : ∀ g : Equiv.Perm (Fin 3), (∀ x, g * x = x * g) → g = 1 := by decide
    exact key g hc
  have hcard : Nat.card (MulAut (Equiv.Perm (Fin 3))) ≤ Nat.card (Equiv.Perm (Fin 3)) := by
    refine (Nat.card_le_card_of_injective _ injective_mulAut_perm_fin_three).trans ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_coe, Fintype.card_coe]
    decide
  have hbij := hconj.bijective_of_nat_card_le hcard
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨φ, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨ψ, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨g, rfl⟩ := hbij.2 φ
  obtain ⟨h, rfl⟩ := hbij.2 ψ
  rw [OuterAut.mk_conj, OuterAut.mk_conj]

/-- The automorphisms of `M` written multiplicatively are its `ℤ`-linear automorphisms. -/
def mulAutMultiplicativeEquiv (M : Type*) [AddCommGroup M] :
    MulAut (Multiplicative M) ≃* (M ≃ₗ[ℤ] M) where
  toFun φ := (AddEquiv.toMultiplicative.symm φ).toIntLinearEquiv
  invFun f := AddEquiv.toMultiplicative f.toAddEquiv
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- **`OuterAut ℤ² ≅ GL₂(ℤ)`**: the outer automorphisms of the abelian group `ℤ²` are its
automorphisms, the invertible `2 × 2` integer matrices. -/
noncomputable def outerAutIntPairEquiv :
    OuterAut (Multiplicative (Fin 2 → ℤ)) ≃* Matrix.GeneralLinearGroup (Fin 2) ℤ :=
  OuterAut.mulEquivOfIsMulCommutative.trans <|
    (mulAutMultiplicativeEquiv _).trans <|
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ (Fin 2 → ℤ)).symm.trans
        Matrix.GeneralLinearGroup.toLin.symm

/-- The automorphisms of `ℤ` are the multiplications by units: `f ↦ f 1`. -/
def linearEquivIntEquivUnits : (ℤ ≃ₗ[ℤ] ℤ) ≃ ℤˣ where
  toFun f := ⟨f 1, f.symm 1, by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, f.apply_symm_apply], by
      rw [mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one, f.symm_apply_apply]⟩
  invFun u := LinearEquiv.smulOfUnit u
  left_inv f := by
    ext x
    change (f 1 : ℤ) • x = f x
    rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]
  right_inv u := by
    ext
    change (u : ℤ) • (1 : ℤ) = u
    rw [smul_eq_mul, mul_one]

/-- **`OuterAut ℤ` has exactly two elements**, the classes of `id` and of `-id`. -/
theorem card_outerAut_int : Nat.card (OuterAut (Multiplicative ℤ)) = 2 := by
  rw [Nat.card_congr (OuterAut.mulEquivOfIsMulCommutative.trans
      (mulAutMultiplicativeEquiv ℤ)).toEquiv,
    Nat.card_congr linearEquivIntEquivUnits, Nat.card_eq_fintype_card, Fintype.card_units_int]

end TauCeti.OuterAutExamples
