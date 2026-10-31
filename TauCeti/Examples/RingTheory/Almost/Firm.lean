/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Firm

/-!
# Examples of firm modules

These examples test the action map `m~ ⊗[V] M → M`, the equivalence `m~ ⊗[V] m ≃ m~`, firm modules
and the functor `M ↦ m~ ⊗[V] M`:

* over the classical setup `(ℤ, ℤ)` the action map and the equivalence are computed on explicit
  tensors, fixing the scalar conventions, and both vanish for the zero setup;
* `m~` and every module are firm for the classical setup, `m~` is firm for every setup, `ℤ` is not
  firm for the zero setup of `ℤ`, and a firm almost zero module is zero;
* the functor `firm` kills `V ⧸ m` for every setup and every module for the zero setup, but not
  `ℤ` for the classical setup.

## References

* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Construction 4.1.5.
-/

open CategoryTheory Limits TensorProduct TauCeti.Almost TauCeti.Almost.BasicSetup

variable {V : Type*} [CommRing V]

/-! ### The action map and the equivalence `m~ ⊗[V] m ≃ m~` -/

-- Over `(ℤ, ℤ)`, `(2 ⊗ 3) ⊗ 5 + (7 ⊗ 11) ⊗ 13 ↦ 2 * 3 * 5 + 7 * 11 * 13 = 1031`.
example : (classical ℤ).tildeAct ℤ
    (((⟨2, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨3, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ (5 : ℤ) +
      ((⟨7, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨11, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ
        (13 : ℤ)) = 1031 := by
  simp only [map_add, tildeAct_tmul, tildeMul_tmul, smul_eq_mul]
  norm_num

example : (classical V).tildeAct V
    (((⟨1, by simp⟩ : (classical V).ideal) ⊗ₜ (⟨1, by simp⟩ : (classical V).ideal)) ⊗ₜ (1 : V)) =
      1 := by
  simp

-- For the zero setup, `m~ = 0`, so the action map is zero.
example (M : Type*) [AddCommGroup M] [Module V M] : (zero V).tildeAct M = 0 := by
  have : Subsingleton ((zero V).tilde ⊗[V] M) :=
    ((zero V).isAlmostZero_iff_subsingleton_tilde_tensor M).mp isAlmostZero_zero
  exact Subsingleton.elim _ _

-- Classically, `(1 ⊗ 1) ⊗ 1 ↦ 1 ⊗ 1`.
example : (classical V).tildeTensorIdealEquiv
    (((⟨1, by simp⟩ : (classical V).ideal) ⊗ₜ (⟨1, by simp⟩ : (classical V).ideal)) ⊗ₜ
      (⟨1, by simp⟩ : (classical V).ideal)) =
      (⟨1, by simp⟩ : (classical V).ideal) ⊗ₜ (⟨1, by simp⟩ : (classical V).ideal) := by
  simp

-- Over `(ℤ, ℤ)`, followed by multiplication, `(2 ⊗ 3) ⊗ 5 + (7 ⊗ 11) ⊗ 13 ↦ 1031`.
example : (classical ℤ).tildeMul ((classical ℤ).tildeTensorIdealEquiv
    (((⟨2, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨3, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ
        (⟨5, by simp⟩ : (classical ℤ).ideal) +
      ((⟨7, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨11, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ
        (⟨13, by simp⟩ : (classical ℤ).ideal))) = 1031 := by
  simp only [map_add, tildeTensorIdealEquiv_tmul, map_smul, tildeMul_tmul, smul_eq_mul]
  norm_num

-- For the zero setup, the equivalence is between zero modules.
example : Subsingleton ((zero V).tilde ⊗[V] (zero V).ideal) :=
  inferInstance

-- The factors of `m~` commute.
example (S : BasicSetup V) (x y : S.ideal) : (x ⊗ₜ[V] y : S.tilde) = y ⊗ₜ x :=
  S.tmul_comm x y

/-! ### Firm modules -/

example (S : BasicSetup V) : S.IsFirm S.tilde :=
  S.isFirm_tilde

example (M : Type*) [AddCommGroup M] [Module V M] : (classical V).IsFirm M :=
  isFirm_classical M

-- `ℤ` is not firm for the zero setup of `ℤ`: the image of its action map is `0`.
example : ¬ (zero ℤ).IsFirm ℤ := by
  rw [isFirm_self_iff, zero_ideal]
  exact bot_ne_top

-- For the zero setup, firm means zero.
example : (zero V).IsFirm Unit :=
  (isFirm_zero_iff Unit).mpr inferInstance

-- A firm module killed by `m` is zero; `V ⧸ m` is almost zero, so it is firm only if it is zero.
example (S : BasicSetup V) (h : S.IsFirm (V ⧸ S.ideal)) : Subsingleton (V ⧸ S.ideal) :=
  h.subsingleton_of_isAlmostZero S.isAlmostZero_quotient

/-! ### The functor `firm` -/

-- `firm` kills `V ⧸ m`.
example (S : BasicSetup V) : IsZero (S.firm.obj (ModuleCat.of V (V ⧸ S.ideal))) :=
  (S.isZero_firm_obj_iff (ModuleCat.of V (V ⧸ S.ideal))).mpr S.isAlmostZero_quotient

-- For the zero setup, `firm` sends every module to zero.
example (M : ModuleCat.{0} ℤ) : IsZero ((zero ℤ).firm.obj M) :=
  ((zero ℤ).isZero_firm_obj_iff M).mpr isAlmostZero_zero

-- For the classical setup, `firm` does not kill `ℤ`.
example : ¬ IsZero ((classical ℤ).firm.obj (ModuleCat.of ℤ ℤ)) := by
  rw [isZero_firm_obj_iff, isAlmostZero_classical_iff]
  intro h
  exact zero_ne_one (Subsingleton.elim (0 : ℤ) 1)
