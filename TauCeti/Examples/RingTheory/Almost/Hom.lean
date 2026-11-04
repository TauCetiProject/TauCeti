/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.Almost.Hom

/-!
# Examples of linear representatives of almost morphisms

The almost-Hom formula recovers the classical action map on explicit tensors, but does not
recover the ordinary identity of an almost zero residue module. For the zero setup its source
and every representative vanish.
-/

open CategoryTheory Limits TensorProduct TauCeti.Almost TauCeti.Almost.BasicSetup
  TauCeti.Almost.Module

universe u

variable {V : Type u} [CommRing V]

-- The identity is represented by the multiplication action `(x ⊗ y) ⊗ z ↦ x * y * z`.
example : homLinearEquiv (classical ℤ) (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) (𝟙 _)
    (((⟨2, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨3, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ (5 : ℤ) +
      ((⟨7, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨11, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ
        (13 : ℤ)) = 1031 := by
  rw [homLinearEquiv_id]
  simp only [map_add, tildeAct_tmul, tildeMul_tmul, smul_eq_mul]
  norm_num

-- With `m = 0`, the source of the representative is zero, not an ordinary copy of `M`.
example (M N : ModuleCat.{u} V)
    (f : (toAlmost (zero V)).obj M ⟶ (toAlmost (zero V)).obj N) :
    Subsingleton ((zero V).tilde ⊗[V] M) ∧ homLinearEquiv (zero V) M N f = 0 := by
  have : Subsingleton ((zero V).tilde ⊗[V] M) :=
    ((zero V).isAlmostZero_iff_subsingleton_tilde_tensor M).mp isAlmostZero_zero
  exact ⟨inferInstance, Subsingleton.elim _ _⟩

-- Ordinary residue identities can be nonzero even though their almost representatives vanish.
example (S : BasicSetup V) (hS : S.ideal ≠ ⊤) :
    (𝟙 (ModuleCat.of V (V ⧸ S.ideal))) ≠ 0 ∧
      homLinearEquiv S (ModuleCat.of V (V ⧸ S.ideal)) (ModuleCat.of V (V ⧸ S.ideal))
        (𝟙 _) = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun f : ModuleCat.of V (V ⧸ S.ideal) ⟶ ModuleCat.of V (V ⧸ S.ideal) =>
      f.hom (Ideal.Quotient.mk S.ideal 1)) h
    have : (1 : V) ∈ S.ideal := Ideal.Quotient.eq_zero_iff_mem.mp h1
    exact hS ((Ideal.eq_top_iff_one S.ideal).mpr this)
  · have h := (isZero_toAlmost_obj_iff S (ModuleCat.of V (V ⧸ S.ideal))).mpr
      S.isAlmostZero_quotient
    rw [h.eq_of_src (𝟙 _) 0, map_zero]

-- The inverse comparison recovers the doubled classical identity, not its negative or zero.
example : (homLinearEquiv (classical ℤ) (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ)).symm
    ((2 : ℤ) • (classical ℤ).tildeAct ℤ) ≠ 0 := by
  intro h
  have h' := congrArg (homLinearEquiv (classical ℤ) (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ)) h
  simp only [LinearEquiv.apply_symm_apply, map_zero] at h'
  have h1 := LinearMap.congr_fun h'
    (((⟨1, by simp⟩ : (classical ℤ).ideal) ⊗ₜ (⟨1, by simp⟩ : (classical ℤ).ideal)) ⊗ₜ (1 : ℤ))
  norm_num at h1
