/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.AlgebraicGeometry.Frobenius.FiniteField
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Finite-field Frobenius comparison checks

Base change of the identity on `Spec 𝔽₂` is identity over every new base, and the
relative Frobenius comparison recovers that map. In contrast, absolute squaring on
`Spec 𝔽₄` is not identity, even though its underlying space has only one point.
These checks distinguish scalar-preserving base change from absolute Frobenius.
-/

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

-- This permits arbitrary new bases, including nonperfect and nonreduced schemes.
example {T : Scheme} (g : T ⟶ Spec (CommRingCat.of (ZMod 2))) :
    (pullback.snd (𝟙 _) g).iterateRelativeFrobenius 2
        (natCast_eq_zero_of_hom g (natCast_spec_eq_zero (CommRingCat.of (ZMod 2)))) 1 ≫
      ((𝟙 _ : Spec (CommRingCat.of (ZMod 2)) ⟶ _).qPowerFrobeniusTwistBaseChangeIso
        2 1 (by simp) g).hom = 𝟙 _ := by
  rw [← Hom.qPowerFrobenius_baseChange]
  have h : qPowerFrobenius (ZMod 2) (𝟙 _) 1 (by simp) = 𝟙 _ := by
    simpa only [qPowerFrobenius_eq_iterated] using
      iterateFrobenius_spec_eq_id (ZMod 2) 1 (by simp)
  apply pullback.hom_ext <;> simp [h]

-- The extension-field scalar action of absolute Frobenius is nontrivial.
example : (Spec (CommRingCat.of (GaloisField 2 2))).frobenius 2
    (natCast_spec_eq_zero (CommRingCat.of (GaloisField 2 2))) ≠ 𝟙 _ := by
  intro h
  have hx (x : GaloisField 2 2) : x ^ 2 = x := by
    apply (ConcreteCategory.bijective_of_isIso
      (ΓSpecIso (CommRingCat.of (GaloisField 2 2))).inv).injective
    have he := congrArg (fun f ↦ f.appTop
      ((ΓSpecIso (CommRingCat.of (GaloisField 2 2))).inv x)) h
    simpa using he
  have he : FiniteField.frobeniusAlgHom (ZMod 2) (GaloisField 2 2) = 1 := by
    ext x
    simpa using hx x
  have ho := FiniteField.orderOf_frobeniusAlgHom (ZMod 2) (GaloisField 2 2)
  rw [he, orderOf_one, GaloisField.finrank 2 (by decide : 2 ≠ 0)] at ho
  norm_num at ho
