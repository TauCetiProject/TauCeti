/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Quaternion.Fueter
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Reflection and real affine changes of Fueter regular functions

Quaternionic conjugation in both the argument and the value exchanges the left and right
Fueter equations. The reflected function is written `fun q ↦ star (f (star q))`, without
introducing a separate function carrier. The pointwise equivalences also give the exact
change of domain `star '' s`, needed to transfer ordered integral formulas between sides.

Translations and real dilations of the argument preserve each side of regularity. We state
these together as precomposition by `q ↦ p + r • q`, allowing also the constant map `r = 0`.
Only pointwise real differentiability is used throughout.

## References

* I. Frenkel and M. Libine, *Quaternionic analysis, representation theory and physics*,
  Adv. Math. 218 (2008), arXiv:0711.2699v5, §2.2, Definition 1 and Proposition 2.
-/

public section

open Quaternion
open scoped Pointwise

namespace TauCeti

variable {f : ℍ → ℍ} {q : ℍ} {s : Set ℍ}

/-- Conjugating both the input and output of a real-linear map exchanges its ordered Fueter
operators, and conjugates the result. -/
theorem fueterLeft_eq_star_fueterRight {D D' : ℍ →L[ℝ] ℍ}
    (hD : ∀ h, D' h = star (D (star h))) :
    fueterLeft D' = star (fueterRight D) := by
  rw [fueterLeft_apply, fueterRight_apply]
  simp only [hD, star_one, star_add, star_mul]
  have hi : star (⟨0, 1, 0, 0⟩ : ℍ) = -(⟨0, 1, 0, 0⟩ : ℍ) := by ext <;> simp
  have hj : star (⟨0, 0, 1, 0⟩ : ℍ) = -(⟨0, 0, 1, 0⟩ : ℍ) := by ext <;> simp
  have hk : star (⟨0, 0, 0, 1⟩ : ℍ) = -(⟨0, 0, 0, 1⟩ : ℍ) := by ext <;> simp
  simp only [hi, hj, hk, map_neg, star_neg, mul_neg, neg_mul]

/-- The right operator of the conjugated real-linear map is the conjugate of the left
operator of the original map. -/
theorem fueterRight_eq_star_fueterLeft {D D' : ℍ →L[ℝ] ℍ}
    (hD : ∀ h, D' h = star (D (star h))) :
    fueterRight D' = star (fueterLeft D) := by
  have h := fueterLeft_eq_star_fueterRight (D := D') (D' := D) (fun h ↦ by simp [hD])
  simpa using (congrArg star h).symm

/-- Reflecting a right Fueter regular function in both argument and value gives a left
Fueter regular function at the conjugate point. -/
theorem RightFueterAt.star_star (hf : RightFueterAt f q) :
    LeftFueterAt (fun x ↦ star (f (star x))) (star q) := by
  let : StarModule ℝ ℍ := ⟨fun r h ↦ by simp⟩
  have hd := hf.differentiableAt.hasFDerivAt.star_star
  apply hd.leftFueterAt_iff.mpr
  rw [fueterLeft_eq_star_fueterRight (D := fderiv ℝ f q) (fun h ↦ by simp),
    hf.fueterRight_fderiv, star_zero]

/-- Reflecting a left Fueter regular function exchanges it with right regularity. -/
theorem LeftFueterAt.star_star (hf : LeftFueterAt f q) :
    RightFueterAt (fun x ↦ star (f (star x))) (star q) := by
  let : StarModule ℝ ℍ := ⟨fun r h ↦ by simp⟩
  have hd := hf.differentiableAt.hasFDerivAt.star_star
  apply hd.rightFueterAt_iff.mpr
  rw [fueterRight_eq_star_fueterLeft (D := fderiv ℝ f q) (fun h ↦ by simp),
    hf.fueterLeft_fderiv, star_zero]

/-- Reflection exchanges pointwise left and right Fueter regularity, in both directions. -/
@[simp]
theorem leftFueterAt_star_star_iff :
    LeftFueterAt (fun x ↦ star (f (star x))) (star q) ↔ RightFueterAt f q := by
  constructor
  · intro hf
    simpa using hf.star_star
  · exact RightFueterAt.star_star

/-- The dual pointwise reflection equivalence. -/
@[simp]
theorem rightFueterAt_star_star_iff :
    RightFueterAt (fun x ↦ star (f (star x))) (star q) ↔ LeftFueterAt f q := by
  constructor
  · intro hf
    simpa using hf.star_star
  · exact LeftFueterAt.star_star

/-- A right regular function on `s` reflects to a left regular function on `star '' s`. -/
theorem RightFueterOn.star_star (hf : RightFueterOn f s) :
    LeftFueterOn (fun x ↦ star (f (star x))) (star '' s) := by
  rw [leftFueterOn_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact (rightFueterOn_iff.mp hf x hx).star_star

/-- A left regular function on `s` reflects to a right regular function on `star '' s`. -/
theorem LeftFueterOn.star_star (hf : LeftFueterOn f s) :
    RightFueterOn (fun x ↦ star (f (star x))) (star '' s) := by
  rw [rightFueterOn_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact (leftFueterOn_iff.mp hf x hx).star_star

/-- The exact reflected-domain correspondence for left regularity. -/
@[simp]
theorem leftFueterOn_star_star_iff :
    LeftFueterOn (fun x ↦ star (f (star x))) (star s) ↔ RightFueterOn f s := by
  rw [← Set.image_star]
  constructor
  · intro hf
    rw [rightFueterOn_iff]
    intro x hx
    exact leftFueterAt_star_star_iff.mp (leftFueterOn_iff.mp hf (star x) ⟨x, hx, rfl⟩)
  · exact RightFueterOn.star_star

/-- The exact reflected-domain correspondence for right regularity. -/
@[simp]
theorem rightFueterOn_star_star_iff :
    RightFueterOn (fun x ↦ star (f (star x))) (star s) ↔ LeftFueterOn f s := by
  rw [← Set.image_star]
  constructor
  · intro hf
    rw [leftFueterOn_iff]
    intro x hx
    exact rightFueterAt_star_star_iff.mp (rightFueterOn_iff.mp hf (star x) ⟨x, hx, rfl⟩)
  · exact LeftFueterOn.star_star

/-- Translation and real dilation of the argument preserve left Fueter regularity,
including zero dilation. -/
theorem LeftFueterAt.comp_const_add_smul {p : ℍ} {r : ℝ}
    (hf : LeftFueterAt f (p + r • q)) :
    LeftFueterAt (fun x ↦ f (p + r • x)) q := by
  let D := fderiv ℝ f (p + r • q)
  have hD : HasFDerivAt f D (p + r • q) := hf.differentiableAt.hasFDerivAt
  have hA : HasFDerivAt (fun x : ℍ ↦ p + r • x)
      (r • ContinuousLinearMap.id ℝ ℍ) q := by
    simpa only [smul_apply, ContinuousLinearMap.id_apply] using
      (r • ContinuousLinearMap.id ℝ ℍ).hasFDerivAt.const_add p
  have hd : HasFDerivAt (fun x ↦ f (p + r • x)) (r • D) q := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id] using hD.comp q hA
  apply hd.leftFueterAt_iff.mpr
  simp [D, hf.fueterLeft_fderiv]

/-- Translation and real dilation of the argument preserve right Fueter regularity,
including zero dilation. -/
theorem RightFueterAt.comp_const_add_smul {p : ℍ} {r : ℝ}
    (hf : RightFueterAt f (p + r • q)) :
    RightFueterAt (fun x ↦ f (p + r • x)) q := by
  let D := fderiv ℝ f (p + r • q)
  have hD : HasFDerivAt f D (p + r • q) := hf.differentiableAt.hasFDerivAt
  have hA : HasFDerivAt (fun x : ℍ ↦ p + r • x)
      (r • ContinuousLinearMap.id ℝ ℍ) q := by
    simpa only [smul_apply, ContinuousLinearMap.id_apply] using
      (r • ContinuousLinearMap.id ℝ ℍ).hasFDerivAt.const_add p
  have hd : HasFDerivAt (fun x ↦ f (p + r • x)) (r • D) q := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.comp_id] using hD.comp q hA
  apply hd.rightFueterAt_iff.mpr
  simp [D, hf.fueterRight_fderiv]

/-- The left-regular domain pulls back under a real affine change of argument. -/
theorem LeftFueterOn.comp_const_add_smul (hf : LeftFueterOn f s) (p : ℍ) (r : ℝ) :
    LeftFueterOn (fun x ↦ f (p + r • x)) ((fun x ↦ p + r • x) ⁻¹' s) := by
  rw [leftFueterOn_iff]
  intro q hq
  exact (leftFueterOn_iff.mp hf _ hq).comp_const_add_smul

/-- The right-regular domain pulls back under a real affine change of argument. -/
theorem RightFueterOn.comp_const_add_smul (hf : RightFueterOn f s) (p : ℍ) (r : ℝ) :
    RightFueterOn (fun x ↦ f (p + r • x)) ((fun x ↦ p + r • x) ⁻¹' s) := by
  rw [rightFueterOn_iff]
  intro q hq
  exact (rightFueterOn_iff.mp hf _ hq).comp_const_add_smul

end TauCeti
