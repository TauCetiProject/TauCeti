/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Proper
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Change
public import TauCeti.NumberTheory.NumberField.Global.Orders.Quadratic.NarrowPic
public import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RingTheory.Norm.Basic
import Mathlib.Tactic.Ring

/-!
# Oriented form ideals and narrow classes

The primitive form ideal is corrected by `√D` when its leading coefficient is negative.
For positive nonsquare discriminants, this correction makes proper changes of variables
scale the ideal by a positive-norm element. The resulting class in the existing narrow
Picard group is therefore invariant under the left special-linear action.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7 and the narrow analogue.
-/

public section
noncomputable section

open QuadraticAlgebra FractionalIdeal
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

variable (f : BinaryQuadraticForm ℤ) (D : ℤ) [Fact (¬ IsSquare D)]

-- The nonsquare hypothesis supplies the field structure used by Units.mk0.
/-- The orientation correction: one for positive leading coefficient, and `√D` otherwise.
For nonsquare discriminant the leading coefficient cannot vanish. -/
def idealSignFactor : (QuadraticAlgebra ℚ (D : ℚ) 0)ˣ :=
  if 0 < f.a then 1 else Units.mk0 omega (by
    intro h
    have hi := congrArg QuadraticAlgebra.im h
    simp at hi)

/-- A positive leading coefficient has trivial orientation correction. -/
@[simp] theorem idealSignFactor_of_a_pos (ha : 0 < f.a) : f.idealSignFactor D = 1 := by
  simp only [idealSignFactor, ite_eq_left ha]

/-- A nonpositive leading coefficient has square-root orientation correction. -/
@[simp] theorem coe_idealSignFactor_of_not_a_pos (ha : ¬ 0 < f.a) :
    (f.idealSignFactor D : QuadraticAlgebra ℚ (D : ℚ) 0) = omega := by
  simp only [idealSignFactor, ite_eq_right ha, Units.val_mk0]

/-- The norm of the orientation correction is one or `-D`, according to the leading sign. -/
theorem norm_idealSignFactor :
    Algebra.norm ℚ (f.idealSignFactor D : QuadraticAlgebra ℚ (D : ℚ) 0) =
      if 0 < f.a then 1 else -(D : ℚ) := by
  by_cases ha : 0 < f.a
  · rw [idealSignFactor_of_a_pos f D ha]
    simp [ha]
  · rw [coe_idealSignFactor_of_not_a_pos f D ha]
    simp [ha, Algebra.norm_quadraticAlgebra_apply, QuadraticAlgebra.norm_def]

/-- The sign-corrected primitive ideal in the supplier's invertible ideal group. -/
def orientedInvertibleFractionalIdeal (hf : f.discrim = D) (hprim : f.IsPrimitive) :
    (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)).invertibleProperFractionalIdeals :=
  toPrincipalIdeal _ _ (f.idealSignFactor D) * f.invertibleFractionalIdeal D hf hprim

/-- The corrected ideal is the original invertible ideal multiplied by its sign factor. -/
theorem orientedInvertibleFractionalIdeal_def (hf : f.discrim = D) (hprim : f.IsPrimitive) :
    f.orientedInvertibleFractionalIdeal D hf hprim =
      toPrincipalIdeal _ _ (f.idealSignFactor D) * f.invertibleFractionalIdeal D hf hprim := by
  rfl

/-- Positive-leading representatives use the original primitive form ideal. -/
theorem orientedInvertibleFractionalIdeal_of_a_pos (hf : f.discrim = D)
    (hprim : f.IsPrimitive) (ha : 0 < f.a) :
    f.orientedInvertibleFractionalIdeal D hf hprim = f.invertibleFractionalIdeal D hf hprim := by
  rw [orientedInvertibleFractionalIdeal_def, idealSignFactor_of_a_pos f D ha,
    map_one, one_mul]

/-- Negative-leading representatives use the original ideal scaled by `√D`. -/
theorem coe_orientedInvertibleFractionalIdeal_of_a_neg (hf : f.discrim = D)
    (hprim : f.IsPrimitive) (ha : f.a < 0) :
    (f.orientedInvertibleFractionalIdeal D hf hprim).val =
      spanSingleton _ (omega : QuadraticAlgebra ℚ (D : ℚ) 0) * f.fractionalIdeal D hf := by
  rw [orientedInvertibleFractionalIdeal_def, Units.val_mul, coe_toPrincipalIdeal,
    coe_invertibleFractionalIdeal,
    coe_idealSignFactor_of_not_a_pos f D (not_lt_of_ge ha.le)]

/-- The sign-corrected ideal-scaling factor for a proper change of variables. -/
def orientedIdealChangeFactor (hf : f.discrim = D) (γ : SL(2, ℤ)) :
    (QuadraticAlgebra ℚ (D : ℚ) 0)ˣ :=
  (γ • f).idealSignFactor D *
    Units.mk0 (f.idealChangeFactor D γ) (idealChangeFactor_ne_zero f D
      (a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out)) γ) *
      (f.idealSignFactor D)⁻¹

/-- The corrected change factor is the old factor conjugated by the sign corrections. -/
theorem coe_orientedIdealChangeFactor (hf : f.discrim = D) (γ : SL(2, ℤ)) :
    (f.orientedIdealChangeFactor D hf γ : QuadraticAlgebra ℚ (D : ℚ) 0) =
      ((γ • f).idealSignFactor D : QuadraticAlgebra ℚ (D : ℚ) 0) *
        f.idealChangeFactor D γ *
          (f.idealSignFactor D : QuadraticAlgebra ℚ (D : ℚ) 0)⁻¹ := by
  simp only [orientedIdealChangeFactor, Units.val_mul, Units.val_mk0,
    Units.val_inv_eq_inv_val]

private theorem norm_idealSignFactor_mul_a_pos (hD : 0 < D) (ha : f.a ≠ 0) :
    0 < Algebra.norm ℚ (f.idealSignFactor D : QuadraticAlgebra ℚ (D : ℚ) 0) * (f.a : ℚ) := by
  rw [norm_idealSignFactor]
  have hDQ : 0 < (D : ℚ) := by exact_mod_cast hD
  by_cases h : 0 < f.a
  · have hQ : 0 < (f.a : ℚ) := by exact_mod_cast h
    simp only [ite_eq_left h, one_mul]
    exact hQ
  · have hQ : (f.a : ℚ) < 0 := by exact_mod_cast (show f.a < 0 by omega)
    simp only [ite_eq_right h]
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hDQ) hQ

/-- The corrected scaling factor has positive norm for positive nonsquare discriminant. -/
theorem norm_orientedIdealChangeFactor_pos (hf : f.discrim = D) (hD : 0 < D)
    (γ : SL(2, ℤ)) :
    0 < Algebra.norm ℚ (f.orientedIdealChangeFactor D hf γ : QuadraticAlgebra ℚ (D : ℚ) 0) := by
  have ha : f.a ≠ 0 := a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out)
  have hga : (γ • f).a ≠ 0 := a_ne_zero_of_not_isSquare_discrim
    ((discrim_smul γ f).trans hf ▸ Fact.out)
  have hchange : Algebra.norm ℚ (f.idealChangeFactor D γ) =
      ((γ • f).a : ℚ) / (f.a : ℚ) := by
    rw [Algebra.norm_quadraticAlgebra_apply]
    exact norm_idealChangeFactor f D hf γ
  have hnorm : Algebra.norm ℚ
      (f.orientedIdealChangeFactor D hf γ : QuadraticAlgebra ℚ (D : ℚ) 0) =
      (Algebra.norm ℚ ((γ • f).idealSignFactor D : QuadraticAlgebra ℚ (D : ℚ) 0) *
        ((γ • f).a : ℚ)) /
      (Algebra.norm ℚ (f.idealSignFactor D : QuadraticAlgebra ℚ (D : ℚ) 0) * (f.a : ℚ)) := by
    simp only [coe_orientedIdealChangeFactor, map_mul, Algebra.norm_inv, hchange,
      div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hnorm]
  exact div_pos (norm_idealSignFactor_mul_a_pos (γ • f) D hD hga)
    (norm_idealSignFactor_mul_a_pos f D hD ha)

/-- Sign-corrected ideals differ by the corrected principal factor. -/
theorem orientedInvertibleFractionalIdeal_smul (hf : f.discrim = D) (hprim : f.IsPrimitive)
    (γ : SL(2, ℤ)) :
    (γ • f).orientedInvertibleFractionalIdeal D ((discrim_smul γ f).trans hf)
      ((isPrimitive_smul_iff f γ).mpr hprim) =
      toPrincipalIdeal _ _ (f.orientedIdealChangeFactor D hf γ) *
        f.orientedInvertibleFractionalIdeal D hf hprim := by
  have hfactor : f.orientedIdealChangeFactor D hf γ * f.idealSignFactor D =
      (γ • f).idealSignFactor D * Units.mk0 (f.idealChangeFactor D γ)
        (idealChangeFactor_ne_zero f D
          (a_ne_zero_of_not_isSquare_discrim (hf ▸ Fact.out)) γ) := by
    apply Units.ext
    simp only [Units.val_mul, coe_orientedIdealChangeFactor, Units.val_mk0]
    rw [mul_assoc, inv_mul_cancel₀ (f.idealSignFactor D).ne_zero, mul_one]
  rw [orientedInvertibleFractionalIdeal_def,
    invertibleFractionalIdeal_smul f D hf hprim γ, orientedInvertibleFractionalIdeal_def]
  rw [← mul_assoc, ← map_mul, ← hfactor, map_mul, mul_assoc]

/-- The narrow class assigned to a primitive form by its sign-corrected ideal. -/
def narrowPicClass (hf : f.discrim = D) (hprim : f.IsPrimitive) :
    GlobalNumberFields.NarrowPic (QuadraticOrder.numberFieldOrder D
      (hf ▸ f.discrim_emod_four_eq_zero_or_one)) :=
  GlobalNumberFields.NarrowPic.mk
    (QuadraticOrder.numberFieldOrder D (hf ▸ f.discrim_emod_four_eq_zero_or_one))
    (f.orientedInvertibleFractionalIdeal D hf hprim)

/-- The oriented narrow class is the supplier's class of the corrected ideal. -/
theorem narrowPicClass_def (hf : f.discrim = D) (hprim : f.IsPrimitive) :
    f.narrowPicClass D hf hprim = GlobalNumberFields.NarrowPic.mk
      (QuadraticOrder.numberFieldOrder D (hf ▸ f.discrim_emod_four_eq_zero_or_one))
      (f.orientedInvertibleFractionalIdeal D hf hprim) := by
  rfl

/-- For positive nonsquare discriminant the oriented narrow class is properly invariant. -/
theorem narrowPicClass_smul (hf : f.discrim = D) (hprim : f.IsPrimitive) (hD : 0 < D)
    (γ : SL(2, ℤ)) :
    (γ • f).narrowPicClass D ((discrim_smul γ f).trans hf)
      ((isPrimitive_smul_iff f γ).mpr hprim) = f.narrowPicClass D hf hprim := by
  let O := QuadraticOrder.numberFieldOrder D (hf ▸ f.discrim_emod_four_eq_zero_or_one)
  have hfactor := GlobalNumberFields.NarrowPic.mkPrincipal_eq_one_of_norm_pos O
    (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0)
    (norm_orientedIdealChangeFactor_pos f D hf hD γ)
  rw [GlobalNumberFields.NarrowPic.mkPrincipal_apply] at hfactor
  rw [narrowPicClass_def, orientedInvertibleFractionalIdeal_smul f D hf hprim γ,
    map_mul, hfactor, one_mul]
  exact (narrowPicClass_def f D hf hprim).symm

/-- Using any positive-leading proper representative agrees with the sign-corrected map. -/
theorem narrowPicClass_eq_mk_of_smul_a_pos (hf : f.discrim = D) (hprim : f.IsPrimitive)
    (hD : 0 < D) (γ : SL(2, ℤ)) (ha : 0 < (γ • f).a) :
    f.narrowPicClass D hf hprim = GlobalNumberFields.NarrowPic.mk
      (QuadraticOrder.numberFieldOrder D (hf ▸ f.discrim_emod_four_eq_zero_or_one))
      ((γ • f).invertibleFractionalIdeal D ((discrim_smul γ f).trans hf)
        ((isPrimitive_smul_iff f γ).mpr hprim)) := by
  rw [← narrowPicClass_smul f D hf hprim hD γ, narrowPicClass_def,
    orientedInvertibleFractionalIdeal_of_a_pos _ _ _ _ ha]

/-- The oriented ideal construction descends to proper classes of primitive forms of positive
nonsquare discriminant, with values in the supplier's narrow Picard group. -/
def properClassToNarrowPic (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    MulAction.orbitRel.Quotient SL(2, ℤ) (primitiveForms D) →
      GlobalNumberFields.NarrowPic (QuadraticOrder.numberFieldOrder D hD) :=
  Quotient.lift (fun f ↦ f.val.narrowPicClass D
      ((mem_primitiveForms D f.val).mp f.property).1
      ((mem_primitiveForms D f.val).mp f.property).2) (by
    intro f g h
    obtain ⟨γ, rfl⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    simpa only [SubMulAction.val_smul] using narrowPicClass_smul g.val D
      ((mem_primitiveForms D g.val).mp g.property).1
      ((mem_primitiveForms D g.val).mp g.property).2 hpos γ)

/-- On a representative, the proper-class map is its oriented ideal's narrow class. -/
@[simp] theorem properClassToNarrowPic_mk (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D) (f : primitiveForms D) :
    properClassToNarrowPic D hD hpos (Quotient.mk'' f) =
      f.val.narrowPicClass D ((mem_primitiveForms D f.val).mp f.property).1
        ((mem_primitiveForms D f.val).mp f.property).2 := by
  simp only [properClassToNarrowPic, Quotient.lift_mk]

end TauCeti.BinaryQuadraticForm
