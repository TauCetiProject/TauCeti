/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Change
public import TauCeti.NumberTheory.NumberField.Global.Orders.Picard
import TauCeti.Algebra.QuadraticAlgebra.Discriminant
import Mathlib.RingTheory.Norm.Basic

/-!
# Picard classes of primitive binary quadratic forms

A primitive integral form `f = (a, b, c)` of nonsquare discriminant `D` has the invertible
fractional ideal `aℤ + ((-b + √D)/2)ℤ` of the quadratic order `O_D` of discriminant `D`
(`TauCeti.BinaryQuadraticForm.invertibleFractionalIdeal`). Its class in the Picard group
`Pic(O_D)` is `TauCeti.BinaryQuadraticForm.picClass`. Properly equivalent forms have ideals
differing by an explicit principal factor (`invertibleFractionalIdeal_smul`), so the class is
constant on proper equivalence classes.

For negative `D` the converse holds on positive definite forms: two primitive forms with positive
leading coefficients and the same Picard class are properly equivalent. If `I_g = μ I_f`, then
`μ` carries the basis `a, (-b + √D)/2` of `I_f` to a basis of `I_g`, and the integral change of
basis has determinant `1`. Its sign is read off the square-root coordinate of `u · star v`, which
is multiplied by the norm `N(μ) > 0` and records the orientation of the pair `u, v`; its absolute
value is `1` because the same argument applies to `μ⁻¹`. The matching proper change of variables
then sends `f` to `g`, since a form of fixed discriminant is determined by the quotient of its
two ideal generators.

Consequently the proper equivalence classes of primitive positive definite forms of discriminant
`-n` inject into `Pic(O_{-n})` (`posDefProperClassToPic_injective`). This is the injective half
of the form-ideal correspondence of Cox, Theorem 7.7.

The positive-norm ideal comparison used below is proved in
`TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Change`; it also applies to the
positive-discriminant narrow correspondence.

## Main definitions and results

* `TauCeti.BinaryQuadraticForm.picClass`: the Picard class of a primitive form.
* `TauCeti.BinaryQuadraticForm.picClass_smul`: it is invariant under proper equivalence.
* `TauCeti.BinaryQuadraticForm.picClass_eq_picClass_iff_of_neg`: for `D < 0` and positive
  leading coefficients, equal Picard classes are exactly proper equivalence.
* `TauCeti.BinaryQuadraticForm.posDefProperClassToPic`: the induced map on proper classes of
  primitive positive definite forms, and `posDefProperClassToPic_injective`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7.
-/

public section

open QuadraticAlgebra FractionalIdeal MulAction
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

section NonSquare

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)]

/-- **The Picard class of a primitive form.** For a primitive form `(a, b, c)` of nonsquare
discriminant `D`, the class of the invertible ideal `aℤ + ((-b + √D)/2)ℤ` in the Picard group of
the quadratic order of discriminant `D`. -/
noncomputable def picClass (f : primitiveForms D) : Pic (QuadraticOrder.numberFieldOrder D hD) :=
  (QuadraticOrder.numberFieldOrder D hD).mkPic
    ((f : BinaryQuadraticForm ℤ).invertibleFractionalIdeal D
      ((mem_primitiveForms D f).mp f.2).1 ((mem_primitiveForms D f).mp f.2).2)

/-- The Picard class of a primitive form is the class of its invertible form ideal. -/
theorem picClass_def (f : primitiveForms D) :
    picClass D hD f = (QuadraticOrder.numberFieldOrder D hD).mkPic
      ((f : BinaryQuadraticForm ℤ).invertibleFractionalIdeal D
        ((mem_primitiveForms D f).mp f.2).1 ((mem_primitiveForms D f).mp f.2).2) := (rfl)

/-- **Properly equivalent forms have the same Picard class.** -/
@[simp] theorem picClass_smul (γ : SL(2, ℤ)) (f : primitiveForms D) :
    picClass D hD (γ • f) = picClass D hD f := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨hfD, hprim⟩ := (mem_primitiveForms D f).mp hf
  have h := invertibleFractionalIdeal_smul f D hfD hprim γ
  simp only [picClass_def, SubMulAction.val_smul]
  rw [h, map_mul, ClassGroup.mk_toPrincipalIdeal, one_mul]

/-- **Equal Picard classes of positive definite forms.** For negative `D`, two primitive forms of
discriminant `D` with positive leading coefficients have the same Picard class exactly when they
are properly equivalent. -/
theorem picClass_eq_picClass_iff_of_neg (hneg : D < 0) {f g : primitiveForms D}
    (hf : 0 < (f : BinaryQuadraticForm ℤ).a) (hg : 0 < (g : BinaryQuadraticForm ℤ).a) :
    picClass D hD f = picClass D hD g ↔ ∃ γ : SL(2, ℤ), γ • f = g := by
  refine ⟨fun h ↦ ?_, fun ⟨γ, hγ⟩ ↦ by rw [← hγ, picClass_smul]⟩
  obtain ⟨f, hfm⟩ := f
  obtain ⟨g, hgm⟩ := g
  obtain ⟨hfD, hfp⟩ := (mem_primitiveForms D f).mp hfm
  obtain ⟨hgD, hgp⟩ := (mem_primitiveForms D g).mp hgm
  simp only [picClass_def] at h
  -- The quotient `I_g I_f⁻¹` is principal, generated by some `μ`.
  have hquot : (QuadraticOrder.numberFieldOrder D hD).mkPic
      (g.invertibleFractionalIdeal D hgD hgp * (f.invertibleFractionalIdeal D hfD hfp)⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h, mul_inv_cancel]
  obtain ⟨μ, hμ⟩ := ClassGroup.mk_eq_one_iff_exists.mp hquot
  have hI : g.fractionalIdeal D hgD = spanSingleton _ (μ : QuadraticAlgebra ℚ (D : ℚ) 0) *
      f.fractionalIdeal D hfD := by
    rw [← coe_invertibleFractionalIdeal f D hfD hfp, ← coe_invertibleFractionalIdeal g D hgD hgp,
      ← coe_toPrincipalIdeal, ← Units.val_mul, hμ, inv_mul_cancel_right]
  have hnorm : 0 < Algebra.norm ℚ (μ : QuadraticAlgebra ℚ (D : ℚ) 0) := by
    refine lt_of_le_of_ne ?_ (Algebra.norm_ne_zero_iff.mpr μ.ne_zero).symm
    rw [Algebra.norm_quadraticAlgebra_apply]
    apply norm_nonneg_of_discr_nonpos
    rw [discr_def]
    have hnegQ : (D : ℚ) < 0 := by exact_mod_cast hneg
    linarith
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_fractionalIdeal_eq_of_norm_pos
    f g D hfD hgD hf hg μ hnorm hI
  exact ⟨γ, Subtype.ext (by rw [SubMulAction.val_smul]; exact hγ)⟩

end NonSquare

section PosDef

variable (n : ℕ) [NeZero n]

variable (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)

/-- A primitive positive definite form, as a primitive form of discriminant `-n`. -/
private def toPrimitiveForms (f : ↥(posDef n ⊓ primitiveForms (-n))) : primitiveForms (-n) :=
  ⟨f, inf_le_right (a := posDef n) f.2⟩

private theorem coe_toPrimitiveForms (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    (toPrimitiveForms n f : BinaryQuadraticForm ℤ) = f := (rfl)

/-- **The Picard class of a proper class of primitive positive definite forms**, the class of
`aℤ + ((-b + √(-n))/2)ℤ` in the Picard group of the quadratic order of discriminant `-n`. -/
noncomputable def posDefProperClassToPic :
    PosDefProperClass n → Pic (QuadraticOrder.numberFieldOrder (-n) hn) :=
  Quotient.lift (fun f ↦ picClass (-n) hn (toPrimitiveForms n f)) fun f g hfg ↦ by
    obtain ⟨γ, rfl⟩ := mem_orbit_iff.mp ((orbitRel_apply).mp hfg)
    exact picClass_smul (-n) hn γ (toPrimitiveForms n g)

/-- The Picard class of the proper class of a form is the Picard class of the form. -/
@[simp] theorem posDefProperClassToPic_mk (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    posDefProperClassToPic n hn (Quotient.mk _ f) =
      picClass (-n) hn ⟨f, inf_le_right (a := posDef n) f.2⟩ := (rfl)

/-- **Distinct proper classes of primitive positive definite forms have distinct Picard classes.**
This is the injective half of the correspondence between proper classes of primitive positive
definite forms of discriminant `-n` and the Picard group of the order of discriminant `-n`. -/
theorem posDefProperClassToPic_injective : Function.Injective (posDefProperClassToPic n hn) := by
  intro p q
  refine Quotient.inductionOn₂ p q fun f g h ↦ ?_
  have hneg : (-n : ℤ) < 0 := by simpa using NeZero.pos n
  obtain ⟨γ, hγ⟩ := (picClass_eq_picClass_iff_of_neg (-n) hn hneg
    ((mem_posDef_inf_primitiveForms n).mp f.2).2.1
    ((mem_posDef_inf_primitiveForms n).mp g.2).2.1).mp h
  refine Quotient.sound (mem_orbit_iff.mpr ⟨γ⁻¹, Subtype.ext ?_⟩)
  have hγ' := congrArg Subtype.val hγ
  simp only [SubMulAction.val_smul, coe_toPrimitiveForms] at hγ' ⊢
  rw [← hγ', inv_smul_smul]

end PosDef

end TauCeti.BinaryQuadraticForm
