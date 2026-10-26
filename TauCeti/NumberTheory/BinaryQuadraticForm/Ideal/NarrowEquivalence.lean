/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.NarrowClass
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Normalization
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Class
public import TauCeti.NumberTheory.BinaryQuadraticForm.PositiveRepresentative

/-!
# Proper classes and the narrow Picard group

Every invertible ideal has a positive-leading primitive form representative up to positive
rational scaling. Equality of narrow classes supplies a positive-norm scaling factor, and
the signed basis comparison then recovers a proper equivalence. Positive-leading
normalization identifies this comparison with the original sign-corrected form-ideal map.
These constructions give the bijection into the supplier's native narrow Picard group.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7 and the narrow analogue.
-/

public section
noncomputable section

open FractionalIdeal
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

/-- Every native narrow Picard class comes from a primitive proper form class. -/
theorem properClassToNarrowPic_surjective (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    Function.Surjective (properClassToNarrowPic D hD hpos) := by
  let O := QuadraticOrder.numberFieldOrder D hD
  intro c
  obtain ⟨I, hIc⟩ := GlobalNumberFields.NarrowPic.mk_surjective O c
  obtain ⟨f, hf, hp, ha, r, hr, hscale⟩ :=
    exists_pos_primitive_form_fractionalIdeal_eq D hD I.val (O.invertible_isProper I)
  let g : primitiveForms D := ⟨f, (mem_primitiveForms D f).mpr ⟨hf, hp⟩⟩
  have hrK : (r : QuadraticAlgebra ℚ (D : ℚ) 0) ≠ 0 := by exact_mod_cast hr.ne'
  let u := Units.mk0 (r : QuadraticAlgebra ℚ (D : ℚ) 0) hrK
  have hnorm : Algebra.norm ℚ (u : QuadraticAlgebra ℚ (D : ℚ) 0) = r ^ 2 := by
    simp [u, Algebra.norm_quadraticAlgebra_apply, QuadraticAlgebra.norm_def, pow_two]
  have hfactor := GlobalNumberFields.NarrowPic.mkPrincipal_eq_one_of_norm_pos O
    (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0) (hnorm ▸ sq_pos_of_pos hr)
  rw [GlobalNumberFields.NarrowPic.mkPrincipal_apply] at hfactor
  have hI : I = toPrincipalIdeal _ _ u * f.invertibleFractionalIdeal D hf hp := by
    apply Units.ext
    rw [Units.val_mul, coe_toPrincipalIdeal, coe_invertibleFractionalIdeal]
    exact hscale
  have hmap := congrArg (GlobalNumberFields.NarrowPic.mk O) hI
  dsimp only [O] at hfactor hmap
  simp only [map_mul, hfactor, one_mul] at hmap
  refine ⟨Quotient.mk _ g, ?_⟩
  simpa only [properClassToNarrowPic_mk, g, narrowPicClass_def,
    orientedInvertibleFractionalIdeal_of_a_pos f D hf hp ha] using hmap.symm.trans hIc

private theorem exists_smul_eq_of_narrowPicClass_eq (D : ℤ)
    (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)] (hpos : 0 < D)
    (f g : primitiveForms D)
    (h : f.val.narrowPicClass D ((mem_primitiveForms D f.val).mp f.property).1
        ((mem_primitiveForms D f.val).mp f.property).2 =
      g.val.narrowPicClass D ((mem_primitiveForms D g.val).mp g.property).1
        ((mem_primitiveForms D g.val).mp g.property).2) :
    ∃ γ : SL(2, ℤ), γ • f = g := by
  have hf := ((mem_primitiveForms D f.val).mp f.property).1
  have hg := ((mem_primitiveForms D g.val).mp g.property).1
  have hfp := ((mem_primitiveForms D f.val).mp f.property).2
  have hgp := ((mem_primitiveForms D g.val).mp g.property).2
  obtain ⟨ρ, hρ⟩ := exists_smul_a_pos f.val (hf.symm ▸ hpos)
  obtain ⟨σ, hσ⟩ := exists_smul_a_pos g.val (hg.symm ▸ hpos)
  have hρD := (discrim_smul ρ f.val).trans hf
  have hσD := (discrim_smul σ g.val).trans hg
  have hρp := (isPrimitive_smul_iff f.val ρ).mpr hfp
  have hσp := (isPrimitive_smul_iff g.val σ).mpr hgp
  let O := QuadraticOrder.numberFieldOrder D hD
  have hmk : GlobalNumberFields.NarrowPic.mk O
      ((ρ • f.val).invertibleFractionalIdeal D hρD hρp) =
      GlobalNumberFields.NarrowPic.mk O
        ((σ • g.val).invertibleFractionalIdeal D hσD hσp) := by
    rw [narrowPicClass_eq_mk_of_smul_a_pos f.val D hf hfp hpos ρ hρ,
      narrowPicClass_eq_mk_of_smul_a_pos g.val D hg hgp hpos σ hσ] at h
    exact h
  obtain ⟨u, hu, hI⟩ :=
    (GlobalNumberFields.NarrowPic.mk_eq_mk_iff_exists_norm_pos O
      (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0)).mp hmk
  have hscale : (σ • g.val).fractionalIdeal D hσD =
      spanSingleton (nonZeroDivisors O.toSubalgebra)
        (u : QuadraticAlgebra ℚ (D : ℚ) 0) * (ρ • f.val).fractionalIdeal D hρD := by
    have hval := congrArg Units.val hI
    simpa only [Units.val_mul, coe_invertibleFractionalIdeal, coe_toPrincipalIdeal,
      mul_comm] using hval.symm
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_fractionalIdeal_eq_of_norm_pos
    (ρ • f.val) (σ • g.val) D hρD hσD hρ hσ u hu hscale
  refine ⟨σ⁻¹ * τ * ρ, Subtype.ext ?_⟩
  simp only [SubMulAction.val_smul, mul_smul, hτ, inv_smul_smul]

/-- Equal oriented narrow classes determine equal proper classes at positive nonsquare
discriminant. -/
theorem properClassToNarrowPic_injective (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    Function.Injective (properClassToNarrowPic D hD hpos) := by
  intro q r
  induction q using Quotient.inductionOn with
  | h f =>
    induction r using Quotient.inductionOn with
    | h g =>
      intro h
      obtain ⟨γ, hγ⟩ := exists_smul_eq_of_narrowPicClass_eq D hD hpos f g
        (by simpa only [properClassToNarrowPic_mk] using h)
      rw [← hγ]
      exact MulAction.orbitRel.Quotient.quotient_smul_eq.symm

/-- Proper classes of primitive positive-discriminant forms are in bijection with the
consumed narrow Picard group through the original sign-corrected map. -/
def properClassEquivNarrowPic (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    MulAction.orbitRel.Quotient SL(2, ℤ) (primitiveForms D) ≃
      GlobalNumberFields.NarrowPic (QuadraticOrder.numberFieldOrder D hD) :=
  Equiv.ofBijective (properClassToNarrowPic D hD hpos)
    ⟨properClassToNarrowPic_injective D hD hpos, properClassToNarrowPic_surjective D hD hpos⟩

/-- The bijection retains the existing oriented form-ideal map as its forward function. -/
@[simp] theorem properClassEquivNarrowPic_apply (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D)
    (q : MulAction.orbitRel.Quotient SL(2, ℤ) (primitiveForms D)) :
    properClassEquivNarrowPic D hD hpos q = properClassToNarrowPic D hD hpos q := by
  rfl

end TauCeti.BinaryQuadraticForm
