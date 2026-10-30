/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Narrow.Class
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Normalization
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
  obtain ⟨f, hf, hp, ha, r, u, hr, hu, hI⟩ :=
    exists_pos_primitive_form_invertibleFractionalIdeal_eq D hD I
  let g : primitiveForms D := ⟨f, (mem_primitiveForms D f).mpr ⟨hf, hp⟩⟩
  have hnorm : Algebra.norm ℚ (u : QuadraticAlgebra ℚ (D : ℚ) 0) = r ^ 2 := by
    simp [hu, Algebra.norm_quadraticAlgebra_apply, QuadraticAlgebra.norm_def, pow_two]
  have hfactor := GlobalNumberFields.NarrowPic.mkPrincipal_eq_one_of_norm_pos O
    (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0) (hnorm ▸ sq_pos_of_pos hr)
  rw [GlobalNumberFields.NarrowPic.mkPrincipal_apply] at hfactor
  have hmap := congrArg (GlobalNumberFields.NarrowPic.mk O) hI
  dsimp only [O] at hfactor hmap
  simp only [map_mul, hfactor, one_mul] at hmap
  refine ⟨Quotient.mk _ g, ?_⟩
  simpa only [properClassToNarrowPic_mk, g, narrowPicClass_def,
    orientedInvertibleFractionalIdeal_of_a_pos f D hf hp ha] using hmap.symm.trans hIc

/-- **Equal oriented narrow classes.** For positive nonsquare `D`, two primitive forms of
discriminant `D` have the same oriented narrow class exactly when they are properly
equivalent. -/
theorem narrowPicClass_eq_narrowPicClass_iff_of_pos (D : ℤ) [Fact (¬ IsSquare D)]
    (hpos : 0 < D) {f g : BinaryQuadraticForm ℤ} (hf : f.discrim = D) (hfp : f.IsPrimitive)
    (hg : g.discrim = D) (hgp : g.IsPrimitive) :
    f.narrowPicClass D hf hfp = g.narrowPicClass D hg hgp ↔ ∃ γ : SL(2, ℤ), γ • f = g := by
  refine ⟨fun h ↦ ?_, by rintro ⟨γ, rfl⟩; exact (narrowPicClass_smul f D hf hfp hpos γ).symm⟩
  obtain ⟨ρ, hρ⟩ := exists_smul_a_pos f (hf.symm ▸ hpos)
  obtain ⟨σ, hσ⟩ := exists_smul_a_pos g (hg.symm ▸ hpos)
  have hρD := (discrim_smul ρ f).trans hf
  have hσD := (discrim_smul σ g).trans hg
  have hρp := (isPrimitive_smul_iff f ρ).mpr hfp
  have hσp := (isPrimitive_smul_iff g σ).mpr hgp
  have hD : D % 4 = 0 ∨ D % 4 = 1 := hf ▸ f.discrim_emod_four_eq_zero_or_one
  let O := QuadraticOrder.numberFieldOrder D hD
  have hmk : GlobalNumberFields.NarrowPic.mk O
      ((ρ • f).invertibleFractionalIdeal D hρD hρp) =
      GlobalNumberFields.NarrowPic.mk O
        ((σ • g).invertibleFractionalIdeal D hσD hσp) := by
    rw [narrowPicClass_eq_mk_of_smul_a_pos f D hf hfp hpos ρ hρ,
      narrowPicClass_eq_mk_of_smul_a_pos g D hg hgp hpos σ hσ] at h
    exact h
  obtain ⟨u, hu, hI⟩ :=
    (GlobalNumberFields.NarrowPic.mk_eq_mk_iff_exists_norm_pos O
      (QuadraticAlgebra.finrank_eq_two (D : ℚ) 0)).mp hmk
  have hscale : (σ • g).fractionalIdeal D hσD =
      spanSingleton (nonZeroDivisors O.toSubalgebra)
        (u : QuadraticAlgebra ℚ (D : ℚ) 0) * (ρ • f).fractionalIdeal D hρD := by
    -- Rewriting with `mul_comm` first keeps commutativity out of the `simp` set.
    rw [mul_comm]
    simpa only [Units.val_mul, coe_invertibleFractionalIdeal, coe_toPrincipalIdeal]
      using (congrArg Units.val hI).symm
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_fractionalIdeal_eq_of_norm_pos
    (ρ • f) (σ • g) D hρD hσD hρ hσ u hu hscale
  exact ⟨σ⁻¹ * τ * ρ, by simp only [mul_smul, hτ, inv_smul_smul]⟩

/-- Equal oriented narrow classes determine equal proper classes at positive nonsquare
discriminant. -/
theorem properClassToNarrowPic_injective (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] (hpos : 0 < D) :
    Function.Injective (properClassToNarrowPic D hD hpos) := by
  refine fun q r ↦ Quotient.inductionOn₂ q r fun f g h ↦ ?_
  simp only [properClassToNarrowPic_mk, narrowPicClass_eq_narrowPicClass_iff_of_pos D hpos] at h
  obtain ⟨γ, hγ⟩ := h
  obtain rfl : γ • f = g := Subtype.ext ((SubMulAction.val_smul γ f).trans hγ)
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
