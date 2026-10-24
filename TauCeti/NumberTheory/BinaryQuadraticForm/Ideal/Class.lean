/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Change
public import TauCeti.NumberTheory.NumberField.Global.Orders.Picard
import TauCeti.Algebra.QuadraticAlgebra.Discriminant

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

/-! ### The orientation of a pair of ideal elements -/

/-- The square-root coordinate of `u · star v`, for integral combinations `u = x a + y β` and
`v = z a + w β` of the generators `a, β = (-b + √D)/2`, is `-(x w - y z) a / 2`. -/
private theorem im_mul_star_idealGenerators (f : BinaryQuadraticForm ℤ) (D : ℤ) (x y z w : ℤ) :
    ((x • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + y • f.idealGenerator D) *
        star (z • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + w • f.idealGenerator D)).im =
      -((x * w - y * z : ℤ) : ℚ) * f.a / 2 := by
  simp only [zsmul_eq_mul, im_mul, re_mul, re_add, im_add, re_star, im_star, re_intCast,
    im_intCast, idealGenerator_re, idealGenerator_im, Int.cast_sub, Int.cast_mul]
  ring

/-- If `μ` sends the ideal generators of `f` to the integral combinations `x a' + y β'` and
`z a' + w β'` of the ideal generators of `g`, then `N(μ) a = (x w - y z) a'`. -/
private theorem norm_mul_a_eq (f g : BinaryQuadraticForm ℤ) (D : ℤ)
    (μ : QuadraticAlgebra ℚ (D : ℚ) 0) (x y z w : ℤ)
    (h₁ : μ * f.a = x • (g.a : QuadraticAlgebra ℚ (D : ℚ) 0) + y • g.idealGenerator D)
    (h₂ : μ * f.idealGenerator D =
      z • (g.a : QuadraticAlgebra ℚ (D : ℚ) 0) + w • g.idealGenerator D) :
    QuadraticAlgebra.norm μ * f.a = ((x * w - y * z : ℤ) : ℚ) * g.a := by
  -- Multiplying both entries of `u · star v` by `μ` multiplies it by `μ · star μ = N(μ)`.
  have h : ((μ * f.a) * star (μ * f.idealGenerator D)).im =
      QuadraticAlgebra.norm μ * ((f.a : QuadraticAlgebra ℚ (D : ℚ) 0) *
        star (f.idealGenerator D)).im := by
    rw [← smul_eq_mul (QuadraticAlgebra.norm μ), ← im_smul, Algebra.smul_def,
      algebraMap_norm_eq_mul_star, star_mul]
    congr 1
    ring
  have hf := im_mul_star_idealGenerators f D 1 0 0 1
  have hg := im_mul_star_idealGenerators g D x y z w
  simp only [one_smul, zero_smul, add_zero, zero_add] at hf
  rw [h₁, h₂, hg, hf] at h
  push_cast at h ⊢
  linarith

/-- If `μ` carries the ideal basis `a, β` of `f` to the ideal basis of `g` by a matrix of
determinant `1`, then `g` is the corresponding proper transform of `f`. -/
private theorem exists_smul_eq_of_mul_eq {D : ℤ} {f g : BinaryQuadraticForm ℤ}
    (hfD : f.discrim = D) (hgD : g.discrim = D) (hfa : f.a ≠ 0) (hga : g.a ≠ 0)
    (μ : QuadraticAlgebra ℚ (D : ℚ) 0) {x y z w : ℤ} (hdet : x * w - y * z = 1)
    (ha : (g.a : QuadraticAlgebra ℚ (D : ℚ) 0) =
      μ * (x • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + y • f.idealGenerator D))
    (hβ : g.idealGenerator D =
      μ * (z • (f.a : QuadraticAlgebra ℚ (D : ℚ) 0) + w • f.idealGenerator D)) :
    ∃ γ : SL(2, ℤ), γ • f = g := by
  let γ : SL(2, ℤ) := ⟨!![w, z; y, x], by rw [Matrix.det_fin_two_of]; linarith⟩
  refine ⟨γ, (eq_of_idealGenerator_mul_a_eq hgD ((discrim_smul γ f).trans hfD) hga ?_).symm⟩
  have hfirst := idealChangeFactor_mul_first f D hfD hfa γ
  have hsecond := idealChangeFactor_mul_second f D hfD hfa γ
  simp only [γ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hfirst hsecond
  rw [← hfirst, ← hsecond, ha, hβ]
  simp only [zsmul_eq_mul]
  ring

/-- **Homothetic form ideals of positive definite forms come from proper equivalence.** If two
forms of negative discriminant `D` with positive leading coefficients have fractional ideals
`I_g = μ I_f`, then `g = γ • f` for some `γ ∈ SL(2, ℤ)`. -/
private theorem exists_smul_eq_of_fractionalIdeal_eq {D : ℤ} [Fact (¬ IsSquare D)]
    (hneg : D < 0) {f g : BinaryQuadraticForm ℤ} (hfD : f.discrim = D) (hgD : g.discrim = D)
    (hfa : 0 < f.a) (hga : 0 < g.a) {μ : QuadraticAlgebra ℚ (D : ℚ) 0} (hμ : μ ≠ 0)
    (hI : g.fractionalIdeal D hgD = spanSingleton _ μ * f.fractionalIdeal D hfD) :
    ∃ γ : SL(2, ℤ), γ • f = g := by
  -- `μ` maps the generators of `I_f` into `I_g`, with integral coefficients `x, y, z, w`.
  have hfg : ∀ u ∈ f.fractionalIdeal D hfD, μ * u ∈ g.fractionalIdeal D hgD := fun u hu ↦ by
    rw [hI]
    exact FractionalIdeal.mem_singleton_mul.mpr ⟨u, hu, rfl⟩
  obtain ⟨x, y, hxy⟩ := (mem_fractionalIdeal_iff g D hgD _).mp
    (hfg _ (a_mem_fractionalIdeal f D hfD))
  obtain ⟨z, w, hzw⟩ := (mem_fractionalIdeal_iff g D hgD _).mp
    (hfg _ (idealGenerator_mem_fractionalIdeal f D hfD))
  -- The generators of `I_g` are `μ` times elements of `I_f`, with coefficients `x', y', z', w'`.
  obtain ⟨u, hu, hua⟩ := FractionalIdeal.mem_singleton_mul.mp
    (hI ▸ a_mem_fractionalIdeal g D hgD)
  obtain ⟨v, hv, hvβ⟩ := FractionalIdeal.mem_singleton_mul.mp
    (hI ▸ idealGenerator_mem_fractionalIdeal g D hgD)
  obtain ⟨x', y', rfl⟩ := (mem_fractionalIdeal_iff f D hfD u).mp hu
  obtain ⟨z', w', rfl⟩ := (mem_fractionalIdeal_iff f D hfD v).mp hv
  refine exists_smul_eq_of_mul_eq hfD hgD hfa.ne' hga.ne' μ ?_ hua hvβ
  -- Both changes of basis scale the leading coefficients by a norm and a determinant.
  have h₁ := norm_mul_a_eq f g D μ x y z w hxy.symm hzw.symm
  have h₂ := norm_mul_a_eq g f D μ⁻¹ x' y' z' w'
    (by rw [hua, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul])
    (by rw [hvβ, ← mul_assoc, inv_mul_cancel₀ hμ, one_mul])
  have hNinv : QuadraticAlgebra.norm μ * QuadraticAlgebra.norm μ⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hμ, map_one]
  have hfaQ : (0 : ℚ) < f.a := by exact_mod_cast hfa
  have hgaQ : (0 : ℚ) < g.a := by exact_mod_cast hga
  -- The determinants multiply to `1`.
  have hprod : (x' * w' - y' * z') * (x * w - y * z) = 1 := by
    have hprodQ : ((x' * w' - y' * z' : ℤ) : ℚ) * ((x * w - y * z : ℤ) : ℚ) = 1 := by
      refine mul_right_cancel₀ (mul_pos hfaQ hgaQ).ne' ?_
      linear_combination -(congrArg₂ (· * ·) h₁ h₂) + (f.a : ℚ) * g.a * hNinv
    exact_mod_cast hprodQ
  -- Since `D < 0`, norms are nonnegative, so the determinant is nonnegative, hence `1`.
  refine Int.eq_one_of_mul_eq_one_right ?_ hprod
  have hN : 0 ≤ QuadraticAlgebra.norm μ⁻¹ := norm_nonneg_of_discr_nonpos (by
    rw [discr_def]
    have hD : (D : ℚ) < 0 := by exact_mod_cast hneg
    linarith) μ⁻¹
  have hdet : (0 : ℚ) ≤ ((x' * w' - y' * z' : ℤ) : ℚ) :=
    nonneg_of_mul_nonneg_left (h₂ ▸ mul_nonneg hN hgaQ.le) hfaQ
  exact_mod_cast hdet

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
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_fractionalIdeal_eq hneg hfD hgD hf hg μ.ne_zero hI
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
