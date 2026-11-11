/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.ClassNumber
public import TauCeti.NumberTheory.BinaryQuadraticForm.Root
import TauCeti.Analysis.Complex.Fuchsian.LevelOne.Sphere
import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Reflection

/-!
# Singular moduli and the Hilbert class polynomial

A primitive positive definite form `a x² + b x y + c y²` of discriminant `-n` has the root
`τ = (-b + i √n) / (2 a)` in the upper half-plane, and the value `j(τ)` of the modular invariant
depends only on the proper equivalence class of the form. This value is the *singular modulus*
`singularModulus n q` of the class `q`. Through the bijection between proper classes and the
Picard group of the order of discriminant `-n` (`posDefProperClassEquivPic`), singular moduli are
indexed by invertible ideal classes; classically `j(τ)` is the `j`-invariant of the elliptic curve
`ℂ / 𝔞` for the ideal `𝔞 = aℤ + ((-b + √(-n)) / 2)ℤ` of the form, a lattice homothetic to
`ℤ + τℤ`.

Since `j` separates the `SL(2, ℤ)`-orbits of the upper half-plane
(`TauCeti.ModularGroup.j_eq_j_iff`) and a form is determined by its root, distinct classes have
distinct singular moduli. Since the `q`-expansion of `j` has integer coefficients, complex
conjugation sends the singular modulus of a class to that of the reflected form
`a x² - b x y + c y²`, which represents the inverse Picard class.

The *Hilbert class polynomial* `hilbertClassPolynomial n` is the monic polynomial whose roots are
the singular moduli of discriminant `-n`, each with multiplicity one. It is the product of
`X - j(τ)` over the roots `τ` of the primitive reduced forms of discriminant `-n`, one for each
proper class. Its degree is the order of the Picard group, which for a fundamental discriminant is
the class number of the field, and its coefficients are real. The theory of complex
multiplication shows that its coefficients are in fact integers and that adjoining any singular
modulus of discriminant `-n` to the quadratic field `K = ℚ(√(-n))` generates the ring class field
of the order of discriminant `-n` over `K`; neither statement is proved here.

## Main definitions

* `TauCeti.BinaryQuadraticForm.singularModulus n q`: the value of `j` at the root of any form in
  the proper class `q` of primitive positive definite forms of discriminant `-n`.
* `TauCeti.BinaryQuadraticForm.hilbertClassPolynomial n`: the product of `X - j(τ)` over the
  roots `τ` of the primitive reduced forms of discriminant `-n`.

## Main results

* `TauCeti.BinaryQuadraticForm.singularModulus_injective`: distinct proper classes have distinct
  singular moduli.
* `TauCeti.BinaryQuadraticForm.star_singularModulus`: the complex conjugate of the singular
  modulus of a class is the singular modulus of the inverse Picard class, and
  `im_singularModulus_eq_zero_iff`: a singular modulus is real exactly when its Picard class has
  order dividing `2`.
* `TauCeti.BinaryQuadraticForm.isRoot_hilbertClassPolynomial_iff`: the roots of the Hilbert class
  polynomial are exactly the singular moduli of discriminant `-n`.
* `TauCeti.BinaryQuadraticForm.separable_hilbertClassPolynomial`: these roots are simple.
* `TauCeti.BinaryQuadraticForm.natDegree_hilbertClassPolynomial_eq_nat_card_pic`,
  `natDegree_hilbertClassPolynomial_eq_classNumber`: its degree is the order of the Picard group
  of the order of discriminant `-n`, and the class number of a quadratic field of discriminant
  `-n`.
* `TauCeti.BinaryQuadraticForm.map_star_hilbertClassPolynomial`: it is invariant under complex
  conjugation of the coefficients, so its coefficients are real
  (`im_coeff_hilbertClassPolynomial`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §11 (the `j`-invariant of a lattice and of an ideal
  class) and §13 (the class equation and its roots).
* B. H. Gross and D. B. Zagier, *On singular moduli*, J. Reine Angew. Math. **355** (1985),
  191–220.
-/

public section
noncomputable section

open Polynomial MulAction UpperHalfPlane
open TauCeti.ModularForm
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

variable (n : ℕ) [NeZero n]

/-! ### Singular moduli -/

/-- The value of `j` at the root of a primitive positive definite form is constant on the proper
class of the form. -/
private theorem j_root_eq_of_orbitRel {f g : ↥(posDef n ⊓ primitiveForms (-n))}
    (h : orbitRel SL(2, ℤ) _ f g) :
    j (root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩) =
      j (root ⟨g, inf_le_left (b := primitiveForms (-n)) g.2⟩) := by
  obtain ⟨γ, rfl⟩ := mem_orbit_iff.1 h
  rw [← j_smul_SL2Z γ (root ⟨g, inf_le_left (b := primitiveForms (-n)) g.2⟩), ← root_smul]
  -- both sides are the form `γ • g`, once as an element of `posDef n ⊓ primitiveForms (-n)` and
  -- once as an element of `posDef n`; the sub-action subtypes share their underlying forms
  congr 2

/-- The **singular modulus** of a proper class of primitive positive definite forms of
discriminant `-n`: the value `j(τ)` of the modular invariant at the root
`τ = (-b + i √n) / (2 a)` of any form `a x² + b x y + c y²` in the class. -/
def singularModulus : PosDefProperClass n → ℂ :=
  Quotient.lift (fun f ↦ j (root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩))
    fun _ _ ↦ j_root_eq_of_orbitRel n

/-- The singular modulus of the class of a form is the value of `j` at the root of the form. -/
@[simp]
theorem singularModulus_mk (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    singularModulus n (Quotient.mk _ f) =
      j (root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩) :=
  (rfl)

variable {n} in
/-- **Distinct proper classes have distinct singular moduli.** Two roots with the same value of
`j` lie in one `SL(2, ℤ)`-orbit, and a positive definite form is determined by its root. -/
theorem singularModulus_injective : Function.Injective (singularModulus n) := by
  refine Quotient.ind₂ fun f g h ↦ Quotient.sound ?_
  obtain ⟨γ, hγ⟩ := ModularGroup.j_eq_j_iff.1 h
  rw [← root_smul, root_injective.eq_iff] at hγ
  refine mem_orbit_iff.2 ⟨γ⁻¹, Subtype.ext ?_⟩
  rw [SubMulAction.val_smul, inv_smul_eq_iff]
  exact (congrArg Subtype.val hγ).symm

variable {n} in
/-- Complex conjugation sends the singular modulus of the class of `a x² + b x y + c y²` to the
singular modulus of the class of the reflected form `a x² - b x y + c y²`. -/
theorem star_singularModulus_mk_of_eq_reflected {f g : ↥(posDef n ⊓ primitiveForms (-n))}
    (hg : (g : BinaryQuadraticForm ℤ) = (f : BinaryQuadraticForm ℤ).reflected) :
    starRingEnd ℂ (singularModulus n (Quotient.mk _ f)) = singularModulus n (Quotient.mk _ g) := by
  rw [singularModulus_mk, singularModulus_mk, ← j_J_smul,
    root_of_eq_reflected (f := ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩)
      (g := ⟨g, inf_le_left (b := primitiveForms (-n)) g.2⟩) hg]

variable {n} in
/-- **Complex conjugation inverts the class of a singular modulus.** The complex conjugate of the
singular modulus of a class is the singular modulus of the inverse class in the Picard group of
the order of discriminant `-n`. -/
theorem star_singularModulus (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) (q : PosDefProperClass n) :
    starRingEnd ℂ (singularModulus n q) =
      singularModulus n
        ((posDefProperClassEquivPic n hn).symm (posDefProperClassToPic n hn q)⁻¹) := by
  induction q using Quotient.inductionOn with | h f
  let g : ↥(posDef n ⊓ primitiveForms (-n)) :=
    ⟨(f : BinaryQuadraticForm ℤ).reflected, reflected_mem_posDef_inf_primitiveForms_iff.2 f.2⟩
  rw [star_singularModulus_mk_of_eq_reflected (g := g) rfl]
  refine congrArg (singularModulus n) ((Equiv.eq_symm_apply _).2 ?_)
  rw [posDefProperClassEquivPic_apply]
  exact posDefProperClassToPic_mk_eq_inv_of_eq_reflected n hn (f := f) (g := g) rfl

variable {n} in
/-- **Real singular moduli are the ambiguous classes.** The singular modulus of a class is real
exactly when the class has order dividing `2` in the Picard group of the order of discriminant
`-n`. In particular the singular modulus of the principal class is real. -/
theorem im_singularModulus_eq_zero_iff (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)
    (q : PosDefProperClass n) :
    (singularModulus n q).im = 0 ↔ posDefProperClassToPic n hn q ^ 2 = 1 := by
  rw [← Complex.conj_eq_iff_im, star_singularModulus hn, singularModulus_injective.eq_iff,
    Equiv.symm_apply_eq, posDefProperClassEquivPic_apply]
  -- `Iff.rfl` closes the cast mismatch `((-n : ℤ) : ℚ) = -(n : ℚ)` between the Picard group in
  -- the type of `posDefProperClassToPic` and the one in `posDefProperClassEquivPic`
  exact inv_eq_iff_mul_eq_one.trans (by rw [sq]; exact Iff.rfl)

/-! ### The Hilbert class polynomial -/

/-- The proper class of a primitive reduced form. -/
private abbrev reducedClass (f : primitiveReducedForms n) : PosDefProperClass n :=
  Quotient.mk _ ⟨f, mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2⟩

/-- The **Hilbert class polynomial** of discriminant `-n`: the product of `X - j(τ)` over the
roots `τ = (-b + i √n) / (2 a)` of the primitive reduced forms `a x² + b x y + c y²` of
discriminant `-n`. Each proper class of primitive positive definite forms contains exactly one
primitive reduced form, so the roots are the singular moduli of discriminant `-n`. -/
def hilbertClassPolynomial : ℂ[X] :=
  ∏ f : primitiveReducedForms n, (X - C (singularModulus n
    (Quotient.mk _ ⟨f, mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2⟩)))

/-- The Hilbert class polynomial is the product of `X - j(q)` over all proper classes `q` of
primitive positive definite forms of discriminant `-n`. -/
theorem hilbertClassPolynomial_eq_prod [Fintype (PosDefProperClass n)] :
    hilbertClassPolynomial n = ∏ q : PosDefProperClass n, (X - C (singularModulus n q)) :=
  Fintype.prod_bijective (reducedClass n) posDefProperClass_mk_primitiveReducedForms_bijective _ _
    fun _ ↦ rfl

/-- The Hilbert class polynomial is monic. -/
theorem monic_hilbertClassPolynomial : (hilbertClassPolynomial n).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

/-- The degree of the Hilbert class polynomial of discriminant `-n` is the number of primitive
reduced forms of discriminant `-n`. -/
theorem natDegree_hilbertClassPolynomial :
    (hilbertClassPolynomial n).natDegree = (primitiveReducedForms n).card := by
  rw [hilbertClassPolynomial, natDegree_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _]
  simp

/-- **The degree of the Hilbert class polynomial is the order of the Picard group** of the
quadratic order of discriminant `-n`. -/
theorem natDegree_hilbertClassPolynomial_eq_nat_card_pic
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) :
    (hilbertClassPolynomial n).natDegree =
      Nat.card (GlobalNumberFields.Pic (QuadraticOrder.numberFieldOrder (-n) hn)) := by
  rw [natDegree_hilbertClassPolynomial, nat_card_pic]

/-- **The degree of the Hilbert class polynomial is the class number**: if `K` is a quadratic
field of discriminant `-n`, the Hilbert class polynomial of discriminant `-n` has degree the class
number of `K`. -/
theorem natDegree_hilbertClassPolynomial_eq_classNumber {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hn : NumberField.discr K = -n) :
    (hilbertClassPolynomial n).natDegree = NumberField.classNumber K := by
  rw [natDegree_hilbertClassPolynomial, classNumber_eq_card_primitiveReducedForms_of_discr_eq hK hn]

/-- The roots of the Hilbert class polynomial, with multiplicity, are the singular moduli at the
roots of the primitive reduced forms of discriminant `-n`. -/
theorem roots_hilbertClassPolynomial :
    (hilbertClassPolynomial n).roots =
      Finset.univ.val.map fun f : primitiveReducedForms n ↦ singularModulus n (Quotient.mk _
        ⟨f, mem_posDef_inf_primitiveForms_of_mem_primitiveReducedForms f.2⟩) := by
  rw [hilbertClassPolynomial, roots_prod _ _ (monic_prod_of_monic _ _
    fun _ _ ↦ monic_X_sub_C _).ne_zero]
  simp [Multiset.bind_singleton]

/-- **The roots of the Hilbert class polynomial are the singular moduli**: `x` is a root exactly
when it is the value of `j` at the root of a primitive positive definite form of discriminant
`-n`. -/
theorem isRoot_hilbertClassPolynomial_iff {x : ℂ} :
    (hilbertClassPolynomial n).IsRoot x ↔ ∃ q : PosDefProperClass n, singularModulus n q = x := by
  rw [← mem_roots (monic_hilbertClassPolynomial n).ne_zero, roots_hilbertClassPolynomial,
    Multiset.mem_map]
  refine ⟨fun ⟨f, _, hf⟩ ↦ ⟨_, hf⟩, fun ⟨q, hq⟩ ↦ ?_⟩
  obtain ⟨f, rfl⟩ := posDefProperClass_mk_primitiveReducedForms_bijective.2 q
  exact ⟨f, Finset.mem_univ_val _, hq⟩

/-- The singular modulus of every proper class of discriminant `-n` is a root of the Hilbert class
polynomial of discriminant `-n`. -/
theorem isRoot_hilbertClassPolynomial_singularModulus (q : PosDefProperClass n) :
    (hilbertClassPolynomial n).IsRoot (singularModulus n q) :=
  (isRoot_hilbertClassPolynomial_iff n).2 ⟨q, rfl⟩

/-- **The Hilbert class polynomial has simple roots**, since distinct proper classes have distinct
singular moduli. -/
theorem separable_hilbertClassPolynomial : (hilbertClassPolynomial n).Separable :=
  separable_prod_X_sub_C_iff.2 <| singularModulus_injective.comp
    posDefProperClass_mk_primitiveReducedForms_bijective.1

/-- Complex conjugation sends the singular modulus of a proper class to the singular modulus of
its reflected class, the class of the forms `a x² - b x y + c y²`. -/
@[simp]
theorem star_singularModulus_eq_reflectedClass (q : PosDefProperClass n) :
    starRingEnd ℂ (singularModulus n q) = singularModulus n (reflectedClass n q) := by
  induction q using Quotient.inductionOn with | h f
  rw [reflectedClass_mk]
  exact star_singularModulus_mk_of_eq_reflected rfl

/-- **The Hilbert class polynomial is invariant under complex conjugation**: conjugation permutes
the singular moduli, sending each class to the class of its reflected form. -/
@[simp]
theorem map_star_hilbertClassPolynomial :
    (hilbertClassPolynomial n).map (starRingEnd ℂ) = hilbertClassPolynomial n := by
  have := Fintype.ofFinite (PosDefProperClass n)
  rw [hilbertClassPolynomial_eq_prod, Polynomial.map_prod]
  simp only [Polynomial.map_sub, map_X, map_C, star_singularModulus_eq_reflectedClass]
  exact Fintype.prod_bijective _ (reflectedClass_involutive n).bijective _ _ fun _ ↦ rfl

/-- **The Hilbert class polynomial has real coefficients.** -/
@[simp]
theorem im_coeff_hilbertClassPolynomial (k : ℕ) : ((hilbertClassPolynomial n).coeff k).im = 0 := by
  rw [← Complex.conj_eq_iff_im, ← coeff_map, map_star_hilbertClassPolynomial]

end TauCeti.BinaryQuadraticForm
