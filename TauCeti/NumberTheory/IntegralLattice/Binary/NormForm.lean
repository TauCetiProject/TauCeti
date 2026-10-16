/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Content
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
import TauCeti.Algebra.QuadraticDiscriminant

/-!
# Binary norm forms of integral lattices

In a rank-two carrier basis, a lattice with Gram matrix `!![A, B; B, C]` has binary norm
form `A x² + 2B x y + C y²`. Its discriminant is `-4 * determinant`. Dividing by its
content produces a primitive form when the ambient form is nonzero. The content and primitive
discriminant are basis-independent, although the polynomial depends on the basis.

The intrinsic nonnegative content `binaryContent` and the primitive discriminant
`binaryDiscriminant` are characterized by computation in any carrier basis. Nondegeneracy gives
positive content and nonzero primitive discriminant. The latter is zero or one modulo four,
negative for either definite sign, and positive for an indefinite lattice. A separate integer twist
of the form multiplies its content by the absolute scalar.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Sections 1 and 2.
-/

public section

open Module

namespace TauCeti.IntegralLattice
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (b : Basis (Fin 2) ℤ L)

/-- The integral norm in a rank-two carrier basis, with twice the off-diagonal Gram entry as its
middle coefficient. -/
noncomputable def binaryNormForm : BinaryQuadraticForm ℤ :=
  ⟨L.integralNorm (b 0), 2 * L.integralForm (b 0) (b 1), L.integralNorm (b 1)⟩

/-- The leading coefficient is the first diagonal Gram entry. -/
@[simp]
theorem binaryNormForm_a : (L.binaryNormForm b).a = L.gramMatrix b 0 0 := by
  simp [binaryNormForm, gramMatrix_apply, integralNorm_apply]

/-- The middle coefficient is twice the off-diagonal Gram entry. -/
@[simp]
theorem binaryNormForm_b : (L.binaryNormForm b).b = 2 * L.gramMatrix b 0 1 := by
  simp [binaryNormForm, gramMatrix_apply]

/-- The last coefficient is the second diagonal Gram entry. -/
@[simp]
theorem binaryNormForm_c : (L.binaryNormForm b).c = L.gramMatrix b 1 1 := by
  simp [binaryNormForm, gramMatrix_apply, integralNorm_apply]

/-- The binary form evaluates to the integral norm of the vector with the given coordinates. -/
@[simp]
theorem eval_binaryNormForm (x y : ℤ) :
    (L.binaryNormForm b).eval x y = L.integralNorm (x • b 0 + y • b 1) := by
  simp only [BinaryQuadraticForm.eval_def, binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    gramMatrix_apply, ← integralNorm_apply, integralNorm_add, integralNorm_zsmul,
    map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The same polynomial computes the rational norm in the extended basis. -/
theorem norm_eq_binaryNormForm (z : V) :
    L.norm z = ((L.binaryNormForm b).a : ℚ) * ((b.extendOfIsLattice ℚ).repr z 0) ^ 2 +
      ((L.binaryNormForm b).b : ℚ) * (b.extendOfIsLattice ℚ).repr z 0 *
        (b.extendOfIsLattice ℚ).repr z 1 +
      ((L.binaryNormForm b).c : ℚ) * ((b.extendOfIsLattice ℚ).repr z 1) ^ 2 := by
  let e := b.extendOfIsLattice ℚ
  have hz : e.repr z 0 • e 0 + e.repr z 1 • e 1 = z := by
    simpa only [Fin.sum_univ_two] using e.sum_repr z
  conv_lhs => rw [← hz, norm_add, norm_smul, norm_smul]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, e, Basis.extendOfIsLattice_apply,
    binaryNormForm_a, binaryNormForm_b, binaryNormForm_c, intCast_gramMatrix_apply,
    norm_apply, Int.cast_mul, Int.cast_ofNat]
  ring

/-- The discriminant of the norm form is minus four times the lattice determinant. -/
@[simp]
theorem discrim_binaryNormForm :
    (L.binaryNormForm b).discrim = -4 * L.determinant := by
  have hs := L.isSymm_integralForm.eq (b 0) (b 1)
  rw [L.determinant_eq_gramDet b, gramDet_def, Matrix.det_fin_two,
    BinaryQuadraticForm.discrim_def, discrim]
  simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c, gramMatrix_apply]
  rw [hs]
  ring

/-- An integer divides the content exactly when it divides every integral norm. -/
theorem dvd_content_binaryNormForm_iff (n : ℕ) :
    n ∣ (L.binaryNormForm b).content ↔ ∀ z : L, (n : ℤ) ∣ L.integralNorm z := by
  rw [BinaryQuadraticForm.dvd_content_iff_forall_eval]
  constructor
  · intro h z
    have hz : b.repr z 0 • b 0 + b.repr z 1 • b 1 = z := by
      simpa only [Fin.sum_univ_two] using b.sum_repr z
    rw [← hz, ← eval_binaryNormForm]
    exact h _ _
  · intro h x y
    rw [eval_binaryNormForm]
    exact h _

/-- Changing the carrier basis preserves the content of the norm form. -/
theorem content_binaryNormForm_eq (b' : Basis (Fin 2) ℤ L) :
    (L.binaryNormForm b).content = (L.binaryNormForm b').content := by
  apply Nat.dvd_antisymm
  · rw [dvd_content_binaryNormForm_iff L b', ← dvd_content_binaryNormForm_iff L b]
  · rw [dvd_content_binaryNormForm_iff L b, ← dvd_content_binaryNormForm_iff L b']

/-- The discriminant of the primitive part is independent of the carrier basis. -/
theorem discrim_binaryNormForm_primPart_eq (b' : Basis (Fin 2) ℤ L) :
    (L.binaryNormForm b).primPart.discrim = (L.binaryNormForm b').primPart.discrim := by
  by_cases hc : (L.binaryNormForm b).content = 0
  · have hf := (L.binaryNormForm b).content_eq_zero_iff.mp hc
    have hf' := (L.binaryNormForm b').content_eq_zero_iff.mp
      ((content_binaryNormForm_eq L b b').symm.trans hc)
    rw [hf, hf']
  · have h := (L.binaryNormForm b).discrim_eq_content_sq_mul
    have h' := (L.binaryNormForm b').discrim_eq_content_sq_mul
    rw [discrim_binaryNormForm] at h h'
    rw [← content_binaryNormForm_eq L b b'] at h'
    exact mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hc)) (h.symm.trans h')

/-- A nondegenerate rank-two lattice has a nonzero norm-form discriminant. -/
theorem discrim_binaryNormForm_ne_zero [L.IsNondegenerate] :
    (L.binaryNormForm b).discrim ≠ 0 := by
  rw [discrim_binaryNormForm]
  exact mul_ne_zero (by decide) (L.determinant_ne_zero_iff.mpr L.form_nondegenerate)

/-- The binary norm form vanishes exactly when the ambient lattice form vanishes. -/
@[simp]
theorem binaryNormForm_eq_zero_iff : L.binaryNormForm b = 0 ↔ L.form = 0 := by
  constructor
  · intro hf
    have hnorm (z : V) : L.norm z = 0 := by
      rw [norm_eq_binaryNormForm L b]
      simp [hf]
    ext x y
    simp only [LinearMap.zero_apply]
    have h := L.norm_add x y
    simp only [hnorm] at h
    linarith
  · intro hf
    have hpair (x y : L) : L.integralForm x y = 0 := by
      apply Int.cast_injective (α := ℚ)
      rw [integralForm_cast, hf]
      simp
    ext <;> simp [binaryNormForm, integralNorm_apply, hpair]

/-- A nonzero ambient form has a nonzero binary norm form, including the degenerate case. -/
theorem binaryNormForm_ne_zero (hL : L.form ≠ 0) : L.binaryNormForm b ≠ 0 :=
  (binaryNormForm_eq_zero_iff L b).not.mpr hL

/-- A nonzero ambient form has a binary norm form of positive content. -/
theorem content_binaryNormForm_pos (hL : L.form ≠ 0) : 0 < (L.binaryNormForm b).content :=
  (L.binaryNormForm b).content_pos_iff.mpr (binaryNormForm_ne_zero L b hL)

/-- Dividing the norm form by its content gives a primitive form whenever the ambient form
is nonzero. -/
theorem isPrimitive_binaryNormForm_primPart (hL : L.form ≠ 0) :
    (L.binaryNormForm b).primPart.IsPrimitive :=
  (L.binaryNormForm b).isPrimitive_primPart (binaryNormForm_ne_zero L b hL)

/-- The basis-independent nonnegative content of a rank-two lattice; it is positive for a
nonzero ambient form. -/
noncomputable def binaryContent (hV : Module.finrank ℚ V = 2) : ℕ :=
  (L.binaryNormForm (Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV))).content

/-- The basis-independent discriminant of the primitive norm form of a rank-two lattice. -/
noncomputable def binaryDiscriminant (hV : Module.finrank ℚ V = 2) : ℤ :=
  (L.binaryNormForm (Module.finBasisOfFinrankEq ℤ L
    (L.finrank_carrier.trans hV))).primPart.discrim

/-- The intrinsic content can be computed in any carrier basis. -/
theorem binaryContent_eq_content_binaryNormForm (hV : Module.finrank ℚ V = 2) :
    L.binaryContent hV = (L.binaryNormForm b).content :=
  L.content_binaryNormForm_eq _ b

/-- The intrinsic primitive discriminant can be computed in any carrier basis. -/
theorem binaryDiscriminant_eq_discrim_primPart (hV : Module.finrank ℚ V = 2) :
    L.binaryDiscriminant hV = (L.binaryNormForm b).primPart.discrim :=
  L.discrim_binaryNormForm_primPart_eq _ b

/-- The primitive discriminant times the squared content is minus four times the determinant. -/
theorem binaryContent_sq_mul_binaryDiscriminant (hV : Module.finrank ℚ V = 2) :
    (L.binaryContent hV : ℤ) ^ 2 * L.binaryDiscriminant hV = -4 * L.determinant := by
  let b := Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
  rw [binaryContent_eq_content_binaryNormForm L b hV,
    binaryDiscriminant_eq_discrim_primPart L b hV,
    ← BinaryQuadraticForm.discrim_eq_content_sq_mul, discrim_binaryNormForm]

/-- A rank-two lattice with nonzero ambient form has positive content. -/
theorem binaryContent_pos (hV : Module.finrank ℚ V = 2) (hL : L.form ≠ 0) :
    0 < L.binaryContent hV := by
  let b := Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
  rw [binaryContent_eq_content_binaryNormForm L b hV]
  exact content_binaryNormForm_pos L b hL

/-- The primitive discriminant of a nondegenerate rank-two lattice is nonzero. -/
theorem binaryDiscriminant_ne_zero (hV : Module.finrank ℚ V = 2) [L.IsNondegenerate] :
    L.binaryDiscriminant hV ≠ 0 := by
  intro h
  have he := binaryContent_sq_mul_binaryDiscriminant L hV
  rw [h, mul_zero] at he
  exact (mul_ne_zero (by decide : (-4 : ℤ) ≠ 0)
    (L.determinant_ne_zero_iff.mpr L.form_nondegenerate)) he.symm

/-- An integral primitive discriminant is zero or one modulo four. -/
theorem binaryDiscriminant_emod_four_eq_zero_or_one (hV : Module.finrank ℚ V = 2) :
    L.binaryDiscriminant hV % 4 = 0 ∨ L.binaryDiscriminant hV % 4 = 1 := by
  let b := Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
  rw [binaryDiscriminant_eq_discrim_primPart L b hV,
    BinaryQuadraticForm.discrim_def, Int.discrim_emod_four]
  omega

/-- Twisting the lattice form by an integer scales the associated binary form by that integer. -/
@[simp]
theorem binaryNormForm_smul (n : ℤ) :
    (n • L).binaryNormForm b = n • L.binaryNormForm b := by
  ext <;> simp
  ring

/-- A form twist multiplies the lattice content by the absolute scalar. -/
@[simp]
theorem binaryContent_smul (n : ℤ) (hV : Module.finrank ℚ V = 2) :
    (n • L).binaryContent hV = n.natAbs * L.binaryContent hV := by
  let b := Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
  rw [binaryContent_eq_content_binaryNormForm (n • L) b hV,
    binaryContent_eq_content_binaryNormForm L b hV, binaryNormForm_smul,
    BinaryQuadraticForm.content_smul']

/-- The primitive discriminant of a positive definite rank-two lattice is negative. -/
theorem binaryDiscriminant_neg_of_isPosDef (hV : Module.finrank ℚ V = 2)
    (hL : L.IsPosDef) : L.binaryDiscriminant hV < 0 := by
  let b := Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
  have hdet : 0 < L.determinant := by
    have hm := (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
      (b.extendOfIsLattice ℚ) L.form L.isSymm).mp hL
    rw [L.determinant_eq_gramDet b]
    exact_mod_cast (L.intCast_gramDet b).symm ▸ hm.det_pos
  have he := L.binaryContent_sq_mul_binaryDiscriminant hV
  have hsq := sq_nonneg (L.binaryContent hV : ℤ)
  nlinarith

/-- Negating the lattice form preserves the primitive discriminant. -/
@[simp]
theorem binaryDiscriminant_neg (hV : Module.finrank ℚ V = 2) :
    (-L).binaryDiscriminant hV = L.binaryDiscriminant hV := by
  let b := Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
  rw [neg_def, binaryDiscriminant_eq_discrim_primPart ((-1 : ℤ) • L) b hV,
    binaryDiscriminant_eq_discrim_primPart L b hV, binaryNormForm_smul, neg_one_smul,
    BinaryQuadraticForm.primPart_neg]
  simpa only [neg_one_smul, neg_one_sq, one_mul] using
    BinaryQuadraticForm.discrim_smul' (-1 : ℤ) (L.binaryNormForm b).primPart

/-- The primitive discriminant of a negative definite rank-two lattice is negative. -/
theorem binaryDiscriminant_neg_of_isNegDef (hV : Module.finrank ℚ V = 2)
    (hL : L.IsNegDef) : L.binaryDiscriminant hV < 0 := by
  have hneg : (-L).IsPosDef := by
    rw [(-L).isPosDef_iff]
    intro x hx
    simpa only [neg_form, LinearMap.neg_apply, neg_pos] using L.isNegDef_iff.mp hL x hx
  rw [← binaryDiscriminant_neg L hV]
  exact (-L).binaryDiscriminant_neg_of_isPosDef hV hneg

/-- The primitive discriminant of an indefinite rank-two lattice is positive. -/
theorem binaryDiscriminant_pos_of_isIndefinite (hV : Module.finrank ℚ V = 2)
    (hL : L.IsIndefinite) : 0 < L.binaryDiscriminant hV := by
  let b := Module.finBasisOfFinrankEq ℤ L (L.finrank_carrier.trans hV)
  obtain ⟨⟨xp, hp⟩, ⟨xn, hn⟩⟩ := L.isIndefinite_iff_exists_pos_and_exists_neg.mp hL
  rw [← norm_apply, norm_eq_binaryNormForm L b] at hp hn
  have hd := discrim_pos_of_exists_pos_of_exists_neg
    ⟨_, _, hp⟩ ⟨_, _, hn⟩
  have hi : 0 < (L.binaryNormForm b).discrim := by
    rw [discrim] at hd
    rw [BinaryQuadraticForm.discrim_def, discrim]
    exact_mod_cast hd
  rw [BinaryQuadraticForm.discrim_eq_content_sq_mul] at hi
  rw [binaryDiscriminant_eq_discrim_primPart L b hV]
  exact ((mul_pos_iff.mp hi).resolve_right (fun h ↦ (sq_nonneg _).not_gt h.1)).2

end TauCeti.IntegralLattice
