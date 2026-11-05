/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import TauCeti.LinearAlgebra.Matrix.SkewAdjoint

/-!
# Alternating forms from signed negation of minuscule weights

A negation index of a minuscule weight table pairs each weight with its negative. Signs which
reverse under negation and under nontrivial simple reflections define a matrix with the sign of
`a` at the entry `(a, indexNeg a)` and zero elsewhere. This matrix is skew, squares to `-1`, and
is alternating over every commutative ring, including in characteristic two, where alternation
is proved by cancelling each index against its negation. The raising and lowering matrices `X`
satisfy `X J + J Xᵀ = 0` for this matrix `J`, so their unipotents `1 + t X` preserve it.

## Main definitions

* `TauCeti.MinusculeWeightTable.SignedNegation`: a negation index with compatible signs.
* `TauCeti.MinusculeWeightTable.SignedNegation.form`: the signed pairing matrix, with entries
  `form_apply` and action on vectors `form_mulVec_apply`.

## Main results

* `TauCeti.MinusculeWeightTable.SignedNegation.indexNeg_involutive` and
  `indexNeg_eq_iff_weight_eq_neg`: the negation index is an involution, characterized by the
  negated weight.
* `TauCeti.MinusculeWeightTable.SignedNegation.form_transpose` and `form_mul_self`: the form is
  skew and squares to `-1`.
* `TauCeti.MinusculeWeightTable.SignedNegation.isUnit_form`: the form is a unit.
* `TauCeti.MinusculeWeightTable.SignedNegation.dotProduct_form_mulVec_self`: the form is
  alternating.
* `TauCeti.MinusculeWeightTable.SignedNegation.one_add_smul_raisingMatrix_preserves_form` and
  `one_add_smul_loweringMatrix_preserves_form`: the root unipotents preserve the form.

## References

* The root unipotents preserve the form by `Matrix.one_add_smul_mul_mul_transpose`, applied to
  the identities `X J + J Xᵀ = 0` and `X * X = 0` of the raising and lowering matrices; the
  signed negation and the pair-cancellation proof of alternation are specific to this file.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)

/-- A negation index of the weight table, with signs compatible with negation and reflections. -/
structure SignedNegation where
  /-- The index of the negative of a weight. -/
  indexNeg : ι → ι
  /-- The negation index negates every simple-coroot coordinate. -/
  weight_indexNeg : ∀ a i, T.weight (indexNeg a) i = -T.weight a i
  /-- Integral signs on the weight indices. -/
  sign : ι → ℤ
  /-- Every sign squares to one. -/
  sign_mul_self : ∀ a, sign a * sign a = 1
  /-- Negated weights have opposite signs. -/
  sign_indexNeg : ∀ a, sign (indexNeg a) = -sign a
  /-- Nontrivial simple reflections reverse signs. -/
  sign_reflection : ∀ i a, T.weight a i ≠ 0 →
    sign (T.reflection i a) = -sign a

attribute [simp] SignedNegation.weight_indexNeg SignedNegation.sign_indexNeg
  SignedNegation.sign_mul_self

namespace SignedNegation

variable {T} (s : T.SignedNegation)

/-- The negation index is determined by the weights, so equal signs give equal data. -/
@[ext]
theorem ext {s₁ s₂ : T.SignedNegation} (h : ∀ a, s₁.sign a = s₂.sign a) : s₁ = s₂ := by
  obtain ⟨n₁, hn₁, σ₁, _, _, _⟩ := s₁
  obtain ⟨n₂, hn₂, σ₂, _, _, _⟩ := s₂
  obtain rfl : n₁ = n₂ :=
    funext fun a ↦ T.weight_injective (funext fun i ↦ by rw [hn₁, hn₂])
  obtain rfl : σ₁ = σ₂ := funext h
  rfl

/-- The negation index of `a` is the unique index whose weight is `-T.weight a`. -/
theorem indexNeg_eq_iff_weight_eq_neg (a b : ι) :
    s.indexNeg a = b ↔ T.weight b = -T.weight a := by
  constructor
  · rintro rfl
    funext i
    exact s.weight_indexNeg a i
  · intro h
    apply T.weight_injective
    funext i
    rw [h, Pi.neg_apply, s.weight_indexNeg]

@[simp]
theorem indexNeg_indexNeg (a : ι) : s.indexNeg (s.indexNeg a) = a := by
  apply T.weight_injective
  funext i
  simp only [s.weight_indexNeg, neg_neg]

/-- The negation index is an involution. -/
theorem indexNeg_involutive : Function.Involutive s.indexNeg :=
  s.indexNeg_indexNeg

@[simp]
theorem indexNeg_reflection (i : B) (a : ι) :
    s.indexNeg (T.reflection i a) = T.reflection i (s.indexNeg a) := by
  apply T.weight_injective
  funext j
  simp only [s.weight_indexNeg, T.weight_reflection]
  ring

theorem indexNeg_ne_self (a : ι) : s.indexNeg a ≠ a := by
  intro h
  have hn := s.sign_indexNeg a
  rw [h] at hn
  have hz : s.sign a = 0 := by omega
  have hsq := s.sign_mul_self a
  simp [hz] at hsq

variable (R : Type*) [CommRing R] [DecidableEq ι]

/-- The signed pairing of each weight with its negative. -/
def form : Matrix ι ι R := Matrix.of fun a b ↦ if b = s.indexNeg a then (s.sign a : R) else 0

/-- The entry of the form at `(a, b)` is the sign of `a` when `b` is the negation index of `a`,
and zero otherwise. -/
theorem form_apply (a b : ι) :
    s.form R a b = if b = s.indexNeg a then (s.sign a : R) else 0 := by
  rw [form, Matrix.of_apply]

/-- The form pairs each index with its negation index, with the sign of the index. -/
@[simp]
theorem form_apply_indexNeg (a : ι) : s.form R a (s.indexNeg a) = s.sign a := by
  rw [form_apply, ite_eq_left rfl]

/-- The form vanishes off the negation pairs. -/
@[simp]
theorem form_apply_of_ne {a b : ι} (h : b ≠ s.indexNeg a) : s.form R a b = 0 := by
  rw [form_apply, ite_eq_right h]

/-- The form vanishes on the diagonal. -/
@[simp]
theorem form_apply_self (a : ι) : s.form R a a = 0 :=
  s.form_apply_of_ne R (s.indexNeg_ne_self a).symm

/-- The signed form commutes with a change of coefficient ring. -/
@[simp]
theorem form_map {S : Type*} [CommRing S] (f : R →+* S) :
    (s.form R).map f = s.form S := by
  ext a b
  rw [Matrix.map_apply, form_apply, form_apply]
  split_ifs
  · exact map_intCast f _
  · exact map_zero f

variable [Fintype ι]

/-- Left multiplication by the form selects the negated row. -/
theorem form_mul_apply (M : Matrix ι ι R) (a b : ι) :
    (s.form R * M) a b = (s.sign a : R) * M (s.indexNeg a) b := by
  simp [Matrix.mul_apply, form_apply, ite_mul]

/-- Right multiplication by the form selects the negated column. -/
theorem mul_form_apply (M : Matrix ι ι R) (a b : ι) :
    (M * s.form R) a b = M a (s.indexNeg b) * (s.sign (s.indexNeg b) : R) := by
  simp only [Matrix.mul_apply, form_apply, mul_ite, mul_zero]
  have h (k : ι) : b = s.indexNeg k ↔ k = s.indexNeg b := by
    rw [eq_comm, s.indexNeg_involutive.eq_iff]
  simp_rw [h]
  simp

omit [Fintype ι] in
/-- The form is skew: its transpose is its negative. -/
@[simp]
theorem form_transpose : (s.form R)ᵀ = -s.form R := by
  ext a b
  rw [Matrix.transpose_apply, Matrix.neg_apply, form_apply, form_apply]
  by_cases h : b = s.indexNeg a
  · subst h
    rw [ite_eq_left (s.indexNeg_indexNeg a).symm, ite_eq_left rfl, s.sign_indexNeg, Int.cast_neg]
  · have h' : a ≠ s.indexNeg b := fun hab ↦ h (s.indexNeg_involutive.eq_iff.mp hab.symm)
    rw [ite_eq_right h', ite_eq_right h, neg_zero]

/-- The form is unimodular, with inverse its negative. -/
@[simp]
theorem form_mul_self : s.form R * s.form R = -1 := by
  ext a b
  rw [s.form_mul_apply, form_apply, Matrix.neg_apply, Matrix.one_apply]
  by_cases h : b = a
  · rw [h, ite_eq_left (s.indexNeg_indexNeg a).symm, ite_eq_left rfl, s.sign_indexNeg, Int.cast_neg,
      mul_neg, ← Int.cast_mul, s.sign_mul_self, Int.cast_one]
  · have h' : b ≠ s.indexNeg (s.indexNeg a) := by
      rw [s.indexNeg_indexNeg]
      exact h
    rw [ite_eq_right h', ite_eq_right (Ne.symm h), mul_zero, neg_zero]

/-- The signed form is a unit, with inverse its negative. -/
theorem isUnit_form : IsUnit (s.form R) :=
  Matrix.isUnit_of_mul_self_eq_neg_one (s.form_mul_self R)

/-- The form sends a vector to the signed vector of its negated coordinates. -/
theorem form_mulVec_apply (x : ι → R) (a : ι) :
    (s.form R).mulVec x a = (s.sign a : R) * x (s.indexNeg a) := by
  simp [Matrix.mulVec, dotProduct, form_apply, ite_mul]

/-- The form is alternating even when two is not invertible. -/
@[simp]
theorem dotProduct_form_mulVec_self (x : ι → R) :
    dotProduct x ((s.form R).mulVec x) = 0 := by
  simp_rw [dotProduct, s.form_mulVec_apply]
  apply Finset.sum_ninvolution s.indexNeg
  · intro a
    simp only [s.indexNeg_indexNeg, s.sign_indexNeg, Int.cast_neg]
    ring
  · intro a _
    exact s.indexNeg_ne_self a
  · intro a
    exact Finset.mem_univ _
  · exact s.indexNeg_indexNeg

private theorem rootMatrix_mul_form_add_eq_zero (i : B) (q : ℤ) (hq : q ≠ 0) (Y : Matrix ι ι R)
    (hY : ∀ a b, Y a b = if T.weight b i = q ∧ a = T.reflection i b then 1 else 0) :
    Y * s.form R + s.form R * Yᵀ = 0 := by
  have key (a b : ι) (h : T.weight (s.indexNeg b) i = q ∧ a = T.reflection i (s.indexNeg b)) :
      T.weight (s.indexNeg a) i = q ∧ b = T.reflection i (s.indexNeg a) := by
    obtain ⟨hw, h⟩ := h
    refine ⟨?_, ?_⟩
    · rw [h, s.weight_indexNeg, T.weight_reflection_self, neg_neg]
      exact hw
    · rw [h, s.indexNeg_reflection, s.indexNeg_indexNeg, T.reflection_apply_apply]
  ext a b
  have hc := Iff.intro (key a b) (key b a)
  rw [Matrix.add_apply, s.mul_form_apply, s.form_mul_apply, Matrix.transpose_apply, hY, hY,
    Matrix.zero_apply]
  by_cases h : T.weight (s.indexNeg b) i = q ∧ a = T.reflection i (s.indexNeg b)
  · have hsign : s.sign a = -s.sign (s.indexNeg b) := by
      rw [h.2]
      exact s.sign_reflection i _ (by rw [h.1]; exact hq)
    rw [ite_eq_left h, ite_eq_left (hc.mp h), one_mul, mul_one, hsign, Int.cast_neg,
      add_neg_cancel]
  · rw [ite_eq_right h, ite_eq_right (mt hc.mpr h), zero_mul, mul_zero, add_zero]

/-- The raising matrix `X` satisfies `X J + J Xᵀ = 0` for the signed negation form `J`. -/
theorem raisingMatrix_map_mul_form_add_eq_zero (i : B) :
    (T.raisingMatrix i).map (Int.cast : ℤ → R) * s.form R +
      s.form R * ((T.raisingMatrix i).map (Int.cast : ℤ → R))ᵀ = 0 :=
  s.rootMatrix_mul_form_add_eq_zero R i (-1) (by decide) _ fun a b ↦ by
    rw [Matrix.map_apply, T.raisingMatrix_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]

/-- The lowering matrix `X` satisfies `X J + J Xᵀ = 0` for the signed negation form `J`. -/
theorem loweringMatrix_map_mul_form_add_eq_zero (i : B) :
    (T.loweringMatrix i).map (Int.cast : ℤ → R) * s.form R +
      s.form R * ((T.loweringMatrix i).map (Int.cast : ℤ → R))ᵀ = 0 :=
  s.rootMatrix_mul_form_add_eq_zero R i 1 (by decide) _ fun a b ↦ by
    rw [Matrix.map_apply, T.loweringMatrix_apply, Int.cast_ite, Int.cast_one, Int.cast_zero]

/-- Every raising unipotent preserves the form over every commutative ring. -/
theorem one_add_smul_raisingMatrix_preserves_form (i : B) (t : R) :
    (1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → R)) * s.form R *
      (1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → R))ᵀ = s.form R :=
  Matrix.one_add_smul_mul_mul_transpose _ _ t (s.raisingMatrix_map_mul_form_add_eq_zero R i)
    (T.raisingMatrix_map_mul_self i)

/-- Every lowering unipotent preserves the form over every commutative ring. -/
theorem one_add_smul_loweringMatrix_preserves_form (i : B) (t : R) :
    (1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → R)) * s.form R *
      (1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → R))ᵀ = s.form R :=
  Matrix.one_add_smul_mul_mul_transpose _ _ t (s.loweringMatrix_map_mul_form_add_eq_zero R i)
    (T.loweringMatrix_map_mul_self i)

end SignedNegation

end TauCeti.MinusculeWeightTable
