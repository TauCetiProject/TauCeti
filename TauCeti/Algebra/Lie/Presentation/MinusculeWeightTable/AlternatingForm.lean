/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import TauCeti.LinearAlgebra.Matrix.Alternating

/-!
# Alternating forms from signed opposition of minuscule weights

An opposition pairs each weight with its negative. Signs which reverse on opposite weights
and nontrivial simple reflections define an alternating form preserved by the root operators.
The construction works over every commutative ring, including characteristic two.

The type E7 minuscule carrier supplies these data from its existing weight and parent tables.
-/

public section

open scoped Matrix

namespace TauCeti.MinusculeWeightTable

variable {B ι : Type*} (T : MinusculeWeightTable B ι)

/-- An opposition of the weight table, with signs compatible with opposition and reflections. -/
structure SignedOpposition where
  /-- The index of the negative of a weight. -/
  opposition : ι → ι
  /-- Opposition negates every simple-coroot coordinate. -/
  weight_opposition : ∀ a i, T.weight (opposition a) i = -T.weight a i
  /-- Integral signs on the weight indices. -/
  sign : ι → ℤ
  /-- Every sign squares to one. -/
  sign_mul_self : ∀ a, sign a * sign a = 1
  /-- Opposite weights have opposite signs. -/
  sign_opposition : ∀ a, sign (opposition a) = -sign a
  /-- Nontrivial simple reflections reverse signs. -/
  sign_reflection : ∀ i a, T.weight a i ≠ 0 →
    sign (T.reflection i a) = -sign a

namespace SignedOpposition

variable {T} (s : T.SignedOpposition)

@[simp]
theorem opposition_apply_apply (a : ι) : s.opposition (s.opposition a) = a := by
  apply T.weight_injective
  funext i
  simp only [s.weight_opposition, neg_neg]

theorem opposition_injective : Function.Injective s.opposition :=
  Function.Involutive.injective s.opposition_apply_apply

theorem opposition_eq_iff (a b : ι) : s.opposition a = b ↔ a = s.opposition b := by
  constructor <;> intro h
  · rw [← h, s.opposition_apply_apply]
  · rw [h, s.opposition_apply_apply]

@[simp]
theorem opposition_reflection (i : B) (a : ι) :
    s.opposition (T.reflection i a) = T.reflection i (s.opposition a) := by
  apply T.weight_injective
  funext j
  simp only [s.weight_opposition, T.weight_reflection]
  ring

theorem opposition_ne_self (a : ι) : s.opposition a ≠ a := by
  intro h
  have hn := s.sign_opposition a
  rw [h] at hn
  have hz : s.sign a = 0 := by omega
  have hsq := s.sign_mul_self a
  simp [hz] at hsq

variable (R : Type*) [CommRing R] [DecidableEq ι]

/-- The signed pairing of each weight with its opposite. -/
def form : Matrix ι ι R := fun a b ↦ if b = s.opposition a then s.sign a else 0

@[simp]
theorem form_apply_opposition (a : ι) : s.form R a (s.opposition a) = s.sign a := by
  simp [form]

@[simp]
theorem form_apply_of_ne {a b : ι} (h : b ≠ s.opposition a) : s.form R a b = 0 := by
  simp [form, h]

@[simp]
theorem form_apply_self (a : ι) : s.form R a a = 0 := by
  simp [form, Ne.symm (s.opposition_ne_self a)]

/-- The signed form commutes with a change of coefficient ring. -/
@[simp]
theorem form_map {S : Type*} [CommRing S] (f : R →+* S) :
    (s.form R).map f = s.form S := by
  ext a b
  by_cases h : b = s.opposition a <;> simp [form, h]

variable [Fintype ι]

/-- Left multiplication by the form selects the opposite row. -/
theorem form_mul_apply (M : Matrix ι ι R) (a b : ι) :
    (s.form R * M) a b = (s.sign a : R) * M (s.opposition a) b := by
  simp [Matrix.mul_apply, form, ite_mul]

/-- Right multiplication by the form selects the opposite column. -/
theorem mul_form_apply (M : Matrix ι ι R) (a b : ι) :
    (M * s.form R) a b = M a (s.opposition b) * (s.sign (s.opposition b) : R) := by
  simp only [Matrix.mul_apply, form, mul_ite, mul_zero]
  have h (k : ι) : b = s.opposition k ↔ k = s.opposition b := by
    rw [eq_comm, s.opposition_eq_iff]
  simp_rw [h]
  simp

omit [Fintype ι] in
@[simp]
theorem form_transpose : (s.form R)ᵀ = -s.form R := by
  ext a b
  by_cases h : b = s.opposition a
  · subst b
    simp [Matrix.transpose_apply, form, s.sign_opposition]
  · have h' : a ≠ s.opposition b := by
      intro hab
      exact h ((s.opposition_eq_iff b a).mp hab.symm)
    simp [Matrix.transpose_apply, form, h, h']

/-- The form is unimodular, with inverse its negative. -/
@[simp]
theorem form_mul_self : s.form R * s.form R = -1 := by
  ext a b
  rw [s.form_mul_apply]
  by_cases h : b = a
  · subst b
    simp [form, s.sign_opposition, ← Int.cast_mul, s.sign_mul_self]
  · simp [form, h, Ne.symm h]

/-- The form is alternating even when two is not invertible. -/
theorem dotProduct_form_mulVec_self (x : ι → R) :
    dotProduct x ((s.form R).mulVec x) = 0 := by
  have hm (a : ι) : ((s.form R).mulVec x) a =
      (s.sign a : R) * x (s.opposition a) := by
    simp [Matrix.mulVec, dotProduct, form, ite_mul]
  simp_rw [dotProduct, hm]
  apply Finset.sum_ninvolution s.opposition
  · intro a
    simp only [s.opposition_apply_apply, s.sign_opposition, Int.cast_neg]
    ring
  · intro a _
    exact s.opposition_ne_self a
  · intro a
    exact Finset.mem_univ _
  · exact s.opposition_apply_apply

private theorem rootMatrix_mul_form_add_transpose (i : B) (q : ℤ) (hq : q ≠ 0) :
    let Y : Matrix ι ι R := fun a b ↦
      if T.weight b i = q ∧ a = T.reflection i b then 1 else 0
    Y * s.form R + s.form R * Yᵀ = 0 := by
  intro Y
  have hr (a b : ι) (h : a = T.reflection i (s.opposition b)) :
      b = T.reflection i (s.opposition a) := by
    rw [h, s.opposition_reflection, s.opposition_apply_apply, T.reflection_apply_apply]
  ext a b
  have hc : (T.weight (s.opposition b) i = q ∧ a = T.reflection i (s.opposition b)) ↔
      (T.weight (s.opposition a) i = q ∧ b = T.reflection i (s.opposition a)) := by
    constructor
    · rintro ⟨hw, h⟩
      refine ⟨?_, hr a b h⟩
      rw [h, s.weight_opposition, T.weight_reflection_self, neg_neg]
      exact hw
    · rintro ⟨hw, h⟩
      refine ⟨?_, hr b a h⟩
      rw [h, s.weight_opposition, T.weight_reflection_self, neg_neg]
      exact hw
  rw [Matrix.add_apply, s.mul_form_apply, s.form_mul_apply, Matrix.transpose_apply]
  by_cases h : T.weight (s.opposition b) i = q ∧ a = T.reflection i (s.opposition b)
  · have hsign : s.sign a = -s.sign (s.opposition b) := by
      rw [h.2]
      exact s.sign_reflection i _ (by rw [h.1]; exact hq)
    simp only [Y, ite_eq_left h, ite_eq_left (hc.mp h), one_mul, mul_one, hsign,
      Int.cast_neg, add_neg_cancel, Matrix.zero_apply]
  · simp only [Y, ite_eq_right h, ite_eq_right (mt hc.mpr h), zero_mul, mul_zero, add_zero,
      Matrix.zero_apply]

/-- Raising operators are skew-adjoint for the signed opposition form. -/
theorem raisingMatrix_mul_form_add_transpose (i : B) :
    (T.raisingMatrix i).map (Int.cast : ℤ → R) * s.form R +
      s.form R * ((T.raisingMatrix i).map (Int.cast : ℤ → R))ᵀ = 0 := by
  have hM : (T.raisingMatrix i).map (Int.cast : ℤ → R) =
      fun a b ↦ if T.weight b i = (-1) ∧ a = T.reflection i b then 1 else 0 := by
    ext a b
    simp
  rw [hM]
  exact s.rootMatrix_mul_form_add_transpose R i (-1) (by decide)

/-- Lowering operators are skew-adjoint for the signed opposition form. -/
theorem loweringMatrix_mul_form_add_transpose (i : B) :
    (T.loweringMatrix i).map (Int.cast : ℤ → R) * s.form R +
      s.form R * ((T.loweringMatrix i).map (Int.cast : ℤ → R))ᵀ = 0 := by
  have hM : (T.loweringMatrix i).map (Int.cast : ℤ → R) =
      fun a b ↦ if T.weight b i = 1 ∧ a = T.reflection i b then 1 else 0 := by
    ext a b
    simp
  rw [hM]
  exact s.rootMatrix_mul_form_add_transpose R i 1 (by decide)

/-- Every raising unipotent preserves the form over every commutative ring. -/
theorem one_add_smul_raisingMatrix_preserves_form (i : B) (t : R) :
    (1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → R)) * s.form R *
      (1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → R))ᵀ = s.form R := by
  apply Matrix.one_add_smul_mul_mul_transpose
  · exact s.raisingMatrix_mul_form_add_transpose R i
  · have h := congrArg (RingHom.mapMatrix (Int.castRingHom R)) (T.raisingMatrix_pow_two i)
    rw [map_pow, map_zero] at h
    simpa only [RingHom.mapMatrix_apply, Int.coe_castRingHom, pow_two] using h

/-- Every lowering unipotent preserves the form over every commutative ring. -/
theorem one_add_smul_loweringMatrix_preserves_form (i : B) (t : R) :
    (1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → R)) * s.form R *
      (1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → R))ᵀ = s.form R := by
  apply Matrix.one_add_smul_mul_mul_transpose
  · exact s.loweringMatrix_mul_form_add_transpose R i
  · have h := congrArg (RingHom.mapMatrix (Int.castRingHom R)) (T.loweringMatrix_pow_two i)
    rw [map_pow, map_zero] at h
    simpa only [RingHom.mapMatrix_apply, Int.coe_castRingHom, pow_two] using h

end SignedOpposition

end TauCeti.MinusculeWeightTable
