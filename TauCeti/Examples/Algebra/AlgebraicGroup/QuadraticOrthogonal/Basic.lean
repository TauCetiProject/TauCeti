/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic

/-!
# Examples of orthogonal group schemes of quadratic forms

The Checks of ReductiveGroups §9B.6 on the orthogonal group scheme `O(q)` of a quadratic form
(`TauCeti.QuadraticOrthogonal.groupScheme`), whose points over `A` are
`TauCeti.QuadraticOrthogonal.pointsSubgroup`.

* Over `𝔽₂` with `q = x²`, the polar form vanishes, so every element of `GL₁` preserves it, while
  `O(q)(A) = {a : a² = 1} = μ₂(A)`: in characteristic two `O(q)` is not the isometry group of the
  polar form.
* Over `𝔽₂` with `q = xy`, `O(q)(𝔽₂)` consists of the identity and the swap `s`, and
  `det s = -1 = 1`.
* Over `ℤ`, the root map `x_{ε₁}(a) = I + 2a E₁₂ - a E₂₃ - a² E₁₃` preserves `q₃ = x₁x₃ + x₂²`
  over every commutative ring, so it is a point of `O(q₃)`.
-/

public section

open Matrix QuadraticForm

namespace TauCeti.QuadraticOrthogonal

/-! ### `q = x²` over `𝔽₂` -/

/-- The form `q = x²` on `𝔽₂`, as a form on `Fin 1 → 𝔽₂`. -/
noncomputable abbrev squareForm : QuadraticForm (ZMod 2) (Fin 1 → ZMod 2) :=
  QuadraticMap.proj 0 0

/-- The polar form of `x²` over `𝔽₂` vanishes. -/
example (x y : Fin 1 → ZMod 2) : QuadraticMap.polar squareForm x y = 0 := by
  simp only [QuadraticMap.polar, QuadraticMap.proj_apply, Pi.add_apply]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]

/-- `q_A(x) = x²` for `q = x²` over `𝔽₂`. -/
theorem baseChangeForm_squareForm {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : Fin 1 → A) : baseChangeForm squareForm A x = x 0 ^ 2 := by
  simp [baseChangeForm_apply, coefficientMatrix_apply, dotProduct, mulVec, pow_two]

/-- **`O(x²) = μ₂` over `𝔽₂`**: an invertible `1 × 1` matrix preserves `x²` exactly when its
entry squares to `1`. -/
example {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (g : GL (Fin 1) A) :
    g ∈ pointsSubgroup (ZMod 2) 1 squareForm A ↔ (g : Matrix (Fin 1) (Fin 1) A) 0 0 ^ 2 = 1 := by
  simp only [mem_pointsSubgroup_iff, baseChangeForm_squareForm]
  refine ⟨fun h ↦ by simpa [mulVec, dotProduct] using h fun _ ↦ 1, fun h x ↦ ?_⟩
  simp only [mulVec, dotProduct, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  rw [mul_pow, h, one_mul]

/-! ### `q = xy` over `𝔽₂` -/

/-- The form `q = xy` on `𝔽₂²`. -/
noncomputable abbrev hyperbolicForm : QuadraticForm (ZMod 2) (Fin 2 → ZMod 2) :=
  QuadraticMap.proj 0 1

/-- `q_A(x) = x₀ x₁` for `q = xy` over `𝔽₂`. -/
theorem baseChangeForm_hyperbolicForm {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (x : Fin 2 → A) : baseChangeForm hyperbolicForm A x = x 0 * x 1 := by
  simp [baseChangeForm_apply, coefficientMatrix_apply, dotProduct, mulVec, Fin.sum_univ_two,
    QuadraticMap.polar]

/-- **`O(xy)(𝔽₂) = {1, s}`**: over `𝔽₂`, an invertible `2 × 2` matrix preserves `xy` exactly
when it is the identity or the swap of the two coordinates. -/
example (g : GL (Fin 2) (ZMod 2)) :
    g ∈ pointsSubgroup (ZMod 2) 2 hyperbolicForm (ZMod 2) ↔
      (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 ∨
        (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 0] := by
  simp only [mem_pointsSubgroup_iff, baseChangeForm_hyperbolicForm]
  set M := (g : Matrix (Fin 2) (Fin 2) (ZMod 2))
  have key : ∀ a b c d : ZMod 2,
      ((∀ x : Fin 2 → ZMod 2, (a * x 0 + b * x 1) * (c * x 0 + d * x 1) = x 0 * x 1) ↔
        (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0)) := by
    decide
  have hM : M = !![M 0 0, M 0 1; M 1 0, M 1 1] := eta_fin_two M
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![1, 0; 0, 1] := eta_fin_two _
  have hx : ∀ x : Fin 2 → ZMod 2, (M *ᵥ x) 0 * (M *ᵥ x) 1 =
      (M 0 0 * x 0 + M 0 1 * x 1) * (M 1 0 * x 0 + M 1 1 * x 1) := fun x ↦ by
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  simp only [hx]
  rw [key, hM, h1]
  simp only [Matrix.of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one, ← Matrix.ext_iff, Fin.forall_fin_two]
  tauto

/-- The swap has determinant `-1 = 1` over `𝔽₂`, so `ker(det)` does not cut out `SO(q)` there. -/
example : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2)).det = 1 := by
  rw [det_fin_two_of]
  decide

/-! ### The root map `x_{ε₁}` of `q₃` -/

/-- The split form `q₃ = x₁x₃ + x₂²` on `ℤ³`. -/
noncomputable abbrev splitFormThree : QuadraticForm ℤ (Fin 3 → ℤ) :=
  QuadraticMap.proj 0 2 + QuadraticMap.proj 1 1

/-- `q₃(x) = x₁x₃ + x₂²` over every commutative ring. -/
theorem baseChangeForm_splitFormThree {A : Type*} [CommRing A] (x : Fin 3 → A) :
    baseChangeForm splitFormThree A x = x 0 * x 2 + x 1 ^ 2 := by
  simp +decide [baseChangeForm_apply, coefficientMatrix_apply, dotProduct, mulVec,
    Fin.sum_univ_three, QuadraticMap.polar]
  ring

/-- **The root map `x_{ε₁}(a)` preserves `q₃`**: the image of `(x₁, x₂, x₃)` is
`(x₁ + 2a x₂ - a² x₃, x₂ - a x₃, x₃)`, and
`(x₁ + 2a x₂ - a² x₃) x₃ + (x₂ - a x₃)² = x₁x₃ + x₂²`. -/
theorem baseChangeForm_splitFormThree_rootMap {A : Type*} [CommRing A] (a : A) (x : Fin 3 → A) :
    baseChangeForm splitFormThree A (!![1, 2 * a, -a ^ 2; 0, 1, -a; 0, 0, 1] *ᵥ x) =
      baseChangeForm splitFormThree A x := by
  simp only [baseChangeForm_splitFormThree]
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- The root map `x_{ε₁}(a)` is a point of `O(q₃)` over every commutative ring. -/
example {A : Type*} [CommRing A] (a : A) :
    nonsingInvUnit !![1, 2 * a, -a ^ 2; 0, 1, -a; 0, 0, 1] (by simp [det_fin_three]) ∈
      pointsSubgroup ℤ 3 splitFormThree A :=
  (mem_pointsSubgroup_iff _).2 (baseChangeForm_splitFormThree_rootMap a)

end TauCeti.QuadraticOrthogonal
