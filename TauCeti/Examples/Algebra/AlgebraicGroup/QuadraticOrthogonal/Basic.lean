/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic

/-!
# Examples of orthogonal group schemes of quadratic forms

Checks on the orthogonal group scheme `O(q)` of a quadratic form `q`
(`TauCeti.QuadraticOrthogonal.groupScheme`), whose points over `A` are
`TauCeti.QuadraticOrthogonal.pointsSubgroup`. The forms are coordinate products
`QuadraticMap.proj i j` and their sums.

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

/-- The polar form of `q = x²` over `𝔽₂` vanishes. -/
example (x y : Fin 1 → ZMod 2) :
    QuadraticMap.polar (QuadraticMap.proj 0 0 : QuadraticForm (ZMod 2) (Fin 1 → ZMod 2)) x y =
      0 := by
  simp only [QuadraticMap.polar, QuadraticMap.proj_apply, Pi.add_apply]
  linear_combination (x 0 * y 0) * CharTwo.two_eq_zero (R := ZMod 2)

/-- **`O(x²) = μ₂` over `𝔽₂`**: an invertible `1 × 1` matrix preserves `q = x²` exactly when its
entry squares to `1`. -/
example {A : Type*} [CommRing A] [Algebra (ZMod 2) A] (g : GL (Fin 1) A) :
    g ∈ pointsSubgroup (ZMod 2) 1 (QuadraticMap.proj 0 0) A ↔
      (g : Matrix (Fin 1) (Fin 1) A) 0 0 ^ 2 = 1 := by
  simp only [mem_pointsSubgroup_iff, baseChangeForm_proj, QuadraticMap.proj_apply]
  refine ⟨fun h ↦ by simpa [mulVec, dotProduct, sq] using h fun _ ↦ 1, fun h x ↦ ?_⟩
  simp [mulVec, dotProduct, ← sq, mul_pow, h]

/-! ### `q = xy` over `𝔽₂` -/

/-- **`O(xy)(𝔽₂) = {1, s}`**: over `𝔽₂`, an invertible `2 × 2` matrix preserves `q = xy` exactly
when it is the identity or the swap of the two coordinates. -/
example (g : GL (Fin 2) (ZMod 2)) :
    g ∈ pointsSubgroup (ZMod 2) 2 (QuadraticMap.proj 0 1) (ZMod 2) ↔
      (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 ∨
        (g : Matrix (Fin 2) (Fin 2) (ZMod 2)) = !![0, 1; 1, 0] := by
  simp only [mem_pointsSubgroup_iff, baseChangeForm_proj, QuadraticMap.proj_apply]
  set M := (g : Matrix (Fin 2) (Fin 2) (ZMod 2))
  have key : ∀ a b c d : ZMod 2,
      ((∀ x : Fin 2 → ZMod 2, (a * x 0 + b * x 1) * (c * x 0 + d * x 1) = x 0 * x 1) ↔
        (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0)) := by
    decide
  have hx : ∀ x : Fin 2 → ZMod 2, (M *ᵥ x) 0 * (M *ᵥ x) 1 =
      (M 0 0 * x 0 + M 0 1 * x 1) * (M 1 0 * x 0 + M 1 1 * x 1) := fun x ↦ by
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  simp only [hx]
  rw [key]
  simp [← Matrix.ext_iff, Fin.forall_fin_two, Matrix.one_apply]
  tauto

/-- The swap has determinant `-1 = 1` over `𝔽₂`, so `det` does not distinguish it from the
identity. -/
example : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 2)).det = 1 := by
  rw [det_fin_two_of]
  decide

/-! ### The root map `x_{ε₁}` of `q₃` -/

/-- **The root map `x_{ε₁}(a)` is a point of `O(q₃)`** for `q₃ = x₁x₃ + x₂²` over `ℤ`, over every
commutative ring: the image of `(x₁, x₂, x₃)` is `(x₁ + 2a x₂ - a² x₃, x₂ - a x₃, x₃)`, and
`(x₁ + 2a x₂ - a² x₃) x₃ + (x₂ - a x₃)² = x₁x₃ + x₂²`. -/
example {A : Type*} [CommRing A] (a : A) :
    nonsingInvUnit !![1, 2 * a, -a ^ 2; 0, 1, -a; 0, 0, 1] (by simp [det_fin_three]) ∈
      pointsSubgroup ℤ 3 (QuadraticMap.proj 0 2 + QuadraticMap.proj 1 1) A := by
  refine (mem_pointsSubgroup_iff _).2 fun x ↦ ?_
  simp only [baseChangeForm_add, add_apply, baseChangeForm_proj, QuadraticMap.proj_apply,
    nonsingInvUnit]
  simp [mulVec, dotProduct, Fin.sum_univ_three]
  ring

end TauCeti.QuadraticOrthogonal
