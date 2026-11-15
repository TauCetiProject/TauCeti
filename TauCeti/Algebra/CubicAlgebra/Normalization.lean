/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CubicAlgebra.Basic

/-!
# Free cubic algebras are cubic algebras of binary cubic forms

Let `A` be a commutative `R`-algebra which is free of rank three with a basis `1, ω, θ`. Shifting
`ω` and `θ` by scalars makes `ωθ` a scalar, and then associativity forces the remaining products
into the table of a binary cubic form: if `ωθ = r`, `ω² = p + qω + sθ` and `θ² = t + uω + vθ`, then
`r = su`, `p = -sv` and `t = -qu`, which is the table of `⟨-s, q, -v, u⟩ : Cubic R`. Hence `A` is
isomorphic to the cubic algebra of that form. Together with `Cubic.CubicAlgebra` this is the free
case of the correspondence between binary cubic forms and cubic algebras.

## Main definitions

* `Module.Basis.cubicForm c`: the binary cubic form read off a basis `c` of a rank-three algebra
  from the products `c 1 * c 1` and `c 2 * c 2`.
* `Module.Basis.cubicAlgEquiv c`: for a basis with `c 0 = 1` and `c 1 * c 2` a scalar, the algebra
  isomorphism `c.cubicForm.CubicAlgebra ≃ₐ[R] A` sending `ω ↦ c 1` and `θ ↦ c 2`.

## Main results

* `Cubic.CubicAlgebra.mul_table_eq_of_linearIndependent`: associativity forces the table.
* `Cubic.CubicAlgebra.cubicForm_basis`: the form read off the basis `1, ω, θ` of `P.CubicAlgebra`
  is `P`.
* `Module.Basis.normalize`: shifting `b 1` and `b 2` by scalars makes their product a scalar.
* `Module.Basis.exists_cubicAlgEquiv`: every commutative `R`-algebra with a basis `1, ω, θ` is
  isomorphic to the cubic algebra of some binary cubic form.

## References

* M. M. Wood, *Parametrizing quartic algebras over an arbitrary base*, Algebra & Number Theory
  **5** (2011), 1069–1094, §2.
* W. T. Gan, B. Gross, G. Savin, *Fourier coefficients of modular forms on `G₂`*, Duke Math. J.
  **115** (2002), 105–169.
-/

public section

namespace Cubic.CubicAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Associativity forces the cubic table.** Let `1, ω, θ` be linearly independent in a commutative
`R`-algebra, with `ωθ = r`, `ω² = p + qω + sθ` and `θ² = t + uω + vθ`. Then `r = su`, `p = -sv` and
`t = -qu`; that is, these products are the table of the form `⟨-s, q, -v, u⟩`. -/
theorem mul_table_eq_of_linearIndependent {ω θ : A}
    (hli : LinearIndependent R ![1, ω, θ]) {r p q s t u v : R}
    (hωθ : ω * θ = algebraMap R A r) (hωω : ω * ω = algebraMap R A p + q • ω + s • θ)
    (hθθ : θ * θ = algebraMap R A t + u • ω + v • θ) :
    r = s * u ∧ p = -(s * v) ∧ t = -(q * u) := by
  rw [Fintype.linearIndependent_iff] at hli
  -- A vanishing combination `α + βω + γθ = 0` has vanishing coefficients.
  have hcoeff {α β γ : R} (h : algebraMap R A α + β • ω + γ • θ = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
    have := hli ![α, β, γ] (by simpa [Fin.sum_univ_three, Algebra.smul_def] using h)
    exact ⟨this 0, this 1, this 2⟩
  simp only [Algebra.smul_def] at hωω hθθ hcoeff
  -- Compare `ω² θ = ω (ω θ)` and `θ² ω = θ (θ ω)` in the basis `1, ω, θ`.
  obtain ⟨-, h₁, h₂⟩ := @hcoeff (q * r + s * t) (s * u - r) (p + s * v) (by
    simp only [map_add, map_sub, map_mul]
    linear_combination -θ * hωω + ω * hωθ - algebraMap R A q * hωθ - algebraMap R A s * hθθ)
  obtain ⟨-, h₃, -⟩ := @hcoeff (u * p + v * r) (t + u * q) (u * s - r) (by
    simp only [map_add, map_sub, map_mul]
    linear_combination -ω * hθθ + θ * hωθ - algebraMap R A u * hωω - algebraMap R A v * hωθ)
  exact ⟨by linear_combination -h₁, by linear_combination h₂, by linear_combination h₃⟩

end Cubic.CubicAlgebra

namespace Module.Basis

open Cubic Cubic.CubicAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The binary cubic form read off a basis `c` of a rank-three algebra: if
`c 1 * c 1 = p + q c 1 + s c 2` and `c 2 * c 2 = t + u c 1 + v c 2`, it is `⟨-s, q, -v, u⟩`. -/
noncomputable def cubicForm (c : Basis (Fin 3) R A) : Cubic R :=
  ⟨-c.repr (c 1 * c 1) 2, c.repr (c 1 * c 1) 1, -c.repr (c 2 * c 2) 2, c.repr (c 2 * c 2) 1⟩

variable (c : Basis (Fin 3) R A) (hc₀ : c 0 = 1)
include hc₀

/-- In a basis with `c 0 = 1`, every element is `x₀ + x₁ c 1 + x₂ c 2` in its coordinates. -/
theorem algebraMap_repr_add_smul_add_smul (x : A) :
    algebraMap R A (c.repr x 0) + c.repr x 1 • c 1 + c.repr x 2 • c 2 = x := by
  conv_rhs => rw [← c.sum_repr x]
  rw [Fin.sum_univ_three, hc₀, Algebra.algebraMap_eq_smul_one]

/-- A basis with `c 0 = 1` is the linearly independent family `1, c 1, c 2`. -/
theorem linearIndependent_one_cons : LinearIndependent R ![1, c 1, c 2] := by
  convert c.linearIndependent using 1
  ext i
  fin_cases i <;> simp [hc₀]

variable {r : R} (hc : c 1 * c 2 = algebraMap R A r)
include hc

/-- For a basis with `c 0 = 1` and `c 1 * c 2` a scalar, `c 1` and `c 2` satisfy the table of
`c.cubicForm`. -/
theorem mul_table_cubicForm :
    c 1 * c 2 = algebraMap R A (-(c.cubicForm.a * c.cubicForm.d)) ∧
    c 1 * c 1 = algebraMap R A (-(c.cubicForm.a * c.cubicForm.c)) + c.cubicForm.b • c 1 -
      c.cubicForm.a • c 2 ∧
    c 2 * c 2 = algebraMap R A (-(c.cubicForm.b * c.cubicForm.d)) + c.cubicForm.d • c 1 -
      c.cubicForm.c • c 2 := by
  obtain ⟨hr, hp, ht⟩ := mul_table_eq_of_linearIndependent (c.linearIndependent_one_cons hc₀) hc
    (c.algebraMap_repr_add_smul_add_smul hc₀ (c 1 * c 1)).symm
    (c.algebraMap_repr_add_smul_add_smul hc₀ (c 2 * c 2)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, hr]
    simp [cubicForm]
  · conv_lhs => rw [← c.algebraMap_repr_add_smul_add_smul hc₀ (c 1 * c 1)]
    simp [cubicForm, hp, sub_eq_add_neg]
  · conv_lhs => rw [← c.algebraMap_repr_add_smul_add_smul hc₀ (c 2 * c 2)]
    simp [cubicForm, ht, sub_eq_add_neg]

/-- A commutative `R`-algebra with a basis `1, ω, θ` such that `ωθ` is a scalar is the cubic
algebra of the form `c.cubicForm`, through `ω ↦ c 1` and `θ ↦ c 2`. -/
noncomputable def cubicAlgEquiv : c.cubicForm.CubicAlgebra ≃ₐ[R] A :=
  AlgEquiv.ofBijective (lift (c 1) (c 2) (c.mul_table_cubicForm hc₀ hc).1
      (c.mul_table_cubicForm hc₀ hc).2.1 (c.mul_table_cubicForm hc₀ hc).2.2) <| by
    -- The algebra map sends the basis `1, ω, θ` to the basis `c`.
    have h : (lift (c 1) (c 2) (c.mul_table_cubicForm hc₀ hc).1 (c.mul_table_cubicForm hc₀ hc).2.1
        (c.mul_table_cubicForm hc₀ hc).2.2).toLinearMap =
        ((basis c.cubicForm).equiv c (Equiv.refl _)).toLinearMap :=
      (basis c.cubicForm).ext fun i ↦ by
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        fin_cases i <;> simp [hc₀]
    rw [← AlgHom.coe_toLinearMap, h]
    exact LinearEquiv.bijective _

@[simp]
theorem cubicAlgEquiv_ω : c.cubicAlgEquiv hc₀ hc (ω c.cubicForm) = c 1 := by
  simp [cubicAlgEquiv]

@[simp]
theorem cubicAlgEquiv_θ : c.cubicAlgEquiv hc₀ hc (θ c.cubicForm) = c 2 := by
  simp [cubicAlgEquiv]

end Module.Basis

namespace Cubic.CubicAlgebra

/-- The form read off the basis `1, ω, θ` of the cubic algebra of `P` is `P` itself. -/
@[simp]
theorem cubicForm_basis {R : Type*} [CommRing R] (P : Cubic R) : (basis P).cubicForm = P := by
  ext <;> simp [Module.Basis.cubicForm, ω_mul_ω, θ_mul_θ]

end Cubic.CubicAlgebra

namespace Module.Basis

open Cubic Cubic.CubicAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (b : Basis (Fin 3) R A) (hb₀ : b 0 = 1)

/-- The vectors `1, b 1 - e₂, b 2 - e₁`, where `b 1 * b 2 = e₀ + e₁ b 1 + e₂ b 2`. -/
private noncomputable def shift : Fin 3 → A :=
  ![1, b 1 - algebraMap R A (b.repr (b 1 * b 2) 2), b 2 - algebraMap R A (b.repr (b 1 * b 2) 1)]

include hb₀ in
private theorem linearIndependent_shift : LinearIndependent R (b.shift) := by
  set e := b.repr (b 1 * b 2)
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- The coordinates of `∑ gᵢ shiftᵢ` in `b` are `g₀ - g₁ e₂ - g₂ e₁`, `g₁`, `g₂`.
  have hb := Fintype.linearIndependent_iff.1 b.linearIndependent
    ![g 0 - g 1 * e 2 - g 2 * e 1, g 1, g 2] (by
      simp only [shift, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, hb₀, Algebra.smul_def, map_sub,
        map_mul, mul_one] at hg ⊢
      linear_combination hg)
  have h₀ := hb 0
  have h₁ := hb 1
  have h₂ := hb 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h₀ h₁ h₂
  intro i
  fin_cases i
  · simpa [h₁, h₂] using h₀
  · exact h₁
  · exact h₂

include hb₀ in
private theorem top_le_span_shift : ⊤ ≤ Submodule.span R (Set.range b.shift) := by
  rw [← b.span_eq, Submodule.span_le]
  refine Set.range_subset_iff.2 fun i ↦ ?_
  have hmem (j : Fin 3) : b.shift j ∈ Submodule.span R (Set.range b.shift) :=
    Submodule.subset_span ⟨j, rfl⟩
  -- `b 1` and `b 2` are the shifted vectors plus multiples of `1`.
  have h₁ : b 1 = b.shift 1 + b.repr (b 1 * b 2) 2 • b.shift 0 := by
    simp only [shift, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one,
      sub_add_cancel]
  have h₂ : b 2 = b.shift 2 + b.repr (b 1 * b 2) 1 • b.shift 0 := by
    simp only [shift, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, Algebra.smul_def, mul_one, sub_add_cancel]
  match i with
  | 0 => simpa [shift, hb₀] using hmem 0
  | 1 =>
    rw [h₁]
    exact Submodule.add_mem _ (hmem 1) (Submodule.smul_mem _ _ (hmem 0))
  | 2 =>
    rw [h₂]
    exact Submodule.add_mem _ (hmem 2) (Submodule.smul_mem _ _ (hmem 0))

/-- The normalization of a basis `1, b 1, b 2` of a rank-three algebra: shift `b 1` and `b 2` by
scalars so that their product is a scalar. If `b 1 * b 2 = e₀ + e₁ b 1 + e₂ b 2`, the new basis is
`1, b 1 - e₂, b 2 - e₁`. -/
noncomputable def normalize : Basis (Fin 3) R A :=
  .mk (b.linearIndependent_shift hb₀) (b.top_le_span_shift hb₀)

@[simp]
theorem normalize_zero : b.normalize hb₀ 0 = 1 := by
  simp [normalize, shift]

@[simp]
theorem normalize_one :
    b.normalize hb₀ 1 = b 1 - algebraMap R A (b.repr (b 1 * b 2) 2) := by
  simp [normalize, shift]

@[simp]
theorem normalize_two :
    b.normalize hb₀ 2 = b 2 - algebraMap R A (b.repr (b 1 * b 2) 1) := by
  simp [normalize, shift]

/-- After normalization the product of the second and third basis vectors is a scalar. -/
theorem normalize_one_mul_normalize_two :
    b.normalize hb₀ 1 * b.normalize hb₀ 2 =
      algebraMap R A (b.repr (b 1 * b 2) 0 + b.repr (b 1 * b 2) 1 * b.repr (b 1 * b 2) 2) := by
  have hsum := b.algebraMap_repr_add_smul_add_smul hb₀ (b 1 * b 2)
  rw [normalize_one, normalize_two]
  simp only [Algebra.smul_def, map_add, map_mul] at hsum ⊢
  linear_combination -hsum

include hb₀ in
/-- **Free cubic algebras come from binary cubic forms.** A commutative `R`-algebra with a basis
whose first vector is `1` is isomorphic to the cubic algebra of the binary cubic form read off its
normalized basis. -/
theorem exists_cubicAlgEquiv : ∃ P : Cubic R, Nonempty (P.CubicAlgebra ≃ₐ[R] A) :=
  ⟨(b.normalize hb₀).cubicForm,
    ⟨(b.normalize hb₀).cubicAlgEquiv (b.normalize_zero hb₀)
      (b.normalize_one_mul_normalize_two hb₀)⟩⟩

end Module.Basis
