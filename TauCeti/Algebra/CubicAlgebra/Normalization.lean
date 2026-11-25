/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CubicAlgebra.Basic
import Mathlib.LinearAlgebra.Transvection.Basic
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Algebras with a basis `1, ω, θ` are cubic algebras of binary cubic forms

Let `A` be a commutative `R`-algebra with a basis `1, ω, θ` whose first vector is `1`. Shifting
`ω` and `θ` by scalars makes `ωθ` a scalar, and then associativity forces the remaining products
into the table of a binary cubic form: if `ωθ = r`, `ω² = p + qω + sθ` and `θ² = t + uω + vθ`, then
`r = su`, `p = -sv` and `t = -qu`, which is the table of `⟨-s, q, -v, u⟩ : Cubic R`. Hence `A` is
isomorphic to the cubic algebra of that form. Together with `Cubic.CubicAlgebra` this gives the
correspondence between binary cubic forms and commutative `R`-algebras with a basis `1, ω, θ` in
which `ωθ` is a scalar, and shows that every basis whose first vector is `1` can be brought to this
shape. The `GL₂`-equivariance of the form under a change of basis is not treated here.

## Main definitions

* `Module.Basis.cubicForm c`: the binary cubic form read off a basis `c` with `c 0 = 1` from the
  products `c 1 * c 1`, `c 1 * c 2` and `c 2 * c 2`.
* `Module.Basis.cubicAlgEquiv c`: for a basis with `c 0 = 1` and `c 1 * c 2` a scalar, the algebra
  isomorphism `c.cubicForm.CubicAlgebra ≃ₐ[R] A` sending `ω ↦ c 1` and `θ ↦ c 2`.
* `Module.Basis.cubicNormalize b`: the basis obtained from `b` by shifting `b 1` and `b 2` by
  scalars.

## Main results

* `Cubic.CubicAlgebra.eq_mul_and_eq_neg_mul_and_eq_neg_mul_of_linearIndependent`: associativity
  forces the table.
* `Cubic.CubicAlgebra.cubicForm_basis`: the form read off the basis `1, ω, θ` of `P.CubicAlgebra`
  is `P`.
* `Module.Basis.cubicNormalize_one_mul_cubicNormalize_two`: after the shift, the product of the
  second and third basis vectors is a scalar, and
  `Module.Basis.eq_repr_mul_of_sub_mul_sub_eq_algebraMap` says that no other shift does this.
* `Module.Basis.cubicForm_cubicNormalize`: the shift does not change the form.
* `Module.Basis.exists_cubicAlgebra_algEquiv`: every commutative `R`-algebra with a basis whose
  first vector is `1` is isomorphic to the cubic algebra of some binary cubic form.

## References

* M. M. Wood, *Parametrizing quartic algebras over an arbitrary base*, Algebra & Number Theory
  **5** (2011), 1069–1094, §2.
* W. T. Gan, B. Gross, G. Savin, *Fourier coefficients of modular forms on `G₂`*, Duke Math. J.
  **115** (2002), 105–169.
-/

public section

namespace Cubic.CubicAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Associativity forces the cubic table.** Let `1, ω', θ'` be linearly independent in a
commutative `R`-algebra, with `ω'θ' = r`, `ω'² = p + qω' + sθ'` and `θ'² = t + uω' + vθ'`. Then
`r = su`, `p = -sv` and `t = -qu`; that is, these products are the table of the form
`⟨-s, q, -v, u⟩`. -/
theorem eq_mul_and_eq_neg_mul_and_eq_neg_mul_of_linearIndependent {ω' θ' : A}
    (hli : LinearIndependent R ![1, ω', θ']) {r p q s t u v : R}
    (hωθ : ω' * θ' = algebraMap R A r) (hωω : ω' * ω' = algebraMap R A p + q • ω' + s • θ')
    (hθθ : θ' * θ' = algebraMap R A t + u • ω' + v • θ') :
    r = s * u ∧ p = -(s * v) ∧ t = -(q * u) := by
  rw [Fintype.linearIndependent_iff] at hli
  -- A vanishing combination `α + βω' + γθ' = 0` has vanishing coefficients.
  have hcoeff {α β γ : R} (h : algebraMap R A α + β • ω' + γ • θ' = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
    have := hli ![α, β, γ] (by simpa [Fin.sum_univ_three, Algebra.smul_def] using h)
    exact ⟨this 0, this 1, this 2⟩
  simp only [Algebra.smul_def] at hωω hθθ hcoeff
  -- Compare `ω'² θ' = ω' (ω' θ')` and `θ'² ω' = θ' (θ' ω')` in the basis `1, ω', θ'`.
  obtain ⟨-, h₁, h₂⟩ := @hcoeff (q * r + s * t) (s * u - r) (p + s * v) (by
    simp only [map_add, map_sub, map_mul]
    linear_combination -θ' * hωω + ω' * hωθ - algebraMap R A q * hωθ - algebraMap R A s * hθθ)
  obtain ⟨-, h₃, -⟩ := @hcoeff (u * p + v * r) (t + u * q) (u * s - r) (by
    simp only [map_add, map_sub, map_mul]
    linear_combination -ω' * hθθ + θ' * hωθ - algebraMap R A u * hωω - algebraMap R A v * hωθ)
  exact ⟨by linear_combination -h₁, by linear_combination h₂, by linear_combination h₃⟩

end Cubic.CubicAlgebra

namespace Module.Basis

open Cubic Cubic.CubicAlgebra

section CubicForm

variable {R A : Type*} [Ring R] [AddCommMonoid A] [Mul A] [Module R A] (c : Basis (Fin 3) R A)

/-- The binary cubic form read off a basis `c`, meant for bases whose first vector is `1`. Writing
`c 1 * c 1 = p c 0 + q c 1 + s c 2`, `c 1 * c 2 = e₀ c 0 + e₁ c 1 + e₂ c 2` and
`c 2 * c 2 = t c 0 + u c 1 + v c 2`, it is `⟨-s, q - 2e₂, 2e₁ - v, u⟩`. When `c 1 * c 2` is a
multiple of `c 0` this is `⟨-s, q, -v, u⟩`, and when `c 0 = 1` it does not change under the
normalizing shift `Module.Basis.cubicNormalize` (`Module.Basis.cubicForm_cubicNormalize`). -/
noncomputable def cubicForm : Cubic R :=
  ⟨-c.repr (c 1 * c 1) 2, c.repr (c 1 * c 1) 1 - 2 * c.repr (c 1 * c 2) 2,
    2 * c.repr (c 1 * c 2) 1 - c.repr (c 2 * c 2) 2, c.repr (c 2 * c 2) 1⟩

@[simp] theorem cubicForm_a : c.cubicForm.a = -c.repr (c 1 * c 1) 2 := (rfl)

@[simp]
theorem cubicForm_b : c.cubicForm.b = c.repr (c 1 * c 1) 1 - 2 * c.repr (c 1 * c 2) 2 := (rfl)

@[simp]
theorem cubicForm_c : c.cubicForm.c = 2 * c.repr (c 1 * c 2) 1 - c.repr (c 2 * c 2) 2 := (rfl)

@[simp] theorem cubicForm_d : c.cubicForm.d = c.repr (c 2 * c 2) 1 := (rfl)

end CubicForm

/-- In a basis with `c 0 = 1`, every element is `x₀ + x₁ c 1 + x₂ c 2` in its coordinates. -/
private theorem algebraMap_repr_add_smul_add_smul {R A : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] (c : Basis (Fin 3) R A) (hc₀ : c 0 = 1) (x : A) :
    algebraMap R A (c.repr x 0) + c.repr x 1 • c 1 + c.repr x 2 • c 2 = x := by
  conv_rhs => rw [← c.sum_repr x]
  rw [Fin.sum_univ_three, hc₀, Algebra.algebraMap_eq_smul_one]

/-- A basis with `c 0 = 1` is the linearly independent family `1, c 1, c 2`. -/
private theorem linearIndependent_one_cons {R A : Type*} [Semiring R] [AddCommMonoid A]
    [Module R A] [One A] (c : Basis (Fin 3) R A) (hc₀ : c 0 = 1) :
    LinearIndependent R ![1, c 1, c 2] := by
  convert c.linearIndependent using 1
  ext i
  fin_cases i <;> simp [hc₀]

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section CubicAlgEquiv

variable (c : Basis (Fin 3) R A) (hc₀ : c 0 = 1) {r : R} (hc : c 1 * c 2 = algebraMap R A r)
include hc₀ hc

/-- For a basis with `c 0 = 1` and `c 1 * c 2` a scalar, `c 1` and `c 2` satisfy the table of
`c.cubicForm`. -/
private theorem mul_table_cubicForm :
    c 1 * c 2 = algebraMap R A (-(c.cubicForm.a * c.cubicForm.d)) ∧
    c 1 * c 1 = algebraMap R A (-(c.cubicForm.a * c.cubicForm.c)) + c.cubicForm.b • c 1 -
      c.cubicForm.a • c 2 ∧
    c 2 * c 2 = algebraMap R A (-(c.cubicForm.b * c.cubicForm.d)) + c.cubicForm.d • c 1 -
      c.cubicForm.c • c 2 := by
  have he₁ : c.repr (c 1 * c 2) 1 = 0 := by simp [hc, repr_algebraMap hc₀]
  have he₂ : c.repr (c 1 * c 2) 2 = 0 := by simp [hc, repr_algebraMap hc₀]
  obtain ⟨hr, hp, ht⟩ := eq_mul_and_eq_neg_mul_and_eq_neg_mul_of_linearIndependent
    (linearIndependent_one_cons c hc₀) hc
    (algebraMap_repr_add_smul_add_smul c hc₀ (c 1 * c 1)).symm
    (algebraMap_repr_add_smul_add_smul c hc₀ (c 2 * c 2)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [hc, hr]
    simp
  · conv_lhs => rw [← algebraMap_repr_add_smul_add_smul c hc₀ (c 1 * c 1)]
    simp [hp, he₁, he₂, sub_eq_add_neg]
  · conv_lhs => rw [← algebraMap_repr_add_smul_add_smul c hc₀ (c 2 * c 2)]
    simp [ht, he₁, he₂, sub_eq_add_neg]

/-- For a basis with `c 0 = 1` and `c 1 * c 2` a scalar, `c 1 * c 2 = -ad` for the coefficients
of `c.cubicForm`. -/
theorem apply_one_mul_apply_two_cubicForm :
    c 1 * c 2 = algebraMap R A (-(c.cubicForm.a * c.cubicForm.d)) :=
  (mul_table_cubicForm c hc₀ hc).1

/-- For a basis with `c 0 = 1` and `c 1 * c 2` a scalar, `c 1 * c 1 = -ac + b c 1 - a c 2` for
the coefficients of `c.cubicForm`. -/
theorem apply_one_mul_apply_one_cubicForm :
    c 1 * c 1 = algebraMap R A (-(c.cubicForm.a * c.cubicForm.c)) + c.cubicForm.b • c 1 -
      c.cubicForm.a • c 2 :=
  (mul_table_cubicForm c hc₀ hc).2.1

/-- For a basis with `c 0 = 1` and `c 1 * c 2` a scalar, `c 2 * c 2 = -bd + d c 1 - c c 2` for
the coefficients of `c.cubicForm`. -/
theorem apply_two_mul_apply_two_cubicForm :
    c 2 * c 2 = algebraMap R A (-(c.cubicForm.b * c.cubicForm.d)) + c.cubicForm.d • c 1 -
      c.cubicForm.c • c 2 :=
  (mul_table_cubicForm c hc₀ hc).2.2

/-- A commutative `R`-algebra with a basis `1, ω, θ` such that `ωθ` is a scalar is the cubic
algebra of the form `c.cubicForm`, through `ω ↦ c 1` and `θ ↦ c 2`. -/
noncomputable def cubicAlgEquiv : c.cubicForm.CubicAlgebra ≃ₐ[R] A :=
  AlgEquiv.ofBijective (lift (c 1) (c 2) (c.apply_one_mul_apply_two_cubicForm hc₀ hc)
      (c.apply_one_mul_apply_one_cubicForm hc₀ hc)
      (c.apply_two_mul_apply_two_cubicForm hc₀ hc)) <| by
    -- The algebra map sends the basis `1, ω, θ` to the basis `c`.
    have h : (lift (c 1) (c 2) (c.apply_one_mul_apply_two_cubicForm hc₀ hc)
        (c.apply_one_mul_apply_one_cubicForm hc₀ hc)
        (c.apply_two_mul_apply_two_cubicForm hc₀ hc)).toLinearMap =
        ((basis c.cubicForm).equiv c (Equiv.refl _)).toLinearMap :=
      (basis c.cubicForm).ext fun i ↦ by
        rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
        fin_cases i <;> simp [hc₀]
    rw [← AlgHom.coe_toLinearMap, h]
    exact LinearEquiv.bijective _

theorem cubicAlgEquiv_apply (x : c.cubicForm.CubicAlgebra) :
    c.cubicAlgEquiv hc₀ hc x = algebraMap R A x.re + x.imOmega • c 1 + x.imTheta • c 2 := (rfl)

@[simp]
theorem cubicAlgEquiv_omega : c.cubicAlgEquiv hc₀ hc (ω c.cubicForm) = c 1 := by
  simp [cubicAlgEquiv_apply]

@[simp]
theorem cubicAlgEquiv_theta : c.cubicAlgEquiv hc₀ hc (θ c.cubicForm) = c 2 := by
  simp [cubicAlgEquiv_apply]

@[simp]
theorem cubicAlgEquiv_basis (i : Fin 3) : c.cubicAlgEquiv hc₀ hc (basis c.cubicForm i) = c i := by
  fin_cases i <;> simp [hc₀]

@[simp]
theorem cubicAlgEquiv_symm_apply (x : A) :
    (c.cubicAlgEquiv hc₀ hc).symm x = ⟨c.repr x 0, c.repr x 1, c.repr x 2⟩ := by
  rw [AlgEquiv.symm_apply_eq, cubicAlgEquiv_apply]
  exact (algebraMap_repr_add_smul_add_smul c hc₀ x).symm

end CubicAlgEquiv

end Module.Basis

namespace Cubic.CubicAlgebra

/-- The form read off the basis `1, ω, θ` of the cubic algebra of `P` is `P` itself. -/
@[simp]
theorem cubicForm_basis {R : Type*} [CommRing R] (P : Cubic R) : (basis P).cubicForm = P := by
  ext <;> simp [omega_mul_omega, theta_mul_theta, omega_mul_theta]

end Cubic.CubicAlgebra

namespace Module.Basis

open Cubic Cubic.CubicAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (b : Basis (Fin 3) R A) (hb₀ : b 0 = 1)

/-- The normalization of a basis `1, b 1, b 2` of a commutative algebra: if
`b 1 * b 2 = e₀ + e₁ b 1 + e₂ b 2`, it is the basis `1, b 1 - e₂, b 2 - e₁`, the image of `b` under
the transvection `x ↦ x - (e₂ x₁ + e₁ x₂) • 1`. -/
noncomputable def cubicNormalize : Basis (Fin 3) R A :=
  b.map <| LinearEquiv.transvection
    (f := -(b.repr (b 1 * b 2) 2 • b.coord 1 + b.repr (b 1 * b 2) 1 • b.coord 2)) (v := 1)
    (by rw [← hb₀]; simp)

@[simp]
theorem cubicNormalize_zero : b.cubicNormalize hb₀ 0 = 1 := by
  simpa [cubicNormalize, LinearMap.transvection.apply] using hb₀

@[simp]
theorem cubicNormalize_one :
    b.cubicNormalize hb₀ 1 = b 1 - algebraMap R A (b.repr (b 1 * b 2) 2) := by
  simp [cubicNormalize, LinearMap.transvection.apply, Algebra.algebraMap_eq_smul_one,
    sub_eq_add_neg]

@[simp]
theorem cubicNormalize_two :
    b.cubicNormalize hb₀ 2 = b 2 - algebraMap R A (b.repr (b 1 * b 2) 1) := by
  simp [cubicNormalize, LinearMap.transvection.apply, Algebra.algebraMap_eq_smul_one,
    sub_eq_add_neg]

/-- The coordinates in the normalized basis: the coordinates of `b 1` and `b 2` are unchanged, and
the coordinate of `1` absorbs the shifts. -/
theorem cubicNormalize_repr (x : A) :
    (b.cubicNormalize hb₀).repr x = ![b.repr x 0 + b.repr (b 1 * b 2) 2 * b.repr x 1 +
      b.repr (b 1 * b 2) 1 * b.repr x 2, b.repr x 1, b.repr x 2] := by
  ext i
  fin_cases i
  · simp [cubicNormalize, LinearEquiv.transvection.symm_eq, LinearMap.transvection.apply, ← hb₀]
    ring
  all_goals
    simp [cubicNormalize, LinearEquiv.transvection.symm_eq, LinearMap.transvection.apply, ← hb₀]

/-- After normalization the product of the second and third basis vectors is a scalar. -/
theorem cubicNormalize_one_mul_cubicNormalize_two :
    b.cubicNormalize hb₀ 1 * b.cubicNormalize hb₀ 2 =
      algebraMap R A (b.repr (b 1 * b 2) 0 + b.repr (b 1 * b 2) 1 * b.repr (b 1 * b 2) 2) := by
  have hsum := algebraMap_repr_add_smul_add_smul b hb₀ (b 1 * b 2)
  rw [cubicNormalize_one, cubicNormalize_two]
  simp only [Algebra.smul_def, map_add, map_mul] at hsum ⊢
  linear_combination -hsum

include hb₀ in
/-- The shifts in `Module.Basis.cubicNormalize` are the only scalar shifts of `b 1` and `b 2` whose
product is a scalar. -/
theorem eq_repr_mul_of_sub_mul_sub_eq_algebraMap {u v w : R}
    (h : (b 1 - algebraMap R A u) * (b 2 - algebraMap R A v) = algebraMap R A w) :
    u = b.repr (b 1 * b 2) 2 ∧ v = b.repr (b 1 * b 2) 1 := by
  have h₁ : b.repr (b 1 * b 2) 1 - v = 0 := by
    simpa [mul_sub, sub_mul, repr_smul', repr_mul_algebraMap, repr_algebraMap hb₀] using
      congr($(congrArg b.repr h) 1)
  have h₂ : b.repr (b 1 * b 2) 2 - u = 0 := by
    simpa [mul_sub, sub_mul, repr_smul', repr_mul_algebraMap, repr_algebraMap hb₀] using
      congr($(congrArg b.repr h) 2)
  exact ⟨by linear_combination -h₂, by linear_combination -h₁⟩

/-- A basis whose second and third vectors already have a scalar product is its own
normalization. -/
theorem cubicNormalize_eq_self {r : R} (hb : b 1 * b 2 = algebraMap R A r) :
    b.cubicNormalize hb₀ = b := by
  refine Basis.eq_of_apply_eq fun i ↦ ?_
  fin_cases i <;> simp [hb, repr_algebraMap hb₀, hb₀]

/-- Normalization does not change the binary cubic form read off the basis. -/
@[simp]
theorem cubicForm_cubicNormalize : (b.cubicNormalize hb₀).cubicForm = b.cubicForm := by
  ext <;>
    simp [cubicNormalize_repr, mul_sub, sub_mul, repr_mul_algebraMap, repr_smul',
      repr_algebraMap hb₀] <;> ring

include hb₀ in
/-- **Algebras with a basis `1, ω, θ` come from binary cubic forms.** A commutative `R`-algebra
with a basis whose first vector is `1` is isomorphic to the cubic algebra of some binary cubic
form. -/
theorem exists_cubicAlgebra_algEquiv : ∃ P : Cubic R, Nonempty (P.CubicAlgebra ≃ₐ[R] A) :=
  ⟨(b.cubicNormalize hb₀).cubicForm,
    ⟨(b.cubicNormalize hb₀).cubicAlgEquiv (b.cubicNormalize_zero hb₀)
      (b.cubicNormalize_one_mul_cubicNormalize_two hb₀)⟩⟩

end Module.Basis
