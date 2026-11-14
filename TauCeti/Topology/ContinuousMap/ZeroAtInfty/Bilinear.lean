/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Outer products and two-variable functionals on discrete model spaces

For discrete index types `I` and `J`, the currying isometry
`ZeroAtInftyContinuousMap.curryEquiv : C₀(I × J, E) ≃ₗᵢ[R] C₀(I, C₀(J, E))` turns operations in
one variable at a time into two-variable operations on the product model space without auxiliary
topological tensor products:

* `ZeroAtInftyContinuousMap.prodMul`: the outer product `(a, b) ↦ ((i, j) ↦ a i * b j)` of two
  scalar null families, satisfying `‖prodMul a b‖ ≤ ‖a‖ * ‖b‖` and sending coordinate vectors to
  coordinate vectors;
* `ZeroAtInftyContinuousMap.prodFunctional`: the continuous linear functional
  `C₀(I × J, R) →L[R] R` built from `u : C₀(I, R) →L[R] R` and a bounded
  `v : C₀(J, R) →L[R] R` by applying `v` to the rows and `u` to the resulting column.

On outer products `prodFunctional u v hv (prodMul a b) = u a * v b`. Because coordinate vectors
span a dense submodule of `C₀(I × J, R)`, two-variable functionals satisfy Fubini symmetry under
`Homeomorph.prodComm` (`prodFunctional_comp_congrLeft_prodComm`) over any Hausdorff seminormed
commutative ring, with no completeness or ultrametric hypothesis. Over a nontrivially normed field,
the operator norm is multiplicative: `‖prodFunctional u v hv‖ = ‖u‖ * ‖v‖`.

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer, 2002, §§10 and 17.
-/

public section

open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

section OuterProduct

variable {I J R : Type*} [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J]

section SeminormedRing

variable [SeminormedRing R]

/-- **Outer product of scalar null families.** Given `a ∈ C₀(I, R)` and `b ∈ C₀(J, R)`, the
two-variable family `(i, j) ↦ a i * b j` vanishes at infinity on `I × J`. -/
noncomputable def prodMul (a : C₀(I, R)) (b : C₀(J, R)) : C₀(I × J, R) :=
  (curryEquiv ℕ R).symm
    (compLeft ((ContinuousLinearMap.id ℕ R).smulRight b)
      ⟨‖b‖, fun r ↦ by
        simpa only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
          (mul_comm ‖b‖)] using norm_smul_le r b⟩ a)

/-- `prodMul a b` evaluates at `(i, j)` to `a i * b j`. -/
@[simp]
theorem prodMul_apply (a : C₀(I, R)) (b : C₀(J, R)) (p : I × J) :
    prodMul a b p = a p.1 * b p.2 := by
  simp [prodMul]

/-- The sup norm of an outer product is at most the product of the sup norms. -/
theorem norm_prodMul_le (a : C₀(I, R)) (b : C₀(J, R)) :
    ‖prodMul a b‖ ≤ ‖a‖ * ‖b‖ :=
  (norm_le (by positivity)).2 fun p ↦ by
    rw [prodMul_apply]
    exact (norm_mul_le _ _).trans
      (mul_le_mul (norm_coe_le_norm a p.1) (norm_coe_le_norm b p.2)
        (norm_nonneg _) (norm_nonneg _))

/-- An outer product with `0` on the left is `0`. -/
@[simp]
theorem prodMul_zero_left (b : C₀(J, R)) : prodMul (0 : C₀(I, R)) b = 0 := by
  ext; simp

/-- An outer product with `0` on the right is `0`. -/
@[simp]
theorem prodMul_zero_right (a : C₀(I, R)) : prodMul a (0 : C₀(J, R)) = 0 := by
  ext; simp

/-- `prodMul` is additive in its first argument. -/
theorem prodMul_add_left (a₁ a₂ : C₀(I, R)) (b : C₀(J, R)) :
    prodMul (a₁ + a₂) b = prodMul a₁ b + prodMul a₂ b := by
  ext; simp [add_mul]

/-- `prodMul` is additive in its second argument. -/
theorem prodMul_add_right (a : C₀(I, R)) (b₁ b₂ : C₀(J, R)) :
    prodMul a (b₁ + b₂) = prodMul a b₁ + prodMul a b₂ := by
  ext; simp [mul_add]

/-- `prodMul` commutes with left scalar multiplication in its first argument. -/
theorem prodMul_smul_left (r : R) (a : C₀(I, R)) (b : C₀(J, R)) :
    prodMul (r • a) b = r • prodMul a b := by
  ext; simp [mul_assoc]

/-- The outer product of two coordinate vectors is a coordinate vector on the product index. -/
@[simp]
theorem prodMul_single [DecidableEq I] [DecidableEq J] (i : I) (j : J) (r s : R) :
    prodMul (single i r) (single j s) = single (i, j) (r * s) := by
  ext ⟨i', j'⟩
  by_cases hi : i' = i <;> by_cases hj : j' = j <;> simp [single_apply, hi, hj]

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing R]

/-- Over a commutative seminormed ring, `prodMul` commutes with scalar multiplication in its
second argument. -/
theorem prodMul_smul_right (r : R) (a : C₀(I, R)) (b : C₀(J, R)) :
    prodMul a (r • b) = r • prodMul a b := by
  ext; simp [mul_left_comm]

/-- Currying an outer product scales the second factor by the coordinates of the first. -/
@[simp]
theorem curryEquiv_prodMul (a : C₀(I, R)) (b : C₀(J, R)) (i : I) :
    curryEquiv R R (prodMul a b) i = a i • b := by
  ext j; simp

/-- Swapping the two indices swaps the factors of an outer product. -/
@[simp]
theorem congrLeft_prodComm_prodMul (a : C₀(I, R)) (b : C₀(J, R)) :
    congrLeft R R (Homeomorph.prodComm I J) (prodMul a b) = prodMul b a := by
  ext ⟨j, i⟩; simp [mul_comm]

end SeminormedCommRing

end OuterProduct

section ProdFunctional

variable {I J R : Type*}
  [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J]

section SeminormedCommRing

variable [SeminormedCommRing R]

/-- **Product of two continuous linear functionals on discrete model spaces.** Given
`u : C₀(I, R) →L[R] R` and a uniformly bounded `v : C₀(J, R) →L[R] R`, `prodFunctional u v hv`
applies `v` to each row `j ↦ f (i, j)` via `curryEquiv` and then applies `u` to the resulting
family on `I`. -/
noncomputable def prodFunctional (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) : C₀(I × J, R) →L[R] R :=
  u ∘L compLeft v hv ∘L (curryEquiv (I := I) (J := J) R R).toLinearIsometry.toContinuousLinearMap

/-- `prodFunctional u v hv` evaluates `v` on the curried rows and `u` on the result. -/
theorem prodFunctional_apply (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) (f : C₀(I × J, R)) :
    prodFunctional u v hv f = u (compLeft v hv (curryEquiv R R f)) := (rfl)

/-- A product functional does not depend on the witness of boundedness of its second factor. -/
theorem prodFunctional_congr_bound (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv₁ hv₂ : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional u v hv₁ = prodFunctional u v hv₂ := (rfl)

/-- On an outer product, `prodFunctional u v hv` multiplies the values of `u` and `v`. -/
@[simp]
theorem prodFunctional_prodMul (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) (a : C₀(I, R)) (b : C₀(J, R)) :
    prodFunctional u v hv (prodMul a b) = u a * v b := by
  have hrow : compLeft v hv (curryEquiv R R (prodMul a b)) = v b • a := by
    ext i
    simp [mul_comm]
  rw [prodFunctional_apply, hrow, map_smul, smul_eq_mul, mul_comm]

/-- On a coordinate vector, `prodFunctional u v hv` multiplies the values on the unit coordinate
vectors. -/
@[simp]
theorem prodFunctional_single [DecidableEq I] [DecidableEq J]
    (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖)
    (i : I) (j : J) (r : R) :
    prodFunctional u v hv (single (i, j) r) = r * (u (single i 1) * v (single j 1)) := by
  have hsingle : single (i, j) r = prodMul (single i r) (single j (1 : R)) := by
    rw [prodMul_single, mul_one]
  rw [hsingle, prodFunctional_prodMul, ← smul_single_one i r, map_smul, smul_eq_mul, mul_assoc]

/-- A product functional with `0` on the left is `0`. -/
@[simp]
theorem prodFunctional_zero_left (v : C₀(J, R) →L[R] R) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional (0 : C₀(I, R) →L[R] R) v hv = 0 := by
  ext; simp [prodFunctional_apply]

/-- A product functional with `0` on the right is `0`. -/
@[simp]
theorem prodFunctional_zero_right (u : C₀(I, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖(0 : C₀(J, R) →L[R] R) y‖ ≤ C * ‖y‖) :
    prodFunctional u (0 : C₀(J, R) →L[R] R) hv = 0 := by
  have h0 : compLeft (α := I) (0 : C₀(J, R) →L[R] R) hv = 0 := by ext; simp
  ext f
  simp [prodFunctional_apply, h0]

/-- `prodFunctional` is additive in its first factor. -/
theorem prodFunctional_add_left (u₁ u₂ : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional (u₁ + u₂) v hv = prodFunctional u₁ v hv + prodFunctional u₂ v hv := by
  ext; simp [prodFunctional_apply]

/-- `prodFunctional` is additive in its second factor. -/
theorem prodFunctional_add_right (u : C₀(I, R) →L[R] R) (v₁ v₂ : C₀(J, R) →L[R] R)
    (hv₁ : ∃ C, ∀ y, ‖v₁ y‖ ≤ C * ‖y‖) (hv₂ : ∃ C, ∀ y, ‖v₂ y‖ ≤ C * ‖y‖)
    (hv : ∃ C, ∀ y, ‖(v₁ + v₂) y‖ ≤ C * ‖y‖) :
    prodFunctional u (v₁ + v₂) hv = prodFunctional u v₁ hv₁ + prodFunctional u v₂ hv₂ := by
  have hadd : compLeft (α := I) (v₁ + v₂) hv = compLeft v₁ hv₁ + compLeft v₂ hv₂ := by
    ext; simp
  ext f
  simp [prodFunctional_apply, hadd]

/-- `prodFunctional` commutes with scalar multiplication in its first factor. -/
theorem prodFunctional_smul_left (r : R) (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    prodFunctional (r • u) v hv = r • prodFunctional u v hv := by
  ext; simp [prodFunctional_apply]

/-- `prodFunctional` commutes with scalar multiplication in its second factor. -/
theorem prodFunctional_smul_right (r : R) (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) (hrv : ∃ C, ∀ y, ‖(r • v) y‖ ≤ C * ‖y‖) :
    prodFunctional u (r • v) hrv = r • prodFunctional u v hv := by
  have hsmul : compLeft (α := I) (r • v) hrv = r • compLeft v hv := by
    ext; simp
  ext f
  simp [prodFunctional_apply, hsmul]

/-- If `u` is bounded by `C₁ ≥ 0` and `v` is bounded by `C₂`, then `prodFunctional u v hv` is
bounded by `C₁ * C₂`. -/
theorem norm_prodFunctional_apply_le (u : C₀(I, R) →L[R] R) (v : C₀(J, R) →L[R] R)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) {C₁ C₂ : ℝ} (hC₁₀ : 0 ≤ C₁)
    (hC₁ : ∀ x, ‖u x‖ ≤ C₁ * ‖x‖) (hC₂ : ∀ y, ‖v y‖ ≤ C₂ * ‖y‖) (f : C₀(I × J, R)) :
    ‖prodFunctional u v hv f‖ ≤ (C₁ * C₂) * ‖f‖ := by
  rw [prodFunctional_apply, mul_assoc]
  refine (hC₁ _).trans (mul_le_mul_of_nonneg_left ?_ hC₁₀)
  exact (norm_compLeft_apply_le v hC₂ (curryEquiv R R f)).trans_eq
    (by rw [(curryEquiv R R).norm_map])

/-- **Fubini symmetry for bounded model-space functionals.** Swapping the two indices exchanges
the two factors of `prodFunctional`. -/
theorem prodFunctional_comp_congrLeft_prodComm [T2Space R]
    (u : C₀(I, R) →L[R] R) (hu : ∃ C, ∀ x, ‖u x‖ ≤ C * ‖x‖)
    (v : C₀(J, R) →L[R] R) (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    (prodFunctional v u hu).comp
        (congrLeft R R (Homeomorph.prodComm I J)).toLinearIsometry.toContinuousLinearMap =
      prodFunctional u v hv := by
  classical
  refine continuousLinearMap_ext_single_one fun ij ↦ ?_
  rcases ij with ⟨i, j⟩
  simp [mul_comm]

end SeminormedCommRing

section NontriviallyNormedField

variable {K : Type*} [NontriviallyNormedField K]

/-- Over a nontrivially normed field, the operator norm of `prodFunctional u v` equals the product
of the operator norms `‖u‖ * ‖v‖`. -/
@[simp]
theorem opNorm_prodFunctional (u : C₀(I, K) →L[K] K) (v : C₀(J, K) →L[K] K)
    (hv : ∃ C, ∀ y, ‖v y‖ ≤ C * ‖y‖) :
    ‖prodFunctional u v hv‖ = ‖u‖ * ‖v‖ := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (by positivity)
      (norm_prodFunctional_apply_le u v hv (norm_nonneg u) u.le_opNorm v.le_opNorm)
  · rcases eq_or_lt_of_le (norm_nonneg u) with hu0 | hu0
    · rw [← hu0, zero_mul]
      exact norm_nonneg (prodFunctional u v hv)
    · have hvb (b : C₀(J, K)) : ‖u‖ * ‖v b‖ ≤ ‖prodFunctional u v hv‖ * ‖b‖ := by
        rcases eq_or_lt_of_le (norm_nonneg (v b)) with hvb0 | hvb0
        · rw [← hvb0, mul_zero]
          exact mul_nonneg (norm_nonneg (prodFunctional u v hv)) (norm_nonneg b)
        · rw [← le_div_iff₀ hvb0]
          refine ContinuousLinearMap.opNorm_le_bound u
            (div_nonneg (mul_nonneg (norm_nonneg (prodFunctional u v hv)) (norm_nonneg b))
              hvb0.le) fun a ↦ ?_
          rw [div_mul_eq_mul_div, le_div_iff₀ hvb0]
          calc
            ‖u a‖ * ‖v b‖ = ‖u a * v b‖ := (norm_mul (u a) (v b)).symm
            _ = ‖prodFunctional u v hv (prodMul a b)‖ := by rw [prodFunctional_prodMul]
            _ ≤ ‖prodFunctional u v hv‖ * ‖prodMul a b‖ :=
              (prodFunctional u v hv).le_opNorm (prodMul a b)
            _ ≤ ‖prodFunctional u v hv‖ * (‖a‖ * ‖b‖) :=
              mul_le_mul_of_nonneg_left (norm_prodMul_le a b)
                (norm_nonneg (prodFunctional u v hv))
            _ = ‖prodFunctional u v hv‖ * ‖b‖ * ‖a‖ := by ring
      rw [← le_div_iff₀' hu0]
      refine ContinuousLinearMap.opNorm_le_bound v
        (div_nonneg (norm_nonneg (prodFunctional u v hv)) hu0.le) fun b ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀' hu0]
      exact hvb b

end NontriviallyNormedField

end ProdFunctional

end ZeroAtInftyContinuousMap
