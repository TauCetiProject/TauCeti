/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ExteriorPower
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.SesquilinearForm
public import TauCeti.LinearAlgebra.ExteriorAlgebra.HermitianMetric
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange

/-!
# The Gram metric of a Euclidean exterior algebra and its complexification

Let `V` be a finite-dimensional real inner product space. Mathlib puts a Gram-determinant inner
product on each homogeneous exterior power `⋀[ℝ]^k V`. On the full exterior algebra
`ExteriorAlgebra ℝ V`, the bilinear form `ExteriorAlgebra.gramForm V` makes the increasing wedge
basis `e.toBasis.ExteriorAlgebra` orthonormal for every orthonormal basis `e` of `V`
(`ExteriorAlgebra.gramForm_eq_toLinearMapₛₗ₂`). It does not
depend on `e`, makes distinct exterior powers orthogonal
(`ExteriorAlgebra.gramForm_eq_zero_of_mem_exteriorPower`), evaluates on decomposable wedges by the
Gram determinant (`ExteriorAlgebra.gramForm_ιMulti_ιMulti`), and restricts on each `⋀[ℝ]^k V` to
Mathlib's inner product (`ExteriorAlgebra.gramForm_coe_exteriorPower`). No global `Norm` or
`InnerProductSpace` instance on `ExteriorAlgebra ℝ V` is introduced, so the algebra norm is left
unconstrained.

After complexification, `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` carries the positive definite Hermitian form
`(ExteriorAlgebra.gramForm V).sesqComplexification`, while `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` carries
the Hermitian form making the wedge basis `(e.toBasis.baseChange ℂ).ExteriorAlgebra` orthonormal.
Because `e.toBasis.baseChange ℂ` is orthonormal for `(innerₗ V).sesqComplexification`
(`OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex`), the two exterior Hermitian forms match
under `ExteriorAlgebra.baseChangeEquiv`
(`OrthonormalBasis.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv`), and on homogeneous
`k`-forms both agree with `(innerₗ (⋀[ℝ]^k V)).sesqComplexification`
(`ExteriorAlgebra.sesqComplexification_gramForm_subtype_baseChange`,
`OrthonormalBasis.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_coe_exteriorPower`).

## Main definitions

* `ExteriorAlgebra.gramForm V`: the symmetric positive definite Gram bilinear form on
  `ExteriorAlgebra ℝ V`.

## Main results

* `ExteriorAlgebra.gramForm_eq_toLinearMapₛₗ₂`:
  characterization of `gramForm V` in the wedge basis of any orthonormal basis of `V`.
* `ExteriorAlgebra.gramForm_ι_mul_left`, `ExteriorAlgebra.gramForm_eq_zero_of_mem_exteriorPower`,
  `ExteriorAlgebra.gramForm_ιMulti_ιMulti`, and `ExteriorAlgebra.gramForm_coe_exteriorPower`:
  creation–contraction adjointness, degree orthogonality, Gram-determinant evaluation, and
  agreement with the inner product on `⋀[ℝ]^k V`.
* `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv` and
  `ExteriorAlgebra.sesqComplexification_gramForm_subtype_baseChange`: comparison of the wedge-basis
  Hermitian form on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` with the sesquilinear complexification of the
  Gram metric on `ℂ ⊗[ℝ] ExteriorAlgebra ℝ V` and on `ℂ ⊗[ℝ] ⋀[ℝ]^k V`.

## References

* W. Greub, *Multilinear Algebra*, 2nd ed., Springer (1978), Chapter 5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

open Matrix Module TauCeti.ExteriorAlgebra
open scoped ComplexOrder RealInnerProductSpace TensorProduct

namespace OrthonormalBasis

variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fintype I] [LinearOrder I] (e : OrthonormalBasis I ℝ V)

/-- **The wedge-basis Hermitian form on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` does not depend on the
real orthonormal basis `e`.** -/
theorem toLinearMapₛₗ₂_baseChange_exteriorAlgebra_eq {I' : Type*} [Fintype I'] [LinearOrder I']
    (e' : OrthonormalBasis I' ℝ V) :
    Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℂ) =
      Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e'.toBasis.baseChange ℂ).ExteriorAlgebra (e'.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I') (Finset I') ℂ) :=
  ExteriorAlgebra.toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq _ _
    (e.toLinearMapₛₗ₂_baseChange_complex.trans e'.toLinearMapₛₗ₂_baseChange_complex.symm)

/-- **The Gram-determinant formula on `ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)`**: in every degree `k`,
the wedge-basis Hermitian form evaluates on decomposable wedges as the determinant of
`(innerₗ V).sesqComplexification`. -/
theorem toLinearMapₛₗ₂_baseChange_exteriorAlgebra_ιMulti_ιMulti (k : ℕ)
    (u v : Fin k → ℂ ⊗[ℝ] V) :
    Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℂ)
        (ExteriorAlgebra.ιMulti ℂ k u) (ExteriorAlgebra.ιMulti ℂ k v) =
      (Matrix.of fun i j ↦
        LinearMap.BilinForm.sesqComplexification (innerₗ V) (u i) (v j)).det := by
  rw [ExteriorAlgebra.toLinearMapₛₗ₂_ιMulti_ιMulti, e.toLinearMapₛₗ₂_baseChange_complex]

end OrthonormalBasis

namespace ExteriorAlgebra

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

variable (V) in
/-- **The Gram bilinear form on the exterior algebra** of a finite-dimensional real inner product
space `V`: the symmetric positive definite bilinear form for which the increasing wedge basis of
every orthonormal basis of `V` is orthonormal (`ExteriorAlgebra.gramForm_eq_toLinearMapₛₗ₂`). On
each homogeneous exterior power `⋀[ℝ]^k V` it agrees with Mathlib's Gram-determinant inner product
(`ExteriorAlgebra.gramForm_coe_exteriorPower`), and distinct exterior powers are orthogonal. -/
def gramForm : LinearMap.BilinForm ℝ (ExteriorAlgebra ℝ V) :=
  let b := (stdOrthonormalBasis ℝ V).toBasis.ExteriorAlgebra
  Matrix.toLinearMapₛₗ₂ (starRingEnd ℝ) b b 1

/-- **In any orthonormal frame, `gramForm V` is the wedge-basis sesquilinear form**
`Matrix.toLinearMapₛₗ₂ (starRingEnd ℝ) e.toBasis.ExteriorAlgebra e.toBasis.ExteriorAlgebra 1`. -/
theorem gramForm_eq_toLinearMapₛₗ₂ {I : Type*} [Fintype I] [LinearOrder I]
    (e : OrthonormalBasis I ℝ V) :
    gramForm V =
      Matrix.toLinearMapₛₗ₂ (starRingEnd ℝ) e.toBasis.ExteriorAlgebra e.toBasis.ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℝ) :=
  toLinearMapₛₗ₂_eq_of_toLinearMapₛₗ₂_eq (stdOrthonormalBasis ℝ V).toBasis e.toBasis
    ((stdOrthonormalBasis ℝ V).toLinearMapₛₗ₂_real.trans e.toLinearMapₛₗ₂_real.symm)

/-- Increasing wedge-basis elements of an orthonormal basis are orthonormal for `gramForm V`. -/
@[simp]
theorem gramForm_basis_basis {I : Type*} [Fintype I] [LinearOrder I]
    (e : OrthonormalBasis I ℝ V) (s t : Finset I) :
    gramForm V (e.toBasis.ExteriorAlgebra s) (e.toBasis.ExteriorAlgebra t) =
      if s = t then 1 else 0 := by
  rw [gramForm_eq_toLinearMapₛₗ₂ e, Matrix.toLinearMapₛₗ₂_apply_basis, Matrix.one_apply]

/-- The vacuum `1` is a unit vector for `gramForm V`. -/
@[simp]
theorem gramForm_one_one : gramForm V 1 1 = 1 := by
  rw [gramForm_eq_toLinearMapₛₗ₂ (stdOrthonormalBasis ℝ V), toLinearMapₛₗ₂_apply_one_one]

/-- **Exterior multiplication by `v` is adjoint to contraction by `⟪v, ·⟫`** for `gramForm V`. -/
theorem gramForm_ι_mul_left (v : V) (s t : ExteriorAlgebra ℝ V) :
    gramForm V (ι ℝ v * s) t =
      gramForm V s (CliffordAlgebra.contractLeft (Q := 0) (innerₗ V v) t) := by
  let e := stdOrthonormalBasis ℝ V
  rw [gramForm_eq_toLinearMapₛₗ₂ e, toLinearMapₛₗ₂_ι_mul_left, e.toLinearMapₛₗ₂_real]

/-- **Contraction by `⟪v, ·⟫` is adjoint to exterior multiplication by `v`** for `gramForm V`. -/
theorem gramForm_ι_mul_right (v : V) (s t : ExteriorAlgebra ℝ V) :
    gramForm V s (ι ℝ v * t) =
      gramForm V (CliffordAlgebra.contractLeft (Q := 0) (innerₗ V v) s) t := by
  let e := stdOrthonormalBasis ℝ V
  rw [gramForm_eq_toLinearMapₛₗ₂ e, toLinearMapₛₗ₂_ι_mul_right, e.toLinearMapₛₗ₂_real]

/-- **Distinct exterior powers are orthogonal** for `gramForm V`. -/
theorem gramForm_eq_zero_of_mem_exteriorPower {k l : ℕ} (hkl : k ≠ l)
    {s t : ExteriorAlgebra ℝ V} (hs : s ∈ ⋀[ℝ]^k V) (ht : t ∈ ⋀[ℝ]^l V) :
    gramForm V s t = 0 := by
  rw [gramForm_eq_toLinearMapₛₗ₂ (stdOrthonormalBasis ℝ V)]
  exact toLinearMapₛₗ₂_eq_zero_of_mem_exteriorPower _ hkl hs ht

/-- **The Gram-determinant formula for `gramForm V`**: in every degree `k` (including `k = 0` and
`k > finrank ℝ V`), `gramForm V (u₁ ∧ ⋯ ∧ uₖ) (v₁ ∧ ⋯ ∧ vₖ) = det (⟪uᵢ, vⱼ⟫)`. -/
theorem gramForm_ιMulti_ιMulti (k : ℕ) (u v : Fin k → V) :
    gramForm V (ιMulti ℝ k u) (ιMulti ℝ k v) = (Matrix.of fun i j ↦ ⟪u i, v j⟫).det := by
  let e := stdOrthonormalBasis ℝ V
  rw [gramForm_eq_toLinearMapₛₗ₂ e, toLinearMapₛₗ₂_ιMulti_ιMulti, e.toLinearMapₛₗ₂_real]
  rfl

/-- **On each exterior power `⋀[ℝ]^k V`, `gramForm V` agrees with Mathlib's inner product.** -/
@[simp]
theorem gramForm_coe_exteriorPower {k : ℕ} (x y : ⋀[ℝ]^k V) :
    gramForm V (x : ExteriorAlgebra ℝ V) (y : ExteriorAlgebra ℝ V) = ⟪x, y⟫ := by
  have key : (gramForm V).compl₁₂ (⋀[ℝ]^k V).subtype (⋀[ℝ]^k V).subtype = innerₗ (⋀[ℝ]^k V) := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun u ↦ ?_)
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun v ↦ ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.compl₁₂_apply, Submodule.coe_subtype,
      exteriorPower.ιMulti_apply_coe, gramForm_ιMulti_ιMulti, innerₗ_apply_apply,
      exteriorPower.inner_ιMulti_ιMulti]
    rw [← Matrix.det_transpose]
    rfl
  exact LinearMap.congr_fun₂ key x y

/-- `gramForm V` is symmetric. -/
theorem isSymm_gramForm : (gramForm V).IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  rw [gramForm_eq_toLinearMapₛₗ₂ (stdOrthonormalBasis ℝ V),
    ← Matrix.star_toLinearMapₛₗ₂_one_apply, star_trivial]

/-- `gramForm V` is positive semidefinite. -/
theorem isPosSemidef_gramForm : (gramForm V).IsPosSemidef where
  isSymm := isSymm_gramForm
  isNonneg := ⟨fun x ↦ by
    rw [gramForm_eq_toLinearMapₛₗ₂ (stdOrthonormalBasis ℝ V)]
    exact Matrix.toLinearMapₛₗ₂_one_self_nonneg _ x⟩

/-- `gramForm V` is definite: `gramForm V x x = 0` only for `x = 0`. -/
@[simp]
theorem gramForm_self_eq_zero_iff {x : ExteriorAlgebra ℝ V} : gramForm V x x = 0 ↔ x = 0 := by
  rw [gramForm_eq_toLinearMapₛₗ₂ (stdOrthonormalBasis ℝ V)]
  exact Matrix.toLinearMapₛₗ₂_one_self_eq_zero_iff _

/-- The quadratic map of `gramForm V` is positive definite. -/
theorem posDef_toQuadraticMap_gramForm : (gramForm V).toQuadraticMap.PosDef := by
  intro x hx
  exact lt_of_le_of_ne (isPosSemidef_gramForm.isNonneg.nonneg x)
    (Ne.symm (gramForm_self_eq_zero_iff.not.mpr hx))

/-! ### Complexification of the exterior Gram metric -/

/-- **On complexified homogeneous `k`-forms, `(gramForm V).sesqComplexification` agrees with
`(innerₗ (⋀[ℝ]^k V)).sesqComplexification`.** -/
@[simp]
theorem sesqComplexification_gramForm_subtype_baseChange {k : ℕ} (x y : ℂ ⊗[ℝ] ⋀[ℝ]^k V) :
    LinearMap.BilinForm.sesqComplexification (gramForm V)
        ((⋀[ℝ]^k V).subtype.baseChange ℂ x) ((⋀[ℝ]^k V).subtype.baseChange ℂ y) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V)) x y :=
  LinearMap.BilinForm.sesqComplexification_baseChange_baseChange _
    (fun u w ↦ gramForm_coe_exteriorPower u w) x y

/-- **Complexified exterior powers of distinct degrees are orthogonal** for
`(gramForm V).sesqComplexification`. -/
theorem sesqComplexification_gramForm_subtype_baseChange_eq_zero {k l : ℕ} (hkl : k ≠ l)
    (x : ℂ ⊗[ℝ] ⋀[ℝ]^k V) (y : ℂ ⊗[ℝ] ⋀[ℝ]^l V) :
    LinearMap.BilinForm.sesqComplexification (gramForm V)
        ((⋀[ℝ]^k V).subtype.baseChange ℂ x) ((⋀[ℝ]^l V).subtype.baseChange ℂ y) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂, add_zero]
  | tmul z u =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂, add_zero]
    | tmul w v =>
      simp [gramForm_eq_zero_of_mem_exteriorPower hkl u.2 v.2]

end ExteriorAlgebra

namespace OrthonormalBasis

variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [Fintype I] [LinearOrder I] (e : OrthonormalBasis I ℝ V)

/-- **Under `ExteriorAlgebra.baseChangeEquiv`, the wedge-basis Hermitian form on
`ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)` is `(ExteriorAlgebra.gramForm V).sesqComplexification`.** -/
theorem toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv
    (x y : ℂ ⊗[ℝ] ExteriorAlgebra ℝ V) :
    Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℂ)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ x)
        (ExteriorAlgebra.baseChangeEquiv ℝ V ℂ y) =
      LinearMap.BilinForm.sesqComplexification (ExteriorAlgebra.gramForm V) x y := by
  set H := Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
    (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
    (1 : Matrix (Finset I) (Finset I) ℂ)
  have hbasis (s : Finset I) :
      ExteriorAlgebra.baseChangeEquiv ℝ V ℂ (1 ⊗ₜ e.toBasis.ExteriorAlgebra s) =
        (e.toBasis.baseChange ℂ).ExteriorAlgebra s := by
    rw [e.toBasis.exteriorAlgebra_eq_prod_map_sort,
      (e.toBasis.baseChange ℂ).exteriorAlgebra_eq_prod_map_sort,
      ← Algebra.TensorProduct.includeRight_apply (R := ℝ) (A := ℂ), map_list_prod, map_list_prod]
    simp [List.map_map, Function.comp_def, ExteriorAlgebra.baseChangeEquiv_apply]
  have htmul (c : ℂ) (u : ExteriorAlgebra ℝ V) :
      ExteriorAlgebra.baseChangeEquiv ℝ V ℂ (c ⊗ₜ[ℝ] u) =
        c • ExteriorAlgebra.baseChangeEquiv ℝ V ℂ (1 ⊗ₜ[ℝ] u) := by
    have hc : c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul]
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
  | tmul z u =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ hy₁ hy₂ => simp only [map_add, hy₁, hy₂]
    | tmul w v =>
      rw [LinearMap.BilinForm.sesqComplexification_tmul_tmul, htmul z u, htmul w v, H.map_smulₛₗ,
        LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc]
      congr 1
      have hbasis' (r : ℝ) (s : Finset I) :
          ExteriorAlgebra.baseChangeEquiv ℝ V ℂ (1 ⊗ₜ[ℝ] (r • e.toBasis.ExteriorAlgebra s)) =
            (r : ℂ) • (e.toBasis.baseChange ℂ).ExteriorAlgebra s := by
        rw [← TensorProduct.smul_tmul, Complex.real_smul, mul_one, htmul, hbasis]
      -- Both sides are ℝ-bilinear in `(u, v)`; compare them on the wedge basis of `e`.
      conv_lhs =>
        rw [← e.toBasis.ExteriorAlgebra.sum_repr u, ← e.toBasis.ExteriorAlgebra.sum_repr v]
      conv_rhs =>
        rw [← e.toBasis.ExteriorAlgebra.sum_repr u, ← e.toBasis.ExteriorAlgebra.sum_repr v]
      simp only [TensorProduct.tmul_sum, map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply,
        LinearMap.smul_apply, hbasis', H, Matrix.toLinearMapₛₗ₂_apply_basis, Matrix.one_apply,
        ExteriorAlgebra.gramForm_basis_basis, Complex.conj_ofReal, smul_eq_mul, Complex.ofReal_sum,
        Complex.ofReal_mul, apply_ite ((↑) : ℝ → ℂ), Complex.ofReal_one, Complex.ofReal_zero]

/-- **On each complex exterior power `⋀[ℂ]^k (ℂ ⊗[ℝ] V)`, the wedge-basis Hermitian form agrees
with `(innerₗ (⋀[ℝ]^k V)).sesqComplexification` along `TauCeti.exteriorPower.equivBaseChange`.** -/
theorem toLinearMapₛₗ₂_baseChange_exteriorAlgebra_coe_exteriorPower {k : ℕ}
    (x y : ⋀[ℂ]^k (ℂ ⊗[ℝ] V)) :
    Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ)
        (e.toBasis.baseChange ℂ).ExteriorAlgebra (e.toBasis.baseChange ℂ).ExteriorAlgebra
        (1 : Matrix (Finset I) (Finset I) ℂ)
        (x : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) (y : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) =
      LinearMap.BilinForm.sesqComplexification (innerₗ (⋀[ℝ]^k V))
        (TauCeti.exteriorPower.equivBaseChange ℂ k x)
        (TauCeti.exteriorPower.equivBaseChange ℂ k y) := by
  have hx : (x : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) =
      ExteriorAlgebra.baseChangeEquiv ℝ V ℂ
        ((⋀[ℝ]^k V).subtype.baseChange ℂ (TauCeti.exteriorPower.equivBaseChange ℂ k x)) := by
    rw [TauCeti.exteriorPower.subtype_baseChange_equivBaseChange, AlgEquiv.apply_symm_apply]
  have hy : (y : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) =
      ExteriorAlgebra.baseChangeEquiv ℝ V ℂ
        ((⋀[ℝ]^k V).subtype.baseChange ℂ (TauCeti.exteriorPower.equivBaseChange ℂ k y)) := by
    rw [TauCeti.exteriorPower.subtype_baseChange_equivBaseChange, AlgEquiv.apply_symm_apply]
  rw [hx, hy, e.toLinearMapₛₗ₂_baseChange_exteriorAlgebra_baseChangeEquiv,
    ExteriorAlgebra.sesqComplexification_gramForm_subtype_baseChange]

end OrthonormalBasis
