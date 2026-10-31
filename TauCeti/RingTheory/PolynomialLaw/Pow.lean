/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Homogeneous
public import Mathlib.LinearAlgebra.TensorAlgebra.ToTensorPower
public import Mathlib.RingTheory.TensorProduct.Basic
import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Power laws

For an `R`-algebra `A`, associative and unital but not necessarily commutative, and `d : ℕ`, the
`d`-th power `x ↦ x ^ d` is a polynomial law `A →ₚₗ[R] A`, homogeneous of degree `d`: after scalar
extension to a commutative `R`-algebra `S` it is the `d`-th power in the `S`-algebra `S ⊗[R] A`.

Applied in the tensor algebra of a module `M` to the degree-one generators, it gives the tensor
power law `m ↦ m ⊗ ⋯ ⊗ m : M → ⨂[R]^d M`, again homogeneous of degree `d`. After scalar extension
it sends a finite sum `∑ⱼ sⱼ ⊗ mⱼ` to the sum over all words `w` of length `d` of
`(∏ₜ s_{w t}) ⊗ m_{w 0} ⊗ ⋯ ⊗ m_{w (d - 1)}`; no factorial is inverted. Through Roby
representability this law gives the comparison of homogeneous divided powers with symmetric tensors.

## Main declarations

* `PolynomialLaw.pow R A d`: the power law `x ↦ x ^ d` on `A`, with
  `PolynomialLaw.pow_toFun`, `PolynomialLaw.ground_pow` and
  `PolynomialLaw.isHomogeneousOfDegree_pow`.
* `PolynomialLaw.tensorPower R M d`: the tensor power law `m ↦ m ⊗ ⋯ ⊗ m`, with
  `PolynomialLaw.tensorPower_toFun_sum_tmul`, `PolynomialLaw.ground_tensorPower` and
  `PolynomialLaw.isHomogeneousOfDegree_tensorPower`.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963), IV §5][Roby-1963]
-/

public section

noncomputable section

universe u

open TensorProduct

namespace PolynomialLaw

variable {R : Type u} [CommSemiring R]

section Pow

variable {A : Type*} [Semiring A] [Algebra R A]

variable (R A) in
/-- The power law `x ↦ x ^ d` on an `R`-algebra `A`: after scalar extension to a commutative
`R`-algebra `S` it is the `d`-th power in the `S`-algebra `S ⊗[R] A` (`pow_toFun`). -/
def pow (d : ℕ) : A →ₚₗ[R] A where
  toFun' _ _ _ x := x ^ d
  isCompat' φ := funext fun x ↦ by
    simp only [Function.comp_apply, AlgHom.rTensor_toLinearMap_apply, map_pow]

/-- The component of the power law at a commutative `R`-algebra in the universe of `R` is the
`d`-th power. -/
theorem pow_toFun' (d : ℕ) (S : Type u) [CommSemiring S] [Algebra R S] (x : S ⊗[R] A) :
    (pow R A d).toFun' S x = x ^ d :=
  (rfl)

/-- The power law is the `d`-th power after scalar extension to a commutative `R`-algebra in
any universe. -/
@[simp]
theorem pow_toFun (d : ℕ) (S : Type*) [CommSemiring S] [Algebra R S] (x : S ⊗[R] A) :
    (pow R A d).toFun S x = x ^ d := by
  obtain ⟨n, ψ, p, rfl⟩ := exists_lift x
  rw [← isCompat_apply, ← toFun'_eq_toFun, pow_toFun', AlgHom.rTensor_toLinearMap_apply,
    AlgHom.rTensor_toLinearMap_apply, map_pow]

/-- The ground map of the power law is `x ↦ x ^ d`. -/
@[simp]
theorem ground_pow (d : ℕ) (x : A) : (pow R A d).ground x = x ^ d := by
  simp [ground_apply, toFun'_eq_toFun, Algebra.TensorProduct.tmul_pow]

/-- The power law `x ↦ x ^ d` is homogeneous of degree `d`. -/
theorem isHomogeneousOfDegree_pow (d : ℕ) : (pow R A d).IsHomogeneousOfDegree d :=
  isHomogeneousOfDegree_iff.mpr fun S _ _ s x ↦ by
    rw [toFun'_eq_toFun, pow_toFun, pow_toFun, smul_pow]

end Pow

section TensorPower

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable (R M) in
/-- The tensor power law `m ↦ m ⊗ ⋯ ⊗ m : M → ⨂[R]^d M`: the power law of the tensor algebra on
the degree-one generators, followed by the projection to the degree-`d` tensors. Its value on a
finite sum of pure tensors is `tensorPower_toFun_sum_tmul`. -/
def tensorPower (d : ℕ) : M →ₚₗ[R] ⨂[R]^d M :=
  (DirectSum.component R ℕ (fun n ↦ ⨂[R]^n M) d ∘ₗ
      TensorAlgebra.toDirectSum.toLinearMap).toPolynomialLaw.comp
    ((pow R (TensorAlgebra R M) d).comp (TensorAlgebra.ι R).toPolynomialLaw)

/-- The product of a list of pure tensors in `S ⊗[R] A` is the pure tensor of the products. -/
private theorem list_prod_ofFn_tmul {A : Type*} [Semiring A] [Algebra R A] {S : Type*}
    [CommSemiring S] [Algebra R S] {n : ℕ} (s : Fin n → S) (a : Fin n → A) :
    (List.ofFn fun t ↦ s t ⊗ₜ[R] a t).prod = (∏ t, s t) ⊗ₜ[R] (List.ofFn a).prod := by
  induction n with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

/-- The tensor power law on a finite sum of pure tensors: `(∑ⱼ sⱼ ⊗ mⱼ)^{⊗ d}` is the sum over
all words `w : Fin d → ι` with letters in `F` of `(∏ₜ s_{w t}) ⊗ (m_{w 0} ⊗ ⋯ ⊗ m_{w (d - 1)})`. -/
theorem tensorPower_toFun_sum_tmul (d : ℕ) {S : Type*} [CommSemiring S] [Algebra R S]
    {ι : Type*} (F : Finset ι) (s : ι → S) (m : ι → M) :
    (tensorPower R M d).toFun S (∑ j ∈ F, s j ⊗ₜ[R] m j) =
      ∑ w ∈ Fintype.piFinset fun _ : Fin d ↦ F,
        (∏ t, s (w t)) ⊗ₜ[R] PiTensorProduct.tprod R fun t ↦ m (w t) := by
  classical
  -- expand the `d`-th power in `S ⊗[R] TensorAlgebra R M` as a multilinear map in `d` slots
  have hpow : (∑ j ∈ F, s j ⊗ₜ[R] TensorAlgebra.ι R (m j)) ^ d =
      ∑ w ∈ Fintype.piFinset fun _ : Fin d ↦ F,
        (∏ t, s (w t)) ⊗ₜ[R] TensorAlgebra.tprod R M d fun t ↦ m (w t) := by
    rw [← MultilinearMap.mkPiAlgebraFin_apply_const (R := S),
      MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [MultilinearMap.mkPiAlgebraFin_apply, list_prod_ofFn_tmul, TensorAlgebra.tprod_apply]
  simp only [tensorPower, toFun_comp_apply, LinearMap.toPolynomialLaw_toFun, map_sum,
    LinearMap.baseChange_tmul, pow_toFun, hpow, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    TensorAlgebra.toDirectSum_tensorPower_tprod, ← DirectSum.lof_eq_of R,
    DirectSum.component.lof_self]

/-- The ground map of the tensor power law is `m ↦ m ⊗ ⋯ ⊗ m`. -/
@[simp]
theorem ground_tensorPower (d : ℕ) (m : M) :
    (tensorPower R M d).ground m = PiTensorProduct.tprod R fun _ ↦ m := by
  have h := tensorPower_toFun_sum_tmul (R := R) d (S := R) (Finset.univ : Finset Unit)
    (fun _ ↦ 1) fun _ ↦ m
  simp only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_const_one] at h
  rw [ground_apply, toFun'_eq_toFun, h]
  simp

/-- The tensor power law `m ↦ m ⊗ ⋯ ⊗ m` is homogeneous of degree `d`. -/
theorem isHomogeneousOfDegree_tensorPower (d : ℕ) :
    (tensorPower R M d).IsHomogeneousOfDegree d := by
  simpa [tensorPower] using (LinearMap.isHomogeneousOfDegree_toPolynomialLaw
    (DirectSum.component R ℕ (fun n ↦ ⨂[R]^n M) d ∘ₗ TensorAlgebra.toDirectSum.toLinearMap)).comp
    ((isHomogeneousOfDegree_pow (R := R) (A := TensorAlgebra R M) d).comp
      (LinearMap.isHomogeneousOfDegree_toPolynomialLaw (TensorAlgebra.ι R)))

end TensorPower

end PolynomialLaw
