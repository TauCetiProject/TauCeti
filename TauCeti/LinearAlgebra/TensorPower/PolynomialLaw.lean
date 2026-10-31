/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorAlgebra.Projection
public import TauCeti.RingTheory.PolynomialLaw.Power

/-!
# The diagonal tensor polynomial law

The function `m ↦ m ⊗ ⋯ ⊗ m` extends to a homogeneous polynomial law of degree `d` with values
in `TensorPower R d M`. It is constructed by embedding `M` in its tensor algebra, taking the
`d`th power after scalar extension, and projecting to degree `d`. No factorial is inverted.
The law, rather than just its ground values, determines the integral linear comparison
from homogeneous divided powers to tensor powers.

The construction uses Mathlib's tensor algebra decomposition by Eric Wieser and its
polynomial laws by Antoine Chambert-Loir and María Inés de Frutos-Fernández. For the
comparison with divided powers see Roby, *Lois polynômes et lois formelles en théorie des
modules* (1963), Chapter IV, Theorem 2.
-/

public noncomputable section

open TensorProduct

universe u

namespace TensorPower

variable {R : Type u} [CommSemiring R] {M N : Type*}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The homogeneous degree-`d` polynomial law taking a vector to its pure tensor power. -/
def diagonalLaw (R : Type u) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]
    (d : ℕ) : M →ₚₗ[R] TensorPower R d M :=
  (TensorAlgebra.tensorPowerProjection d).toPolynomialLaw.comp
    ((PolynomialLaw.power R (TensorAlgebra R M) d).comp
      (TensorAlgebra.ι R).toPolynomialLaw)

/-- On any scalar extension, the diagonal law is the degree-`d` projection of the `d`th power
of the scalar-extended tensor algebra generator. -/
theorem diagonalLaw_toFun (d : ℕ) (S : Type*) [CommSemiring S] [Algebra R S]
    (x : S ⊗[R] M) :
    (diagonalLaw R M d).toFun S x =
      (TensorAlgebra.tensorPowerProjection d).baseChange S
        (((TensorAlgebra.ι R).baseChange S x) ^ d) := by
  simp [diagonalLaw]

/-- The ground value of the diagonal law is the pure tensor, with coefficient one. -/
@[simp]
theorem ground_diagonalLaw (d : ℕ) (m : M) :
    (diagonalLaw R M d).ground m = PiTensorProduct.tprod R (fun _ : Fin d ↦ m) := by
  simp [PolynomialLaw.ground_apply, PolynomialLaw.toFun'_eq_toFun, diagonalLaw_toFun,
    Algebra.TensorProduct.tmul_pow]

/-- The diagonal tensor law is homogeneous of degree `d`. -/
theorem isHomogeneousOfDegree_diagonalLaw (d : ℕ) :
    (diagonalLaw R M d).IsHomogeneousOfDegree d := by
  simpa only [diagonalLaw, Nat.one_mul, Nat.mul_one] using
    (LinearMap.isHomogeneousOfDegree_toPolynomialLaw
      (TensorAlgebra.tensorPowerProjection (R := R) (M := M) d)).comp
      ((PolynomialLaw.isHomogeneousOfDegree_power d).comp
        (TensorAlgebra.ι R (M := M)).isHomogeneousOfDegree_toPolynomialLaw)

/-- On a pure scalar tensor, the diagonal law raises the scalar to the `d`th power. -/
@[simp]
theorem diagonalLaw_toFun_tmul (d : ℕ) (S : Type*) [CommSemiring S] [Algebra R S]
    (s : S) (m : M) :
    (diagonalLaw R M d).toFun S (s ⊗ₜ[R] m) =
      (s ^ d) ⊗ₜ[R] PiTensorProduct.tprod R (fun _ : Fin d ↦ m) := by
  simp [diagonalLaw_toFun, Algebra.TensorProduct.tmul_pow]

/-- The product of a list of pure tensors in `S ⊗[R] A` is the pure tensor of the products. -/
private theorem list_prod_ofFn_tmul {A : Type*} [Semiring A] [Algebra R A] {S : Type*}
    [CommSemiring S] [Algebra R S] {n : ℕ} (s : Fin n → S) (a : Fin n → A) :
    (List.ofFn fun t ↦ s t ⊗ₜ[R] a t).prod = (∏ t, s t) ⊗ₜ[R] (List.ofFn a).prod := by
  induction n with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ n ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

/-- The diagonal law on a finite sum of pure tensors: `(∑ⱼ sⱼ ⊗ mⱼ)^{⊗ d}` is the sum over
all words `w : Fin d → ι` with letters in `F` of `(∏ₜ s_{w t}) ⊗ (m_{w 0} ⊗ ⋯ ⊗ m_{w (d - 1)})`. -/
theorem diagonalLaw_toFun_sum_tmul (d : ℕ) (S : Type*) [CommSemiring S] [Algebra R S]
    {ι : Type*} (F : Finset ι) (s : ι → S) (m : ι → M) :
    (diagonalLaw R M d).toFun S (∑ j ∈ F, s j ⊗ₜ[R] m j) =
      ∑ w ∈ Fintype.piFinset fun _ : Fin d ↦ F,
        (∏ t, s (w t)) ⊗ₜ[R] PiTensorProduct.tprod R fun t ↦ m (w t) := by
  classical
  -- expand the `d`th power in `S ⊗[R] TensorAlgebra R M` as a multilinear map in `d` slots
  have hpow : (∑ j ∈ F, s j ⊗ₜ[R] TensorAlgebra.ι R (m j)) ^ d =
      ∑ w ∈ Fintype.piFinset fun _ : Fin d ↦ F,
        (∏ t, s (w t)) ⊗ₜ[R] TensorAlgebra.tprod R M d fun t ↦ m (w t) := by
    rw [← MultilinearMap.mkPiAlgebraFin_apply_const (R := S), MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [MultilinearMap.mkPiAlgebraFin_apply, list_prod_ofFn_tmul, TensorAlgebra.tprod_apply]
  simp only [diagonalLaw_toFun, map_sum, LinearMap.baseChange_tmul, hpow,
    TensorAlgebra.tensorPowerProjection_tprod_self]

/-- The diagonal law is natural under linear maps, as a law on all scalar extensions. -/
theorem diagonalLaw_comp_toPolynomialLaw (d : ℕ) (f : M →ₗ[R] N) :
    (diagonalLaw R N d).comp f.toPolynomialLaw =
      (PiTensorProduct.map fun _ : Fin d ↦ f).toPolynomialLaw.comp (diagonalLaw R M d) := by
  let F := TensorAlgebra.lift R ((TensorAlgebra.ι R).comp f)
  have hι : (TensorAlgebra.ι R).comp f = F.toLinearMap.comp (TensorAlgebra.ι R) := by
    ext m
    simp [F]
  have hp := TensorAlgebra.tensorPowerProjection_comp_lift d f
  calc
    _ = (TensorAlgebra.tensorPowerProjection d).toPolynomialLaw.comp
        ((PolynomialLaw.power R (TensorAlgebra R N) d).comp
          ((TensorAlgebra.ι R).comp f).toPolynomialLaw) := by
      simp only [diagonalLaw, PolynomialLaw.comp_assoc, LinearMap.toPolynomialLaw_comp]
    _ = ((TensorAlgebra.tensorPowerProjection d).comp F.toLinearMap).toPolynomialLaw.comp
        ((PolynomialLaw.power R (TensorAlgebra R M) d).comp
          (TensorAlgebra.ι R).toPolynomialLaw) := by
      rw [hι, LinearMap.toPolynomialLaw_comp,
        PolynomialLaw.comp_assoc _ _ (PolynomialLaw.power R (TensorAlgebra R N) d),
        PolynomialLaw.power_comp_toPolynomialLaw]
      simp only [PolynomialLaw.comp_assoc, LinearMap.toPolynomialLaw_comp]
    _ = _ := by
      rw [hp]
      simp only [diagonalLaw, LinearMap.toPolynomialLaw_comp, PolynomialLaw.comp_assoc]

end TensorPower
