/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Balanced tensor coordinates from a right-module basis

If `M` is free as a right `A`-module with basis `b`, then `M ⊗[A] N` is the direct
sum of copies of `N` indexed by `b`. Right modules use left actions of `Aᵐᵒᵖ`.
The coordinate at `i` of `m ⊗ n` is `unop (b.repr m i) • n`.

This identifies extension of scalars along a right-free algebra inclusion with
finite-support coefficient vectors, without commutativity of the balancing algebra
or finiteness of the basis. The tensor product here is `TauCeti.BalancedTensorProduct`.

## References

* G. Karpilovsky, *Projective Representations of Finite Groups* (1985).
-/

public noncomputable section

namespace Module.Basis

open MulOpposite TauCeti TauCeti.BalancedTensorProduct

variable {k A M N ι : Type*} [CommRing k] [Semiring A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
  [IsScalarTower k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N]
  [IsScalarTower k A N]

private def tensorCoordinatesBilinear : (ι →₀ Aᵐᵒᵖ) →ₗ[k] N →ₗ[k] (ι →₀ N) :=
  LinearMap.mk₂ k (fun f n => f.sum fun i a => Finsupp.single i (unop a • n))
    (fun f g n => Finsupp.sum_add_index' (by simp)
      (by intros; simp [add_smul, Finsupp.single_add]))
    (fun r f n => by
      rw [Finsupp.sum_smul_index' (by simp)]
      simp [unop_smul, smul_assoc, Finsupp.smul_sum])
    (fun f n n' => by simp [smul_add, Finsupp.single_add, Finsupp.sum_add])
    (fun r f n => by
      rw [Finsupp.smul_sum]
      congr 1
      funext i a
      rw [← smul_comm r, Finsupp.smul_single])

private theorem tensorCoordinatesBilinear_single (i : ι) (a : Aᵐᵒᵖ) (n : N) :
    tensorCoordinatesBilinear (k := k) (Finsupp.single i a) n =
      Finsupp.single i (unop a • n) := by
  classical
  simp [tensorCoordinatesBilinear]

variable (b : Basis ι Aᵐᵒᵖ M)

private def tensorCoordinates : BalancedTensorProduct k A M N →ₗ[k] (ι →₀ N) :=
  lift ((tensorCoordinatesBilinear (k := k) (A := A)).comp
    (b.repr.restrictScalars k).toLinearMap) (by
    intro a m n
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply,
      map_smul]
    induction b.repr m using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [smul_add, map_add, LinearMap.add_apply, hf, hg]
    | single i d =>
      simp [Finsupp.smul_single, tensorCoordinatesBilinear_single, smul_eq_mul,
        unop_mul, mul_smul])

private theorem tensorCoordinates_tmul (m : M) (n : N) :
    tensorCoordinates (N := N) b (tmul k A m n) =
      (b.repr m).sum fun i a => Finsupp.single i (unop a • n) := by
  simp [tensorCoordinates, tensorCoordinatesBilinear]

private theorem tensorCoordinates_basis (i : ι) (n : N) :
    tensorCoordinates (N := N) b (tmul k A (b i) n) = Finsupp.single i n := by
  classical
  simp [tensorCoordinates_tmul]

/-- Coordinates for tensoring a free right module with a left module over the same algebra.
No finiteness assumption on the basis is required. -/
def balancedTensorProductEquiv : BalancedTensorProduct k A M N ≃ₗ[k] (ι →₀ N) := by
  classical
  refine LinearEquiv.ofLinearMap (tensorCoordinates b)
    (Finsupp.lsum k fun i => BalancedTensorProduct.mk k A (b i)) ?_ ?_
  · apply Finsupp.lhom_ext'
    intro i
    ext n
    simp [LinearMap.comp_apply, Finsupp.lsum_single, tensorCoordinates_basis]
  · apply hom_ext
    intro m n
    simp only [LinearMap.comp_apply, tensorCoordinates_tmul, LinearMap.id_apply]
    rw [Finsupp.sum, map_sum]
    simp only [Finsupp.lsum_single, mk_apply, ← balance k A]
    have hreconstruct : (∑ i ∈ (b.repr m).support, b.repr m i • b i) = m := by
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr m
    simpa only [map_sum, LinearMap.flip_apply, mk_apply, op_unop] using
      congrArg ((BalancedTensorProduct.mk k A).flip n) hreconstruct

/-- The coordinate vector of a pure tensor, expressed as a finite sum. -/
theorem balancedTensorProductEquiv_tmul (m : M) (n : N) :
    b.balancedTensorProductEquiv (tmul k A m n) =
      (b.repr m).sum fun i a => Finsupp.single i (unop a • n) := by
  simp [balancedTensorProductEquiv, tensorCoordinates_tmul]

/-- The entry formula for a pure tensor. -/
@[simp]
theorem balancedTensorProductEquiv_tmul_apply (m : M) (n : N) (i : ι) :
    b.balancedTensorProductEquiv (tmul k A m n) i = unop (b.repr m i) • n := by
  classical
  rw [balancedTensorProductEquiv_tmul]
  simp +contextual [Finsupp.sum_apply, Finsupp.single_apply]

/-- Tensoring one basis vector gives an elementary coefficient vector. -/
@[simp]
theorem balancedTensorProductEquiv_basis_tmul (i : ι) (n : N) :
    b.balancedTensorProductEquiv (tmul k A (b i) n) = Finsupp.single i n := by
  simp [balancedTensorProductEquiv, tensorCoordinates_basis]

/-- The inverse inserts the right-module basis vector at the specified coordinate. -/
@[simp]
theorem balancedTensorProductEquiv_symm_single (i : ι) (n : N) :
    b.balancedTensorProductEquiv.symm (Finsupp.single i n) = tmul k A (b i) n := by
  apply b.balancedTensorProductEquiv.injective
  simp

/-- Reconstruct a balanced tensor by summing its basis tensors. -/
theorem balancedTensorProductEquiv_symm_apply (f : ι →₀ N) :
    b.balancedTensorProductEquiv.symm f = f.sum fun i n => tmul k A (b i) n := by
  classical
  rw [LinearEquiv.symm_apply_eq, Finsupp.sum, map_sum]
  simp only [balancedTensorProductEquiv_basis_tmul]
  exact (Finsupp.sum_single f).symm

section Naturality

variable {N' : Type*} [AddCommGroup N'] [Module k N'] [Module A N']
  [IsScalarTower k A N']

/-- Tensor coordinates commute with equivariant ground-ring linear maps of the left module. -/
theorem balancedTensorProductEquiv_map (f : N →ₗ[k] N')
    (hf : ∀ (a : A) n, f (a • n) = a • f n) :
    b.balancedTensorProductEquiv.toLinearMap.comp
        (BalancedTensorProduct.map LinearMap.id f (fun _ _ => rfl) hf) =
      (Finsupp.mapRange.linearMap f).comp b.balancedTensorProductEquiv.toLinearMap := by
  apply hom_ext
  intro m n
  ext i
  simp [hf]

end Naturality

end Module.Basis
