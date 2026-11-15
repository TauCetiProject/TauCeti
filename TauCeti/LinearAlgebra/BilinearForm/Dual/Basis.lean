/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Trace

/-!
# Expansions along a basis and its dual basis for a bilinear form

Let `B` be a nondegenerate bilinear form on a vector space `V` and `b` a finite basis of `V`.
Mathlib's `LinearMap.BilinForm.dualBasis` is the basis `b'` with
`B (b' i) (b j) = if j = i then 1 else 0` (`LinearMap.BilinForm.apply_dualBasis_left`), and it reads
off coordinates in itself as `b'.repr v i = B v (b i)` (`LinearMap.BilinForm.dualBasis_repr_apply`).
This file records the companion coordinate identities for the pair `(b, b')`: coordinates in `b` are
read off by `b'`, so every vector expands in both bases with coefficients given by `B`, the sum
`∑ᵢ B (b' i) (p (b i))` is the trace of an endomorphism `p`, and for every bilinear map `f` the
contraction `∑ᵢ f (b i) (b' i)` does not depend on `b`. The last statement says that `∑ᵢ bᵢ ⊗ b'ᵢ`
is a canonical tensor attached to `B`; for the Killing form it underlies the Casimir element.

No symmetry of `B` is assumed: the dual basis always sits in the first argument of `B`.

## Main results

* `LinearMap.BilinForm.repr_apply_eq_apply_dualBasis`: coordinates in `b` are pairings against the
  dual basis.
* `LinearMap.BilinForm.sum_apply_dualBasis_smul`, `LinearMap.BilinForm.sum_apply_smul_dualBasis`:
  expansion of a vector in `b` and in its dual basis.
* `LinearMap.BilinForm.sum_apply_dualBasis_eq_trace`: contraction against the dual basis computes
  the trace.
* `LinearMap.sum_apply_dualBasis_eq`: the contraction of a bilinear map against a basis and its
  dual basis is independent of the basis.
* `LinearMap.sum_apply_dualBasis_of_isAdjointPair`: an adjoint pair of operators may be moved
  between the two slots of that contraction.
-/

public section

open Finset Module

namespace LinearMap

variable {K V W ι ι' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [DecidableEq ι] [DecidableEq ι']

namespace BilinForm

variable {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate)

/-- Coordinates in `b` are pairings against the dual basis of `b`. -/
theorem repr_apply_eq_apply_dualBasis [Finite ι] (b : Basis ι K V) (v : V) (i : ι) :
    b.repr v i = B (B.dualBasis hB b i) v := by
  have h := B.flip.dualBasis_repr_apply hB.flip (B.dualBasis hB b) v i
  rwa [dualBasis_flip_dualBasis, flip_apply] at h

variable [Fintype ι]

/-- **Expansion in `b`**, with the coefficients read off by the dual basis. -/
@[simp]
theorem sum_apply_dualBasis_smul (b : Basis ι K V) (v : V) :
    ∑ i, B (B.dualBasis hB b i) v • b i = v := by
  simp only [← repr_apply_eq_apply_dualBasis, Basis.sum_repr]

/-- **Expansion in the dual basis**, with the coefficients read off by `b`. -/
@[simp]
theorem sum_apply_smul_dualBasis (b : Basis ι K V) (v : V) :
    ∑ i, B v (b i) • B.dualBasis hB b i = v := by
  simp only [← dualBasis_repr_apply hB, Basis.sum_repr]

/-- **The sum `∑ᵢ B (b' i) (p (b i))` along a basis `b` and its dual basis `b'` is the trace of
`p`**: its terms are the diagonal entries of the matrix of `p` in `b`. -/
theorem sum_apply_dualBasis_eq_trace (b : Basis ι K V) (p : V →ₗ[K] V) :
    ∑ i, B (B.dualBasis hB b i) (p (b i)) = trace K V p := by
  simp [trace_eq_matrix_trace K b, Matrix.trace, toMatrix_apply,
    repr_apply_eq_apply_dualBasis hB]

end BilinForm

variable (f : V →ₗ[K] V →ₗ[K] W) {B : LinearMap.BilinForm K V} (hB : B.Nondegenerate) [Fintype ι]

/-- **Expansion of the first argument of a bilinear map in `b`**, with the coefficients read off
by the dual basis. -/
@[simp]
theorem sum_apply_dualBasis_smul_apply (b : Basis ι K V) (u v : V) :
    ∑ i, B (B.dualBasis hB b i) u • f (b i) v = f u v := by
  conv_rhs => rw [← BilinForm.sum_apply_dualBasis_smul hB b u]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- **Expansion of the second argument of a bilinear map in the dual basis**, with the
coefficients read off by `b`. -/
@[simp]
theorem sum_apply_smul_apply_dualBasis (b : Basis ι K V) (u v : V) :
    ∑ i, B v (b i) • f u (B.dualBasis hB b i) = f u v := by
  conv_rhs => rw [← BilinForm.sum_apply_smul_dualBasis hB b v]
  simp only [map_sum, map_smul]

/-- **The sum `∑ᵢ f (b i) (b' i)` of a bilinear map along a basis `b` and its dual basis `b'` does
not depend on the basis.**  Expanding each `c j` in the basis `b` produces exactly the coefficients
that expand `b' i` in the dual basis of `c`. -/
theorem sum_apply_dualBasis_eq [Fintype ι'] (b : Basis ι K V) (c : Basis ι' K V) :
    ∑ i, f (b i) (B.dualBasis hB b i) = ∑ j, f (c j) (B.dualBasis hB c j) :=
  calc ∑ i, f (b i) (B.dualBasis hB b i)
      = ∑ i, ∑ j, B (B.dualBasis hB b i) (c j) • f (b i) (B.dualBasis hB c j) :=
        sum_congr rfl fun i _ ↦ (f.sum_apply_smul_apply_dualBasis hB c _ _).symm
    _ = ∑ j, f (c j) (B.dualBasis hB c j) := by
        rw [Finset.sum_comm]
        exact sum_congr rfl fun j _ ↦ f.sum_apply_dualBasis_smul_apply hB b _ _

/-- **An adjoint pair of operators may be moved from one slot to the other.**  If
`B (p x) y = B x (q y)`, then applying `q` to the basis vectors `b i` and applying `p` to their
duals `b' i` give the same sum, because both expand to `∑ᵢ ∑ⱼ B (p (b' i)) (b j) • f (b i) (b' j)`.
-/
theorem sum_apply_dualBasis_of_isAdjointPair (b : Basis ι K V) {p q : V →ₗ[K] V}
    (hpq : IsAdjointPair B B p q) :
    ∑ i, f (q (b i)) (B.dualBasis hB b i) = ∑ i, f (b i) (p (B.dualBasis hB b i)) :=
  calc ∑ i, f (q (b i)) (B.dualBasis hB b i)
      = ∑ i, ∑ j, B (B.dualBasis hB b j) (q (b i)) • f (b j) (B.dualBasis hB b i) :=
        sum_congr rfl fun i _ ↦ (f.sum_apply_dualBasis_smul_apply hB b _ _).symm
    _ = ∑ i, ∑ j, B (p (B.dualBasis hB b i)) (b j) • f (b i) (B.dualBasis hB b j) := by
        rw [Finset.sum_comm]
        simp only [hpq _ _]
    _ = ∑ i, f (b i) (p (B.dualBasis hB b i)) :=
        sum_congr rfl fun i _ ↦ f.sum_apply_smul_apply_dualBasis hB b _ _

end LinearMap
