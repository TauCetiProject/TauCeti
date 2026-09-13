/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant

/-!
# Discriminants in field towers

This file proves the standard discriminant identity for the basis of a composite extension
obtained from bases of the two steps in a field tower.

## Main result

* `TauCeti.Algebra.discr_smulTower`: the discriminant of `b.smulTower c` is the appropriate power of
  the discriminant of `b`, multiplied by the norm of the discriminant of `c`.

## Provenance

No formal code is vendored. The proof combines Mathlib's trace-matrix formula for a basis,
the trace transitivity formula, and determinant multiplicativity.
-/

public section

open Matrix Module

namespace TauCeti.Algebra

/-- The discriminant of the product basis in a tower is the discriminant of the lower basis,
raised to the degree of the upper step, times the norm of the upper basis discriminant. -/
theorem discr_smulTower {K : Type*} [Field K]
    {L M : Type*} [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Module.Basis ι K L) (c : Module.Basis κ L M) :
    Algebra.discr K (b.smulTower c) =
      Algebra.discr K b ^ Fintype.card κ * Algebra.norm K (Algebra.discr L c) := by
  let C : Matrix κ κ L := _root_.Algebra.traceMatrix L c
  let f : M →ₗ[L] M := Matrix.toLin c c C
  let D : Matrix (ι × κ) (ι × κ) K :=
    Matrix.blockDiagonal fun _ : κ => _root_.Algebra.traceMatrix K b
  have htrace :
      _root_.Algebra.traceMatrix K (b.smulTower c) =
        D * LinearMap.toMatrix (b.smulTower c) (b.smulTower c) (f.restrictScalars K) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [_root_.Algebra.traceMatrix_apply, Basis.smulTower_apply,
      _root_.Algebra.traceForm_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
      ← _root_.Algebra.trace_trace_of_basis b c, map_smul, smul_eq_mul, Matrix.mul_apply,
      ← Finset.univ_product_univ, Matrix.blockDiagonal_apply, LinearMap.toMatrix_apply,
      LinearMap.coe_restrictScalars, Matrix.toLin_self, Basis.smulTower_repr, map_sum,
      Basis.repr_self, Finsupp.smul_single, mul_one, Finsupp.coe_smul, Finsupp.coe_finsetSum,
      Pi.smul_apply, Finset.sum_apply, ite_mul, zero_mul, Finset.sum_product,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, D, f, C]
    have hc :
        (∑ x : κ, (Finsupp.single x (_root_.Algebra.trace L M (c x * c l)) : κ →₀ L) k) =
          _root_.Algebra.trace L M (c k * c l) := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro x _ hx
        rw [Finsupp.single_eq_of_ne hx.symm]
      · simp
    rw [hc]
    simpa [Matrix.mulVec, dotProduct, Basis.equivFun_apply, mul_comm, mul_left_comm,
      mul_assoc] using
      (congrFun (_root_.Algebra.traceMatrix_of_basis_mulVec b
        (b j * _root_.Algebra.trace L M (c k * c l))) i).symm
  rw [_root_.Algebra.discr_def, htrace, Matrix.det_mul]
  simp only [D, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ]
  rw [← _root_.Algebra.discr_def, LinearMap.det_toMatrix,
    LinearMap.det_restrictScalars]
  -- Expose the norm as the determinant of the relative trace matrix.
  change _root_.Algebra.discr K b ^ Fintype.card κ *
      _root_.Algebra.norm K (LinearMap.det (Matrix.toLin c c C)) = _
  have hC : C.det = _root_.Algebra.discr L c := by
    rfl
  rw [LinearMap.det_toLin, hC]

end TauCeti.Algebra

end
