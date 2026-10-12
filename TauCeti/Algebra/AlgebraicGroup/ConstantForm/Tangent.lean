/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

/-!
# Tangent equations for a constant-form subgroup

For the subgroup of `GLₙ` defined by `g C gᵀ = C`, the tangent equation at the identity
is `X C + C Xᵀ = 0`. This identifies the image of the closed-subgroup differential
without assuming that the form is nondegenerate or that the base is a field.
The coefficients may lie in any commutative algebra over the base ring.

The computation uses the counit-valued Leibniz rule and
`HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span`, following the same quotient
method as `SpecialLinear.mem_lieSubalgebra_definingHopfIdeal_iff`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a (tangent spaces of closed subgroups).
-/

public section

open Matrix

namespace TauCeti.ConstantForm

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {n : ℕ}

/-- Differentiating the constant-form relation gives `X C + C Xᵀ` entrywise. -/
theorem derivation_relationMatrix
    (C : Matrix (Fin n) (Fin n) R)
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B))
    (i j : Fin n) :
    Bialgebra.CounitAlgebra.algEquivSelf R (GeneralLinear.coordinateHopfAlgebra R n) B
        (d (relationMatrix R n C i j)) =
      (GeneralLinear.tangentMatrix n d * C.map (algebraMap R B) +
        C.map (algebraMap R B) * (GeneralLinear.tangentMatrix n d)ᵀ) i j := by
  classical
  simp only [relationMatrix_def, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, map_sub, map_sum,
    Bialgebra.CounitAlgebra.algEquivSelf_apply_mul, GeneralLinear.genericMatrix_apply,
    GeneralLinear.coordinateHopfAlgebra_counit_X, d.map_algebraMap,
    Bialgebra.counit_mul, Bialgebra.counit_algebraMap, map_zero, mul_zero, ite_mul,
    Matrix.add_apply, GeneralLinear.tangentMatrix_apply]
  simp_rw [apply_ite]
  simp only [map_one, map_zero, ite_mul, one_mul, zero_mul, zero_add]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact @mul_comm B _ _ _

/-- An ambient tangent vector belongs to the Lie algebra of the constant-form
subgroup exactly when its matrix satisfies the linearized form equation. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff
    (C : Matrix (Fin n) (Fin n) R)
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n C) ↔
      GeneralLinear.tangentMatrix n d * C.map (algebraMap R B) +
        C.map (algebraMap R B) * (GeneralLinear.tangentMatrix n d)ᵀ = 0 := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _
    (definingHopfIdeal_toIdeal R n C)]
  constructor
  · intro h
    ext i j
    rw [← derivation_relationMatrix C d,
      h _ (relationMatrix_mem_relationSet R n C i j), map_zero, Matrix.zero_apply]
  · intro h x hx
    obtain ⟨i, j, rfl⟩ := (mem_relationSet_iff R n C).mp hx
    apply (Bialgebra.CounitAlgebra.algEquivSelf R
      (GeneralLinear.coordinateHopfAlgebra R n) B).injective
    rw [map_zero, derivation_relationMatrix C d, h, Matrix.zero_apply]

end TauCeti.ConstantForm
