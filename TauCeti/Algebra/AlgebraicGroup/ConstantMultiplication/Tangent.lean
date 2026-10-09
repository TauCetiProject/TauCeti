/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

/-!
# Tangent equations for a constant-multiplication subgroup

For the subgroup of `GLₙ` preserving the bilinear multiplication with constant structure matrices
`Cₖ`, defined by `g Cₖ = (∑ₐ gₐₖ Cₐ) g`, the tangent equation at the identity is

```text
X Cₖ = ∑ₐ Xₐₖ Cₐ + Cₖ X,
```

that is, `X (eₖ * v) = (X eₖ) * v + eₖ * (X v)`: the Lie algebra of the subgroup consists of the
derivations of the multiplication. This identifies the image of the closed-subgroup differential
without assuming anything about the multiplication or the base ring. The coefficients may lie in
any commutative algebra over the base ring.

The computation uses the counit-valued Leibniz rule and
`HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span`, following
`TauCeti.ConstantForm.mem_lieSubalgebra_definingHopfIdeal_iff` for the subgroup fixing a constant
form.

## Main results

* `TauCeti.ConstantMultiplication.derivation_relationMatrix`: a tangent vector of `GLₙ` sends
  each defining relation to the corresponding entry of `X Cₖ − ∑ₐ Xₐₖ Cₐ − Cₖ X`.
* `TauCeti.ConstantMultiplication.mem_lieSubalgebra_definingHopfIdeal_iff`: an ambient tangent
  vector lies in the Lie algebra of the subgroup exactly when its matrix is a derivation of the
  multiplication.
* `TauCeti.ConstantMultiplication.toMatrix_leibniz_iff`: the structure-matrix equations for
  a linear endomorphism are equivalent to its Leibniz rule.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a (tangent spaces of closed subgroups).
* J. C. Jantzen, *Representations of Algebraic Groups* (2003), I.7.
-/

public section

open Matrix

namespace TauCeti.ConstantMultiplication

universe u v

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {n : ℕ} (C : Fin n → Matrix (Fin n) (Fin n) R)

/-- Differentiating a defining relation of the constant-multiplication subgroup gives the entry
of `X Cₖ − ∑ₐ Xₐₖ Cₐ − Cₖ X`, where `X` is the tangent matrix. -/
theorem derivation_relationMatrix
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B))
    (k i j : Fin n) :
    Bialgebra.CounitAlgebra.algEquivSelf R (GeneralLinear.coordinateHopfAlgebra R n) B
        (d (relationMatrix R n C (GeneralLinear.genericMatrix R n) k i j)) =
      (GeneralLinear.tangentMatrix n d * (C k).map (algebraMap R B) -
        imageStructureMatrix R n C (GeneralLinear.tangentMatrix n d) k -
        (C k).map (algebraMap R B) * GeneralLinear.tangentMatrix n d) i j := by
  classical
  simp only [relationMatrix_def, imageStructureMatrix_def, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul, map_sub,
    map_sum, Bialgebra.CounitAlgebra.algEquivSelf_apply_mul, GeneralLinear.genericMatrix_apply,
    GeneralLinear.coordinateHopfAlgebra_counit_X, d.map_algebraMap, Bialgebra.counit_mul,
    Bialgebra.counit_algebraMap, map_zero, mul_zero, zero_add, GeneralLinear.tangentMatrix_apply]
  simp_rw [apply_ite]
  simp only [map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [apply_ite (algebraMap R B), map_zero, ite_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    mul_comm (algebraMap R B _)]
  abel

/-- An ambient tangent vector belongs to the Lie algebra of the constant-multiplication subgroup
exactly when its matrix `X` is a derivation of the multiplication:
`X Cₖ = ∑ₐ Xₐₖ Cₐ + Cₖ X` for every `k`. -/
theorem mem_lieSubalgebra_definingHopfIdeal_iff
    (d : Derivation R (GeneralLinear.coordinateHopfAlgebra R n)
      (Bialgebra.CounitAlgebra R (GeneralLinear.coordinateHopfAlgebra R n) B)) :
    d ∈ HopfIdeal.lieSubalgebra (B := B) (definingHopfIdeal R n C) ↔
      ∀ k, GeneralLinear.tangentMatrix n d * (C k).map (algebraMap R B) =
        imageStructureMatrix R n C (GeneralLinear.tangentMatrix n d) k +
          (C k).map (algebraMap R B) * GeneralLinear.tangentMatrix n d := by
  rw [HopfIdeal.mem_lieSubalgebra_iff_of_toIdeal_eq_span _ (definingHopfIdeal_toIdeal R n C)]
  constructor
  · intro h k
    rw [← sub_eq_zero, sub_add_eq_sub_sub]
    ext i j
    rw [← derivation_relationMatrix C d,
      h _ (relationMatrix_genericMatrix_mem_relationSet R n C k i j), map_zero,
      Matrix.zero_apply]
  · intro h x hx
    obtain ⟨k, i, j, rfl⟩ := (mem_relationSet_iff R n C).mp hx
    apply (Bialgebra.CounitAlgebra.algEquivSelf R
      (GeneralLinear.coordinateHopfAlgebra R n) B).injective
    rw [map_zero, derivation_relationMatrix C d, ← sub_add_eq_sub_sub, h k, sub_self,
      Matrix.zero_apply]

section Basis

variable {S T : Type*} [CommRing S] [Algebra R S]
  [NonUnitalNonAssocSemiring T] [Module S T] [IsScalarTower S T T]
  [SMulCommClass S T T]

/-- In a basis with the given structure matrices, the linearized multiplication equations
are equivalent to the associative Leibniz rule. The multiplication need not be associative
or unital. -/
theorem toMatrix_leibniz_iff (b : Module.Basis (Fin n) S T)
    (hC : ∀ k, LinearMap.toMatrix b b (LinearMap.mulLeft S (b k)) =
      (C k).map (algebraMap R S)) (f : T →ₗ[S] T) :
    (∀ k, LinearMap.toMatrix b b f * (C k).map (algebraMap R S) =
      imageStructureMatrix R n C (LinearMap.toMatrix b b f) k +
        (C k).map (algebraMap R S) * LinearMap.toMatrix b b f) ↔
      ∀ x y, f (x * y) = f x * y + x * f y := by
  simp_rw [imageStructureMatrix_toMatrix R n C b hC, ← hC,
    ← LinearMap.toMatrix_comp, ← map_add, (LinearMap.toMatrix b b).injective.eq_iff]
  constructor
  · intro h x y
    have hx : f ∘ₗ LinearMap.mulRight S y =
        LinearMap.mulRight S y ∘ₗ f + LinearMap.mulRight S (f y) :=
      b.ext fun k => by simpa using LinearMap.congr_fun (h k) y
    simpa using LinearMap.congr_fun hx x
  · intro h k
    ext y
    simp [h]

end Basis

end TauCeti.ConstantMultiplication
