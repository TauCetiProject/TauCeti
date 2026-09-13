/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.BaseChange
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Base change of bialgebras in stages

For a tower of commutative semirings `k → L → K` and a `k`-bialgebra `H`, extending `H` to `L`
and then to `K` agrees with extending it to `K` in one step. This file upgrades the algebra
equivalence `TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv` to a bialgebra equivalence

```text
K ⊗[L] (L ⊗[k] H) ≃ₐc[K] K ⊗[k] H.
```

When `H` is commutative, contravariantly this is the statement that the geometric fibre of the
affine monoid scheme represented by `H` — an affine group scheme when `H` is moreover a Hopf
algebra — may be computed through an intermediate field: it is what lets a group split by a finite
Galois extension be recognised over an algebraic closure.

## Main declarations

* `TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv`: the tower comparison as a
  bialgebra equivalence.
* `TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_tmul`: its value on nested pure
  tensors.
* `TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_symm_tmul`: the value of its
  inverse on pure tensors.

## References

* This formalization is adapted from the sibling comparison
  `TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv` between base change and tensor
  products.
-/

public section

open scoped TensorProduct

namespace TauCeti.Bialgebra.TensorProduct

section Tower

variable (k : Type*) (L : Type*) (H : Type*) (K : Type*)
variable [CommSemiring k] [CommSemiring L] [Algebra k L] [CommSemiring K]
variable [Algebra k K] [Algebra L K] [IsScalarTower k L K]
variable [Semiring H] [_root_.Bialgebra k H]

private theorem baseChangeTowerAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K (K ⊗[k] H)).comp
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom =
      Bialgebra.counitAlgHom K (K ⊗[L] (L ⊗[k] H)) := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [_root_.TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul l h =>
      simp [Algebra.smul_def, IsScalarTower.algebraMap_apply k L K, mul_comm, mul_assoc]

-- With both comultiplications rewritten by `TauCeti.Coalgebra.baseChange_comul_tmul`, the
-- comparison is an identity between two nestings of `distribBaseChange`, checked on the
-- unspecified comultiplication `x` of an element of `H`.
private theorem _root_.TensorProduct.baseChangeTowerAlgEquiv_comul_aux
    (s : K) (l : L) (x : H ⊗[k] H) :
    (Algebra.TensorProduct.map
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom)
      (_root_.TensorProduct.AlgebraTensorModule.distribBaseChange L K
        (L ⊗[k] H) (L ⊗[k] H)
        (s ⊗ₜ[L] _root_.TensorProduct.AlgebraTensorModule.distribBaseChange k L H H
          (l ⊗ₜ[k] x))) =
      _root_.TensorProduct.AlgebraTensorModule.distribBaseChange k K H H ((l • s) ⊗ₜ[k] x) := by
  induction x using _root_.TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [_root_.TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul h₁ h₂ => simp

private theorem baseChangeTowerAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom).comp
      (Bialgebra.comulAlgHom K (K ⊗[L] (L ⊗[k] H))) =
    (Bialgebra.comulAlgHom K (K ⊗[k] H)).comp
      (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using _root_.TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [_root_.TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul l h =>
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
        AlgEquiv.coe_toAlgHom,
        TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_tmul,
        TauCeti.Coalgebra.baseChange_comul_tmul]
      exact _root_.TensorProduct.baseChangeTowerAlgEquiv_comul_aux k L H K s l
        (Coalgebra.comul (R := k) h)

/-- **Base change of bialgebras composes in stages.** For a tower `k → L → K`, extending a
`k`-bialgebra `H` to `L` and then to `K` is extending it to `K` in one step.

The underlying algebra equivalence is
`TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv`; the content added here is that it
respects the counit and the comultiplication. -/
noncomputable def baseChangeTowerBialgEquiv :
    K ⊗[L] (L ⊗[k] H) ≃ₐc[K] K ⊗[k] H :=
  BialgEquiv.ofAlgEquiv (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K)
    (baseChangeTowerAlgEquiv_counit_comp k L H K)
    (baseChangeTowerAlgEquiv_map_comp_comul k L H K)

/-- On a nested pure tensor, the tower comparison absorbs the intermediate scalar. -/
@[simp]
theorem baseChangeTowerBialgEquiv_tmul (s : K) (l : L) (h : H) :
    baseChangeTowerBialgEquiv k L H K (s ⊗ₜ[L] (l ⊗ₜ[k] h)) = (l • s) ⊗ₜ[k] h := by
  rw [baseChangeTowerBialgEquiv, _root_.BialgEquiv.ofAlgEquiv_apply]
  exact TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_tmul k L H K s l h

/-- The inverse tower comparison inserts the unit of the intermediate ring. -/
@[simp]
theorem baseChangeTowerBialgEquiv_symm_tmul (s : K) (h : H) :
    (baseChangeTowerBialgEquiv k L H K).symm (s ⊗ₜ[k] h) = s ⊗ₜ[L] (1 ⊗ₜ[k] h) := by
  -- `BialgEquiv.ofAlgEquiv` retains the inverse of the supplied algebra equivalence.
  change (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).symm (s ⊗ₜ[k] h) = _
  exact TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_symm_tmul k L H K s h

end Tower

end TauCeti.Bialgebra.TensorProduct
