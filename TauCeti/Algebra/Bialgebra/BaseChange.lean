/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.BaseChange
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Base change of bialgebras

Scalar extension preserves the bialgebra operations. Algebra homomorphisms between scalar
extensions preserve the counit and comultiplication exactly when their restrictions to the
original algebras do, with the scalar factors multiplied for the comultiplication.

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

* `TensorProduct.comulAlgHom_baseChange`: the comultiplication on a scalar extension.
* `AlgHom.map_comp_comulAlgHom_baseChange_iff`: test preservation of comultiplication on the
  original algebra.
* `AlgHom.counitAlgHom_comp_baseChange_iff`: test preservation of the counit on the original
  algebra.

* `TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv`: the tower comparison as a
  bialgebra equivalence.
* `TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_tmul`: its value on nested pure
  tensors.
* `TauCeti.Bialgebra.TensorProduct.baseChangeTowerBialgEquiv_symm_tmul`: the value of its
  inverse on pure tensors.
* `TensorProduct.baseChangeTowerBialgEquiv_symm_map`: its inverse is natural in the outer ring.

## References

* This formalization is adapted from the sibling comparison
  `TauCeti.Bialgebra.TensorProduct.baseChangeTensorBialgEquiv` between base change and tensor
  products.
-/

public section

open scoped TensorProduct

open Algebra.TensorProduct (map)
open TauCeti.Algebra (mulBaseChange)

section ScalarExtension

variable {R T H G : Type*} [CommSemiring R] [CommSemiring T] [Algebra R T]
  [Semiring H] [Semiring G] [_root_.Bialgebra R H] [_root_.Bialgebra R G]

/-- The comultiplication on a scalar extension is the extended comultiplication followed by
the distribution of scalar extension over the tensor product. -/
theorem _root_.TensorProduct.comulAlgHom_baseChange (z : T ⊗[R] G) :
    Bialgebra.comulAlgHom T (T ⊗[R] G) z =
      TensorProduct.AlgebraTensorModule.distribBaseChange R T G G
        (map (AlgHom.id R T) (Bialgebra.comulAlgHom R G) z) := by
  rw [Bialgebra.comulAlgHom_apply, TauCeti.Coalgebra.baseChange_comul, LinearMap.comp_apply]
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul a x => simp

/-- An algebra homomorphism between scalar extensions preserves comultiplication if and only
if its restriction to the original algebra does, after multiplying the scalar factors. -/
theorem _root_.AlgHom.map_comp_comulAlgHom_baseChange_iff (F : T ⊗[R] H →ₐ[T] T ⊗[R] G) :
    (map F F).comp (Bialgebra.comulAlgHom T (T ⊗[R] H)) =
        (Bialgebra.comulAlgHom T (T ⊗[R] G)).comp F ↔
      ((mulBaseChange R T G G).restrictScalars R).comp ((map ((AlgHom.liftEquiv R T H _).symm F)
          ((AlgHom.liftEquiv R T H _).symm F)).comp (Bialgebra.comulAlgHom R H)) =
        (map (AlgHom.id R T) (Bialgebra.comulAlgHom R G)).comp
          ((AlgHom.liftEquiv R T H _).symm F) := by
  set f := (AlgHom.liftEquiv R T H (T ⊗[R] G)).symm F
  have key (y : H ⊗[R] H) :
      map F F (TensorProduct.AlgebraTensorModule.distribBaseChange R T H H (1 ⊗ₜ y)) =
        TensorProduct.AlgebraTensorModule.distribBaseChange R T G G
          (mulBaseChange R T G G (map f f y)) := by
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul,
        TensorProduct.mulBaseChange_tmul_eq_distribBaseChange_symm, LinearEquiv.apply_symm_apply]
      simp [f]
  -- both sides are determined by their values on `1 ⊗ h`, computed by `key` and
  -- `comulAlgHom_baseChange`
  rw [← (AlgHom.liftEquiv R T H _).symm.injective.eq_iff, AlgHom.ext_iff, AlgHom.ext_iff]
  refine forall_congr' fun h ↦ ?_
  simp only [AlgHom.liftEquiv_symm_apply, AlgHom.comp_apply, TensorProduct.comulAlgHom_baseChange]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, key,
    (TensorProduct.AlgebraTensorModule.distribBaseChange R T G G).injective.eq_iff]
  simp only [f, AlgHom.liftEquiv_symm_apply, AlgHom.restrictScalars_apply]

/-- An algebra homomorphism between scalar extensions preserves the counit if and only if
its restriction to the original algebra does. -/
theorem _root_.AlgHom.counitAlgHom_comp_baseChange_iff (F : T ⊗[R] H →ₐ[T] T ⊗[R] G) :
    (Bialgebra.counitAlgHom T (T ⊗[R] G)).comp F =
        Bialgebra.counitAlgHom T (T ⊗[R] H) ↔
      ((Bialgebra.counitAlgHom T (T ⊗[R] G)).restrictScalars R).comp
          ((AlgHom.liftEquiv R T H _).symm F) =
        (Algebra.ofId R T).comp (Bialgebra.counitAlgHom R H) := by
  rw [← (AlgHom.liftEquiv R T H T).symm.injective.eq_iff, AlgHom.ext_iff, AlgHom.ext_iff]
  simp [Algebra.algebraMap_eq_smul_one]

end ScalarExtension

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
  induction z using _root_.TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [_root_.TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul l h =>
      simp [Algebra.smul_def, IsScalarTower.algebraMap_apply k L K, mul_comm, mul_assoc]

private theorem baseChangeTowerAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom
        (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom).comp
      (Bialgebra.comulAlgHom K (K ⊗[L] (L ⊗[k] H))) =
    (Bialgebra.comulAlgHom K (K ⊗[k] H)).comp
      (TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro s z
  induction z using _root_.TensorProduct.inductionOn with
  | add x y hx hy =>
      simpa only [_root_.TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy
  | tmul l h =>
      simp only [AlgHom.coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply,
        AlgEquiv.coe_toAlgHom,
        TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_tmul,
        TauCeti.Coalgebra.baseChange_comul_tmul]
      simpa only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        AlgEquiv.coe_toAlgHom, TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_tmul,
        ← AlgEquiv.coe_toLinearEquiv,
        TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv_toLinearEquiv] using
        DFunLike.congr_fun
          (TauCeti.Algebra.TensorProduct.map_baseChangeTowerAlgEquiv_comp_baseChangeTensorAlgEquiv
            k L H H K)
          (s ⊗ₜ[L] (l ⊗ₜ[k] Coalgebra.comul (R := k) h))

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

/-- The algebra equivalence underlying the scalar-extension tower comparison. -/
@[simp]
theorem baseChangeTowerBialgEquiv_toAlgEquiv :
    (baseChangeTowerBialgEquiv k L H K).toAlgEquiv =
      TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv k L H K :=
  (rfl)

/-- On a nested pure tensor, the tower comparison absorbs the intermediate scalar. -/
@[simp]
theorem baseChangeTowerBialgEquiv_tmul (s : K) (l : L) (h : H) :
    baseChangeTowerBialgEquiv k L H K (s ⊗ₜ[L] (l ⊗ₜ[k] h)) = (l • s) ⊗ₜ[k] h := by
  rw [← BialgEquiv.coe_toAlgEquiv, baseChangeTowerBialgEquiv_toAlgEquiv]
  exact TauCeti.Algebra.TensorProduct.baseChangeTowerAlgEquiv_tmul k L H K s l h

/-- On a tensor with unit scalar, the tower comparison extends the intermediate coefficients. -/
@[simp]
theorem _root_.TensorProduct.baseChangeTowerBialgEquiv_one_tmul (x : L ⊗[k] H) :
    baseChangeTowerBialgEquiv k L H K (1 ⊗ₜ[L] x) =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L K) (AlgHom.id k H) x := by
  induction x using _root_.TensorProduct.inductionOn with
  | add x y hx hy => simp only [_root_.TensorProduct.tmul_add, map_add, hx, hy]
  | tmul a b => simp [Algebra.smul_def]

/-- The inverse tower comparison inserts the unit of the intermediate ring. -/
@[simp]
theorem baseChangeTowerBialgEquiv_symm_tmul (s : K) (h : H) :
    (baseChangeTowerBialgEquiv k L H K).symm (s ⊗ₜ[k] h) = s ⊗ₜ[L] (1 ⊗ₜ[k] h) := by
  apply EquivLike.injective (baseChangeTowerBialgEquiv k L H K)
  simp only [BialgEquiv.apply_symm_apply, baseChangeTowerBialgEquiv_tmul, one_smul]

/-- The inverse tower comparison is natural in the outer ring: for an `L`-algebra homomorphism
`f : K →ₐ[L] K'`, it intertwines the two scalar extensions along `f`. -/
theorem _root_.TensorProduct.baseChangeTowerBialgEquiv_symm_map {K' : Type*} [CommSemiring K']
    [Algebra k K'] [Algebra L K'] [IsScalarTower k L K'] (f : K →ₐ[L] K') (x : K ⊗[k] H) :
    (baseChangeTowerBialgEquiv k L H K').symm
        (Algebra.TensorProduct.map (f.restrictScalars k) (AlgHom.id k H) x) =
      Algebra.TensorProduct.map f (AlgHom.id L (L ⊗[k] H))
        ((baseChangeTowerBialgEquiv k L H K).symm x) := by
  induction x using _root_.TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s h => simp

end Tower

end TauCeti.Bialgebra.TensorProduct
