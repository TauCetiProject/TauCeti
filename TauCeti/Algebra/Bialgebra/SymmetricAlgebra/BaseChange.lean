/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.SymmetricAlgebra
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Functoriality

/-!
# Base change of symmetric bialgebras

For a commutative semiring extension `k → K` and a `k`-module `M`, scalar extension of the
symmetric bialgebra on `M` is canonically the symmetric bialgebra on the scalar extension of `M`:

```text
K ⊗[k] SymmetricAlgebra k M ≃ₐc[K] SymmetricAlgebra K (K ⊗[k] M).
```

The equivalence preserves the counit and comultiplication and is characterized in both directions
on pure-tensor generators.

In rank one this is the coordinate-bialgebra calculation behind base change of the additive
group, in `TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.BaseChange`.

## Main declarations

* `SymmetricAlgebra.scalarTensorBialgEquiv`: scalar extension of a symmetric bialgebra is
  the symmetric bialgebra on the scalar-extended module.
* `SymmetricAlgebra.scalarTensorBialgEquiv_tmul_ι`: the equivalence on pure-tensor
  generators.
* `SymmetricAlgebra.scalarTensorBialgEquiv_symm_ι_tmul`: the inverse on pure-tensor
  generators.
* `SymmetricAlgebra.scalarTensorBialgEquiv_tmul_one`: the equivalence on scalar copies.

* `LinearMap.scalarTensorBialgEquiv_comp_map`: naturality under linear maps.

## References

The construction follows W. C. Waterhouse, *Introduction to Affine Group Schemes*, §1. It uses
Mathlib's `AlgHom.liftEquiv`, `SymmetricAlgebra.lift`, and
`BialgEquiv.ofAlgEquiv`, together with the bialgebra structures from
`Mathlib.RingTheory.Bialgebra.SymmetricAlgebra` and
`Mathlib.RingTheory.Bialgebra.TensorProduct`.
-/

public section

open scoped TensorProduct

namespace SymmetricAlgebra

universe u v w

variable {k : Type u} {K : Type v} {M : Type w}
variable [CommSemiring k] [CommSemiring K] [Algebra k K]
variable [AddCommMonoid M] [Module k M]

/-- The algebra map from the symmetric algebra on the scalar-extended module back to the scalar
extension of the original symmetric algebra. -/
private noncomputable def toScalarTensor :
    SymmetricAlgebra K (K ⊗[k] M) →ₐ[K] K ⊗[k] SymmetricAlgebra k M :=
  lift <| LinearMap.baseChange K (ι k M)

/-- The algebra map from the scalar extension of the symmetric algebra to the symmetric algebra
on the scalar-extended module. -/
private noncomputable def fromScalarTensor :
    K ⊗[k] SymmetricAlgebra k M →ₐ[K] SymmetricAlgebra K (K ⊗[k] M) :=
  AlgHom.liftEquiv k K (SymmetricAlgebra k M) (SymmetricAlgebra K (K ⊗[k] M)) <|
    lift <| (ι K (K ⊗[k] M)).restrictScalars k ∘ₗ TensorProduct.mk k K M 1

@[simp]
private theorem fromScalarTensor_tmul_ι (s : K) (m : M) :
    fromScalarTensor (k := k) (K := K) (M := M) (s ⊗ₜ[k] ι k M m) =
      ι K (K ⊗[k] M) (s ⊗ₜ[k] m) := by
  simp only [fromScalarTensor, AlgHom.liftEquiv_tmul, lift_ι_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, TensorProduct.mk_apply]
  rw [← map_smul, TensorProduct.smul_tmul']
  simp only [smul_eq_mul, mul_one]

@[simp]
private theorem toScalarTensor_ι_tmul (s : K) (m : M) :
    toScalarTensor (k := k) (K := K) (M := M) (ι K (K ⊗[k] M) (s ⊗ₜ[k] m)) =
      s ⊗ₜ[k] ι k M m := by
  simp [toScalarTensor]

private theorem toScalarTensor_comp_fromScalarTensor :
    (toScalarTensor (k := k) (K := K) (M := M)).comp
        (fromScalarTensor (k := k) (K := K) (M := M)) = AlgHom.id K _ := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    simp [fromScalarTensor, toScalarTensor, Algebra.smul_def,
      Algebra.TensorProduct.algebraMap_apply]
  · apply algHom_ext
    apply LinearMap.ext
    intro m
    have h :
        toScalarTensor (k := k) (K := K) (M := M)
            (fromScalarTensor (k := k) (K := K) (M := M) (1 ⊗ₜ[k] ι k M m)) =
          1 ⊗ₜ[k] ι k M m := by
      rw [fromScalarTensor_tmul_ι, toScalarTensor_ι_tmul]
    exact h

private theorem fromScalarTensor_comp_toScalarTensor :
    (fromScalarTensor (k := k) (K := K) (M := M)).comp
        (toScalarTensor (k := k) (K := K) (M := M)) = AlgHom.id K _ := by
  apply algHom_ext
  apply LinearMap.ext
  intro z
  suffices h :
      fromScalarTensor (k := k) (K := K) (M := M)
          (toScalarTensor (k := k) (K := K) (M := M) (ι K (K ⊗[k] M) z)) =
        ι K (K ⊗[k] M) z by
    exact h
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  | tmul s m => rw [toScalarTensor_ι_tmul, fromScalarTensor_tmul_ι]

/-- The underlying algebra equivalence for scalar extension of a symmetric algebra. -/
private noncomputable def scalarTensorAlgEquiv :
    K ⊗[k] SymmetricAlgebra k M ≃ₐ[K] SymmetricAlgebra K (K ⊗[k] M) :=
  AlgEquiv.ofAlgHom
    (fromScalarTensor (k := k) (K := K) (M := M))
    (toScalarTensor (k := k) (K := K) (M := M))
    (fromScalarTensor_comp_toScalarTensor (k := k) (K := K) (M := M))
    (toScalarTensor_comp_fromScalarTensor (k := k) (K := K) (M := M))

@[simp]
private theorem scalarTensorAlgEquiv_tmul_ι (s : K) (m : M) :
    scalarTensorAlgEquiv (k := k) (K := K) (M := M) (s ⊗ₜ[k] ι k M m) =
      ι K (K ⊗[k] M) (s ⊗ₜ[k] m) :=
  fromScalarTensor_tmul_ι (k := k) (K := K) (M := M) s m

private theorem scalarTensorAlgEquiv_counit_tmul_ι (m : M) :
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M)))
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M) (1 ⊗ₜ[k] ι k M m)) =
      (Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k M)) (1 ⊗ₜ[k] ι k M m) := by
  rw [scalarTensorAlgEquiv_tmul_ι, counitAlgHom_eq]
  simpa using algebraMapInv_ι (R := K) (M := K ⊗[k] M) (1 ⊗ₜ[k] m)

private theorem scalarTensorAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M))).comp
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom =
      Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k M) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    have hs :
        (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[k] SymmetricAlgebra k M) s =
          algebraMap K (K ⊗[k] SymmetricAlgebra k M) s := by
      rw [Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    simp only [AlgHom.comp_apply]
    rw [hs]
    exact (congrArg
        (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M)))
        (AlgEquiv.commutes (scalarTensorAlgEquiv (k := k) (K := K) (M := M)) s)).trans <|
      (AlgHom.commutes (Bialgebra.counitAlgHom K (SymmetricAlgebra K (K ⊗[k] M))) s).trans <|
      (AlgHom.commutes (Bialgebra.counitAlgHom K (K ⊗[k] SymmetricAlgebra k M)) s).symm
  · apply algHom_ext
    apply LinearMap.ext
    intro m
    exact scalarTensorAlgEquiv_counit_tmul_ι (k := k) (K := K) (M := M) m

private theorem scalarTensorAlgEquiv_comul_tmul_ι (m : M) :
    (Algebra.TensorProduct.map
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom)
        (Coalgebra.comul (R := K) (A := K ⊗[k] SymmetricAlgebra k M) (1 ⊗ₜ[k] ι k M m)) =
      Coalgebra.comul (R := K) (A := SymmetricAlgebra K (K ⊗[k] M))
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M) (1 ⊗ₜ[k] ι k M m)) := by
  rw [scalarTensorAlgEquiv_tmul_ι, TensorProduct.comul_tmul, Bialgebra.comul_one, comul_ι]
  simp only [TensorProduct.tmul_add, map_add, Algebra.TensorProduct.one_def,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.map_tmul]
  have hι :
      (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom (1 ⊗ₜ[k] ι k M m) =
        ι K (K ⊗[k] M) (1 ⊗ₜ[k] m) := by
    simpa only [AlgEquiv.coe_toAlgHom] using
      scalarTensorAlgEquiv_tmul_ι (k := k) (K := K) (M := M) 1 m
  have h_one :
      (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom (1 ⊗ₜ[k] 1) = 1 := by
    simpa only [Algebra.TensorProduct.one_def] using
      map_one (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
  rw [hι, h_one, comul_ι]

private theorem scalarTensorAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom).comp
        (Bialgebra.comulAlgHom K (K ⊗[k] SymmetricAlgebra k M)) =
      (Bialgebra.comulAlgHom K (SymmetricAlgebra K (K ⊗[k] M))).comp
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro s
    have hs :
        (Algebra.TensorProduct.includeLeft : K →ₐ[K] K ⊗[k] SymmetricAlgebra k M) s =
          algebraMap K (K ⊗[k] SymmetricAlgebra k M) s := by
      rw [Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    simp only [AlgHom.comp_apply]
    rw [hs]
    exact (congrArg
        (Algebra.TensorProduct.map
          (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
          (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom)
        (AlgHom.commutes (Bialgebra.comulAlgHom K (K ⊗[k] SymmetricAlgebra k M)) s)).trans <|
      (AlgHom.commutes (Algebra.TensorProduct.map
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom
        (scalarTensorAlgEquiv (k := k) (K := K) (M := M)).toAlgHom) s).trans <|
      (AlgHom.commutes (Bialgebra.comulAlgHom K (SymmetricAlgebra K (K ⊗[k] M))) s).symm.trans <|
      congrArg (Bialgebra.comulAlgHom K (SymmetricAlgebra K (K ⊗[k] M)))
        (AlgEquiv.commutes (scalarTensorAlgEquiv (k := k) (K := K) (M := M)) s).symm
  · apply algHom_ext
    apply LinearMap.ext
    intro m
    exact scalarTensorAlgEquiv_comul_tmul_ι (k := k) (K := K) (M := M) m

/-- **Symmetric bialgebras commute with scalar extension.**

The equivalence sends `s ⊗ ι(m)` to the generator `ι(s ⊗ m)` of the symmetric algebra on the
scalar-extended module. -/
noncomputable def scalarTensorBialgEquiv :
    K ⊗[k] SymmetricAlgebra k M ≃ₐc[K] SymmetricAlgebra K (K ⊗[k] M) :=
  BialgEquiv.ofAlgEquiv (scalarTensorAlgEquiv (k := k) (K := K) (M := M))
    (scalarTensorAlgEquiv_counit_comp (k := k) (K := K) (M := M))
    (scalarTensorAlgEquiv_map_comp_comul (k := k) (K := K) (M := M))

/-- The scalar-extension equivalence sends `s ⊗ ι(m)` to `ι(s ⊗ m)`. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul_ι (s : K) (m : M) :
    scalarTensorBialgEquiv (k := k) (K := K) (M := M) (s ⊗ₜ[k] ι k M m) =
      ι K (K ⊗[k] M) (s ⊗ₜ[k] m) :=
  scalarTensorAlgEquiv_tmul_ι (k := k) (K := K) (M := M) s m

/-- The inverse scalar-extension equivalence sends the generator indexed by `s ⊗ m` to
`s ⊗ ι(m)`. -/
@[simp]
theorem scalarTensorBialgEquiv_symm_ι_tmul (s : K) (m : M) :
    (scalarTensorBialgEquiv (k := k) (K := K) (M := M)).symm (ι K (K ⊗[k] M) (s ⊗ₜ[k] m)) =
      s ⊗ₜ[k] ι k M m := by
  rw [← scalarTensorBialgEquiv_tmul_ι]
  exact BialgEquiv.symm_apply_apply _ _

/-- The scalar-extension equivalence identifies the scalar copy of `K` on both sides. -/
@[simp]
theorem scalarTensorBialgEquiv_tmul_one (s : K) :
    scalarTensorBialgEquiv (k := k) (K := K) (M := M) (s ⊗ₜ[k] 1) =
      algebraMap K (SymmetricAlgebra K (K ⊗[k] M)) s := by
  calc
    _ = scalarTensorBialgEquiv (k := k) (K := K) (M := M)
        (algebraMap K (K ⊗[k] SymmetricAlgebra k M) s) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
    _ = _ := AlgEquiv.commutes
      (scalarTensorBialgEquiv (k := k) (K := K) (M := M) :
        (K ⊗[k] SymmetricAlgebra k M) ≃ₐ[K] SymmetricAlgebra K (K ⊗[k] M)) s

end SymmetricAlgebra

namespace LinearMap

open SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The scalar-extension comparison commutes with maps induced by linear maps. -/
theorem scalarTensorBialgEquiv_comp_map {N : Type*} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) :
    (scalarTensorBialgEquiv (k := R) (K := S) (M := N)).toAlgEquiv.toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id S S) (SymmetricAlgebra.map R f)) =
      (SymmetricAlgebra.map S (f.baseChange S)).comp
        (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom := by
  apply Algebra.TensorProduct.ext
  · ext
  · apply SymmetricAlgebra.algHom_ext
    ext m
    simp

end LinearMap
