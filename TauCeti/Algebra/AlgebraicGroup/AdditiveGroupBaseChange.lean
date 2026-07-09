/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup
public import TauCeti.Algebra.AlgebraicGroup.BaseChangeNaturality

/-!
# Base change of additive-group points

The vector group attached to a `k`-module `M` is represented by the symmetric bialgebra
`SymmetricAlgebra k M`. This file records the base-changed functor-of-points calculation:
if `K` is a `k`-algebra and `A` is a commutative `K`-algebra, then the convolution monoid of
`K`-algebra maps out of `K ⊗[k] SymmetricAlgebra k M` is the additive monoid of `k`-linear
maps `M →ₗ[k] A`.

The equivalence first restricts a base-changed point along
`m ↦ 1 ⊗ ι(m)` using `AlgHom.baseChangePointsMulEquiv`, then applies
`AdditiveGroup.pointsMulEquiv`. The characteristic lemmas spell out the generator values,
the inverse map on scalar multiples of generators, naturality in the value algebra, and the
one-dimensional additive group `𝔾ₐ`.

This is the additive-group worked example from the ReductiveGroups roadmap, combined with
the Layer 0 base-change target for coordinate bialgebras and their functors of points.

## Main declarations

* `TauCeti.AdditiveGroup.baseChangePointsMulEquiv`: base-changed vector-group points are
  `k`-linear maps `M →ₗ[k] A`.
* `TauCeti.AdditiveGroup.toAdd_baseChangePointsMulEquiv_apply`: the equivalence reads a
  point on `1 ⊗ ι(m)`.
* `TauCeti.AdditiveGroup.baseChangePointsMulEquiv_symm_apply_tmul_ι`: the inverse
  equivalence evaluates scalar multiples of base-changed generators.
* `TauCeti.AdditiveGroup.gaBaseChangePointsMulEquiv`: the base-changed `𝔾ₐ` points are the
  additive monoid of `A`.

## References

The generic base-change step is Tau Ceti's `AlgHom.baseChangePointsMulEquiv`; the vector-group
points calculation is Tau Ceti's `AdditiveGroup.pointsMulEquiv`. This specialization follows
the API pattern of `RootsOfUnityGroup.baseChangePointsMulEquiv`,
`SplitTorus.baseChangePointsMulEquiv`, and `DiagonalizableGroup.baseChangePointsMulEquiv`.
-/

public section

open SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w w'

variable {k : Type u} {K : Type v} {A : Type w} {M : Type w'}
variable [CommSemiring k] [CommSemiring K] [CommSemiring A]
variable [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
variable [AddCommMonoid M] [Module k M]

/-- The `A`-points of the base change `K ⊗[k] SymmetricAlgebra k M` of the vector group on
`M` are the additive monoid of `k`-linear maps `M →ₗ[k] A`.

The source is the convolution monoid of `K`-algebra maps out of the base-changed bialgebra;
the target is written multiplicatively as `Multiplicative (M →ₗ[k] A)` to match `≃*`. -/
noncomputable def baseChangePointsMulEquiv :
    WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A) ≃* Multiplicative (M →ₗ[k] A) :=
  (AlgHom.baseChangePointsMulEquiv (k := k) (K := K)
      (A := SymmetricAlgebra k M) (R := A)).symm.trans
    (pointsMulEquiv (R := k) (M := M) (A := A))

/-- The base-changed vector-group points equivalence reads a point by evaluating it on the
base-changed generator `1 ⊗ ι(m)`. -/
@[simp]
theorem toAdd_baseChangePointsMulEquiv_apply
    (F : WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A)) (m : M) :
    Multiplicative.toAdd (baseChangePointsMulEquiv F) m =
      F.ofConv (1 ⊗ₜ[k] ι k M m) := by
  rw [baseChangePointsMulEquiv, MulEquiv.trans_apply, toAdd_pointsMulEquiv_apply,
    AlgHom.baseChangePointsMulEquiv_symm_apply]

/-- The inverse base-changed vector-group points equivalence evaluates scalar multiples of
base-changed generators by scalar multiplication of the corresponding linear-map value. -/
@[simp]
theorem baseChangePointsMulEquiv_symm_apply_tmul_ι
    (φ : Multiplicative (M →ₗ[k] A)) (s : K) (m : M) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M)).symm φ).ofConv
        (s ⊗ₜ[k] ι k M m) =
      s • (Multiplicative.toAdd φ m) := by
  simp [baseChangePointsMulEquiv, pointsMulEquiv_symm_apply]

/-- The inverse base-changed vector-group points equivalence takes the generator indexed by
`m` to the value of the chosen linear map at `m`. -/
theorem baseChangePointsMulEquiv_symm_apply_ι
    (φ : Multiplicative (M →ₗ[k] A)) (m : M) :
    ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M)).symm φ).ofConv
        (1 ⊗ₜ[k] ι k M m) =
      Multiplicative.toAdd φ m := by
  rw [baseChangePointsMulEquiv_symm_apply_tmul_ι]
  simp

variable {B : Type*} [CommSemiring B] [Algebra K B] [Algebra k B] [IsScalarTower k K B]

/-- The base-changed vector-group points equivalence is natural in the value algebra:
post-composing a point with a `K`-algebra map post-composes the corresponding `k`-linear map. -/
theorem toAdd_baseChangePointsMulEquiv_mapValue (ψ : A →ₐ[K] B)
    (F : WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A)) :
    Multiplicative.toAdd
        (baseChangePointsMulEquiv
          (AlgHom.mapValue (H := K ⊗[k] SymmetricAlgebra k M) ψ F)) =
      (ψ.toLinearMap.restrictScalars k).comp
        (Multiplicative.toAdd
          (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M) F)) := by
  ext m
  rw [toAdd_baseChangePointsMulEquiv_apply, LinearMap.comp_apply,
    toAdd_baseChangePointsMulEquiv_apply, AlgHom.mapValue_apply, ofConv_toConv,
    AlgHom.comp_apply]
  rw [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply]

/-- Naturality of the base-changed vector-group points equivalence in the value algebra. -/
theorem baseChangePointsMulEquiv_mapValue (ψ : A →ₐ[K] B)
    (F : WithConv (K ⊗[k] SymmetricAlgebra k M →ₐ[K] A)) :
    baseChangePointsMulEquiv
        (AlgHom.mapValue (H := K ⊗[k] SymmetricAlgebra k M) ψ F) =
      Multiplicative.ofAdd
        ((ψ.toLinearMap.restrictScalars k).comp
          (Multiplicative.toAdd
            (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M) F))) := by
  simp only [baseChangePointsMulEquiv, MulEquiv.trans_apply,
    AlgHom.baseChangePointsMulEquiv_symm_mapValue, pointsMulEquiv_mapValue]
  congr 1

/-- Naturality of the inverse base-changed vector-group points equivalence in the value
algebra. -/
theorem mapValue_baseChangePointsMulEquiv_symm_apply (ψ : A →ₐ[K] B)
    (φ : Multiplicative (M →ₗ[k] A)) :
    AlgHom.mapValue (H := K ⊗[k] SymmetricAlgebra k M) ψ
        ((baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := M)).symm φ) =
      (baseChangePointsMulEquiv (k := k) (K := K) (A := B) (M := M)).symm
        (Multiplicative.ofAdd ((ψ.toLinearMap.restrictScalars k).comp
          (Multiplicative.toAdd φ))) := by
  apply (baseChangePointsMulEquiv (k := k) (K := K) (A := B) (M := M)).injective
  rw [baseChangePointsMulEquiv_mapValue]
  simp

section Ga

variable {A : Type w} [CommSemiring A]
variable [Algebra K A] [Algebra k A] [IsScalarTower k K A]

/-- The base-changed one-dimensional additive group `𝔾ₐ` has `A`-points the additive monoid
of the value algebra `A`. -/
noncomputable def gaBaseChangePointsMulEquiv :
    WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A) ≃* Multiplicative A :=
  (baseChangePointsMulEquiv (k := k) (K := K) (A := A) (M := k)).trans
    (AddEquiv.toMultiplicative (LinearMap.ringLmapEquivSelf k k A).toAddEquiv)

/-- The base-changed `𝔾ₐ` points equivalence reads a point by evaluating it on
`1 ⊗ ι(1)`. -/
@[simp]
theorem toAdd_gaBaseChangePointsMulEquiv
    (F : WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A)) :
    Multiplicative.toAdd (gaBaseChangePointsMulEquiv F) =
      F.ofConv (1 ⊗ₜ[k] ι k k 1) := by
  rw [gaBaseChangePointsMulEquiv]
  simp

/-- The inverse base-changed `𝔾ₐ` points equivalence takes the generator `1 ⊗ ι(1)` to the
chosen value. -/
@[simp]
theorem gaBaseChangePointsMulEquiv_symm_apply_ι (a : Multiplicative A) :
    ((gaBaseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm a).ofConv
        (1 ⊗ₜ[k] ι k k 1) =
      Multiplicative.toAdd a := by
  rw [gaBaseChangePointsMulEquiv, MulEquiv.symm_trans_apply,
    baseChangePointsMulEquiv_symm_apply_ι]
  simp

/-- Reading a base-changed `𝔾ₐ`-point as an element of the value algebra is natural in the
value algebra: post-composing the point with a `K`-algebra map applies that map to the
corresponding element. -/
theorem toAdd_gaBaseChangePointsMulEquiv_mapValue (ψ : A →ₐ[K] B)
    (F : WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A)) :
    Multiplicative.toAdd
        (gaBaseChangePointsMulEquiv
          (AlgHom.mapValue (H := K ⊗[k] SymmetricAlgebra k k) ψ F)) =
      ψ (Multiplicative.toAdd
        (gaBaseChangePointsMulEquiv (k := k) (K := K) (A := A) F)) := by
  rw [toAdd_gaBaseChangePointsMulEquiv, toAdd_gaBaseChangePointsMulEquiv,
    AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply]

/-- The base-changed `𝔾ₐ` points equivalence is natural in the value algebra. -/
theorem gaBaseChangePointsMulEquiv_mapValue (ψ : A →ₐ[K] B)
    (F : WithConv (K ⊗[k] SymmetricAlgebra k k →ₐ[K] A)) :
    gaBaseChangePointsMulEquiv
        (AlgHom.mapValue (H := K ⊗[k] SymmetricAlgebra k k) ψ F) =
      Multiplicative.ofAdd
        (ψ (Multiplicative.toAdd
          (gaBaseChangePointsMulEquiv (k := k) (K := K) (A := A) F))) := by
  exact congrArg Multiplicative.ofAdd (toAdd_gaBaseChangePointsMulEquiv_mapValue ψ F)

/-- Naturality of the inverse base-changed `𝔾ₐ` points equivalence in the value algebra. -/
theorem mapValue_gaBaseChangePointsMulEquiv_symm_apply (ψ : A →ₐ[K] B)
    (a : Multiplicative A) :
    AlgHom.mapValue (H := K ⊗[k] SymmetricAlgebra k k) ψ
        ((gaBaseChangePointsMulEquiv (k := k) (K := K) (A := A)).symm a) =
      (gaBaseChangePointsMulEquiv (k := k) (K := K) (A := B)).symm
        (Multiplicative.ofAdd (ψ (Multiplicative.toAdd a))) := by
  apply (gaBaseChangePointsMulEquiv (k := k) (K := K) (A := B)).injective
  rw [gaBaseChangePointsMulEquiv_mapValue]
  rw [(gaBaseChangePointsMulEquiv (k := k) (K := K) (A := A)).apply_symm_apply a]
  exact ((gaBaseChangePointsMulEquiv (k := k) (K := K) (A := B)).apply_symm_apply
    (Multiplicative.ofAdd (ψ (Multiplicative.toAdd a)))).symm

end Ga

end AdditiveGroup

end TauCeti
