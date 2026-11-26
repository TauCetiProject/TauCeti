/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.Algebra.AlgebraicGroup.BaseChange.Basic
public import TauCeti.Topology.Algebra.PointTopology.Group
import TauCeti.Topology.Algebra.ContinuousMulEquiv

/-!
# Point topology for base change of bialgebras

For a `k`-bialgebra `A`, a commutative `k`-algebra `K`, and a commutative topological semiring `R`
forming a scalar tower `k → K → R`, `TauCeti.AlgHom.baseChangePointsMulEquiv` identifies the
convolution monoid `WithConv (A →ₐ[k] R)` with `WithConv (K ⊗[k] A →ₐ[K] R)` via `AlgHom.liftEquiv`,
and `TauCeti.PointTopology.baseChangeHomeomorph` identifies the underlying evaluation point
topologies.

This file combines the two into the topological monoid isomorphism
`TauCeti.AlgHom.baseChangePointsContinuousMulEquiv` identifying `R`-valued convolution points of `A`
with those of the scalar extension `K ⊗[k] A` (an isomorphism of topological groups when `A` is a
Hopf algebra). In the special case of a commutative Hopf algebra `A` over an integral domain `k`
with fraction field `K`, this identifies the topological group of `R`-points of the integral model
`Spec A` over `k` with that of its generic fibre `Spec (K ⊗[k] A)` over `K`.

## Main declarations

* `TauCeti.AlgHom.baseChangePointsContinuousMulEquiv`: topological monoid isomorphism
  `WithConv (A →ₐ[k] R) ≃ₜ* WithConv (K ⊗[k] A →ₐ[K] R)`.

## References

* B. Conrad, *Weil and Grothendieck approaches to adelic points*, Enseign. Math. (2) 58 (2012),
  Prop. 2.1, p. 2.
-/

public section

open TensorProduct WithConv TauCeti.PointTopology

namespace TauCeti.AlgHom

variable (k K A R : Type*) [CommSemiring k] [CommSemiring K] [Algebra k K]
  [Semiring A] [_root_.Bialgebra k A] [CommSemiring R] [Algebra k R] [Algebra K R]
  [IsScalarTower k K R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- The scalar-extension adjunction is a topological monoid isomorphism on convolution points over
a topological semiring `R`. -/
noncomputable def baseChangePointsContinuousMulEquiv :
    WithConv (A →ₐ[k] R) ≃ₜ* WithConv (K ⊗[k] A →ₐ[K] R) where
  toMulEquiv := baseChangePointsMulEquiv (k := k) (K := K) (A := A) (R := R)
  continuous_toFun := isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.mpr <|
    ((baseChangeHomeomorph k K A R).symm.continuous.comp isHomeomorph_ofConv.continuous).congr
      fun f ↦ Algebra.TensorProduct.ext' fun c a ↦ by simp
  continuous_invFun := isHomeomorph_ofConv.isEmbedding.isInducing.continuous_iff.mpr <|
    ((baseChangeHomeomorph k K A R).continuous.comp isHomeomorph_ofConv.continuous).congr
      fun f ↦ AlgHom.ext fun a ↦ by simp

@[simp]
theorem coe_baseChangePointsContinuousMulEquiv :
    (baseChangePointsContinuousMulEquiv k K A R :
      WithConv (A →ₐ[k] R) ≃* WithConv (K ⊗[k] A →ₐ[K] R)) =
      baseChangePointsMulEquiv :=
  (rfl)

@[simp]
theorem baseChangePointsContinuousMulEquiv_apply_ofConv (f : WithConv (A →ₐ[k] R)) :
    (baseChangePointsContinuousMulEquiv k K A R f).ofConv =
      AlgHom.liftEquiv k K A R f.ofConv :=
  (congrArg ofConv (DFunLike.congr_fun (coe_baseChangePointsContinuousMulEquiv k K A R) f)).trans
    (baseChangePointsMulEquiv_apply_ofConv f)

@[simp]
theorem baseChangePointsContinuousMulEquiv_symm_ofConv (f : WithConv (K ⊗[k] A →ₐ[K] R)) :
    ((baseChangePointsContinuousMulEquiv k K A R).symm f).ofConv =
      (AlgHom.liftEquiv k K A R).symm f.ofConv :=
  (congrArg ofConv
    (ContinuousMulEquiv.symm_apply_of_coe_eq
      (coe_baseChangePointsContinuousMulEquiv k K A R) f)).trans
    (baseChangePointsMulEquiv_symm_ofConv f)

theorem baseChangePointsContinuousMulEquiv_apply_tmul
    (f : WithConv (A →ₐ[k] R)) (s : K) (a : A) :
    (baseChangePointsContinuousMulEquiv k K A R f).ofConv (s ⊗ₜ[k] a) = s • f.ofConv a := by
  rw [baseChangePointsContinuousMulEquiv_apply_ofConv, AlgHom.liftEquiv_tmul]

theorem baseChangePointsContinuousMulEquiv_symm_apply
    (f : WithConv (K ⊗[k] A →ₐ[K] R)) (a : A) :
    ((baseChangePointsContinuousMulEquiv k K A R).symm f).ofConv a = f.ofConv (1 ⊗ₜ[k] a) := by
  rw [baseChangePointsContinuousMulEquiv_symm_ofConv, AlgHom.liftEquiv_symm_apply]

end TauCeti.AlgHom
