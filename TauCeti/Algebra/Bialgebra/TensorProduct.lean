/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Bialgebra maps and base change for tensor products

This file packages the canonical inclusions into and projections out of a tensor product of
bialgebras as bialgebra morphisms, and records their action on pure tensors. The projections are
obtained by applying the counit to the other tensor factor.

Tensor products of bialgebra maps commute with the inclusions, and compose to the identity exactly
when both factors do, which is the input for transporting isomorphisms along tensor products.

Scalar extension also commutes with tensor products of bialgebras. The resulting bialgebra
equivalence upgrades `TauCeti.Algebra.TensorProduct.baseChangeTensorAlgEquiv` and records its
action on pure tensors in both directions.

The underlying algebra equivalence upgrades Mathlib's
`TensorProduct.AlgebraTensorModule.distribBaseChange`. The bialgebra comparison supplies the
product/base-change identification for coordinate rings of direct products of affine group schemes.

The tensor-product bialgebra structure and its unit isomorphisms are from Mathlib's
`Mathlib.RingTheory.Bialgebra.TensorProduct`.
-/

public section

open TensorProduct

namespace TauCeti

namespace Bialgebra.TensorProduct

universe u v w x

variable {R H₁ H₂ : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]

/-- The left inclusion `x ↦ x ⊗ₜ 1` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₂` tensored on the right with `H₁`,
precomposed with the right-unit isomorphism `H₁ ≃ₐc[R] H₁ ⊗[R] R`. -/
noncomputable def includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (BialgHom.id R H₁) (_root_.Bialgebra.unitBialgHom R H₂)).comp
    (_root_.Bialgebra.TensorProduct.rid R R H₁).symm.toBialgHom

/-- The right inclusion `y ↦ 1 ⊗ₜ y` of a bialgebra into a tensor product of bialgebras,
packaged as a bialgebra morphism. It is the unit `R →ₐc[R] H₁` tensored on the left with `H₂`,
precomposed with the left-unit isomorphism `H₂ ≃ₐc[R] R ⊗[R] H₂`. -/
noncomputable def includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.map (_root_.Bialgebra.unitBialgHom R H₁) (BialgHom.id R H₂)).comp
    (_root_.Bialgebra.TensorProduct.lid R H₂).symm.toBialgHom

@[simp]
theorem includeLeft_apply (x : H₁) : includeLeft (H₂ := H₂) x = x ⊗ₜ[R] (1 : H₂) := by
  simp [includeLeft, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem includeRight_apply (y : H₂) : includeRight (H₁ := H₁) y = (1 : H₁) ⊗ₜ[R] y := by
  simp [includeRight, _root_.Bialgebra.unitBialgHom, Algebra.ofId_apply]

@[simp]
theorem includeLeft_toAlgHom :
    (includeLeft : H₁ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeLeft := by
  ext x
  simp only [BialgHom.coe_toAlgHom, includeLeft_apply, Algebra.TensorProduct.includeLeft_apply]

@[simp]
theorem includeRight_toAlgHom :
    (includeRight : H₂ →ₐc[R] H₁ ⊗[R] H₂).toAlgHom = Algebra.TensorProduct.includeRight := by
  ext y
  simp only [BialgHom.coe_toAlgHom, includeRight_apply, Algebra.TensorProduct.includeRight_apply]

/-- The left projection `H₁ ⊗[R] H₂ → H₁`, given on pure tensors by
`x ⊗ₜ y ↦ ε(y) • x`, as a bialgebra morphism. -/
noncomputable def projectLeft : H₁ ⊗[R] H₂ →ₐc[R] H₁ :=
  (_root_.Bialgebra.TensorProduct.rid R R H₁).toBialgHom.comp <|
    _root_.Bialgebra.TensorProduct.map (BialgHom.id R H₁)
      (_root_.Bialgebra.counitBialgHom R H₂)

/-- The right projection `H₁ ⊗[R] H₂ → H₂`, given on pure tensors by
`x ⊗ₜ y ↦ ε(x) • y`, as a bialgebra morphism. -/
noncomputable def projectRight : H₁ ⊗[R] H₂ →ₐc[R] H₂ :=
  (_root_.Bialgebra.TensorProduct.lid R H₂).toBialgHom.comp <|
    _root_.Bialgebra.TensorProduct.map (_root_.Bialgebra.counitBialgHom R H₁)
      (BialgHom.id R H₂)

@[simp]
theorem projectLeft_tmul (x : H₁) (y : H₂) :
    projectLeft (R := R) (H₁ := H₁) (H₂ := H₂) (x ⊗ₜ[R] y) =
      Coalgebra.counit (R := R) (A := H₂) y • x := by
  simp [projectLeft]

@[simp]
theorem projectRight_tmul (x : H₁) (y : H₂) :
    projectRight (R := R) (H₁ := H₁) (H₂ := H₂) (x ⊗ₜ[R] y) =
      Coalgebra.counit (R := R) (A := H₁) x • y := by
  simp [projectRight]

/-- The left projection is a retraction of the left inclusion. -/
@[simp]
theorem projectLeft_comp_includeLeft :
    (projectLeft (R := R) (H₁ := H₁) (H₂ := H₂)).comp includeLeft = BialgHom.id R H₁ := by
  ext x
  simp

/-- The right projection is a retraction of the right inclusion. -/
@[simp]
theorem projectRight_comp_includeRight :
    (projectRight (R := R) (H₁ := H₁) (H₂ := H₂)).comp includeRight = BialgHom.id R H₂ := by
  ext y
  simp

/-- Tensor products of bialgebra maps commute with the left inclusions. -/
@[simp]
theorem map_comp_includeLeft {A B C D : Type*} [Semiring A] [Semiring B] [Semiring C] [Semiring D]
    [_root_.Bialgebra R A] [_root_.Bialgebra R B] [_root_.Bialgebra R C] [_root_.Bialgebra R D]
    (φ : A →ₐc[R] B) (ψ : C →ₐc[R] D) :
    (_root_.Bialgebra.TensorProduct.map φ ψ).comp includeLeft = includeLeft.comp φ := by
  apply BialgHom.coe_toAlgHom_injective
  simp only [BialgHom.comp_toAlgHom, _root_.Bialgebra.TensorProduct.map_toAlgHom,
    includeLeft_toAlgHom, Algebra.TensorProduct.map_comp_includeLeft]

/-- Tensor products of bialgebra maps commute with the right inclusions. -/
@[simp]
theorem map_comp_includeRight {A B C D : Type*} [Semiring A] [Semiring B] [Semiring C] [Semiring D]
    [_root_.Bialgebra R A] [_root_.Bialgebra R B] [_root_.Bialgebra R C] [_root_.Bialgebra R D]
    (φ : A →ₐc[R] B) (ψ : C →ₐc[R] D) :
    (_root_.Bialgebra.TensorProduct.map φ ψ).comp includeRight = includeRight.comp ψ := by
  apply BialgHom.coe_toAlgHom_injective
  simp only [BialgHom.comp_toAlgHom, _root_.Bialgebra.TensorProduct.map_toAlgHom,
    includeRight_toAlgHom, Algebra.TensorProduct.map_comp_includeRight]

/-- Tensor products of bialgebra maps compose to the identity exactly when both factors do. The
factors are recovered by restricting along the inclusions, which the counit projections retract. -/
theorem map_comp_map_eq_id_iff {A B C D : Type*} [Semiring A] [Semiring B] [Semiring C]
    [Semiring D] [_root_.Bialgebra R A] [_root_.Bialgebra R B] [_root_.Bialgebra R C]
    [_root_.Bialgebra R D] {φ : A →ₐc[R] B} {φ' : B →ₐc[R] A} {ψ : C →ₐc[R] D}
    {ψ' : D →ₐc[R] C} :
    (_root_.Bialgebra.TensorProduct.map φ' ψ').comp (_root_.Bialgebra.TensorProduct.map φ ψ) =
        BialgHom.id R (A ⊗[R] C) ↔
      φ'.comp φ = BialgHom.id R A ∧ ψ'.comp ψ = BialgHom.id R C := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hφ, hψ⟩ ↦ ?_⟩
  · ext x
    simpa using congrArg (projectLeft (H₂ := C)) (DFunLike.congr_fun h (x ⊗ₜ[R] 1))
  · ext y
    simpa using congrArg (projectRight (H₁ := A)) (DFunLike.congr_fun h (1 ⊗ₜ[R] y))
  apply BialgHom.coe_toAlgHom_injective
  rw [BialgHom.comp_toAlgHom, _root_.Bialgebra.TensorProduct.map_toAlgHom,
    _root_.Bialgebra.TensorProduct.map_toAlgHom, ← Algebra.TensorProduct.map_comp,
    ← BialgHom.comp_toAlgHom, ← BialgHom.comp_toAlgHom, hφ, hψ]
  simp only [BialgHom.id_toAlgHom, Algebra.TensorProduct.map_id]

section BaseChange

variable (k : Type u) (K : Type w) [CommSemiring k] [CommSemiring K] [Algebra k K]
variable (H : Type v) (L : Type x) [Semiring H] [Semiring L]
variable [_root_.Bialgebra k H] [_root_.Bialgebra k L]

private theorem baseChangeTensorAlgEquiv_counit_comp :
    (Bialgebra.counitAlgHom K
        ((K ⊗[k] H) ⊗[K] (K ⊗[k] L))).comp
      (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom =
    Bialgebra.counitAlgHom K (K ⊗[k] (H ⊗[k] L)) := by
  ext h <;> simp [Algebra.smul_def]

private theorem baseChangeTensorAlgEquiv_map_comp_comul :
    (Algebra.TensorProduct.map
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom
        (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom).comp
      (Bialgebra.comulAlgHom K (K ⊗[k] (H ⊗[k] L))) =
    (Bialgebra.comulAlgHom K ((K ⊗[k] H) ⊗[K] (K ⊗[k] L))).comp
      (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).toAlgHom := by
  apply AlgHom.toLinearMap_injective
  ext h l
  simp [← (Coalgebra.Repr.arbitrary k h).eq, ← (Coalgebra.Repr.arbitrary k l).eq,
    TensorProduct.tmul_sum, TensorProduct.sum_tmul]

/-- **Base change commutes with tensor products of bialgebras.**

The underlying algebra equivalence distributes scalar extension across a tensor product. This
bundling records that it also preserves the counit and comultiplication. For commutative Hopf
algebras, it is contravariantly the canonical identification `(G × H)_K ≅ G_K × H_K` of affine
groups. -/
noncomputable def baseChangeTensorBialgEquiv :
    K ⊗[k] (H ⊗[k] L) ≃ₐc[K]
      ((K ⊗[k] H) ⊗[K] (K ⊗[k] L)) :=
  BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L)
    (R := K) (A := K ⊗[k] (H ⊗[k] L))
    (B := (K ⊗[k] H) ⊗[K] (K ⊗[k] L))
    (baseChangeTensorAlgEquiv_counit_comp k K H L)
    (baseChangeTensorAlgEquiv_map_comp_comul k K H L)

/-- The algebra equivalence underlying the product/base-change bialgebra equivalence. -/
@[simp]
theorem baseChangeTensorBialgEquiv_toAlgEquiv :
    (baseChangeTensorBialgEquiv k K H L).toAlgEquiv =
      Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L :=
  (rfl)

/-- On a pure tensor, the product/base-change equivalence puts the scalar in the first
base-changed factor. -/
@[simp]
theorem baseChangeTensorBialgEquiv_tmul (s : K) (h : H) (l : L) :
    baseChangeTensorBialgEquiv k K H L (s ⊗ₜ[k] (h ⊗ₜ[k] l)) =
      (s ⊗ₜ[k] h) ⊗ₜ[K] (1 ⊗ₜ[k] l) := by
  rw [← BialgEquiv.coe_toAlgEquiv, baseChangeTensorBialgEquiv_toAlgEquiv]
  exact Algebra.TensorProduct.baseChangeTensorAlgEquiv_tmul k K H L s h l

/-- The inverse product/base-change equivalence multiplies the two scalar coefficients. -/
@[simp]
theorem baseChangeTensorBialgEquiv_symm_tmul
    (s t : K) (h : H) (l : L) :
    (baseChangeTensorBialgEquiv k K H L).symm
        ((s ⊗ₜ[k] h) ⊗ₜ[K] (t ⊗ₜ[k] l)) =
      (s * t) ⊗ₜ[k] (h ⊗ₜ[k] l) := by
  apply EquivLike.injective (baseChangeTensorBialgEquiv k K H L)
  rw [BialgEquiv.apply_symm_apply]
  simpa only [← BialgEquiv.coe_toAlgEquiv, baseChangeTensorBialgEquiv_toAlgEquiv] using
    (Algebra.TensorProduct.baseChangeTensorAlgEquiv k K H L).symm_apply_eq.mp
      (Algebra.TensorProduct.baseChangeTensorAlgEquiv_symm_tmul k K H L s t h l)

end BaseChange

end Bialgebra.TensorProduct

end TauCeti
