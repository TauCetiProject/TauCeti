/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Differential
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.TensorProduct

/-!
# Points and tangent vectors acting on a tensor product of comodules

The tensor product `M ⊗ N` of two comodules over a bialgebra `H` carries the diagonal coaction
`m ⊗ n ↦ m₀ ⊗ n₀ ⊗ m₁ n₁` (`TauCeti.Comodule.tensor`). This file computes the two actions that a
comodule representation induces on it:

* a base-valued point `g` of `H` acts **diagonally**, `g • (m ⊗ n) = g • m ⊗ g • n`, because `g`
  is multiplicative;
* a tangent vector `d` at the identity acts by the **Leibniz rule**,
  `d • (m ⊗ n) = d • m ⊗ n + m ⊗ d • n`, because `d` is a derivation into the counit
  coefficients.

The first is the statement that the comodule tensor product integrates the tensor product of
group representations; the second, that differentiating a representation turns tensor products
of representations of the group into tensor products of representations of its Lie algebra.

## Main results

* `TauCeti.Comodule.basePointsRepresentation_tensor_tmul`: a base-valued point acts diagonally on
  the tensor product comodule.
* `TauCeti.Comodule.differential_tensor_tmul`: a tangent vector acts on the tensor product
  comodule by the Leibniz rule.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.7 and I.7.11.
* J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 10.
-/

public section

open TensorProduct WithConv

namespace TauCeti.Comodule

attribute [local instance] tensor

section Contraction

variable {R H V W : Type*} [CommSemiring R] [Semiring H] [Algebra R H]
variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]

/-- Contracting the combined coefficient of two coacted tensors against a functional which splits
on products as `θ (a * b) = φ a * ψ b + φ' a * ψ' b` splits the contraction accordingly. -/
private theorem tensorComponent_tensorCombine {θ φ ψ φ' ψ' : H →ₗ[R] R}
    (hθ : ∀ a b, θ (a * b) = φ a * ψ b + φ' a * ψ' b) (x : V ⊗[R] H) (y : W ⊗[R] H) :
    LinearMap.tensorComponent θ (tensorCombine (R := R) (C := H) (M := V) (N := W) (x ⊗ₜ y)) =
      LinearMap.tensorComponent φ x ⊗ₜ LinearMap.tensorComponent ψ y +
        LinearMap.tensorComponent φ' x ⊗ₜ LinearMap.tensorComponent ψ' y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' =>
    simp only [TensorProduct.add_tmul, map_add, hx, hx']
    abel
  | tmul v a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' =>
      simp only [TensorProduct.tmul_add, map_add, hy, hy']
      abel
    | tmul w b =>
      simp only [tensorCombine_tmul_tmul, LinearMap.tensorComponent_tmul, hθ, add_smul,
        TensorProduct.smul_tmul_smul]

end Contraction

section Points

variable {R H V W : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid V] [Module R V] [Comodule R H V]
variable [AddCommMonoid W] [Module R W] [Comodule R H W]

/-- **A point acts diagonally on a tensor product of comodules**: a base-valued point `g` of the
Hopf algebra `H` acts on the diagonal tensor product comodule `V ⊗ W` by
`g • (v ⊗ w) = g • v ⊗ g • w`. -/
theorem basePointsRepresentation_tensor_tmul (g : WithConv (H →ₐ[R] R)) (v : V) (w : W) :
    basePointsRepresentation (H := H) (V ⊗[R] W) g (v ⊗ₜ w) =
      basePointsRepresentation (H := H) V g v ⊗ₜ basePointsRepresentation (H := H) W g w := by
  have hV : endOfPoint V g.ofConv (1 ⊗ₜ v) = 1 ⊗ₜ basePointsRepresentation (H := H) V g v := by
    apply (TensorProduct.lid R V).injective
    rw [basePointsRepresentation_apply, TensorProduct.lid_tmul, one_smul]
  have hW : endOfPoint W g.ofConv (1 ⊗ₜ w) = 1 ⊗ₜ basePointsRepresentation (H := H) W g w := by
    apply (TensorProduct.lid R W).injective
    rw [basePointsRepresentation_apply, TensorProduct.lid_tmul, one_smul]
  have h := endOfPoint_tensor_tmul g.ofConv 1 1 v w
  rw [hV, hW, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul] at h
  rw [basePointsRepresentation_apply, ← mul_one (1 : R), ← h, TensorProduct.lid_tmul, mul_one,
    one_smul]

end Points

section Tangent

variable {R H V W : Type*} [CommRing R] [CommRing H] [Bialgebra R H]
variable [AddCommGroup V] [Module R V] [Comodule R H V]
variable [AddCommGroup W] [Module R W] [Comodule R H W]

/-- **The Leibniz rule for a tensor product of comodules**: a tangent vector `d` at the identity
acts on the diagonal tensor product comodule `V ⊗ W` by `d • (v ⊗ w) = d • v ⊗ w + v ⊗ d • w`. -/
theorem differential_tensor_tmul (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) (v : V)
    (w : W) :
    differential (R := R) (H := H) (M := V ⊗[R] W) d (v ⊗ₜ w) =
      differential (R := R) (H := H) d v ⊗ₜ w + v ⊗ₜ differential (R := R) (H := H) d w := by
  have hd (a b : H) :
      ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) (a * b) =
        ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) a *
            Coalgebra.counit (R := R) b +
          Coalgebra.counit (R := R) a *
            ((Bialgebra.CounitAlgebra.algEquivSelf R H R).toLinearMap ∘ₗ d.toLinearMap) b := by
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, Derivation.leibniz, map_add,
      AlgEquiv.toLinearMap_apply, Bialgebra.CounitAlgebra.algEquivSelf_smul,
      Algebra.algebraMap_self, RingHom.id_apply]
    ring
  rw [differential_apply, differential_apply, differential_apply, tensor_coact, tensorCoact_tmul,
    tensorComponent_tensorCombine hd]
  simp only [← coactComponent_apply, coactComponent_counit, LinearMap.id_apply]

/-- The Leibniz rule for a tensor product of comodules, as an identity of linear maps:
a tangent vector acts on `V ⊗ W` by `d ⊗ 1 + 1 ⊗ d`. -/
theorem differential_tensor (d : Derivation R H (Bialgebra.CounitAlgebra R H R)) :
    differential (R := R) (H := H) (M := V ⊗[R] W) d =
      (differential (R := R) (H := H) (M := V) d).rTensor W +
        (differential (R := R) (H := H) (M := W) d).lTensor V :=
  TensorProduct.ext' fun v w ↦ by
    rw [differential_tensor_tmul, LinearMap.add_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul]

end Tangent

end TauCeti.Comodule
