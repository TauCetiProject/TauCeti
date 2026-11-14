/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Finite
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import TauCeti.Algebra.HopfAlgebra.RightHopfModule.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# The Larson–Sweedler right Hopf module structure on the linear dual

For a finite projective coalgebra `H` over a commutative semiring `R`, left convolution
multiplication on `Module.Dual R H` corresponds via `TauCeti.Comodule.ofConvolutionAction` to a
canonical right `H`-comodule structure `TauCeti.Comodule.dualLeftConv R H` on `Module.Dual R H`,
characterized by
`LinearMap.tensorComponent ψ (coact φ) = (toConv ψ * toConv φ).ofConv`.
When `H` has a distinguished element `1`, the fixed subcomodule of `dualLeftConv R H` is precisely
`TauCeti.leftCointegrals R H`.

When `H` is a finite projective Hopf algebra over `R`, `Module.Dual R H` also carries the right
`H`-action `(φ ◁ h)(y) = φ(y * S(h))`. Together with `dualLeftConv R H`, this forms the
**Larson–Sweedler dual right Hopf module** `TauCeti.RightHopfModule.dual R H`. Applying the
Fundamental Theorem of Hopf Modules (`TauCeti.RightHopfModule.coinvariantsTensorEquiv`) yields the
canonical `R`-linear decomposition
`TauCeti.leftCointegralsTensorEquiv : leftCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`
sending `φ ⊗ h` to `y ↦ φ(y * S(h))`, over an arbitrary commutative semiring `R`.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94, Proposition 2.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorem 2.1.3.
-/

public section

open scoped TensorProduct Coalgebra

namespace TauCeti

universe u v

section Coalgebra

variable (R : Type u) (H : Type v) [CommSemiring R] [AddCommMonoid H] [Module R H]
  [Coalgebra R H]

/-- Left convolution multiplication on `Module.Dual R H`, bundled as an algebra homomorphism from
`WithConv (Module.Dual R H)` into `Module.End R (Module.Dual R H)`. -/
private noncomputable def leftConvAction :
    WithConv (Module.Dual R H) →ₐ[R] Module.End R (Module.Dual R H) where
  toFun ψ :=
    (WithConv.linearEquiv R (Module.Dual R H)).toLinearMap ∘ₗ
      LinearMap.mulLeft R ψ ∘ₗ
      (WithConv.linearEquiv R (Module.Dual R H)).symm.toLinearMap
  map_one' := by ext φ x; simp
  map_mul' ψ₁ ψ₂ := by ext φ x; simp [mul_apply_eq_comp]
  map_zero' := by ext φ x; simp
  map_add' ψ₁ ψ₂ := by ext φ x; simp [add_mul]
  commutes' r := by ext φ x; simp [Algebra.algebraMap_eq_smul_one]

@[simp]
private theorem leftConvAction_apply (ψ : WithConv (Module.Dual R H)) (φ : Module.Dual R H) :
    leftConvAction R H ψ φ = (ψ * WithConv.toConv φ).ofConv :=
  (rfl)

namespace Comodule

variable [Module.Finite R H] [Module.Projective R H]

/-- The right `H`-comodule structure on `Module.Dual R H` reconstructed from left convolution
multiplication via `Comodule.ofConvolutionAction`: contracting the coaction of `φ` against `ψ`
gives the convolution product `ψ * φ`. -/
@[implicit_reducible]
noncomputable def dualLeftConv : Comodule R H (Module.Dual R H) :=
  Comodule.ofConvolutionAction (leftConvAction R H)

variable {R H}

/-- Contracting `(dualLeftConv R H).coact φ` against `ψ` recovers the convolution product
`ψ * φ`. -/
theorem tensorComponent_dualLeftConv_coact (ψ φ : Module.Dual R H) :
    LinearMap.tensorComponent ψ ((dualLeftConv R H).coact φ) =
      (WithConv.toConv ψ * WithConv.toConv φ).ofConv :=
  Comodule.tensorComponent_ofConvolutionAction (leftConvAction R H) ψ φ

/-- Pointwise evaluation of `LinearMap.tensorComponent ψ ((dualLeftConv R H).coact φ)` at `y : H`.
-/
theorem tensorComponent_dualLeftConv_coact_apply (ψ φ : Module.Dual R H) (y : H) :
    LinearMap.tensorComponent ψ ((dualLeftConv R H).coact φ) y =
      ψ (TensorProduct.rid R H (φ.lTensor H (Coalgebra.comul y))) := by
  rw [tensorComponent_dualLeftConv_coact, ConvolutionDual.mul_apply_eq_lTensor]

/-- When `H` has a distinguished element `1`, the fixed vectors of `dualLeftConv R H` are
precisely the left cointegrals on `H`. -/
@[simp]
theorem dualLeftConv_fixedSubcomodule_carrier [One H] :
    (letI := dualLeftConv R H; (fixedSubcomodule R H (Module.Dual R H)).carrier) =
      leftCointegrals R H := by
  let _ := dualLeftConv R H
  ext φ
  change φ ∈ fixedSubcomodule R H (Module.Dual R H) ↔ φ ∈ leftCointegrals R H
  rw [mem_fixedSubcomodule, mem_leftCointegrals, isLeftCointegral_iff_convMul]
  change (dualLeftConv R H).coact φ = φ ⊗ₜ[R] (1 : H) ↔ _
  constructor
  · intro hφ ψ
    apply WithConv.ofConv_injective
    have hc := congrArg (LinearMap.tensorComponent ψ.ofConv) hφ
    simpa only [tensorComponent_dualLeftConv_coact, WithConv.toConv_ofConv,
      LinearMap.tensorComponent_tmul, WithConv.ofConv_smul] using hc
  · intro hφ
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro ψ
    have hc := congrArg WithConv.ofConv (hφ (WithConv.toConv ψ))
    simpa only [tensorComponent_dualLeftConv_coact, LinearMap.tensorComponent_tmul,
      WithConv.ofConv_smul, WithConv.ofConv_toConv] using hc

end Comodule

end Coalgebra

/-! ### The Larson–Sweedler dual right Hopf module -/

section HopfAlgebra

open _root_.HopfAlgebra

variable (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

/-- The right `H`-action `(φ ◁ h)(y) = φ(y * S(h))` on `Module.Dual R H`, bundled as an algebra
homomorphism from `Hᵐᵒᵖ` into `Module.End R (Module.Dual R H)`. -/
private noncomputable def dualRightAction :
    Hᵐᵒᵖ →ₐ[R] Module.End R (Module.Dual R H) where
  toFun h := LinearMap.lcomp R R (LinearMap.mulRight R (antipode R h.unop))
  map_one' := by ext φ y; simp
  map_mul' a b := by
    ext φ y
    simp [mul_apply_eq_comp, antipode_mul_antidistrib, mul_assoc]
  map_zero' := by ext φ y; simp
  map_add' a b := by ext φ y; simp [mul_add]
  commutes' r := by
    ext φ y
    simp [Algebra.algebraMap_eq_smul_one]

@[simp]
private theorem dualRightAction_op_apply (h : H) (φ : Module.Dual R H) :
    dualRightAction R H (MulOpposite.op h) φ = φ ∘ₗ LinearMap.mulRight R (antipode R h) :=
  (rfl)

namespace RightHopfModule

section Helpers

variable {R H}

/-- Pair `ψ` against the first tensor factor and `φ` against the second tensor factor of
`H ⊗[R] H`. -/
private def evalLegs (ψ φ : Module.Dual R H) : H ⊗[R] H →ₗ[R] R :=
  ψ ∘ₗ (TensorProduct.rid R H).toLinearMap ∘ₗ φ.lTensor H

private theorem lTensor_comp_mulRight (φ : Module.Dual R H) (u : H ⊗[R] H) (a : H) :
    (φ ∘ₗ LinearMap.mulRight R a).lTensor H u = φ.lTensor H (u * (1 ⊗ₜ[R] a)) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [add_mul, map_add, hu₁, hu₂]
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul]

private theorem evalLegs_comp_mulRight_left (ψ φ : Module.Dual R H) (u : H ⊗[R] H) (d : H) :
    evalLegs (ψ ∘ₗ LinearMap.mulRight R d) φ u = evalLegs ψ φ (u * (d ⊗ₜ[R] (1 : H))) := by
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ hu₁ hu₂ => simp only [add_mul, map_add, hu₁, hu₂]
  | tmul x y => simp [evalLegs, Algebra.TensorProduct.tmul_mul_tmul]

private theorem map₂_dualRightAction_tmul
    (z : Module.Dual R H ⊗[R] H) (c d : H) :
    TensorProduct.map₂
        ((dualRightAction R H).toLinearMap ∘ₗ (MulOpposite.opLinearEquiv R).toLinearMap).flip
        (LinearMap.mul R H) z (c ⊗ₜ[R] d) =
      TensorProduct.map (dualRightAction R H (MulOpposite.op c)) (LinearMap.mulRight R d) z := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, LinearMap.add_apply, hz₁, hz₂]
  | tmul φ a => rfl

end Helpers

variable [Module.Finite R H] [Module.Projective R H]

/-- **The Larson–Sweedler right Hopf module on `Module.Dual R H`** for a finite projective Hopf
algebra `H` over `R`. Its coaction is reconstructed from left convolution multiplication and its
right `H`-action is `(φ ◁ h)(y) = φ(y * S(h))`. -/
noncomputable def dual : RightHopfModule R H (Module.Dual R H) where
  toComodule := Comodule.dualLeftConv R H
  action := dualRightAction R H
  coact_action φ h := by
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro ψ
    ext y
    have hlhs :
        LinearMap.tensorComponent ψ
            ((Comodule.dualLeftConv R H).coact
              (dualRightAction R H (MulOpposite.op h) φ)) y =
          evalLegs ψ φ (Coalgebra.comul y * (1 ⊗ₜ[R] antipode R h)) := by
      rw [Comodule.tensorComponent_dualLeftConv_coact_apply, dualRightAction_op_apply,
        lTensor_comp_mulRight φ]
      rfl
    have hrhs_step (w : H ⊗[R] H) :
        LinearMap.tensorComponent ψ
            (TensorProduct.map₂
              ((dualRightAction R H).toLinearMap ∘ₗ
                (MulOpposite.opLinearEquiv R).toLinearMap).flip
              (LinearMap.mul R H)
              ((Comodule.dualLeftConv R H).coact φ) w) y =
          evalLegs ψ φ
            (Coalgebra.comul y *
              LinearMap.mul' R (H ⊗[R] H)
                (TensorProduct.map (Coalgebra.comul ∘ₗ antipode R)
                  (Algebra.TensorProduct.includeLeft (R := R) (A := H) (B := H)).toLinearMap
                  w)) := by
      induction w using TensorProduct.inductionOn with
      | add w₁ w₂ hw₁ hw₂ => simp only [map_add, LinearMap.add_apply, mul_add, hw₁, hw₂]
      | tmul c d =>
        rw [map₂_dualRightAction_tmul, LinearMap.tensorComponent_map, dualRightAction_op_apply,
          LinearMap.comp_apply, LinearMap.mulRight_apply,
          Comodule.tensorComponent_dualLeftConv_coact_apply]
        change evalLegs (ψ ∘ₗ LinearMap.mulRight R d) φ (Coalgebra.comul (y * antipode R c)) = _
        rw [Bialgebra.comul_mul, evalLegs_comp_mulRight_left, mul_assoc]
        rfl
    rw [hlhs, hrhs_step, HopfAlgebra.mul_comul_antipode_includeLeft_apply]

variable {R H}

/-- The underlying comodule of `RightHopfModule.dual` is `Comodule.dualLeftConv`. -/
@[simp]
theorem dual_toComodule :
    (dual R H).toComodule = Comodule.dualLeftConv R H :=
  (rfl)

/-- The coaction of `RightHopfModule.dual` is the coaction of `Comodule.dualLeftConv`. -/
@[simp]
theorem dual_coact :
    (dual R H).coact = (Comodule.dualLeftConv R H).coact :=
  (rfl)

/-- The right `H`-action of `RightHopfModule.dual` acts by `(φ ◁ h)(y) = φ(y * S(h))`. -/
@[simp]
theorem dual_action_op_apply (h : H) (φ : Module.Dual R H) (y : H) :
    (dual R H).action (MulOpposite.op h) φ y = φ (y * antipode R h) :=
  (rfl)

/-- The coinvariants of the Larson–Sweedler dual right Hopf module `Module.Dual R H` are
precisely the left cointegrals on `H`. -/
@[simp]
theorem dual_coinvariants :
    (dual R H).coinvariants = leftCointegrals R H :=
  (dual R H).coinvariants_eq_fixedSubcomodule.trans
    (Comodule.dualLeftConv_fixedSubcomodule_carrier (R := R) (H := H))

end RightHopfModule

section Decomposition

variable [Module.Finite R H] [Module.Projective R H]

/-- **Larson–Sweedler dual decomposition** over a commutative semiring: for any finite projective
Hopf algebra `H` over `R`, the map `φ ⊗ h ↦ (y ↦ φ(y * S(h)))` is an `R`-linear equivalence
`leftCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`. -/
noncomputable def leftCointegralsTensorEquiv :
    leftCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H :=
  (TensorProduct.congr
    (LinearEquiv.ofEq _ _ (RightHopfModule.dual_coinvariants (R := R) (H := H))).symm
    (LinearEquiv.refl R H)).trans (RightHopfModule.dual R H).coinvariantsTensorEquiv

variable {R H}

/-- On pure tensors, `leftCointegralsTensorEquiv` sends `φ ⊗ₜ h` to `y ↦ φ(y * S(h))`. -/
@[simp]
theorem leftCointegralsTensorEquiv_tmul_apply
    (φ : leftCointegrals R H) (h y : H) :
    leftCointegralsTensorEquiv R H (φ ⊗ₜ[R] h) y =
      (φ : Module.Dual R H) (y * antipode R h) := by
  simp [leftCointegralsTensorEquiv]

/-- `leftCointegralsTensorEquiv` intertwines right multiplication on the `H` tensor factor with
precomposition by right multiplication by `S(a)`. -/
@[simp]
theorem leftCointegralsTensorEquiv_lTensor_mulRight_apply
    (a : H) (z : leftCointegrals R H ⊗[R] H) (y : H) :
    leftCointegralsTensorEquiv R H
        ((LinearMap.mulRight R a).lTensor (leftCointegrals R H) z) y =
      leftCointegralsTensorEquiv R H z (y * antipode R a) := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [map_add, LinearMap.add_apply, hz₁, hz₂]
  | tmul φ h =>
    simp [antipode_mul_antidistrib, mul_assoc]

end Decomposition

end HopfAlgebra

end TauCeti
