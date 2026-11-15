/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import TauCeti.LinearAlgebra.Eigenspace.Involution
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Koszul commutor for modules graded by involutions

For involutions `γ` on `E` and `δ` on `F`, the Koszul commutor exchanges the factors of
`E ⊗ F`, with a minus sign precisely when both factors are odd. Over a commutative ring
with `2` invertible the even and odd projections give this map directly on the original
module carriers. This complements `TensorProduct.gradedComm`, whose carriers are external
direct sums. It is useful when the grading is specified by a parity operator, for instance
on a graded Clifford module.
-/

public section
noncomputable section

namespace Module.End

open TensorProduct

variable {R E F : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

private def koszulCommAux (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) : E ⊗[R] F →ₗ[R] F ⊗[R] E :=
  (TensorProduct.comm R E F).toLinearMap ∘ₗ
    (map ((γ.eigenspace 1).subtype ∘ₗ eigenProjOfInvolutive hγ (one_mul 1)) 1 +
      map ((γ.eigenspace (-1)).subtype ∘ₗ
        eigenProjOfInvolutive hγ (by simp)) δ)

private theorem koszulCommAux_tmul (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (x : E) (y : F) :
    koszulCommAux γ δ hγ (x ⊗ₜ y) =
      (⅟2 : R) • (y ⊗ₜ x + y ⊗ₜ γ x + δ y ⊗ₜ x - δ y ⊗ₜ γ x) := by
  simp only [koszulCommAux, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_add,
    Function.comp_apply, Pi.add_apply, map_tmul, Submodule.coe_subtype,
    coe_eigenProjOfInvolutive_apply, one_smul, smul_add, one_apply_eq_self, add_tmul,
    neg_smul, smul_neg, map_add, comm_tmul, tmul_smul]
  simp only [tmul_smul, tmul_neg]
  module

private theorem koszulCommAux_comp (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) :
    koszulCommAux δ γ hδ ∘ₗ koszulCommAux γ δ hγ = LinearMap.id := by
  apply TensorProduct.ext'
  intro x y
  simp only [LinearMap.comp_apply, koszulCommAux_tmul, map_smul, map_add, map_sub,
    hγ x, hδ y, LinearMap.id_apply]
  -- The composite expands to `(⅟2)^2 * 4` times the tensor; these two uses of
  -- `2 * ⅟2 = 1` reduce that coefficient to `1`.
  linear_combination (norm := module)
    (2 * ⅟2 : R) • (mul_invOf_self (2 : R)) • (x ⊗ₜ[R] y) +
      (mul_invOf_self (2 : R)) • (x ⊗ₜ[R] y)

/-- The Koszul commutor for involutive parity operators: exchanging two odd vectors changes
sign. The underlying carriers retain the caller's module structures. -/
def koszulComm (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) : E ⊗[R] F ≃ₗ[R] F ⊗[R] E :=
  .ofLinearMap (koszulCommAux γ δ hγ) (koszulCommAux δ γ hδ)
    (koszulCommAux_comp δ γ hδ hγ) (koszulCommAux_comp γ δ hγ hδ)

/-- The commutor on a pure tensor, expressed using the parity operators. -/
theorem koszulComm_tmul (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) (x : E) (y : F) :
    koszulComm γ δ hγ hδ (x ⊗ₜ y) =
      (⅟2 : R) • (y ⊗ₜ x + y ⊗ₜ γ x + δ y ⊗ₜ x - δ y ⊗ₜ γ x) :=
  koszulCommAux_tmul γ δ hγ x y

/-- Exchanging the factors again is the inverse Koszul commutor. -/
theorem koszulComm_symm (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) :
    (koszulComm γ δ hγ hδ).symm = koszulComm δ γ hδ hγ := by
  rfl

/-- Applying the Koszul commutor twice, with swapped parity operators, is the identity. -/
@[simp]
theorem koszulComm_koszulComm (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) (z : E ⊗[R] F) :
    koszulComm δ γ hδ hγ (koszulComm γ δ hγ hδ z) = z :=
  (koszulComm γ δ hγ hδ).symm_apply_apply z

/-- Composing the Koszul commutors in opposite directions is the identity equivalence. -/
@[simp]
theorem koszulComm_trans_koszulComm (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) :
    (koszulComm γ δ hγ hδ).trans (koszulComm δ γ hδ hγ) = LinearEquiv.refl R (E ⊗[R] F) := by
  ext z
  exact koszulComm_koszulComm γ δ hγ hδ z

/-- Homogeneous vectors of degrees `p` and `q` acquire the Koszul sign `(-1)^(p*q)`. -/
theorem koszulComm_tmul_of_apply_eq_neg_one_pow_smul (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) {p q : ℕ} {x : E} {y : F}
    (hx : γ x = (-1 : R) ^ p • x) (hy : δ y = (-1 : R) ^ q • y) :
    koszulComm γ δ hγ hδ (x ⊗ₜ y) = (-1 : R) ^ (p * q) • (y ⊗ₜ x) := by
  rw [koszulComm_tmul, hx, hy]
  by_cases hp : Even p <;> by_cases hq : Even q <;>
    simp only [neg_one_pow_eq_ite, Nat.even_mul, hp, hq, true_or, false_or, ite_true,
      ite_false, one_smul, neg_one_smul, tmul_neg, neg_tmul, neg_neg]
  · linear_combination (norm := module) (mul_invOf_self (2 : R)) • (y ⊗ₜ[R] x)
  · linear_combination (norm := module) (mul_invOf_self (2 : R)) • (y ⊗ₜ[R] x)
  · linear_combination (norm := module) (mul_invOf_self (2 : R)) • (y ⊗ₜ[R] x)
  · linear_combination (norm := module) -(mul_invOf_self (2 : R)) • (y ⊗ₜ[R] x)

/-- The Koszul commutor preserves the tensor parity operator. -/
theorem koszulComm_map (γ : Module.End R E) (δ : Module.End R F)
    (hγ : Function.Involutive γ) (hδ : Function.Involutive δ) (z : E ⊗[R] F) :
    koszulComm γ δ hγ hδ (map γ δ z) = map δ γ (koszulComm γ δ hγ hδ z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp only [map_tmul, koszulComm_tmul, hγ x, hδ y, map_smul, map_add, map_sub]
  | add a b ha hb => simp only [map_add, ha, hb]

end Module.End
