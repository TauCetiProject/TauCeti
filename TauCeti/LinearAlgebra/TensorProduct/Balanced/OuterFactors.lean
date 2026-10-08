/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Extracting outer factors from a balanced tensor product

For a right `A`-module `M`, a left `A`-module `N`, and ground-ring modules `L`, `P`,
there is a canonical identification

`(M ⊗[k] L) ⊗[A] (N ⊗[k] P) ≃ (M ⊗[A] N) ⊗[k] (L ⊗[k] P)`.

Here the displayed `A`-tensor products mean `BalancedTensorProduct`. The `A` actions
on the ground-ring tensor products act on their first factors, as in Mathlib.
The identification isolates the middle balanced factor in compositions of bimodules
of the form `L ⊗[k] M` and `N ⊗[k] P`: first commute the factors of the first
ground-ring tensor product. In particular, a vanishing middle factor makes the
whole tensor product vanish.

We descend Mathlib's `TensorProduct.tensorTensorTensorComm` using the balanced
universal property. This is an ordinary module identification, with no flatness
assumption; it does not assert a derived tensor comparison. The tensor composition
convention follows Keller, *Deriving DG categories*, Section 6.1.
-/

public section

namespace TauCeti.BalancedTensorProduct

open MulOpposite
open scoped TensorProduct

variable (k A M N L P : Type*) [CommRing k] [Semiring A]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [SMulCommClass k Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N] [SMulCommClass k A N]
  [AddCommGroup L] [Module k L] [AddCommGroup P] [Module k P]

private def extractOuterFactors :
    BalancedTensorProduct k A (M ⊗[k] L) (N ⊗[k] P) →ₗ[k]
      BalancedTensorProduct k A M N ⊗[k] (L ⊗[k] P) :=
  lift (TensorProduct.curry <|
    TensorProduct.map (mkQ k A) LinearMap.id ∘ₗ
      (TensorProduct.tensorTensorTensorComm k M L N P).toLinearMap) (by
    intro a x y
    induction x using TensorProduct.inductionOn with
    | tmul m l =>
      induction y using TensorProduct.inductionOn with
      | tmul n p =>
        simp only [TensorProduct.curry_apply, TensorProduct.smul_tmul',
          LinearMap.comp_apply, LinearEquiv.coe_coe,
          TensorProduct.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
          mkQ_tmul, LinearMap.id_apply, balance]
      | add y y' hy hy' => simp_all only [smul_add, map_add]
    | add x x' hx hx' =>
      simp_all only [smul_add, map_add, LinearMap.add_apply])

private def insertOuterFactors :
    BalancedTensorProduct k A M N ⊗[k] (L ⊗[k] P) →ₗ[k]
      BalancedTensorProduct k A (M ⊗[k] L) (N ⊗[k] P) :=
  TensorProduct.lift <| lift (TensorProduct.curry <| TensorProduct.curry <|
    mkQ k A ∘ₗ (TensorProduct.tensorTensorTensorComm k M N L P).toLinearMap) (by
    intro a m n
    apply TensorProduct.ext'
    intro l p
    simp only [TensorProduct.curry_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.tensorTensorTensorComm_tmul, mkQ_tmul]
    simpa only [TensorProduct.smul_tmul'] using
      balance k A a (m ⊗ₜ[k] l) (n ⊗ₜ[k] p))

private theorem extractOuterFactors_tmul (m : M) (n : N) (l : L) (p : P) :
    extractOuterFactors k A M N L P (tmul k A (m ⊗ₜ[k] l) (n ⊗ₜ[k] p)) =
      tmul k A m n ⊗ₜ[k] (l ⊗ₜ[k] p) := by
  simp [extractOuterFactors]

private theorem insertOuterFactors_tmul (m : M) (n : N) (l : L) (p : P) :
    insertOuterFactors k A M N L P (tmul k A m n ⊗ₜ[k] (l ⊗ₜ[k] p)) =
      tmul k A (m ⊗ₜ[k] l) (n ⊗ₜ[k] p) := by
  simp [insertOuterFactors]

/-- Extract the two ground-ring factors on which the balancing algebra does not act.
The actions on `M ⊗ L` and `N ⊗ P` are Mathlib's first-factor actions. -/
def outerFactors :
    BalancedTensorProduct k A (M ⊗[k] L) (N ⊗[k] P) ≃ₗ[k]
      BalancedTensorProduct k A M N ⊗[k] (L ⊗[k] P) :=
  LinearEquiv.ofLinearMap (extractOuterFactors k A M N L P)
    (insertOuterFactors k A M N L P)
    (by
      apply TensorProduct.ext'
      intro x y
      induction x using induction_on with
      | ht m n =>
        induction y using TensorProduct.inductionOn with
        | tmul l p =>
          simp [extractOuterFactors_tmul, insertOuterFactors_tmul]
        | add y y' hy hy' => simp_all only [TensorProduct.tmul_add, map_add]
      | ha x x' hx hx' => simp_all only [TensorProduct.add_tmul, map_add])
    (by
      apply hom_ext
      intro x y
      induction x using TensorProduct.inductionOn with
      | tmul m l =>
        induction y using TensorProduct.inductionOn with
        | tmul n p =>
          simp [extractOuterFactors_tmul, insertOuterFactors_tmul]
        | add y y' hy hy' => simp_all only [tmul_add, map_add]
      | add x x' hx hx' => simp_all only [add_tmul, map_add])

/-- On pure tensors, `outerFactors` separates the balanced factors `m`, `n` from
the ground-ring factors `l`, `p`. -/
@[simp]
theorem outerFactors_tmul (m : M) (n : N) (l : L) (p : P) :
    outerFactors k A M N L P (tmul k A (m ⊗ₜ[k] l) (n ⊗ₜ[k] p)) =
      tmul k A m n ⊗ₜ[k] (l ⊗ₜ[k] p) := by
  simp [outerFactors, extractOuterFactors_tmul]

/-- On pure tensors, the inverse of `outerFactors` reinserts the ground-ring factors
`l`, `p` into the two arguments of the balanced tensor product. -/
@[simp]
theorem outerFactors_symm_tmul (m : M) (n : N) (l : L) (p : P) :
    (outerFactors k A M N L P).symm (tmul k A m n ⊗ₜ[k] (l ⊗ₜ[k] p)) =
      tmul k A (m ⊗ₜ[k] l) (n ⊗ₜ[k] p) := by
  simp [outerFactors, insertOuterFactors_tmul]

section Naturality

variable {M' N' L' P' : Type*}
  [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [SMulCommClass k Aᵐᵒᵖ M']
  [AddCommGroup N'] [Module k N'] [Module A N'] [SMulCommClass k A N']
  [AddCommGroup L'] [Module k L'] [AddCommGroup P'] [Module k P']

/-- Extracting outer factors commutes with tensoring equivariant maps in the acted
factors and arbitrary linear maps in the two ground-ring factors. -/
theorem outerFactors_map (f : M →ₗ[k] M') (g : N →ₗ[k] N')
    (l : L →ₗ[k] L') (p : P →ₗ[k] P')
    (hf : ∀ (a : A) m, f (op a • m) = op a • f m)
    (hg : ∀ (a : A) n, g (a • n) = a • g n) :
    (outerFactors k A M' N' L' P').toLinearMap ∘ₗ
        map (TensorProduct.map f l) (TensorProduct.map g p)
          (fun a x => by
            induction x using TensorProduct.inductionOn with
            | tmul m l => simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, hf]
            | add x y hx hy => simp only [smul_add, map_add, hx, hy])
          (fun a x => by
            induction x using TensorProduct.inductionOn with
            | tmul n p => simp only [TensorProduct.smul_tmul', TensorProduct.map_tmul, hg]
            | add x y hx hy => simp only [smul_add, map_add, hx, hy]) =
      TensorProduct.map (map f g hf hg) (TensorProduct.map l p) ∘ₗ
        (outerFactors k A M N L P).toLinearMap := by
  apply hom_ext
  intro x y
  induction x using TensorProduct.inductionOn with
  | tmul m l =>
    induction y using TensorProduct.inductionOn with
    | tmul n p => simp
    | add y y' hy hy' => simp_all only [tmul_add, map_add]
  | add x x' hx hx' => simp_all only [add_tmul, map_add]

end Naturality

end TauCeti.BalancedTensorProduct
