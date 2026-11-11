/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.FullCartan.Basic
public import Mathlib.Algebra.Lie.BaseChange
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Full-Cartan shell brackets after scalar extension

The scalar extension of the full-Cartan shell algebra has coordinates
`(A ⊗[ℤ] Y) × (B.normTwoShell →₀ A)`. The Cartan factor is the actual scalar extension of `Y`,
not a chosen central/coroot splitting. These coordinates work over every commutative ring,
including nonflat coefficient rings. They give a bracket formula for arbitrary Cartan tensors
and finite root combinations. In particular the formulas still apply to Cartan torsion and to
signed root-cycle torsion appearing after reduction.

`baseChangeEquiv` uses Mathlib's tensor/product and tensor/finsupp equivalences. The bracket is
Mathlib's scalar-extended Lie bracket on `A ⊗[ℤ] FullShellLieAlgebra D`; the coordinate product
is only a module product, not a product of Lie algebras. Opposite roots contribute to its
Cartan factor through the actual coroot map of `D`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, Part II, Chapter 1.
* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.
-/

public section

open scoped TensorProduct

namespace Matrix.FullShellLieAlgebra

noncomputable section

variable {I : Type*} [Fintype I] {B : Matrix I I ℤ} {Y : Type*} [AddCommGroup Y]
  (D : ShellCartanDatum B Y) (A : Type*) [CommRing A]

/-- Cartan tensors and finitely supported root coefficients of the scalar-extended algebra. -/
def baseChangeEquiv :
    A ⊗[ℤ] FullShellLieAlgebra D ≃ₗ[A] (A ⊗[ℤ] Y) × (B.normTwoShell →₀ A) :=
  LinearEquiv.baseChange ℤ A _ _ (equivProd D) ≪≫ₗ
    TensorProduct.prodRight ℤ A A Y (B.normTwoShell →₀ ℤ) ≪≫ₗ
    (LinearEquiv.refl A _).prodCongr (TensorProduct.finsuppScalarRight ℤ A A B.normTwoShell)

/-- The Cartan coordinate of a pure tensor. -/
@[simp]
theorem baseChangeEquiv_tmul_fst (r : A) (x : FullShellLieAlgebra D) :
    (baseChangeEquiv D A (r ⊗ₜ[ℤ] x)).1 = r ⊗ₜ[ℤ] (equivProd D x).1 := by
  simp [baseChangeEquiv]

/-- Each root coefficient of a pure tensor. -/
@[simp]
theorem baseChangeEquiv_tmul_snd_apply (r : A) (x : FullShellLieAlgebra D)
    (a : B.normTwoShell) :
    (baseChangeEquiv D A (r ⊗ₜ[ℤ] x)).2 a = (equivProd D x).2 a • r := by
  simp [baseChangeEquiv]

/-- Scalar extension of the Cartan inclusion has zero root coefficients. -/
@[simp]
theorem baseChangeEquiv_cartan (y : A ⊗[ℤ] Y) :
    baseChangeEquiv D A ((cartan D).baseChange A y) = (y, 0) := by
  induction y using TensorProduct.inductionOn with
  | tmul r y =>
    apply Prod.ext
    · simp
    · ext a; simp
  | add y z hy hz => simp [hy, hz]

/-- A scalar multiple of a root vector has a single nonzero root coordinate. -/
@[simp]
theorem baseChangeEquiv_tmul_root (r : A) (a : B.normTwoShell) :
    baseChangeEquiv D A (r ⊗ₜ[ℤ] root D a) = (0, Finsupp.single a r) := by
  classical
  apply Prod.ext
  · simp
  · ext b
    simp only [baseChangeEquiv_tmul_snd_apply, equivProd_root]
    by_cases h : a = b <;> simp [h]

/-- Reconstruction of a Cartan tensor. -/
@[simp]
theorem baseChangeEquiv_symm_cartan (y : A ⊗[ℤ] Y) :
    (baseChangeEquiv D A).symm (y, 0) = (cartan D).baseChange A y := by
  rw [LinearEquiv.symm_apply_eq, baseChangeEquiv_cartan]

/-- Reconstruction of one root coefficient. -/
@[simp]
theorem baseChangeEquiv_symm_single (r : A) (a : B.normTwoShell) :
    (baseChangeEquiv D A).symm (0, Finsupp.single a r) = r ⊗ₜ[ℤ] root D a := by
  rw [LinearEquiv.symm_apply_eq, baseChangeEquiv_tmul_root]

/-- Reconstruction of arbitrary Cartan and root coordinates. -/
theorem baseChangeEquiv_symm_apply (y : A ⊗[ℤ] Y) (f : B.normTwoShell →₀ A) :
    (baseChangeEquiv D A).symm (y, f) =
      (cartan D).baseChange A y + f.sum (fun a r => r ⊗ₜ[ℤ] root D a) := by
  classical
  apply (baseChangeEquiv D A).injective
  simp only [LinearEquiv.apply_symm_apply, map_add, baseChangeEquiv_cartan, map_finsuppSum,
    baseChangeEquiv_tmul_root]
  apply Prod.ext
  · simp [Finsupp.sum, Prod.fst_sum]
  · simpa only [Finsupp.sum, Prod.snd_add, Prod.snd_sum, Prod.snd_zero, zero_add] using
      (Finsupp.sum_single f).symm

/-- The scalar-extended root weight, evaluated on the full Cartan tensor module. -/
def baseChangeWeight (a : I → ℤ) : A ⊗[ℤ] Y →ₗ[A] A :=
  Module.Dual.baseChange A (D.weight a)

/-- Evaluation of a root weight on a pure Cartan tensor. -/
@[simp]
theorem baseChangeWeight_tmul (a : I → ℤ) (r : A) (y : Y) :
    baseChangeWeight D A a (r ⊗ₜ[ℤ] y) = (D.weight a y : A) * r := by
  simpa only [baseChangeWeight, zsmul_eq_mul] using
    Module.Dual.baseChange_apply_tmul A (D.weight a) r y

variable [LinearOrder I] [hB : Fact B.PosDef] [hdiag : Fact (∀ i, Even (B i i))]

/-- The integral full-Cartan bracket is a Lie bracket under the Gram hypotheses. -/
local instance : LieRing (FullShellLieAlgebra D) := lieRing D hB.out hdiag.out

/-- Arbitrary scalar-extended Cartan vectors commute. -/
@[simp]
theorem baseChange_cartan_lie_cartan (y z : A ⊗[ℤ] Y) :
    ⁅(cartan D).baseChange A y, (cartan D).baseChange A z⁆ = 0 := by
  induction y using TensorProduct.inductionOn with
  | tmul r y =>
    induction z using TensorProduct.inductionOn with
    | tmul s z => simp
    | add z w hz hw => rw [map_add, LieRing.lie_add, hz, hw, add_zero]
  | add y w hy hw => rw [map_add, LieRing.add_lie, hy, hw, add_zero]

/-- The Cartan/root bracket evaluates the extended weight on an arbitrary Cartan tensor. -/
@[simp]
theorem baseChange_cartan_lie_root (y : A ⊗[ℤ] Y) (r : A) (a : B.normTwoShell) :
    ⁅(cartan D).baseChange A y, r ⊗ₜ[ℤ] root D a⁆ =
      (baseChangeWeight D A a y * r) ⊗ₜ[ℤ] root D a := by
  induction y using TensorProduct.inductionOn with
  | tmul s y =>
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul', mul_assoc, mul_left_comm]
  | add y z hy hz => simp [hy, hz, add_mul, TensorProduct.add_tmul]

/-- The root/Cartan bracket is the negative of the weight action. -/
@[simp]
theorem baseChange_root_lie_cartan (r : A) (a : B.normTwoShell) (y : A ⊗[ℤ] Y) :
    ⁅r ⊗ₜ[ℤ] root D a, (cartan D).baseChange A y⁆ =
      -((baseChangeWeight D A a y * r) ⊗ₜ[ℤ] root D a) := by
  rw [← lie_skew, baseChange_cartan_lie_root]

/-- The bracket in Cartan/root coordinates. Root/root terms use the integral signed root
bracket, so opposite roots land in the full Cartan module via their coroots. -/
theorem baseChangeEquiv_symm_lie_symm (y z : A ⊗[ℤ] Y)
    (f g : B.normTwoShell →₀ A) :
    ⁅(baseChangeEquiv D A).symm (y, f), (baseChangeEquiv D A).symm (z, g)⁆ =
      g.sum (fun a r => (baseChangeWeight D A a y * r) ⊗ₜ[ℤ] root D a) -
      f.sum (fun a r => (baseChangeWeight D A a z * r) ⊗ₜ[ℤ] root D a) +
      f.sum (fun a r => g.sum (fun b s => (r * s) ⊗ₜ[ℤ] rootBracket D a b)) := by
  classical
  have hcross : (∑ b ∈ g.support, ∑ a ∈ f.support, (f a * g b) ⊗ₜ[ℤ] rootBracket D a b) =
      ∑ a ∈ f.support, ∑ b ∈ g.support, (f a * g b) ⊗ₜ[ℤ] rootBracket D a b :=
    Finset.sum_comm
  rw [baseChangeEquiv_symm_apply, baseChangeEquiv_symm_apply]
  simp only [LieRing.lie_add, LieRing.add_lie, baseChange_cartan_lie_cartan, zero_add,
    Finsupp.sum, _root_.lie_sum (L := A ⊗[ℤ] FullShellLieAlgebra D)
      (M := A ⊗[ℤ] FullShellLieAlgebra D), _root_.sum_lie,
    baseChange_cartan_lie_root, baseChange_root_lie_cartan,
    LieAlgebra.ExtendScalars.bracket_tmul, root_lie_root, Finset.sum_neg_distrib,
    sub_eq_add_neg, Finset.sum_add_distrib, hcross]
  -- The root/Cartan contribution precedes the Cartan/root contribution in bilinear expansion.
  ac_rfl

end

end Matrix.FullShellLieAlgebra
