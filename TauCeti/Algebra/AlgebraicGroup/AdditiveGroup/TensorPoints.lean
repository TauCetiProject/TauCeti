/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Basic
public import Mathlib.LinearAlgebra.Contraction

/-!
# Tensor coordinates for points of a vector group

For a finite projective module `P`, the points of `Spec (Sym P)` over an algebra `A` are
canonically `A ⊗ P*`. The identification preserves the additive group law and is natural
in `A`. The dual here is essential: `Spec (Sym P)` represents linear forms on `P`.

The construction combines `AdditiveGroup.pointsMulEquiv` with Mathlib's finite-projective
tensor–Hom equivalence `dualTensorHomEquiv`.

## References

* A. Grothendieck, *Éléments de géométrie algébrique II*, (1.7.8).
-/

public section

open scoped TensorProduct
open WithConv

namespace TauCeti.AdditiveGroup

variable {R : Type*} [CommSemiring R] (P : Type*) [AddCommMonoid P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]
  (A : Type*) [CommSemiring A] [Algebra R A]

/-- Tensor coordinates for the points of the vector group `Spec (Sym P)`. -/
noncomputable def tensorPointsMulEquiv : Multiplicative (A ⊗[R] Module.Dual R P) ≃*
    WithConv (SymmetricAlgebra R P →ₐ[R] A) :=
  ((TensorProduct.comm R A (Module.Dual R P)).trans
    (dualTensorHomEquiv R P A)).toAddEquiv.toMultiplicative.trans pointsMulEquiv.symm

/-- The point of a tensor evaluates a linear generator by scalar-extended evaluation. -/
theorem tensorPointsMulEquiv_apply_ι (x : A ⊗[R] Module.Dual R P) (p : P) :
    (tensorPointsMulEquiv P A (Multiplicative.ofAdd x)).ofConv (SymmetricAlgebra.ι R P p) =
      dualTensorHom R P A (TensorProduct.comm R A (Module.Dual R P) x) p := by
  simp [tensorPointsMulEquiv, dualTensorHomEquiv]

/-- A pure tensor gives the point sending `p` to `φ(p) • a`. -/
@[simp]
theorem tensorPointsMulEquiv_tmul_apply_ι (a : A) (φ : Module.Dual R P) (p : P) :
    (tensorPointsMulEquiv P A (Multiplicative.ofAdd (a ⊗ₜ[R] φ))).ofConv
        (SymmetricAlgebra.ι R P p) = φ p • a := by
  rw [tensorPointsMulEquiv_apply_ι]
  simp

/-- Tensor coordinates commute with changes of the value algebra. -/
theorem mapValue_tensorPointsMulEquiv {B : Type*} [CommSemiring B] [Algebra R B]
    (φ : A →ₐ[R] B) (x : A ⊗[R] Module.Dual R P) :
    AlgHom.mapValue φ (tensorPointsMulEquiv P A (Multiplicative.ofAdd x)) =
      tensorPointsMulEquiv P B
        (Multiplicative.ofAdd (LinearMap.rTensor (Module.Dual R P) φ.toLinearMap x)) := by
  apply WithConv.ofConv_injective
  apply SymmetricAlgebra.hom_ext
  ext p
  simp only [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, tensorPointsMulEquiv_apply_ι]
  induction x using TensorProduct.inductionOn with
  | tmul a ψ => simp
  | add x y hx hy => simp_all only [map_add, LinearMap.add_apply]

end TauCeti.AdditiveGroup
