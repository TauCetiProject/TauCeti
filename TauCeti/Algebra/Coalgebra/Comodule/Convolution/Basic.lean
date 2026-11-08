/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# The convolution algebra acts on a comodule

Contracting a right coaction against a linear functional gives an endomorphism of the
comodule. Coassociativity makes this an algebra homomorphism from the convolution algebra
of the coalgebra's dual. Comodule morphisms intertwine these actions. Restricting this
homomorphism to counit-valued derivations gives the differentiated action of an affine group.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.
-/

public section

open WithConv TensorProduct

namespace LinearMap

variable {R C : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The unit of the convolution dual is the coalgebra counit. -/
@[simp]
theorem ofConv_one_eq_counit :
    (1 : WithConv (Module.Dual R C)).ofConv = Coalgebra.counit := by
  simp [convOne_def]

/-- Multiplication in the convolution dual is successive contraction of comultiplication. -/
theorem convMul_eq_comp_tensorComponent (f g : WithConv (Module.Dual R C)) :
    (f * g).ofConv = f.ofConv ∘ₗ tensorComponent g.ofConv ∘ₗ Coalgebra.comul := by
  have hp : f.ofConv ∘ₗ tensorComponent g.ofConv =
      LinearMap.mul' R R ∘ₗ TensorProduct.map f.ofConv g.ofConv := by
    ext c d
    simp [mul_comm]
  rw [← comp_assoc, hp, convMul_def, comp_assoc]

/-- Successive contractions of a comultiplication on the right tensor factor are
contraction by the convolution product. -/
theorem tensorComponent_lTensor_comul {M : Type*} [AddCommMonoid M] [Module R M]
    (f g : WithConv (Module.Dual R C)) (x : M ⊗[R] C) :
    tensorComponent f.ofConv
        ((tensorComponent g.ofConv).lTensor M (Coalgebra.comul.lTensor M x)) =
      tensorComponent (f * g).ofConv x := by
  simp [lTensor_def, convMul_eq_comp_tensorComponent, comp_assoc]

end LinearMap

namespace TauCeti.Comodule

variable {R C M N : Type*} [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Contracting a coaction against the counit is the identity. -/
@[simp]
theorem coactComponent_counit :
    coactComponent (M := M) (Coalgebra.counit (R := R) (A := C)) = LinearMap.id := by
  ext m
  rw [coactComponent_apply, LinearMap.tensorComponent_def, LinearMap.comp_apply,
    lTensor_counit_coact]
  simp

/-- The convolution algebra on the linear dual of the coalgebra acts by contraction of
the coaction. -/
noncomputable def convolutionAction : WithConv (C →ₗ[R] R) →ₐ[R] Module.End R M where
  toFun f := coactComponent f.ofConv
  map_zero' := by ext m; simp [coactComponent_apply]
  map_add' f g := by
    ext m
    simp [coactComponent_apply]
  map_one' := by
    ext m
    rw [LinearMap.ofConv_one_eq_counit, coactComponent_counit]
    rfl
  map_mul' f g := by
    ext m
    rw [_root_.mul_apply_eq_comp, coactComponent_coactComponent]
    rw [LinearMap.convMul_eq_comp_tensorComponent]
  commutes' r := by
    ext m
    have h : (algebraMap R (WithConv (C →ₗ[R] R)) r).ofConv =
        r • Coalgebra.counit (R := R) := by
      ext c
      simp
    rw [coactComponent_apply, h, map_smul, LinearMap.smul_apply,
      ← coactComponent_apply, coactComponent_counit]
    rfl

/-- Evaluating the convolution action contracts the coaction against the underlying functional. -/
@[simp]
theorem convolutionAction_apply (f : WithConv (C →ₗ[R] R)) (m : M) :
    convolutionAction (R := R) (C := C) (M := M) f m =
      LinearMap.tensorComponent f.ofConv (coact (R := R) (C := C) m) :=
  coactComponent_apply f.ofConv m

/-- Comodule morphisms intertwine the convolution actions. -/
@[simp↓]
theorem Hom.map_convolutionAction (f : Hom R C M N) (g : WithConv (C →ₗ[R] R)) (m : M) :
    f (convolutionAction (R := R) (C := C) (M := M) g m) =
      convolutionAction (R := R) (C := C) (M := N) g (f m) := by
  rw [convolutionAction_apply, convolutionAction_apply, ← f.map_coact_apply]
  simpa using (LinearMap.tensorComponent_map g.ofConv f.toLinearMap LinearMap.id
    (coact (R := R) (C := C) m)).symm

end TauCeti.Comodule
