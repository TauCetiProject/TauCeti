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

namespace TauCeti.Comodule

open WithConv TensorProduct

variable {R C M N : Type*} [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable [AddCommMonoid N] [Module R N] [Comodule R C N]

/-- Contracting a coaction against the counit is the identity. -/
@[simp]
theorem coactComponent_counit :
    coactComponent (M := M) (Coalgebra.counit (R := R) (A := C)) = LinearMap.id := by
  have h : LinearMap.tensorComponent (M := M) (Coalgebra.counit (R := R) (A := C)) =
      (TensorProduct.rid R M).toLinearMap ∘ₗ Coalgebra.counit.lTensor M := by
    ext m c
    simp
  ext m
  rw [coactComponent_apply, h, LinearMap.comp_apply, lTensor_counit_coact]
  simp

/-- The convolution algebra of the dual coalgebra acts by contraction of the coaction. -/
noncomputable def convolutionAction : WithConv (C →ₗ[R] R) →ₐ[R] Module.End R M where
  toFun f := coactComponent f.ofConv
  map_zero' := by ext m; simp [coactComponent_apply]
  map_add' f g := by
    ext m
    simp only [coactComponent_apply, ofConv_add, LinearMap.add_apply]
    induction coact (R := R) (C := C) m using TensorProduct.inductionOn with
    | add x y hx hy => simp_all only [map_add]; ac_rfl
    | tmul m c => simp [add_smul]
  map_one' := by
    ext m
    have h : (1 : WithConv (C →ₗ[R] R)).ofConv = Coalgebra.counit := by
      ext c
      simp
    rw [h, coactComponent_counit]
    rfl
  map_mul' f g := by
    ext m
    rw [Module.End.mul_apply, coactComponent_coactComponent, coactComponent_apply]
    have h : pairCoeff f.ofConv g.ofConv ∘ₗ Coalgebra.comul = (f * g).ofConv := by
      rw [LinearMap.convMul_def]
      have hp : pairCoeff f.ofConv g.ofConv =
          LinearMap.mul' R R ∘ₗ TensorProduct.map f.ofConv g.ofConv := by
        ext c d
        simp
      rw [hp, LinearMap.comp_assoc]
    exact (LinearMap.congr_fun
      (tensorPairComponent_comp_lTensor_comul (M := M) h) (coact m)).symm
  commutes' r := by
    ext m
    rw [coactComponent_apply]
    have h : LinearMap.tensorComponent (M := M)
        (algebraMap R (WithConv (C →ₗ[R] R)) r).ofConv =
        r • LinearMap.tensorComponent (M := M) (Coalgebra.counit (R := R)) := by
      ext m c
      simp [smul_smul]
    rw [h, LinearMap.smul_apply]
    rw [← coactComponent_apply, coactComponent_counit]
    rfl

@[simp]
theorem convolutionAction_apply (f : WithConv (C →ₗ[R] R)) (m : M) :
    convolutionAction (R := R) (C := C) (M := M) f m =
      LinearMap.tensorComponent f.ofConv (coact (R := R) (C := C) m) :=
  coactComponent_apply f.ofConv m

/-- Comodule morphisms intertwine the convolution actions. -/
theorem Hom.map_convolutionAction (f : Hom R C M N) (g : WithConv (C →ₗ[R] R)) (m : M) :
    f (convolutionAction (R := R) (C := C) (M := M) g m) =
      convolutionAction (R := R) (C := C) (M := N) g (f m) := by
  rw [convolutionAction_apply, convolutionAction_apply, ← f.map_coact_apply]
  simpa using (LinearMap.tensorComponent_map g.ofConv f.toLinearMap LinearMap.id
    (coact (R := R) (C := C) m)).symm

end TauCeti.Comodule
