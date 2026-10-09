/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tensor
public import Mathlib.RingTheory.Etale.Descent

/-!
# Smooth affine group homomorphisms detected on their kernels

A faithfully flat homomorphism of affine group schemes is smooth exactly when its
scheme-theoretic kernel is smooth over the base. The base may be any commutative ring,
and neither ambient group is required to be smooth or of finite type. This reduces
smoothness of quotient homomorphisms to the geometry of their identity fibres.

The forward implication identifies the kernel with the fibre over the identity using
`CommHopfAlgCat.quotientKernelHopfIdealAlgEquiv`. For the converse,
`CommHopfAlgCat.kernelPairTensorEquiv` identifies the source base change of the
homomorphism with the projection from the source times the kernel. Smoothness of this
projection descends along the faithfully flat coordinate map, using Mathlib's
`Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat`.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
* J. S. Milne, *Algebraic Groups* (2017), §1.e.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- The scheme-theoretic kernel of a smooth affine group homomorphism is smooth over
the base, without any smoothness assumption on the ambient groups. -/
theorem algebraSmooth_quotient_kernelHopfIdeal_of_smooth {f : H ⟶ K}
    (hf : f.hom.toAlgHom.toRingHom.Smooth) :
    Algebra.Smooth R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let := f.hom.toAlgHom.toAlgebra
  let := (Bialgebra.counitAlgHom R H).toAlgebra
  have : Algebra.Smooth H K := hf
  have : Algebra.Smooth R (K ⊗[H] R) :=
    Algebra.Smooth.of_equiv ((Algebra.TensorProduct.comm H R K).restrictScalars R)
  exact Algebra.Smooth.of_equiv
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).symm

/-- A faithfully flat affine group homomorphism is smooth exactly when its
scheme-theoretic kernel is smooth over the base. No finite-presentation hypothesis is
needed: smoothness of the kernel supplies it by faithfully flat descent. -/
theorem smooth_iff_algebraSmooth_quotient_kernelHopfIdeal (f : H ⟶ K)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    f.hom.toAlgHom.toRingHom.Smooth ↔
      Algebra.Smooth R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  refine ⟨algebraSmooth_quotient_kernelHopfIdeal_of_smooth, fun h ↦ ?_⟩
  let := f.hom.toAlgHom.toAlgebra
  have : Module.FaithfullyFlat H K := hf
  have : Algebra.Smooth K (K ⊗[H] K) :=
    Algebra.Smooth.of_equiv (kernelPairTensorEquiv f).symm
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat K

end TauCeti.CommHopfAlgCat
