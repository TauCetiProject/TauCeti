/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tensor
public import Mathlib.RingTheory.Finiteness.Descent

/-!
# Finiteness of affine group morphisms detected on the kernel

A faithfully flat homomorphism of affine group schemes is finite, of finite type, or of
finite presentation exactly when its scheme-theoretic kernel has the corresponding property
over the base. No finite-type hypothesis on either ambient group is required, and the base
may be any commutative ring.

The forward implications use the kernel as the fibre over the identity. For the converses,
`kernelPairTensorEquiv` identifies the self-base-change of the morphism with the projection
from the source times the kernel, and Mathlib's faithfully flat descent applies.

In particular, finite presentation of the kernel upgrades an fpqc group homomorphism to an
fppf homomorphism, so the fppf first isomorphism theorem applies. The finite criterion detects
isogenies among faithfully flat homomorphisms.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
* J. S. Milne, *Algebraic Groups* (2017), §5.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- A faithfully flat affine group morphism is finite exactly when its scheme-theoretic
kernel is finite over the base. -/
theorem finite_iff_moduleFinite_quotient_kernelHopfIdeal (f : H ⟶ K)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    f.hom.toAlgHom.Finite ↔ Module.Finite R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  refine ⟨moduleFinite_quotient_kernelHopfIdeal, fun h ↦ ?_⟩
  let := f.hom.toAlgHom.toAlgebra
  have : Module.FaithfullyFlat H K := hf
  have : Module.Finite K (K ⊗[H] K) :=
    Module.Finite.equiv (kernelPairTensorEquiv f).symm.toLinearEquiv
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K

/-- The kernel of a finite-type affine group morphism is of finite type over the base. -/
theorem finiteType_quotient_kernelHopfIdeal {f : H ⟶ K}
    (hf : f.hom.toAlgHom.FiniteType) :
    Algebra.FiniteType R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let := f.hom.toAlgHom.toAlgebra
  let := (Bialgebra.counitAlgHom R H).toAlgebra
  have : Algebra.FiniteType H K := hf
  have : Algebra.FiniteType R (K ⊗[H] R) :=
    Algebra.FiniteType.equiv (inferInstanceAs (Algebra.FiniteType R (R ⊗[H] K)))
      ((Algebra.TensorProduct.comm H R K).restrictScalars R)
  exact Algebra.FiniteType.equiv inferInstance
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).symm

/-- A faithfully flat affine group morphism is of finite type exactly when its
scheme-theoretic kernel is of finite type over the base. -/
theorem finiteType_iff_finiteType_quotient_kernelHopfIdeal (f : H ⟶ K)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    f.hom.toAlgHom.FiniteType ↔ Algebra.FiniteType R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  refine ⟨finiteType_quotient_kernelHopfIdeal, fun h ↦ ?_⟩
  let := f.hom.toAlgHom.toAlgebra
  have : Module.FaithfullyFlat H K := hf
  have : Algebra.FiniteType K (K ⊗[H] K) :=
    Algebra.FiniteType.equiv inferInstance (kernelPairTensorEquiv f).symm
  exact Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat K

/-- The kernel of a finitely presented affine group morphism is finitely presented over
the base. -/
theorem finitePresentation_quotient_kernelHopfIdeal {f : H ⟶ K}
    (hf : f.hom.toAlgHom.toRingHom.FinitePresentation) :
    Algebra.FinitePresentation R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let := f.hom.toAlgHom.toAlgebra
  let := (Bialgebra.counitAlgHom R H).toAlgebra
  have : Algebra.FinitePresentation H K := hf
  have : Algebra.FinitePresentation R (K ⊗[H] R) :=
    Algebra.FinitePresentation.equiv ((Algebra.TensorProduct.comm H R K).restrictScalars R)
  exact Algebra.FinitePresentation.equiv
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).symm

/-- A faithfully flat affine group morphism is finitely presented exactly when its
scheme-theoretic kernel is finitely presented over the base. Thus finite presentation of
the kernel suffices for the morphism to be an fppf cover. -/
theorem finitePresentation_iff_finitePresentation_quotient_kernelHopfIdeal (f : H ⟶ K)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    f.hom.toAlgHom.toRingHom.FinitePresentation ↔
      Algebra.FinitePresentation R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  refine ⟨finitePresentation_quotient_kernelHopfIdeal, fun h ↦ ?_⟩
  let := f.hom.toAlgHom.toAlgebra
  have : Module.FaithfullyFlat H K := hf
  have : Algebra.FinitePresentation K (K ⊗[H] K) :=
    Algebra.FinitePresentation.equiv (kernelPairTensorEquiv f).symm
  exact Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat K

end TauCeti.CommHopfAlgCat
