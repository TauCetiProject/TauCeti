/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Etale
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tensor
public import Mathlib.RingTheory.Etale.Descent
import TauCeti.Algebra.Lie.Submodule.Finrank

/-!
# Étale kernels, homomorphisms, and injective differentials

The scheme-theoretic kernel of a morphism of affine groups of finite type over a field is
étale exactly when the differential at the identity is injective. In particular this detects
whether the kernel of an isogeny has infinitesimal structure. Neither the source nor the target
is assumed smooth, and the ground field need not be perfect.

A faithfully flat affine group homomorphism over any commutative base ring is étale
exactly when its scheme-theoretic kernel is étale. Thus, over a field, a faithfully flat
homomorphism with finite-type source is étale exactly when its differential is injective.

The Lie algebra of the kernel is identified with the kernel of the differential by
`CommHopfAlgCat.kernelLieEquiv`. The zero-Lie-algebra criterion for étaleness then applies.
The morphism criterion uses `CommHopfAlgCat.kernelPairTensorEquiv` and Mathlib's
`Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat` to descend étaleness from the
source base change of the homomorphism.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

section CommRing

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- The scheme-theoretic kernel of an étale affine group homomorphism is étale
over the base. The ambient groups need not themselves be étale or smooth. -/
theorem algebraEtale_quotient_kernelHopfIdeal {f : H ⟶ K}
    (hf : f.hom.toAlgHom.toRingHom.Etale) :
    Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  let := f.hom.toAlgHom.toAlgebra
  let := (Bialgebra.counitAlgHom R H).toAlgebra
  have : Algebra.Etale H K := hf
  have : Algebra.Etale R (K ⊗[H] R) :=
    Algebra.Etale.of_equiv ((Algebra.TensorProduct.comm H R K).restrictScalars R)
  exact Algebra.Etale.of_equiv
    ((quotientKernelHopfIdealAlgEquiv f).restrictScalars R).symm

/-- A faithfully flat affine group homomorphism is étale exactly when its
scheme-theoretic kernel is étale over the base. Neither ambient group is required
to be smooth or of finite type. -/
theorem etale_iff_algebraEtale_quotient_kernelHopfIdeal (f : H ⟶ K)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    f.hom.toAlgHom.toRingHom.Etale ↔
      Algebra.Etale R (K ⧸ (kernelHopfIdeal f).toIdeal) := by
  refine ⟨algebraEtale_quotient_kernelHopfIdeal, fun h ↦ ?_⟩
  let := f.hom.toAlgHom.toAlgebra
  have : Module.FaithfullyFlat H K := hf
  have : Algebra.Etale K (K ⊗[H] K) :=
    Algebra.Etale.of_equiv (kernelPairTensorEquiv f).symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat K

end CommRing

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}

/-- The kernel of an affine group morphism is étale exactly when its differential is injective.
Only the source group scheme, represented by `K`, is required to be of finite type. -/
theorem algebraEtale_quotient_kernelHopfIdeal_iff [Algebra.FiniteType k K] (f : H ⟶ K) :
    Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal) ↔
      Function.Injective (derivationCompLieHom (B := k) f.hom) := by
  rw [HopfAlgebra.algebraEtale_iff_finrank_lie_eq_zero, finrank_kernelLie]
  rw [← finrank_toSubmodule, Submodule.finrank_eq_zero, LieSubmodule.toSubmodule_eq_bot,
    LieHom.ker_eq_bot]

/-- A faithfully flat affine group homomorphism with finite-type source over a field
is étale exactly when its differential at the identity is injective. Smoothness of
the source and target is not assumed. -/
theorem etale_iff_injective_derivationCompLieHom [Algebra.FiniteType k K] (f : H ⟶ K)
    (hf : f.hom.toAlgHom.toRingHom.FaithfullyFlat) :
    f.hom.toAlgHom.toRingHom.Etale ↔
      Function.Injective (derivationCompLieHom (B := k) f.hom) :=
  (etale_iff_algebraEtale_quotient_kernelHopfIdeal f hf).trans
    (algebraEtale_quotient_kernelHopfIdeal_iff f)

end TauCeti.CommHopfAlgCat
