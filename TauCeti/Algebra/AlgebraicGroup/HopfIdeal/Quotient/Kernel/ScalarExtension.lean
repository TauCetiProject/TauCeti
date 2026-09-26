/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Basic

/-!
# Scalar extension of scheme-theoretic kernels

The kernel Hopf ideal of a scalar-extended coordinate morphism is the scalar extension of
its kernel Hopf ideal. This identifies the defining equations of the scheme-theoretic kernel
after extension of the base ring, including its infinitesimal structure.
-/

public section

open CategoryTheory TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v w

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable {H K : _root_.CommHopfAlgCat.{v} R}

/-- Formation of the kernel Hopf ideal commutes with extension of the base ring. -/
@[simp]
theorem baseChangeHopfIdeal_kernelHopfIdeal (f : H ⟶ K) :
    baseChangeHopfIdeal (K := S) (kernelHopfIdeal f) =
      kernelHopfIdeal (baseChangeMap (K := S) f) := by
  have hmap : ((Algebra.TensorProduct.includeRight : K →ₐ[R] S ⊗[R] K) :
      K →+* S ⊗[R] K).comp (f.hom : H →+* K) =
      ((baseChangeMap (K := S) f).hom :
        S ⊗[R] H →+* S ⊗[R] K).comp
          (Algebra.TensorProduct.includeRight : H →ₐ[R] S ⊗[R] H) := by
    ext x
    exact (baseChangeMap_apply_tmul f 1 x).symm
  ext y
  rw [← HopfIdeal.mem_toIdeal, ← HopfIdeal.mem_toIdeal,
    baseChangeHopfIdeal_toIdeal, kernelHopfIdeal_toIdeal,
    kernelHopfIdeal_toIdeal, ← baseChangeHopfIdeal_augmentation,
    baseChangeHopfIdeal_toIdeal]
  rw [← Ideal.map_coe (f := (Algebra.TensorProduct.includeRight : K →ₐ[R] S ⊗[R] K)),
    ← Ideal.map_coe (f := (Algebra.TensorProduct.includeRight : H →ₐ[R] S ⊗[R] H)),
    Ideal.map_map, Ideal.map_map, hmap]

end TauCeti.CommHopfAlgCat
