/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# Injectivity in semilinear Galois descent

Over a finite Galois extension `L/k`, an injective `k`-linear map into the invariant vectors
of a semilinear representation stays injective after extending scalars to `L`. Together with
the spanning theorem for invariant vectors, this identifies a semilinear representation with
the scalar extension of its invariants. The result applies to infinite-dimensional vector
spaces and does not require the Galois group order to be invertible.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L V W : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
variable [AddCommGroup W] [Module k W]
variable [FiniteDimensional k L] [IsGalois k L]

/-- An injective map into invariant vectors of a semilinear Galois representation remains
injective after scalar extension. No dimension restriction is imposed on either module. -/
theorem liftBaseChange_injective_of_invariant
    {ρ : Representation k (L ≃ₐ[k] L) V}
    (hsemi : ∀ (σ : L ≃ₐ[k] L) (a : L) (v : V),
      ρ σ (a • v) = σ a • ρ σ v)
    (f : W →ₗ[k] V) (hf : Function.Injective f)
    (hfix : ∀ (σ : L ≃ₐ[k] L) (w : W), ρ σ (f w) = f w) :
    Function.Injective (f.liftBaseChange L) := by
  classical
  let b := Module.finBasis k L
  -- The trace-dual basis extracts each coefficient of a tensor by an orbit sum.
  have hnorm (a : L) (w : W) :
      ρ.norm (a • f w) = Algebra.trace k L a • f w := by
    simp only [Representation.norm, LinearMap.sum_apply, hsemi, hfix]
    rw [← Finset.sum_smul, ← trace_eq_sum_automorphisms,
      IsScalarTower.algebraMap_smul]
  let p : V →ₗ[k] L ⊗[k] V := ∑ i,
    (TensorProduct.mk k L V (b i)).comp
      (ρ.norm.comp ((LinearMap.lsmul L V (b.traceDual i)).restrictScalars k))
  have hp : p.comp ((f.liftBaseChange L).restrictScalars k) = f.lTensor L := by
    apply TensorProduct.ext'
    intro a w
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, p,
      LinearMap.sum_apply, LinearMap.lsmul_apply, smul_smul, hnorm,
      TensorProduct.mk_apply]
    have hcoeff (i) : Algebra.trace k L (b.traceDual i * a) = b.repr a i := by
      rw [← b.traceDual_traceDual, Module.Basis.traceDual_repr_apply]
      simp [Algebra.traceForm, mul_comm]
    simp only [hcoeff, ← TensorProduct.smul_tmul]
    rw [← TensorProduct.sum_tmul, b.sum_repr]
  intro x y h
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := L) f hf
  have h' := congrArg p h
  simpa only [← hp, LinearMap.comp_apply, LinearMap.restrictScalars_apply] using h'

end TauCeti.GaloisDescent
