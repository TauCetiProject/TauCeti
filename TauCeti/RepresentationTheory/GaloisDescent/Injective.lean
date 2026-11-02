/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Trace.Basic

/-!
# Injectivity in semilinear Galois descent

Let `G` be a finite Galois group for a field extension `L/k` (`IsGaloisGroup G k L`), for
instance `Gal(L/k)` itself when `L/k` is finite Galois. An injective `k`-linear map into the
invariant vectors of a semilinear representation of `G` stays injective after extending scalars
to `L`. Together with the spanning theorem for invariant vectors, this identifies a semilinear
representation with the scalar extension of its invariants. The result applies to
infinite-dimensional vector spaces and does not require the order of `G` to be invertible.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64 (Galois descent).
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k G L V W : Type*} [Field k] [Group G] [Field L] [Algebra k L]
variable [MulSemiringAction G L] [IsGaloisGroup G k L] [Finite G]
variable [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]
variable [AddCommGroup W] [Module k W]

/-- An injective map into invariant vectors of a semilinear representation of a finite Galois
group `G` of `L/k` remains injective after scalar extension. Semilinearity is only required on
scalar multiples of the image of the map. No dimension restriction is imposed on either
module. -/
theorem liftBaseChange_injective_of_invariant
    {ρ : Representation k G V}
    {f : W →ₗ[k] V} (hf : Function.Injective f)
    (hsemi : ∀ (g : G) (a : L) (w : W), ρ g (a • f w) = (g • a) • f w) :
    Function.Injective (f.liftBaseChange L) := by
  classical
  have := IsGaloisGroup.finiteDimensional G k L
  have := IsGaloisGroup.isGalois G k L
  let := Fintype.ofFinite G
  let b := Module.finBasis k L
  -- The trace-dual basis extracts each coefficient of a tensor by an orbit sum.
  have hnorm (a : L) (w : W) :
      ρ.norm (a • f w) = Algebra.trace k L a • f w := by
    simp only [Representation.norm, LinearMap.sum_apply, hsemi]
    rw [← Finset.sum_smul, ← IsScalarTower.algebraMap_smul L (Algebra.trace k L a),
      trace_eq_sum_automorphisms]
    congr 1
    exact Fintype.sum_equiv (IsGaloisGroup.mulEquivAlgEquiv G k L).toEquiv _ _ fun _ ↦ rfl
  let p : V →ₗ[k] L ⊗[k] V := ∑ i,
    (TensorProduct.mk k L V (b i)).comp
      (ρ.norm.comp ((LinearMap.lsmul L V (b.traceDual i)).restrictScalars k))
  have hp : p.comp ((f.liftBaseChange L).restrictScalars k) = f.lTensor L := by
    refine TensorProduct.ext' fun a w ↦ ?_
    have hcoeff (i) : Algebra.trace k L (b.traceDual i * a) = b.repr a i := by
      rw [← b.traceDual_traceDual, Module.Basis.traceDual_repr_apply]
      simp [Algebra.traceForm, mul_comm]
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.liftBaseChange_tmul, LinearMap.lTensor_tmul, p, LinearMap.sum_apply,
      LinearMap.lsmul_apply, smul_smul, hnorm, hcoeff, TensorProduct.mk_apply,
      ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
  refine Function.Injective.of_comp (f := p) ?_
  rw [← LinearMap.coe_restrictScalars k (f.liftBaseChange L), ← LinearMap.coe_comp, hp]
  exact Module.Flat.lTensor_preserves_injective_linearMap f hf

end TauCeti.GaloisDescent
