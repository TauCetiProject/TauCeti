/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.FormallySmooth
import TauCeti.Algebra.Lie.Submodule.Finrank

/-!
# Lie dimensions of kernels of formally smooth group morphisms

For a formally smooth affine group morphism `G → H` with finite-dimensional tangent space
at the identity of `G`, the dimensions satisfy `dim Lie(ker f) + dim Lie(H) = dim Lie(G)`.
The groups themselves need not be smooth. Formal smoothness gives the surjectivity of the
differential, and `CommHopfAlgCat.kernelLieEquiv` identifies its kernel.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k}

/-- For a formally smooth affine group morphism, the Lie dimensions of its kernel and target
add to the Lie dimension of its source. Only the source tangent space must be finite-dimensional.
The coordinate morphism `f : H ⟶ K` represents the group morphism `Spec K → Spec H`. -/
theorem finrank_kernelLie_add_finrank_lie_of_formallySmooth
    [Module.Finite k (Derivation k K (Bialgebra.CounitAlgebra k K k))]
    (f : H ⟶ K) (hf : f.hom.toAlgHom.toRingHom.FormallySmooth) :
    Module.finrank k (Derivation k (K ⧸ (kernelHopfIdeal f).toIdeal)
        (Bialgebra.CounitAlgebra k (K ⧸ (kernelHopfIdeal f).toIdeal) k)) +
      Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
        Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)) := by
  let df := (derivationCompLieHom (B := k) f.hom).toLinearMap
  have hdf : Function.Surjective df :=
    derivationCompLieHom_surjective_of_formallySmooth f.hom hf
  have hrank := df.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hdf, finrank_top] at hrank
  rw [finrank_kernelLie, ← finrank_toSubmodule, LieHom.ker_toSubmodule, add_comm]
  exact hrank

end TauCeti.CommHopfAlgCat
