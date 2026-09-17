/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Etale
import TauCeti.Algebra.Lie.Submodule.Finrank

/-!
# Étale kernels and injective differentials

The scheme-theoretic kernel of a morphism of affine groups of finite type over a field is
étale exactly when the differential at the identity is injective. In particular this detects
whether the kernel of an isogeny has infinitesimal structure. Neither the source nor the target
is assumed smooth, and the ground field need not be perfect.

The Lie algebra of the kernel is identified with the kernel of the differential by
`CommHopfAlgCat.kernelLieEquiv`. The zero-Lie-algebra criterion for étaleness then applies.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.
-/

public section

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{u} k}

/-- The kernel of an affine group morphism is étale exactly when its differential is injective.
Only the source group scheme, represented by `K`, is required to be of finite type. -/
theorem algebraEtale_quotient_kernelHopfIdeal_iff [Algebra.FiniteType k K] (f : H ⟶ K) :
    Algebra.Etale k (K ⧸ (kernelHopfIdeal f).toIdeal) ↔
      Function.Injective (derivationCompLieHom (B := k) f.hom) := by
  rw [HopfAlgebra.algebraEtale_iff_finrank_lie_eq_zero, finrank_kernelLie]
  rw [← finrank_toSubmodule, Submodule.finrank_eq_zero, LieSubmodule.toSubmodule_eq_bot,
    LieHom.ker_eq_bot]

end TauCeti.CommHopfAlgCat
