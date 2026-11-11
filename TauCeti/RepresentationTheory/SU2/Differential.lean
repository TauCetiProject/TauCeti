/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Differential.Analytic
public import TauCeti.RepresentationTheory.SU2.HolomorphicExtension
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# The differential of the holomorphic symmetric-power extension

The holomorphic `GL₂(ℂ)` extension of the continuous `SU(2)` symmetric-power model has the same
differential as the algebraic symmetric-power representation in the model's weight basis.

## Main results

* `TauCeti.SU2.mvfderiv_symPowerHolomorphicExtension_one`: the analytic derivative of the actual
  operator-valued extension agrees with its algebraic differential.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  §3.5, Theorem 3.28: the differential of a Lie-group homomorphism at the identity.
* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter III, §8, Propositions (8.6)–(8.7), pp.154–155: holomorphic extensions and the
  classical complexifications.
-/

public section

open Matrix Manifold
open scoped ContDiff Manifold Matrix.Norms.Operator
attribute [local instance] Matrix.linftyOpTopologicalSpace
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SU2

variable (d : ℕ)

local notation "V" => EuclideanSpace ℂ (Fin (d + 1))

/-- The derivative at the identity of the holomorphic operator action is the algebraic
symmetric-power differential in the same weight basis. -/
theorem mvfderiv_symPowerHolomorphicExtension_one
    (X : TangentSpace 𝓘(ℂ, Matrix (Fin 2) (Fin 2) ℂ) (1 : GL (Fin 2) ℂ)) :
    mvfderiv 𝓘(ℂ, Matrix (Fin 2) (Fin 2) ℂ)
        (fun g : GL (Fin 2) ℂ => (symPowerHolomorphicExtension d g : V →L[ℂ] V)) 1 X =
      Module.End.toContinuousLinearMap V
        ((isPolynomialRep_symPowerModelGL d).isRationalRep.differential X) := by
  have he : (fun g : GL (Fin 2) ℂ => (symPowerHolomorphicExtension d g : V →L[ℂ] V)) =
      (fun g : GL (Fin 2) ℂ => Module.End.toContinuousLinearMap V (symPowerModelGL d g)) := by
    funext g
    ext w
    simp only [symPowerHolomorphicExtension_apply, Module.End.toContinuousLinearMap_apply,
      symPowerModelGL_apply]
  rw [he]
  exact (isPolynomialRep_symPowerModelGL d).isRationalRep.mvfderiv_toContinuousLinearMap_one X

end TauCeti.SU2
