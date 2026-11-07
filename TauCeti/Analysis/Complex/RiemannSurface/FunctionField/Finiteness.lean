/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
public import TauCeti.FieldTheory.IntermediateField.Adjoin.BoundedDegree

/-!
# Finiteness of the meromorphic function-field extension

A finite holomorphic map `β : X → OnePoint ℂ` from a compact connected Riemann surface
makes its meromorphic function field a finite extension of `ℂ(t)`, of degree at most the
degree of `β`.

The polynomial equation from
`TauCeti.RiemannSurface.MeromorphicFunction.natDegree_minpoly_ratFunc_le` bounds the degree
of each element. Characteristic zero supplies separability, so the primitive element theorem
on finite intermediate fields upgrades this to a bound on the whole extension. This does not
assert equality with the degree of `β`: that additionally requires meromorphic functions
separating points in an unbranched fibre.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, §8, Theorems 8.2 and 8.3.
-/

public section

open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]
  (β : FiniteHolomorphicMap X (OnePoint ℂ))
  [Algebra (RatFunc ℂ) (MeromorphicFunction X)]
  (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
    ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom)

include h

/-- Pullback along a finite holomorphic map to the sphere makes the meromorphic function field
of a compact connected Riemann surface finite-dimensional over `ℂ(t)`. -/
theorem finiteDimensional_ratFunc : FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X) := by
  let : Algebra.IsIntegral (RatFunc ℂ) (MeromorphicFunction X) :=
    ⟨fun f ↦ isIntegral_ratFunc β f h⟩
  exact Field.finiteDimensional_of_natDegree_minpoly_le (RatFunc ℂ) (MeromorphicFunction X)
    (degree β) (fun f ↦ natDegree_minpoly_ratFunc_le β f h)

/-- The meromorphic function-field extension induced by `β` has degree at most its analytic
degree. -/
theorem finrank_ratFunc_le_degree :
    Module.finrank (RatFunc ℂ) (MeromorphicFunction X) ≤ degree β := by
  let : Algebra.IsIntegral (RatFunc ℂ) (MeromorphicFunction X) :=
    ⟨fun f ↦ isIntegral_ratFunc β f h⟩
  exact Field.finrank_le_of_natDegree_minpoly_le (RatFunc ℂ) (MeromorphicFunction X)
    (degree β) (fun f ↦ natDegree_minpoly_ratFunc_le β f h)

end TauCeti.RiemannSurface.MeromorphicFunction
