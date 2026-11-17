/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Degree
public import TauCeti.FieldTheory.IntermediateField.Adjoin.PrimitiveElement
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Separation

/-!
# A separating function generates the meromorphic function field

Let `β : X → OnePoint ℂ` be a finite holomorphic map from a compact connected Riemann surface.
A meromorphic function taking distinct finite values on an unbranched fibre generates `M(X)`
over `ℂ(t)`, where the algebra structure is pullback along `β`. Its minimal-polynomial degree
is `degree β`, and no element of `M(X)` has larger degree. The primitive element theorem in
each two-generated subextension therefore shows that adjoining any further element adds
nothing.

Consequently, pairwise separation of the points of one unbranched fibre suffices for the
field-degree identity `[M(X) : ℂ(t)] = degree β`. The point-separation hypothesis is explicit:
this file does not establish the existence of pairwise separators on arbitrary compact surfaces.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §8,
  Corollary 8.3, for the polynomial equation of degree `deg β` satisfied by each meromorphic
  function (the upper bound).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, Corollary 1.93, for the equality `[M(X) : ℂ(t)] = degree β`.
-/

public section

open OnePoint
open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [ConnectedSpace X] [T2Space X]
  (β : FiniteHolomorphicMap X (OnePoint ℂ))
  [Algebra (RatFunc ℂ) (MeromorphicFunction X)]
  (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
    ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom)

include h

/-- A meromorphic function taking distinct finite values on an unbranched fibre generates the
meromorphic function field over the rational functions pulled back along `β`. -/
theorem adjoin_simple_eq_top_of_injOn_fiber (f : MeromorphicFunction X)
    {y₀ : OnePoint ℂ} (hy₀ : y₀ ∉ β.branchValues)
    (hf : ∀ x ∈ β ⁻¹' {y₀}, f x ≠ ∞) (hinj : (β ⁻¹' {y₀}).InjOn f) :
    IntermediateField.adjoin (RatFunc ℂ) {f} = ⊤ := by
  let : Algebra.IsAlgebraic (RatFunc ℂ) (MeromorphicFunction X) :=
    ⟨fun g => (isIntegral_ratFunc β g h).isAlgebraic⟩
  apply (Field.adjoin_simple_eq_top_iff_forall_natDegree_minpoly_le f).mpr
  intro g
  rw [natDegree_minpoly_ratFunc_eq_degree β f h hy₀ hf hinj]
  exact natDegree_minpoly_ratFunc_le β g h

/-- If the points of one unbranched fibre are pairwise separated by meromorphic functions,
the degree of the meromorphic function field over the pulled-back rational functions equals
the degree of the holomorphic map. -/
theorem finrank_ratFunc_eq_degree_of_pairwise_separated_fiber
    {y₀ : OnePoint ℂ} (hy₀ : y₀ ∉ β.branchValues)
    (hsep : (β ⁻¹' {y₀}).Pairwise fun x x' =>
      ∃ g : MeromorphicFunction X, g x ≠ g x') :
    Module.finrank (RatFunc ℂ) (MeromorphicFunction X) = degree β := by
  obtain ⟨f, hf, hinj⟩ := exists_forall_ne_infty_and_injOn (β.finite_fiber y₀) hsep
  have hgen := adjoin_simple_eq_top_of_injOn_fiber β h f hy₀ hf hinj
  have hfin := IntermediateField.adjoin.finiteDimensional (isIntegral_ratFunc β f h)
  rw [hgen] at hfin
  let : FiniteDimensional (RatFunc ℂ) (MeromorphicFunction X) :=
    IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  rw [← (Field.primitive_element_iff_minpoly_natDegree_eq (RatFunc ℂ) f).mp hgen]
  exact natDegree_minpoly_ratFunc_eq_degree β f h hy₀ hf hinj

end TauCeti.RiemannSurface.MeromorphicFunction
