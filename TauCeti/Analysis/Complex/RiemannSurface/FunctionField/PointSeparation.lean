/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch
public import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Generator
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
import TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Separation

/-!
# Point separation and the degree of the meromorphic function field

Let `X` be a compact connected Riemann surface with `H¹(X, 𝒪)` finite-dimensional, of dimension
the analytic genus `g`. For a point `x`, Riemann–Roch gives the divisor `(g + 1) · x` at least two
independent global sections, so `𝒪((g + 1) · x)` contains a non-constant meromorphic function.
Such a function is holomorphic away from `x`, and a meromorphic function without poles on a
compact connected surface is constant, so its only pole is `x`
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_forall_apply_eq_infty_iff`). In particular
meromorphic functions separate the points of `X`
(`TauCeti.RiemannSurface.MeromorphicFunction.exists_apply_ne_apply_of_ne`).

Point separation is the hypothesis of the degree theorem for `M(X) / ℂ(t)` in
`TauCeti.Analysis.Complex.RiemannSurface.FunctionField.Generator`. Discharging it, for a finite
holomorphic map `β : X → ℙ¹` and the `ℂ(t)`-algebra structure on `M(X)` given by pullback along
`β`:

* `M(X)` is generated over `ℂ(t)` by a single meromorphic function
  (`TauCeti.RiemannSurface.MeromorphicFunction.exists_adjoin_simple_eq_top`);
* `[M(X) : ℂ(t)] = deg β`
  (`TauCeti.RiemannSurface.MeromorphicFunction.finrank_ratFunc_eq_degree`).

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, §16
  (Theorem 16.9 and Corollary 16.10, a meromorphic function with a single pole of bounded order
  from Riemann–Roch).
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, Theorem 1.90 (meromorphic functions separate points) and Corollary 1.93 (the
  equality `[M(S) : ℂ(f)] = deg f`).
-/

public section

open OnePoint TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface.MeromorphicFunction

open TauCeti.AlgebraicGeometry (WeilDivisor)

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
  [FiniteDimensional ℂ ((cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
    (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)]

/-- **A meromorphic function with a single pole.** On a compact connected Riemann surface with
finite-dimensional `H¹(X, 𝒪)`, every point `x` is the only pole of some meromorphic function. -/
theorem exists_forall_apply_eq_infty_iff (x : X) :
    ∃ f : MeromorphicFunction X, ∀ y, f y = ∞ ↔ y = x := by
  let D : WeilDivisor X := (analyticGenus X + 1) • WeilDivisor.ofPoint x
  have hdeg : WeilDivisor.degree D = analyticGenus X + 1 := by
    simp [D, map_nsmul, WeilDivisor.degree_ofPoint]
  have hdim := degree_add_one_sub_analyticGenus_le_finrank_divisorSheaf D
  rw [(divisorSheafSectionsEquiv D ⊤).finrank_eq, hdeg] at hdim
  obtain ⟨s, hs⟩ := divisorSections.exists_toMeromorphic_notMem_range_algebraMap D (by omega)
  -- away from `x` the divisor `D` allows no pole
  have hne (y : X) (hy : y ≠ x) : divisorSections.toMeromorphic D s y ≠ ∞ := by
    -- `toMeromorphic_apply_of_nonpos` reads the divisor by `Finsupp` application, not `coeff`
    have h0 := WeilDivisor.coeff_ofPoint_of_ne hy
    unfold WeilDivisor.coeff at h0
    simp [D, h0]
  -- a meromorphic function without poles is constant, so `x` is a pole
  have hx : divisorSections.toMeromorphic D s x = ∞ := by
    by_contra hx
    refine hs (exists_algebraMap_eq_of_forall_ne_infty fun y ↦ ?_)
    rcases eq_or_ne y x with rfl | hy
    · exact hx
    · exact hne y hy
  exact ⟨_, fun y ↦ ⟨fun hy ↦ by_contra fun h ↦ hne y h hy, fun hyx ↦ hyx ▸ hx⟩⟩

/-- **Meromorphic functions separate points.** On a compact connected Riemann surface with
finite-dimensional `H¹(X, 𝒪)`, two distinct points take different values under some meromorphic
function. -/
theorem exists_apply_ne_apply_of_ne {x y : X} (hxy : x ≠ y) :
    ∃ f : MeromorphicFunction X, f x ≠ f y := by
  obtain ⟨f, hf⟩ := exists_forall_apply_eq_infty_iff x
  exact ⟨f, fun h ↦ hxy ((hf y).1 (h ▸ (hf x).2 rfl)).symm⟩

variable (β : FiniteHolomorphicMap X (OnePoint ℂ))
  [Algebra (RatFunc ℂ) (MeromorphicFunction X)]
  (h : algebraMap (RatFunc ℂ) (MeromorphicFunction X) =
    ((comapₐ β β.holomorphic β.nonconstant).comp ratFuncEquiv.toAlgHom).toRingHom)

include h

/-- **The meromorphic function field is a simple extension of `ℂ(t)`.** For the `ℂ(t)`-algebra
structure on `M(X)` given by pullback along a finite holomorphic map `β : X → ℙ¹`, some
meromorphic function generates `M(X)` over `ℂ(t)`. -/
theorem exists_adjoin_simple_eq_top :
    ∃ f : MeromorphicFunction X, IntermediateField.adjoin (RatFunc ℂ) {f} = ⊤ := by
  obtain ⟨y₀, hy₀⟩ := β.finite_branchValues.infinite_compl.nonempty
  obtain ⟨f, hf, hinj⟩ := exists_forall_ne_infty_and_injOn (β.finite_fiber y₀)
    fun _ _ _ _ hxy ↦ exists_apply_ne_apply_of_ne hxy
  exact ⟨f, adjoin_simple_eq_top_of_injOn_fiber β h f hy₀ hf hinj⟩

/-- **The degree theorem.** For the `ℂ(t)`-algebra structure on `M(X)` given by pullback along a
finite holomorphic map `β : X → ℙ¹`, the degree of the meromorphic function field over `ℂ(t)` is
the degree of `β`. -/
theorem finrank_ratFunc_eq_degree :
    Module.finrank (RatFunc ℂ) (MeromorphicFunction X) = degree β := by
  obtain ⟨y₀, hy₀⟩ := β.finite_branchValues.infinite_compl.nonempty
  exact finrank_ratFunc_eq_degree_of_pairwise_separated_fiber β h hy₀
    fun _ _ _ _ hxy ↦ exists_apply_ne_apply_of_ne hxy

end TauCeti.RiemannSurface.MeromorphicFunction
