/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint

/-!
# Finitely many closed suspension orbits below a period

Let `φ : M ≃ₘ^n⟮I, I⟯ M` be a diffeomorphism of a compact manifold modelled on a
finite-dimensional space, with smooth mapping torus `Y_φ`. Each periodic point `x` of `φ` of
period `d > 0` gives a closed orbit `γ : ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]`, of the suspension flow
(`TauCeti.SmoothMappingTorus.closedOrbit`), and an orbit torus `(s, θ) ↦ (s, γ θ)` in
`(ℝ / ℤ) × Y_φ` (`TauCeti.SmoothMappingTorus.orbitTorus`), whose image is the product of the
circle with the image of `γ`.

If `φ` is nondegenerate up to period `N` (`TauCeti.IsNondegenerateUpToPeriod`), it has only
finitely many periodic points of positive period at most `N`, and the image of a closed orbit is
the flow orbit through `[0, x]`, independent of the chosen period. Hence only finitely many
subsets of `Y_φ` are images of closed orbits of period at most `N`, and only finitely many subsets
of `(ℝ / ℤ) × Y_φ` are images of their orbit tori. Multiple covers of one orbit have the same
image, so these are finite sets of images, not of parametrized orbits.

When `φ` is an area-preserving map of a closed surface and `(ℝ / ℤ) × Y_φ` carries a block
almost complex structure, these images are the embedded pseudoholomorphic tori of bounded period
in the count of Taubes; the finiteness makes each truncation of that count a finite sum.

## Main results

* `TauCeti.IsNondegenerateUpToPeriod.finite_setOf_range_closedOrbit`: finitely many images of
  closed orbits of period at most `N`.
* `TauCeti.IsNondegenerateUpToPeriod.finite_setOf_range_orbitTorus`: finitely many images of
  orbit tori of period at most `N`.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic &
  Geometric Topology 5 (2005), 301–354, Section 2.
-/

public section

open Set Function
open scoped Manifold ContDiff

namespace TauCeti.IsNondegenerateUpToPeriod

open SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [CompactSpace M] [T2Space M] {n : ℕ∞ω} {φ : M ≃ₘ^n⟮I, I⟯ M} {N : ℕ}

/-- **Finitely many closed orbits below a period.** If a diffeomorphism `φ` of a compact manifold
modelled on a finite-dimensional space is nondegenerate up to period `N`, then only finitely many
subsets of the mapping torus `Y_φ` are images of closed orbits of the suspension flow through
periodic points of positive period at most `N`. -/
theorem finite_setOf_range_closedOrbit (h : IsNondegenerateUpToPeriod I φ N) :
    {S : Set (SmoothMappingTorus φ) | ∃ (d : ℕ) (x : M) (hx : IsPeriodicPt φ d x),
      0 < d ∧ d ≤ N ∧ range (closedOrbit φ hx) = S}.Finite := by
  refine ((h.finite_setOf_isPeriodicPt φ.continuous).image
    fun x ↦ (flow φ).orbit (mk φ 0 x)).subset ?_
  rintro S ⟨d, x, hx, hd, hdN, rfl⟩
  exact ⟨x, ⟨d, hd, hdN, hx⟩, (range_closedOrbit hx).symm⟩

/-- **Finitely many orbit tori below a period.** If a diffeomorphism `φ` of a compact manifold
modelled on a finite-dimensional space is nondegenerate up to period `N`, then only finitely many
subsets of `(ℝ / ℤ) × Y_φ` are images of orbit tori through periodic points of positive period at
most `N`. -/
theorem finite_setOf_range_orbitTorus (h : IsNondegenerateUpToPeriod I φ N) :
    {S : Set (UnitAddCircle × SmoothMappingTorus φ) | ∃ (d : ℕ) (x : M)
      (hx : IsPeriodicPt φ d x), 0 < d ∧ d ≤ N ∧ range (orbitTorus φ hx) = S}.Finite := by
  refine (h.finite_setOf_range_closedOrbit.image (univ ×ˢ ·)).subset ?_
  rintro S ⟨d, x, hx, hd, hdN, rfl⟩
  exact ⟨_, ⟨d, x, hx, hd, hdN, rfl⟩, (range_orbitTorus hx).symm⟩

end TauCeti.IsNondegenerateUpToPeriod
