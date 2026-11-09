/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.Geometry.Symplectic.JHolomorphic.OrbitTorus.Zeta

/-!
# The orbit-torus series of the closed orbits of a mapping torus

Let `φ` be a diffeomorphism of a compact manifold `M`, modelled on a finite-dimensional real space,
and let `Y_φ` be its mapping torus. A point `x` of period `d > 0` gives the closed orbit
`[t] ↦ [t, x]` of the suspension flow, traversed once when `d` is the least period of `x`, with
class `[γ_x] ∈ H₁(Y_φ; ℤ)` (`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass`) and time
period `N [γ_x] = d` (`TauCeti.SmoothMappingTorus.timePeriodHom_closedOrbitHomologyClass`). The
positivity of this period is what allows the local multiplicity series `f(t)` of the orbit torus
`S¹ × γ_x` to be substituted at `t = e^[γ_x]` in the Novikov completion `Nov(ℤ, H₁(Y_φ; ℤ), N)`
(`TauCeti.NovikovSeries.ofPowerSeries`).

If `φ` is nondegenerate up to every period, it has only finitely many points with a positive
period at most any bound. Hence for any family of distinct points `x i` of positive periods `d i`
the time periods `N [γ_(x i)] = d i` tend to infinity along the cofinite filter
(`TauCeti.SmoothMappingTorus.tendsto_timePeriodHom_closedOrbitHomologyClass`), which is the
finiteness hypothesis of the product formulas for orbit-torus series
(`TauCeti.hasProd_ofPowerSeries_torusWeightSeries`). For such a family, for instance one point of
least period on each periodic orbit, the product of the substituted orbit-torus series therefore
converges in `Nov(ℤ, H₁(Y_φ; ℤ), N)` to the integral Euler product, and over a `ℚ`-algebra it is
the orbit zeta function
(`TauCeti.SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod`).

The return maps enter through `2 × 2` matrices `P i` of determinant one, from which the labels of
the orbit tori are read off as in
`TauCeti.ofPowerSeries_torusWeightSeries_eq_zpow_unitsOneSubSingle`.
That these are the labels of the actual twisted normal operators of the orbit tori is a separate
determinant comparison.

## Main results

* `TauCeti.SmoothMappingTorus.tendsto_timePeriodHom_closedOrbitHomologyClass`: for distinct
  periodic points of a strongly nondegenerate diffeomorphism of a compact manifold, the time
  periods of their closed orbits tend to infinity.
* `TauCeti.SmoothMappingTorus.hasProd_ofPowerSeries_torusWeightSeries_closedOrbitHomologyClass`:
  the product of the orbit-torus series of the closed orbits converges to the integral Euler
  product in `Nov(ℤ, H₁(Y_φ; ℤ), N)`.
* `TauCeti.SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod`: that
  product is the orbit zeta function.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*,
  J. Differential Geom. 44 (1996), 818--893.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory, Reidemeister torsion, and
  Seiberg–Witten invariants of 3-manifolds*, Topology 38 (1999), 861--888.
-/

public section

open Filter Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

open NovikovSeries

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  (hφ : ∀ N, IsNondegenerateUpToPeriod I φ N) {ι : Type*} {x : ι → M} (hx : Injective x)
  {d : ι → ℕ} (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)

include hφ hx hd in
/-- **Finitely many closed orbits below each period.** For a diffeomorphism of a compact manifold
which is nondegenerate up to every period, the time periods `N [γ_(x i)] = d i` of the closed
orbits through distinct points `x i` of positive periods `d i` tend to infinity along the cofinite
filter. -/
theorem tendsto_timePeriodHom_closedOrbitHomologyClass :
    Tendsto (fun i ↦ timePeriodHom φ (closedOrbitHomologyClass (hxd i))) cofinite atTop := by
  simp only [timePeriodHom_closedOrbitHomologyClass]
  refine tendsto_natCast_atTop_atTop.comp (tendsto_atTop.2 fun N ↦ eventually_cofinite.2 ?_)
  -- The points with a positive period at most `N` form a finite set.
  exact (((hφ N).finite_setOf_isPeriodicPt φ.continuous).preimage hx.injOn).subset
    fun i hi ↦ ⟨d i, hd i, (not_le.1 hi).le, hxd i⟩

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {P : ι → Matrix (Fin 2) (Fin 2) R} (hdet : ∀ i, (P i).det = 1)

include hφ hx hd hdet in
/-- **The orbit-torus series of the closed orbits converge to an integral Euler product.** Let `φ`
be a diffeomorphism of a compact manifold, nondegenerate up to every period, and let `x i` be
distinct points of positive periods `d i`, with nondegenerate matrices `P i` of determinant one
standing for their return maps. The
product over `i` of the labelled local series of the orbit tori, substituted at
`t = e^[γ_(x i)]`, converges in `Nov(ℤ, H₁(Y_φ; ℤ), N)` to the Euler product
`∏ᵢ (1 - σ' i e^[γ_(x i)]) ^ (-(ε i σ' i))`, with `ε i = sgn det (1 - P i)` and `σ' i = -1` if
`det (1 + P i) < 0`, `σ' i = 1` otherwise. -/
theorem hasProd_ofPowerSeries_torusWeightSeries_closedOrbitHomologyClass
    (hP : ∀ i, (1 - P i).det ≠ 0) :
    HasProd (fun i ↦ ofPowerSeries (closedOrbitHomologyClass (hxd i))
        (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
        (torusWeightSeries (decide (0 < (1 - P i).det)) (if (1 + P i).det < 0 then 1 else 0)))
      (eulerProduct (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
        (fun i ↦ if (1 + P i).det < 0 then -1 else 1)
        (fun i ↦ -(SignType.sign (1 - P i).det * if (1 + P i).det < 0 then -1 else 1))) :=
  TauCeti.hasProd_ofPowerSeries_torusWeightSeries _
    (tendsto_timePeriodHom_closedOrbitHomologyClass hφ hx hxd hd) hdet hP

include hφ hx hd hdet in
/-- **The orbit-torus series of the closed orbits give the orbit zeta function.** Under the
hypotheses of
`TauCeti.SmoothMappingTorus.hasProd_ofPowerSeries_torusWeightSeries_closedOrbitHomologyClass`,
with every nonzero power of each `P i` nondegenerate, the product of the substituted orbit-torus
series is, over any `ℚ`-algebra `K`, the orbit zeta function
`exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - P i ^ n) e^(n [γ_(x i)]) / n)` in `Nov(K, H₁(Y_φ; ℤ), N)`. -/
theorem orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod
    (hP : ∀ i, ∀ k ≠ 0, (1 - P i ^ k).det ≠ 0) (K : Type*) [CommRing K] [Algebra ℚ K] :
    orbitZeta K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (1 - P i ^ n).det) =
      mapRingHom (Int.castRingHom K) (AddMonoidHom.id _) ⟨1, one_pos, by simp⟩
        (∏' i, ofPowerSeries (closedOrbitHomologyClass (hxd i))
          (timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
          (torusWeightSeries (decide (0 < (1 - P i).det))
            (if (1 + P i).det < 0 then 1 else 0))) :=
  TauCeti.orbitZeta_eq_mapRingHom_tprod_ofPowerSeries_torusWeightSeries _
    (tendsto_timePeriodHom_closedOrbitHomologyClass hφ hx hxd hd) hdet hP K

end TauCeti.SmoothMappingTorus
