/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.PeriodicPoint

/-!
# The orbit zeta function of a mapping torus as a sum over periodic points

Let `φ` be a diffeomorphism of a compact manifold `M`, nondegenerate up to every period, with
smooth mapping torus `Y_φ` and time period homomorphism `N : H₁(Y_φ; ℤ) → ℝ`
(`TauCeti.SmoothMappingTorus.timePeriodHom`). Choose one point `x i` on each periodic orbit of `φ`,
of least period `d i`. The `n`-fold iterate of the closed suspension orbit through `x i` has class
`n [γ_(x i)]` and Lefschetz sign `sgn det (1 - d(φ^[d i * n])_(x i))`, and the orbit zeta function
of these closed orbits in the Novikov completion `Nov(K, H₁(Y_φ; ℤ), N)` is

`ζ = exp (∑ᵢ ∑_{n ≥ 1} sgn det (1 - d(φ^[d i * n])_(x i)) / n · e^(n [γ_(x i)]))`.

This file rewrites its logarithm as a sum over the periodic points of `φ` with a chosen positive
period (`TauCeti.SmoothMappingTorus.hasSum_orbitLog_closedOrbitHomologyClass_periodicPts`):

`log ζ = ∑_{n > 0} ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)]`,

where `[γ_(y, n)]` is the class of the closed suspension orbit through `y` traversed in time `n`
(`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass`). Every class of period `n` collects the
fixed points of `φ^[n]` with their signs `sgn det (1 - d(φ^[n])_y)`, which at interior points are
the local indices in the Lefschetz fixed-point formula for `φ^[n]`. The orbit expansion of `ζ` is
the exponential of the series of these signed fixed-point counts
(`TauCeti.SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_exp_tsum`).

The comparison rests on two facts about the closed orbits: their classes do not depend on the
starting point in the orbit and are multiplied by `k` when the orbit is traversed `k` times
(`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_apply_iterate`,
`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_const_mul`); and the Lefschetz sign of a
fixed point of `φ^[n]` is the same at all points of its orbit, since `φ` conjugates `φ^[n]` to
itself (`Diffeomorph.det_id_sub_fixedPointDerivative_iterate_apply_iterate`).

## Main results

* `TauCeti.SmoothMappingTorus.hasSum_orbitLog_closedOrbitHomologyClass_periodicPts`: the orbit
  logarithm of the closed suspension orbits as a sum over periodic points of `φ`.
* `TauCeti.SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_exp_tsum`: the orbit zeta
  function as the exponential of that sum.

## References

* M. Artin and B. Mazur, *On periodic points*, Ann. of Math. 81 (1965), 82–99.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999).
-/

public section

open Filter Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

open NovikovSeries

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  (hφ : ∀ N, IsNondegenerateUpToPeriod I φ N) {ι : Type*} {x : ι → M}
  (hx : ∀ i, x i ∈ periodicPts φ) (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
  (K : Type*) [CommRing K] [Algebra ℚ K]

include hφ hx hrep in
/-- **The orbit logarithm of the closed orbits as a sum over periodic points.** Let `φ` be a
diffeomorphism of a compact manifold, nondegenerate up to every period, and let `x i` list one
point on each periodic orbit of `φ`, of least period `d i`. Over a `ℚ`-algebra `K`, the orbit
logarithm `∑ᵢ ∑_{n ≥ 1} sgn det (1 - d(φ^[d i * n])_(x i)) / n · e^(n [γ_(x i)])` of the closed
suspension orbits is the sum, over the points `y` of positive period `n`, of
`sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)]`. -/
theorem hasSum_orbitLog_closedOrbitHomologyClass_periodicPts :
    HasSum (fun p : {p : ℕ × M // 0 < p.1 ∧ IsPeriodicPt φ p.1 p.2} ↦
        (single (closedOrbitHomologyClass p.2.2) (algebraMap ℚ K
          (((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[p.1.1] ⟨p.1.2, p.2.2.eq⟩)) : ℤ) : ℚ) / p.1.1)) :
          NovikovSeries K _ (timePeriodHom φ)))
      (orbitLog K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (isPeriodicPt_minimalPeriod φ (x i)))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[minimalPeriod φ (x i) * n]
            ⟨x i, ((isPeriodicPt_minimalPeriod φ (x i)).mul_const n).eq⟩)))) := by
  have hd (i : ι) : 0 < minimalPeriod φ (x i) := minimalPeriod_pos_of_mem_periodicPts (hx i)
  -- Distinct representatives lie on distinct orbits.
  have hxinj : Injective x := fun i i' h ↦
    (hrep (x i) (hx i)).unique ⟨0, rfl⟩ ⟨0, by rw [iterate_zero_apply, h]⟩
  refine hasSum_orbitLog_periodicPts hx hrep
    (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos _ (hd i))
    (tendsto_timePeriodHom_closedOrbitHomologyClass hφ hxinj
      (fun i ↦ isPeriodicPt_minimalPeriod φ (x i)) hd) _ _ (fun i k j _ ↦ ?_)
    (fun i k j _ ↦ ?_)
  · -- The class of the `(k + 1)`-fold orbit does not depend on the starting point.
    exact (closedOrbitHomologyClass_apply_iterate
      ((isPeriodicPt_minimalPeriod φ (x i)).const_mul (k + 1)) j).trans
        (closedOrbitHomologyClass_const_mul (isPeriodicPt_minimalPeriod φ (x i)) (k + 1))
  · -- Neither does the Lefschetz sign; then reorder the period `(k + 1) d i = d i (k + 1)`.
    have key : ∀ (m m' : ℕ), m = m' → ∀ (p : (⇑φ)^[m] (x i) = x i)
        (p' : (⇑φ)^[m'] (x i) = x i),
        fixedPointDerivative I (⇑φ)^[m] ⟨x i, p⟩ = fixedPointDerivative I (⇑φ)^[m'] ⟨x i, p'⟩ := by
      rintro _ _ rfl _ _
      rfl
    simp only
    rw [φ.det_id_sub_fixedPointDerivative_iterate_apply_iterate (by simp)
      ((isPeriodicPt_minimalPeriod φ (x i)).const_mul (k + 1)) j, key _ _ (mul_comm _ _)]

include hφ hx hrep in
/-- **The orbit zeta function of the closed orbits as an exponential of fixed-point counts.**
Under the hypotheses of
`TauCeti.SmoothMappingTorus.hasSum_orbitLog_closedOrbitHomologyClass_periodicPts`, the orbit zeta
function of the closed suspension orbits is
`exp (∑_{n > 0} ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)])`. -/
theorem orbitZeta_closedOrbitHomologyClass_eq_exp_tsum :
    orbitZeta K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (isPeriodicPt_minimalPeriod φ (x i)))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[minimalPeriod φ (x i) * n]
            ⟨x i, ((isPeriodicPt_minimalPeriod φ (x i)).mul_const n).eq⟩))) =
      NormedSpace.exp (∑' p : {p : ℕ × M // 0 < p.1 ∧ IsPeriodicPt φ p.1 p.2},
        (single (closedOrbitHomologyClass p.2.2) (algebraMap ℚ K
          (((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[p.1.1] ⟨p.1.2, p.2.2.eq⟩)) : ℤ) : ℚ) / p.1.1)) :
          NovikovSeries K _ (timePeriodHom φ))) := by
  rw [orbitZeta_def,
    (hasSum_orbitLog_closedOrbitHomologyClass_periodicPts hφ hx hrep K).tsum_eq]

end TauCeti.SmoothMappingTorus
