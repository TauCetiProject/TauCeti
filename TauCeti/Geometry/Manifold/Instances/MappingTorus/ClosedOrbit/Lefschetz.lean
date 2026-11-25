/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LefschetzNumber.Surface
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit.Zeta
import TauCeti.RingTheory.PowerSeries.Log

/-!
# The univariate orbit zeta function of a mapping torus and the Lefschetz zeta function

Let `φ` be a diffeomorphism of a locally compact manifold `M` each of whose positive iterates has
finitely many fixed points, with mapping torus `Y_φ`, and let `k` be a field of characteristic
zero. Specialized along the integral time period `N : H₁(Y_φ; ℤ) → ℤ`, the orbit zeta function of
the periodic orbits of `φ` is the image at `t = e^1` of the power series

`exp (∑_{n ≥ 1} a_n tⁿ / n)`,    `a_n = ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)`

(`TauCeti.SmoothMappingTorus.mapRingHom_intTimePeriodHom_orbitZeta`). The homological, or
Lefschetz, zeta function of `φ` is `ζ_φ = exp (∑_{n ≥ 1} L(φⁿ) tⁿ / n)`
(`ContinuousMap.lefschetzZeta`), built from the Lefschetz numbers of the iterates; it is defined
for every continuous map, with no condition on its fixed points.

Since a power series without constant term is determined by its formal exponential
(`PowerSeries.subst_exp_inj`), and in characteristic zero the coefficient `a_n / n` determines
`a_n`, the univariate orbit zeta function is the Lefschetz zeta function exactly when the
Lefschetz fixed-point formula `a_n = L(φⁿ)` holds for every iterate
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff`).
When `M` is a closed connected oriented surface and `φ` has degree one, as an
orientation-preserving diffeomorphism does, the Lefschetz zeta function is the homology determinant
formula `det (1 - t P) / (1 - t)²` with `P = φ_*` on `H₁(M; k)`
(`TauCeti.HomologicalOrientation.lefschetzZeta_eq_reverse_charpoly_mul_inv_of_degree_eq_one`), so
the same condition characterizes the equality of the univariate orbit zeta function with that
rational function
(`TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_reverse_charpoly_mul_inv_iff`).
For a compact `M` and `φ` nondegenerate up to every period the Lefschetz fixed-point theorem gives
the condition; that theorem is not proved here.

## Main results

* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff`:
  the univariate orbit zeta function is the Lefschetz zeta function if and only if the signed
  fixed-point count of every iterate `φⁿ`, `n ≥ 1`, is its Lefschetz number.
* `TauCeti.SmoothMappingTorus.mapRingHom_orbitZeta_eq_ofPowerSeries_reverse_charpoly_mul_inv_iff`:
  for a degree-one diffeomorphism of a closed oriented surface, the univariate orbit zeta function
  is `det (1 - t P) / (1 - t)²` under the same condition.

## References

* S. Smale, *Differentiable dynamical systems*, Bull. Amer. Math. Soc. 73 (1967), 747–817 (the
  Lefschetz zeta function and its determinant formula).
* E.-N. Ionel and T. H. Parker, *The Gromov invariants of Ruan–Tian and Taubes*, Math. Res. Lett.
  4 (1997), 521–532, Lemma 3.1.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
-/

public section

noncomputable section

open Function Module
open scoped Manifold ContDiff PowerSeries

namespace TauCeti.SmoothMappingTorus

open NovikovSeries

section Lefschetz

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  (hfin : ∀ n, 0 < n → (ptsOfPeriod φ n).Finite) {ι : Type*} {x : ι → M} {d : ι → ℕ}
  (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)
  (hmin : ∀ i, minimalPeriod φ (x i) = d i)
  (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
  (k : Type) [Field k] [Algebra ℚ k]

include hfin hxd hd hmin hrep in
/-- **The univariate orbit zeta function and the Lefschetz zeta function.** Under the hypotheses
of `TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`, over a field `k` of
characteristic zero, the pushforward of the orbit zeta function of the periodic orbits of `φ` along
the integral time period is the image at `t = e^1` of the Lefschetz zeta function
`exp (∑_{n ≥ 1} L(φⁿ) tⁿ / n)` of `φ` if and only if, for every `n ≥ 1`, the fixed points of `φ^[n]`
counted with their signs `sgn det (1 - d(φ^[n])_y)` add up to the Lefschetz number `L(φⁿ)`. -/
theorem mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff :
    mapRingHom (RingHom.id k) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ)
        (orbitZeta k (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp) ((⟨φ, φ.continuous⟩ : C(M, M)).lefschetzZeta k) ↔
    ∀ n, 0 < n → ((∑ᶠ y : {y : M // (⇑φ)^[n] y = y}, (SignType.sign (LinearMap.det
        (LinearMap.id - fixedPointDerivative I (⇑φ)^[n] y)) : ℤ) : ℤ) : k) =
      (⟨(⇑φ)^[n], φ.continuous.iterate n⟩ : C(M, M)).lefschetzNumber k := by
  rw [mapRingHom_intTimePeriodHom_orbitZeta hfin hxd hd hmin hrep,
    (ofPowerSeries_injective _).eq_iff, ContinuousMap.lefschetzZeta_def,
    PowerSeries.subst_exp_inj (by simp) (by simp), PowerSeries.ext_iff]
  refine forall_congr' fun n ↦ ?_
  simp only [PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · -- The coefficient `a / n` determines `a`, since `n ≠ 0` in characteristic zero.
    simp only [hn, forall_const]
    exact (smul_right_injective k (inv_ne_zero (Nat.cast_ne_zero.2 hn.ne'))).eq_iff

end Lefschetz

section Surface

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {I : ModelWithCorners ℝ E E} [TopologicalSpace M] [ChartedSpace E M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M] [FiniteCWType M] {φ : M ≃ₘ⟮I, I⟯ M}
  (hfin : ∀ n, 0 < n → (ptsOfPeriod φ n).Finite) {ι : Type*} {x : ι → M} {d : ι → ℕ}
  (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)
  (hmin : ∀ i, minimalPeriod φ (x i) = d i)
  (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
  (o : HomologicalOrientation M E 2) (hE : finrank ℝ E = 2) (k : Type) [Field k] [Algebra ℚ k]

include hfin hxd hd hmin hrep in
/-- **The univariate orbit zeta function and the homology determinant formula.** Let `φ` be a
diffeomorphism of degree one of a closed connected surface `M` with a homological orientation, of
finite CW type, under the hypotheses of
`TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`, and let `k` be a field of
characteristic zero. The pushforward of the orbit zeta function of the periodic orbits of `φ`
along the integral time period is the image at `t = e^1` of `det (1 - t P) / (1 - t)²`, with
`P = φ_*` on `H₁(M; k)`, if and only if, for every `n ≥ 1`, the fixed points of `φ^[n]` counted
with their signs `sgn det (1 - d(φ^[n])_y)` add up to the Lefschetz number `L(φⁿ)`. -/
theorem mapRingHom_orbitZeta_eq_ofPowerSeries_reverse_charpoly_mul_inv_iff
    (hφ : o.degree o hE ⟨φ, φ.continuous⟩ = 1) :
    mapRingHom (RingHom.id k) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ)
        (orbitZeta k (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp)
        (((ContinuousMap.singularHomologyMap k 1 ⟨φ, φ.continuous⟩).charpoly.reverse : k⟦X⟧) *
          ((1 - PowerSeries.X) ^ 2)⁻¹) ↔
    ∀ n, 0 < n → ((∑ᶠ y : {y : M // (⇑φ)^[n] y = y}, (SignType.sign (LinearMap.det
        (LinearMap.id - fixedPointDerivative I (⇑φ)^[n] y)) : ℤ) : ℤ) : k) =
      (⟨(⇑φ)^[n], φ.continuous.iterate n⟩ : C(M, M)).lefschetzNumber k := by
  rw [← o.lefschetzZeta_eq_reverse_charpoly_mul_inv_of_degree_eq_one hE k hφ]
  exact mapRingHom_orbitZeta_eq_ofPowerSeries_lefschetzZeta_iff
    hfin hxd hd hmin hrep k

end Surface

end TauCeti.SmoothMappingTorus
