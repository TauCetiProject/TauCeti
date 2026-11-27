/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic
import TauCeti.Dynamics.PeriodicPts.PeriodicPair

/-!
# The orbit zeta function of a mapping torus as a sum over fixed points

Let `φ` be a diffeomorphism of a locally compact manifold `M`, modelled on a finite-dimensional
real space, each of whose positive iterates has only finitely many fixed points (for instance a
diffeomorphism of a compact manifold nondegenerate up to every period), and let `Y_φ` be its
mapping torus. A point `y` with
`φ^[n] y = y`, `n > 0`, gives a closed orbit of the suspension flow of time period `n`, with class
`[γ_(y, n)] ∈ H₁(Y_φ; ℤ)` (`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass`), and a sign
`sgn det (1 - d(φ^[n])_y)`: the local Lefschetz index of `y` as a fixed point of `φ^[n]` when `y`
is nondegenerate, and `0` when it is degenerate. The *fixed-point form* of the zeta function of
`φ` is the exponential of

`∑_{n ≥ 1} (1 / n) ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) e^[γ_(y, n)]`

in the Novikov completion `Nov(K, H₁(Y_φ; ℤ), N)` along the time period homomorphism `N`, over a
`ℚ`-algebra `K`. Recording only the time period `N [γ_(y, n)] = n` would turn it into
`exp (∑_{n ≥ 1} (∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)) tⁿ / n)`. When `M` is compact and
`φ` is nondegenerate up to every period, the Lefschetz fixed-point formula identifies these inner
sums with the Lefschetz numbers `L(φⁿ)`; this is how the fixed-point form compares the orbit zeta
function with the homological zeta function
(`TauCeti/Geometry/Manifold/Instances/MappingTorus/ClosedOrbit/Lefschetz.lean`). The Lefschetz
formula itself is not proved here.

This file proves that the fixed-point form is the orbit zeta function
(`TauCeti.NovikovSeries.orbitZeta`) of the periodic orbits of `φ`, labelled by the return maps:
for points `x i`, one on each periodic orbit, of least periods `d i`,

`∑_{n, y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)]
  = ∑ᵢ ∑_{k ≥ 1} sgn det (1 - d(φ^[d i * k])_(x i)) / k · e^(k [γ_(x i)])`

(`TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`). Indeed the pairs `(n, y)` are
the pairs `(d i * k, φ^[j] (x i))` with `k ≥ 1` and `j < d i`, each exactly once
(`Function.periodicPairEquiv`). The class of the closed orbit of `φ^[j] (x i)` of period `d i * k`
is `k [γ_(x i)]`
(`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_const_mul`,
`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_apply_iterate`), its sign is that of
`x i` (`TauCeti.det_id_sub_fixedPointDerivative_apply_iterate`), and the `d i` points of the orbit
together contribute `d i / (d i * k) = 1 / k`
(`TauCeti.NovikovSeries.hasSum_orbitLog_sigma_fin`). Exponentiating,

`orbitZeta = exp (∑_{n, y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)])`

(`TauCeti.SmoothMappingTorus.orbitZeta_eq_exp_tsum_single_sign_det_div`). The orbit zeta function
is in turn the product of the local multiplicity series of the orbit tori in `S¹ × Y_φ` when `M` is
a surface and `φ` is area-preserving
(`SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod_fixedPointDerivative`),
so this identifies that product with a sum over fixed points.

**The univariate specialization.** The integral time period `N : H₁(Y_φ; ℤ) → ℤ`
(`TauCeti.SmoothMappingTorus.intTimePeriodHom`) pushes the orbit zeta function forward to a
Novikov series on `ℤ`, a Laurent series in `t = e^1`, forgetting the classes of the orbits and
keeping their periods. It is the power series

`exp (∑_{n ≥ 1} (∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)) tⁿ / n)`,

Mathlib's formal exponential `PowerSeries.exp` substituted, evaluated at `t`
(`TauCeti.SmoothMappingTorus.mapRingHom_intTimePeriodHom_orbitZeta`). Indeed the pushforward of
the fixed-point sum has coefficient `(1 / n) ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)` at `tⁿ`,
the fixed points of `φ^[n]` being the pairs `(n, y)` of period `n`, and the pushforward and the
evaluation at `t` both commute with the exponential (`TauCeti.NovikovSeries.mapRingHom_exp`,
`TauCeti.NovikovSeries.ofPowerSeries_subst_exp`).

## Main results

* `TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`: the terms of the fixed points of
  the iterates of `φ` sum to the orbit logarithm of its periodic orbits.
* `TauCeti.SmoothMappingTorus.orbitZeta_eq_exp_tsum_single_sign_det_div`: the orbit zeta function
  is the exponential of that sum.
* `TauCeti.SmoothMappingTorus.mapRingHom_intTimePeriodHom_orbitZeta`: its specialization along the
  time period is `exp (∑_{n ≥ 1} (∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)) tⁿ / n)`.

## References

* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999), Section 2.
* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
-/

public section

noncomputable section

open Filter Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

open NovikovSeries

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  (hfin : ∀ n, 0 < n → (ptsOfPeriod φ n).Finite) {ι : Type*} {x : ι → M} {d : ι → ℕ}
  (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)
  (hmin : ∀ i, minimalPeriod φ (x i) = d i)
  (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
  (K : Type*) [CommRing K] [Algebra ℚ K]

include hfin hxd hd hmin hrep in
/-- **The fixed points of the iterates sum to the orbit logarithm.** Let `φ` be a diffeomorphism
each of whose positive iterates has finitely many fixed points, and let `x i` be points of least
periods `d i > 0` such that every periodic point of `φ` lies on the orbit of exactly one `x i`.
Then over any `ℚ`-algebra `K`, the terms `sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)]`, one for
each `n > 0` and each fixed point `y` of `φ^[n]`, sum in `Nov(K, H₁(Y_φ; ℤ), N)` to the orbit
logarithm
`∑ᵢ ∑_{k ≥ 1} sgn det (1 - d(φ^[d i * k])_(x i)) / k · e^(k [γ_(x i)])` of the periodic orbits,
labelled by their return maps. -/
theorem hasSum_single_sign_det_div_orbitLog :
    HasSum (fun q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2} ↦
      (single (closedOrbitHomologyClass q.property.2) (algebraMap ℚ K
        ((SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[q.val.1] ⟨q.val.2, q.property.2.eq⟩)) : ℤ) / q.val.1)) :
        NovikovSeries K _ (timePeriodHom φ)))
      (orbitLog K (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩)))) := by
  have hx : Injective x :=
    injective_of_existsUnique_iterate (fun i ↦ mk_mem_periodicPts (hd i) (hxd i)) hrep
  have key := hasSum_orbitLog_sigma_fin (K := K)
    (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
    (tendsto_timePeriodHom_closedOrbitHomologyClass hfin hx hxd hd)
    (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
      fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩)))
    (fun i ↦ (hd i).ne')
  rw [← (periodicPairEquiv hmin hd hrep).hasSum_iff]
  convert key using 2 with q
  obtain ⟨⟨i, k⟩, j⟩ := q
  -- The pair `(n, y)` is `(d i * (k + 1), φ^[j] (x i))`. The closed orbit through `y` of period
  -- `n` has class `(k + 1) • [γ_(x i)]` and the sign of `x i`.
  have hq := coe_periodicPairEquiv_apply hmin hd hrep ⟨(i, k), j⟩
  have hn := congrArg Prod.fst hq
  have hy := congrArg Prod.snd hq
  dsimp only [Function.comp_apply]
  congr 1
  · simp only [hn, hy, Nat.mul_comm (d i)]
    rw [closedOrbitHomologyClass_apply_iterate ((hxd i).const_mul (k + 1)) j,
      closedOrbitHomologyClass_const_mul]
  · rw [det_id_sub_fixedPointDerivative_congr _ (((hxd i).mul_const (k + 1)).apply_iterate j).eq
      (congrArg _ hn) hy, det_id_sub_fixedPointDerivative_apply_iterate
      ((hxd i).mul_const (k + 1)) (fun _ ↦ φ.contMDiff.mdifferentiable (by simp) _) j, hn]

include hfin hxd hd hmin hrep in
/-- **The orbit zeta function as a sum over fixed points.** Under the hypotheses of
`TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`, the orbit zeta function of the
periodic orbits of `φ`, labelled by their return maps, is
`exp (∑_{n > 0} ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)])`. -/
theorem orbitZeta_eq_exp_tsum_single_sign_det_div :
    orbitZeta K (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩))) =
      NormedSpace.exp (∑' q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2},
        (single (closedOrbitHomologyClass q.property.2) (algebraMap ℚ K
          ((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[q.val.1] ⟨q.val.2, q.property.2.eq⟩)) : ℤ) / q.val.1)) :
          NovikovSeries K _ (timePeriodHom φ))) := by
  rw [orbitZeta_def, (hasSum_single_sign_det_div_orbitLog hfin hxd hd hmin hrep K).tsum_eq]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] in
include hfin in
/-- The terms of the fixed-point sum of the iterates of `φ`, specialized to their time periods,
have coefficient `(1 / n) ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)` at the period `n`. -/
private theorem finsum_coeff_single_natCast (n : ℕ) :
    ∑ᶠ q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2},
        (single (q.val.1 : ℤ) (algebraMap ℚ K
          ((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[q.val.1] ⟨q.val.2, q.property.2.eq⟩)) : ℤ) / q.val.1)) :
          NovikovSeries K ℤ (Int.castAddHom ℝ)).coeff n =
      (n : ℚ)⁻¹ • ((∑ᶠ y : {y : M // (⇑φ)^[n] y = y}, (SignType.sign (LinearMap.det
          (LinearMap.id - fixedPointDerivative I (⇑φ)^[n] y)) : ℤ) : ℤ) : K) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- No closed orbit has period `0`.
    simp only [CharP.cast_eq_zero, inv_zero, zero_smul]
    exact finsum_eq_zero_of_forall_eq_zero fun q ↦
      coeff_single_of_ne (by exact_mod_cast q.property.1.ne) _
  -- The fixed points `y` of `φ^[n]` are the pairs `(n, y)` contributing to the coefficient of `n`.
  let e : {y : M // (⇑φ)^[n] y = y} → {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2} :=
    fun y ↦ ⟨(n, y), hn, y.property⟩
  have he : Injective e := fun y y' h ↦ Subtype.ext (congrArg (fun q ↦ q.val.2) h)
  have hsupp : (Function.support fun q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2} ↦
      (single (q.val.1 : ℤ) (algebraMap ℚ K
        ((SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[q.val.1] ⟨q.val.2, q.property.2.eq⟩)) : ℤ) / q.val.1)) :
        NovikovSeries K ℤ (Int.castAddHom ℝ)).coeff n) ⊆ Set.range e := by
    intro q hq
    by_cases hqn : (q.val.1 : ℤ) = n
    · exact ⟨⟨q.val.2, (Nat.cast_injective hqn) ▸ q.property.2⟩,
        Subtype.ext (Prod.ext (Nat.cast_injective hqn).symm rfl)⟩
    · exact absurd (coeff_single_of_ne (Ne.symm hqn) _) hq
  have : Finite {y : M // (⇑φ)^[n] y = y} := (hfin n hn).to_subtype
  have := Fintype.ofFinite {y : M // (⇑φ)^[n] y = y}
  rw [← Set.indicator_eq_self.2 hsupp, ← finsum_mem_def, finsum_mem_range he,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [e, coeff_single_same, Int.cast_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun y _ ↦ by
    rw [div_eq_inv_mul, _root_.map_mul, map_intCast, Algebra.smul_def]

include hfin hxd hd hmin hrep in
/-- **The univariate orbit zeta function.** Under the hypotheses of
`TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`, the pushforward of the orbit
zeta function of the periodic orbits of `φ` along the integral time period `N : H₁(Y_φ; ℤ) → ℤ`
is the image at `t = e^1` of the power series
`exp (∑_{n ≥ 1} (∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)) tⁿ / n)`, the formal exponential
substituted. -/
theorem mapRingHom_intTimePeriodHom_orbitZeta :
    mapRingHom (RingHom.id K) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ)
        (orbitZeta K (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
          (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩)))) =
      ofPowerSeries (1 : ℤ) (by simp) ((PowerSeries.exp K).subst (PowerSeries.mk fun n ↦
        (n : ℚ)⁻¹ • ((∑ᶠ y : {y : M // (⇑φ)^[n] y = y}, (SignType.sign (LinearMap.det
          (LinearMap.id - fixedPointDerivative I (⇑φ)^[n] y)) : ℤ) : ℤ) : K))) := by
  have hpos i := timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i)
  rw [orbitZeta_def, ofPowerSeries_subst_exp _ ?hc]
  case hc => simp only [PowerSeries.constantCoeff_mk, Nat.cast_zero, inv_zero, zero_smul]
  rw [mapRingHom_exp _ _ _ (orbitLog_mem_posIdeal hpos _)]
  congr 1
  -- Compare coefficients, pushing the fixed-point sum forward along the time period.
  have hs := (hasSum_single_sign_det_div_orbitLog hfin hxd hd hmin hrep K).map
    (mapRingHom (RingHom.id K) (intTimePeriodHom φ) (exists_period_rescale_intTimePeriodHom φ))
    (continuous_mapRingHom _ _ _)
  ext h
  rw [coeff_eq_finsum_of_hasSum hs h]
  simp only [Function.comp_apply, mapRingHom_apply, map_single,
    intTimePeriodHom_closedOrbitHomologyClass, AddMonoidHom.coe_ofClass, RingHom.id_apply]
  rcases lt_or_ge h 0 with hneg | hnn
  · -- No closed orbit has negative period.
    rw [coeff_ofPowerSeries_of_forall_nsmul_ne _ fun n hn ↦ by simp at hn; omega]
    exact finsum_eq_zero_of_forall_eq_zero fun q ↦ coeff_single_of_ne (by omega) _
  · lift h to ℕ using hnn with n
    rw [finsum_coeff_single_natCast hfin, show (n : ℤ) = n • (1 : ℤ) by simp,
      coeff_ofPowerSeries_nsmul, PowerSeries.coeff_mk]

end TauCeti.SmoothMappingTorus
