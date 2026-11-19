/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic

/-!
# The orbit zeta function of a mapping torus as a sum over fixed points

Let `φ` be a diffeomorphism of a compact manifold `M`, modelled on a finite-dimensional real space,
nondegenerate up to every period, and let `Y_φ` be its mapping torus. A point `y` with
`φ^[n] y = y`, `n > 0`, gives a closed orbit of the suspension flow of time period `n`, with class
`[γ_(y, n)] ∈ H₁(Y_φ; ℤ)` (`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass`), and a
Lefschetz sign `sgn det (1 - d(φ^[n])_y)`. The *fixed-point form* of the zeta function of `φ` is
the exponential of

`∑_{n ≥ 1} (1 / n) ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) e^[γ_(y, n)]`

in the Novikov completion `Nov(K, H₁(Y_φ; ℤ), N)` along the time period homomorphism `N`, over a
`ℚ`-algebra `K`. Recording only the time period `N [γ_(y, n)] = n` would turn it into
`exp (∑_{n ≥ 1} (∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)) tⁿ / n)`, whose inner sums the
Lefschetz fixed-point formula identifies with the Lefschetz numbers `L(φⁿ)`; this is how the
fixed-point form compares the orbit zeta function with the homological zeta function. Neither
that specialization nor the Lefschetz formula is proved here.

This file proves that the fixed-point form is the orbit zeta function
(`TauCeti.NovikovSeries.orbitZeta`) of the periodic orbits of `φ`, labelled by the return maps:
for points `x i`, one on each periodic orbit, of least periods `d i`,

`∑_{n, y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)]
  = ∑ᵢ ∑_{k ≥ 1} sgn det (1 - d(φ^[d i * k])_(x i)) / k · e^(k [γ_(x i)])`

(`TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`). Indeed the pairs `(n, y)` are
the pairs `(d i * k, φ^[j] (x i))` with `k ≥ 1` and `j < d i`, each exactly once. The class of the
closed orbit of `φ^[j] (x i)` of period `d i * k` is `k [γ_(x i)]`
(`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_const_mul`,
`TauCeti.SmoothMappingTorus.closedOrbitHomologyClass_apply_iterate`), its Lefschetz sign is that of
`x i` (`TauCeti.det_id_sub_fixedPointDerivative_apply_iterate`), and the `d i` points of the orbit
together contribute `d i / (d i * k) = 1 / k`
(`TauCeti.NovikovSeries.hasSum_orbitLog_sigma_fin`). Exponentiating,

`orbitZeta = exp (∑_{n, y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)])`

(`TauCeti.SmoothMappingTorus.orbitZeta_eq_exp_tsum_single_sign_det_div`). The orbit zeta function
is in turn the product of the local multiplicity series of the orbit tori in `S¹ × Y_φ` when `M` is
a surface and `φ` is area-preserving
(`SmoothMappingTorus.orbitZeta_closedOrbitHomologyClass_eq_mapRingHom_tprod_fixedPointDerivative`),
so this identifies that product with a sum over fixed points.

## Main results

* `TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`: the terms of the fixed points of
  the iterates of `φ` sum to the orbit logarithm of its periodic orbits.
* `TauCeti.SmoothMappingTorus.orbitZeta_eq_exp_tsum_single_sign_det_div`: the orbit zeta function
  is the exponential of that sum.

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
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}
  (hφ : ∀ N, IsNondegenerateUpToPeriod I φ N) {ι : Type*} {x : ι → M} {d : ι → ℕ}
  (hxd : ∀ i, IsPeriodicPt φ (d i) (x i)) (hd : ∀ i, 0 < d i)
  (hmin : ∀ i, minimalPeriod φ (x i) = d i)
  (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
  (K : Type*) [CommRing K] [Algebra ℚ K]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] in
include hxd hd hmin hrep in
/-- The map `(i, k, j) ↦ (d i * (k + 1), φ^[j] (x i))`, `j < d i`, from the iterates of the orbits
of the `x i` with a point of the orbit to the pairs `(n, y)` with `n > 0` and `φ^[n] y = y`, is a
bijection, when every periodic point lies on the orbit of exactly one `x i` and `d i` is the least
period of `x i`. -/
private theorem bijective_periodicPair :
    Bijective fun q : (p : ι × ℕ) × Fin (d p.1) ↦
      (⟨(d q.1.1 * (q.1.2 + 1), (⇑φ)^[q.2] (x q.1.1)), Nat.mul_pos (hd q.1.1) q.1.2.succ_pos,
        ((hxd q.1.1).mul_const _).apply_iterate _⟩ :
        {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2}) := by
  have hper (i : ι) : x i ∈ periodicPts φ := mk_mem_periodicPts (hd i) (hxd i)
  constructor
  · rintro ⟨⟨i, k⟩, j⟩ ⟨⟨i', k'⟩, j'⟩ h
    simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨hn, hy⟩ := h
    -- The common point lies on the orbits of `x i` and of `x i'`, so `i = i'`.
    have hii : i = i' := (hrep _ (mk_mem_periodicPts (hd i) ((hxd i).apply_iterate j))).unique
      ⟨j, rfl⟩ ⟨j', hy.symm⟩
    subst hii
    have hkk : k = k' := by
      have := Nat.eq_of_mul_eq_mul_left (hd i) hn
      omega
    subst hkk
    -- Distinct iterates below the least period give distinct points.
    have hj : (j : ℕ) < minimalPeriod φ (x i) := by rw [hmin]; exact j.2
    have hj' : (j' : ℕ) < minimalPeriod φ (x i) := by rw [hmin]; exact j'.2
    have hjj : (j : ℕ) = j' := iterate_injOn_Iio_minimalPeriod hj hj' hy
    rw [Fin.ext hjj]
  · rintro ⟨⟨n, y⟩, hn, hy⟩
    obtain ⟨i, ⟨j, hj⟩, -⟩ := hrep y (mk_mem_periodicPts hn hy)
    -- The least period of `y` is `d i`, which divides `n`.
    have hmy : minimalPeriod φ y = d i := by rw [← hj, minimalPeriod_apply_iterate (hper i), hmin]
    obtain ⟨m, rfl⟩ : d i ∣ n := hmy ▸ hy.minimalPeriod_dvd
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    refine ⟨⟨(i, m - 1), ⟨j % d i, Nat.mod_lt _ (hd i)⟩⟩, ?_⟩
    simp only [Subtype.mk.injEq, Prod.mk.injEq]
    refine ⟨by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm)], ?_⟩
    rw [← hj, ← hmin i, iterate_mod_minimalPeriod_eq]

include hφ hxd hd hmin hrep in
/-- **The fixed points of the iterates sum to the orbit logarithm.** Let `φ` be a diffeomorphism
of a compact manifold, nondegenerate up to every period, and let `x i` be points of least periods
`d i > 0` such that every periodic point of `φ` lies on the orbit of exactly one `x i`. Then over
any `ℚ`-algebra `K`, the terms `sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)]`, one for each `n > 0`
and each fixed point `y` of `φ^[n]`, sum in `Nov(K, H₁(Y_φ; ℤ), N)` to the orbit logarithm
`∑ᵢ ∑_{k ≥ 1} sgn det (1 - d(φ^[d i * k])_(x i)) / k · e^(k [γ_(x i)])` of the periodic orbits,
labelled by their return maps. -/
theorem hasSum_single_sign_det_div_orbitLog :
    HasSum (fun q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2} ↦
      (single (closedOrbitHomologyClass q.2.2) (algebraMap ℚ K
        ((SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[q.1.1] ⟨q.1.2, q.2.2.eq⟩)) : ℤ) / q.1.1)) :
        NovikovSeries K _ (timePeriodHom φ)))
      (orbitLog K (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩)))) := by
  have hx : Injective x := fun i i' h ↦
    (hrep _ (mk_mem_periodicPts (hd i) (hxd i))).unique ⟨0, rfl⟩ ⟨0, h.symm⟩
  have key := hasSum_orbitLog_sigma_fin (K := K)
    (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos (hxd i) (hd i))
    (tendsto_timePeriodHom_closedOrbitHomologyClass hφ hx hxd hd)
    (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
      fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩)))
    (fun i ↦ (hd i).ne')
  rw [← (Equiv.ofBijective _ (bijective_periodicPair hxd hd hmin hrep)).hasSum_iff]
  convert key using 2 with q
  obtain ⟨⟨i, k⟩, j⟩ := q
  -- The closed orbit through `φ^[j] (x i)` of period `d i * (k + 1)` has class
  -- `(k + 1) • [γ_(x i)]` and the Lefschetz sign of `x i`. Both are stated for an arbitrary
  -- period `n` and point `y` equal to these, as the pair `(n, y)` is the image of `(i, k, j)`.
  have hclass : ∀ (n : ℕ), n = (k + 1) * d i → ∀ (h : IsPeriodicPt φ n ((⇑φ)^[j] (x i))),
      closedOrbitHomologyClass h = (k + 1) • closedOrbitHomologyClass (hxd i) := by
    rintro _ rfl h
    rw [← closedOrbitHomologyClass_const_mul (hxd i) (k + 1),
      ← closedOrbitHomologyClass_apply_iterate ((hxd i).const_mul (k + 1)) j]
  have hcoeff : ∀ (n : ℕ) (y : M), n = d i * (k + 1) → y = (⇑φ)^[j] (x i) →
      ∀ (h : IsPeriodicPt φ n y),
      algebraMap ℚ K ((SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[n] ⟨y, h.eq⟩)) : ℤ) / n) =
        algebraMap ℚ K ((SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[d i * (k + 1)]
            ⟨x i, ((hxd i).mul_const (k + 1)).eq⟩)) : ℤ) / (d i * (k + 1) : ℕ)) := by
    rintro _ _ rfl rfl h
    rw [det_id_sub_fixedPointDerivative_apply_iterate ((hxd i).mul_const (k + 1))
      (φ.contMDiff.mdifferentiable (by simp)) j]
  dsimp only [Function.comp_apply]
  congr 1
  · exact hclass _ (Nat.mul_comm _ _) _
  · exact hcoeff _ _ rfl rfl (((hxd i).mul_const (k + 1)).apply_iterate j)

include hφ hxd hd hmin hrep in
/-- **The orbit zeta function as a sum over fixed points.** Under the hypotheses of
`TauCeti.SmoothMappingTorus.hasSum_single_sign_det_div_orbitLog`, the orbit zeta function of the
periodic orbits of `φ`, labelled by their return maps, is
`exp (∑_{n > 0} ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(y, n)])`. -/
theorem orbitZeta_eq_exp_tsum_single_sign_det_div :
    orbitZeta K (timePeriodHom φ) (fun i ↦ closedOrbitHomologyClass (hxd i))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[d i * n] ⟨x i, ((hxd i).mul_const n).eq⟩))) =
      NormedSpace.exp (∑' q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2},
        (single (closedOrbitHomologyClass q.2.2) (algebraMap ℚ K
          ((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[q.1.1] ⟨q.1.2, q.2.2.eq⟩)) : ℤ) / q.1.1)) :
          NovikovSeries K _ (timePeriodHom φ))) := by
  rw [orbitZeta_def, (hasSum_single_sign_det_div_orbitLog hφ hxd hd hmin hrep K).tsum_eq]

end TauCeti.SmoothMappingTorus
