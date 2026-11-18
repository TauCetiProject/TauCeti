/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.PeriodicPts.Representative
public import TauCeti.Geometry.Manifold.DeRham.MappingTorus
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic

/-!
# The orbit logarithm of a mapping torus as a sum over fixed points

Let `φ` be a diffeomorphism of a finite-dimensional manifold `M`, with smooth mapping torus `Y_φ`
and time period `N(h) = ∫_h dt` on `H₁(Y_φ; ℤ)` (`TauCeti.SmoothMappingTorus.timePeriodHom`). Each
periodic orbit of `φ`, of least period `d` through a point `x`, is a primitive closed orbit of the
suspension flow, of class `[γ_x] ∈ H₁(Y_φ; ℤ)` and time period `d`. Its `n`-fold iterate has the
Lefschetz sign `ε(n) = sgn det (1 - d(φ^[d n])_x)`. The orbit logarithm

`L = ∑_x ∑_{n ≥ 1} ε(n) / n · e^(n [γ_x])`

(`TauCeti.NovikovSeries.orbitLog`), a sum over one point `x` of each periodic orbit, is the
logarithm of the orbit zeta function of `φ` in the Novikov completion `Nov(K, H₁(Y_φ; ℤ), N)`.

This file rewrites `L` as a sum over the fixed points of the iterates of `φ`. A fixed point `y` of
`φ^[n]`, `n > 0`, gives the closed orbit `[t] ↦ [t, y]` of period `n`, of class `[γ_(n, y)]`. If
each positive iterate of `φ` has only finitely many fixed points, then

`L = ∑_{n ≥ 1} 1 / n · ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) · e^[γ_(n, y)]`

(`TauCeti.SmoothMappingTorus.hasSum_single_closedOrbitHomologyClass_orbitLog`), and the orbit zeta
function is the exponential of the right side
(`TauCeti.SmoothMappingTorus.orbitZeta_eq_exp_tsum`). Indeed a periodic orbit of least period `d`
consists of `d` points, each of which is a fixed point of `φ^[d n]` with the class
`[γ_(d n, φ^[j] x)] = n [γ_x]` and the same sign `ε(n)`: the derivatives of `φ^[d n]` at `x` and
at `φ x` are `B A` and `A B` for `A = dφ_x`, so `det (1 - d(φ^[d n]))` is constant along the orbit
(`TauCeti.det_id_sub_fixedPointDerivative_iterate_apply_iterate`). These `d` terms of weight
`1 / (d n)` add up to the term `ε(n) / n · e^(n [γ_x])` of `L`.

On a closed manifold, when all fixed points of `φ^[n]` are nondegenerate, the inner sum
`∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y)` is the signed fixed-point count of `φ^[n]`, so the right
side is the homology-refined form of the series `∑_n L(φⁿ) tⁿ / n` of Lefschetz numbers. Identifying
these counts with the alternating traces of `φ_*` on homology is the Lefschetz fixed-point formula,
which is not proved here.

## Main results

* `TauCeti.SmoothMappingTorus.summable_single_closedOrbitHomologyClass`: if each positive iterate
  has finitely many fixed points, the fixed-point terms are summable.
* `TauCeti.SmoothMappingTorus.hasSum_single_closedOrbitHomologyClass_orbitLog`: the orbit
  logarithm is the sum over the fixed points of the iterates.
* `TauCeti.SmoothMappingTorus.orbitZeta_eq_exp_tsum`: the orbit zeta function is the exponential
  of that sum.

## References

* D. Fried, *Lefschetz formulas for flows*, Contemp. Math. 58, Part III (1987), 19–69.
* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, Section 1.3 and Example 1.9 (the zeta function of a mapping torus).
-/

public section

open Filter Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

open NovikovSeries

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M] {φ : M ≃ₘ⟮I, I⟯ M}

variable (hfin : ∀ n, 0 < n → (ptsOfPeriod φ n).Finite) {ι : Type*} {x : ι → M}
  (hx : ∀ i, x i ∈ periodicPts φ) (hrep : ∀ y ∈ periodicPts φ, ∃! i, ∃ j, (⇑φ)^[j] (x i) = y)
  (K : Type*) [CommRing K] [Algebra ℚ K]

include hfin in
/-- The terms `sgn det (1 - d(φ^[n])_y) / n · e^[γ_(n, y)]` over the fixed points `y` of the
positive iterates `φ^[n]` are summable: only finitely many of them have period `n` below any
cutoff. -/
theorem summable_single_closedOrbitHomologyClass :
    Summable (fun q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2} ↦
      (single (closedOrbitHomologyClass q.2.2) (algebraMap ℚ K
        ((SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[q.1.1] ⟨q.1.2, q.2.2.eq⟩)) : ℤ) / q.1.1)) :
        NovikovSeries K _ (timePeriodHom φ))) := by
  refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    (hasBasis_nhds_zero.tendsto_right_iff.2 fun C _ ↦ eventually_cofinite.2 ?_)
  have hT : {n : ℕ | 0 < n ∧ (n : ℝ) < C}.Finite :=
    (Set.finite_Iio ⌈C⌉₊).subset fun n hn ↦ Nat.lt_ceil.2 hn.2
  -- A term outside `U_C` has period `n < C`, and each such `φ^[n]` has finitely many fixed points.
  refine ((hT.biUnion fun n hn ↦ (Set.finite_singleton n).prod (hfin n hn.1)).preimage
    Subtype.val_injective.injOn).subset fun q hq ↦ Set.mem_biUnion
      (x := q.1.1) ⟨q.2.1, ?_⟩ ⟨Set.mem_singleton _, q.2.2⟩
  by_contra hC
  refine hq (antitone_periodFiltration ?_ (single_mem_periodFiltration _ _))
  simpa using not_lt.1 hC

include hfin hx hrep in
/-- **The orbit logarithm of a mapping torus as a sum over fixed points.** Let `φ` be a
diffeomorphism each of whose positive iterates has finitely many fixed points, and let `x` be a
family of orbit representatives of its periodic points: every periodic point lies on the orbit
of exactly one `x i`. Let `d i` be the least period of `x i`, `[γ_i]` the class of the closed orbit
through `x i` and `ε i n = sgn det (1 - d(φ^[d i * n])_(x i))`. Then, in
`Nov(K, H₁(Y_φ; ℤ), N)`, the terms `sgn det (1 - d(φ^[n])_y) / n · e^[γ_(n, y)]` over the pairs
`(n, y)` with `n > 0` and `φ^[n] y = y` sum to the orbit logarithm
`∑ᵢ ∑_{n ≥ 1} ε i n / n · e^(n [γ_i])`. Here `[γ_(n, y)]` is the class of the closed orbit of
period `n` through `y`. -/
theorem hasSum_single_closedOrbitHomologyClass_orbitLog :
    HasSum (fun q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2} ↦
        (single (closedOrbitHomologyClass q.2.2) (algebraMap ℚ K
          ((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[q.1.1] ⟨q.1.2, q.2.2.eq⟩)) : ℤ) / q.1.1)) :
          NovikovSeries K _ (timePeriodHom φ)))
      (orbitLog K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (isPeriodicPt_minimalPeriod φ (x i)))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[minimalPeriod φ (x i) * n]
            ⟨x i, ((isPeriodicPt_minimalPeriod φ (x i)).mul_const n).eq⟩)))) := by
  set g := fun q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2} ↦
    (single (closedOrbitHomologyClass q.2.2) (algebraMap ℚ K
      ((SignType.sign (LinearMap.det (LinearMap.id -
        fixedPointDerivative I (⇑φ)^[q.1.1] ⟨q.1.2, q.2.2.eq⟩)) : ℤ) / q.1.1)) :
      NovikovSeries K _ (timePeriodHom φ))
  have hd (i : ι) : 0 < minimalPeriod φ (x i) := minimalPeriod_pos_of_mem_periodicPts (hx i)
  have hdiff : MDifferentiable I I φ := φ.contMDiff.mdifferentiable (by simp)
  refine hasSum_of_hasSum_sum_sigmaMinimalPeriodEquiv hx hrep
    (summable_single_closedOrbitHomologyClass hfin K)
    (hasSum_orbitLog (fun i ↦ timePeriodHom_closedOrbitHomologyClass_pos _ (hd i)) ?_ _) ?_
  · simp only [timePeriodHom_closedOrbitHomologyClass]
    exact tendsto_natCast_atTop_atTop.comp
      (tendsto_minimalPeriod_cofinite hfin hx (injective_of_existsUnique_iterate_eq hx hrep))
  · rintro ⟨i, k⟩
    have hxi := isPeriodicPt_minimalPeriod φ (x i)
    -- A term of `g` at a pair `(n, y)` depends only on `n` and `y`.
    have hg : ∀ (q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2}) {n : ℕ} {y : M}
        (hy : IsPeriodicPt φ n y), (q : ℕ × M) = (n, y) → g q =
          single (closedOrbitHomologyClass hy) (algebraMap ℚ K
            ((SignType.sign (LinearMap.det (LinearMap.id -
              fixedPointDerivative I (⇑φ)^[n] ⟨y, hy.eq⟩)) : ℤ) / n)) := by
      rintro ⟨⟨n, y⟩, hn, hy⟩ n' y' hy' h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      rfl
    -- Each of the `d` points `φ^[j] (x i)` contributes the class `(k + 1) [γ_i]` and the sign of
    -- the `(k + 1)`-fold iterate of the orbit, with weight `1 / (d (k + 1))`.
    have hterm (j : Fin (minimalPeriod φ (x i))) :
        g (sigmaMinimalPeriodEquiv (⇑φ) hx hrep ⟨(i, k), j⟩) =
          single ((k + 1) • closedOrbitHomologyClass hxi) (algebraMap ℚ K
            ((SignType.sign (LinearMap.det (LinearMap.id -
              fixedPointDerivative I (⇑φ)^[minimalPeriod φ (x i) * (k + 1)]
                ⟨x i, (hxi.mul_const (k + 1)).eq⟩)) : ℤ) /
              ((minimalPeriod φ (x i) * (k + 1) : ℕ) : ℚ))) := by
      rw [hg _ ((hxi.mul_const (k + 1)).apply_iterate j)
          (coe_sigmaMinimalPeriodEquiv_apply hx hrep _),
        closedOrbitHomologyClass_mul_apply_iterate hxi,
        det_id_sub_fixedPointDerivative_iterate_apply_iterate (hxi.mul_const (k + 1))
          fun _ _ ↦ hdiff _]
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_single, ← map_nsmul, nsmul_eq_mul]
    congr 2
    have hd' : ((minimalPeriod φ (x i) : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    push_cast
    field_simp

include hfin hx hrep in
/-- **The orbit zeta function of a mapping torus from the fixed points of the iterates.** Under the
hypotheses of `TauCeti.SmoothMappingTorus.hasSum_single_closedOrbitHomologyClass_orbitLog`, the
orbit zeta function `exp (∑ᵢ ∑_{n ≥ 1} ε i n / n · e^(n [γ_i]))` of `φ` is the exponential of
`∑_{n ≥ 1} ∑_{φ^[n] y = y} sgn det (1 - d(φ^[n])_y) / n · e^[γ_(n, y)]`. -/
theorem orbitZeta_eq_exp_tsum :
    orbitZeta K (timePeriodHom φ)
        (fun i ↦ closedOrbitHomologyClass (isPeriodicPt_minimalPeriod φ (x i)))
        (fun i n ↦ SignType.sign (LinearMap.det (LinearMap.id -
          fixedPointDerivative I (⇑φ)^[minimalPeriod φ (x i) * n]
            ⟨x i, ((isPeriodicPt_minimalPeriod φ (x i)).mul_const n).eq⟩))) =
      NormedSpace.exp (∑' q : {q : ℕ × M // 0 < q.1 ∧ IsPeriodicPt φ q.1 q.2},
        (single (closedOrbitHomologyClass q.2.2) (algebraMap ℚ K
          ((SignType.sign (LinearMap.det (LinearMap.id -
            fixedPointDerivative I (⇑φ)^[q.1.1] ⟨q.1.2, q.2.2.eq⟩)) : ℤ) / q.1.1)) :
          NovikovSeries K _ (timePeriodHom φ))) := by
  rw [orbitZeta_def, (hasSum_single_closedOrbitHomologyClass_orbitLog hfin hx hrep K).tsum_eq]

end TauCeti.SmoothMappingTorus
