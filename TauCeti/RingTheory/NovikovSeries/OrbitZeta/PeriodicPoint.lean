/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.PeriodicPts.Parametrization
public import TauCeti.RingTheory.NovikovSeries.OrbitZeta.Basic

/-!
# The orbit logarithm of a map as a sum over its periodic points

Let `f : α → α` be a map, and let `x : ι → α` list one point on each periodic orbit of `f`: every
periodic point is `f^[j] (x i)` for exactly one `i`. The `i`-th orbit has least period
`d i = minimalPeriod f (x i)`. The orbit logarithm (`TauCeti.NovikovSeries.orbitLog`) of these
orbits is a sum over the primitive orbits and their iterates,

`L = ∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) · e^((k + 1) • γ i)`.

This file rewrites it as a sum over the periodic points with a chosen positive period: for
`n > 0` and `y` with `f^[n] y = y`,

`L = ∑_{(n, y)} s(n, y) / n · e^(c(n, y))`,

provided the exponent `c(n, y)` and the sign `s(n, y)` attached to the periodic point `y` of
period `n` only depend on the orbit of `y` and on the number `n / d i` of times the orbit is
traversed: `c((k + 1) d i, f^[j] (x i)) = (k + 1) • γ i` and
`s((k + 1) d i, f^[j] (x i)) = ε i (k + 1)`
(`TauCeti.NovikovSeries.hasSum_orbitLog_periodicPts`).

Indeed the points of period `(k + 1) d i` on the `i`-th orbit are the `d i` points `f^[j] (x i)`
with `j < d i` (`Function.bijective_periodicPtsParam`), and the `(k + 1)`-fold iterate of the orbit
is counted once for each of them, with weight `ε i (k + 1) / ((k + 1) d i)`. Together they
contribute `ε i (k + 1) / (k + 1)`, the term of the orbit logarithm. The multiplicity `k + 1` in the
denominator of the orbit logarithm thus becomes the period `n` in the denominator of the sum over
periodic points.

For a diffeomorphism of a compact manifold, with `c(n, y)` the class of the closed orbit of the
suspension flow through `y` and `s(n, y)` the Lefschetz sign of `y` as a fixed point of `f^[n]`,
the sum over periodic points of a fixed period `n` is the signed count of fixed points of `f^[n]`
entering the Lefschetz fixed-point formula. Grouping the sum by `n` turns the orbit zeta function
into the exponential of the series of these fixed-point counts.

## Main results

* `TauCeti.NovikovSeries.hasSum_orbitLog_periodicPts`: the orbit logarithm as a sum over periodic
  points with a chosen positive period.

## References

* M. Artin and B. Mazur, *On periodic points*, Ann. of Math. 81 (1965), 82–99.
* M. Hutchings and Y.-J. Lee, *Circle-valued Morse theory and Reidemeister torsion*,
  Geom. Topol. 3 (1999).
-/

public section

noncomputable section

open Filter Function Topology

namespace TauCeti.NovikovSeries

variable {α ι H : Type*} [AddCommMonoid H] {N : H →+ ℝ} {K : Type*} [CommRing K] [Algebra ℚ K]
  {f : α → α} {x : ι → α}

/-- **The orbit logarithm as a sum over periodic points.** Let `x : ι → α` list one point on each
periodic orbit of `f`, with least periods `d i = minimalPeriod f (x i)`, and let `γ i` be classes of
positive period, only finitely many below each cutoff. Attach to each periodic point `y` with a
chosen positive period `n` an exponent `c(n, y)` and a sign `s(n, y)`, which on the `i`-th orbit
traversed `k + 1` times are `(k + 1) • γ i` and `ε i (k + 1)`. Then

`∑_{(n, y)} s(n, y) / n · e^(c(n, y)) = ∑ᵢ ∑ₖ ε i (k + 1) / (k + 1) · e^((k + 1) • γ i)`,

the orbit logarithm of the orbits. -/
theorem hasSum_orbitLog_periodicPts (hx : ∀ i, x i ∈ periodicPts f)
    (hrep : ∀ y ∈ periodicPts f, ∃! i, ∃ j, f^[j] (x i) = y) {γ : ι → H}
    (hpos : ∀ i, 0 < N (γ i)) (hfin : Tendsto (fun i ↦ N (γ i)) cofinite atTop)
    {ε : ι → ℕ → ℤ} (c : {p : ℕ × α // 0 < p.1 ∧ IsPeriodicPt f p.1 p.2} → H)
    (s : {p : ℕ × α // 0 < p.1 ∧ IsPeriodicPt f p.1 p.2} → ℤ)
    (hc : ∀ i k j hp, c ⟨((k + 1) * minimalPeriod f (x i), f^[j] (x i)), hp⟩ = (k + 1) • γ i)
    (hs : ∀ i k j hp, s ⟨((k + 1) * minimalPeriod f (x i), f^[j] (x i)), hp⟩ = ε i (k + 1)) :
    HasSum (fun p ↦ (single (c p) (algebraMap ℚ K ((s p : ℚ) / p.1.1)) : NovikovSeries K H N))
      (orbitLog K N γ ε) := by
  set d : ι → ℕ := fun i ↦ minimalPeriod f (x i)
  have hd (i : ι) : 0 < d i := minimalPeriod_pos_of_mem_periodicPts (hx i)
  -- The term of the `(k + 1)`-fold iterate of the `i`-th orbit counted at its `j`-th point.
  set F : (ι × ℕ) × ℕ → NovikovSeries K H N := fun q ↦ single ((q.1.2 + 1) • γ q.1.1)
    (algebraMap ℚ K ((ε q.1.1 (q.1.2 + 1) : ℚ) / ((q.1.2 + 1) * d q.1.1 : ℕ)))
  set S : Set ((ι × ℕ) × ℕ) := {q | q.2 < d q.1.1}
  rw [← (Equiv.ofBijective _ (bijective_periodicPtsParam hx hrep)).hasSum_iff]
  have hterm : (fun p : {p : ℕ × α // 0 < p.1 ∧ IsPeriodicPt f p.1 p.2} ↦
      (single (c p) (algebraMap ℚ K ((s p : ℚ) / p.1.1)) : NovikovSeries K H N)) ∘
        Equiv.ofBijective _ (bijective_periodicPtsParam hx hrep) = fun q ↦ F q.1 := by
    funext ⟨⟨⟨i, k⟩, j⟩, hj⟩
    have hq : periodicPtsParam hx ⟨((i, k), j), hj⟩ =
        ⟨_, isPeriodicPt_succ_mul_minimalPeriod_iterate hx i k j⟩ :=
      Subtype.ext (coe_periodicPtsParam hx _)
    simp only [comp_apply, Equiv.ofBijective_apply, hq, hc, hs, F, d]
  rw [hterm]
  refine (hasSum_subtype_iff_indicator (s := S) (f := F)).2 ?_
  -- The terms tend to zero: only finitely many lie below each cutoff.
  have hsum : Summable (S.indicator F) := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
      (hasBasis_nhds_zero.tendsto_right_iff.2 fun C _ ↦ eventually_cofinite.2 ?_)
    refine (((finite_setOf_period_succ_nsmul_lt hpos hfin C).biUnion fun p _ ↦
      (Set.finite_Iio (d p.1)).image fun j ↦ (p, j))).subset fun q hq ↦ ?_
    by_cases hqS : q ∈ S
    · refine Set.mem_biUnion (x := q.1) ?_ ⟨q.2, hqS, rfl⟩
      simp only [Set.mem_ofPred_eq]
      refine lt_of_not_ge fun hC ↦ hq ?_
      rw [Set.indicator_of_mem hqS]
      exact antitone_periodFiltration hC (single_mem_periodFiltration _ _)
    · exact absurd (by rw [Set.indicator_of_notMem hqS]; exact zero_mem _) hq
  -- The `d i` points of the `i`-th orbit together contribute the term of its `(k + 1)`-fold
  -- iterate to the orbit logarithm.
  have hfib (p : ι × ℕ) : HasSum (fun j ↦ S.indicator F (p, j))
      (single ((p.2 + 1) • γ p.1) (algebraMap ℚ K ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ)))) := by
    have hsupp : ∀ j ∉ Finset.range (d p.1), S.indicator F (p, j) = 0 := fun j hj ↦
      Set.indicator_of_notMem (by simpa [S] using hj) _
    have hval : ∑ j ∈ Finset.range (d p.1), S.indicator F (p, j) =
        single ((p.2 + 1) • γ p.1) (algebraMap ℚ K ((ε p.1 (p.2 + 1) : ℚ) / (p.2 + 1 : ℕ))) := by
      rw [Finset.sum_congr rfl fun j hj ↦ Set.indicator_of_mem (by simpa [S] using hj) _]
      simp only [F]
      rw [Finset.sum_const, Finset.card_range, smul_single, nsmul_eq_mul,
        ← map_natCast (algebraMap ℚ K), ← _root_.map_mul]
      congr 2
      have := (hd p.1).ne'
      push_cast
      field_simp
    rw [← hval]
    exact hasSum_sum_of_ne_finset_zero hsupp
  rw [← (hsum.hasSum.prod_fiberwise hfib).unique (hasSum_orbitLog hpos hfin ε)]
  exact hsum.hasSum

end TauCeti.NovikovSeries
