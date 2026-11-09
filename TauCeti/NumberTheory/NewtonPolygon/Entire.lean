/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.GaussNorm
public import TauCeti.NumberTheory.NewtonPolygon.Mul
public import TauCeti.RingTheory.PowerSeries.Entire.Basic

/-!
# Newton polygons of products of restricted and entire series

Fix a real additive valuation `v` on a normed division ring and a base `b > 1` with
`‖x‖ = b ^ (-(v x).untop₀)` for nonzero `x`. A nonzero series restricted at the radius `b ^ σ`
attains its Gauss norm there, so its coefficient heights touch a supporting line of slope `σ`.
Consequently, at every slope `σ` such that two series are restricted at the radius `b ^ σ`, the
supporting value at `σ` of the Newton polygon of their product is the sum of those of the
factors. This includes a radius on the boundary of convergence, where a polygon may end in a ray.

An entire series is restricted at every radius, so for entire series the supporting values add at
every slope. Since a convex height sequence is determined by its supporting values, the Newton
polygon of a product of entire series is the Minkowski sum of the Newton polygons of the factors.
This global identity fails for series that are only restricted on a disc: `1 - X` and the
geometric series `∑ Xⁿ` have product `1`, a single point, while the Minkowski sum of their
polygons is a horizontal half-line.

A nonzero entire series is restricted at every radius `b ^ σ`, so its Newton polygon touches a
supporting line of every slope `σ`, and it lies above a line of the larger slope `σ + 1`. Hence it
has a finite face of every slope. Consequently only finitely many finite unit edges have slope
below any real cutoff, and if there are infinitely many finite edges their slopes tend to infinity.

## Main results

* `PowerSeries.supportingValue_newtonPolygon_mul_of_isRestricted`: supporting values of Newton
  polygons add under multiplication at every slope of a common restricted radius.
* `PowerSeries.IsEntire.newtonPolygon_mul`: the Newton polygon of a product of entire series is
  the Minkowski sum of the Newton polygons of the factors.
* `PowerSeries.IsEntire.exists_isFiniteFace_newtonPolygon`: a nonzero entire series has a finite
  face of every slope.
* `PowerSeries.IsEntire.finite_setOf_unitSlope_newtonPolygon_le`,
  `PowerSeries.IsEntire.tendsto_unitSlope_newtonPolygon`: the slopes of an entire series are
  locally finite, and tend to infinity if there are infinitely many.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open Filter TauCeti

namespace PowerSeries

variable {K : Type*} [NormedDivisionRing K] (v : AddValuation K (WithTop ℝ)) {b : ℝ}
  (hb : 1 < b) (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f g : K⟦X⟧}

include hb hv

/-- If `f` and `g` are restricted at the radius `b ^ σ`, the supporting value at `σ` of the
Newton polygon of `f * g` is the sum of those of the Newton polygons of `f` and `g`. The radius
may lie on the boundary of convergence of either factor. -/
theorem supportingValue_newtonPolygon_mul_of_isRestricted {σ : ℝ}
    (hf : f.IsRestricted (b ^ σ)) (hg : g.IsRestricted (b ^ σ)) :
    supportingValue ((f * g).newtonPolygon v) σ =
      supportingValue (f.newtonPolygon v) σ + supportingValue (g.newtonPolygon v) σ := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul, newtonPolygon_zero, supportingValue_top, EReal.top_add_of_ne_bot
      (supportingValue_newtonPolygon_ne_bot_of_isRestricted g v hb hv hg)]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, newtonPolygon_zero, supportingValue_top, EReal.add_top_of_ne_bot
      (supportingValue_newtonPolygon_ne_bot_of_isRestricted f v hb hv hf)]
  obtain ⟨c, i, hc, hi⟩ :=
    exists_isSupportingLine_mem_supportingFace_of_isRestricted f v hb hv hf hf0
  obtain ⟨d, j, hd, hj⟩ :=
    exists_isSupportingLine_mem_supportingFace_of_isRestricted g v hb hv hg hg0
  exact supportingValue_newtonPolygon_mul v hc hi hd hj

/-- The Newton polygon of a product of entire series is the Minkowski sum of the Newton polygons
of the factors. -/
theorem IsEntire.newtonPolygon_mul (hf : f.IsEntire) (hg : g.IsEntire) :
    (f * g).newtonPolygon v = minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [zero_mul, newtonPolygon_zero, top_minkowskiSum]
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [mul_zero, newtonPolygon_zero, minkowskiSum_top]
  exact newtonPolygon_mul_of_forall_exists_mem_supportingFace v
    (fun _ => exists_isSupportingLine_mem_supportingFace_of_isRestricted f v hb hv
      (hf.isRestricted _) hf0)
    (fun _ => exists_isSupportingLine_mem_supportingFace_of_isRestricted g v hb hv
      (hg.isRestricted _) hg0)

/-- The Newton polygon of a nonzero entire series has a finite face of every real slope. -/
theorem IsEntire.exists_isFiniteFace_newtonPolygon (hf : f.IsEntire) (hf0 : f ≠ 0) (σ : ℝ) :
    ∃ l u : ℕ, IsFiniteFace (f.newtonPolygon v) σ l u := by
  -- The coefficient heights touch a supporting line of slope `σ` and lie above one of slope
  -- `σ + 1`; both lines lie below the Newton polygon, and the contact persists.
  obtain ⟨c, i, hc, hi⟩ := exists_isSupportingLine_mem_supportingFace_of_isRestricted f v hb hv
    (hf.isRestricted (b ^ σ)) hf0
  obtain ⟨c', -, hc', -⟩ := exists_isSupportingLine_mem_supportingFace_of_isRestricted f v hb hv
    (hf.isRestricted (b ^ (σ + 1))) hf0
  have henv := isLowerConvexEnvelope_newtonPolygon hc.isAdmissible
  have hσ : IsSupportingLine (f.newtonPolygon v) σ c := isSupportingLine_iff_forall.mpr <|
    henv.greatest (isConvexSeq_affine c σ) (isSupportingLine_iff_forall.mp hc)
  have hσ' : IsSupportingLine (f.newtonPolygon v) (σ + 1) c' := isSupportingLine_iff_forall.mpr <|
    henv.greatest (isConvexSeq_affine c' (σ + 1)) (isSupportingLine_iff_forall.mp hc')
  exact (f.isConvexSeq_newtonPolygon v).exists_isFiniteFace_of_finite_supportingFace hσ
    (hσ'.finite_supportingFace (lt_add_one σ) c) ⟨i, henv.supportingFace_subset hc hi⟩

/-- **Local finiteness of slopes.** Only finitely many finite unit edges of the Newton polygon
of an entire series have slope at most a given real number. -/
theorem IsEntire.finite_setOf_unitSlope_newtonPolygon_le (hf : f.IsEntire) (c : ℝ) :
    {n | n ∈ finiteEdges (f.newtonPolygon v) ∧ unitSlope (f.newtonPolygon v) n ≤ c}.Finite := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨l, u, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 c
  exact hface.finite_setOf_unitSlope_le (f.isConvexSeq_newtonPolygon v)

/-- If the Newton polygon of an entire series has infinitely many finite unit edges, their
slopes tend to infinity. -/
theorem IsEntire.tendsto_unitSlope_newtonPolygon (hf : f.IsEntire)
    (hinf : (finiteEdges (f.newtonPolygon v)).Infinite) :
    Tendsto (unitSlope (f.newtonPolygon v)) atTop atTop := by
  -- The finite edges are order connected and unbounded, so they contain a final segment.
  obtain ⟨a, ha⟩ := hinf.nonempty
  have hedges : ∀ᶠ n in atTop, n ∈ finiteEdges (f.newtonPolygon v) := by
    refine eventually_atTop.mpr ⟨a, fun n han => ?_⟩
    obtain ⟨m, hm, hnm⟩ := hinf.exists_gt n
    exact (ordConnected_finiteEdges (f.isConvexSeq_newtonPolygon v).ordConnected).out ha hm
      ⟨han, hnm.le⟩
  refine tendsto_atTop.mpr fun c => ?_
  have hfin := (hf.finite_setOf_unitSlope_newtonPolygon_le v hb hv c).eventually_cofinite_notMem
  rw [Nat.cofinite_eq_atTop] at hfin
  filter_upwards [hedges, hfin] with n hn hnc
  exact le_of_not_ge fun hle => hnc ⟨hn, hle⟩

end PowerSeries
