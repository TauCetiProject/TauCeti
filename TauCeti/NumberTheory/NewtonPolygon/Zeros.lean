/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Multiplicity
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.NumberTheory.NewtonPolygon.Weierstrass
public import TauCeti.RingTheory.PowerSeries.Entire.GoodZero
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Zeros of entire series on spheres and slope multiplicities

Let `K` be a complete ultrametric normed field whose norm comes from a real additive valuation
`v` with base `b > 1`, so `‖x‖ = b ^ (-v x)` for `x ≠ 0`. The *multiplicity* of a zero `x` of a
power series `f` is the order at zero of its Taylor translate `taylor x f = f(x + T)`
(`PowerSeries.taylor`); for an entire series it is the order of the good zero of `f` at `x`
(`PowerSeries.isGoodZero_iff_order_taylor_eq`), and it is `0` exactly when `f(x) ≠ 0`.

When `K` is algebraically closed, the zeros of a nonzero entire series `f` on the sphere
`‖x‖ = b ^ σ`, counted with multiplicity, number exactly the multiplicity of the slope `σ` in the
Newton polygon of `f`:

`newtonSlopeMultiplicity f v σ = ∑ᶠ x ∈ sphere 0 (b ^ σ), order (taylor x f)`
(`PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor`).

In particular each sphere carries only finitely many zeros
(`PowerSeries.IsEntire.finite_setOf_norm_eq_and_evalAt_eq_zero`), and a slope of positive
multiplicity is the negated valuation of an actual zero
(`PowerSeries.IsEntire.exists_norm_eq_and_evalAt_eq_zero`). The latter is read off a Weierstrass
preparation at the radius `b ^ σ`: the prepared polynomial carries the finite unit edges of slope
`σ`, so it has a root of norm `b ^ σ`. The count then follows by splitting off the factor
`(X - x) ^ h` at such a zero, which has slope `σ` with multiplicity `h`, since slope multiplicities
of entire series add under products (`PowerSeries.IsEntire.newtonSlopeMultiplicity_mul`) and so do
orders of zeros. Algebraic closedness is needed for the existence of zeros: over `ℚ_p` the
polynomial `1 - X ^ 2 / p` has slope `-1 / 2` with multiplicity two but no zero.

These counts apply to Fredholm series `det (1 - T u)` of compact operators, whose zeros are the
inverses of the nonzero eigenvalues.

## Main results

* `PowerSeries.IsEntire.exists_norm_eq_and_evalAt_eq_zero`: a slope of positive multiplicity comes
  from a zero on the corresponding sphere.
* `PowerSeries.IsEntire.finite_setOf_norm_eq_and_evalAt_eq_zero`: a nonzero entire series has only
  finitely many zeros on each sphere.
* `PowerSeries.IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor`: the multiplicity of a
  slope counts the zeros on the corresponding sphere with multiplicity.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §§1, 3.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §4.
-/

public section

open TauCeti

namespace PowerSeries

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (v : AddValuation K (WithTop ℝ)) {b : ℝ} (hb : 1 < b)
  (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {f : K⟦X⟧}

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- A power of `X - x`, for `x` on the sphere of radius `b ^ σ`, has the slope `σ` with
multiplicity its exponent. -/
private theorem newtonSlopeMultiplicity_X_sub_C_pow (hb : 1 < b)
    (hv : ∀ x ≠ 0, ‖x‖ = b ^ (-(v x).untop₀)) {σ : ℝ} {x : K} (hx : ‖x‖ = b ^ σ) (h : ℕ) :
    ((X - C x) ^ h : K⟦X⟧).newtonSlopeMultiplicity v σ = h := by
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ).ne' (by simpa using hx.symm)
  have hσ : -(v x).untop₀ = σ :=
    (Real.rpow_right_inj (zero_lt_one.trans hb) hb.ne').mp ((hv x hx0).symm.trans hx)
  have hpoly : ((X - C x) ^ h : K⟦X⟧) =
      (((Multiset.replicate h x).map (Polynomial.X - Polynomial.C ·)).prod : Polynomial K) := by
    simp [Multiset.map_replicate, Multiset.prod_replicate]
  rw [hpoly, Polynomial.newtonSlopeMultiplicity_coe,
    Polynomial.newtonSlopes_multiset_prod_X_sub_C (fun _ ↦ v.top_iff.mp),
    Multiset.filter_eq_self.mpr fun y hy ↦ (Multiset.eq_of_mem_replicate hy).symm ▸ hx0,
    Multiset.map_replicate, hσ, Multiset.count_replicate_self]

include hb hv

/-- **Zeros at every slope.** Over a complete algebraically closed ultrametric field, if the slope
`σ` has positive multiplicity in the Newton polygon of an entire series `f`, then `f` has a zero
on the sphere `‖x‖ = b ^ σ`. -/
theorem IsEntire.exists_norm_eq_and_evalAt_eq_zero [IsAlgClosed K] (hf : f.IsEntire) {σ : ℝ}
    (hσ : f.newtonSlopeMultiplicity v σ ≠ 0) : ∃ x : K, ‖x‖ = b ^ σ ∧ f.evalAt x = 0 := by
  classical
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hσ (newtonSlopeMultiplicity_zero v σ)
  have hc : 0 < b ^ σ := Real.rpow_pos_of_pos (zero_lt_one.trans hb) σ
  obtain ⟨l, j, hface⟩ := hf.exists_isFiniteFace_newtonPolygon v hb hv hf0 σ
  have hlj : l < j := by
    rw [newtonSlopeMultiplicity_eq_of_isFiniteFace hface] at hσ
    omega
  -- Prepare `f = e * ω` at the radius `b ^ σ`, at the right end `j` of the face of slope `σ`.
  have hfd := isDistinguished_of_isFiniteFace v hb hv (hf.isRestricted _) hface
  obtain ⟨e, ω, he, hω, heω⟩ :=
    hfd.exists_isUnit_isMonicOfDegree_mul_eq hfd.coeff_ne_zero.isUnit hc (hf.isRestricted _)
  -- The unit edge of `f` at `l` has slope `σ`, and `ω` has the same edge.
  have hl : l ∈ finiteEdges (f.newtonPolygon v) := by
    have hmem : l ∈ Set.Ico l j := ⟨le_rfl, hlj⟩
    rw [← hface.setOf_unitSlope_eq (f.isConvexSeq_newtonPolygon v)] at hmem
    exact hmem.1
  have hlω := (mem_finiteEdges_newtonPolygon_iff_of_isUnit_mul v hb hv hfd he
    hω.natDegree_eq.le heω l).mpr ⟨hl, hlj⟩
  have hslope : unitSlope (ω.newtonPolygon v) l = σ :=
    (unitSlope_newtonPolygon_eq_of_isUnit_mul v hb hv hfd he hω.natDegree_eq.le heω hl
      hlj).trans (hface.unitSlope_eq le_rfl hlj)
  have hmem : σ ∈ ω.newtonSlopes v := (Polynomial.mem_newtonSlopes ω v).mpr ⟨l, hlω, hslope⟩
  -- Over an algebraically closed field the slope `σ` of `ω` comes from a root of norm `b ^ σ`.
  rw [Polynomial.newtonSlopes_eq_map_roots (fun _ ↦ v.top_iff.mp) (IsAlgClosed.splits ω)]
    at hmem
  obtain ⟨x, hx, hxσ⟩ := Multiset.mem_map.mp hmem
  obtain ⟨hxroot, hx0⟩ := Multiset.mem_filter.mp hx
  have hxnorm : ‖x‖ = b ^ σ := by rw [hv x hx0, hxσ]
  refine ⟨x, hxnorm, ?_⟩
  rw [← heω, IsRestricted.evalAt_mul e.2 (TauCeti.PowerSeries.isRestricted_polynomial _)
    hxnorm.le, evalAt_coe, Polynomial.coe_aeval_eq_eval,
    ((Polynomial.mem_roots hω.monic.ne_zero).mp hxroot).eq_zero, mul_zero]

/-- The zeros of a nonzero entire series on a sphere, with their orders, add up to the
multiplicity of the corresponding slope. This is the joint finiteness and counting statement,
proved by splitting off one zero at a time. -/
private theorem exists_finset_newtonSlopeMultiplicity_eq_sum [IsAlgClosed K]
    (σ : ℝ) : ∀ (n : ℕ) (f : K⟦X⟧), f.IsEntire → f ≠ 0 → f.newtonSlopeMultiplicity v σ = n →
      ∃ s : Finset K, (∀ x, x ∈ s ↔ ‖x‖ = b ^ σ ∧ f.evalAt x = 0) ∧
        (n : ℕ∞) = ∑ x ∈ s, (PowerSeries.taylor x f).order := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hf hf0 hn
  -- A zero `x` of order `h` on the sphere splits off a factor of slope `σ` and multiplicity `h`.
  have split {x : K} (hx : ‖x‖ = b ^ σ) (hfx : f.evalAt x = 0) :
      ∃ h g, 0 < h ∧ f.IsGoodZero x h ∧ g.IsEntire ∧ g ≠ 0 ∧ g.evalAt x ≠ 0 ∧
        f = (X - C x) ^ h * g ∧ n = h + g.newtonSlopeMultiplicity v σ := by
    obtain ⟨h, hh, hfxh⟩ := hf.exists_pos_isGoodZero_of_evalAt_eq_zero hf0 hfx
    obtain ⟨g, hg, rfl, hgx⟩ := hf.isGoodZero_iff.mp hfxh
    have hg0 : g ≠ 0 := by
      rintro rfl
      exact hf0 (mul_zero _)
    refine ⟨h, g, hh, hfxh, hg, hg0, hgx.ne_zero, rfl, ?_⟩
    rw [← hn, ((isEntire_X.sub (isEntire_C x)).pow h).newtonSlopeMultiplicity_mul v hb hv hg
      (left_ne_zero_of_mul hf0) hg0,
      newtonSlopeMultiplicity_X_sub_C_pow v hb hv hx]
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · -- With no slope `σ`, there is no zero on the sphere.
    refine ⟨∅, fun x ↦ ⟨fun hx ↦ absurd hx (Finset.notMem_empty x), fun ⟨hx, hfx⟩ ↦ ?_⟩, by simp⟩
    obtain ⟨h, g, hh, -, -, -, -, -, hhg⟩ := split hx hfx
    omega
  obtain ⟨x, hx, hfx⟩ := hf.exists_norm_eq_and_evalAt_eq_zero v hb hv (hn ▸ hnpos.ne')
  obtain ⟨h, g, hh, hfxh, hg, hg0, hgx, rfl, hhg⟩ := split hx hfx
  obtain ⟨s, hs, hsum⟩ := ih (g.newtonSlopeMultiplicity v σ) (by omega) g hg hg0 rfl
  have hlin : (X - C x : K⟦X⟧).IsEntire := isEntire_X.sub (isEntire_C x)
  have hfac : ((X - C x) ^ h : K⟦X⟧).IsEntire := hlin.pow h
  have hxs : x ∉ s := fun hxs ↦ hgx ((hs x).mp hxs).2
  -- Away from `x` the factor `(X - x) ^ h` is a unit, so `f` and `g` have the same zeros there.
  have hord {y : K} (hy : y ≠ x) :
      (PowerSeries.taylor y ((X - C x) ^ h * g)).order = (PowerSeries.taylor y g).order := by
    obtain ⟨k, hk⟩ := hg.exists_isGoodZero hg0 y
    have hunit : IsUnit (((X - C x) ^ h : K⟦X⟧).evalAt y) := by
      rw [hlin.evalAt_pow, evalAt_X_sub_C]
      exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hy)).pow h
    rw [isGoodZero_iff_order_taylor_eq.mp hk, mul_comm,
      isGoodZero_iff_order_taylor_eq.mp ((hg.isGoodZero_mul_iff_of_isUnit hfac hunit).mpr hk)]
  refine ⟨insert x s, fun y ↦ ?_, ?_⟩
  · rw [Finset.mem_insert, hs y, hfac.evalAt_mul hg, hlin.evalAt_pow, evalAt_X_sub_C, mul_eq_zero,
      pow_eq_zero_iff hh.ne', sub_eq_zero, Algebra.algebraMap_self_apply]
    constructor
    · rintro (rfl | ⟨hy, hgy⟩)
      exacts [⟨hx, .inl rfl⟩, ⟨hy, .inr hgy⟩]
    · rintro ⟨hy, rfl | hgy⟩
      exacts [.inl rfl, .inr ⟨hy, hgy⟩]
  · rw [Finset.sum_insert hxs, isGoodZero_iff_order_taylor_eq.mp hfxh,
      Finset.sum_congr rfl fun y hy ↦ hord (ne_of_mem_of_not_mem hy hxs), ← hsum, hhg]
    exact Nat.cast_add _ _

/-- Over a complete algebraically closed ultrametric field, a nonzero entire series has only
finitely many zeros on each sphere `‖x‖ = b ^ σ`. -/
theorem IsEntire.finite_setOf_norm_eq_and_evalAt_eq_zero [IsAlgClosed K] (hf : f.IsEntire)
    (hf0 : f ≠ 0) (σ : ℝ) : {x : K | ‖x‖ = b ^ σ ∧ f.evalAt x = 0}.Finite := by
  obtain ⟨s, hs, -⟩ := exists_finset_newtonSlopeMultiplicity_eq_sum v hb hv σ _ f hf hf0 rfl
  exact s.finite_toSet.subset fun x hx ↦ (hs x).mpr hx

/-- **Slope multiplicities count zeros.** Over a complete algebraically closed ultrametric
field, the multiplicity of the slope `σ` in the Newton polygon of a nonzero entire series `f` is
the number of zeros of `f` on the sphere `‖x‖ = b ^ σ`, each counted with its multiplicity, the
order of the Taylor translate `taylor x f`. -/
theorem IsEntire.newtonSlopeMultiplicity_eq_finsum_order_taylor [IsAlgClosed K]
    (hf : f.IsEntire) (hf0 : f ≠ 0) (σ : ℝ) :
    (f.newtonSlopeMultiplicity v σ : ℕ∞) =
      ∑ᶠ x ∈ Metric.sphere (0 : K) (b ^ σ), (PowerSeries.taylor x f).order := by
  obtain ⟨s, hs, hsum⟩ := exists_finset_newtonSlopeMultiplicity_eq_sum v hb hv σ _ f hf hf0 rfl
  rw [hsum, finsum_mem_eq_sum_of_inter_support_eq]
  ext x
  simp only [Set.mem_inter_iff, mem_sphere_iff_norm, sub_zero, Function.mem_support,
    Finset.mem_coe, hs x, ne_eq]
  obtain ⟨h, hxh⟩ := hf.exists_isGoodZero hf0 x
  rw [isGoodZero_iff_order_taylor_eq.mp hxh, Nat.cast_eq_zero]
  have : f.evalAt x = 0 ↔ h ≠ 0 := by
    rcases Nat.eq_zero_or_pos h with rfl | hh
    · simpa using (isGoodZero_zero_iff.mp hxh).ne_zero
    · simpa [hh.ne'] using hxh.evalAt_eq_zero hh
  tauto

end PowerSeries
