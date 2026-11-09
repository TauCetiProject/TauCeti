/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Vertex
public import TauCeti.Data.Rat.NumDenDvd

/-!
# Rational slopes of bounded faces

A finite face of positive width and integral endpoint heights has rational slope, with
reduced denominator dividing its horizontal length. For a lower convex envelope of integral
coefficient heights, the endpoint integrality follows from contact: both endpoints of each
bounded face of positive width are original coefficient points. The finite domain itself
may be unbounded, and intermediate envelope heights need not be integral.

The positive-width hypothesis is essential: a singleton can be a face at irrational slopes.
Terminal rays are also excluded; integral coefficient heights do not force their slopes to
be rational. For rational coefficient heights and an envelope with finite domain, every
finite envelope height is rational, including the interpolated noncontact heights.

The arithmetic uses `Rat.den_dvd_iff_exists_eq_intCast_div`, ultimately Mathlib's
`Rat.den_dvd`, rather than introducing another reduced-fraction construction.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

namespace TauCeti

/-- A finite face of positive width and integral endpoints has rational slope. Its reduced
denominator divides the width, even when the polygon has unbounded finite domain. -/
theorem IsFiniteFace.exists_rat_eq_and_den_dvd {h : ℕ → WithTop ℝ} {σ : ℝ} {l u : ℕ}
    (hf : IsFiniteFace h σ l u) (hlu : l < u)
    (hl : ∃ y : ℤ, h l = ((y : ℝ) : WithTop ℝ))
    (hu : ∃ z : ℤ, h u = ((z : ℝ) : WithTop ℝ)) :
    ∃ q : ℚ, (q : ℝ) = σ ∧ q.den ∣ u - l := by
  obtain ⟨y, hy⟩ := hl
  obtain ⟨z, hz⟩ := hu
  refine ⟨(z - y : ℤ) / (u - l : ℕ), ?_, ?_⟩
  · rw [hf.slope_eq_div hlu, hy, hz]
    simp
  · exact (Rat.den_dvd_iff_exists_eq_intCast_div (Nat.sub_pos_of_lt hlu).ne').mpr
      ⟨z - y, rfl⟩

/-- Every bounded face of positive width of an envelope of integral coefficient heights has
rational slope with reduced denominator dividing its width. Missing coefficients are allowed,
and no integrality is assumed for the interpolated heights between contact points. -/
theorem IsLowerConvexEnvelope.exists_rat_eq_and_den_dvd_of_isFiniteFace
    {a h : ℕ → WithTop ℝ} (hh : IsLowerConvexEnvelope a h)
    (hint : ∀ n, a n ≠ ⊤ → ∃ z : ℤ, a n = ((z : ℝ) : WithTop ℝ))
    {σ : ℝ} {l u : ℕ} (hf : IsFiniteFace h σ l u) (hlu : l < u) :
    ∃ q : ℚ, (q : ℝ) = σ ∧ q.den ∣ u - l := by
  have hl := hh.eq_left_of_isFiniteFace hf
  have hu := hh.eq_right_of_isFiniteFace hf
  apply hf.exists_rat_eq_and_den_dvd hlu
  · rw [hl]
    exact hint l (hl ▸ hf.left_ne_top)
  · rw [hu]
    exact hint u (hu ▸ hf.right_ne_top)

/-- A bounded face of positive width with rational endpoint heights has rational slope.
A singleton face is excluded, since it can support lines of irrational slope. -/
theorem IsFiniteFace.exists_rat_slope {h : ℕ → WithTop ℝ} {σ : ℝ} {l u : ℕ}
    (hf : IsFiniteFace h σ l u) (hlu : l < u)
    (hl : ∃ y : ℚ, h l = ((y : ℝ) : WithTop ℝ))
    (hu : ∃ z : ℚ, h u = ((z : ℝ) : WithTop ℝ)) :
    ∃ q : ℚ, (q : ℝ) = σ := by
  obtain ⟨y, hy⟩ := hl
  obtain ⟨z, hz⟩ := hu
  refine ⟨(z - y) / (u - l : ℕ), ?_⟩
  rw [hf.slope_eq_div hlu, hy, hz]
  simp

/-- Every finite height of a finite-domain lower convex envelope of rational point heights
is rational. Missing coefficients and noncontact indices are allowed. The bounded-domain
hypothesis excludes terminal rays, whose slopes need not be rational. -/
theorem IsLowerConvexEnvelope.exists_rat_height_of_finiteDomain
    {a h : ℕ → WithTop ℝ} (hh : IsLowerConvexEnvelope a h)
    (hint : ∀ n, a n ≠ ⊤ → ∃ q : ℚ, a n = ((q : ℝ) : WithTop ℝ))
    (hfin : {n | h n ≠ ⊤}.Finite) {n : ℕ} (hn : h n ≠ ⊤) :
    ∃ q : ℚ, h n = ((q : ℝ) : WithTop ℝ) := by
  obtain ⟨c, σ, hc, heq⟩ := hh.isConvexSeq.exists_affine_minorant_eq hn
  have hc' : IsSupportingLine h σ c := isSupportingLine_iff_forall.mpr hc
  have hnc : n ∈ supportingFace h σ c := by
    rw [mem_supportingFace, heq, WithTop.coe_untop₀_of_ne_top hn]
  have hfacefin : (supportingFace h σ c).Finite := hfin.subset fun i hi => by
    rw [mem_supportingFace] at hi
    simpa only [Set.mem_ofPred_eq, hi] using (WithTop.coe_ne_top (a := c + σ * i))
  obtain ⟨l, u, hf⟩ := hh.isConvexSeq.exists_isFiniteFace_of_finite_supportingFace
    hc' hfacefin ⟨n, hnc⟩
  obtain ⟨d, hd, hface⟩ := hf.exists_intercept
  have hcd : c = d := by
    have hld : l ∈ supportingFace h σ d := hface.symm.subset ⟨le_rfl, hf.left_le_right⟩
    exact EReal.coe_injective ((supportingValue_eq_coe_of_mem_supportingFace hc' hnc).symm.trans
      (supportingValue_eq_coe_of_mem_supportingFace hd hld))
  subst d
  have hni : n ∈ Set.Icc l u := hface.subset hnc
  obtain ⟨y, hy⟩ : ∃ y : ℚ, h l = ((y : ℝ) : WithTop ℝ) := by
    rw [hh.eq_left_of_isFiniteFace hf]
    exact hint l (hh.eq_left_of_isFiniteFace hf ▸ hf.left_ne_top)
  rcases eq_or_lt_of_le hf.left_le_right with rfl | hlu
  · obtain rfl : n = l := by have := hni.1; have := hni.2; omega
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ : ∃ z : ℚ, h u = ((z : ℝ) : WithTop ℝ) := by
    rw [hh.eq_right_of_isFiniteFace hf]
    exact hint u (hh.eq_right_of_isFiniteFace hf ▸ hf.right_ne_top)
  obtain ⟨q, hq⟩ := hf.exists_rat_slope hlu ⟨y, hy⟩ ⟨z, hz⟩
  refine ⟨y + q * (n - l : ℕ), ?_⟩
  have hlc := mem_supportingFace.mp (hface.symm.subset ⟨le_rfl, hf.left_le_right⟩)
  have hyl : (y : ℝ) = c + σ * l := WithTop.coe_injective (hy.symm.trans hlc)
  rw [mem_supportingFace] at hnc
  rw [hnc, WithTop.coe_eq_coe]
  push_cast
  rw [hq, Nat.cast_sub hni.1, hyl]
  ring

end TauCeti
