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
be rational.

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
  have hl := hh.eq_left_of_isFiniteFace hf hlu
  have hu := hh.eq_right_of_isFiniteFace hf hlu
  apply hf.exists_rat_eq_and_den_dvd hlu
  · rw [hl]
    exact hint l (hl ▸ hf.left_ne_top)
  · rw [hu]
    exact hint u (hu ▸ hf.right_ne_top)

end TauCeti
