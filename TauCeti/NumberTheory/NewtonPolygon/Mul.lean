/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Basic
public import TauCeti.Analysis.Convex.Sequence.Minkowski.Face

/-!
# Newton polygons of products

The coefficient heights of a product `f * g` lie above the Minkowski sum (min-convolution)
of the coefficient heights of `f` and `g`, by the ultrametric inequality. At the least, and
likewise at the greatest, contact indices of supporting lines of a common slope, the
coefficient of the product has a unique dominant term, so the inequality is an equality
there. These coefficient statements hold for power series over any ring with a real additive
valuation, without any convergence hypothesis.

For polynomials every supporting line touches the coefficient heights, so the supporting
values of `f * g` are the sums of those of `f` and `g`. In the language of Gauss norms this is
the multiplicativity of Gauss norms at every radius. Reconstructing a convex sequence from its
supporting lines then gives the product formula for Newton polygons: the polygon of `f * g`
is the Minkowski sum of the polygons of `f` and `g`. No hypothesis on `f`, `g` or `v` is
needed; if either factor has empty polygon, both sides are empty.

## Main results

* `PowerSeries.minkowskiSum_le_addValuation_coeff_mul`: the coefficient heights of a product
  lie above the Minkowski sum of the coefficient heights of the factors.
* `PowerSeries.addValuation_coeff_mul_of_isLeast` and
  `PowerSeries.addValuation_coeff_mul_of_isGreatest`: the unique dominant term at the sum of
  the least, respectively greatest, contact indices of supporting lines of a common slope.
* `Polynomial.supportingValue_addValuation_coeff_mul`: supporting values of coefficient heights
  add under multiplication of polynomials.
* `Polynomial.newtonPolygon_mul`: the Newton polygon of a product of polynomials is the
  Minkowski sum of the Newton polygons of the factors.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
-/

public section

open Finset TauCeti

namespace PowerSeries

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- The coefficient heights of a product of power series lie above the Minkowski sum of the
coefficient heights of the factors. -/
theorem minkowskiSum_le_addValuation_coeff_mul (f g : R⟦X⟧) (n : ℕ) :
    minkowskiSum (fun n => v (coeff n f)) (fun n => v (coeff n g)) n ≤
      v (coeff n (f * g)) := by
  rw [coeff_mul]
  exact v.map_le_sum fun p hp =>
    (minkowskiSum_le_add_of_add_eq (mem_antidiagonal.mp hp)).trans_eq (v.map_mul _ _).symm

variable {v} {f g : R⟦X⟧} {σ c d : ℝ} {l l' : ℕ}

/-- If `l` and `l'` touch supporting lines of a common slope for the coefficient heights of
`f` and `g`, and no other split of `l + l'` touches both lines, then the coefficient of
`f * g` at `l + l'` has a unique term of least valuation. -/
private theorem addValuation_coeff_mul_of_unique
    (hc : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hl : l ∈ supportingFace (fun n => v (coeff n f)) σ c)
    (hd : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hl' : l' ∈ supportingFace (fun n => v (coeff n g)) σ d)
    (huniq : ∀ i j, i + j = l + l' → i ∈ supportingFace (fun n => v (coeff n f)) σ c →
      j ∈ supportingFace (fun n => v (coeff n g)) σ d → i = l) :
    v (coeff (l + l') (f * g)) = v (coeff l f) + v (coeff l' g) := by
  classical
  have hmin := minkowskiSum_add_eq_of_mem_supportingFace hc hl hd hl'
  have hmem := (mem_supportingFace_minkowskiSum_iff hc hd).mpr ⟨l, l', rfl, hl, hl'⟩
  have hfin : v (coeff l f) + v (coeff l' g) ≠ ⊤ := by
    rw [mem_supportingFace] at hl hl'
    rw [hl, hl', ← WithTop.coe_add]
    exact WithTop.coe_ne_top
  have hll' : (l, l') ∈ antidiagonal (l + l') := mem_antidiagonal.mpr rfl
  rw [coeff_mul, ← add_sum_erase _ _ hll', v.map_add_eq_of_lt_left, v.map_mul]
  rw [v.map_mul]
  refine v.map_lt_sum hfin fun p hp => ?_
  obtain ⟨hne, hp⟩ := mem_erase.mp hp
  have hp' : p.1 + p.2 = l + l' := mem_antidiagonal.mp hp
  rw [v.map_mul]
  refine (hmin ▸ minkowskiSum_le_add_of_add_eq hp').lt_of_ne fun heq => hne ?_
  obtain ⟨hi, hj⟩ := (minkowskiSum_add_eq_add_iff_of_mem_supportingFace hc hd (hp' ▸ hmem)).mp
    (by rw [hp', hmin, heq])
  have hi' := huniq p.1 p.2 hp' hi hj
  exact Prod.ext hi' (by omega)

/-- At the sum of the least contact indices of supporting lines of a common slope, the
coefficient of a product has a unique dominant term: its valuation is the sum of the
valuations of the two corresponding coefficients. -/
theorem addValuation_coeff_mul_of_isLeast
    (hc : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hl : IsLeast (supportingFace (fun n => v (coeff n f)) σ c) l)
    (hd : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hl' : IsLeast (supportingFace (fun n => v (coeff n g)) σ d) l') :
    v (coeff (l + l') (f * g)) = v (coeff l f) + v (coeff l' g) :=
  addValuation_coeff_mul_of_unique hc hl.1 hd hl'.1 fun i j hij hi hj => by
    have := hl.2 hi
    have := hl'.2 hj
    omega

/-- At the sum of the greatest contact indices of supporting lines of a common slope, the
coefficient of a product has a unique dominant term: its valuation is the sum of the
valuations of the two corresponding coefficients. -/
theorem addValuation_coeff_mul_of_isGreatest
    (hc : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hu : IsGreatest (supportingFace (fun n => v (coeff n f)) σ c) l)
    (hd : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hu' : IsGreatest (supportingFace (fun n => v (coeff n g)) σ d) l') :
    v (coeff (l + l') (f * g)) = v (coeff l f) + v (coeff l' g) :=
  addValuation_coeff_mul_of_unique hc hu.1 hd hu'.1 fun i j hij hi hj => by
    have := hu.2 hi
    have := hu'.2 hj
    omega

end PowerSeries

namespace Polynomial

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- A polynomial has a supporting line of every slope touching its coefficient heights at a
least contact index, unless all of its coefficient heights are infinite. -/
private theorem exists_isSupportingLine_isLeast (f : R[X]) (hf : (fun n => v (f.coeff n)) ≠ ⊤)
    (σ : ℝ) : ∃ c l, IsSupportingLine (fun n => v (f.coeff n)) σ c ∧
      IsLeast (supportingFace (fun n => v (f.coeff n)) σ c) l := by
  classical
  obtain ⟨c, n, hc, hn⟩ := exists_isSupportingLine_and_mem_supportingFace
    (finite_setOf_addValuation_coeff_ne_top f v) hf σ
  exact ⟨c, Nat.find ⟨n, hn⟩, hc, Nat.find_spec ⟨n, hn⟩, fun _ hm => Nat.find_min' _ hm⟩

/-- Supporting values of coefficient heights add under multiplication of polynomials. When `v`
comes from an absolute value, this is the multiplicativity of Gauss norms at every radius.
No hypothesis is needed: if all coefficient heights of a factor are infinite, both sides
are `⊤`. -/
theorem supportingValue_addValuation_coeff_mul (f g : R[X]) (σ : ℝ) :
    supportingValue (fun n => v ((f * g).coeff n)) σ =
      supportingValue (fun n => v (f.coeff n)) σ +
        supportingValue (fun n => v (g.coeff n)) σ := by
  have hle (n : ℕ) :
      minkowskiSum (fun n => v (f.coeff n)) (fun n => v (g.coeff n)) n ≤
        v ((f * g).coeff n) := by
    simpa only [← coe_mul, coeff_coe] using
      PowerSeries.minkowskiSum_le_addValuation_coeff_mul v (f : PowerSeries R) g n
  -- A factor with only infinite coefficient heights forces the same for the product.
  by_cases hf : (fun n => v (f.coeff n)) = ⊤
  · rw [hf, supportingValue_top, EReal.top_add_of_ne_bot (supportingValue_ne_bot_of_finite
      (finite_setOf_addValuation_coeff_ne_top g v) σ), supportingValue_eq_top_iff, eq_top_iff]
    intro n
    have h := hle n
    rwa [hf, top_minkowskiSum] at h
  by_cases hg : (fun n => v (g.coeff n)) = ⊤
  · rw [hg, supportingValue_top, EReal.add_top_of_ne_bot (supportingValue_ne_bot_of_finite
      (finite_setOf_addValuation_coeff_ne_top f v) σ), supportingValue_eq_top_iff, eq_top_iff]
    intro n
    have h := hle n
    rwa [hg, minkowskiSum_top] at h
  obtain ⟨c, l, hc, hl⟩ := exists_isSupportingLine_isLeast v f hf σ
  obtain ⟨d, l', hd, hl'⟩ := exists_isSupportingLine_isLeast v g hg σ
  -- The sum of the two supporting lines supports the product heights and touches them at
  -- `l + l'`, by the unique dominant term there.
  have hline : IsSupportingLine (fun n => v ((f * g).coeff n)) σ (c + d) :=
    isSupportingLine_iff_forall.mpr fun n =>
      (isSupportingLine_iff_forall.mp (hc.minkowskiSum hd) n).trans (hle n)
  have hmem : l + l' ∈ supportingFace (fun n => v ((f * g).coeff n)) σ (c + d) := by
    have key := PowerSeries.addValuation_coeff_mul_of_isLeast (f := (f : PowerSeries R)) (g := g)
      (by simpa only [coeff_coe] using hc) (by simpa only [coeff_coe] using hl)
      (by simpa only [coeff_coe] using hd) (by simpa only [coeff_coe] using hl')
    have hlc := hl.1
    have hlc' := hl'.1
    rw [mem_supportingFace] at hlc hlc' ⊢
    rw [← coe_mul, coeff_coe, coeff_coe, coeff_coe] at key
    rw [key, hlc, hlc', ← WithTop.coe_add, WithTop.coe_eq_coe, Nat.cast_add]
    ring
  rw [supportingValue_eq_coe_of_mem_supportingFace hline hmem,
    supportingValue_eq_coe_of_mem_supportingFace hc hl.1,
    supportingValue_eq_coe_of_mem_supportingFace hd hl'.1, EReal.coe_add]

/-- The Newton polygon of a product of polynomials is the Minkowski sum of the Newton polygons
of the factors. No hypothesis is needed: if either factor has empty Newton polygon, so does
the product. -/
theorem newtonPolygon_mul (f g : R[X]) :
    (f * g).newtonPolygon v = minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) := by
  have hS (h : R[X]) : supportingValue (h.newtonPolygon v) =
      supportingValue fun n => v (h.coeff n) := by
    rw [newtonPolygon_def]
    exact supportingValue_lowerConvexEnvelope (isAdmissible_addValuation_coeff h v)
  -- Both sides are convex, so it suffices to compare their supporting values.
  have hM := (isConvexSeq_newtonPolygon f v).minkowskiSum (isConvexSeq_newtonPolygon g v)
  funext n
  refine WithTop.toEReal_injective ?_
  rw [← (isConvexSeq_newtonPolygon (f * g) v).iSup_supportingValue_add n,
    ← hM.iSup_supportingValue_add n]
  refine iSup_congr fun σ => congrArg (· + _) ?_
  rw [hS, supportingValue_addValuation_coeff_mul]
  -- A factor with empty Newton polygon makes both sides empty.
  by_cases hf : f.newtonPolygon v = ⊤
  · rw [hf, top_minkowskiSum, supportingValue_top, ← hS, hf, supportingValue_top,
      EReal.top_add_of_ne_bot (supportingValue_ne_bot_of_finite
        (finite_setOf_addValuation_coeff_ne_top g v) σ)]
  by_cases hg : g.newtonPolygon v = ⊤
  · rw [hg, minkowskiSum_top, supportingValue_top, ← hS g, hg, supportingValue_top,
      EReal.add_top_of_ne_bot (supportingValue_ne_bot_of_finite
        (finite_setOf_addValuation_coeff_ne_top f v) σ)]
  rw [supportingValue_minkowskiSum hf hg, hS, hS]

end Polynomial
