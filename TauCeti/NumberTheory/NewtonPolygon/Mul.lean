/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Minkowski.SlopeData
public import TauCeti.NumberTheory.NewtonPolygon.Slopes
import Mathlib.Tactic.LinearCombination

/-!
# Newton polygons of products

The Newton polygon of a product of polynomials is the Minkowski sum of the Newton polygons of
the factors, given by the min-convolution `TauCeti.minkowskiSum`. When both Newton polygons are
nonempty, for example when both factors are nonzero over a field, the finite slopes of the
product are those of the two factors together. These are the identities from which the slopes
of a split polynomial are read off its linear factors.

One inequality is the ultrametric inequality for the coefficients of a product, and holds for
power series with admissible coefficient heights. For the other, fix a slope `σ` and take the
first index at which the coefficient heights of each factor touch their supporting line of
slope `σ`. At the sum of these two indices the coefficient of the product has a unique dominant
term, so its valuation is the sum of the two valuations. Hence the supporting values of the
product are the sums of the supporting values of the factors, and a convex sequence is
determined by its supporting values.

## Main results

* `PowerSeries.addValuation_coeff_mul_eq_add_of_isLeast`: at the sum of the first contact
  indices of supporting lines of a common slope, the valuation of the coefficient of a product
  is the sum of the valuations of the two coefficients;
  `PowerSeries.addValuation_coeff_mul_eq_add_of_lt` is the general unique-dominant-term form.
* `PowerSeries.minkowskiSum_newtonPolygon_le_newtonPolygon_mul`: for admissible coefficient
  heights, the Minkowski sum of the Newton polygons of two power series lies below the Newton
  polygon of their product.
* `Polynomial.newtonPolygon_mul`: the Newton polygon of a product of polynomials is the
  Minkowski sum of the Newton polygons of the factors. No hypothesis is needed: if either
  factor has the empty polygon, so does the product.
* `Polynomial.newtonSlopes_mul`: if both factors have nonempty Newton polygons, the finite
  slope multiset of the product is the sum of the finite slope multisets of the factors.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
* K. S. Kedlaya, [*Newton polygons*](https://kskedlaya.org/18.787/newton-poly.pdf),
  MIT 18.787, fall 2007, §§1–2. Kedlaya plots coefficient points at negative indices; our
  convention uses positive indices, so the slopes have the opposite sign.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §3.
-/

public section

open TauCeti

namespace PowerSeries

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ)) {f g : R⟦X⟧}

/-- The unique dominant term of a coefficient of a product. Suppose the coefficient heights of
`f` and `g` touch supporting lines of a common slope `σ` at `i` and `j`, and every other split
`p + q = i + j` has `p` or `q` strictly above its line. Then the valuation of the coefficient of
`f * g` at `i + j` is the sum of the valuations of the coefficients of `f` at `i` and of `g`
at `j`. -/
theorem addValuation_coeff_mul_eq_add_of_lt {σ c d : ℝ} {i j : ℕ}
    (hf : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hi : i ∈ supportingFace (fun n => v (coeff n f)) σ c)
    (hg : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hj : j ∈ supportingFace (fun n => v (coeff n g)) σ d)
    (hsplit : ∀ p q, p + q = i + j → p ≠ i →
      ((c + σ * p : ℝ) : WithTop ℝ) < v (coeff p f) ∨
        ((d + σ * q : ℝ) : WithTop ℝ) < v (coeff q g)) :
    v (coeff (i + j) (f * g)) = v (coeff i f) + v (coeff j g) := by
  simp only [mem_supportingFace] at hi hj
  have hmem : (i, j) ∈ Finset.antidiagonal (i + j) := Finset.mem_antidiagonal.mpr rfl
  rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem, ← AddValuation.map_mul]
  refine AddValuation.map_add_eq_of_lt_left v ?_
  rw [AddValuation.map_mul, hi, hj, ← WithTop.coe_add]
  refine AddValuation.map_lt_sum v WithTop.coe_ne_top fun x hx => ?_
  obtain ⟨hxij, hx⟩ := Finset.mem_erase.mp hx
  have hpq := Finset.mem_antidiagonal.mp hx
  have hp : x.1 ≠ i := fun h => hxij (Prod.ext h (by omega))
  have hline : (c + σ * i) + (d + σ * j) = (c + σ * x.1) + (d + σ * x.2) := by
    have hcast : (x.1 : ℝ) + x.2 = i + j := by exact_mod_cast hpq
    linear_combination (-σ) * hcast
  rw [AddValuation.map_mul, hline, WithTop.coe_add]
  rcases hsplit x.1 x.2 hpq hp with h | h
  · exact WithTop.add_lt_add_of_lt_of_le WithTop.coe_ne_top h
      (isSupportingLine_iff_forall.mp hg x.2)
  · exact WithTop.add_lt_add_of_le_of_lt WithTop.coe_ne_top
      (isSupportingLine_iff_forall.mp hf x.1) h

/-- The valuation of the coefficient of a product at the sum of the first contact indices.
If `i` and `j` are the least indices at which the coefficient heights of `f` and `g` touch
supporting lines of a common slope, then the valuation of the coefficient of `f * g` at `i + j`
is the sum of the valuations of the coefficients of `f` at `i` and of `g` at `j`. -/
theorem addValuation_coeff_mul_eq_add_of_isLeast {σ c d : ℝ} {i j : ℕ}
    (hf : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hi : IsLeast (supportingFace (fun n => v (coeff n f)) σ c) i)
    (hg : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hj : IsLeast (supportingFace (fun n => v (coeff n g)) σ d) j) :
    v (coeff (i + j) (f * g)) = v (coeff i f) + v (coeff j g) := by
  refine addValuation_coeff_mul_eq_add_of_lt v hf hi.1 hg hj.1 fun p q hpq hp => ?_
  rcases lt_or_gt_of_ne hp with hp | hp
  · exact .inl <| (isSupportingLine_iff_forall.mp hf p).lt_of_ne fun h => by
      have := hi.2 (mem_supportingFace.mpr h.symm)
      omega
  · exact .inr <| (isSupportingLine_iff_forall.mp hg q).lt_of_ne fun h => by
      have := hj.2 (mem_supportingFace.mpr h.symm)
      omega

/-- For admissible coefficient heights, the Minkowski sum of the Newton polygons of two power
series lies below the Newton polygon of their product. -/
theorem minkowskiSum_newtonPolygon_le_newtonPolygon_mul
    (hf : IsAdmissible fun n => v (coeff n f)) (hg : IsAdmissible fun n => v (coeff n g)) :
    minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) ≤ (f * g).newtonPolygon v :=
  le_newtonPolygon ((isConvexSeq_newtonPolygon f v).minkowskiSum (isConvexSeq_newtonPolygon g v))
    fun n => by
      rw [coeff_mul]
      refine AddValuation.map_le_sum v fun x hx => ?_
      rw [AddValuation.map_mul]
      exact (minkowskiSum_le_add_of_add_eq (Finset.mem_antidiagonal.mp hx)).trans
        (add_le_add (newtonPolygon_le hf _) (newtonPolygon_le hg _))

end PowerSeries

namespace Polynomial

variable {R : Type*} [Ring R] (f g : R[X]) (v : AddValuation R (WithTop ℝ))

/-- A polynomial with a nonempty Newton polygon has a supporting line of each slope, touching
its coefficient heights at a least index. -/
private theorem exists_isSupportingLine_isLeast_coeff_coe (hf : f.newtonPolygon v ≠ ⊤)
    (σ : ℝ) : ∃ (c : ℝ) (i : ℕ),
      IsSupportingLine (fun n => v (PowerSeries.coeff n (f : PowerSeries R))) σ c ∧
        IsLeast (supportingFace (fun n => v (PowerSeries.coeff n (f : PowerSeries R))) σ c) i := by
  refine exists_isSupportingLine_isLeast_supportingFace ?_ ?_ σ
  · refine (Set.finite_Iic f.natDegree).subset fun n hn => Set.mem_Iic.mpr ?_
    refine le_of_not_gt fun h => hn ?_
    rw [coeff_coe, coeff_eq_zero_of_natDegree_lt h, AddValuation.map_zero]
  · obtain ⟨n, hn⟩ := not_forall.mp (mt (newtonPolygon_eq_top_iff f v).mpr hf)
    exact ⟨n, by rwa [Set.mem_ofPred_eq, coeff_coe]⟩

/-- The Newton polygon of a product of polynomials is the Minkowski sum of the Newton polygons
of the factors. If either factor has the empty Newton polygon, for example if it is zero, so
does the product. -/
theorem newtonPolygon_mul :
    (f * g).newtonPolygon v = minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) := by
  refine le_antisymm ?_ ?_
  swap
  · simpa only [← newtonPolygon_coe, coe_mul] using
      PowerSeries.minkowskiSum_newtonPolygon_le_newtonPolygon_mul v
        (by simpa only [coeff_coe] using isAdmissible_addValuation_coeff f v)
        (by simpa only [coeff_coe] using isAdmissible_addValuation_coeff g v)
  rcases eq_or_ne (f.newtonPolygon v) ⊤ with hf | hf
  · simp [hf]
  rcases eq_or_ne (g.newtonPolygon v) ⊤ with hg | hg
  · simp [hg]
  -- Compare supporting values. Those of a Newton polygon are those of the coefficient heights.
  rw [(isConvexSeq_newtonPolygon _ v).le_iff_forall_supportingValue_le]
  intro σ
  obtain ⟨c, i, hc, hi⟩ := exists_isSupportingLine_isLeast_coeff_coe f v hf σ
  obtain ⟨d, j, hd, hj⟩ := exists_isSupportingLine_isLeast_coeff_coe g v hg σ
  simp only [supportingValue_minkowskiSum hf hg, supportingValue_newtonPolygon, ← coeff_coe,
    coe_mul]
  rw [supportingValue_eq_coe_of_mem_supportingFace hc hi.1,
    supportingValue_eq_coe_of_mem_supportingFace hd hj.1]
  -- The coefficient of the product at the sum of the first contact indices of the factors
  -- lies on the line of slope `σ` and intercept `c + d`.
  rw [← EReal.coe_add]
  refine supportingValue_le_coe_of_mem_supportingFace (n := i + j) ?_
  have hi' := hi.1
  have hj' := hj.1
  simp only [mem_supportingFace] at hi' hj' ⊢
  rw [PowerSeries.addValuation_coeff_mul_eq_add_of_isLeast v hc hi hd hj, hi', hj',
    ← WithTop.coe_add]
  congr 1
  push_cast
  ring

/-- If both factors have nonempty Newton polygons, the finite slope multiset of a product of
polynomials is the sum of the finite slope multisets of the factors. The hypotheses exclude
zero factors: the product `0 * g` has no finite slopes, whatever those of `g`. If only zero
has infinite valuation, a nonzero polynomial has a nonempty Newton polygon by
`Polynomial.newtonPolygon_ne_top_of_ne_zero`. -/
theorem newtonSlopes_mul (hf : f.newtonPolygon v ≠ ⊤) (hg : g.newtonPolygon v ≠ ⊤) :
    (f * g).newtonSlopes v = f.newtonSlopes v + g.newtonSlopes v := by
  obtain ⟨d₁, hd₁⟩ := (exists_finiteSlopeData_heights_eq_iff f v).2 hf
  obtain ⟨d₂, hd₂⟩ := (exists_finiteSlopeData_heights_eq_iff g v).2 hg
  rw [newtonSlopes_eq_slopeMultiset hd₁, newtonSlopes_eq_slopeMultiset hd₂,
    ← FiniteSlopeData.slopeMultiset_minkowskiSum]
  exact newtonSlopes_eq_slopeMultiset
    (by rw [FiniteSlopeData.heights_minkowskiSum, hd₁, hd₂, newtonPolygon_mul])

end Polynomial
