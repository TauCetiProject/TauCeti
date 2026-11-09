/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Minkowski.SlopeData
public import TauCeti.Analysis.Convex.Sequence.Vertex
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

The same dominant-term argument works for power series at any slope where supporting lines
touch the coefficient heights of both factors, with no convergence hypothesis. There the
supporting values of the product are again the sums of those of the factors. When `v` comes
from an absolute value, this is the multiplicativity of Gauss norms at the corresponding radius.
If such contacts exist at every slope, the Newton polygon of the product is the Minkowski sum
of the Newton polygons of the factors; the polynomial identity is the case of finitely many
finite heights.

At a common slope where both power-series polygons have finite faces, the product has the
finite face whose absolute endpoints are the sums of those of the factors. This local law
requires no convergence hypothesis and does not assert a global product identity outside the
face. Singleton faces are allowed and contribute width zero; endpoints include any initial
order of vanishing.

## Main results

* `PowerSeries.addValuation_coeff_mul_eq_add_of_isLeast` and
  `PowerSeries.addValuation_coeff_mul_eq_add_of_isGreatest`: at the sum of the first,
  respectively last, contact indices of supporting lines of a common slope, the valuation of
  the coefficient of a product is the sum of the valuations of the two coefficients;
  `PowerSeries.addValuation_coeff_mul_eq_add_of_lt` is the general unique-dominant-term form.
* `PowerSeries.minkowskiSum_le_addValuation_coeff_mul`: the coefficient heights of a product
  lie above the Minkowski sum of the coefficient heights of the factors.
* `PowerSeries.supportingValue_addValuation_coeff_mul`: supporting values of coefficient
  heights add under multiplication, at any slope where both factors touch a supporting line.
* `PowerSeries.minkowskiSum_newtonPolygon_le_newtonPolygon_mul`: for admissible coefficient
  heights, the Minkowski sum of the Newton polygons of two power series lies below the Newton
  polygon of their product.
* `PowerSeries.supportingValue_newtonPolygon_mul`: the same additivity for the supporting
  values of the Newton polygons.
* `PowerSeries.newtonPolygon_mul_of_forall_exists_mem_supportingFace`: if the coefficient
  heights of both factors touch supporting lines of every slope, the Newton polygon of the
  product is the Minkowski sum of the Newton polygons of the factors.
* `PowerSeries.isFiniteFace_newtonPolygon_mul`: finite faces at a common slope add under
  multiplication, with both absolute endpoints adding.
* `Polynomial.newtonPolygon_mul`: the Newton polygon of a product of polynomials is the
  Minkowski sum of the Newton polygons of the factors. No hypothesis is needed: if either
  factor has the empty polygon, so does the product.
* `Polynomial.supportingValue_addValuation_coeff_mul`: supporting values of coefficient heights
  add under multiplication of polynomials, at every slope.
* `Polynomial.newtonSlopes_mul`, `Polynomial.newtonSlopes_prod` and
  `Polynomial.newtonSlopes_finprod`: when the factors have nonempty Newton polygons, the finite
  slope multiset of a product of polynomials is the sum of the finite slope multisets of the
  factors.
* `Polynomial.newtonSlopes_le_of_dvd`: the finite slopes of a factor of a polynomial with a
  nonempty Newton polygon are among those of the polynomial, with multiplicity.

## References

* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
* K. S. Kedlaya, [*Newton polygons*](https://kskedlaya.org/18.787/newton-poly.pdf),
  MIT 18.787, fall 2007, §§1–2. Kedlaya plots coefficient points at negative indices; our
  convention uses positive indices, so the slopes have the opposite sign.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
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

/-- The valuation of the coefficient of a product at the sum of the last contact indices.
If `i` and `j` are the greatest indices at which the coefficient heights of `f` and `g` touch
supporting lines of a common slope, then the valuation of the coefficient of `f * g` at `i + j`
is the sum of the valuations of the coefficients of `f` at `i` and of `g` at `j`. -/
theorem addValuation_coeff_mul_eq_add_of_isGreatest {σ c d : ℝ} {i j : ℕ}
    (hf : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hi : IsGreatest (supportingFace (fun n => v (coeff n f)) σ c) i)
    (hg : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hj : IsGreatest (supportingFace (fun n => v (coeff n g)) σ d) j) :
    v (coeff (i + j) (f * g)) = v (coeff i f) + v (coeff j g) := by
  refine addValuation_coeff_mul_eq_add_of_lt v hf hi.1 hg hj.1 fun p q hpq hp => ?_
  rcases lt_or_gt_of_ne hp with hp | hp
  · exact .inr <| (isSupportingLine_iff_forall.mp hg q).lt_of_ne fun h => by
      have := hj.2 (mem_supportingFace.mpr h.symm)
      omega
  · exact .inl <| (isSupportingLine_iff_forall.mp hf p).lt_of_ne fun h => by
      have := hi.2 (mem_supportingFace.mpr h.symm)
      omega

/-- The coefficient heights of a product of power series lie above the Minkowski sum of the
coefficient heights of the factors. -/
theorem minkowskiSum_le_addValuation_coeff_mul (n : ℕ) :
    minkowskiSum (fun n => v (coeff n f)) (fun n => v (coeff n g)) n ≤
      v (coeff n (f * g)) := by
  rw [coeff_mul]
  exact AddValuation.map_le_sum v fun x hx =>
    (minkowskiSum_le_add_of_add_eq (Finset.mem_antidiagonal.mp hx)).trans_eq
      (AddValuation.map_mul v _ _).symm

/-- If supporting lines of a common slope touch the coefficient heights of `f` and `g`, then
the supporting value of the coefficient heights of `f * g` at that slope is the sum of those
of `f` and `g`. When `v` comes from an absolute value, this is the multiplicativity of Gauss
norms at the corresponding radius. -/
theorem supportingValue_addValuation_coeff_mul {σ c d : ℝ} {i j : ℕ}
    (hf : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hi : i ∈ supportingFace (fun n => v (coeff n f)) σ c)
    (hg : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hj : j ∈ supportingFace (fun n => v (coeff n g)) σ d) :
    supportingValue (fun n => v (coeff n (f * g))) σ =
      supportingValue (fun n => v (coeff n f)) σ +
        supportingValue (fun n => v (coeff n g)) σ := by
  -- The sum of the two supporting lines supports the product heights and touches them at the
  -- sum of the least contact indices, by the unique dominant term there.
  have hline : IsSupportingLine (fun n => v (coeff n (f * g))) σ (c + d) :=
    isSupportingLine_iff_forall.mpr fun n =>
      (isSupportingLine_iff_forall.mp (hf.minkowskiSum hg) n).trans
        (minkowskiSum_le_addValuation_coeff_mul v n)
  have hm := isLeast_csInf ⟨i, hi⟩
  have hm' := isLeast_csInf ⟨j, hj⟩
  have hmem : sInf (supportingFace (fun n => v (coeff n f)) σ c) +
      sInf (supportingFace (fun n => v (coeff n g)) σ d) ∈
        supportingFace (fun n => v (coeff n (f * g))) σ (c + d) := by
    have key := addValuation_coeff_mul_eq_add_of_isLeast v hf hm hg hm'
    have hmc := hm.1
    have hmc' := hm'.1
    rw [mem_supportingFace] at hmc hmc' ⊢
    rw [key, hmc, hmc', ← WithTop.coe_add, WithTop.coe_eq_coe, Nat.cast_add]
    ring
  rw [supportingValue_eq_coe_of_mem_supportingFace hline hmem,
    supportingValue_eq_coe_of_mem_supportingFace hf hi,
    supportingValue_eq_coe_of_mem_supportingFace hg hj, EReal.coe_add]

/-- For admissible coefficient heights, the Minkowski sum of the Newton polygons of two power
series lies below the Newton polygon of their product. -/
theorem minkowskiSum_newtonPolygon_le_newtonPolygon_mul
    (hf : IsAdmissible fun n => v (coeff n f)) (hg : IsAdmissible fun n => v (coeff n g)) :
    minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) ≤ (f * g).newtonPolygon v :=
  le_newtonPolygon ((isConvexSeq_newtonPolygon f v).minkowskiSum (isConvexSeq_newtonPolygon g v))
    fun n => (minkowskiSum_mono (newtonPolygon_le hf) (newtonPolygon_le hg) n).trans
      (minkowskiSum_le_addValuation_coeff_mul v n)

/-- If supporting lines of a common slope `σ` touch the coefficient heights of `f` and `g`, then
the supporting value at `σ` of the Newton polygon of `f * g` is the sum of those of the Newton
polygons of `f` and `g`. No convergence hypothesis is needed beyond these two contacts. -/
theorem supportingValue_newtonPolygon_mul {σ c d : ℝ} {i j : ℕ}
    (hf : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hi : i ∈ supportingFace (fun n => v (coeff n f)) σ c)
    (hg : IsSupportingLine (fun n => v (coeff n g)) σ d)
    (hj : j ∈ supportingFace (fun n => v (coeff n g)) σ d) :
    supportingValue ((f * g).newtonPolygon v) σ =
      supportingValue (f.newtonPolygon v) σ + supportingValue (g.newtonPolygon v) σ := by
  have hfg : IsAdmissible fun n => v (coeff n (f * g)) :=
    (hf.minkowskiSum hg).isAdmissible.mono (minkowskiSum_le_addValuation_coeff_mul v)
  rw [supportingValue_newtonPolygon hfg, supportingValue_newtonPolygon hf.isAdmissible,
    supportingValue_newtonPolygon hg.isAdmissible]
  exact supportingValue_addValuation_coeff_mul v hf hi hg hj

/-- If the coefficient heights of `f` touch a supporting line of some slope, the Newton polygon
of `f` is nonempty. -/
private theorem newtonPolygon_ne_top_of_mem_supportingFace {σ c : ℝ} {i : ℕ}
    (hf : IsSupportingLine (fun n => v (coeff n f)) σ c)
    (hi : i ∈ supportingFace (fun n => v (coeff n f)) σ c) : f.newtonPolygon v ≠ ⊤ := by
  intro htop
  have hle := newtonPolygon_le hf.isAdmissible i
  rw [htop, mem_supportingFace.mp hi] at hle
  exact WithTop.coe_ne_top (top_le_iff.mp hle)

/-- The Newton polygon of a product is the Minkowski sum of the Newton polygons of the factors,
provided that at every slope the coefficient heights of each factor touch a supporting line.
This holds for polynomials with nonempty Newton polygons, and for nonzero entire series when the
valuation comes from the norm. Without contact the identity can fail: `1 - X` and the geometric
series `∑ Xⁿ` have product `1`, a single point, while the Minkowski sum of their polygons is a
horizontal half-line. -/
theorem newtonPolygon_mul_of_forall_exists_mem_supportingFace
    (hf : ∀ σ : ℝ, ∃ (c : ℝ) (i : ℕ), IsSupportingLine (fun n => v (coeff n f)) σ c ∧
      i ∈ supportingFace (fun n => v (coeff n f)) σ c)
    (hg : ∀ σ : ℝ, ∃ (d : ℝ) (j : ℕ), IsSupportingLine (fun n => v (coeff n g)) σ d ∧
      j ∈ supportingFace (fun n => v (coeff n g)) σ d) :
    (f * g).newtonPolygon v = minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) := by
  obtain ⟨c₀, i₀, hc₀, hi₀⟩ := hf 0
  obtain ⟨d₀, j₀, hd₀, hj₀⟩ := hg 0
  refine le_antisymm ?_
    (minkowskiSum_newtonPolygon_le_newtonPolygon_mul v hc₀.isAdmissible hd₀.isAdmissible)
  -- Compare supporting values: those of the product are the sums at every slope.
  rw [(isConvexSeq_newtonPolygon _ v).le_iff_forall_supportingValue_le]
  intro σ
  obtain ⟨c, i, hc, hi⟩ := hf σ
  obtain ⟨d, j, hd, hj⟩ := hg σ
  rw [supportingValue_minkowskiSum (newtonPolygon_ne_top_of_mem_supportingFace v hc₀ hi₀)
    (newtonPolygon_ne_top_of_mem_supportingFace v hd₀ hj₀),
    supportingValue_newtonPolygon_mul v hc hi hd hj]

/-- Finite Newton faces at a common slope add under multiplication, with both absolute
endpoints adding. This is a local product law: the polygons need not agree with their
Minkowski sum away from this face. No convergence hypothesis is required. -/
theorem isFiniteFace_newtonPolygon_mul {σ : ℝ} {l u l' u' : ℕ}
    (hf : IsFiniteFace (f.newtonPolygon v) σ l u)
    (hg : IsFiniteFace (g.newtonPolygon v) σ l' u') :
    IsFiniteFace ((f * g).newtonPolygon v) σ (l + l') (u + u') := by
  have hfa : IsAdmissible fun n => v (coeff n f) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top
      (by simpa only [newtonPolygon_def] using hf.left_ne_top)
  have hga : IsAdmissible fun n => v (coeff n g) :=
    isAdmissible_of_lowerConvexEnvelope_ne_top
      (by simpa only [newtonPolygon_def] using hg.left_ne_top)
  have hF := isLowerConvexEnvelope_newtonPolygon hfa
  have hG := isLowerConvexEnvelope_newtonPolygon hga
  obtain ⟨c, hc, hfl, hfu⟩ :=
    hF.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hf
  obtain ⟨d, hd, hgl, hgu⟩ :=
    hG.exists_isSupportingLine_isLeast_isGreatest_of_isFiniteFace hg
  have hcF : IsSupportingLine (f.newtonPolygon v) σ c :=
    isSupportingLine_iff_forall.mpr
      (hF.greatest (isConvexSeq_affine c σ) (isSupportingLine_iff_forall.mp hc))
  have hdG : IsSupportingLine (g.newtonPolygon v) σ d :=
    isSupportingLine_iff_forall.mpr
      (hG.greatest (isConvexSeq_affine d σ) (isSupportingLine_iff_forall.mp hd))
  have hprod : IsAdmissible fun n => v (coeff n (f * g)) :=
    (hc.minkowskiSum hd).isAdmissible.mono (minkowskiSum_le_addValuation_coeff_mul v)
  have hle := minkowskiSum_newtonPolygon_le_newtonPolygon_mul v hfa hga
  -- At either extreme split, the unique dominant coefficient makes the lower bound exact.
  have hend (i j : ℕ)
      (hi : i ∈ supportingFace (fun n => v (coeff n f)) σ c)
      (hj : j ∈ supportingFace (fun n => v (coeff n g)) σ d)
      (hij : v (coeff (i + j) (f * g)) = v (coeff i f) + v (coeff j g)) :
      (f * g).newtonPolygon v (i + j) =
        minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) (i + j) := by
    have hiF := hF.supportingFace_subset hc hi
    have hjG := hG.supportingFace_subset hd hj
    have hfi : f.newtonPolygon v i = v (coeff i f) :=
      (mem_supportingFace.mp hiF).trans (mem_supportingFace.mp hi).symm
    have hgj : g.newtonPolygon v j = v (coeff j g) :=
      (mem_supportingFace.mp hjG).trans (mem_supportingFace.mp hj).symm
    apply le_antisymm ?_ (hle (i + j))
    calc
      (f * g).newtonPolygon v (i + j) ≤ v (coeff (i + j) (f * g)) :=
        newtonPolygon_le hprod _
      _ = f.newtonPolygon v i + g.newtonPolygon v j := by rw [hij, hfi, hgj]
      _ = minkowskiSum (f.newtonPolygon v) (g.newtonPolygon v) (i + j) :=
        (minkowskiSum_add_eq_of_mem_supportingFace hcF hiF hdG hjG).symm
  exact (hf.minkowskiSum hg).of_le_of_eq_endpoints
    (isConvexSeq_newtonPolygon (f * g) v) hle
    (hend l l' hfl.1 hgl.1 (addValuation_coeff_mul_eq_add_of_isLeast v hc hfl hd hgl))
    (hend u u' hfu.1 hgu.1 (addValuation_coeff_mul_eq_add_of_isGreatest v hc hfu hd hgu))

end PowerSeries

namespace Polynomial

section Ring

variable {R : Type*} [Ring R] (f g : R[X]) (v : AddValuation R (WithTop ℝ))

/-- A polynomial with a nonempty Newton polygon has coefficient heights touching a supporting
line of each slope. -/
private theorem exists_isSupportingLine_mem_supportingFace_coeff_coe
    (hf : f.newtonPolygon v ≠ ⊤) (σ : ℝ) : ∃ (c : ℝ) (i : ℕ),
      IsSupportingLine (fun n => v (PowerSeries.coeff n (f : PowerSeries R))) σ c ∧
        i ∈ supportingFace (fun n => v (PowerSeries.coeff n (f : PowerSeries R))) σ c := by
  obtain ⟨c, i, hc, hi⟩ := exists_isSupportingLine_isLeast_supportingFace
    (h := fun n => v (PowerSeries.coeff n (f : PowerSeries R)))
    (by simpa only [coeff_coe] using finite_setOf_addValuation_coeff_ne_top f v)
    (by
      obtain ⟨n, hn⟩ := not_forall.mp (mt (newtonPolygon_eq_top_iff f v).mpr hf)
      exact ⟨n, by rwa [Set.mem_ofPred_eq, coeff_coe]⟩) σ
  exact ⟨c, i, hc, hi.1⟩

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
  simpa only [← newtonPolygon_coe, coe_mul] using
    (PowerSeries.newtonPolygon_mul_of_forall_exists_mem_supportingFace v
      (exists_isSupportingLine_mem_supportingFace_coeff_coe f v hf)
      (exists_isSupportingLine_mem_supportingFace_coeff_coe g v hg)).le

/-- Supporting values of coefficient heights add under multiplication of polynomials. When `v`
comes from an absolute value, this is the multiplicativity of Gauss norms at every radius.
No hypothesis is needed: if all coefficient heights of a factor are infinite, both sides
are `⊤`. -/
theorem supportingValue_addValuation_coeff_mul (σ : ℝ) :
    supportingValue (fun n => v ((f * g).coeff n)) σ =
      supportingValue (fun n => v (f.coeff n)) σ +
        supportingValue (fun n => v (g.coeff n)) σ := by
  have hB (h : R[X]) : supportingValue (h.newtonPolygon v) σ ≠ ⊥ := by
    rw [supportingValue_newtonPolygon]
    exact supportingValue_ne_bot_of_finite (finite_setOf_addValuation_coeff_ne_top h v) σ
  rw [← supportingValue_newtonPolygon (f * g), ← supportingValue_newtonPolygon f,
    ← supportingValue_newtonPolygon g, newtonPolygon_mul,
    supportingValue_minkowskiSum_of_ne_bot (hB f) (hB g)]

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

variable {f g v} in
/-- If `f` has a nonempty Newton polygon, the finite slopes of a factor `g` of `f` are among the
finite slopes of `f`, counted with multiplicity. This holds for every nonzero `f` when only zero
has infinite valuation, by `Polynomial.newtonPolygon_ne_top_of_ne_zero`. -/
theorem newtonSlopes_le_of_dvd (hf : f.newtonPolygon v ≠ ⊤) (hgf : g ∣ f) :
    g.newtonSlopes v ≤ f.newtonSlopes v := by
  obtain ⟨h, rfl⟩ := hgf
  have hg : g.newtonPolygon v ≠ ⊤ := fun hg => hf (by rw [newtonPolygon_mul, hg, top_minkowskiSum])
  have hh : h.newtonPolygon v ≠ ⊤ := fun hh => hf (by rw [newtonPolygon_mul, hh, minkowskiSum_top])
  rw [newtonSlopes_mul _ _ v hg hh]
  exact Multiset.le_add_right _ _

end Ring

section CommRing

variable {ι R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ))

/-- A finite product of polynomials with nonempty Newton polygons has a nonempty Newton polygon. -/
theorem newtonPolygon_ne_top_prod (s : Finset ι) (g : ι → R[X])
    (hg : ∀ i ∈ s, (g i).newtonPolygon v ≠ ⊤) : (∏ i ∈ s, g i).newtonPolygon v ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using monic_one.newtonPolygon_ne_top v
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, newtonPolygon_mul]
    obtain ⟨m, hm⟩ := Function.ne_iff.mp (hg a (Finset.mem_insert_self a s))
    obtain ⟨n, hn⟩ := Function.ne_iff.mp (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))
    intro htop
    exact (minkowskiSum_ne_top_iff.mpr ⟨m, n, rfl, hm, hn⟩) (congrFun htop (m + n))

/-- The finite slope multiset of a finite product of polynomials with nonempty Newton polygons is
the sum of the finite slope multisets of the factors. -/
theorem newtonSlopes_prod (s : Finset ι) (g : ι → R[X])
    (hg : ∀ i ∈ s, (g i).newtonPolygon v ≠ ⊤) :
    (∏ i ∈ s, g i).newtonSlopes v = ∑ i ∈ s, (g i).newtonSlopes v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using newtonSlopes_C v (1 : R)
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, (g i).newtonPolygon v ≠ ⊤ := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      newtonSlopes_mul _ _ v (hg a (Finset.mem_insert_self a s))
        (newtonPolygon_ne_top_prod v s g hs),
      ih hs]

/-- The finite slope multiset of a finitely supported product `∏ᶠ i, g i`, whose nontrivial
factors have nonempty Newton polygons, is the sum of their finite slope multisets. -/
theorem newtonSlopes_finprod (g : ι → R[X]) (hfin : (Function.mulSupport g).Finite)
    (hg : ∀ i ∈ Function.mulSupport g, (g i).newtonPolygon v ≠ ⊤) :
    (∏ᶠ i, g i).newtonSlopes v = ∑ i ∈ hfin.toFinset, (g i).newtonSlopes v := by
  rw [finprod_eq_prod g hfin]
  exact newtonSlopes_prod v hfin.toFinset g fun i hi => hg i (hfin.mem_toFinset.mp hi)

end CommRing

end Polynomial
