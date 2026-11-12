/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Order
public import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse
public import TauCeti.LinearAlgebra.Matrix.Minor
public import TauCeti.NumberTheory.NewtonPolygon.Roots

/-!
# Hodge lower bounds for Newton polygons and the Fredholm convention

A Hodge lower polygon is given by nondecreasing weights `λ₀ ≤ λ₁ ≤ ⋯` and a starting point: it
is the convex height sequence `H (start + k) = y₀ + ∑_{i < k} λᵢ` on a specified finite interval
or half-line, with height `⊤` elsewhere. These are exactly the heights of
`TauCeti.FiniteSlopeData` and `TauCeti.InfiniteSlopeData`. Since the Newton polygon is the
greatest convex minorant of the coefficient heights, `H` lies below the Newton polygon of `f`
exactly when every coefficient satisfies `H n ≤ v (coeff n f)` (for admissible coefficient
heights in the power-series case). Because `H` is `⊤` outside its domain, this includes the
coefficients there having infinite valuation; the domain is part of the data, and agreement of
endpoints is a separate statement.

For a square matrix `A` the relevant polynomial is the Fredholm determinant
`det (1 - X A) = Matrix.charpolyRev A`, the reverse of the characteristic polynomial. With this
convention:

* its Newton polygon starts at `(0, 0)` and has height `v (det A)` at the dimension `d`;
* its finite slopes are the negatives of the finite slopes of the characteristic polynomial,
  hence, when the characteristic polynomial splits in a valued extension in which only zero has
  infinite valuation, the valuations of the nonzero eigenvalues, counted with multiplicity;
* if only zero has infinite valuation, there are `d - a` of them, where `a` is the order of
  vanishing of the characteristic polynomial at zero: zero eigenvalues lower the degree of
  `det (1 - X A)` and contribute no finite slope, so a singular matrix has a polygon ending
  before `d`.

The comparison with a Hodge polygon of length at least `d` starting at `0` needs only
coefficient bounds in degrees at most `d`. Since the coefficients of `det (1 - X A)` are signed
sums of principal minors, lower bounds for the valuations of the principal minors of each size
by the partial sums of the weights give the comparison. Proving such minor estimates, for
example from row bounds or invariant factors, is a separate matter; here they are hypotheses.

## Main results

* `Polynomial.heights_le_newtonPolygon_iff`, `PowerSeries.heights_le_newtonPolygon_iff`: the
  polygon of finite or infinite slope data lies below a Newton polygon (for admissible
  coefficient heights in the power-series case) exactly when the cumulative slope sums bound the
  coefficient heights on its domain and the coefficients are infinite outside it.
* `Matrix.newtonPolygon_charpolyRev_apply_zero`, `Matrix.newtonPolygon_charpolyRev_apply_card`:
  the endpoint heights `0` and `v (det A)` of the Newton polygon of `det (1 - X A)`.
* `Matrix.newtonSlopes_charpolyRev`, `Matrix.newtonSlopes_charpolyRev_eq_map_roots_map`: the
  finite slopes of `det (1 - X A)` are the negated slopes of the characteristic polynomial, and,
  when it splits in a valued extension where only zero has infinite valuation, the valuations of
  the nonzero eigenvalues.
* `Matrix.card_newtonSlopes_charpolyRev`: if only zero has infinite valuation, their number is
  the dimension minus the multiplicity of the eigenvalue zero.
* `Matrix.heights_le_newtonPolygon_charpolyRev_iff`,
  `Matrix.heights_le_newtonPolygon_charpolyRev_of_principalMinor`: Hodge lower bounds for the
  Newton polygon of `det (1 - X A)` from coefficient bounds or from principal-minor bounds.

## References

* K. S. Kedlaya, [*A little p-adic numerical analysis*](https://kskedlaya.org/18.787/numerical.pdf),
  MIT 18.787 notes (2007), §3.
* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
-/

public section

open Polynomial TauCeti

/-! ### Hodge polygons from slope data -/

namespace Polynomial

variable {R : Type*} [Ring R] {f : R[X]} {v : AddValuation R (WithTop ℝ)}

/-- **Hodge lower bound.** The polygon of finite slope data, with heights
`initialHeight + ∑_{i < k} slope i` at `start + k`, lies below the Newton polygon of a
polynomial exactly when these partial sums bound the corresponding coefficient heights and every
coefficient outside `[start, start + length]` has infinite valuation. -/
theorem heights_le_newtonPolygon_iff {d : FiniteSlopeData ℝ} :
    d.heights ≤ f.newtonPolygon v ↔
      (∀ n, n < d.start ∨ d.start + d.length < n → v (f.coeff n) = ⊤) ∧
        ∀ k ≤ d.length,
          ((d.initialHeight + prefixSum k d.slope : ℝ) : WithTop ℝ) ≤
            v (f.coeff (d.start + k)) := by
  rw [newtonPolygon_def, le_lowerConvexEnvelope_iff (isAdmissible_addValuation_coeff f v)
    d.isConvexSeq_heights, FiniteSlopeData.heights_le_iff]

end Polynomial

namespace PowerSeries

variable {R : Type*} [Ring R] {f : R⟦X⟧} {v : AddValuation R (WithTop ℝ)}

/-- **Hodge lower bound.** For admissible coefficient heights, the polygon of infinite slope
data, with heights `initialHeight + ∑_{i < k} slope i` at `start + k`, lies below the Newton
polygon of a power series exactly when these partial sums bound the corresponding coefficient
heights and every coefficient before `start` has infinite valuation. Without admissibility the
Newton polygon is the all-infinite fallback, and the forward direction fails. -/
theorem heights_le_newtonPolygon_iff {d : InfiniteSlopeData ℝ}
    (hf : IsAdmissible fun n => v (coeff n f)) :
    d.heights ≤ f.newtonPolygon v ↔
      (∀ n < d.start, v (coeff n f) = ⊤) ∧
        ∀ k, ((d.initialHeight + ∑ i ∈ Finset.range k, d.slope i : ℝ) : WithTop ℝ) ≤
          v (coeff (d.start + k) f) := by
  rw [newtonPolygon_def, le_lowerConvexEnvelope_iff hf d.isConvexSeq_heights,
    InfiniteSlopeData.heights_le_iff]

end PowerSeries

/-! ### The Fredholm determinant of a matrix -/

namespace Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] {v : AddValuation R (WithTop ℝ)}
  (A : Matrix ι ι R)

/-- The Newton polygon of `det (1 - X A)` starts at `(0, 0)`. -/
theorem newtonPolygon_charpolyRev_apply_zero : A.charpolyRev.newtonPolygon v 0 = 0 := by
  rw [newtonPolygon_apply_zero, coeff_charpolyRev_zero, AddValuation.map_one]

/-- At the dimension `d`, the Newton polygon of `det (1 - X A)` has height `v (det A)`, the
valuation of its degree-`d` coefficient `(-1) ^ d * det A`. It is infinite when `A` is singular,
or more generally when `det A` has infinite valuation. -/
@[simp]
theorem newtonPolygon_charpolyRev_apply_card :
    A.charpolyRev.newtonPolygon v (Fintype.card ι) = v A.det := by
  rw [newtonPolygon_eq_of_natDegree_le _ _ (natDegree_charpolyRev_le A), coeff_charpolyRev_card,
    AddValuation.map_mul, AddValuation.map_neg_one_pow, zero_add]

/-- The finite slopes of `det (1 - X A)` are the negatives of the finite slopes of the
characteristic polynomial of `A`. -/
theorem newtonSlopes_charpolyRev :
    A.charpolyRev.newtonSlopes v = (A.charpoly.newtonSlopes v).map Neg.neg := by
  rw [← reverse_charpoly, newtonSlopes_reverse]

/-- If only zero has infinite valuation, `det (1 - X A)` has `d - a` finite slopes, counted with
multiplicity, where `d` is the dimension and `a` the order of vanishing of the characteristic
polynomial at zero. The zero eigenvalues contribute no finite slope. -/
theorem card_newtonSlopes_charpolyRev (hv : ∀ x, v x = ⊤ → x = 0) :
    (A.charpolyRev.newtonSlopes v).card = Fintype.card ι - A.charpoly.natTrailingDegree := by
  have : Nontrivial R := ⟨0, 1, fun h => by
    have h1 := v.map_one
    rw [← h, AddValuation.map_zero] at h1
    exact WithTop.top_ne_zero h1⟩
  rw [newtonSlopes_charpolyRev, Multiset.card_map, card_newtonSlopes _ _ hv,
    charpoly_natDegree_eq_dim]

/-- **Fredholm slopes are eigenvalue valuations.** If the characteristic polynomial of `A` splits
in a valued extension `L` whose valuation `w` restricts to `v`, and only zero has infinite
valuation in `L`, the finite slopes of `det (1 - X A)` are the valuations `w α` of the nonzero
eigenvalues `α` of `A` in `L`, counted with multiplicity. -/
theorem newtonSlopes_charpolyRev_eq_map_roots_map {L : Type*} [CommRing L] [IsDomain L]
    [DecidableEq L] {w : AddValuation L (WithTop ℝ)} (hw : ∀ x, w x = ⊤ → x = 0) (φ : R →+* L)
    (hφ : ∀ x, w (φ x) = v x) (hA : (A.charpoly.map φ).Splits) :
    A.charpolyRev.newtonSlopes v =
      ((A.charpoly.map φ).roots.filter (· ≠ 0)).map fun α => (w α).untop₀ := by
  rw [newtonSlopes_charpolyRev, newtonSlopes_eq_map_roots_map hw φ hφ hA, Multiset.map_map]
  exact Multiset.map_congr rfl fun _ _ => neg_neg _

variable {A}

/-- **Hodge lower bound for `det (1 - X A)`.** For finite slope data starting at `0` whose length
is at least the dimension `d`, its polygon lies below the Newton polygon of `det (1 - X A)`
exactly when the partial slope sums bound the coefficient heights in degrees at most `d`. The
degree of `det (1 - X A)` is at most `d`, so no other condition remains. -/
theorem heights_le_newtonPolygon_charpolyRev_iff {d : FiniteSlopeData ℝ} (hstart : d.start = 0)
    (hlength : Fintype.card ι ≤ d.length) :
    d.heights ≤ A.charpolyRev.newtonPolygon v ↔
      ∀ k ≤ Fintype.card ι,
        ((d.initialHeight + prefixSum k d.slope : ℝ) : WithTop ℝ) ≤ v (A.charpolyRev.coeff k) := by
  have htop (n : ℕ) (hn : Fintype.card ι < n) : v (A.charpolyRev.coeff n) = ⊤ := by
    rw [coeff_charpolyRev_eq_zero A hn, AddValuation.map_zero]
  simp only [heights_le_newtonPolygon_iff, hstart, zero_add, Nat.not_lt_zero, false_or]
  refine ⟨fun h k hk => h.2 k (hk.trans hlength),
    fun h => ⟨fun n hn => htop n (hlength.trans_lt hn), fun k _ => ?_⟩⟩
  rcases le_or_gt k (Fintype.card ι) with hk | hk
  · exact h k hk
  · rw [htop k hk]
    exact le_top

/-- **Hodge lower bound from principal minors.** Let finite slope data start at `0` and have
length at least the dimension. If every principal minor of `A` on a set `s` has valuation at least
`initialHeight + ∑_{i < #s} slope i`, then the polygon of the slope data lies below the Newton
polygon of `det (1 - X A)`, whose coefficients are signed sums of principal minors. -/
theorem heights_le_newtonPolygon_charpolyRev_of_principalMinor {d : FiniteSlopeData ℝ}
    (hstart : d.start = 0) (hlength : Fintype.card ι ≤ d.length)
    (hminor : ∀ s : Finset ι,
      ((d.initialHeight + prefixSum s.card d.slope : ℝ) : WithTop ℝ) ≤ v (A.principalMinor s)) :
    d.heights ≤ A.charpolyRev.newtonPolygon v := by
  refine (heights_le_newtonPolygon_charpolyRev_iff hstart hlength).mpr fun k _ => ?_
  rw [coeff_charpolyRev, AddValuation.map_mul, AddValuation.map_neg_one_pow, zero_add]
  refine AddValuation.map_le_sum v fun s hs => ?_
  rw [← principalMinor_def, ← (Finset.mem_powersetCard.mp hs).2]
  exact hminor s

end Matrix
