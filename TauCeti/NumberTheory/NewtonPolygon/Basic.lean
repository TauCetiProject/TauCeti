/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Order.Interval.Set.Nat
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.Valuation.Basic
public import TauCeti.Analysis.Convex.Sequence.Envelope
public import TauCeti.Analysis.Convex.Sequence.Supporting

/-!
# Newton polygons of polynomials and power series

Given an additive valuation `v` with real values, a polynomial or power series `f` has the
coefficient heights `n ↦ v (coeff n f)`, plotted at the points `(n, v (coeff n f))`, with
height `⊤` at the vanishing coefficients. Its Newton polygon is the lower convex envelope of
these heights. With this orientation slopes increase from left to right, and a slope `m`
corresponds to a nonzero root of valuation `-m`.

The valuation is real valued. A valuation with values in another ordered group `WithTop Γ`
is normalised first by an order-preserving additive embedding `Γ → ℝ`, for example through
`AddValuation.map`.

A polynomial has only finitely many nonzero coefficients, so its heights are always
admissible and its Newton polygon is their lower convex envelope. A power series need
not have admissible heights; its `newtonPolygon` is then the all-infinite fallback of
`TauCeti.lowerConvexEnvelope`, and geometric statements assume admissibility.

## Main definitions

* `PowerSeries.newtonPolygon f v`: the lower convex envelope of the heights
  `n ↦ v (coeff n f)`.
* `Polynomial.newtonPolygon f v`: the same construction for a polynomial; it agrees with
  the Newton polygon of the power series `(f : R⟦X⟧)` by `Polynomial.newtonPolygon_coe`.
  Both take the valuation as an explicit argument rather than through a global instance.

## Main results

* `Polynomial.isLowerConvexEnvelope_newtonPolygon`: the Newton polygon of a polynomial is the
  greatest convex minorant of its coefficient heights.
* `PowerSeries.supportingValue_newtonPolygon` and `Polynomial.supportingValue_newtonPolygon`:
  the Newton polygon has the same supporting values as the coefficient heights.
* `Polynomial.newtonPolygon_eq_top_iff`: the Newton polygon of a polynomial is empty exactly
  when every coefficient has infinite valuation.
* `Polynomial.newtonPolygon_ne_top_iff`: if only zero has infinite valuation (for example
  over a division ring), a nonzero polynomial has a polygon whose finite domain is the
  interval from its order of vanishing at zero to its degree; in particular the polygon is
  nonempty by `Polynomial.newtonPolygon_ne_top_of_ne_zero`.
* `Polynomial.Monic.newtonPolygon_ne_top`: a monic polynomial has a nonempty Newton polygon,
  whatever the valuation.
* `Polynomial.newtonPolygon_natTrailingDegree` and `Polynomial.newtonPolygon_natDegree`:
  the polygon begins at the trailing coefficient and ends at the leading coefficient.
* `Polynomial.ncard_finiteEdges_newtonPolygon`: if only zero has infinite valuation, a
  polynomial of degree `d` and order `a` of vanishing at zero has `d - a` finite unit edges,
  and by `Polynomial.finiteEdges_newtonPolygon_monomial` a monomial has none.
* `PowerSeries.newtonPolygon_smul`, `PowerSeries.newtonPolygon_X_pow_mul`,
  `PowerSeries.newtonPolygon_rescale` and `PowerSeries.newtonPolygon_map`: multiplication by
  a scalar translates the heights, multiplication by `X ^ k` shifts the polygon `k` places,
  the substitution `X ↦ c X` shears it by the valuation of `c`, and an extension of
  coefficients compatible with the valuations preserves it. The corresponding polynomial
  statements are proved as well, with `Polynomial.newtonPolygon_comp_C_mul_X` for the
  substitution `X ↦ c X`.
* `Polynomial.newtonPolygon_reflect` and `Polynomial.newtonPolygon_reverse`: reversing a
  polynomial of degree `d`, or more generally reflecting its coefficients in any `N ≥ d`,
  reflects the Newton polygon by `n ↦ N - n`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4.
-/

public section

open TauCeti

namespace PowerSeries

variable {R S : Type*} [Ring R] [Ring S]

/-- The Newton polygon of a power series `f` with respect to a real additive valuation `v`:
the lower convex envelope of the coefficient heights `n ↦ v (coeff n f)`. If these heights
have no real affine lower bound, it is the all-infinite fallback. -/
noncomputable def newtonPolygon (f : R⟦X⟧) (v : AddValuation R (WithTop ℝ)) :
    ℕ → WithTop ℝ :=
  lowerConvexEnvelope fun n => v (coeff n f)

variable (f : R⟦X⟧) (v : AddValuation R (WithTop ℝ))

/-- The Newton polygon is the lower convex envelope of the coefficient heights. -/
theorem newtonPolygon_def :
    f.newtonPolygon v = lowerConvexEnvelope fun n => v (coeff n f) := (rfl)

/-- The Newton polygon is convex, including the all-infinite fallback. -/
theorem isConvexSeq_newtonPolygon : IsConvexSeq (f.newtonPolygon v) :=
  isConvexSeq_lowerConvexEnvelope _

variable {f v}

/-- For admissible coefficient heights, the Newton polygon is their greatest convex
minorant. -/
theorem isLowerConvexEnvelope_newtonPolygon (hf : IsAdmissible fun n => v (coeff n f)) :
    IsLowerConvexEnvelope (fun n => v (coeff n f)) (f.newtonPolygon v) :=
  isLowerConvexEnvelope_lowerConvexEnvelope hf

/-- For admissible coefficient heights, the Newton polygon lies below every coefficient
point. -/
theorem newtonPolygon_le (hf : IsAdmissible fun n => v (coeff n f)) (n : ℕ) :
    f.newtonPolygon v n ≤ v (coeff n f) :=
  lowerConvexEnvelope_le hf n

/-- A convex sequence lying below every coefficient height lies below the Newton polygon. -/
theorem le_newtonPolygon {H : ℕ → WithTop ℝ} (hH : IsConvexSeq H)
    (hHf : ∀ n, H n ≤ v (coeff n f)) : H ≤ f.newtonPolygon v :=
  le_lowerConvexEnvelope hH hHf

/-- For admissible coefficient heights, the Newton polygon has the same supporting values as
the coefficient heights. -/
theorem supportingValue_newtonPolygon (hf : IsAdmissible fun n => v (coeff n f)) :
    supportingValue (f.newtonPolygon v) = supportingValue fun n => v (coeff n f) :=
  supportingValue_lowerConvexEnvelope hf

variable (v)

/-- The zero power series has the empty Newton polygon. -/
@[simp]
theorem newtonPolygon_zero : (0 : R⟦X⟧).newtonPolygon v = ⊤ := by
  simp only [newtonPolygon_def, map_zero, AddValuation.map_zero]
  exact lowerConvexEnvelope_top

/-- Every point of the Newton polygon before the order of vanishing at zero is infinite. -/
theorem newtonPolygon_eq_top_of_lt_order {n : ℕ} (hn : n < f.order) :
    f.newtonPolygon v n = ⊤ :=
  lowerConvexEnvelope_eq_top_of_forall_le fun i hi => by
    rw [coeff_of_lt_order i (lt_of_le_of_lt (by exact_mod_cast hi) hn), AddValuation.map_zero]

/-- For admissible coefficient heights, the Newton polygon begins at the first nonzero
coefficient. -/
theorem newtonPolygon_eq_of_order_eq {n : ℕ} (hf : IsAdmissible fun n => v (coeff n f))
    (hn : f.order = n) : f.newtonPolygon v n = v (coeff n f) :=
  lowerConvexEnvelope_eq_of_forall_lt hf fun i hi => by
    rw [coeff_of_lt_order i (hn ▸ by exact_mod_cast hi), AddValuation.map_zero]

variable (f)

/-- Multiplying by a scalar translates the Newton polygon by the valuation of the scalar. -/
theorem newtonPolygon_smul (c : R) :
    (c • f).newtonPolygon v = fun n => v c + f.newtonPolygon v n := by
  simp only [newtonPolygon_def, coeff_smul, smul_eq_mul, AddValuation.map_mul]
  exact lowerConvexEnvelope_const_add _ _

/-- Multiplying by a constant translates the Newton polygon by the valuation of the
constant. -/
theorem newtonPolygon_C_mul (c : R) :
    (C c * f).newtonPolygon v = fun n => v c + f.newtonPolygon v n := by
  simp only [newtonPolygon_def, coeff_C_mul, AddValuation.map_mul]
  exact lowerConvexEnvelope_const_add _ _

/-- Multiplying by `X ^ k` shifts the Newton polygon `k` places to the right. -/
theorem newtonPolygon_X_pow_mul (k : ℕ) :
    (X ^ k * f).newtonPolygon v =
      fun n => if k ≤ n then f.newtonPolygon v (n - k) else ⊤ := by
  simp only [newtonPolygon_def, coeff_X_pow_mul', apply_ite v, AddValuation.map_zero]
  exact lowerConvexEnvelope_shift (fun n => v (coeff n f)) k

/-- Substituting `c X` for `X` shears the Newton polygon by the valuation of `c`, provided
that valuation is finite. -/
theorem newtonPolygon_rescale {R : Type*} [CommRing R] (f : R⟦X⟧)
    (v : AddValuation R (WithTop ℝ)) {c : R} (hc : v c ≠ ⊤) :
    (rescale c f).newtonPolygon v = fun n => f.newtonPolygon v n + n • v c := by
  simp only [newtonPolygon_def, coeff_rescale, AddValuation.map_mul, AddValuation.map_pow,
    add_comm (_ • _)]
  exact lowerConvexEnvelope_add_nsmul _ hc

/-- Mapping the coefficients along a ring homomorphism compatible with the valuations
preserves the Newton polygon. -/
theorem newtonPolygon_map (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    (hφ : ∀ x, w (φ x) = v x) : (map φ f).newtonPolygon w = f.newtonPolygon v := by
  simp only [newtonPolygon_def, coeff_map, hφ]

end PowerSeries

namespace Polynomial

variable {R S : Type*} [Ring R] [Ring S]

/-- The Newton polygon of a polynomial `f` with respect to a real additive valuation `v`:
the lower convex envelope of the coefficient heights `n ↦ v (f.coeff n)`. -/
noncomputable def newtonPolygon (f : R[X]) (v : AddValuation R (WithTop ℝ)) :
    ℕ → WithTop ℝ :=
  lowerConvexEnvelope fun n => v (f.coeff n)

variable (f : R[X]) (v : AddValuation R (WithTop ℝ))

/-- The Newton polygon is the lower convex envelope of the coefficient heights. -/
theorem newtonPolygon_def :
    f.newtonPolygon v = lowerConvexEnvelope fun n => v (f.coeff n) := (rfl)

/-- The Newton polygon of a polynomial is that of the corresponding power series. -/
@[simp]
theorem newtonPolygon_coe : (f : PowerSeries R).newtonPolygon v = f.newtonPolygon v := by
  simp only [PowerSeries.newtonPolygon_def, coeff_coe, newtonPolygon_def]

/-- The coefficient heights of a polynomial are admissible: they are infinite beyond the
degree. -/
theorem isAdmissible_addValuation_coeff : IsAdmissible fun n => v (f.coeff n) :=
  isAdmissible_of_forall_gt (p := f.natDegree) fun n hn => by
    rw [coeff_eq_zero_of_natDegree_lt hn, AddValuation.map_zero]

/-- A polynomial has only finitely many coefficients of finite height. -/
theorem finite_setOf_addValuation_coeff_ne_top : {n | v (f.coeff n) ≠ ⊤}.Finite :=
  f.support.finite_toSet.subset fun n hn =>
    mem_support_iff.mpr fun h => hn (by rw [h, AddValuation.map_zero])

/-- The Newton polygon of a polynomial is the greatest convex minorant of its coefficient
heights. -/
theorem isLowerConvexEnvelope_newtonPolygon :
    IsLowerConvexEnvelope (fun n => v (f.coeff n)) (f.newtonPolygon v) :=
  isLowerConvexEnvelope_lowerConvexEnvelope (isAdmissible_addValuation_coeff f v)

/-- The Newton polygon is convex. -/
theorem isConvexSeq_newtonPolygon : IsConvexSeq (f.newtonPolygon v) :=
  isConvexSeq_lowerConvexEnvelope _

/-- The Newton polygon lies below every coefficient point. -/
theorem newtonPolygon_le (n : ℕ) : f.newtonPolygon v n ≤ v (f.coeff n) :=
  lowerConvexEnvelope_le (isAdmissible_addValuation_coeff f v) n

variable {f v} in
/-- A convex sequence lying below every coefficient height lies below the Newton polygon. -/
theorem le_newtonPolygon {H : ℕ → WithTop ℝ} (hH : IsConvexSeq H)
    (hHf : ∀ n, H n ≤ v (f.coeff n)) : H ≤ f.newtonPolygon v :=
  le_lowerConvexEnvelope hH hHf

/-- The Newton polygon has the same supporting values as the coefficient heights. -/
theorem supportingValue_newtonPolygon :
    supportingValue (f.newtonPolygon v) = supportingValue fun n => v (f.coeff n) :=
  supportingValue_lowerConvexEnvelope (isAdmissible_addValuation_coeff f v)

/-- The zero polynomial has the empty Newton polygon. -/
@[simp]
theorem newtonPolygon_zero : (0 : R[X]).newtonPolygon v = ⊤ := by
  simp only [newtonPolygon_def, coeff_zero, AddValuation.map_zero]
  exact lowerConvexEnvelope_top

/-- The Newton polygon of a polynomial is empty exactly when every coefficient has infinite
valuation. -/
theorem newtonPolygon_eq_top_iff : f.newtonPolygon v = ⊤ ↔ ∀ n, v (f.coeff n) = ⊤ := by
  refine ⟨fun h n => top_le_iff.mp ((congrFun h n).symm.trans_le (newtonPolygon_le f v n)),
    fun h => ?_⟩
  rw [newtonPolygon_def, funext h]
  exact lowerConvexEnvelope_top

/-! ### Elementary operations -/

/-- Multiplying by a scalar translates the Newton polygon by the valuation of the scalar. -/
theorem newtonPolygon_smul (c : R) :
    (c • f).newtonPolygon v = fun n => v c + f.newtonPolygon v n := by
  simp only [newtonPolygon_def, coeff_smul, smul_eq_mul, AddValuation.map_mul]
  exact lowerConvexEnvelope_const_add _ _

/-- Multiplying by a constant translates the Newton polygon by the valuation of the
constant. -/
theorem newtonPolygon_C_mul (c : R) :
    (C c * f).newtonPolygon v = fun n => v c + f.newtonPolygon v n := by
  simp only [newtonPolygon_def, coeff_C_mul, AddValuation.map_mul]
  exact lowerConvexEnvelope_const_add _ _

/-- Multiplying by `X ^ k` shifts the Newton polygon `k` places to the right. -/
theorem newtonPolygon_X_pow_mul (k : ℕ) :
    (X ^ k * f).newtonPolygon v =
      fun n => if k ≤ n then f.newtonPolygon v (n - k) else ⊤ := by
  simp only [newtonPolygon_def, coeff_X_pow_mul', apply_ite v, AddValuation.map_zero]
  exact lowerConvexEnvelope_shift (fun n => v (f.coeff n)) k

/-- Reflecting the coefficients in an index `N` at least the degree reflects the Newton polygon
in `N`: its point at `n ≤ N` moves to `N - n`. -/
theorem newtonPolygon_reflect {N : ℕ} (hN : f.natDegree ≤ N) :
    (reflect N f).newtonPolygon v =
      fun n => if n ≤ N then f.newtonPolygon v (N - n) else ⊤ := by
  have hcoeff : (fun n => v ((reflect N f).coeff n)) =
      fun n => if n ≤ N then v (f.coeff (N - n)) else ⊤ := by
    funext n
    split_ifs with hn
    · rw [coeff_reflect, revAt_le hn]
    · rw [coeff_reflect, revAt_eq_self_of_lt (not_le.mp hn),
        coeff_eq_zero_of_natDegree_lt (hN.trans_lt (not_le.mp hn)), AddValuation.map_zero]
  rw [newtonPolygon_def, hcoeff, newtonPolygon_def]
  exact lowerConvexEnvelope_reflect (a := fun n => v (f.coeff n)) fun n hn => by
    rw [coeff_eq_zero_of_natDegree_lt (hN.trans_lt hn), AddValuation.map_zero]

/-- Reversing a polynomial of degree `d` reflects its Newton polygon by `n ↦ d - n`. -/
theorem newtonPolygon_reverse :
    f.reverse.newtonPolygon v =
      fun n => if n ≤ f.natDegree then f.newtonPolygon v (f.natDegree - n) else ⊤ :=
  f.newtonPolygon_reflect v le_rfl

/-- Substituting `c X` for `X` shears the Newton polygon by the valuation of `c`, provided
that valuation is finite. -/
theorem newtonPolygon_comp_C_mul_X {c : R} (hc : v c ≠ ⊤) :
    (f.comp (C c * X)).newtonPolygon v = fun n => f.newtonPolygon v n + n • v c := by
  simp only [newtonPolygon_def, comp_C_mul_X_coeff, AddValuation.map_mul, AddValuation.map_pow]
  exact lowerConvexEnvelope_add_nsmul _ hc

/-- Mapping the coefficients along a ring homomorphism compatible with the valuations
preserves the Newton polygon. -/
theorem newtonPolygon_map (φ : R →+* S) {w : AddValuation S (WithTop ℝ)}
    (hφ : ∀ x, w (φ x) = v x) : (f.map φ).newtonPolygon w = f.newtonPolygon v := by
  simp only [newtonPolygon_def, coeff_map, hφ]

/-! ### Endpoints and finite domain -/

/-- Every point of the Newton polygon before the order of vanishing at zero is infinite. -/
theorem newtonPolygon_eq_top_of_lt_natTrailingDegree {n : ℕ} (hn : n < f.natTrailingDegree) :
    f.newtonPolygon v n = ⊤ :=
  lowerConvexEnvelope_eq_top_of_forall_le fun i hi => by
    rw [coeff_eq_zero_of_lt_natTrailingDegree (lt_of_le_of_lt hi hn), AddValuation.map_zero]

/-- Every point of the Newton polygon beyond the degree is infinite. -/
theorem newtonPolygon_eq_top_of_natDegree_lt {n : ℕ} (hn : f.natDegree < n) :
    f.newtonPolygon v n = ⊤ :=
  lowerConvexEnvelope_eq_top_of_forall_ge fun k hk => by
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hn hk), AddValuation.map_zero]

/-- The Newton polygon begins at the trailing coefficient. -/
@[simp]
theorem newtonPolygon_natTrailingDegree :
    f.newtonPolygon v f.natTrailingDegree = v f.trailingCoeff :=
  lowerConvexEnvelope_eq_of_forall_lt (isAdmissible_addValuation_coeff f v) fun i hi => by
    rw [coeff_eq_zero_of_lt_natTrailingDegree hi, AddValuation.map_zero]

/-- The Newton polygon ends at the leading coefficient. -/
@[simp]
theorem newtonPolygon_natDegree : f.newtonPolygon v f.natDegree = v f.leadingCoeff :=
  lowerConvexEnvelope_eq_of_forall_gt fun k hk => by
    rw [coeff_eq_zero_of_natDegree_lt hk, AddValuation.map_zero]

/-- If only zero has infinite valuation, the finite domain of the Newton polygon of a nonzero
polynomial runs from its order of vanishing at zero to its degree. Over a division ring the
hypothesis on `v` is `AddValuation.top_iff`. -/
theorem newtonPolygon_ne_top_iff (hv : ∀ x, v x = ⊤ → x = 0) {f : R[X]} (hf : f ≠ 0) {n : ℕ} :
    f.newtonPolygon v n ≠ ⊤ ↔ f.natTrailingDegree ≤ n ∧ n ≤ f.natDegree := by
  rw [newtonPolygon_def, lowerConvexEnvelope_ne_top_iff (isAdmissible_addValuation_coeff f v)]
  refine ⟨fun ⟨i, hin, k, hnk, hi, hk⟩ =>
    ⟨(natTrailingDegree_le_of_ne_zero fun h => hi (h ▸ v.map_zero)).trans hin,
      hnk.trans (le_natDegree_of_ne_zero fun h => hk (h ▸ v.map_zero))⟩,
    fun ⟨hn, hn'⟩ => ⟨_, hn, _, hn', ?_, ?_⟩⟩
  · exact mt (hv _) (trailingCoeff_nonzero_iff_nonzero.mpr hf)
  · exact mt (hv _) (leadingCoeff_ne_zero.mpr hf)

variable {f v} in
/-- If only zero has infinite valuation, a nonzero polynomial has a nonempty Newton polygon.
Over a division ring the hypothesis on `v` is `AddValuation.top_iff`. -/
theorem newtonPolygon_ne_top_of_ne_zero (hv : ∀ x, v x = ⊤ → x = 0) (hf : f ≠ 0) :
    f.newtonPolygon v ≠ ⊤ := fun h =>
  leadingCoeff_ne_zero.mpr hf (hv _ ((newtonPolygon_eq_top_iff f v).mp h f.natDegree))

variable {f} in
/-- A monic polynomial has a nonempty Newton polygon: its leading coefficient has valuation
zero. -/
theorem Monic.newtonPolygon_ne_top (hf : f.Monic) : f.newtonPolygon v ≠ ⊤ := fun h => by
  simpa [hf.leadingCoeff] using (newtonPolygon_eq_top_iff f v).mp h f.natDegree

/-- If only zero has infinite valuation, the finite unit edges of the Newton polygon of a
polynomial are those between its order of vanishing at zero and its degree. -/
theorem finiteEdges_newtonPolygon (hv : ∀ x, v x = ⊤ → x = 0) :
    finiteEdges (f.newtonPolygon v) = Set.Ico f.natTrailingDegree f.natDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · ext n
    simp
  ext n
  simp only [mem_finiteEdges, newtonPolygon_ne_top_iff v hv hf, Set.mem_Ico]
  omega

/-- If only zero has infinite valuation, a polynomial of degree `d` and order of vanishing `a`
at zero has exactly `d - a` finite unit edges. -/
theorem ncard_finiteEdges_newtonPolygon (hv : ∀ x, v x = ⊤ → x = 0) :
    (finiteEdges (f.newtonPolygon v)).ncard = f.natDegree - f.natTrailingDegree := by
  rw [finiteEdges_newtonPolygon f v hv, Set.ncard_Ico_nat]

/-- A monomial, in particular a constant, has no finite unit edges. -/
theorem finiteEdges_newtonPolygon_monomial (k : ℕ) (c : R) :
    finiteEdges ((monomial k c).newtonPolygon v) = ∅ := by
  rcases eq_or_ne c 0 with rfl | hc
  · ext n
    simp
  refine Set.eq_empty_of_forall_notMem fun n hn => ?_
  obtain ⟨hn, hn'⟩ := mem_finiteEdges.mp hn
  rcases lt_or_ge n k with h | h
  · exact hn (newtonPolygon_eq_top_of_lt_natTrailingDegree _ v
      (by rwa [natTrailingDegree_monomial hc]))
  · exact hn' (newtonPolygon_eq_top_of_natDegree_lt _ v
      (by rw [natDegree_monomial_eq k hc]; omega))

end Polynomial
