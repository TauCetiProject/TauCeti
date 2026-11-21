/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.WellKnown
public import TauCeti.NumberTheory.NewtonPolygon.Mul
public import TauCeti.NumberTheory.Padics.LogGauge

/-!
# Newton polygons of products, sums and polynomials vanishing at zero

Worked examples testing the product, addition and root-counting theorems for Newton polygons
against the standard small cases. Over `ℚ_[p]` the valuation is `TauCeti.padicRealValuation p`,
normalised by `v(p) = 1`; the remaining examples hold for every real additive valuation `v` on a
ring.

* **A product of linear factors.** `(1 - X) (1 - p X)` has the finite slopes `0` and `1`, those
  of its two factors (`Polynomial.newtonSlopes_mul`, `Polynomial.newtonSlopes_one_sub_C_mul_X`).
* **A local product law without a global one.** In `R⟦X⟧`, the geometric series `∑ Xⁿ` and
  `1 - X` have product `1` (`PowerSeries.mk_one_mul_one_sub_eq_one`). The Newton polygon of
  `∑ Xⁿ` is the horizontal half-line of height `0`, so the Minkowski sum of the two polygons is
  that half-line, while the polygon of the product is a single point. The supporting values of
  the product are the sums of those of the factors exactly at the slopes `σ ≤ 0`, which
  correspond to the radii `r ≤ 1` when `v` comes from a norm. At every slope `σ < 0`, where
  `∑ Xⁿ` converges, the finite faces of the factors and of the product are all the single index
  `0`, as the local product law `PowerSeries.isFiniteFace_newtonPolygon_mul` requires.
* **Sums.** The Newton polygon of `1 + X ^ 2` has height `0` at the index `1`, where both `1` and
  `X ^ 2` have the coefficient `0`. So the pointwise minimum of the Newton polygons of `1` and
  `X ^ 2`, which is `⊤` at the index `1`, is not a lower bound for the polygon of their sum; its
  lower convex envelope is, and here it equals that polygon, the equality case of
  `Polynomial.lowerConvexEnvelope_inf_le_newtonPolygon_add`.
* **Roots at zero.** `X ^ 2 (1 - p X)` has the roots `0, 0, p⁻¹` but the single finite slope `1`:
  the double root `0` contributes no slope, and the finite slope is the negated valuation of the
  one nonzero root, as in `Polynomial.newtonSlopes_eq_map_roots`.

## References

* K. S. Kedlaya, [*Newton polygons*](https://kskedlaya.org/18.787/newton-poly.pdf),
  MIT 18.787, fall 2007, §§1–3. Kedlaya plots coefficient points at negative indices; our
  convention uses positive indices, so the slopes have the opposite sign.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1, Proposition 1.
-/

public section

open TauCeti

namespace TauCeti.NewtonPolygonProductExample

/-- The heights `0` on `[0, k]` and `⊤` beyond form a convex sequence. -/
private theorem isConvexSeq_ite_le (k : ℕ) :
    IsConvexSeq fun n : ℕ => if n ≤ k then (0 : WithTop ℝ) else ⊤ := by
  simpa using isConvexSeq_affine_ite (s := Set.Iic k) Set.ordConnected_Iic 0 0

section LinearFactors

open Polynomial

variable {p : ℕ} [Fact p.Prime]

private theorem p_ne_zero : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero

/-- Over `ℚ_[p]`, `1 - p X` is a nonzero multiple of `X - p⁻¹`. -/
private theorem one_sub_p_X_eq :
    (1 - C (p : ℚ_[p]) * X : ℚ_[p][X]) = C (-(p : ℚ_[p])) * (X - C (p : ℚ_[p])⁻¹) := by
  rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ p_ne_zero, C_neg, C_neg, C_1, neg_mul]
  ring

/-- Over `ℚ_[p]`, `1 - p X` has the single finite slope `1`. -/
private theorem newtonSlopes_one_sub_p_X :
    (1 - C (p : ℚ_[p]) * X : ℚ_[p][X]).newtonSlopes (padicRealValuation p) = {1} := by
  rw [newtonSlopes_one_sub_C_mul_X _ (by simp), padicRealValuation_p, WithTop.untop₀_one]

/-- `1 - c X` is nonzero, its constant coefficient being `1`. -/
private theorem one_sub_C_mul_X_ne_zero (c : ℚ_[p]) : (1 - C c * X : ℚ_[p][X]) ≠ 0 :=
  fun h => by simpa using congrArg (·.coeff 0) h

/-- Over `ℚ_[p]`, `(1 - X) (1 - p X)` has the finite slopes `0` and `1`. -/
theorem newtonSlopes_one_sub_X_mul_one_sub_p_X :
    ((1 - X) * (1 - C (p : ℚ_[p]) * X) : ℚ_[p][X]).newtonSlopes (padicRealValuation p) =
      {0, 1} := by
  have hv : ∀ x, padicRealValuation p x = ⊤ → x = 0 := fun _ => (padicRealValuation p).top_iff.mp
  have h₁ : (1 - X : ℚ_[p][X]) = 1 - C 1 * X := by rw [C_1, one_mul]
  rw [h₁, newtonSlopes_mul _ _ _ (newtonPolygon_ne_top_of_ne_zero hv (one_sub_C_mul_X_ne_zero 1))
      (newtonPolygon_ne_top_of_ne_zero hv (one_sub_C_mul_X_ne_zero _)),
    newtonSlopes_one_sub_C_mul_X _ (by simp), newtonSlopes_one_sub_p_X, AddValuation.map_one,
    WithTop.untop₀_zero]
  rfl

end LinearFactors

section GeometricSeries

open PowerSeries

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- The Newton polygon of the geometric series `∑ Xⁿ` is the horizontal half-line of height
`0`. -/
theorem newtonPolygon_mk_one : (mk 1 : R⟦X⟧).newtonPolygon v = 0 := by
  have h : (fun n => v (coeff n (mk 1 : R⟦X⟧))) = fun n : ℕ => ((0 + 0 * n : ℝ) : WithTop ℝ) := by
    funext n
    simp
  rw [newtonPolygon_def, h, (isConvexSeq_affine 0 0).lowerConvexEnvelope_eq]
  funext n
  simp

/-- The Newton polygon of `1 - X` is the horizontal segment of height `0` on `[0, 1]`. -/
theorem newtonPolygon_one_sub_X :
    (1 - X : R⟦X⟧).newtonPolygon v = fun n => if n ≤ 1 then 0 else ⊤ := by
  have h : (fun n => v (coeff n (1 - X : R⟦X⟧))) = fun n => if n ≤ 1 then 0 else ⊤ := by
    funext n
    rcases n with _ | _ | n <;> simp [coeff_one, coeff_X]
  rw [newtonPolygon_def, h, (isConvexSeq_ite_le 1).lowerConvexEnvelope_eq]

/-- The Newton polygon of `1` is the single point `(0, 0)`. -/
private theorem newtonPolygon_one :
    (1 : R⟦X⟧).newtonPolygon v = fun n => if n ≤ 0 then 0 else ⊤ := by
  have h : (fun n => v (coeff n (1 : R⟦X⟧))) = fun n => if n ≤ 0 then 0 else ⊤ := by
    funext n
    rcases n with _ | n <;> simp [coeff_one]
  rw [newtonPolygon_def, h, (isConvexSeq_ite_le 0).lowerConvexEnvelope_eq]

/-- The Minkowski sum of the Newton polygons of `∑ Xⁿ` and `1 - X` is the horizontal half-line of
height `0`. -/
theorem minkowskiSum_newtonPolygon_mk_one_newtonPolygon_one_sub_X :
    minkowskiSum ((mk 1 : R⟦X⟧).newtonPolygon v) ((1 - X : R⟦X⟧).newtonPolygon v) = 0 := by
  rw [newtonPolygon_mk_one, newtonPolygon_one_sub_X]
  funext n
  refine le_antisymm ?_ (le_minkowskiSum_iff.mpr fun i j _ => ?_)
  · simpa using minkowskiSum_add_le (0 : ℕ → WithTop ℝ) (fun n => if n ≤ 1 then 0 else ⊤) n 0
  · split_ifs <;> simp

/-- At a slope `σ < 0` the Newton polygon of `∑ Xⁿ` has the finite face `{0}`. -/
theorem isFiniteFace_newtonPolygon_mk_one {σ : ℝ} (hσ : σ < 0) :
    IsFiniteFace ((mk 1 : R⟦X⟧).newtonPolygon v) σ 0 0 := by
  rw [newtonPolygon_mk_one]
  refine isFiniteFace_iff.mpr ⟨le_rfl, 0,
    isSupportingLine_iff_forall.mpr fun n => WithTop.coe_le_coe.mpr ?_, Set.ext fun n => ?_⟩
  · nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · simp [eq_comm (a := (0 : WithTop ℝ)), hσ.ne]

/-- At a slope `σ < 0` the Newton polygon of `1 - X` has the finite face `{0}`. -/
theorem isFiniteFace_newtonPolygon_one_sub_X {σ : ℝ} (hσ : σ < 0) :
    IsFiniteFace ((1 - X : R⟦X⟧).newtonPolygon v) σ 0 0 := by
  rw [newtonPolygon_one_sub_X]
  refine isFiniteFace_iff.mpr
    ⟨le_rfl, 0, isSupportingLine_iff_forall.mpr fun n => ?_, Set.ext fun n => ?_⟩
  · rcases n with _ | _ | n
    · simp
    · simpa using hσ.le
    · simp
  · rcases n with _ | _ | n
    · simp
    · simpa [eq_comm (a := (0 : WithTop ℝ))] using hσ.ne
    · refine iff_of_false (fun h => ?_) (by simp)
      simp only [mem_supportingFace, show ¬n + 1 + 1 ≤ 1 by omega, ↓reduceIte] at h
      exact WithTop.top_ne_coe h

end GeometricSeries

section GeometricSeriesProduct

open PowerSeries

variable {R : Type*} [CommRing R] (v : AddValuation R (WithTop ℝ))

/-- **No global product law.** The Newton polygon of `(∑ Xⁿ) (1 - X) = 1`, a single point, is not
the Minkowski sum of the Newton polygons of the factors, a horizontal half-line. -/
theorem newtonPolygon_mk_one_mul_one_sub_X_ne_minkowskiSum :
    (mk 1 * (1 - X) : R⟦X⟧).newtonPolygon v ≠
      minkowskiSum ((mk 1 : R⟦X⟧).newtonPolygon v) ((1 - X : R⟦X⟧).newtonPolygon v) := by
  rw [minkowskiSum_newtonPolygon_mk_one_newtonPolygon_one_sub_X, mk_one_mul_one_sub_eq_one,
    newtonPolygon_one]
  intro h
  simpa using congrFun h 1

/-- **The local product law.** The supporting values of the Newton polygon of `(∑ Xⁿ) (1 - X)` are
the sums of those of the factors exactly at the slopes `σ ≤ 0`. At a slope `σ > 0` the supporting
value of `∑ Xⁿ` is `⊥`: no line of positive slope lies below its constant heights. -/
theorem supportingValue_newtonPolygon_mk_one_mul_one_sub_X_eq_add_iff (σ : ℝ) :
    supportingValue ((mk 1 * (1 - X) : R⟦X⟧).newtonPolygon v) σ =
        supportingValue ((mk 1 : R⟦X⟧).newtonPolygon v) σ +
          supportingValue ((1 - X : R⟦X⟧).newtonPolygon v) σ ↔ σ ≤ 0 := by
  have h₁ : supportingValue ((mk 1 * (1 - X) : R⟦X⟧).newtonPolygon v) σ = 0 := by
    rw [mk_one_mul_one_sub_eq_one, newtonPolygon_one]
    refine supportingValue_eq_coe_of_mem_supportingFace (c := 0)
      (isSupportingLine_iff_forall.mpr fun n => ?_) (n := 0) (by simp)
    rcases n with _ | n <;> simp
  rw [h₁, newtonPolygon_mk_one, newtonPolygon_one_sub_X]
  constructor
  · intro h
    by_contra hσ
    rw [not_le] at hσ
    have hbot : supportingValue (0 : ℕ → WithTop ℝ) σ = ⊥ := by
      refine supportingValue_eq_bot_iff.mpr fun c => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt (-c / σ)
      refine ⟨n, WithTop.coe_lt_coe.mpr ?_⟩
      rw [div_lt_iff₀ hσ] at hn
      linarith
    rw [hbot, EReal.bot_add] at h
    exact EReal.zero_ne_bot h
  · intro hσ
    have hs₁ : supportingValue (0 : ℕ → WithTop ℝ) σ = 0 :=
      supportingValue_eq_coe_of_mem_supportingFace (c := 0) (isSupportingLine_iff_forall.mpr
        fun n => WithTop.coe_le_coe.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
        (n := 0) (by simp)
    have hs₂ : supportingValue (fun n : ℕ => if n ≤ 1 then (0 : WithTop ℝ) else ⊤) σ = 0 := by
      refine supportingValue_eq_coe_of_mem_supportingFace (c := 0)
        (isSupportingLine_iff_forall.mpr fun n => ?_) (n := 0) (by simp)
      rcases n with _ | _ | n
      · simp
      · simpa using hσ
      · simp
    rw [hs₁, hs₂, add_zero]

/-- At a slope `σ < 0` the local product law gives the Newton polygon of `(∑ Xⁿ) (1 - X)` the
finite face `{0 + 0}`, in agreement with the polygon of the product `1`. -/
theorem isFiniteFace_newtonPolygon_mk_one_mul_one_sub_X {σ : ℝ} (hσ : σ < 0) :
    IsFiniteFace ((mk 1 * (1 - X) : R⟦X⟧).newtonPolygon v) σ 0 0 :=
  isFiniteFace_newtonPolygon_mul v (isFiniteFace_newtonPolygon_mk_one v hσ)
    (isFiniteFace_newtonPolygon_one_sub_X v hσ)

end GeometricSeriesProduct

section Sums

open Polynomial

variable {R : Type*} [Ring R] (v : AddValuation R (WithTop ℝ))

/-- The coefficient heights of `1 + X ^ 2` are `0` at `0` and `2` and `⊤` elsewhere. -/
private theorem addValuation_coeff_one_add_X_sq (n : ℕ) :
    v ((1 + X ^ 2 : R[X]).coeff n) = if n = 0 ∨ n = 2 then 0 else ⊤ := by
  rcases n with _ | _ | _ | n <;> simp [coeff_one, coeff_X_pow]

/-- The Newton polygon of `1 + X ^ 2` is the horizontal segment of height `0` on `[0, 2]`. -/
theorem newtonPolygon_one_add_X_sq :
    (1 + X ^ 2 : R[X]).newtonPolygon v = fun n => if n ≤ 2 then 0 else ⊤ := by
  have h₀ : (1 + X ^ 2 : R[X]).newtonPolygon v 0 ≤ 0 := by simp
  have h₂ : (1 + X ^ 2 : R[X]).newtonPolygon v 2 ≤ 0 := by
    have h := newtonPolygon_le (1 + X ^ 2 : R[X]) v 2
    rw [addValuation_coeff_one_add_X_sq] at h
    simpa using h
  refine le_antisymm (fun n => ?_) (le_newtonPolygon (isConvexSeq_ite_le 2) fun n => ?_)
  · rcases n with _ | _ | _ | n
    · simp
    · -- The middle height lies below the larger of the two outer heights, by convexity.
      simpa using ((isConvexSeq_newtonPolygon _ v).le_max (i := 0) (j := 1) (k := 2) (by omega)
        (by omega)).trans (max_le h₀ h₂)
    · simpa using h₂
    · simp
  · rw [addValuation_coeff_one_add_X_sq]
    rcases n with _ | _ | _ | n <;> simp

/-- The pointwise minimum of the Newton polygons of `1` and `X ^ 2` is `⊤` at the index `1`,
where neither polynomial has a nonzero coefficient. -/
theorem inf_newtonPolygon_one_newtonPolygon_X_sq_apply_one :
    ((1 : R[X]).newtonPolygon v ⊓ (X ^ 2 : R[X]).newtonPolygon v) 1 = ⊤ := by
  have h : (X ^ 2 : R[X]).newtonPolygon v 1 = ⊤ := by
    rw [newtonPolygon_def]
    exact lowerConvexEnvelope_eq_top_of_forall_le fun i hi => by
      simp [coeff_X_pow, show i ≠ 2 by omega]
  rw [Pi.inf_apply, newtonPolygon_eq_top_of_natDegree_lt _ v (by simp), h, inf_idem]

/-- **The pointwise minimum is not a lower bound.** The pointwise minimum of the Newton polygons
of `1` and `X ^ 2` does not lie below the Newton polygon of `1 + X ^ 2`. -/
theorem not_inf_newtonPolygon_le_newtonPolygon_one_add_X_sq :
    ¬(1 : R[X]).newtonPolygon v ⊓ (X ^ 2 : R[X]).newtonPolygon v ≤
      (1 + X ^ 2 : R[X]).newtonPolygon v := fun h => by
  have h₁ := h 1
  rw [inf_newtonPolygon_one_newtonPolygon_X_sq_apply_one, newtonPolygon_one_add_X_sq] at h₁
  simp at h₁

/-- The lower convex envelope of the pointwise minimum of the Newton polygons of `1` and `X ^ 2`
is the Newton polygon of `1 + X ^ 2`. -/
theorem lowerConvexEnvelope_inf_newtonPolygon_one_newtonPolygon_X_sq :
    lowerConvexEnvelope ((1 : R[X]).newtonPolygon v ⊓ (X ^ 2 : R[X]).newtonPolygon v) =
      (1 + X ^ 2 : R[X]).newtonPolygon v := by
  rw [newtonPolygon_def, newtonPolygon_def, newtonPolygon_def,
    lowerConvexEnvelope_inf_lowerConvexEnvelope (isAdmissible_addValuation_coeff 1 v)
      (isAdmissible_addValuation_coeff _ v)]
  congr 1
  funext n
  rcases n with _ | _ | _ | n <;> simp [coeff_one, coeff_X_pow]

end Sums

section RootsAtZero

open Polynomial

variable {p : ℕ} [Fact p.Prime]

/-- Over `ℚ_[p]`, `X ^ 2 (1 - p X)` has the single finite slope `1`. -/
theorem newtonSlopes_X_sq_mul_one_sub_p_X :
    (X ^ 2 * (1 - C (p : ℚ_[p]) * X) : ℚ_[p][X]).newtonSlopes (padicRealValuation p) = {1} := by
  rw [newtonSlopes_X_pow_mul, newtonSlopes_one_sub_p_X]

/-- Over `ℚ_[p]`, the roots of `X ^ 2 (1 - p X)` are `0` with multiplicity two and `p⁻¹`. -/
theorem roots_X_sq_mul_one_sub_p_X :
    (X ^ 2 * (1 - C (p : ℚ_[p]) * X) : ℚ_[p][X]).roots = {0, 0, (p : ℚ_[p])⁻¹} := by
  rw [one_sub_p_X_eq, roots_mul (mul_ne_zero (pow_ne_zero 2 X_ne_zero)
      (mul_ne_zero (C_ne_zero.mpr (neg_ne_zero.mpr p_ne_zero)) (X_sub_C_ne_zero _))), roots_X_pow,
    roots_C_mul _ (neg_ne_zero.mpr p_ne_zero), roots_X_sub_C]
  rfl

open scoped Classical in
/-- **The root zero has no slope.** Over `ℚ_[p]`, the finite slopes of `X ^ 2 (1 - p X)` are the
negated valuations of its nonzero roots: the double root `0` contributes no slope, and the root
`p⁻¹` of valuation `-1` gives the slope `1`. -/
theorem newtonSlopes_X_sq_mul_one_sub_p_X_eq_map_roots :
    (X ^ 2 * (1 - C (p : ℚ_[p]) * X) : ℚ_[p][X]).newtonSlopes (padicRealValuation p) =
      ((X ^ 2 * (1 - C (p : ℚ_[p]) * X) : ℚ_[p][X]).roots.filter (· ≠ 0)).map
        fun α => -(padicRealValuation p α).untop₀ := by
  rw [newtonSlopes_X_sq_mul_one_sub_p_X, roots_X_sq_mul_one_sub_p_X, Multiset.insert_eq_cons,
    Multiset.insert_eq_cons, Multiset.filter_cons_of_neg _ (by simp),
    Multiset.filter_cons_of_neg _ (by simp), Multiset.filter_singleton]
  simp [inv_ne_zero p_ne_zero, AddValuation.map_inv]

end RootsAtZero

end TauCeti.NewtonPolygonProductExample
