/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Twisted.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Order.Minimal

/-!
# Rational successive infima of twisted heights

The `i`-th rational successive infimum is the infimum of the nonnegative thresholds at
which the points of bounded twisted height span a space of dimension at least `i`.
The rational infimum space is the intersection of those spans at all thresholds strictly
above that infimum. All points and spans here are over the fixed number field `K`, not
its algebraic closure.

Finite dimension makes this intersection equal to one of the threshold spans, without
asserting that the infimum itself is attained. In particular, a strict gap between the
`i`-th and `(i+1)`-st infima gives an infimum space of dimension exactly `i`.
For unweighted coordinate forms the positive-index infima are `1`, the zeroth infimum
space is zero, and every positive-index infimum space is the whole space.

These order and dimension statements require no independence or finite-support conditions
on the forms and weights: they apply even to the total `finprod` convention of
`twistedHeight`. The index bounds are essential, since the real infimum of an empty
threshold set is a junk value.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace
  Theorem*, Ann. of Math. 177 (2013), §9, Lemma 9.1 (the fixed-field versions).
-/

public noncomputable section

open Module Submodule Set

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
  (L : GlobalNumberFields.Place K → Fin n → Fin n → K)
  (c : GlobalNumberFields.Place K → Fin n → ℝ) (Q : ℝ)

/-- The `K`-span of the `K`-points of twisted height at most `r`. -/
def twistedHeightSpan (r : ℝ) : Submodule K (Fin n → K) :=
  span K {x | twistedHeight L c Q x ≤ r}

/-- The `i`-th rational successive infimum, with the zeroth infimum equal to zero.
Only indices at most `n` have a nonempty threshold set. -/
def rationalSuccessiveInfimum (i : ℕ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ i ≤ finrank K (twistedHeightSpan L c Q r)}

/-- The rational infimum space: intersect the bounded-height spans at every threshold
strictly larger than the `i`-th rational successive infimum. -/
def rationalInfimumSpace (i : ℕ) : Submodule K (Fin n → K) :=
  ⨅ r > rationalSuccessiveInfimum L c Q i, twistedHeightSpan L c Q r

/-- The bounded-height span is the span of the corresponding sublevel set. -/
theorem twistedHeightSpan_def (r : ℝ) :
    twistedHeightSpan L c Q r = span K {x | twistedHeight L c Q x ≤ r} := (rfl)

/-- Every point of height at most the threshold belongs to the bounded-height span. -/
theorem mem_twistedHeightSpan_of_le {r : ℝ} {x : Fin n → K}
    (hx : twistedHeight L c Q x ≤ r) : x ∈ twistedHeightSpan L c Q r := by
  rw [twistedHeightSpan_def]
  exact subset_span hx

/-- A bounded-height span lies in a submodule exactly when all its generators do. -/
@[simp]
theorem twistedHeightSpan_le {r : ℝ} {S : Submodule K (Fin n → K)} :
    twistedHeightSpan L c Q r ≤ S ↔ ∀ x, twistedHeight L c Q x ≤ r → x ∈ S := by
  rw [twistedHeightSpan_def, span_le]
  rfl

/-- The defining threshold infimum for the `i`-th rational successive infimum. -/
theorem rationalSuccessiveInfimum_def (i : ℕ) :
    rationalSuccessiveInfimum L c Q i =
      sInf {r : ℝ | 0 ≤ r ∧ i ≤ finrank K (twistedHeightSpan L c Q r)} := (rfl)

/-- The infimum space is the intersection of the spans strictly above the infimum. -/
theorem rationalInfimumSpace_def (i : ℕ) :
    rationalInfimumSpace L c Q i =
      ⨅ r > rationalSuccessiveInfimum L c Q i, twistedHeightSpan L c Q r := (rfl)

/-- Membership in an infimum space means membership in every threshold span strictly
above the corresponding infimum. -/
@[simp]
theorem mem_rationalInfimumSpace {i : ℕ} {x : Fin n → K} :
    x ∈ rationalInfimumSpace L c Q i ↔
      ∀ r > rationalSuccessiveInfimum L c Q i, x ∈ twistedHeightSpan L c Q r := by
  simp [rationalInfimumSpace_def]

/-- Bounded-height spans increase with the height threshold. -/
theorem monotone_twistedHeightSpan : Monotone (twistedHeightSpan L c Q) :=
  fun _ _ h ↦ span_mono fun _ hx ↦ hx.trans h

/-- A sufficiently large nonnegative threshold spans the whole fixed-field space. -/
theorem exists_twistedHeightSpan_eq_top :
    ∃ r : ℝ, 0 ≤ r ∧ twistedHeightSpan L c Q r = ⊤ := by
  obtain ⟨r, hr⟩ := (finite_range fun i : Fin n ↦
    twistedHeight L c Q (Pi.single i 1)).bddAbove
  refine ⟨max 0 r, le_max_left _ _, top_unique ?_⟩
  rw [← (Pi.basisFun K (Fin n)).span_eq]
  refine span_le.mpr ?_
  rintro _ ⟨i, rfl⟩
  apply subset_span
  simpa only [mem_ofPred_eq, Pi.basisFun_apply] using
    (hr (mem_range_self i)).trans (le_max_right 0 r)

private theorem successiveThreshold_nonempty {i : ℕ} (hi : i ≤ n) :
    {r : ℝ | 0 ≤ r ∧ i ≤ finrank K (twistedHeightSpan L c Q r)}.Nonempty := by
  obtain ⟨r, hr, htop⟩ := exists_twistedHeightSpan_eq_top L c Q
  refine ⟨r, hr, ?_⟩
  rw [htop, finrank_top, finrank_fin_fun]
  exact hi

/-- Every rational successive infimum is nonnegative, including the empty-set junk value. -/
theorem rationalSuccessiveInfimum_nonneg (i : ℕ) :
    0 ≤ rationalSuccessiveInfimum L c Q i :=
  Real.sInf_nonneg fun _ hr ↦ hr.1

/-- A nonnegative threshold whose span has dimension at least `i` bounds the `i`-th infimum. -/
theorem rationalSuccessiveInfimum_le {i : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hi : i ≤ finrank K (twistedHeightSpan L c Q r)) :
    rationalSuccessiveInfimum L c Q i ≤ r :=
  csInf_le ⟨0, fun _ h ↦ h.1⟩ ⟨hr, hi⟩

/-- The zeroth rational successive infimum is zero. -/
@[simp]
theorem rationalSuccessiveInfimum_zero : rationalSuccessiveInfimum L c Q 0 = 0 :=
  le_antisymm (rationalSuccessiveInfimum_le L c Q le_rfl (Nat.zero_le _))
    (rationalSuccessiveInfimum_nonneg L c Q 0)

/-- Rational successive infima are monotone in the meaningful range of indices. -/
theorem rationalSuccessiveInfimum_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    rationalSuccessiveInfimum L c Q i ≤ rationalSuccessiveInfimum L c Q j :=
  csInf_le_csInf ⟨0, fun _ h ↦ h.1⟩ (successiveThreshold_nonempty L c Q hj)
    fun _ h ↦ ⟨h.1, hij.trans h.2⟩

/-- Every threshold strictly above the `i`-th infimum has span dimension at least `i`.
No attainment at the infimum is required. -/
theorem le_finrank_twistedHeightSpan_of_infimum_lt {i : ℕ} (hi : i ≤ n)
    {r : ℝ} (hr : rationalSuccessiveInfimum L c Q i < r) :
    i ≤ finrank K (twistedHeightSpan L c Q r) := by
  obtain ⟨t, ht, htr⟩ := exists_lt_of_csInf_lt (successiveThreshold_nonempty L c Q hi) hr
  exact ht.2.trans (Submodule.finrank_mono (monotone_twistedHeightSpan L c Q htr.le))

/-- Below the next infimum, a nonnegative threshold has span dimension at most `i`. -/
theorem finrank_twistedHeightSpan_le_of_lt_infimum {i : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (hi : r < rationalSuccessiveInfimum L c Q (i + 1)) :
    finrank K (twistedHeightSpan L c Q r) ≤ i := by
  by_contra h
  exact hi.not_ge (rationalSuccessiveInfimum_le L c Q hr (by omega))

/-- The infimum space lies in every span at a threshold strictly above its infimum. -/
theorem rationalInfimumSpace_le {i : ℕ} {r : ℝ}
    (hr : rationalSuccessiveInfimum L c Q i < r) :
    rationalInfimumSpace L c Q i ≤ twistedHeightSpan L c Q r :=
  iInf_le_of_le r (iInf_le _ hr)

/-- The intersection defining an infimum space is one of its threshold spans.
This is stabilization above the infimum, not attainment at the infimum. -/
theorem exists_rationalInfimumSpace_eq_twistedHeightSpan (i : ℕ) :
    ∃ r > rationalSuccessiveInfimum L c Q i,
      rationalInfimumSpace L c Q i = twistedHeightSpan L c Q r := by
  obtain ⟨r, hr⟩ := exists_minimalFor_of_wellFoundedLT
    (fun r : ℝ ↦ rationalSuccessiveInfimum L c Q i < r)
    (fun r ↦ finrank K (twistedHeightSpan L c Q r))
    ⟨_, lt_add_one (rationalSuccessiveInfimum L c Q i)⟩
  refine ⟨r, hr.prop, le_antisymm (rationalInfimumSpace_le L c Q hr.prop) ?_⟩
  refine le_iInf fun t ↦ le_iInf fun ht ↦ ?_
  rcases le_total r t with h | h
  · exact monotone_twistedHeightSpan L c Q h
  · have hle := monotone_twistedHeightSpan L c Q h
    exact (Submodule.eq_of_le_of_finrank_eq hle
      (le_antisymm (Submodule.finrank_mono hle) (hr.2 ht (Submodule.finrank_mono hle)))).ge

/-- In its meaningful index range the `i`-th infimum space has dimension at least `i`. -/
theorem le_finrank_rationalInfimumSpace {i : ℕ} (hi : i ≤ n) :
    i ≤ finrank K (rationalInfimumSpace L c Q i) := by
  obtain ⟨r, hr, heq⟩ := exists_rationalInfimumSpace_eq_twistedHeightSpan L c Q i
  rw [heq]
  exact le_finrank_twistedHeightSpan_of_infimum_lt L c Q hi hr

/-- A strict gap between successive rational infima gives an infimum space of exactly
the intermediate dimension. -/
theorem finrank_rationalInfimumSpace_of_lt {i : ℕ} (hi : i < n)
    (hgap : rationalSuccessiveInfimum L c Q i < rationalSuccessiveInfimum L c Q (i + 1)) :
    finrank K (rationalInfimumSpace L c Q i) = i := by
  obtain ⟨r, hir, hri⟩ := exists_between hgap
  refine le_antisymm ?_ (le_finrank_rationalInfimumSpace L c Q hi.le)
  exact (Submodule.finrank_mono (rationalInfimumSpace_le L c Q hir)).trans
    (finrank_twistedHeightSpan_le_of_lt_infimum L c Q
      ((rationalSuccessiveInfimum_nonneg L c Q i).trans hir.le) hri)

/-- Infimum spaces are nested as the index increases within its meaningful range. -/
theorem rationalInfimumSpace_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    rationalInfimumSpace L c Q i ≤ rationalInfimumSpace L c Q j :=
  le_iInf fun _ ↦ le_iInf fun hr ↦ rationalInfimumSpace_le L c Q
    ((rationalSuccessiveInfimum_mono L c Q hij hj).trans_lt hr)

/-- The last rational infimum space is the whole fixed-field space. -/
@[simp]
theorem rationalInfimumSpace_last : rationalInfimumSpace L c Q n = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le _) (by
    simpa using le_finrank_rationalInfimumSpace L c Q (le_refl n))

/-! ## Unweighted coordinate forms -/

/-- The bounded-height span for unweighted coordinate forms jumps from zero to the whole
space at threshold `1`. This includes empty coordinate spaces. -/
theorem twistedHeightSpan_coordForms_zero (r : ℝ) :
    twistedHeightSpan (coordForms K n) 0 Q r = if 1 ≤ r then ⊤ else ⊥ := by
  classical
  split_ifs with hr
  · apply top_unique
    rw [← (Pi.basisFun K (Fin n)).span_eq]
    refine span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    apply subset_span
    simp only [mem_ofPred_eq, Pi.basisFun_apply]
    have : Nonempty (Fin n) := ⟨i⟩
    have hlocal (v : GlobalNumberFields.Place K) :
        twistedLocalHeight (coordForms K n) 0 Q v (Pi.single i 1) = 1 := by
      rw [twistedLocalHeight_coordForms_zero]
      refine le_antisymm (ciSup_le fun j ↦ ?_) ?_
      · by_cases h : j = i <;> simp [h]
      · exact le_ciSup_of_le (finite_range _).bddAbove i (by simp)
    rw [twistedHeight_of_ne_zero (by simp)]
    simpa [hlocal] using hr
  · apply bot_unique
    refine span_le.mpr fun x hx ↦ ?_
    by_contra hx0
    have hxne : x ≠ 0 := by simpa using hx0
    have hheight : 1 ≤ twistedHeight (coordForms K n) 0 Q x := by
      rw [twistedHeight_coordForms_zero hxne]
      exact Real.one_le_rpow (Height.one_le_mulHeight x) (by positivity)
    exact hr (hheight.trans hx)

/-- The positive-index rational successive infima of unweighted coordinate forms are `1`. -/
@[simp]
theorem rationalSuccessiveInfimum_coordForms_zero {i : ℕ} (hi : 0 < i) (hin : i ≤ n) :
    rationalSuccessiveInfimum (coordForms K n) 0 Q i = 1 := by
  refine le_antisymm (rationalSuccessiveInfimum_le _ _ _ zero_le_one ?_) ?_
  · rw [twistedHeightSpan_coordForms_zero, ite_eq_left (le_refl 1),
      finrank_top, finrank_fin_fun]
    exact hin
  · apply le_csInf (successiveThreshold_nonempty _ _ _ hin)
    rintro r ⟨_, hr⟩
    by_contra h
    rw [twistedHeightSpan_coordForms_zero, ite_eq_right h, finrank_bot] at hr
    omega

/-- For unweighted coordinate forms the zeroth infimum space is zero. -/
@[simp]
theorem rationalInfimumSpace_coordForms_zero_zero :
    rationalInfimumSpace (coordForms K n) 0 Q 0 = ⊥ := by
  apply bot_unique
  have h := rationalInfimumSpace_le (coordForms K n) 0 Q
    (i := 0) (r := 1 / 2) (by simp)
  rw [twistedHeightSpan_coordForms_zero] at h
  norm_num at h
  exact h.le

/-- Every positive-index infimum space of unweighted coordinate forms is the whole space. -/
@[simp]
theorem rationalInfimumSpace_coordForms_zero {i : ℕ} (hi : 0 < i) (hin : i ≤ n) :
    rationalInfimumSpace (coordForms K n) 0 Q i = ⊤ := by
  apply top_unique
  refine le_iInf fun r ↦ le_iInf fun hr ↦ ?_
  rw [rationalSuccessiveInfimum_coordForms_zero Q hi hin] at hr
  simp [twistedHeightSpan_coordForms_zero, hr.le]

end TauCeti
