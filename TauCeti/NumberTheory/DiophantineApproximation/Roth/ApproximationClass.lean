/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import TauCeti.Algebra.Order.Antidiag.FinsuppEquiv

/-!
# Approximation classes

Mahler's reduction sorts the solutions of a Diophantine inequality by where they are well
approximated, so that the solutions in one class behave alike at every place. Most of the file
is not about places, heights or number fields: a family of maps `φ a : X → ℝ` with nonnegative
values summing to at most `1` sends each point of `X` to a point of the standard simplex, for
`0 < N` the unit cube is cut into half-open cells of side `1 / N`, and two points lie in the same
class when they land in the same cell. The last section specializes this to Roth's inequality
over a number field.

For `0 < N` and a point with nonnegative coordinates, a cell is labelled by its scaled south-west
corner `cellIndex N y a = ⌊N * y a⌋₊`, a tuple of natural numbers. The definition makes sense for
every `y : A → ℝ` and `N : ℕ`, but outside this range it loses its geometric meaning: negative
coordinates are truncated to `0`, and `N = 0` gives the constant label `0`. Three facts come out
of this.

* The classes are finitely many. The label of a point of the simplex satisfies
  `∑ a, c a ≤ N`, and there are `(N + card A).choose (card A)` such labels
  (`TauCeti.ncard_setOf_sum_le`). Without the simplex condition the labels are the
  `(N + 1) ^ card A` cells of the cube; the rejection test at the end of the file shows the
  difference.
* An infinite set has an infinite class, by the pigeonhole principle.
* A class pins every coordinate at once. For `f : A → ℝ` with values in `(0, 1]` and product
  `Λ = ∏ b, f b < 1`, the profile `logProfile f a = log (f a) / log Λ` is a point of the simplex
  lying on the hyperplane `∑ a, y a = 1`, and its cell traps each `f a` between two powers of
  `Λ`: `Λ ^ ((c a + 1) / N) < f a ≤ Λ ^ (c a / N)`. Since the profile lies on the hyperplane, its
  label sums to more than `N - card A`.

Over a number field `K`, with a field extension `F`, finite sets `Sinf` of infinite places and
`Sfin` of finite places of `K`, at each such place `v` an absolute value `w v` of `F` and a target
`α v ∈ F`, the left side of Roth's inequality for `β ∈ K`,

`(∏ v ∈ Sinf, min 1 (w v (β - α v)) ^ mult v) * ∏ v ∈ Sfin, min 1 (w v (β - α v))`,

is a product of local factors indexed by the disjoint union `Sinf ⊕ Sfin` of the two sets of
places. The approximation class of `β` at side `1 / N` is the class `TauCeti.profileClass` of
this family: the cell of side `1 / N` containing its logarithmic profile, or a corner of the
simplex when `β` is one of the targets. At most `(N + |S|).choose |S|` classes occur, where `|S|`
is the number of places.

## Main results

* `TauCeti.cellIndex`: the label of the cell of side `1 / N` containing a point with nonnegative
  coordinates, for `0 < N`.
* `TauCeti.sum_cellIndex_le`: a point of the simplex has a label with `∑ a, c a ≤ N`.
* `TauCeti.ncard_image_cellIndex_le`: at most `(N + card A).choose (card A)` classes are nonempty.
* `Set.Infinite.exists_cellIndex_eq`: an infinite set has an infinite class.
* `TauCeti.logProfile`, with `TauCeti.logProfile_nonneg` and `TauCeti.sum_logProfile`.
* `TauCeti.le_rpow_cellIndex_div` and `TauCeti.rpow_cellIndex_add_one_div_lt`: the two halves of
  Bombieri–Gubler's (6.9); the first is attained.
* `TauCeti.one_sub_card_div_lt_sum_cellIndex_div`: Bombieri–Gubler's (6.10), the label of a point
  on the hyperplane `∑ a, y a = 1` sums to more than `N - card A`.
* `TauCeti.profileClass`: the class of a family with values in `[0, 1]`, which may vanish. A
  vanishing value sends the family to a corner of the simplex, where the upper half of (6.9)
  (`TauCeti.le_rpow_profileClass_div`) and (6.10)
  (`TauCeti.one_sub_card_div_lt_sum_profileClass_div`) still hold.
* `NumberField.sPlaceAbsValue` and `NumberField.sPlaceWeight`: the absolute value and the weight
  (`mult v` at an infinite place, `1` at a finite one) of a place of `Sinf ⊕ Sfin`.
* `NumberField.approxFactor`: the local factor `min 1 (w v (β - α v)) ^ weight` at a place, with
  `NumberField.prod_approxFactor`: their product is the left side of Roth's inequality.
* `NumberField.approxClass`: the approximation class of `β` at side `1 / N`, the label of the
  logarithmic profile when `β` is no target (`NumberField.approxClass_of_forall_algebraMap_ne`)
  and a corner of the simplex when it is one (`NumberField.approxClass_of_exists_algebraMap_eq`).
* `NumberField.ncard_image_approxClass_le`: at most `(N + |S|).choose |S|` classes occur.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), 6.4.2–6.4.4 and Lemma 6.5.6.
* The statements follow Ralf Stephan's formalization
  `DiophantineApproximation/ApproximationClass.lean` in `rwst/Subspace-Theorems` (Apache 2.0).
-/

public section

open Finset Real

namespace TauCeti

variable {A : Type*}

/-- The tuple `⌊N * y a⌋₊` of natural numbers. For `0 < N` and `y : A → ℝ` with nonnegative
coordinates, it labels the half-open cell of side `1 / N` containing `y` by its south-west corner
scaled by `N`. Negative coordinates are truncated to `0`, and for `N = 0` the label is constantly
`0`. -/
noncomputable def cellIndex (N : ℕ) (y : A → ℝ) (a : A) : ℕ := ⌊(N : ℝ) * y a⌋₊

theorem cellIndex_apply (N : ℕ) (y : A → ℝ) (a : A) : cellIndex N y a = ⌊(N : ℝ) * y a⌋₊ :=
  (rfl)

/-- The south-west corner of the cell of a point is below the point. -/
theorem cellIndex_div_le (N : ℕ) {y : A → ℝ} {a : A} (hy : 0 ≤ y a) :
    (cellIndex N y a : ℝ) / N ≤ y a := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simpa using hy
  rw [div_le_iff₀ (by exact_mod_cast hN), mul_comm, cellIndex_apply]
  exact Nat.floor_le (by positivity)

/-- A point is strictly below the north-east corner of its cell. -/
theorem lt_cellIndex_add_one_div {N : ℕ} (hN : 0 < N) (y : A → ℝ) (a : A) :
    y a < ((cellIndex N y a : ℝ) + 1) / N := by
  rw [lt_div_iff₀ (by exact_mod_cast hN), mul_comm, cellIndex_apply]
  exact Nat.lt_floor_add_one _

/-- The label of a point of the standard simplex satisfies `∑ a, c a ≤ N`. -/
theorem sum_cellIndex_le [Fintype A] (N : ℕ) {y : A → ℝ} (hy : ∀ a, 0 ≤ y a)
    (hsum : ∑ a, y a ≤ 1) : ∑ a, cellIndex N y a ≤ N := by
  have key : ∑ a, (cellIndex N y a : ℝ) ≤ N := calc
    ∑ a, (cellIndex N y a : ℝ) ≤ ∑ a, (N : ℝ) * y a :=
      sum_le_sum fun a _ ↦ Nat.floor_le (mul_nonneg N.cast_nonneg (hy a))
    _ = N * ∑ a, y a := (mul_sum ..).symm
    _ ≤ N := mul_le_of_le_one_right N.cast_nonneg hsum
  exact_mod_cast key

/-- **Bombieri–Gubler (6.10).** The label of a point on the hyperplane `∑ a, y a = 1` sums to
more than `N - card A`, after division by `N`. -/
theorem one_sub_card_div_lt_sum_cellIndex_div [Fintype A] {N : ℕ} (hN : 0 < N) {y : A → ℝ}
    (hsum : ∑ a, y a = 1) :
    1 - (Fintype.card A : ℝ) / N < ∑ a, (cellIndex N y a : ℝ) / N := by
  have hA : (univ : Finset A).Nonempty := by
    by_contra h
    simp [not_nonempty_iff_eq_empty.mp h] at hsum
  have hlt : ∑ a, y a < ∑ a, ((cellIndex N y a : ℝ) + 1) / N :=
    sum_lt_sum_of_nonempty hA fun a _ ↦ lt_cellIndex_add_one_div hN y a
  simp only [add_div, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one_div,
    hsum] at hlt
  linarith

variable [Fintype A]

/-- The logarithmic profile of `f : A → ℝ`, the tuple `log (f a) / log (∏ b, f b)`. For `f` with
values in `(0, 1]` and product less than `1` it is a point of the standard simplex lying on the
hyperplane `∑ a, y a = 1`. When the product is `1` the profile is `0`. -/
noncomputable def logProfile (f : A → ℝ) (a : A) : ℝ := log (f a) / log (∏ b, f b)

theorem logProfile_apply (f : A → ℝ) (a : A) : logProfile f a = log (f a) / log (∏ b, f b) :=
  (rfl)

/-- The logarithmic profile of a family in `(0, 1]` is nonnegative. -/
theorem logProfile_nonneg {f : A → ℝ} (hpos : ∀ a, 0 < f a) (hf : ∀ a, f a ≤ 1) (a : A) :
    0 ≤ logProfile f a :=
  div_nonneg_of_nonpos (log_nonpos (hpos a).le (hf a))
    (log_nonpos (prod_nonneg fun b _ ↦ (hpos b).le) (prod_le_one₀ (fun b _ ↦ (hpos b).le)
      fun b _ ↦ hf b))

/-- The logarithmic profile of a positive family with product different from `1` sums to `1`. -/
@[simp]
theorem sum_logProfile {f : A → ℝ} (hpos : ∀ a, 0 < f a) (hprod : ∏ b, f b ≠ 1) :
    ∑ a, logProfile f a = 1 := by
  have hlog : log (∏ b, f b) = ∑ a, log (f a) := log_prod fun a _ ↦ (hpos a).ne'
  simp_rw [logProfile_apply, ← Finset.sum_div, ← hlog]
  exact div_self (log_ne_zero_of_pos_of_ne_one (prod_pos fun b _ ↦ hpos b) hprod)

/-- **The upper half of Bombieri–Gubler (6.9).** For `f` with values in `(0, 1]` and product
`Λ`, each `f a` is at most `Λ ^ (c a / N)`, where `c` labels the cell of the logarithmic
profile of `f`. -/
theorem le_rpow_cellIndex_div (N : ℕ) {f : A → ℝ} (hpos : ∀ a, 0 < f a)
    (hf : ∀ a, f a ≤ 1) (a : A) :
    f a ≤ (∏ b, f b) ^ ((cellIndex N (logProfile f) a : ℝ) / N) := by
  have hprod₀ : 0 < ∏ b, f b := prod_pos fun b _ ↦ hpos b
  rcases (prod_le_one₀ (fun b _ ↦ (hpos b).le) fun b _ ↦ hf b).lt_or_eq with hprod | hprod
  swap
  · rw [hprod, one_rpow]
    exact hf a
  rw [← log_le_log_iff (hpos a) (rpow_pos_of_pos hprod₀ _), log_rpow hprod₀,
    ← le_div_iff_of_neg (log_neg hprod₀ hprod), ← logProfile_apply]
  exact cellIndex_div_le N (logProfile_nonneg hpos hf a)

/-- **The lower half of Bombieri–Gubler (6.9).** For a positive family `f` with product `Λ < 1`,
each `f a` exceeds `Λ ^ ((c a + 1) / N)`, where `c` labels the cell of the logarithmic profile
of `f`. -/
theorem rpow_cellIndex_add_one_div_lt {N : ℕ} (hN : 0 < N) {f : A → ℝ} (hpos : ∀ a, 0 < f a)
    (hprod : ∏ b, f b < 1) (a : A) :
    (∏ b, f b) ^ (((cellIndex N (logProfile f) a : ℝ) + 1) / N) < f a := by
  have hprod₀ : 0 < ∏ b, f b := prod_pos fun b _ ↦ hpos b
  rw [← log_lt_log_iff (rpow_pos_of_pos hprod₀ _) (hpos a), log_rpow hprod₀,
    ← div_lt_iff_of_neg (log_neg hprod₀ hprod), ← logProfile_apply]
  exact lt_cellIndex_add_one_div hN _ a

/-- The classes of a family of maps into the standard simplex, which for `0 < N` are the cells of
side `1 / N`: at most `(N + card A).choose (card A)` labels occur. -/
theorem ncard_image_cellIndex_le {ι : Type*} {X : Set ι} (φ : A → ι → ℝ)
    (hφ₀ : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ₁ : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ((fun x ↦ cellIndex N fun a ↦ φ a x) '' X).ncard ≤
      (N + Fintype.card A).choose (Fintype.card A) := by
  rw [← ncard_setOf_sum_le A N]
  refine Set.ncard_le_ncard ?_ (finite_setOf_sum_le A N)
  rintro _ ⟨x, hx, rfl⟩
  exact sum_cellIndex_le N (fun a ↦ hφ₀ a x hx) (hφ₁ x hx)

/-! ### Families with a vanishing value -/

open scoped Classical in
/-- The approximation class of a family `f : A → ℝ` with values in `[0, 1]`, at side `1 / N`.
When no value of `f` vanishes, it is the label `cellIndex N (logProfile f)` of the logarithmic
profile. When some `f a` vanishes the product of the family is `0` and the profile carries no
information; the class is then the corner `N • e a` of the simplex, for one such `a`. Either way
the class is a label with `∑ a, c a ≤ N` satisfying the upper half of (6.9), and (6.10) when
`0 < N` and the product is less than `1`. -/
noncomputable def profileClass (N : ℕ) (f : A → ℝ) : A → ℕ :=
  if h : ∃ a, f a = 0 then Pi.single h.choose N else cellIndex N (logProfile f)

/-- Without a vanishing value, the class of a family is the label of its logarithmic profile. -/
theorem profileClass_of_forall_ne_zero {N : ℕ} {f : A → ℝ} (hf : ∀ a, f a ≠ 0) :
    profileClass N f = cellIndex N (logProfile f) := by
  rw [profileClass, dite_eq_right (not_exists.mpr hf)]

/-- With a vanishing value, the class of a family is the corner `N • e a` of the simplex at a
place `a` where the family vanishes. -/
theorem profileClass_of_exists_eq_zero [DecidableEq A] (N : ℕ) {f : A → ℝ} (h : ∃ a, f a = 0) :
    ∃ a, f a = 0 ∧ profileClass N f = Pi.single a N := by
  refine ⟨h.choose, h.choose_spec, ?_⟩
  rw [profileClass, dite_eq_left h]
  congr!

/-- With a vanishing value, the class of a family is a corner of the simplex, whose entries sum
to `N`. -/
theorem sum_profileClass_of_exists_eq_zero (N : ℕ) {f : A → ℝ} (h : ∃ a, f a = 0) :
    ∑ a, profileClass N f a = N := by
  classical
  obtain ⟨a, -, ha⟩ := profileClass_of_exists_eq_zero N h
  rw [ha, Finset.sum_pi_single']
  simp

/-- The class of a family with values in `[0, 1]` is a label with `∑ a, c a ≤ N`. -/
theorem sum_profileClass_le (N : ℕ) {f : A → ℝ} (hf₀ : ∀ a, 0 ≤ f a) (hf₁ : ∀ a, f a ≤ 1) :
    ∑ a, profileClass N f a ≤ N := by
  by_cases h : ∃ a, f a = 0
  · exact (sum_profileClass_of_exists_eq_zero N h).le
  · push Not at h
    rw [profileClass_of_forall_ne_zero h]
    have hpos a : 0 < f a := (hf₀ a).lt_of_ne' (h a)
    refine sum_cellIndex_le N (logProfile_nonneg hpos hf₁) ?_
    by_cases hprod : ∏ b, f b = 1
    · simp [logProfile_apply, hprod]
    · exact (sum_logProfile hpos hprod).le

/-- **The upper half of Bombieri–Gubler (6.9) for a family with values in `[0, 1]`**: each `f a`
is at most `Λ ^ (c a / N)`, where `Λ` is the product of the family and `c` its class. -/
theorem le_rpow_profileClass_div (N : ℕ) {f : A → ℝ} (hf₀ : ∀ a, 0 ≤ f a) (hf₁ : ∀ a, f a ≤ 1)
    (a : A) : f a ≤ (∏ b, f b) ^ ((profileClass N f a : ℝ) / N) := by
  by_cases h : ∃ a, f a = 0
  · classical
    obtain ⟨b, hb, hc⟩ := profileClass_of_exists_eq_zero N h
    rw [hc]
    rcases eq_or_ne a b with rfl | ha
    · rw [hb]
      exact rpow_nonneg (prod_nonneg fun b _ ↦ hf₀ b) _
    · simpa [ha] using hf₁ a
  · push Not at h
    rw [profileClass_of_forall_ne_zero h]
    exact le_rpow_cellIndex_div N (fun b ↦ (hf₀ b).lt_of_ne' (h b)) hf₁ a

/-- **Bombieri–Gubler (6.10) for a family with values in `[0, 1]`**: for `0 < N`, if the product
of the family is less than `1`, then its class sums to more than `N - card A`, after division
by `N`. -/
theorem one_sub_card_div_lt_sum_profileClass_div {N : ℕ} (hN : 0 < N) {f : A → ℝ}
    (hf₀ : ∀ a, 0 ≤ f a) (hprod : ∏ b, f b < 1) :
    1 - (Fintype.card A : ℝ) / N < ∑ a, (profileClass N f a : ℝ) / N := by
  by_cases h : ∃ a, f a = 0
  · have hA : 0 < (Fintype.card A : ℝ) := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨h.choose⟩
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_profileClass_of_exists_eq_zero N h,
      div_self hN'.ne']
    linarith [div_pos hA hN']
  · push Not at h
    have hpos a : 0 < f a := (hf₀ a).lt_of_ne' (h a)
    rw [profileClass_of_forall_ne_zero h]
    exact one_sub_card_div_lt_sum_cellIndex_div hN (sum_logProfile hpos hprod.ne)

/-- The classes of a family of maps into `[0, 1]`: at most `(N + card A).choose (card A)` of
them occur. -/
theorem ncard_image_profileClass_le {ι : Type*} {X : Set ι} (φ : ι → A → ℝ)
    (hφ₀ : ∀ x ∈ X, ∀ a, 0 ≤ φ x a) (hφ₁ : ∀ x ∈ X, ∀ a, φ x a ≤ 1) (N : ℕ) :
    ((fun x ↦ profileClass N (φ x)) '' X).ncard ≤
      (N + Fintype.card A).choose (Fintype.card A) := by
  rw [← ncard_setOf_sum_le A N]
  refine Set.ncard_le_ncard ?_ (finite_setOf_sum_le A N)
  rintro _ ⟨x, hx, rfl⟩
  exact sum_profileClass_le N (hφ₀ x hx) (hφ₁ x hx)

end TauCeti

namespace Set

open TauCeti

/-- **An infinite set has an infinite approximation class.** For a family of maps from an infinite
set `X` into the standard simplex and every `N`, some label `c` with `∑ a, c a ≤ N` is shared by
infinitely many points of `X`; for `0 < N` it labels a cell of side `1 / N`. -/
theorem Infinite.exists_cellIndex_eq {ι A : Type*} [Fintype A] {X : Set ι} (hX : X.Infinite)
    (φ : A → ι → ℝ) (hφ₀ : ∀ a, ∀ x ∈ X, 0 ≤ φ a x) (hφ₁ : ∀ x ∈ X, ∑ a, φ a x ≤ 1) (N : ℕ) :
    ∃ c : A → ℕ, ∑ a, c a ≤ N ∧ {x ∈ X | cellIndex N (fun a ↦ φ a x) = c}.Infinite := by
  by_contra! h
  refine hX (((finite_setOf_sum_le A N).biUnion h).subset fun x hx ↦ ?_)
  exact mem_biUnion (sum_cellIndex_le N (fun a ↦ hφ₀ a x hx) (hφ₁ x hx)) ⟨hx, rfl⟩

end Set

/-! ### Approximation classes over a number field -/

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [Algebra K F]
variable (Sinf : Finset (InfinitePlace K)) (Sfin : Finset (FinitePlace K))

/-! ### The places of `Sinf` and `Sfin` as one index type -/

/-- The absolute value of `K` underlying a place of `Sinf` or of `Sfin`, the two sets of places
being joined into the index type `Sinf ⊕ Sfin`. -/
def sPlaceAbsValue : Sinf ⊕ Sfin → AbsoluteValue K ℝ :=
  Sum.elim (fun v ↦ v.val.val) fun v ↦ v.val.val

@[simp]
theorem sPlaceAbsValue_inl (v : Sinf) : sPlaceAbsValue Sinf Sfin (.inl v) = v.val.val :=
  (rfl)

@[simp]
theorem sPlaceAbsValue_inr (v : Sfin) : sPlaceAbsValue Sinf Sfin (.inr v) = v.val.val :=
  (rfl)

/-- The weight of a place of `Sinf` or of `Sfin` in Mathlib's relative normalization of heights:
`mult v` at an infinite place and `1` at a finite place. -/
noncomputable def sPlaceWeight : Sinf ⊕ Sfin → ℕ :=
  Sum.elim (fun v ↦ v.val.mult) fun _ ↦ 1

@[simp]
theorem sPlaceWeight_inl (v : Sinf) : sPlaceWeight Sinf Sfin (.inl v) = v.val.mult :=
  (rfl)

@[simp]
theorem sPlaceWeight_inr (v : Sfin) : sPlaceWeight Sinf Sfin (.inr v) = 1 :=
  (rfl)

/-! ### Local factors and approximation classes -/

/-- The local approximation factor `min 1 (w v (β - α v)) ^ weight` of `β ∈ K` to the target
`α v ∈ F` at a place `v` of `Sinf` or of `Sfin`, measured by the absolute value `w v` of `F` and
raised to the weight `mult v` at an infinite place. Its product over the places is the left side
of Roth's inequality (`NumberField.prod_approxFactor`). As for `NumberField.approxProd`, the data
`w` and `α` are indexed by the underlying absolute value of a place. -/
noncomputable def approxFactor (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ)
    (α : AbsoluteValue K ℝ → F) (β : K) (a : Sinf ⊕ Sfin) : ℝ :=
  min 1 (w (sPlaceAbsValue Sinf Sfin a) (algebraMap K F β - α (sPlaceAbsValue Sinf Sfin a))) ^
    sPlaceWeight Sinf Sfin a

variable {Sinf Sfin} (w : AbsoluteValue K ℝ → AbsoluteValue F ℝ) (α : AbsoluteValue K ℝ → F)

@[simp]
theorem approxFactor_inl (β : K) (v : Sinf) :
    approxFactor Sinf Sfin w α β (.inl v) =
      min 1 (w v.val.val (algebraMap K F β - α v.val.val)) ^ v.val.mult :=
  (rfl)

@[simp]
theorem approxFactor_inr (β : K) (v : Sfin) :
    approxFactor Sinf Sfin w α β (.inr v) = min 1 (w v.val.val (algebraMap K F β - α v.val.val))
        := by
  simp [approxFactor]

theorem approxFactor_nonneg (β : K) (a : Sinf ⊕ Sfin) : 0 ≤ approxFactor Sinf Sfin w α β a :=
  pow_nonneg (le_min zero_le_one (AbsoluteValue.nonneg _ _)) _

theorem approxFactor_le_one (β : K) (a : Sinf ⊕ Sfin) : approxFactor Sinf Sfin w α β a ≤ 1 :=
  pow_le_one₀ (le_min zero_le_one (AbsoluteValue.nonneg _ _)) (min_le_left _ _)

/-- The product of the local approximation factors of `β` is the left side of Roth's inequality,
a product over the infinite places of `Sinf` with exponents `mult v` times a product over the
finite places of `Sfin`. -/
theorem prod_approxFactor (β : K) :
    ∏ a, approxFactor Sinf Sfin w α β a =
      (∏ v ∈ Sinf, min 1 (w v.val (algebraMap K F β - α v.val)) ^ v.mult) *
        ∏ v ∈ Sfin, min 1 (w v.val (algebraMap K F β - α v.val)) := by
  rw [Fintype.prod_sum_type]
  simp only [approxFactor_inl, approxFactor_inr]
  rw [Finset.prod_coe_sort Sinf (fun v ↦ min 1 (w v.val (algebraMap K F β - α v.val)) ^ v.mult),
    Finset.prod_coe_sort Sfin (fun v ↦ min 1 (w v.val (algebraMap K F β - α v.val)))]

/-- The local approximation factor of `β` at a place vanishes exactly when `β` is the target
there. -/
theorem approxFactor_eq_zero_iff (β : K) (a : Sinf ⊕ Sfin) :
    approxFactor Sinf Sfin w α β a = 0 ↔ algebraMap K F β = α (sPlaceAbsValue Sinf Sfin a) := by
  have hweight : sPlaceWeight Sinf Sfin a ≠ 0 := by
    cases a <;> simp [InfinitePlace.mult_ne_zero]
  rw [approxFactor, pow_eq_zero_iff hweight, ← sub_eq_zero (b := α _),
    ← (w (sPlaceAbsValue Sinf Sfin a)).eq_zero]
  refine ⟨fun h ↦ ((min_eq_iff.mp h).resolve_left fun h ↦ one_ne_zero h.1).1, fun h ↦ ?_⟩
  rw [h, min_eq_right zero_le_one]

variable (Sinf Sfin) in
/-- The approximation class of `β ∈ K` at side `1 / N`: the class `TauCeti.profileClass` of its
family of local approximation factors. When `β` is none of the targets it labels the cell of side
`1 / N` containing the logarithmic profile `log Λ_v(β) / log Λ(β)` of the local factors; when `β`
is the target at a place `v`, it is the corner `N • e v` of the simplex. -/
noncomputable def approxClass (N : ℕ) (β : K) : Sinf ⊕ Sfin → ℕ :=
  TauCeti.profileClass N (approxFactor Sinf Sfin w α β)

theorem approxClass_def (N : ℕ) (β : K) :
    approxClass Sinf Sfin w α N β = TauCeti.profileClass N (approxFactor Sinf Sfin w α β) :=
  (rfl)

/-- When `β` is none of the targets, its approximation class is the label of the logarithmic
profile of its local approximation factors. -/
theorem approxClass_of_forall_algebraMap_ne (N : ℕ) {β : K}
    (h : ∀ a, algebraMap K F β ≠ α (sPlaceAbsValue Sinf Sfin a)) :
    approxClass Sinf Sfin w α N β =
      TauCeti.cellIndex N (TauCeti.logProfile (approxFactor Sinf Sfin w α β)) :=
  TauCeti.profileClass_of_forall_ne_zero fun a ↦ (approxFactor_eq_zero_iff w α β a).not.mpr (h a)

/-- When `β` is the target at some place, its approximation class is the corner `N • e a` of the
simplex at a place `a` where `β` is the target. -/
theorem approxClass_of_exists_algebraMap_eq [DecidableEq (Sinf ⊕ Sfin)] (N : ℕ) {β : K}
    (h : ∃ a, algebraMap K F β = α (sPlaceAbsValue Sinf Sfin a)) :
    ∃ a, algebraMap K F β = α (sPlaceAbsValue Sinf Sfin a) ∧
      approxClass Sinf Sfin w α N β = Pi.single a N := by
  simp_rw [← approxFactor_eq_zero_iff w α β] at h ⊢
  exact TauCeti.profileClass_of_exists_eq_zero N h

/-- At most `(N + |S|).choose |S|` approximation classes occur, where `|S|` is the number of
places of `Sinf` and `Sfin`. -/
theorem ncard_image_approxClass_le (X : Set K) (N : ℕ) :
    (approxClass Sinf Sfin w α N '' X).ncard ≤
      (N + (#Sinf + #Sfin)).choose (#Sinf + #Sfin) := by
  have h := TauCeti.ncard_image_profileClass_le (X := X) (approxFactor Sinf Sfin w α)
    (fun β _ ↦ approxFactor_nonneg w α β) (fun β _ ↦ approxFactor_le_one w α β) N
  simpa only [Fintype.card_sum, Fintype.card_coe, ← approxClass_def] using h

end NumberField

/-! ### Tests -/

/-- The classes are cells of the simplex, not of the cube: the constant point `1` of the unit
square has a label summing to `2` at `N = 1`. Without `∑ a, y a ≤ 1` the labels are the
`(N + 1) ^ card A` cells of the cube, `4` against `3` at `N = 1` and `card A = 2`. -/
example : ¬ ∑ a, TauCeti.cellIndex 1 (fun _ : Fin 2 ↦ (1 : ℝ)) a ≤ 1 := by
  norm_num [TauCeti.cellIndex_apply, Fin.sum_univ_two]

/-- The count of labels at `N = 1` and `card A = 2`. -/
example : {c : Fin 2 → ℕ | ∑ a, c a ≤ 1}.ncard = 3 := by
  rw [TauCeti.ncard_setOf_sum_le]
  decide

/-- The upper half of (6.9) is attained, so its exponent is not off by one: for the single value
`f = 1 / 4` the profile is `1`, the label at `N = 2` is `2`, and the bound is an equality. -/
example : (∏ _b : Fin 1, (1 / 4 : ℝ)) ^
    ((TauCeti.cellIndex 2 (TauCeti.logProfile fun _ : Fin 1 ↦ (1 / 4 : ℝ)) 0 : ℝ) / 2) = 1 / 4 := by
  have hprof : TauCeti.logProfile (fun _ : Fin 1 ↦ (1 / 4 : ℝ)) 0 = 1 := by
    rw [TauCeti.logProfile_apply, Fin.prod_univ_one]
    exact div_self (Real.log_neg (by norm_num) (by norm_num)).ne
  rw [TauCeti.cellIndex_apply, hprof]
  norm_num
