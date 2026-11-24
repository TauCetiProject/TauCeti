/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Curve.Arithmetic

/-!
# Formal-group expansions of curves

Let `F` be a commutative formal group law over a commutative ring `R`. Every curve `γ` on `F` has a
unique expansion `γ(T) = ∑^F_{n ≥ 1} cₙ Tⁿ` as an infinite formal-group sum of monomial curves
(Ravenel, proof of Lemma A2.1.26): the coefficient `cₙ` (`FormalGroup.Curve.expansionCoeff`) is the
degree-`n` coefficient of the residual `γ - ∑^F_{0 < j < n} cⱼ Tʲ`, which vanishes below degree `n`.
Since the `N`-th partial sum agrees with `γ` up to degree `N`, the infinite formal-group sum is
stated coefficientwise through its finite partial sums
(`FormalGroup.Curve.coeff_sum_expansionCoeff`), and any family of coefficients with this property
is the expansion of `γ` (`FormalGroup.Curve.forall_coeff_sum_monomialCurve_eq_iff`). The expansion
determines the curve and commutes with base change.

The construction is carried out once along an arbitrary sequence of nonzero degrees `d`
(`FormalGroup.Curve.expansionCoeffAlong`): the `n`-th coefficient is the degree-`d n` coefficient
of the residual after subtracting the terms of degrees `d j`, `j < n`. The expansion `cₙ` uses the
degrees `n + 1`, and the `p`-typical expansion coefficients `FormalGroup.Curve.pTypicalCoeff` use
the degrees `p ^ n`.

The linear expansion coefficient is the linear coefficient of `γ`, but from degree `2` on the
expansion coefficients depend on `F` and not only on the power series `γ(T)`. On a `p`-typical law,
`p`-typicality of a curve is read off its expansion (see
`TauCeti.RingTheory.FormalGroup.Typical.Expansion`).

## Main definitions and results

* `FormalGroup.Curve.expansionCoeffAlong`: the coefficients of the expansion along a sequence of
  degrees `d`, with the recursion `FormalGroup.Curve.expansionCoeffAlong_eq_coeff_sub_sum`,
  uniqueness `FormalGroup.Curve.eq_expansionCoeffAlong_of_coeff_eq_coeff_sum` and base change
  `FormalGroup.Curve.map_expansionCoeffAlong`.
* `FormalGroup.Curve.expansionCoeff`: the coefficients `cₙ` of `γ = ∑^F cₙ Tⁿ`.
* `FormalGroup.Curve.coeff_sum_expansionCoeff`: `γ` agrees with `∑^F_{n ≤ N} cₙ Tⁿ` up to
  degree `N`.
* `FormalGroup.Curve.forall_coeff_sum_monomialCurve_eq_iff`: uniqueness of the expansion.
* `FormalGroup.Curve.expansionCoeff_injective`, `FormalGroup.Curve.map_expansionCoeff`.
* `FormalGroup.Curve.expansionCoeff_monomialCurve`: the expansion of a monomial curve.

## References

* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Academic Press (1986),
  Appendix A2, Lemma A2.1.26 and its proof.
-/

public section

open Finset
open PowerSeries (coeff)

namespace FormalGroup

namespace Curve

variable {R S : Type*} [CommRing R] [CommRing S] {F : FormalGroup R}

/-! ### Expansions along a sequence of degrees -/

section Along

variable (γ : F.Curve) (d : ℕ → ℕ) (hd : ∀ n, d n ≠ 0)

/-- The partial sums `∑^F_{j < n} aⱼ T^(d j)` of the expansion of `γ` along the degrees `d`,
defined together with the coefficients `aⱼ = γ.expansionCoeffAlong d hd j`: the term of degree
`d n` is the degree-`d n` term of the residual `γ - ∑^F_{j < n} aⱼ T^(d j)`. -/
noncomputable def expansionPartialSumAlong : ℕ → F.Curve
  | 0 => 0
  | n + 1 =>
      let s := expansionPartialSumAlong n
      s + F.monomialCurve (d n) (hd n) (coeff (d n) (γ - s).toPowerSeries)

/-- The **expansion coefficients of a curve along a sequence of degrees** `d`: `aₙ` is the
degree-`d n` coefficient of the residual `γ - ∑^F_{j < n} aⱼ T^(d j)`. For `d n = n + 1` these are
the expansion coefficients `FormalGroup.Curve.expansionCoeff`; for `d n = p ^ n` they are the
`p`-typical expansion coefficients `FormalGroup.Curve.pTypicalCoeff`. -/
noncomputable def expansionCoeffAlong (n : ℕ) : R :=
  coeff (d n) (γ - γ.expansionPartialSumAlong d hd n).toPowerSeries

/-- The empty partial sum along `d` is the zero curve. -/
@[simp]
theorem expansionPartialSumAlong_zero : γ.expansionPartialSumAlong d hd 0 = 0 := by
  rw [expansionPartialSumAlong]

/-- The first expansion coefficient along `d` is the degree-`d 0` coefficient of `γ`. -/
@[simp]
theorem expansionCoeffAlong_zero :
    γ.expansionCoeffAlong d hd 0 = coeff (d 0) γ.toPowerSeries := by
  simp [expansionCoeffAlong]

/-- The partial sum along `d` with `n + 1` terms adds the term `aₙ T^(d n)`. -/
theorem expansionPartialSumAlong_succ (n : ℕ) :
    γ.expansionPartialSumAlong d hd (n + 1) = γ.expansionPartialSumAlong d hd n +
      F.monomialCurve (d n) (hd n) (γ.expansionCoeffAlong d hd n) := by
  rw [expansionPartialSumAlong, expansionCoeffAlong]

/-- The partial sums along `d` commute with base change. -/
theorem map_expansionPartialSumAlong (φ : R →+* S) (n : ℕ) :
    Curve.map φ (γ.expansionPartialSumAlong d hd n) =
      (Curve.map φ γ).expansionPartialSumAlong d hd n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [expansionPartialSumAlong_succ, map_add, ih, map_monomialCurve, expansionCoeffAlong,
      ← PowerSeries.coeff_map, ← Curve.toPowerSeries_map, map_sub]

/-- The expansion coefficients along `d` commute with base change. -/
@[simp]
theorem map_expansionCoeffAlong (φ : R →+* S) (n : ℕ) :
    φ (γ.expansionCoeffAlong d hd n) = (Curve.map φ γ).expansionCoeffAlong d hd n := by
  simp only [expansionCoeffAlong, ← PowerSeries.coeff_map, ← Curve.toPowerSeries_map, map_sub,
    map_expansionPartialSumAlong]

variable {γ d hd}

/-- One peeling step: if the residual `γ - ∑^F_{j < n} aⱼ T^(d j)` vanishes below degree `d n`,
then the next residual vanishes up to degree `d n`. -/
theorem coeff_sub_expansionPartialSumAlong_succ_eq_zero [F.IsComm] {n : ℕ}
    (h : ∀ k < d n, coeff k (γ - γ.expansionPartialSumAlong d hd n).toPowerSeries = 0) {k : ℕ}
    (hk : k ≤ d n) : coeff k (γ - γ.expansionPartialSumAlong d hd (n + 1)).toPowerSeries = 0 :=
  coeff_sub_add_monomialCurve_eq_zero (hd n) h hk

variable [F.IsComm]

variable (γ d hd) in
/-- The partial sum along `d` with `n` terms is the formal-group sum `∑^F_{j < n} aⱼ T^(d j)`. -/
theorem expansionPartialSumAlong_eq_sum (n : ℕ) :
    γ.expansionPartialSumAlong d hd n =
      ∑ j ∈ range n, F.monomialCurve (d j) (hd j) (γ.expansionCoeffAlong d hd j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [expansionPartialSumAlong_succ, sum_range_succ, ih]

variable (γ d hd) in
/-- The defining recursion of the expansion coefficients along `d`: `aₙ` is the degree-`d n`
coefficient of `γ - ∑^F_{j < n} aⱼ T^(d j)`. -/
theorem expansionCoeffAlong_eq_coeff_sub_sum (n : ℕ) :
    γ.expansionCoeffAlong d hd n = coeff (d n)
      (γ - ∑ j ∈ range n, F.monomialCurve (d j) (hd j)
        (γ.expansionCoeffAlong d hd j)).toPowerSeries := by
  rw [expansionCoeffAlong, expansionPartialSumAlong_eq_sum]

/-- If the residual `γ - ∑^F_{j < n} aⱼ T^(d j)` vanishes below degree `d n`, then `γ` agrees with
`∑^F_{j < n} aⱼ T^(d j)` below degree `d n`. -/
theorem coeff_eq_coeff_sum_expansionCoeffAlong {n : ℕ}
    (h : ∀ k < d n, coeff k (γ - γ.expansionPartialSumAlong d hd n).toPowerSeries = 0) {k : ℕ}
    (hk : k < d n) :
    coeff k γ.toPowerSeries = coeff k
      (∑ j ∈ range n, F.monomialCurve (d j) (hd j)
        (γ.expansionCoeffAlong d hd j)).toPowerSeries := by
  rw [← expansionPartialSumAlong_eq_sum]
  have h' := coeff_add_eq_left_of_forall_lt_coeff_eq_zero (γ.expansionPartialSumAlong d hd n)
    (γ - γ.expansionPartialSumAlong d hd n) hk h
  rwa [add_sub_cancel] at h'

/-- **Uniqueness of expansions along `d`.** For a strictly increasing sequence of degrees `d`, if
`γ` agrees with `∑^F_{j < n} tⱼ T^(d j)` below degree `d n` for every `n`, then `t` is the family
of expansion coefficients of `γ` along `d`. -/
theorem eq_expansionCoeffAlong_of_coeff_eq_coeff_sum (hmono : StrictMono d) {t : ℕ → R}
    (h : ∀ n k, k < d n → coeff k γ.toPowerSeries = coeff k
      (∑ j ∈ range n, F.monomialCurve (d j) (hd j) (t j)).toPowerSeries) :
    t = γ.expansionCoeffAlong d hd := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    let s := ∑ j ∈ range n, F.monomialCurve (d j) (hd j) (t j)
    have hs : s = ∑ j ∈ range n, F.monomialCurve (d j) (hd j) (γ.expansionCoeffAlong d hd j) :=
      sum_congr rfl fun j hj ↦ by rw [ih j (mem_range.mp hj)]
    have hγ (i : ℕ) (hi : i ≤ d n) : coeff i γ.toPowerSeries =
        coeff i (s + F.monomialCurve (d n) (hd n) (t n)).toPowerSeries := by
      rw [h (n + 1) i (hi.trans_lt (hmono n.lt_succ_self)), sum_range_succ]
    rw [expansionCoeffAlong_eq_coeff_sub_sum, ← hs, coeff_sub_congr hγ fun _ _ ↦ rfl,
      add_sub_cancel_left]
    simp

end Along

/-! ### The expansion in all positive degrees -/

/-- The **expansion coefficients** of a curve `γ` on a formal group law `F`: the coefficient `cₙ`
is the degree-`n` coefficient of the residual `γ - ∑^F_{0 < j < n} cⱼ Tʲ`, and by convention
`c₀ = 0`. These are the expansion coefficients along the degrees `n + 1`, shifted by one. When `F`
is commutative they are the unique `cₙ ∈ R`, `n ≥ 1`, with `γ(T) = ∑^F_{n ≥ 1} cₙ Tⁿ`
(`FormalGroup.Curve.forall_coeff_sum_monomialCurve_eq_iff`). -/
noncomputable def expansionCoeff (γ : F.Curve) : ℕ → R
  | 0 => 0
  | n + 1 => γ.expansionCoeffAlong (· + 1) (fun j ↦ j.succ_ne_zero) n

/-- By convention, the expansion has no constant term. -/
@[simp]
theorem expansionCoeff_zero (γ : F.Curve) : γ.expansionCoeff 0 = 0 := by
  rw [expansionCoeff]

/-- The expansion coefficient in positive degree `n + 1` is the `n`-th expansion coefficient along
the degrees `j + 1`. -/
theorem expansionCoeff_add_one (γ : F.Curve) (n : ℕ) :
    γ.expansionCoeff (n + 1) = γ.expansionCoeffAlong (· + 1) (fun j ↦ j.succ_ne_zero) n := by
  rw [expansionCoeff]

/-- The linear expansion coefficient of a curve is its linear coefficient. -/
@[simp]
theorem expansionCoeff_one (γ : F.Curve) : γ.expansionCoeff 1 = coeff 1 γ.toPowerSeries := by
  simp [expansionCoeff_add_one]

/-- The residual `γ - ∑^F_{0 < j ≤ n} cⱼ Tʲ` vanishes up to degree `n`. -/
private theorem coeff_sub_expansionPartialSumAlong_add_one [F.IsComm] (γ : F.Curve) (n : ℕ) :
    ∀ k < n + 1, coeff k (γ - γ.expansionPartialSumAlong (· + 1)
      (fun j ↦ j.succ_ne_zero) n).toPowerSeries = 0 := by
  induction n with
  | zero =>
    intro k hk
    rw [Nat.lt_one_iff.mp hk]
    exact Curve.coeff_zero_toPowerSeries _
  | succ n ih =>
    intro k hk
    exact coeff_sub_expansionPartialSumAlong_succ_eq_zero (d := (· + 1)) ih (Nat.lt_succ_iff.mp hk)

variable [F.IsComm]

/-- The expansion coefficient in degree `n + 1` is the degree-`n + 1` coefficient of the residual
after subtracting the formal-group sum of the expansion terms of lower degree. -/
theorem expansionCoeff_add_one_eq_coeff_sub_sum (γ : F.Curve) (n : ℕ) :
    γ.expansionCoeff (n + 1) = coeff (n + 1)
      (γ - ∑ j ∈ range n,
        F.monomialCurve (j + 1) j.succ_ne_zero (γ.expansionCoeff (j + 1))).toPowerSeries := by
  simp only [expansionCoeff_add_one]
  exact γ.expansionCoeffAlong_eq_coeff_sub_sum _ _ n

/-- **Existence of the expansion.** The formal-group sum `∑^F_{0 < n ≤ N} cₙ Tⁿ` of the expansion
terms of `γ` agrees with `γ` up to degree `N`. -/
theorem coeff_sum_expansionCoeff (γ : F.Curve) {N k : ℕ} (hk : k ≤ N) :
    coeff k (∑ j ∈ range N,
      F.monomialCurve (j + 1) j.succ_ne_zero (γ.expansionCoeff (j + 1))).toPowerSeries =
      coeff k γ.toPowerSeries := by
  simp only [expansionCoeff_add_one]
  exact (coeff_eq_coeff_sum_expansionCoeffAlong (d := (· + 1))
    (coeff_sub_expansionPartialSumAlong_add_one γ N)
    (Nat.lt_succ_of_le hk)).symm

/-- **Uniqueness of the expansion.** A family `c` describes `γ` as the formal-group sum
`∑^F_{n ≥ 1} cₙ Tⁿ`, in the sense that each partial sum `∑^F_{0 < n ≤ N} cₙ Tⁿ` agrees with `γ` up
to degree `N`, if and only if `c` agrees with the expansion coefficients of `γ` in positive
degrees. -/
theorem forall_coeff_sum_monomialCurve_eq_iff (γ : F.Curve) (c : ℕ → R) :
    (∀ N, ∀ k ≤ N, coeff k (∑ j ∈ range N,
      F.monomialCurve (j + 1) j.succ_ne_zero (c (j + 1))).toPowerSeries =
        coeff k γ.toPowerSeries) ↔
      ∀ n, c (n + 1) = γ.expansionCoeff (n + 1) := by
  refine ⟨fun hc n ↦ ?_, fun hc N k hk ↦ ?_⟩
  · rw [expansionCoeff_add_one]
    exact congrFun (eq_expansionCoeffAlong_of_coeff_eq_coeff_sum (t := fun j ↦ c (j + 1))
      (fun _ _ h ↦ by omega) fun N k hk ↦ (hc N k (Nat.lt_succ_iff.mp hk)).symm) n
  · rw [← γ.coeff_sum_expansionCoeff hk]
    exact congrArg (fun s : F.Curve ↦ coeff k s.toPowerSeries)
      (sum_congr rfl fun j _ ↦ by rw [hc j])

/-- A curve is determined by its expansion coefficients. -/
theorem expansionCoeff_injective :
    Function.Injective (expansionCoeff : F.Curve → ℕ → R) := by
  intro γ δ h
  ext k : 2
  rw [← γ.coeff_sum_expansionCoeff (le_refl k), ← δ.coeff_sum_expansionCoeff (le_refl k), h]

/-- Two curves are equal if and only if their expansion coefficients agree. -/
@[simp]
theorem expansionCoeff_inj {γ δ : F.Curve} : γ.expansionCoeff = δ.expansionCoeff ↔ γ = δ :=
  expansionCoeff_injective.eq_iff

/-- The expansion of a monomial curve `c Tᵐ` is the single term `c Tᵐ`. -/
@[simp]
theorem expansionCoeff_monomialCurve {m : ℕ} (hm : m ≠ 0) (c : R) (n : ℕ) :
    (F.monomialCurve m hm c).expansionCoeff n = if n = m then c else 0 := by
  rcases n with _ | n
  · simp [hm.symm]
  refine (((F.monomialCurve m hm c).forall_coeff_sum_monomialCurve_eq_iff
    fun n ↦ if n = m then c else 0).1 (fun N k hk ↦ ?_) n).symm
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hm
  by_cases hmN : m < N
  · rw [sum_eq_single_of_mem m (mem_range.mpr hmN) fun j _ hj ↦ by simp [hj]]
    simp
  · rw [sum_eq_zero fun j hj ↦ by simp [show j ≠ m by grind]]
    simp [PowerSeries.coeff_X_pow, show k ≠ m + 1 by omega]

/-- The expansion of the zero curve vanishes. -/
@[simp]
theorem expansionCoeff_zero_curve : (0 : F.Curve).expansionCoeff = 0 := by
  funext n
  simpa using expansionCoeff_monomialCurve (F := F) one_ne_zero 0 n

/-- The expansion of the tautological curve `T` is the single term `T`. -/
@[simp]
theorem expansionCoeff_tautologicalCurve (n : ℕ) :
    F.tautologicalCurve.expansionCoeff n = if n = 1 then 1 else 0 := by
  rw [← monomialCurve_one, expansionCoeff_monomialCurve]

omit [F.IsComm] in
/-- Expansion coefficients commute with base change. -/
@[simp]
theorem map_expansionCoeff (φ : R →+* S) (γ : F.Curve) (n : ℕ) :
    φ (γ.expansionCoeff n) = (Curve.map φ γ).expansionCoeff n := by
  rcases n with _ | n
  · simp
  exact γ.map_expansionCoeffAlong _ _ φ n

end Curve

end FormalGroup
