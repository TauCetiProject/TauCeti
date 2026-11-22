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

The linear expansion coefficient is the linear coefficient of `γ`, but from degree `2` on the
expansion coefficients depend on `F` and not only on the power series `γ(T)`. On a `p`-typical law,
`p`-typicality of a curve is read off its expansion (see
`TauCeti.RingTheory.FormalGroup.Typical.Expansion`).

## Main definitions and results

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

/-- The partial sums `∑^F_{0 < j ≤ n} cⱼ Tʲ` of the expansion of `γ`, defined together with the
coefficients `cⱼ`. -/
private noncomputable def expansionPartialSum (γ : F.Curve) : ℕ → F.Curve
  | 0 => 0
  | n + 1 =>
      let s := expansionPartialSum γ n
      s + F.monomialCurve (n + 1) n.succ_ne_zero (coeff (n + 1) (γ - s).toPowerSeries)

/-- The **expansion coefficients** of a curve `γ` on a formal group law `F`: the coefficient `cₙ`
is the degree-`n` coefficient of the residual `γ - ∑^F_{0 < j < n} cⱼ Tʲ`, and by convention
`c₀ = 0`. When `F` is commutative these are the unique `cₙ ∈ R`, `n ≥ 1`, with
`γ(T) = ∑^F_{n ≥ 1} cₙ Tⁿ` (`FormalGroup.Curve.forall_coeff_sum_monomialCurve_eq_iff`). -/
noncomputable def expansionCoeff (γ : F.Curve) (n : ℕ) : R :=
  coeff n (γ - expansionPartialSum γ (n - 1)).toPowerSeries

private theorem expansionPartialSum_succ (γ : F.Curve) (n : ℕ) :
    expansionPartialSum γ (n + 1) = expansionPartialSum γ n +
      F.monomialCurve (n + 1) n.succ_ne_zero (γ.expansionCoeff (n + 1)) := by
  rw [expansionPartialSum, expansionCoeff, Nat.add_sub_cancel]

/-- By convention, the expansion has no constant term. -/
@[simp]
theorem expansionCoeff_zero (γ : F.Curve) : γ.expansionCoeff 0 = 0 := by
  simp [expansionCoeff, expansionPartialSum]

/-- The linear expansion coefficient of a curve is its linear coefficient. -/
@[simp]
theorem expansionCoeff_one (γ : F.Curve) : γ.expansionCoeff 1 = coeff 1 γ.toPowerSeries := by
  simp [expansionCoeff, expansionPartialSum]

/-- The residual `γ - ∑^F_{0 < j ≤ n} cⱼ Tʲ` vanishes up to degree `n`. -/
private theorem coeff_sub_expansionPartialSum [F.IsComm] (γ : F.Curve) (n : ℕ) :
    ∀ k ≤ n, coeff k (γ - expansionPartialSum γ n).toPowerSeries = 0 := by
  induction n with
  | zero =>
    intro k hk
    rw [Nat.le_zero.mp hk]
    exact Curve.coeff_zero_toPowerSeries _
  | succ n ih =>
    intro k hk
    rw [expansionPartialSum]
    exact Curve.coeff_sub_add_monomialCurve_eq_zero n.succ_ne_zero
      (fun i hi ↦ ih i (Nat.lt_succ_iff.mp hi)) hk

variable [F.IsComm]

private theorem expansionPartialSum_eq_sum (γ : F.Curve) (n : ℕ) :
    expansionPartialSum γ n =
      ∑ j ∈ range n, F.monomialCurve (j + 1) j.succ_ne_zero (γ.expansionCoeff (j + 1)) := by
  induction n with
  | zero => simp [expansionPartialSum]
  | succ n ih => rw [expansionPartialSum_succ, sum_range_succ, ih]

/-- The expansion coefficient in degree `n + 1` is the degree-`n + 1` coefficient of the residual
after subtracting the formal-group sum of the expansion terms of lower degree. -/
theorem expansionCoeff_succ (γ : F.Curve) (n : ℕ) :
    γ.expansionCoeff (n + 1) = coeff (n + 1)
      (γ - ∑ j ∈ range n,
        F.monomialCurve (j + 1) j.succ_ne_zero (γ.expansionCoeff (j + 1))).toPowerSeries := by
  rw [expansionCoeff, Nat.add_sub_cancel, expansionPartialSum_eq_sum]

/-- **Existence of the expansion.** The formal-group sum `∑^F_{0 < n ≤ N} cₙ Tⁿ` of the expansion
terms of `γ` agrees with `γ` up to degree `N`. -/
theorem coeff_sum_expansionCoeff (γ : F.Curve) {N k : ℕ} (hk : k ≤ N) :
    coeff k (∑ j ∈ range N,
      F.monomialCurve (j + 1) j.succ_ne_zero (γ.expansionCoeff (j + 1))).toPowerSeries =
      coeff k γ.toPowerSeries := by
  rw [← expansionPartialSum_eq_sum]
  have h := Curve.coeff_add_eq_left_of_forall_lt_coeff_eq_zero (expansionPartialSum γ N)
    (γ - expansionPartialSum γ N) (Nat.lt_succ_of_le hk)
    fun i hi ↦ coeff_sub_expansionPartialSum γ N i (Nat.lt_succ_iff.mp hi)
  rw [add_sub_cancel] at h
  exact h.symm

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
  · induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hsum : ∑ j ∈ range n, F.monomialCurve (j + 1) j.succ_ne_zero (c (j + 1)) =
          ∑ j ∈ range n, F.monomialCurve (j + 1) j.succ_ne_zero (γ.expansionCoeff (j + 1)) :=
        sum_congr rfl fun j hj ↦ by rw [ih j (mem_range.mp hj)]
      have h₁ := hc (n + 1) (n + 1) le_rfl
      have h₂ := γ.coeff_sum_expansionCoeff (le_refl (n + 1))
      rw [sum_range_succ, hsum, Curve.coeff_add_monomialCurve_self] at h₁
      rw [sum_range_succ, Curve.coeff_add_monomialCurve_self] at h₂
      exact add_left_cancel (h₁.trans h₂.symm)
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

/-- Expansion coefficients commute with base change. -/
@[simp]
theorem map_expansionCoeff (φ : R →+* S) (γ : F.Curve) (n : ℕ) :
    φ (γ.expansionCoeff n) = (Curve.map φ γ).expansionCoeff n := by
  rcases n with _ | n
  · simp
  refine ((Curve.map φ γ).forall_coeff_sum_monomialCurve_eq_iff (fun m ↦ φ (γ.expansionCoeff m))).1
    (fun N k hk ↦ ?_) n
  rw [← map_toPowerSeries_sum_monomialCurve φ rfl _ (fun j ↦ j + 1) (fun j ↦ j.succ_ne_zero)
      (fun j ↦ γ.expansionCoeff (j + 1)) _ fun _ _ ↦ rfl,
    PowerSeries.coeff_map, γ.coeff_sum_expansionCoeff hk, Curve.toPowerSeries_map,
    PowerSeries.coeff_map]

end Curve

end FormalGroup
