/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Central fibers of Laurent root factorizations

For an analytic polynomial family with nonzero central fiber, a complete Laurent
factorization off the origin determines the central fiber, including multiplicities.
Branches with negative exponents escape to infinity and contribute only a nonzero scalar;
branches with positive exponents tend to zero; branches with exponent zero tend to their
amplitude values. The exponent of the leading scalar balances the sum of the pole exponents.

This applies to the divided monomial deformation of a Lazard evaluation: its central fiber
is nonzero even when the ordinary fiber is nullified. It identifies all finite branch limits
with that evaluation's root multiset, without assuming a root count or a matching at the
center. Repeated limits and an empty family of branches are allowed. The scalar balance uses
Mathlib’s `AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero`.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.2, proof of Theorem 5.1.
-/

public section

open Filter Polynomial Topology

namespace TauCeti

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  {F : 𝕜 → Polynomial 𝕜} {d : ℕ} {a : ℤ} {e : ι → ℤ}
  {u : 𝕜 → 𝕜} {w : ι → 𝕜 → 𝕜}

/-- A complete Laurent root factorization of an analytic polynomial family with nonzero
central fiber determines its factorization at the origin. Only the amplitudes of pole
branches are required to be nonzero at the origin. Branches with nonnegative
exponents remain as roots. Negative exponents contribute their nonzero unit values to the
scalar, and their sum cancels the exponent of the original scalar. -/
theorem eq_C_mul_prod_of_laurent
    (hF : ∀ j ≤ d, AnalyticAt 𝕜 (fun y ↦ (F y).coeff j) 0)
    (hdeg : ∀ᶠ y in 𝓝 (0 : 𝕜), (F y).natDegree ≤ d) (hF0 : F 0 ≠ 0)
    (hu : AnalyticAt 𝕜 u 0) (hu0 : u 0 ≠ 0)
    (hw : ∀ i, AnalyticAt 𝕜 (w i) 0) (hw0 : ∀ i, e i < 0 → w i 0 ≠ 0)
    (hfac : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      F y = C (y ^ a * u y) * ∏ i, (X - C (y ^ e i * w i y))) :
    a + ∑ i, min (e i) 0 = 0 ∧
      F 0 = C (u 0 * ∏ i ∈ Finset.univ.filter (fun i ↦ e i < 0), -(w i 0)) *
        ∏ i ∈ Finset.univ.filter (fun i ↦ 0 ≤ e i),
          (X - C (if e i = 0 then w i 0 else 0)) := by
  classical
  -- Clear each pole inside its linear factor, retaining its scalar power separately.
  let H (i : ι) (y : 𝕜) : Polynomial 𝕜 :=
    if e i < 0 then C (y ^ (-e i).toNat) * X - C (w i y)
    else X - C (y ^ (e i).toNat * w i y)
  have hlin (i : ι) (y : 𝕜) (hy : y ≠ 0) :
      X - C (y ^ e i * w i y) = C (y ^ min (e i) 0) * H i y := by
    by_cases hi : e i < 0
    · have hn : ((-e i).toNat : ℤ) = -e i := Int.toNat_of_nonneg (by omega)
      have hp : y ^ e i * y ^ (-e i).toNat = 1 := by
        rw [← zpow_natCast, hn, ← zpow_add₀ hy]
        simp
      simp only [H, ite_eq_left hi, min_eq_left hi.le, mul_sub, ← mul_assoc, ← C_mul, hp,
        C_1, one_mul]
    · simp [H, hi, min_eq_right (by omega : 0 ≤ e i),
        ← zpow_natCast, max_eq_left (by omega : 0 ≤ e i)]
  have hrewrite : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      F y = C (y ^ (a + ∑ i, min (e i) 0) * u y) * ∏ i, H i y := by
    filter_upwards [hfac, self_mem_nhdsWithin] with y hy hy0
    have hy0' : y ≠ 0 := by simpa using hy0
    rw [hy]
    simp_rw [hlin _ _ hy0']
    have hpower (s : Finset ι) : (∏ i ∈ s, y ^ min (e i) 0) =
        y ^ (∑ i ∈ s, min (e i) 0) := by
      induction s using Finset.induction_on with
      | empty => simp
      | insert i s hi ih => simp [hi, ih, zpow_add₀ hy0']
    rw [Finset.prod_mul_distrib, ← map_prod, hpower, ← mul_assoc, ← C_mul,
      zpow_add₀ hy0']
    congr 1
    simp [mul_comm, mul_assoc]
  have hH0 (i : ι) : H i 0 =
      if e i < 0 then C (-(w i 0))
      else X - C (if e i = 0 then w i 0 else 0) := by
    by_cases hi : e i < 0
    · have hn : (-e i).toNat ≠ 0 := by omega
      simp [H, hi, zero_pow hn]
    · by_cases he : e i = 0
      · simp [H, he]
      · have hn : (e i).toNat ≠ 0 := by omega
        simp [H, hi, he, zero_pow hn]
  have hHne : (∏ i, H i 0) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [hH0]
    split_ifs with hi he
    · exact C_ne_zero.mpr (neg_ne_zero.mpr (hw0 i hi))
    · exact X_sub_C_ne_zero _
    · exact X_sub_C_ne_zero _
  have hFA (z : 𝕜) : AnalyticAt 𝕜 (fun y ↦ (F y).eval z) 0 := by
    exact (Polynomial.analyticAt_eval_of_analyticAt_coeff hF hdeg z).comp_of_eq
      (analyticAt_id.prod analyticAt_const) (by simp)
  have hHA (z : 𝕜) : AnalyticAt 𝕜 (fun y ↦ u y * (∏ i, H i y).eval z) 0 := by
    simp only [eval_prod]
    apply hu.mul
    refine Finset.analyticAt_fun_prod _ fun i _ ↦ ?_
    have hid : AnalyticAt 𝕜 (fun y : 𝕜 ↦ y) 0 := analyticAt_id
    have hconst : AnalyticAt 𝕜 (fun _ : 𝕜 ↦ z) 0 := analyticAt_const
    by_cases hi : e i < 0
    · simpa [H, hi] using ((hid.fun_pow (-e i).toNat).fun_mul hconst).fun_sub (hw i)
    · simpa [H, hi] using hconst.fun_sub ((hid.fun_pow (e i).toNat).fun_mul (hw i))
  -- At a common nonroot, uniqueness of Laurent order forces the scalar exponent to vanish.
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset ((F 0) * ∏ i, H i 0).roots.toFinset
  have hz' : (F 0).eval z * (∏ i, H i 0).eval z ≠ 0 := by
    simpa only [Multiset.mem_toFinset, mem_roots (mul_ne_zero hF0 hHne), IsRoot,
      eval_mul] using hz
  have hbalance : a + ∑ i, min (e i) 0 = 0 := by
    apply AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero
      (f := fun y ↦ (F y).eval z) (z₀ := (0 : 𝕜))
    · refine ⟨_, hHA z, mul_ne_zero hu0 (mul_ne_zero_iff.mp hz').2, ?_⟩
      filter_upwards [hrewrite] with y hy
      simp only [hy, eval_mul, eval_C, sub_zero, smul_eq_mul]
      simp [mul_comm, mul_left_comm, mul_assoc]
    · exact ⟨_, hFA z, (mul_ne_zero_iff.mp hz').1, by simp⟩
  -- With the exponent removed, analytic identities extend to the central fiber.
  have hcentral : F 0 = C (u 0) * ∏ i, H i 0 := by
    apply Polynomial.funext
    intro z
    have heq : ∀ᶠ y in 𝓝[≠] (0 : 𝕜), (F y).eval z =
        u y * (∏ i, H i y).eval z := by
      filter_upwards [hrewrite] with y hy
      simp [hy, hbalance]
    simpa only [eval_mul, eval_C] using Filter.EventuallyEq.eq_of_nhds
      (((hFA z).frequently_eq_iff_eventually_eq (hHA z)).mp heq.frequently)
  refine ⟨hbalance, ?_⟩
  rw [hcentral]
  -- Separate the constant factors left by poles from the surviving linear factors.
  have hsplit := Finset.prod_filter_mul_prod_filter_not (s := Finset.univ)
    (p := fun i ↦ e i < 0) (f := fun i ↦ H i 0)
  rw [← hsplit]
  simp_rw [hH0]
  have hneg : (∏ i ∈ Finset.univ.filter (fun i ↦ e i < 0),
      if e i < 0 then C (-(w i 0)) else X - C (if e i = 0 then w i 0 else 0)) =
      C (∏ i ∈ Finset.univ.filter (fun i ↦ e i < 0), -(w i 0)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i hi ↦ ite_eq_left (Finset.mem_filter.mp hi).2
  have hpos : (∏ i ∈ Finset.univ.filter (fun i ↦ ¬ e i < 0),
      if e i < 0 then C (-(w i 0)) else X - C (if e i = 0 then w i 0 else 0)) =
      ∏ i ∈ Finset.univ.filter (fun i ↦ 0 ≤ e i),
        (X - C (if e i = 0 then w i 0 else 0)) := by
    simp only [not_lt]
    exact Finset.prod_congr rfl fun i hi ↦ ite_eq_right (not_lt.mpr (Finset.mem_filter.mp hi).2)
  rw [hneg, hpos, ← mul_assoc, ← C_mul]

/-- The root multiset of the nonzero central fiber consists precisely of the finite Laurent
branch limits, with each label counted once. Coincident limits retain their multiplicity. -/
theorem roots_eq_map_of_laurent
    (hF : ∀ j ≤ d, AnalyticAt 𝕜 (fun y ↦ (F y).coeff j) 0)
    (hdeg : ∀ᶠ y in 𝓝 (0 : 𝕜), (F y).natDegree ≤ d) (hF0 : F 0 ≠ 0)
    (hu : AnalyticAt 𝕜 u 0) (hu0 : u 0 ≠ 0)
    (hw : ∀ i, AnalyticAt 𝕜 (w i) 0) (hw0 : ∀ i, e i < 0 → w i 0 ≠ 0)
    (hfac : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      F y = C (y ^ a * u y) * ∏ i, (X - C (y ^ e i * w i y))) :
    (F 0).roots = (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
      (fun i ↦ if e i = 0 then w i 0 else 0) := by
  classical
  rw [(eq_C_mul_prod_of_laurent hF hdeg hF0 hu hu0 hw hw0 hfac).2,
    roots_C_mul _ (mul_ne_zero hu0 (Finset.prod_ne_zero_iff.mpr
      fun i hi ↦ neg_ne_zero.mpr (hw0 i (Finset.mem_filter.mp hi).2))),
    roots_prod _ _ (Finset.prod_ne_zero_iff.mpr fun i _ ↦ X_sub_C_ne_zero _)]
  simp only [roots_X_sub_C, Multiset.bind_singleton]

end TauCeti
