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
Mathlib’s `AnalyticAt.unique_eventuallyEq_zpow_smul_ne_zero`.

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

omit [Fintype ι] in
/-- A pole branch `y ^ e * w` of negative exponent is cleared inside its linear factor, leaving the
scalar `y ^ e` outside; the cleared factors `H i y` are analytic at the origin and take an
explicit value there. -/
private theorem exists_clearing (hw : ∀ i, AnalyticAt 𝕜 (w i) 0) :
    ∃ H : ι → 𝕜 → Polynomial 𝕜,
      (∀ i y, y ≠ 0 → X - C (y ^ e i * w i y) = C (y ^ min (e i) 0) * H i y) ∧
      (∀ i, H i 0 = if e i < 0 then C (-(w i 0)) else X - C (if e i = 0 then w i 0 else 0)) ∧
      ∀ i z, AnalyticAt 𝕜 (fun y ↦ (H i y).eval z) 0 := by
  classical
  refine ⟨fun i y ↦ if e i < 0 then C (y ^ (-e i).toNat) * X - C (w i y)
    else X - C (y ^ (e i).toNat * w i y), ?_, ?_, ?_⟩
  · intro i y hy
    by_cases hi : e i < 0
    · have hn : ((-e i).toNat : ℤ) = -e i := Int.toNat_of_nonneg (by omega)
      have hp : y ^ e i * y ^ (-e i).toNat = 1 := by
        rw [← zpow_natCast, hn, ← zpow_add₀ hy]
        simp
      simp only [ite_eq_left hi, min_eq_left hi.le, mul_sub, ← mul_assoc, ← C_mul, hp,
        C_1, one_mul]
    · simp [hi, min_eq_right (by omega : 0 ≤ e i),
        ← zpow_natCast, max_eq_left (by omega : 0 ≤ e i)]
  · intro i
    by_cases hi : e i < 0
    · have hn : (-e i).toNat ≠ 0 := by omega
      simp [hi, zero_pow hn]
    · by_cases he : e i = 0
      · simp [he]
      · have hn : (e i).toNat ≠ 0 := by omega
        simp [hi, he, zero_pow hn]
  · intro i z
    have hid : AnalyticAt 𝕜 (fun y : 𝕜 ↦ y) 0 := analyticAt_id
    have hconst : AnalyticAt 𝕜 (fun _ : 𝕜 ↦ z) 0 := analyticAt_const
    by_cases hi : e i < 0
    · simpa [hi] using ((hid.fun_pow (-e i).toNat).fun_mul hconst).fun_sub (hw i)
    · simpa [hi] using hconst.fun_sub ((hid.fun_pow (e i).toNat).fun_mul (hw i))

/-- Pulling the scalar powers `y ^ min (e i) 0` out of the factors of the Laurent factorization. -/
private theorem eventually_eq_C_mul_prod_clearing {H : ι → 𝕜 → Polynomial 𝕜}
    (hlin : ∀ i y, y ≠ 0 → X - C (y ^ e i * w i y) = C (y ^ min (e i) 0) * H i y)
    (hfac : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      F y = C (y ^ a * u y) * ∏ i, (X - C (y ^ e i * w i y))) :
    ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      F y = C (y ^ (a + ∑ i, min (e i) 0) * u y) * ∏ i, H i y := by
  classical
  filter_upwards [hfac, self_mem_nhdsWithin] with y hy hy0
  have hy0' : y ≠ 0 := by simpa using hy0
  rw [hy]
  simp_rw [hlin _ _ hy0']
  have hpower (s : Finset ι) : (∏ i ∈ s, y ^ min (e i) 0) =
      y ^ (∑ i ∈ s, min (e i) 0) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp [hi, ih, zpow_add₀ hy0']
  rw [Finset.prod_mul_distrib, ← map_prod, hpower, ← mul_assoc, ← C_mul, zpow_add₀ hy0']
  congr 1
  simp [mul_comm, mul_assoc]

/-- The cleared factors do not vanish identically at the origin. -/
private theorem prod_clearing_ne_zero {H : ι → 𝕜 → Polynomial 𝕜}
    (hw0 : ∀ i, e i < 0 → w i 0 ≠ 0)
    (hH0 : ∀ i, H i 0 =
      if e i < 0 then C (-(w i 0)) else X - C (if e i = 0 then w i 0 else 0)) :
    (∏ i, H i 0) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
  rw [hH0]
  split_ifs with hi he
  · exact C_ne_zero.mpr (neg_ne_zero.mpr (hw0 i hi))
  · exact X_sub_C_ne_zero _
  · exact X_sub_C_ne_zero _

/-- Uniqueness of the Laurent order at a common nonroot forces the scalar exponent to vanish, and
then the analytic identity extends to the central fiber. -/
private theorem balance_and_central_of_clearing {H : ι → 𝕜 → Polynomial 𝕜}
    (hF : ∀ j ≤ d, AnalyticAt 𝕜 (fun y ↦ (F y).coeff j) 0)
    (hdeg : ∀ᶠ y in 𝓝 (0 : 𝕜), (F y).natDegree ≤ d) (hF0 : F 0 ≠ 0)
    (hu : AnalyticAt 𝕜 u 0) (hu0 : u 0 ≠ 0) (hHne : (∏ i, H i 0) ≠ 0)
    (hHan : ∀ i z, AnalyticAt 𝕜 (fun y ↦ (H i y).eval z) 0)
    (hrewrite : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      F y = C (y ^ (a + ∑ i, min (e i) 0) * u y) * ∏ i, H i y) :
    a + ∑ i, min (e i) 0 = 0 ∧ F 0 = C (u 0) * ∏ i, H i 0 := by
  classical
  have hFA (z : 𝕜) : AnalyticAt 𝕜 (fun y ↦ (F y).eval z) 0 :=
    (Polynomial.analyticAt_eval_of_analyticAt_coeff hF hdeg z).comp_of_eq
      (analyticAt_id.prod analyticAt_const) (by simp)
  have hHA (z : 𝕜) : AnalyticAt 𝕜 (fun y ↦ u y * (∏ i, H i y).eval z) 0 := by
    simp only [eval_prod]
    exact hu.mul (Finset.analyticAt_fun_prod _ fun i _ ↦ hHan i z)
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset ((F 0) * ∏ i, H i 0).roots.toFinset
  have hz' : (F 0).eval z * (∏ i, H i 0).eval z ≠ 0 := by
    simpa only [Multiset.mem_toFinset, mem_roots (mul_ne_zero hF0 hHne), IsRoot,
      eval_mul] using hz
  have hbalance : a + ∑ i, min (e i) 0 = 0 := by
    apply AnalyticAt.unique_eventuallyEq_zpow_smul_ne_zero
      (f := fun y ↦ (F y).eval z) (z₀ := (0 : 𝕜))
    · refine ⟨_, hHA z, mul_ne_zero hu0 (mul_ne_zero_iff.mp hz').2, ?_⟩
      filter_upwards [hrewrite] with y hy
      simp only [hy, eval_mul, eval_C, sub_zero, smul_eq_mul]
      simp [mul_comm, mul_left_comm, mul_assoc]
    · exact ⟨_, hFA z, (mul_ne_zero_iff.mp hz').1, by simp⟩
  refine ⟨hbalance, Polynomial.funext fun z ↦ ?_⟩
  have heq : ∀ᶠ y in 𝓝[≠] (0 : 𝕜), (F y).eval z = u y * (∏ i, H i y).eval z := by
    filter_upwards [hrewrite] with y hy
    simp [hy, hbalance]
  simpa only [eval_mul, eval_C] using Filter.EventuallyEq.eq_of_nhds
    (((hFA z).frequently_eq_iff_eventually_eq (hHA z)).mp heq.frequently)

/-- Separating the constant factors left by poles from the surviving linear factors. -/
private theorem C_mul_prod_clearing_zero {H : ι → 𝕜 → Polynomial 𝕜}
    (hH0 : ∀ i, H i 0 =
      if e i < 0 then C (-(w i 0)) else X - C (if e i = 0 then w i 0 else 0)) :
    C (u 0) * ∏ i, H i 0 =
      C (u 0 * ∏ i ∈ Finset.univ.filter (fun i ↦ e i < 0), -(w i 0)) *
        ∏ i ∈ Finset.univ.filter (fun i ↦ 0 ≤ e i),
          (X - C (if e i = 0 then w i 0 else 0)) := by
  classical
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
  obtain ⟨H, hlin, hH0, hHan⟩ := exists_clearing (e := e) hw
  have hHne := prod_clearing_ne_zero hw0 hH0
  obtain ⟨hbalance, hcentral⟩ := balance_and_central_of_clearing hF hdeg hF0 hu hu0 hHne hHan
    (eventually_eq_C_mul_prod_clearing hlin hfac)
  exact ⟨hbalance, by rw [hcentral, C_mul_prod_clearing_zero hH0]⟩

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
