/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Finsupp
public import Mathlib.RingTheory.PowerSeries.Expand
public import TauCeti.RingTheory.PowerSeries.PiTopology

/-!
# Products of expanded power series

For a family of power series `f c` and positive multipliers `m c`, this file computes the
coefficients of the product `∏ c, f c (X ^ m c)` of the expanded series
`PowerSeries.expand (m c) _ (f c)`. The `n`-th coefficient of a finite product is a sum over the
weighted antidiagonal `Finset.weightedFinsuppAntidiag s m n` of the assignments `l` supported in
`s` with `∑ c ∈ s, m c * l c = n`. When every `f c` has constant term `1`, factors with
`n < m c` do not change the `n`-th coefficient. So if only finitely many `m c` lie below each
bound, the infinite product converges in the coefficientwise topology
(`PowerSeries.WithPiTopology`), and each coefficient is that of a finite product.

## Main declarations

* `Finset.weightedFinsuppAntidiag s m n`: the assignments `l : ι →₀ ℕ` supported in `s` with
  `∑ c ∈ s, m c * l c = n`.
* `PowerSeries.coeff_prod_expand`: the `n`-th coefficient of `∏ c ∈ s, f c (X ^ m c)` is the sum
  over `l ∈ s.weightedFinsuppAntidiag m n` of `∏ c ∈ s, coeff (l c) (f c)`.
* `PowerSeries.coeff_prod_expand_of_subset`: adjoining factors with `n < m c` and constant term
  `1` does not change the `n`-th coefficient.
* `PowerSeries.X_pow_dvd_expand_sub_C_constantCoeff`: an expanded series agrees with its
  constant coefficient modulo the corresponding power of `X`.
* `PowerSeries.hasProd_expand`, `PowerSeries.multipliable_expand`,
  `PowerSeries.coeff_tprod_expand`: the infinite product of the expanded series and its
  coefficients, when `{c | m c ≤ n}` is finite for every `n`.
-/

public section

variable {ι : Type*}

namespace Finset

/-- The weighted antidiagonal: the assignments `l : ι →₀ ℕ` supported in `s` with
`∑ c ∈ s, m c * l c = n`. -/
noncomputable def weightedFinsuppAntidiag (s : Finset ι) (m : ι → ℕ+) (n : ℕ) :
    Finset (ι →₀ ℕ) :=
  {l ∈ s.finsupp fun _ ↦ range (n + 1) | ∑ c ∈ s, (m c : ℕ) * l c = n}

/-- A summand of `∑ c ∈ s, m c * l c = n` is at most `n`. -/
private theorem mul_le_of_sum_mul_eq {s : Finset ι} {m : ι → ℕ+} {n : ℕ} {l : ι →₀ ℕ}
    (h : ∑ c ∈ s, (m c : ℕ) * l c = n) {c : ι} (hc : c ∈ s) : (m c : ℕ) * l c ≤ n :=
  h ▸ single_le_sum (f := fun c ↦ (m c : ℕ) * l c) (by simp) hc

/-- An assignment lies in the weighted antidiagonal exactly when it is supported in `s` and has
weighted sum `n`. -/
@[simp]
theorem mem_weightedFinsuppAntidiag {s : Finset ι} {m : ι → ℕ+} {n : ℕ} {l : ι →₀ ℕ} :
    l ∈ s.weightedFinsuppAntidiag m n ↔ l.support ⊆ s ∧ ∑ c ∈ s, (m c : ℕ) * l c = n := by
  simp only [weightedFinsuppAntidiag, mem_filter, mem_finsupp_iff, mem_range]
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, fun c hc ↦ ?_⟩, h.2⟩⟩
  have hle := mul_le_of_sum_mul_eq h.2 hc
  have := Nat.le_mul_of_pos_left (l c) (m c).pos
  omega

/-- Every summand `m c * l c` of an element `l` of the weighted antidiagonal is at most `n`. -/
theorem mul_le_of_mem_weightedFinsuppAntidiag {s : Finset ι} {m : ι → ℕ+} {n : ℕ}
    {l : ι →₀ ℕ} (hl : l ∈ s.weightedFinsuppAntidiag m n) {c : ι} (hc : c ∈ s) :
    (m c : ℕ) * l c ≤ n :=
  mul_le_of_sum_mul_eq (mem_weightedFinsuppAntidiag.1 hl).2 hc

end Finset

namespace PowerSeries

variable {R : Type*} [CommRing R]

/-- **Expansion of a product of expanded power series**: the `n`-th coefficient of
`∏ c ∈ s, f c (X ^ m c)` is the sum, over all `l ∈ s.weightedFinsuppAntidiag m n`, of the products
`∏ c ∈ s, coeff (l c) (f c)`. -/
theorem coeff_prod_expand (s : Finset ι) (m : ι → ℕ+) (f : ι → R⟦X⟧) (n : ℕ) :
    coeff n (∏ c ∈ s, expand (m c) (m c).ne_zero (f c)) =
      ∑ l ∈ s.weightedFinsuppAntidiag m n, ∏ c ∈ s, coeff (l c) (f c) := by
  classical
  rw [coeff_prod]
  simp_rw [coeff_expand, Finset.prod_ite_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij'
    (fun j ↦ Finsupp.onFinset j.support (fun c ↦ j c / m c) fun c hc ↦ by
      simpa using fun h ↦ hc (by simp [h]))
    (fun l ↦ Finsupp.onFinset l.support (fun c ↦ m c * l c) fun c hc ↦ by
      simpa using right_ne_zero_of_mul hc)
    ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag, Finset.mem_weightedFinsuppAntidiag,
      and_imp]
    intro j hsum hsupp hdvd
    refine ⟨(Finsupp.support_onFinset_subset).trans hsupp, ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun c hc ↦ by simp [Nat.mul_div_cancel' (hdvd c hc)]
  · simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag, Finset.mem_weightedFinsuppAntidiag,
      and_imp]
    intro l hsupp hsum
    refine ⟨⟨by simpa using hsum, (Finsupp.support_onFinset_subset).trans hsupp⟩, ?_⟩
    simp
  · simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag, and_imp]
    intro j _ hsupp hdvd
    ext c
    by_cases hc : c ∈ s
    · simp [Nat.mul_div_cancel' (hdvd c hc)]
    · simp [Finsupp.notMem_support_iff.1 fun h ↦ hc (hsupp h)]
  · intro l _
    ext c
    simp
  · intro j _
    simp

/-- **Finite cutoff** for a product of expanded power series: adjoining factors
`f c (X ^ m c)` with `n < m c` and constant term `1` does not change the `n`-th coefficient. -/
theorem coeff_prod_expand_of_subset {s t : Finset ι} (hst : s ⊆ t) {m : ι → ℕ+}
    {f : ι → R⟦X⟧} {n : ℕ} (h : ∀ c ∈ t, c ∉ s → n < m c)
    (hf : ∀ c ∈ t, c ∉ s → constantCoeff (f c) = 1) :
    coeff n (∏ c ∈ t, expand (m c) (m c).ne_zero (f c)) =
      coeff n (∏ c ∈ s, expand (m c) (m c).ne_zero (f c)) := by
  -- An element of the weighted antidiagonal over `t` vanishes at every adjoined index.
  have hzero : ∀ l ∈ t.weightedFinsuppAntidiag m n, ∀ c ∈ t, c ∉ s → l c = 0 := by
    intro l hl c hct hcs
    have hle := Finset.mul_le_of_mem_weightedFinsuppAntidiag hl hct
    have := h c hct hcs
    by_contra hlc
    have := Nat.le_mul_of_pos_right (m c : ℕ) (Nat.pos_of_ne_zero hlc)
    omega
  -- An assignment supported in `s` has the same weighted sum over `s` and over `t`.
  have hsum : ∀ l : ι →₀ ℕ, l.support ⊆ s →
      ∑ c ∈ t, (m c : ℕ) * l c = ∑ c ∈ s, (m c : ℕ) * l c := fun l hl ↦
    (Finset.sum_subset hst fun c _ hcs ↦ by
      simp [Finsupp.notMem_support_iff.1 fun hc ↦ hcs (hl hc)]).symm
  have hconf : t.weightedFinsuppAntidiag m n = s.weightedFinsuppAntidiag m n := by
    ext l
    refine ⟨fun hl ↦ ?_, fun hl ↦ ?_⟩
    · have hsupp : l.support ⊆ s := fun c hc ↦ by
        by_contra hcs
        exact Finsupp.mem_support_iff.1 hc
          (hzero l hl c ((Finset.mem_weightedFinsuppAntidiag.1 hl).1 hc) hcs)
      exact Finset.mem_weightedFinsuppAntidiag.2
        ⟨hsupp, hsum l hsupp ▸ (Finset.mem_weightedFinsuppAntidiag.1 hl).2⟩
    · rw [Finset.mem_weightedFinsuppAntidiag] at hl ⊢
      exact ⟨hl.1.trans hst, (hsum l hl.1).trans hl.2⟩
  rw [coeff_prod_expand, coeff_prod_expand, hconf]
  refine Finset.sum_congr rfl fun l hl ↦ (Finset.prod_subset hst fun c hct hcs ↦ ?_).symm
  rw [Finsupp.notMem_support_iff.1 fun hc ↦ hcs ((Finset.mem_weightedFinsuppAntidiag.1 hl).1 hc),
    coeff_zero_eq_constantCoeff_apply, hf c hct hcs]

/-- An expanded series `f (X ^ p)` agrees with its constant coefficient modulo `X ^ p`. -/
theorem X_pow_dvd_expand_sub_C_constantCoeff (p : ℕ) (hp : p ≠ 0) (f : R⟦X⟧) :
    X ^ p ∣ expand p hp f - C (constantCoeff f) := by
  obtain ⟨g, hg⟩ := X_dvd_iff.2 (by simp : constantCoeff (f - C (constantCoeff f)) = 0)
  refine ⟨expand p hp g, ?_⟩
  rw [← expand_C p hp, ← map_sub, hg, map_mul, expand_X]


open scoped PowerSeries.WithPiTopology

variable [TopologicalSpace R]

/-- If `{c | m c ≤ n}` is finite for every `n` and every `f c` has constant term `1`, the finite
products of the factors `f c (X ^ m c)` converge in the coefficientwise topology
(`PowerSeries.WithPiTopology`), the `n`-th coefficient of the limit being that of the product
over `{c | m c ≤ n}`. -/
theorem hasProd_expand {m : ι → ℕ+} (hm : ∀ n : ℕ, {c | (m c : ℕ) ≤ n}.Finite)
    {f : ι → R⟦X⟧} (hf : ∀ c, constantCoeff (f c) = 1) :
    HasProd (fun c ↦ expand (m c) (m c).ne_zero (f c))
      (mk fun n ↦ coeff n (∏ c ∈ (hm n).toFinset, expand (m c) (m c).ne_zero (f c))) := by
  refine WithPiTopology.hasProd_of_X_pow_dvd_sub_one (fun n ↦ (hm n).toFinset) ?_
  intro n c hc
  have hlt : n + 1 ≤ (m c : ℕ) := by
    have hnot : ¬ (m c : ℕ) ≤ n := by simpa using hc
    omega
  have hdiv : X ^ (m c : ℕ) ∣ expand (m c) (m c).ne_zero (f c) - 1 := by
    simpa [hf c] using
      X_pow_dvd_expand_sub_C_constantCoeff (m c) (m c).ne_zero (f c)
  exact (pow_dvd_pow (X : R⟦X⟧) hlt).trans hdiv

/-- If `{c | m c ≤ n}` is finite for every `n` and every `f c` has constant term `1`, the
factors `f c (X ^ m c)` have an infinite product in the coefficientwise topology
(`PowerSeries.WithPiTopology`) on `R⟦X⟧`. -/
theorem multipliable_expand {m : ι → ℕ+} (hm : ∀ n : ℕ, {c | (m c : ℕ) ≤ n}.Finite)
    {f : ι → R⟦X⟧} (hf : ∀ c, constantCoeff (f c) = 1) :
    Multipliable fun c ↦ expand (m c) (m c).ne_zero (f c) :=
  (hasProd_expand hm hf).multipliable

/-- If `{c | m c ≤ n}` is finite for every `n` and every `f c` has constant term `1`, the `n`-th
coefficient of the infinite product `∏' c, f c (X ^ m c)` is that of the finite product over any
`s` containing every `c` with `m c ≤ n`. -/
theorem coeff_tprod_expand [T2Space R] {m : ι → ℕ+}
    (hm : ∀ n : ℕ, {c | (m c : ℕ) ≤ n}.Finite) {f : ι → R⟦X⟧}
    (hf : ∀ c, constantCoeff (f c) = 1) {s : Finset ι} {n : ℕ}
    (hs : ∀ c, (m c : ℕ) ≤ n → c ∈ s) :
    coeff n (∏' c, expand (m c) (m c).ne_zero (f c)) =
      coeff n (∏ c ∈ s, expand (m c) (m c).ne_zero (f c)) := by
  rw [(hasProd_expand hm hf).tprod_eq, coeff_mk]
  have hsub : (hm n).toFinset ⊆ s := fun c hc ↦ hs c (by simpa using hc)
  refine (coeff_prod_expand_of_subset hsub (fun c _ hc ↦ ?_) fun c _ _ ↦ hf c).symm
  simpa using hc

end PowerSeries
