/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Binomial
public import Mathlib.Algebra.Algebra.Operations

/-!
# Bounded integral spans of ordered binomial products

`ringChooseFilteredSpan h n` is the integral span of the ordered products
`∏ᵢ (h i choose a i)` with `∑ᵢ a i ≤ n`. Products are expressed with `List.ofFn`, as in
`TauCeti.RingTheory.Binomial.IntegralSpan`, so their order is explicit even when the ambient
ring is noncommutative.

For pairwise commuting `h i`, the degree-`n` binomial coefficient of any integer linear
combination of the `h i`, translated by any integer, belongs to this span. In particular,
neither integer multiplication of an argument nor integer translation increases the degree
bound. This controls the shifted coroot binomials in integral enveloping-algebra straightening.

The one-variable multiplication formula `TauCeti.ringChoose_mul_ringChoose`, upper negation
`TauCeti.Ring.choose_neg_mem`, and integer translation `TauCeti.Ring.choose_add_intCast_mem`
provide the integral coefficients. Chu–Vandermonde combines the distinct coordinates.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
-/

public section

namespace TauCeti

open Finset Submodule
open scoped Pointwise

variable {R : Type*} [Ring R] [BinomialRing R]

/-- The integral span of ordered binomial products with total degree at most `n`. No
commutativity or independence of the family is required to define the span. -/
def ringChooseFilteredSpan {r : ℕ} (h : Fin r → R) (n : ℕ) : Submodule ℤ R :=
  span ℤ ((fun a : Fin r → ℕ => (List.ofFn fun i => Ring.choose (h i) (a i)).prod) ''
    {a | ∑ i, a i ≤ n})

/-- The generators of the bounded integral span are ordered binomial products. -/
theorem ringChooseFilteredSpan_def {r : ℕ} (h : Fin r → R) (n : ℕ) :
    ringChooseFilteredSpan h n =
      span ℤ ((fun a : Fin r → ℕ => (List.ofFn fun i => Ring.choose (h i) (a i)).prod) ''
        {a | ∑ i, a i ≤ n}) := (rfl)

/-- Membership in a stage is equivalent to a finite integral expansion indexed by
multi-indices of total degree at most the stage bound. -/
theorem mem_ringChooseFilteredSpan_iff {r : ℕ} (h : Fin r → R) (n : ℕ) (x : R) :
    x ∈ ringChooseFilteredSpan h n ↔
      ∃ c : {a : Fin r → ℕ // ∑ i, a i ≤ n} →₀ ℤ,
        c.sum (fun a z => z • (List.ofFn fun i => Ring.choose (h i) (a.val i)).prod) = x := by
  rw [ringChooseFilteredSpan_def, Set.image_eq_range]
  exact Finsupp.mem_span_range_iff_exists_finsupp

/-- Every ordered binomial product belongs to the stage given by its total degree. -/
theorem prod_ofFn_ringChoose_mem_ringChooseFilteredSpan {r : ℕ} (h : Fin r → R)
    (a : Fin r → ℕ) {n : ℕ} (ha : ∑ i, a i ≤ n) :
    (List.ofFn fun i => Ring.choose (h i) (a i)).prod ∈ ringChooseFilteredSpan h n :=
  subset_span ⟨a, ha, rfl⟩

/-- An integral submodule contains a stage exactly when it contains every product of bounded
total degree. -/
theorem ringChooseFilteredSpan_le_iff {r : ℕ} {h : Fin r → R} {n : ℕ}
    {S : Submodule ℤ R} : ringChooseFilteredSpan h n ≤ S ↔
      ∀ a : Fin r → ℕ, ∑ i, a i ≤ n →
        (List.ofFn fun i => Ring.choose (h i) (a i)).prod ∈ S := by
  simp [ringChooseFilteredSpan_def, span_le, Set.subset_def]

/-- The bounded integral spans increase with the degree bound. -/
theorem ringChooseFilteredSpan_mono {r : ℕ} (h : Fin r → R) :
    Monotone (ringChooseFilteredSpan h) := by
  intro m n hmn
  exact span_mono (Set.image_mono fun _ ha => ha.trans hmn)

/-- The stages exhaust the unbounded integral additive span of ordered binomial products. -/
theorem toAddSubgroup_iSup_ringChooseFilteredSpan_eq_closure {r : ℕ} (h : Fin r → R) :
    (⨆ n, ringChooseFilteredSpan h n).toAddSubgroup =
      AddSubgroup.closure
        (Set.range fun a : Fin r → ℕ => (List.ofFn fun i => Ring.choose (h i) (a i)).prod) := by
  simp_rw [ringChooseFilteredSpan_def]
  rw [iSup_span, ← Set.image_iUnion]
  have hcuts : (⋃ n : ℕ, {a : Fin r → ℕ | ∑ i, a i ≤ n}) = Set.univ := by
    exact (Set.preimage_iUnion (f := fun a : Fin r → ℕ => ∑ i, a i)
      (s := fun n : ℕ => Set.Iic n)).symm.trans
      (by rw [Set.iUnion_Iic, Set.preimage_univ])
  rw [hcuts, Set.image_univ, span_int_eq_addSubgroupClosure]

/-- Every stage contains one, the product with all exponents zero. -/
@[simp↓]
theorem one_mem_ringChooseFilteredSpan {r : ℕ} (h : Fin r → R) (n : ℕ) :
    1 ∈ ringChooseFilteredSpan h n := by
  simpa using prod_ofFn_ringChoose_mem_ringChooseFilteredSpan h (fun _ => 0)
    (n := n) (by simp)

/-- For an empty family every stage consists of the integral multiples of one. -/
@[simp]
theorem ringChooseFilteredSpan_fin_zero (h : Fin 0 → R) (n : ℕ) :
    ringChooseFilteredSpan h n = span ℤ {(1 : R)} := by
  apply le_antisymm
  · rw [ringChooseFilteredSpan_le_iff]
    intro a _
    simp
  · exact span_le.mpr (Set.singleton_subset_iff.mpr (one_mem_ringChooseFilteredSpan h n))

/-- For a singleton family, a stage is the integral span of its coefficients through the
specified degree. -/
@[simp]
theorem ringChooseFilteredSpan_fin_one (h : Fin 1 → R) (n : ℕ) :
    ringChooseFilteredSpan h n = span ℤ (Ring.choose (h 0) '' Set.Iic n) := by
  apply le_antisymm
  · rw [ringChooseFilteredSpan_le_iff]
    intro a ha
    simpa using (subset_span ⟨a 0, Set.mem_Iic.mpr (by simpa using ha), rfl⟩ :
      Ring.choose (h 0) (a 0) ∈ span ℤ (Ring.choose (h 0) '' Set.Iic n))
  · rw [span_le]
    rintro _ ⟨k, hk, rfl⟩
    simpa using prod_ofFn_ringChoose_mem_ringChooseFilteredSpan h (fun _ => k)
      (n := n) (by simpa using hk)

/-- The degree-zero stage consists of the integral multiples of one. -/
@[simp]
theorem ringChooseFilteredSpan_zero {r : ℕ} (h : Fin r → R) :
    ringChooseFilteredSpan h 0 = span ℤ {(1 : R)} := by
  apply le_antisymm
  · rw [ringChooseFilteredSpan_le_iff]
    intro a ha
    have hz : ∀ i, a i = 0 := by
      intro i
      have := single_le_sum (fun j _ => Nat.zero_le (a j)) (mem_univ i)
      omega
    simp [hz]
  · exact span_le.mpr (Set.singleton_subset_iff.mpr (one_mem_ringChooseFilteredSpan h 0))

/-- Multiplying a bounded one-variable span by a bounded span on subsequent coordinates adds
the degree bounds, without requiring commutation between the two sets of coordinates. -/
theorem mul_mem_ringChooseFilteredSpan_cons {r : ℕ} (x : R) (h : Fin r → R)
    {u v : R} {m n : ℕ} (hu : u ∈ span ℤ (Ring.choose x '' Set.Iic m))
    (hv : v ∈ ringChooseFilteredSpan h n) :
    u * v ∈ ringChooseFilteredSpan (Fin.cons x h) (m + n) := by
  have hmul : span ℤ (Ring.choose x '' Set.Iic m) * ringChooseFilteredSpan h n ≤
      ringChooseFilteredSpan (Fin.cons x h) (m + n) := by
    rw [ringChooseFilteredSpan_def h n, span_mul_span, span_le]
    rintro _ ⟨_, ⟨i, hi, rfl⟩, _, ⟨a, ha, rfl⟩, rfl⟩
    dsimp only
    rw [SetLike.mem_coe]
    have hdeg : ∑ j, Fin.cons i a j ≤ m + n := by
      simpa using add_le_add (Set.mem_Iic.mp hi) ha
    simpa only [List.ofFn_succ, List.prod_cons, Fin.cons_zero, Fin.cons_succ] using
      prod_ofFn_ringChoose_mem_ringChooseFilteredSpan (Fin.cons x h) (Fin.cons i a) hdeg
  exact hmul (mul_mem_mul hu hv)

/-- For a commuting family, multiplication of stages adds the total-degree bounds. -/
theorem mul_le_ringChooseFilteredSpan {r : ℕ} (h : Fin r → R)
    (hcomm : ∀ i j, Commute (h i) (h j)) (m n : ℕ) :
    ringChooseFilteredSpan h m * ringChooseFilteredSpan h n ≤
      ringChooseFilteredSpan h (m + n) := by
  induction r generalizing m n with
  | zero => simp [ringChooseFilteredSpan_fin_zero, span_mul_span]
  | succ r ih =>
    rw [ringChooseFilteredSpan_def h m, ringChooseFilteredSpan_def h n, span_mul_span, span_le]
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    dsimp only
    rw [SetLike.mem_coe]
    have htail := ih (fun i => h i.succ) (fun i j => hcomm i.succ j.succ)
      (∑ i : Fin r, a i.succ) (∑ i : Fin r, b i.succ)
      (mul_mem_mul
        (prod_ofFn_ringChoose_mem_ringChooseFilteredSpan _ _ le_rfl)
        (prod_ofFn_ringChoose_mem_ringChooseFilteredSpan _ _ le_rfl))
    have hhead := mul_mem_span_ringChoose_Iic (h 0)
      (subset_span ⟨a 0, Set.mem_Iic.mpr le_rfl, rfl⟩)
      (subset_span ⟨b 0, Set.mem_Iic.mpr le_rfl, rfl⟩)
    have hswap : Commute (List.ofFn fun i : Fin r => Ring.choose (h i.succ) (a i.succ)).prod
        (Ring.choose (h 0) (b 0)) := by
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact (hcomm i.succ 0).ringChoose _ _
    have hmem := mul_mem_ringChooseFilteredSpan_cons (h 0) (fun i => h i.succ) hhead htail
    have hdeg : a 0 + b 0 + ((∑ i : Fin r, a i.succ) + (∑ i : Fin r, b i.succ)) ≤ m + n := by
      simp only [Set.mem_ofPred_eq, Fin.sum_univ_succ] at ha hb
      omega
    apply ringChooseFilteredSpan_mono h hdeg
    simpa only [List.ofFn_succ, List.prod_cons, hswap.mul_mul_mul_comm,
      ← Fin.tail_def, Fin.cons_self_tail] using hmem

/-- For a commuting family, products of elements in two stages lie in the stage with the sum
of their bounds. -/
theorem mul_mem_ringChooseFilteredSpan {r : ℕ} (h : Fin r → R)
    (hcomm : ∀ i j, Commute (h i) (h j)) {u v : R} {m n : ℕ}
    (hu : u ∈ ringChooseFilteredSpan h m) (hv : v ∈ ringChooseFilteredSpan h n) :
    u * v ∈ ringChooseFilteredSpan h (m + n) :=
  mul_le_ringChooseFilteredSpan h hcomm m n (mul_mem_mul hu hv)

/-- The degree-`n` binomial coefficient of an integer linear combination of a commuting family
has an integral ordered expansion of total degree at most `n`. -/
theorem ringChoose_sum_zsmul_mem_ringChooseFilteredSpan {r : ℕ} (h : Fin r → R)
    (hcomm : ∀ i j, Commute (h i) (h j)) (z : Fin r → ℤ) (n : ℕ) :
    Ring.choose (∑ i, z i • h i) n ∈ ringChooseFilteredSpan h n := by
  induction r generalizing n with
  | zero =>
    cases n <;> simp [Ring.choose_zero_succ]
  | succ r ih =>
    have htail : ∀ i j : Fin r, Commute (h i.succ) (h j.succ) :=
      fun i j => hcomm i.succ j.succ
    have hhead : Commute (z 0 • h 0) (∑ i : Fin r, z i.succ • h i.succ) :=
      Commute.sum_right _ _ _ fun i _ =>
        ((hcomm 0 i.succ).smul_left (z 0)).smul_right (z i.succ)
    rw [Fin.sum_univ_succ, Ring.add_choose_eq n hhead]
    refine sum_mem fun ab hab => ?_
    have hmem := mul_mem_ringChooseFilteredSpan_cons (h 0) (fun i => h i.succ)
      (ringChoose_zsmul_mem_span_ringChoose_Iic (h 0) (z 0) ab.1)
      (ih (fun i => h i.succ) htail (fun i => z i.succ) ab.2)
    simpa only [mem_antidiagonal.mp hab, ← Fin.tail_def, Fin.cons_self_tail] using hmem

/-- Integer translation preserves the total-degree bound in the ordered integral expansion of
the binomial coefficient of an integer linear combination of commuting elements. -/
theorem ringChoose_sum_zsmul_add_intCast_mem_ringChooseFilteredSpan {r : ℕ} (h : Fin r → R)
    (hcomm : ∀ i j, Commute (h i) (h j)) (z : Fin r → ℤ) (c : ℤ) (n : ℕ) :
    Ring.choose ((∑ i, z i • h i) + (c : R)) n ∈ ringChooseFilteredSpan h n := by
  apply Ring.choose_add_intCast_mem
    (A := ringChooseFilteredSpan h n) (z := c)
  intro k hk
  exact ringChooseFilteredSpan_mono h hk
    (ringChoose_sum_zsmul_mem_ringChooseFilteredSpan h hcomm z k)

end TauCeti
