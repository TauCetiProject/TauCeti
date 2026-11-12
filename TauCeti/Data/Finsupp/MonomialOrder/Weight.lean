/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.Data.Finsupp.Weight
import TauCeti.Data.Finsupp.Weight
import TauCeti.Geometry.Convex.Cone.Alternative

/-!
# Finitely many comparisons of a monomial order are realized by weights

Let `m` be a monomial order on `σ →₀ ℕ`. A weight vector `w : σ → ℕ` orders monomials by
`Finsupp.weight w`. In general no single weight represents `m`: for the lexicographic order on
two variables, `X 0` exceeds every power of `X 1`, while `X 1 ^ n` eventually has the larger
weight for every positive weight vector. Any *finite* set of comparisons in `m`, however, is
represented by a weight vector with strictly positive entries. This is how a monomial order is
replaced by a weight in the construction of flat degenerations to initial ideals and initial
algebras: only the finitely many comparisons made by a Gröbner or SAGBI certificate matter.

The proof is a theorem of the alternative. Given strict comparisons `a j ≺[m] b j`, Tucker's
theorem over `ℤ` (`TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos`), applied
to the integer vectors `b j - a j` and the coordinate vectors, gives either an integral weight
which is strictly positive on all of them, or a nontrivial relation with natural coefficients
`c j`, `d i` such that `∑ j, c j • a j = ∑ j, c j • b j + ∑ i, d i • single i 1`. The second
alternative is impossible: the comparisons `0 ≺[m] single i 1` are strict as well, and since `m` is
compatible with addition, a nontrivial combination with natural coefficients of strict comparisons
is again strict.

## Main results

* `MonomialOrder.exists_pos_weight_lt`: finitely many strict comparisons `a j ≺[m] b j` are
  realized by a weight vector with positive entries.
* `MonomialOrder.exists_pos_weight_lt_iff_lt`: on a finite set of monomials, some weight vector with
  positive entries induces exactly the comparisons of `m`.
* `MonomialOrder.exists_pos_weight_lt_iff_lt_of_degree_le`: for finitely many variables, some weight
  vector with positive entries induces the comparisons of `m` among all monomials of total degree
  at most `n`.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, University Lecture Series 8, AMS, 1996,
  Chapter 1.
* A. W. Tucker, *Dual systems of homogeneous linear relations*, in *Linear Inequalities and
  Related Systems*, Annals of Mathematics Studies 38, 1956.
-/

public section

open Finsupp

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ)

/-- Integral version of the weight realization: if the exponents `a j`, `b j` are supported in a
finite set `s`, the strict comparisons `a j ≺[m] b j` are realized by an additive functional on
the integer vectors indexed by `s`. -/
private theorem exists_addMonoidHom_lt {ι : Type*} [Finite ι] {a b : ι → σ →₀ ℕ}
    (h : ∀ j, a j ≺[m] b j) (s : Finset σ) (has : ∀ j, (a j).support ⊆ s)
    (hbs : ∀ j, (b j).support ⊆ s) :
    ∃ μ : (s → ℤ) →+ ℤ, ∀ j, μ (fun i ↦ (a j i : ℤ)) < μ (fun i ↦ (b j i : ℤ)) := by
  cases nonempty_fintype ι
  obtain ⟨x, μ, hsum, -, hpos⟩ := TauCeti.exists_nat_sum_nsmul_eq_zero_and_forall_coeff_add_dual_pos
    fun j ↦ (fun i : s ↦ (b j i : ℤ)) - fun i : s ↦ (a j i : ℤ)
  -- The relation `∑ j, x j • (b j - a j) = 0` lifts to an equality of monomials.
  have heq : ∑ j, x j • a j = ∑ j, x j • b j := by
    ext t
    simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
    by_cases ht : t ∈ s
    · have := congrFun hsum ⟨t, ht⟩
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply] at this
      simp only [smul_sub, Finset.sum_sub_distrib, sub_eq_zero, nsmul_eq_mul] at this
      exact_mod_cast this.symm
    · simp [Finsupp.notMem_support_iff.1 fun h ↦ ht (has _ h),
        Finsupp.notMem_support_iff.1 fun h ↦ ht (hbs _ h)]
  -- Such an equality forces the relation to be trivial, since `m` is compatible with addition.
  have hx : x = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hne
    refine (congrArg m.toSyn heq).not_lt ?_
    simp only [map_sum, map_nsmul]
    exact Finset.sum_lt_sum (fun j _ ↦ nsmul_le_nsmul_right (h j).le _)
      ⟨k, Finset.mem_univ k, nsmul_lt_nsmul_right hk (h k)⟩
  refine ⟨μ, fun j ↦ ?_⟩
  simpa [hx] using hpos j

/-- **Weight realization of finitely many comparisons.** Finitely many strict comparisons
`a j ≺[m] b j` of a monomial order are realized by a weight vector with positive entries. -/
theorem exists_pos_weight_lt {ι : Type*} [Finite ι] {a b : ι → σ →₀ ℕ}
    (h : ∀ j, a j ≺[m] b j) :
    ∃ w : σ → ℕ, (∀ i, 0 < w i) ∧ ∀ j, weight w (a j) < weight w (b j) := by
  classical
  cases nonempty_fintype ι
  let s : Finset σ := Finset.univ.biUnion fun j ↦ (a j).support ∪ (b j).support
  have has (j : ι) : (a j).support ⊆ s := fun i hi ↦
    Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, Finset.mem_union_left _ hi⟩
  have hbs (j : ι) : (b j).support ⊆ s := fun i hi ↦
    Finset.mem_biUnion.2 ⟨j, Finset.mem_univ j, Finset.mem_union_right _ hi⟩
  -- Add the comparisons `0 ≺[m] single i 1` for `i ∈ s`, which force positive weights on `s`.
  have hsingle (i : s) : (single (i : σ) 1).support ⊆ s := by
    simp
  obtain ⟨μ, hμ⟩ := m.exists_addMonoidHom_lt (a := Sum.elim a 0)
    (b := Sum.elim b fun i : s ↦ single (i : σ) 1)
    (fun k ↦ k.rec h fun i ↦ by simp [m.toSyn_lt_iff_ne_zero])
    s (fun k ↦ k.rec has fun _ ↦ by simp) (fun k ↦ k.rec hbs hsingle)
  have hμ₁ (i : s) : 0 < μ (Pi.single i 1) := by
    have hi : (fun j : s ↦ ((single (i : σ) 1 j : ℕ) : ℤ)) = Pi.single i 1 := by
      ext j
      rcases eq_or_ne j i with rfl | hji
      · simp
      · simp [hji, Finsupp.single_eq_of_ne (Subtype.coe_ne_coe.2 hji)]
    simpa [hi, ← Pi.zero_def] using hμ (Sum.inr i)
  refine ⟨fun i ↦ if hi : i ∈ s then (μ (Pi.single ⟨i, hi⟩ 1)).toNat else 1, fun i ↦ ?_,
    fun j ↦ ?_⟩
  · dsimp only
    split_ifs with hi
    · exact Int.lt_toNat.2 (hμ₁ ⟨i, hi⟩)
    · exact one_pos
  · have hμw (i : s) : μ (Pi.single i 1) =
        ((if hi : (i : σ) ∈ s then (μ (Pi.single ⟨i, hi⟩ 1)).toNat else 1 : ℕ) : ℤ) := by
      simp [(hμ₁ i).le]
    have := hμ (Sum.inl j)
    simp only [Sum.elim_inl] at this
    exact_mod_cast (natCast_weight_eq_of_support_subset μ hμw (has j)).trans_lt
      (this.trans_eq (natCast_weight_eq_of_support_subset μ hμw (hbs j)).symm)

/-- **Weight realization on a finite set of monomials.** On a finite set `F` of monomials, some
weight vector with positive entries induces exactly the strict comparisons of the monomial order
`m`. -/
theorem exists_pos_weight_lt_iff_lt {F : Set (σ →₀ ℕ)} (hF : F.Finite) :
    ∃ w : σ → ℕ, (∀ i, 0 < w i) ∧
      ∀ a ∈ F, ∀ b ∈ F, (a ≺[m] b ↔ weight w a < weight w b) := by
  have := hF.to_subtype
  obtain ⟨w, hw, hlt⟩ := m.exists_pos_weight_lt
    (a := fun p : {p : F × F // (p.1 : σ →₀ ℕ) ≺[m] p.2} ↦ p.1.1)
    (b := fun p ↦ p.1.2) fun p ↦ p.2
  refine ⟨w, hw, fun a ha b hb ↦ ⟨fun hab ↦ hlt ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩, fun hab ↦ ?_⟩⟩
  rcases lt_trichotomy (m.toSyn a) (m.toSyn b) with h | h | h
  · exact h
  · exact absurd (congrArg (weight w) (m.toSyn.injective h)) hab.ne
  · exact absurd (hlt ⟨(⟨b, hb⟩, ⟨a, ha⟩), h⟩) hab.not_gt

/-- **Weight realization in bounded total degree.** For finitely many variables and every bound
`n`, some weight vector with positive entries induces the strict comparisons of the monomial
order `m` among all monomials of total degree at most `n`. -/
theorem exists_pos_weight_lt_iff_lt_of_degree_le [Finite σ] (n : ℕ) :
    ∃ w : σ → ℕ, (∀ i, 0 < w i) ∧ ∀ a b : σ →₀ ℕ, degree a ≤ n → degree b ≤ n →
      (a ≺[m] b ↔ weight w a < weight w b) := by
  obtain ⟨w, hw, h⟩ := m.exists_pos_weight_lt_iff_lt (finite_of_degree_le n)
  exact ⟨w, hw, fun a b ha hb ↦ h a ha b hb⟩

/-- No weight vector induces all comparisons of the lexicographic order on two variables: `X 0`
exceeds every power of `X 1`. So the finiteness hypotheses above cannot be dropped. -/
example : ¬ ∃ w : Fin 2 → ℕ, ∀ a b : Fin 2 →₀ ℕ, (a ≺[lex] b ↔ weight w a < weight w b) := by
  rintro ⟨w, hw⟩
  have h₀ := (hw 0 (single 1 1)).1 (by simp [toSyn_lt_iff_ne_zero])
  have h₁ := (hw (single 1 (w 0 + 1)) (single 0 1)).1 (by rw [lex_lt_iff]; use 0; simp)
  simp only [map_zero, weight_single, smul_eq_mul, one_mul] at h₀ h₁
  nlinarith

end MonomialOrder
