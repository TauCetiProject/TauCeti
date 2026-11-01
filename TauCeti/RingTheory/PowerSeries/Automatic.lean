/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import TauCeti.Computability.AutomaticSequence.Kernel
public import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.Algebra.Polynomial.Card.BoundedCoeff
import TauCeti.RingTheory.LaurentSeries.Cartier
import TauCeti.RingTheory.PowerSeries.OreRelation

/-!
# Algebraic power series over a finite field have automatic coefficients

Let `K` be a finite field with `q` elements. If a power series `f = ∑ aₙ Xⁿ ∈ K⟦X⟧` is algebraic
over `K[X]`, then its coefficient sequence `(aₙ)` is `q`-automatic
(`PowerSeries.isAutomatic_coeff_of_isAlgebraic`). This is the direction "algebraic implies
automatic" of Christol's theorem.

The proof goes through the `q`-kernel. The Cartier operator `Λ_r = PowerSeries.cartier K q r`
sends `∑ aₙ Xⁿ` to `∑ a_{q n + r} Xⁿ`, so the coefficient sequences of the iterated Cartier
images of `f` are exactly the elements of the `q`-kernel of `(aₙ)`; if `f` lies in a finite set
of power series stable under every `Λ_r` with `r < q`, the kernel is finite and Eilenberg's
theorem makes `(aₙ)` automatic (`PowerSeries.isAutomatic_coeff_of_finite_cartier_stable`, which
holds over every semiring and in every base `k ≥ 2`).

Such a finite stable set exists for algebraic `f`
(`PowerSeries.exists_finite_cartier_stable_of_isAlgebraic`). By
`PowerSeries.exists_ore_relation`, `∑_{i ≤ m} aᵢ f ^ q ^ i = 0` with `aᵢ ∈ K[X]` and `a₀ ≠ 0`.
In the Laurent series field put `g = f / a₀`; then `g = ∑_{1 ≤ i ≤ m} bᵢ g ^ q ^ i` with
`bᵢ = -aᵢ a₀ ^ (q ^ i - 2) ∈ K[X]`. Let `N` bound the degrees of `a₀` and of the `bᵢ`. The set
`H` of the sums `∑_{i ≤ m} cᵢ g ^ q ^ i` with `cᵢ ∈ K[X]` of degree at most `N` is finite and
contains `f = a₀ g`. Substituting the relation for `g` in the term `c₀ g` and using
`Λ_r (u ^ q * v) = u * Λ_r v` gives
`Λ_r (∑_{i ≤ m} cᵢ g ^ q ^ i) = ∑_{i < m} Λ_r (c₀ b_{i + 1} + c_{i + 1}) g ^ q ^ i`,
whose coefficients have degree at most `2 N / q ≤ N`. Hence `H` is stable under the `Λ_r`.

## Main results

* `PowerSeries.isAutomatic_coeff_of_finite_cartier_stable`: a power series lying in a finite
  Cartier-stable set has `k`-automatic coefficients.
* `PowerSeries.exists_finite_cartier_stable_of_isAlgebraic`: over a finite field, an algebraic
  power series lies in a finite set stable under the Cartier operators.
* `PowerSeries.isAutomatic_coeff_of_isAlgebraic`: over a finite field with `q` elements, an
  algebraic power series has `q`-automatic coefficients.

## References

* G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates et
  substitutions*, Bull. Soc. Math. France 108 (1980), Section 7.
* B. Adamczewski, R. Yassawi, *A note on Christol's theorem*, Section 1.
-/

public section

open Polynomial
open scoped LaurentSeries PowerSeries

namespace PowerSeries

section Semiring

variable {R : Type*} [Semiring R] {k : ℕ} [NeZero k]

/-- If a power series `f` lies in a finite set `T` of power series that is stable under the
Cartier operators `cartier R k r` with `r < k`, for a base `k ≥ 2`, then the coefficient sequence
of `f` is `k`-automatic: every element of its `k`-kernel is the coefficient sequence of an element
of `T`. -/
theorem isAutomatic_coeff_of_finite_cartier_stable (hk : 2 ≤ k) {T : Set R⟦X⟧} (hT : T.Finite)
    {f : R⟦X⟧} (hf : f ∈ T) (hTk : ∀ h ∈ T, ∀ r < k, cartier R k r h ∈ T) :
    TauCeti.IsAutomatic k fun n ↦ coeff n f := by
  refine TauCeti.isAutomatic_of_finite_kernel hk <| (hT.image fun h n ↦ coeff n h).subset <|
    TauCeti.kernel_subset_of_mem_of_forall ⟨f, hf, rfl⟩ ?_
  rintro _ ⟨h, hh, rfl⟩ r hr
  exact ⟨cartier R k r h, hTk h hh r hr, funext fun n ↦ coeff_cartier k r n h⟩

end Semiring

section FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- For an Ore relation `∑_{i ≤ m} aᵢ • f ^ q ^ i = 0` and `f = a₀ g` in the Laurent series
field, the series `g` satisfies `g = ∑_{i < m} bᵢ g ^ q ^ (i + 1)` with
`bᵢ = -a_{i + 1} a₀ ^ (q ^ (i + 1) - 2)`. -/
private lemma eq_sum_of_ore_relation {f : K⟦X⟧} {g : K⸨X⸩} {m : ℕ} {a : ℕ → K[X]}
    (ha0 : a 0 ≠ 0) (hfg : (f : K⸨X⸩) = algebraMap K[X] K⸨X⸩ (a 0) * g)
    (hrel : ∑ i ∈ Finset.range (m + 1), a i • f ^ (Fintype.card K ^ i) = 0) :
    g = ∑ i ∈ Finset.range m, algebraMap K[X] K⸨X⸩
      (-(a (i + 1) * a 0 ^ (Fintype.card K ^ (i + 1) - 2))) * g ^ Fintype.card K ^ (i + 1) := by
  have hA : algebraMap K[X] K⸨X⸩ (a 0) ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha0
  have h0 := congrArg (HahnSeries.ofPowerSeries ℤ K) hrel
  simp only [map_sum, map_zero, Algebra.smul_def, map_mul, map_pow,
    ← HahnSeries.algebraMap_apply', hfg] at h0
  rw [Finset.sum_range_succ', pow_zero, pow_one] at h0
  refine mul_left_cancel₀ (pow_ne_zero 2 hA) ?_
  rw [Finset.mul_sum]
  have hterm (i : ℕ) : algebraMap K[X] K⸨X⸩ (a 0) ^ 2 * (algebraMap K[X] K⸨X⸩
      (-(a (i + 1) * a 0 ^ (Fintype.card K ^ (i + 1) - 2))) * g ^ Fintype.card K ^ (i + 1)) =
      -(algebraMap K[X] K⸨X⸩ (a (i + 1)) *
        (algebraMap K[X] K⸨X⸩ (a 0) * g) ^ Fintype.card K ^ (i + 1)) := by
    have h2 : 2 ≤ Fintype.card K ^ (i + 1) :=
      Fintype.one_lt_card.trans_le (Nat.le_self_pow (Nat.succ_ne_zero i) _)
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h2
    simp only [map_neg, map_mul, map_pow, mul_pow, ht, Nat.add_sub_cancel_left]
    ring
  simp only [hterm, Finset.sum_neg_distrib]
  linear_combination h0

/-- Let `g = ∑_{i < m} bᵢ g ^ q ^ (i + 1)` in the Laurent series field with `deg bᵢ ≤ N`. Then the
Cartier operator `Λ_r` of modulus `q` sends a sum `∑_{i ≤ m} cᵢ g ^ q ^ i` with polynomial
coefficients of degree at most `N` to another such sum. The modulus is given as a positive natural
number `d` with `d = q`. -/
private lemma exists_contract_sum_eq (d : ℕ+) (hd : (d : ℕ) = Fintype.card K) {g : K⸨X⸩}
    {m N : ℕ} {b : ℕ → K[X]}
    (hg : g = ∑ i ∈ Finset.range m, algebraMap K[X] K⸨X⸩ (b i) * g ^ Fintype.card K ^ (i + 1))
    (hb : ∀ i < m, (b i).natDegree ≤ N) {c : ℕ → K[X]} (hc : ∀ i, (c i).natDegree ≤ N)
    (r : Fin d) :
    ∃ c' : ℕ → K[X], (∀ i, (c' i).natDegree ≤ N) ∧
      LaurentSeries.contract d
          (∑ i ∈ Finset.range (m + 1), algebraMap K[X] K⸨X⸩ (c i) * g ^ Fintype.card K ^ i) r =
        ∑ i ∈ Finset.range (m + 1), algebraMap K[X] K⸨X⸩ (c' i) * g ^ Fintype.card K ^ i := by
  set q := Fintype.card K
  -- Substituting the relation for `g` in the term `c₀ g` gives
  -- `∑_{i ≤ m} cᵢ g ^ q ^ i = ∑_{i < m} (g ^ q ^ i) ^ q (c₀ bᵢ + c_{i + 1})`.
  have hsub : ∑ i ∈ Finset.range (m + 1), algebraMap K[X] K⸨X⸩ (c i) * g ^ q ^ i =
      ∑ i ∈ Finset.range m, (g ^ q ^ i) ^ q * algebraMap K[X] K⸨X⸩ (c 0 * b i + c (i + 1)) := by
    calc ∑ i ∈ Finset.range (m + 1), algebraMap K[X] K⸨X⸩ (c i) * g ^ q ^ i
        = ∑ i ∈ Finset.range m, algebraMap K[X] K⸨X⸩ (c (i + 1)) * g ^ q ^ (i + 1) +
            algebraMap K[X] K⸨X⸩ (c 0) *
              ∑ i ∈ Finset.range m, algebraMap K[X] K⸨X⸩ (b i) * g ^ q ^ (i + 1) := by
          rw [Finset.sum_range_succ', pow_zero, pow_one, ← hg]
      _ = _ := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [map_add, map_mul, ← pow_mul, ← pow_succ]
          ring
  -- The Cartier operator sends `c₀ bᵢ + c_{i + 1}`, of degree at most `2 N`, to a polynomial of
  -- degree at most `2 N / q ≤ N`.
  choose e he using fun i ↦
    exists_cartier_coe_polynomial_eq d r d.ne_zero (c 0 * b i + c (i + 1))
  refine ⟨fun i ↦ if i < m then e i else 0, fun i ↦ ?_, ?_⟩
  · dsimp only
    split_ifs with hi
    · calc (e i).natDegree ≤ (c 0 * b i + c (i + 1)).natDegree / d := (he i).1
        _ ≤ (N + N) / d := Nat.div_le_div_right <| (natDegree_add_le _ _).trans <|
            max_le (natDegree_mul_le.trans (add_le_add (hc 0) (hb i hi))) ((hc _).trans (by omega))
        _ ≤ N := Nat.div_le_of_le_mul (by nlinarith [Fintype.one_lt_card (α := K)])
    · simp
  · rw [hsub, LaurentSeries.contract_sum, Finset.sum_range_succ]
    simp only [lt_irrefl, ite_false, map_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [LaurentSeries.contract_pow_card_mul d hd, mul_comm]
    simp only [Finset.mem_range.mp hi, ite_true, HahnSeries.algebraMap_apply',
      PowerSeries.algebraMap_apply', Algebra.algebraMap_self, PowerSeries.map_id, id_eq]
    rw [LaurentSeries.contract_coe, (he i).2]

/-- Over a finite field, the Laurent series `∑_{i ≤ m} cᵢ g ^ q ^ i` with polynomial coefficients
`cᵢ` of degree at most `N` form a finite set. -/
private lemma finite_setOf_eq_sum (g : K⸨X⸩) (m N : ℕ) :
    Set.Finite {h : K⸨X⸩ | ∃ c : ℕ → K[X], (∀ i, (c i).natDegree ≤ N) ∧
      h = ∑ i ∈ Finset.range (m + 1), algebraMap K[X] K⸨X⸩ (c i) * g ^ Fintype.card K ^ i} := by
  have hP : {p : K[X] | p.natDegree ≤ N}.Finite :=
    (TauCeti.Polynomial.finite_setOf_natDegree_le_coeff_mem N (Set.finite_univ (α := K))).subset
      fun p hp ↦ ⟨hp, fun _ ↦ trivial⟩
  refine ((Set.Finite.pi (t := fun _ : Fin (m + 1) ↦ {p : K[X] | p.natDegree ≤ N}) fun _ ↦ hP).image
    fun c ↦ ∑ i : Fin (m + 1), algebraMap K[X] K⸨X⸩ (c i) * g ^ Fintype.card K ^ (i : ℕ)).subset ?_
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨fun i ↦ c i, fun i _ ↦ hc i,
    (Finset.sum_range fun i ↦ algebraMap K[X] K⸨X⸩ (c i) * g ^ Fintype.card K ^ i).symm⟩

/-- Over a finite field `K` with `q` elements, a power series algebraic over `K[X]` lies in a
finite set of power series that is stable under the Cartier operators `cartier K q r` with
`r < q`. -/
theorem exists_finite_cartier_stable_of_isAlgebraic {f : K⟦X⟧} (hf : IsAlgebraic K[X] f) :
    ∃ T : Set K⟦X⟧, T.Finite ∧ f ∈ T ∧
      ∀ h ∈ T, ∀ r < Fintype.card K, cartier K (Fintype.card K) r h ∈ T := by
  obtain ⟨m, a, ha0, hrel⟩ := exists_ore_relation hf
  -- Divide by the coefficient `a₀` of the Ore relation in the Laurent series field.
  set g : K⸨X⸩ := (f : K⸨X⸩) / algebraMap K[X] K⸨X⸩ (a 0)
  have hfg : (f : K⸨X⸩) = algebraMap K[X] K⸨X⸩ (a 0) * g :=
    (mul_div_cancel₀ _ ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr ha0)).symm
  set b : ℕ → K[X] := fun i ↦ -(a (i + 1) * a 0 ^ (Fintype.card K ^ (i + 1) - 2))
  -- A bound for the degrees of `a₀` and of the coefficients `bᵢ` of the relation for `g`.
  set N := max (a 0).natDegree ((Finset.range m).sup fun i ↦ (b i).natDegree)
  have hb (i : ℕ) (hi : i < m) : (b i).natDegree ≤ N :=
    le_max_of_le_right (Finset.le_sup (f := fun i ↦ (b i).natDegree) (Finset.mem_range.mpr hi))
  refine ⟨HahnSeries.ofPowerSeries ℤ K ⁻¹' _,
    (finite_setOf_eq_sum g m N).preimage HahnSeries.ofPowerSeries_injective.injOn,
    ⟨fun i ↦ if i = 0 then a 0 else 0, fun i ↦ ?_, ?_⟩, ?_⟩
  · dsimp only
    split_ifs
    · exact le_max_left _ _
    · simp
  · simp [Finset.sum_range_succ', hfg]
  · rintro h ⟨c, hc, hh⟩ r hr
    let d : ℕ+ := ⟨Fintype.card K, Fintype.card_pos⟩
    obtain ⟨c', hc', heq⟩ :=
      exists_contract_sum_eq d rfl (eq_sum_of_ore_relation ha0 hfg hrel) hb hc ⟨r, hr⟩
    refine ⟨c', hc', ?_⟩
    have hcoe : LaurentSeries.contract d (h : K⸨X⸩) ⟨r, hr⟩ =
        (cartier K (Fintype.card K) r h : K⸨X⸩) :=
      LaurentSeries.contract_coe d h ⟨r, hr⟩
    rw [← hcoe, hh, heq]

/-- **Algebraic power series have automatic coefficients.** Over a finite field `K` with `q`
elements, the coefficient sequence of a power series algebraic over `K[X]` is `q`-automatic. This
is the direction "algebraic implies automatic" of Christol's theorem. -/
theorem isAutomatic_coeff_of_isAlgebraic {f : K⟦X⟧} (hf : IsAlgebraic K[X] f) :
    TauCeti.IsAutomatic (Fintype.card K) fun n ↦ coeff n f := by
  obtain ⟨T, hT, hfT, hTk⟩ := exists_finite_cartier_stable_of_isAlgebraic hf
  exact isAutomatic_coeff_of_finite_cartier_stable Fintype.one_lt_card hT hfT hTk

end FiniteField

/-! The example checks the theorem on the indicator of the powers of two over `𝔽₂`: the series
`f = ∑ X ^ 2 ^ k` satisfies `f ^ 2 = f + X`, so it is a root of `T ^ 2 - T - X`. -/

example : TauCeti.IsAutomatic 2 ((Set.range (2 ^ ·)).indicator (1 : ℕ → ZMod 2)) := by
  set f : (ZMod 2)⟦X⟧ := mk ((Set.range (2 ^ ·)).indicator 1) with hf
  -- In characteristic two, `f ^ 2 = ∑ X ^ 2 ^ (k + 1) = f + X`.
  have hsq : f ^ 2 = f + X := by
    have hexp := FiniteField.PowerSeries.expand_card f
    simp only [ZMod.card] at hexp
    rw [← hexp]
    ext n
    obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
    · have hmem : 2 * m ∈ Set.range (2 ^ · : ℕ → ℕ) ↔ m ∈ Set.range (2 ^ · : ℕ → ℕ) := by
        refine ⟨fun ⟨k, hk⟩ ↦ ?_, fun ⟨k, hk⟩ ↦ ⟨k + 1, by simp only [pow_succ] at hk ⊢; omega⟩⟩
        cases k with
        | zero => simp at hk; omega
        | succ k => exact ⟨k, by simp only [pow_succ] at hk ⊢; omega⟩
      simp only [coeff_expand_mul, map_add, coeff_X, hf, coeff_mk, show 2 * m ≠ 1 by omega,
        ite_false, add_zero]
      by_cases h : m ∈ Set.range (2 ^ · : ℕ → ℕ)
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.2 h), Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hmem.1 h)]
    · rw [coeff_expand_of_not_dvd _ _ _ (by omega)]
      simp only [map_add, coeff_X, hf, coeff_mk]
      rcases eq_or_ne m 0 with rfl | hm
      · rw [Set.indicator_of_mem (show 1 ∈ Set.range (2 ^ · : ℕ → ℕ) from ⟨0, pow_zero 2⟩)]
        decide
      · simp only [show 2 * m + 1 ≠ 1 by omega, ite_false, add_zero]
        rw [Set.indicator_of_notMem]
        rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk; omega
        | succ k => simp only [pow_succ] at hk; omega
  have halg : IsAlgebraic (ZMod 2)[X] f := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C Polynomial.X, fun h ↦ ?_, ?_⟩
    · simpa [Polynomial.coeff_X, Polynomial.coeff_C] using congrArg (Polynomial.coeff · 2) h
    · simp [hsq, PowerSeries.algebraMap_apply']
  convert isAutomatic_coeff_of_isAlgebraic halg using 1
  · simp
  · funext n
    simp [hf]

end PowerSeries
