/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.PSeries
public import TauCeti.Analysis.Normed.Ring.InfiniteSum

/-!
# Multiple zeta values

An *index* is a finite list `k = [k₁, …, k_r]` of natural numbers; its weight is `k.sum` and its
depth is `k.length`. The multiple zeta value of a positive index is the series
```text
ζ(k₁, …, k_r) = ∑_{n₁ > n₂ > ⋯ > n_r > 0} n₁^(-k₁) n₂^(-k₂) ⋯ n_r^(-k_r),
```
summed over strictly decreasing tuples of positive integers, with `ζ([]) = 1`. The convention is
the descending one: the first entry `k₁` carries the largest summation variable. This is the
convention of Ihara, Kaneko and Zagier; Brown writes indices in increasing order, so his
`ζ(k_r, …, k₁)` is our `ζ(k₁, …, k_r)`.

A positive index is *admissible* when it is empty or its first entry is at least `2`. The main
result is that the series of a positive index converges exactly when the index is admissible.
For an admissible index of depth `r`, every term of the series is at most
`∏ i, n_i ^ (-(1 + 1/r))`, because the largest variable `n₁` dominates all the others; the latter
is a product of convergent `p`-series. If `k₁ = 1`, then fixing `n₂, …, n_r` leaves a tail of the
harmonic series.

By Brown's theorem, the periods of mixed Tate motives over `ℤ` are `ℚ[(2πi)⁻¹]`-linear
combinations of multiple zeta values; the shuffle and stuffle relations among multiple zeta values
are identities between the convergent series introduced here.

## Main definitions

* `TauCeti.MultipleZeta.PositiveIndex`, `TauCeti.MultipleZeta.Admissible`: positive and
  admissible indices.
* `TauCeti.MultipleZeta.descendingTuples r`: the strictly decreasing `r`-tuples of positive
  integers.
* `TauCeti.MultipleZeta.term k n`: the term `∏ i, n_i ^ (-k_i)` of the series.
* `TauCeti.multipleZeta k`: the multiple zeta value `ζ(k)`, as a sum of nonnegative reals.

## Main statements

* `TauCeti.MultipleZeta.summable_term_iff`: for a positive index, the series is summable if and
  only if the index is admissible.
* `TauCeti.hasSum_multipleZeta`, `TauCeti.multipleZeta_pos`: an admissible index has a convergent
  series with positive sum.
* `TauCeti.multipleZeta_nil`: `ζ([]) = 1`.
* `TauCeti.multipleZeta_singleton`, `TauCeti.ofReal_multipleZeta_singleton`: in depth one,
  `ζ([n]) = ∑_{m > 0} m^(-n)`, which is the value `riemannZeta n` of the Riemann zeta function
  for `n ≥ 2`; in particular `ζ([2]) = π² / 6` (`TauCeti.multipleZeta_two`).

## References

* K. Ihara, M. Kaneko, D. Zagier, *Derivation and double shuffle relations for multiple zeta
  values*, Compositio Math. 142 (2006), §1.
* F. Brown, *Mixed Tate motives over ℤ*, Ann. of Math. 175 (2012), Introduction.
-/

public section

noncomputable section

open Real

namespace TauCeti

namespace MultipleZeta

/-- An index is *positive* when all of its entries are positive. -/
def PositiveIndex (k : List ℕ) : Prop := ∀ n ∈ k, 0 < n

/-- A positive index is *admissible* when it is empty or its first entry, the exponent of the
largest summation variable, is at least `2`. -/
def Admissible (k : List ℕ) : Prop := PositiveIndex k ∧ ∀ n ∈ k.head?, 2 ≤ n

theorem positiveIndex_iff {k : List ℕ} : PositiveIndex k ↔ ∀ n ∈ k, 0 < n :=
  Iff.rfl

theorem PositiveIndex.pos {k : List ℕ} (hk : PositiveIndex k) {n : ℕ} (h : n ∈ k) : 0 < n :=
  hk n h

theorem admissible_iff {k : List ℕ} : Admissible k ↔ PositiveIndex k ∧ ∀ n ∈ k.head?, 2 ≤ n :=
  Iff.rfl

@[simp]
theorem positiveIndex_nil : PositiveIndex [] := by
  simp [PositiveIndex]

@[simp]
theorem positiveIndex_cons {a : ℕ} {k : List ℕ} :
    PositiveIndex (a :: k) ↔ 0 < a ∧ PositiveIndex k := by
  simp [PositiveIndex]

@[simp]
theorem admissible_nil : Admissible [] := by
  simp [Admissible]

@[simp]
theorem admissible_cons {a : ℕ} {k : List ℕ} :
    Admissible (a :: k) ↔ 2 ≤ a ∧ PositiveIndex k := by
  simp only [Admissible, positiveIndex_cons, List.head?_cons, Option.mem_def, Option.some.injEq,
    forall_eq']
  exact ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨by omega, h.2⟩, h.1⟩⟩

theorem Admissible.positiveIndex {k : List ℕ} (hk : Admissible k) : PositiveIndex k :=
  hk.1

/-- The summation range of a multiple zeta value of depth `r`: the strictly decreasing `r`-tuples
`n₀ > n₁ > ⋯ > n_{r-1} > 0` of positive integers. -/
def descendingTuples (r : ℕ) : Set (Fin r → ℕ) := {n | (∀ i, 0 < n i) ∧ StrictAnti n}

@[simp]
theorem mem_descendingTuples {r : ℕ} {n : Fin r → ℕ} :
    n ∈ descendingTuples r ↔ (∀ i, 0 < n i) ∧ StrictAnti n :=
  Iff.rfl

/-- The tuple `(N + r, r - 1, …, 1)` is a strictly decreasing `r`-tuple of positive integers. -/
theorem ite_mem_descendingTuples (N r : ℕ) :
    (fun i : Fin r ↦ if (i : ℕ) = 0 then N + r else r - (i : ℕ)) ∈ descendingTuples r :=
  ⟨fun i ↦ by have := i.isLt; simp only; split_ifs <;> omega, fun i j hij ↦ by
    have := Fin.lt_def.mp hij
    simp only
    split_ifs <;> omega⟩

/-- The tuple `(r, r - 1, …, 1)` is a strictly decreasing `r`-tuple of positive integers. -/
theorem sub_mem_descendingTuples (r : ℕ) : (fun i : Fin r ↦ r - (i : ℕ)) ∈ descendingTuples r := by
  convert ite_mem_descendingTuples 0 r using 2 with i
  split_ifs with hi <;> simp [hi]

/-- The term `∏ i, n_i ^ (-k_i)` of the multiple zeta series of the index `k` at the tuple `n`. -/
def term (k : List ℕ) (n : Fin k.length → ℕ) : ℝ := ∏ i, ((n i : ℝ) ^ k[i])⁻¹

theorem term_def (k : List ℕ) (n : Fin k.length → ℕ) : term k n = ∏ i, ((n i : ℝ) ^ k[i])⁻¹ :=
  (rfl)

@[simp]
theorem term_nil (n : Fin ([] : List ℕ).length → ℕ) : term [] n = 1 :=
  Fin.prod_univ_zero _

/-- The term of `a :: k` splits off the factor of the largest summation variable. -/
theorem term_cons (a : ℕ) (k : List ℕ) (n : Fin (a :: k).length → ℕ) :
    term (a :: k) n = ((n 0 : ℝ) ^ a)⁻¹ * term k (Fin.tail n) :=
  Fin.prod_univ_succ (n := k.length) _

theorem term_nonneg (k : List ℕ) (n : Fin k.length → ℕ) : 0 ≤ term k n := by
  unfold term
  positivity

theorem term_pos (k : List ℕ) {n : Fin k.length → ℕ} (hn : ∀ i, 0 < n i) : 0 < term k n :=
  Finset.prod_pos fun i _ ↦ by have := hn i; positivity

end MultipleZeta

open MultipleZeta

/-- The *multiple zeta value* `ζ(k₁, …, k_r) = ∑_{n₁ > ⋯ > n_r > 0} ∏ i, n_i ^ (-k_i)` of an index
`k`, in descending convention. It is the sum of a series of nonnegative reals, which converges for
a positive index exactly when the index is admissible (`MultipleZeta.summable_term_iff`); the
value is `0` when the series diverges. -/
def multipleZeta (k : List ℕ) : ℝ := ∑' n : descendingTuples k.length, term k n

theorem multipleZeta_eq_tsum (k : List ℕ) :
    multipleZeta k = ∑' n : descendingTuples k.length, term k n :=
  (rfl)

theorem multipleZeta_nonneg (k : List ℕ) : 0 ≤ multipleZeta k :=
  tsum_nonneg fun n ↦ term_nonneg k n

namespace MultipleZeta

/-- The largest summation variable dominates: for a nonempty admissible index of depth `r`,
every term of the series is at most `∏ i, n_i ^ (-(1 + 1/r))`. -/
private theorem term_le_prod_rpow {k : List ℕ} (hk : Admissible k) (hk0 : k ≠ [])
    {n : Fin k.length → ℕ} (hn : n ∈ descendingTuples k.length) :
    term k n ≤ ∏ i, ((n i : ℝ) ^ (1 + (k.length : ℝ)⁻¹))⁻¹ := by
  have hr : 0 < k.length := List.length_pos_iff.mpr hk0
  let i₀ : Fin k.length := ⟨0, hr⟩
  have hpos : ∀ i, (1 : ℝ) ≤ n i := fun i ↦ by exact_mod_cast hn.1 i
  have hle : ∀ i, (n i : ℝ) ≤ n i₀ := fun i ↦ by
    exact_mod_cast hn.2.antitone (Fin.le_def.mpr (Nat.zero_le i))
  have hexp : ∀ i : Fin k.length, 1 ≤ k[i] := fun i ↦ hk.1 _ (List.getElem_mem _)
  have hexp₀ : 2 ≤ k[i₀] := hk.2 _ (by rcases k with _ | ⟨a, k⟩ <;> simp_all [i₀])
  rw [term_def, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  refine inv_anti₀ (Finset.prod_pos fun i _ ↦ by have := hpos i; positivity) ?_
  -- `∏ n_i ^ (1 + 1/r) = (∏ n_i) (∏ n_i ^ (1/r)) ≤ (∏ n_i) n_{i₀} ≤ ∏ n_i ^ k_i`.
  calc ∏ i, (n i : ℝ) ^ (1 + (k.length : ℝ)⁻¹)
      = (∏ i, (n i : ℝ)) * ∏ i, (n i : ℝ) ^ (k.length : ℝ)⁻¹ := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [rpow_add (by linarith [hpos i]), rpow_one]
    _ ≤ (∏ i, (n i : ℝ)) * ∏ _i : Fin k.length, (n i₀ : ℝ) ^ (k.length : ℝ)⁻¹ := by
        gcongr with i
        exact_mod_cast hle i
    _ = (∏ i, (n i : ℝ)) * n i₀ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          rpow_inv_natCast_pow (by linarith [hpos i₀]) hr.ne']
    _ = n i₀ * n i₀ * ∏ i ∈ Finset.univ.erase i₀, (n i : ℝ) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
        ring
    _ ≤ (n i₀ : ℝ) ^ k[i₀] * ∏ i ∈ Finset.univ.erase i₀, (n i : ℝ) ^ k[i] := by
        gcongr with i
        · rw [← pow_two]
          exact pow_le_pow_right₀ (hpos i₀) hexp₀
        · exact le_self_pow₀ (hpos i) (by have := hexp i; omega)
    _ = ∏ i, (n i : ℝ) ^ k[i] :=
        Finset.mul_prod_erase _ (fun i ↦ (n i : ℝ) ^ k[i]) (Finset.mem_univ i₀)

/-- The series of an admissible index converges. -/
private theorem summable_term_of_admissible {k : List ℕ} (hk : Admissible k) :
    Summable fun n : descendingTuples k.length ↦ term k n := by
  by_cases hk0 : k = []
  · subst hk0
    have : Subsingleton (Fin ([] : List ℕ).length → ℕ) := ⟨fun _ _ ↦ funext fun i ↦ i.elim0⟩
    exact .of_finite
  have hp : (1 : ℝ) < 1 + (k.length : ℝ)⁻¹ :=
    lt_add_of_pos_right _ (inv_pos.mpr (by exact_mod_cast List.length_pos_iff.mpr hk0))
  have hsum : Summable fun n : Fin k.length → ℕ ↦
      ∏ i, ((n i : ℝ) ^ (1 + (k.length : ℝ)⁻¹))⁻¹ := by
    refine (summable_norm_prod_of_summable_norm (ι := Fin k.length)
      (f := fun _ (b : ℕ) ↦ ((b : ℝ) ^ (1 + (k.length : ℝ)⁻¹))⁻¹) fun _ ↦ ?_).of_norm
    refine (summable_nat_rpow_inv.mpr hp).congr fun b ↦ ?_
    rw [Real.norm_of_nonneg (by positivity)]
  exact .of_nonneg_of_le (fun n ↦ term_nonneg _ _) (fun n ↦ term_le_prod_rpow hk hk0 n.property)
    (hsum.comp_injective Subtype.val_injective)

/-- The series of an index whose first entry is `1` diverges: fixing the smaller variables to
`r - 1, …, 1` leaves a tail of the harmonic series. -/
private theorem not_summable_term_cons_one (k : List ℕ) :
    ¬ Summable fun n : descendingTuples (1 :: k).length ↦ term (1 :: k) n := by
  intro h
  set r := (1 :: k).length
  -- The tuple `(N + r, r - 1, …, 1)`.
  let t : ℕ → descendingTuples r := fun N ↦ ⟨_, ite_mem_descendingTuples N r⟩
  have ht : Function.Injective t := fun N M h ↦ by
    simpa [t] using congrFun (congrArg Subtype.val h) ⟨0, by simp [r]⟩
  set C : ℝ := ∏ i : Fin k.length, (((k.length - i : ℕ) : ℝ) ^ k[i])⁻¹
  have hC : 0 < C := Finset.prod_pos fun i _ ↦ by
    have : (0 : ℝ) < ((k.length - i : ℕ) : ℝ) := by exact_mod_cast (by omega)
    positivity
  have hterm : ∀ N, term (1 :: k) (t N) = C * ((N + r : ℕ) : ℝ)⁻¹ := fun N ↦ by
    rw [term_cons, term_def]
    simp [t, r, C, Fin.tail, mul_comm]
  have := (h.comp_injective ht).mul_left C⁻¹
  simp only [Function.comp_def, hterm, ← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at this
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff r).mp this)

/-- **Convergence of multiple zeta values.** The multiple zeta series of a positive index `k`
converges if and only if `k` is admissible, that is, empty or with first entry at least `2`. -/
theorem summable_term_iff {k : List ℕ} (hk : PositiveIndex k) :
    (Summable fun n : descendingTuples k.length ↦ term k n) ↔ Admissible k := by
  refine ⟨fun h ↦ ?_, summable_term_of_admissible⟩
  rcases k with _ | ⟨a, k⟩
  · exact admissible_nil
  obtain ⟨ha, hk'⟩ := positiveIndex_cons.mp hk
  refine admissible_cons.mpr ⟨?_, hk'⟩
  by_contra ha2
  obtain rfl : a = 1 := by omega
  exact not_summable_term_cons_one k h

end MultipleZeta

/-- The series of an admissible index converges to its multiple zeta value. -/
theorem hasSum_multipleZeta {k : List ℕ} (hk : Admissible k) :
    HasSum (fun n : descendingTuples k.length ↦ term k n) (multipleZeta k) :=
  ((summable_term_iff hk.positiveIndex).mpr hk).hasSum

/-- The multiple zeta value of an admissible index is positive. -/
theorem multipleZeta_pos {k : List ℕ} (hk : Admissible k) : 0 < multipleZeta k :=
  (hasSum_multipleZeta hk).summable.tsum_pos (fun n ↦ term_nonneg k n)
    ⟨_, sub_mem_descendingTuples k.length⟩ (term_pos k (sub_mem_descendingTuples _).1)

/-- The multiple zeta value of the empty index is the empty product `1`. -/
@[simp]
theorem multipleZeta_nil : multipleZeta [] = 1 := by
  rw [multipleZeta_eq_tsum, tsum_eq_single ⟨finZeroElim, fun i ↦ i.elim0, fun i ↦ i.elim0⟩]
  · exact term_nil _
  · exact fun n hn ↦ (hn (Subtype.ext (funext fun i ↦ i.elim0))).elim

/-- In depth one the multiple zeta value is the sum `ζ([n]) = ∑_{m ≥ 0} (m + 1)^(-n)` over all
positive integers. -/
theorem multipleZeta_singleton (n : ℕ) :
    multipleZeta [n] = ∑' m : ℕ, (((m : ℝ) + 1) ^ n)⁻¹ := by
  have h0 : ∀ i : Fin [n].length, i = ⟨0, by simp⟩ := fun i ↦
    Fin.ext (by have := i.isLt; simp only [List.length_singleton] at this ⊢; omega)
  let e : ℕ ≃ descendingTuples [n].length :=
    { toFun m := ⟨fun _ ↦ m + 1, fun _ ↦ m.succ_pos, fun i j hij ↦ by
        rw [h0 i, h0 j] at hij
        exact absurd hij (lt_irrefl _)⟩
      invFun a := a.val ⟨0, by simp⟩ - 1
      left_inv m := by simp
      right_inv a := Subtype.ext <| funext fun i ↦ by
        have := a.property.1 ⟨0, by simp⟩
        rw [h0 i]
        simp only
        omega }
  rw [multipleZeta_eq_tsum, ← e.tsum_eq]
  simp [term_def, e]

/-- In depth one the multiple zeta value is the Riemann zeta value: `ζ([n]) = riemannZeta n` for
`n ≥ 2`. -/
theorem ofReal_multipleZeta_singleton {n : ℕ} (hn : 2 ≤ n) :
    (multipleZeta [n] : ℂ) = riemannZeta n := by
  rw [multipleZeta_singleton, zeta_eq_tsum_one_div_nat_add_one_cpow (by simp; omega),
    Complex.ofReal_tsum]
  simp

/-- **Euler's evaluation** `ζ(2) = π² / 6`. -/
theorem multipleZeta_two : multipleZeta [2] = π ^ 2 / 6 := by
  have := ofReal_multipleZeta_singleton le_rfl
  rw [Nat.cast_ofNat, riemannZeta_two] at this
  exact_mod_cast this

end TauCeti
