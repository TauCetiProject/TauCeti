/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Fintype.Lattice
import TauCeti.Algebra.Order.AbsoluteValue.Basic
import TauCeti.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Evertse's lemma for a field with simultaneous approximation

Let `K` be a field, `V` a `K`-vector space with linearly independent vectors
`x 0, …, x (m - 1)`, and let `T` be a set of absolute values on `K`. At each `v ∈ T` let `m`
linear forms `L v k` separate the points of `V`, let weights `ν v k > 0` and a nondecreasing
sequence `μ v 0 ≤ … ≤ μ v (m - 1)` bound the values `v (L v k (x j)) ≤ ν v k * μ v j`.
**Evertse's lemma** replaces `x` by vectors

`y j = x j + ∑ l < j, ξ j l • x l`

with coefficients `ξ j l` in a subset `R ⊆ K` and reorders the forms at each place by a
permutation `π v`, so that every value is bounded by the **smaller** of the two relevant
sequence terms:

`v (L v (π v i) (y j)) ≤ C * ν v (π v i) * min (μ v i) (μ v j)`.

The only arithmetic input is that `R` approximates every family of targets at the places of `T`
simultaneously: for every `γ` some `ξ ∈ R` has `v (ξ + γ v) ≤ A v` for all `v ∈ T`
(`AbsoluteValue.exists_evertse_of_approx`). The constant is `C = 2 ^ (2 m + 1) * max 1 (A v)` at
every place, and `C = 1` at a nonarchimedean place where `A v ≤ 1`.

Over a number field, with `R` the elements integral outside a finite set of finite places, this
is the form of Evertse's lemma that replaces Mahler's theorem on compound bodies and Davenport's
lemma in the proof of Schmidt's Subspace Theorem: it turns a family of vectors realizing the
successive minima of a parallelepiped into one whose exterior products are controlled.

The proof has two steps.
* At one place the vectors are made exactly triangular: column elimination with partial
  pivoting, where the pivot row for `x j` maximizes `v (L v r (·)) / ν v r`, produces
  `z j ∈ x j + span (x l, l < j)` with `L v (π i) (z j) = 0` for `i < j`, at the cost of a
  factor `2` per elimination step, or `1` when `v` is nonarchimedean.
* These local triangular families are glued by approximation: the coefficients `ξ j l` are
  chosen from `l = j - 1` down to `0`, each one approximating at every place at once the
  coordinate of the remaining error on `z l`, so that `y j - z j` is a combination of the
  `z l`, `l < j`, with coefficients of size at most `A v` at `v`.

## Main results

* `AbsoluteValue.exists_evertse_of_approx`: Evertse's lemma for any field and any set of
  absolute values admitting simultaneous approximation by a subset `R`.

## References

* J.-H. Evertse, *An improvement of the quantitative Subspace theorem*, Compositio Math. 101
  (1996), 225–311.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press, 2006,
  Lemma 7.5.29.
-/

public section

open Finset Submodule

namespace AbsoluteValue

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `Set.Iio j` in `Fin n`, as a condition on values. -/
private theorem Iio_eq_setOf_val_lt {n : ℕ} (j : Fin n) :
    Set.Iio j = {l : Fin n | l.val < j.val} :=
  Set.ext fun _ ↦ Fin.lt_def

/-- **Elimination with partial pivoting at one place.** If the forms `L r` separate the points of
`V` and `x 0, …, x (n - 1)` are independent in the triangular sense, then there are vectors
`z j ∈ x j + span (x l, l < j)` and rows `π j` with `L (π i) (z j) = 0` for `i < j` and
`L (π j) (z j) ≠ 0`, whose values grow by at most `c ^ n` over those of the `x j`. -/
private theorem exists_triangular {ρ : Type*} [Finite ρ] (v : AbsoluteValue K ℝ) {c : ℝ}
    (hc : 1 ≤ c) (hv : ∀ a b, v (a + b) ≤ c * max (v a) (v b)) (L : ρ → Module.Dual K V)
    (hL : ∀ z, (∀ r, L r z = 0) → z = 0) {ν : ρ → ℝ} (hν : ∀ r, 0 < ν r) :
    ∀ (n : ℕ) (x : Fin n → V), (∀ j, x j ∉ span K (x '' Set.Iio j)) → ∀ M : Fin n → ℝ,
      (∀ j r, v (L r (x j)) ≤ ν r * M j) →
      ∃ (z : Fin n → V) (π : Fin n → ρ), (∀ j, z j - x j ∈ span K (x '' Set.Iio j)) ∧
        (∀ i j, i < j → L (π i) (z j) = 0) ∧ (∀ j, L (π j) (z j) ≠ 0) ∧
        ∀ j r, v (L r (z j)) ≤ c ^ n * (ν r * M j)
  | 0, x, _, M, _ => ⟨x, fun j ↦ j.elim0, fun j ↦ j.elim0, fun _ j ↦ j.elim0, fun j ↦ j.elim0,
      fun j ↦ j.elim0⟩
  | n + 1, x, hx, M, hM => by
    -- Pivot: the row maximizing `v (L r (x 0)) / ν r`, where `L r (x 0) ≠ 0`.
    have hx0 : x 0 ≠ 0 := fun h ↦ hx 0 (h ▸ zero_mem _)
    obtain ⟨r₁, hr₁⟩ : ∃ r, L r (x 0) ≠ 0 := by
      by_contra! h
      exact hx0 (hL _ h)
    have : Nonempty ρ := ⟨r₁⟩
    obtain ⟨r₀, hr₀⟩ := Finite.exists_max fun r ↦ v (L r (x 0)) / ν r
    have hpos : 0 < v (L r₀ (x 0)) := by
      have h₁ : 0 < v (L r₁ (x 0)) / ν r₁ := div_pos (v.pos hr₁) (hν r₁)
      have h₂ := (h₁.trans_le (hr₀ r₁))
      exact (div_pos_iff_of_pos_right (hν r₀)).mp h₂
    have hp : L r₀ (x 0) ≠ 0 := fun h ↦ by simp [h] at hpos
    -- Eliminate the pivot row from the later vectors.
    set t : Fin n → K := fun j ↦ L r₀ (x j.succ) / L r₀ (x 0) with ht
    set x' : Fin n → V := fun j ↦ x j.succ - t j • x 0 with hx'
    have hx'r₀ (j : Fin n) : L r₀ (x' j) = 0 := by
      simp [hx', ht, div_mul_cancel₀ _ hp]
    have hspan (j : Fin n) : span K (x' '' Set.Iio j) ≤ span K (x '' Set.Iio j.succ) := by
      rw [span_le]
      rintro _ ⟨l, hl, rfl⟩
      exact sub_mem (subset_span ⟨l.succ, Fin.succ_lt_succ_iff.mpr hl, rfl⟩)
        (smul_mem _ _ (subset_span ⟨0, Fin.succ_pos j, rfl⟩))
    have hx'ind (j : Fin n) : x' j ∉ span K (x' '' Set.Iio j) := fun h ↦ by
      refine hx j.succ ?_
      have hmem := add_mem (hspan j h) (smul_mem _ (t j) (subset_span ⟨0, Fin.succ_pos j, rfl⟩))
      simp only [hx', sub_add_cancel] at hmem
      exact hmem
    have hM' (j : Fin n) (r : ρ) : v (L r (x' j)) ≤ ν r * (c * M j.succ) := by
      have h := apply_sub_div_mul_le (zero_le_one.trans hc) hv (hν r) (hν r₀) hpos (hM j.succ r)
        (hM j.succ r₀) (hr₀ r)
      simp only [hx', ht, map_sub, map_smul, smul_eq_mul]
      linarith
    obtain ⟨z', π', hz', hzero', hpiv', hbd'⟩ :=
      exists_triangular v hc hv L hL hν n x' hx'ind (fun j ↦ c * M j.succ) hM'
    -- The later vectors vanish in the pivot row.
    have hz'r₀ (j : Fin n) : L r₀ (z' j) = 0 := by
      have hker : span K (x' '' Set.Iio j) ≤ LinearMap.ker (L r₀) := by
        rw [span_le]
        rintro _ ⟨l, -, rfl⟩
        exact hx'r₀ l
      have := hker (hz' j)
      rw [LinearMap.mem_ker, map_sub, hx'r₀, sub_zero] at this
      exact this
    refine ⟨Fin.cons (x 0) z', Fin.cons r₀ π', fun j ↦ ?_, fun i j hij ↦ ?_, fun j ↦ ?_,
      fun j r ↦ ?_⟩
    · cases j using Fin.cases with
      | zero => simp
      | succ j =>
        have hmem := sub_mem (hspan j (hz' j))
          (smul_mem _ (t j) (subset_span ⟨0, Fin.succ_pos j, rfl⟩))
        simp only [hx', sub_sub, sub_add_cancel] at hmem
        simpa only [Fin.cons_succ] using hmem
    · cases j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero i)
      | succ j =>
        cases i using Fin.cases with
        | zero => simpa using hz'r₀ j
        | succ i => simpa using hzero' i j (Fin.succ_lt_succ_iff.mp hij)
    · cases j using Fin.cases with
      | zero => simpa using hp
      | succ j => simpa using hpiv' j
    · cases j using Fin.cases with
      | zero =>
        have h₀ : 0 ≤ ν r * M 0 := (v.nonneg _).trans (hM 0 r)
        simpa using (hM 0 r).trans (le_mul_of_one_le_left h₀ (one_le_pow₀ hc))
      | succ j =>
        simp only [Fin.cons_succ]
        calc v (L r (z' j)) ≤ c ^ n * (ν r * (c * M j.succ)) := hbd' j r
          _ = c ^ (n + 1) * (ν r * M j.succ) := by ring

/-- **Gluing by simultaneous approximation.** Let `z v j ∈ x j + span (x l, l < j)` for every
absolute value `v`. A target `w v` in the span of the `z v l` with `l < s` is matched, at all
places of `T` at once, by a combination of the `x l`, `l < s`, with coefficients in `R`, up to a
combination of the `z v l`, `l < s`, with coefficients of size at most `A v`. -/
private theorem exists_sum_smul_sub_eq {T : Set (AbsoluteValue K ℝ)} {R : Set K}
    {A : AbsoluteValue K ℝ → ℝ} (happrox : ∀ γ : AbsoluteValue K ℝ → K, ∃ ξ ∈ R, ∀ v ∈ T,
      v (ξ + γ v) ≤ A v) {n : ℕ} {x : Fin n → V} {z : AbsoluteValue K ℝ → Fin n → V}
    (hz : ∀ v j, z v j - x j ∈ span K (x '' Set.Iio j)) :
    ∀ s ≤ n, ∀ w : AbsoluteValue K ℝ → V, (∀ v, w v ∈ span K (z v '' {l | l.val < s})) →
      ∃ ξ : Fin n → K, (∀ l, ξ l ∈ R) ∧ ∀ v ∈ T, ∃ e : Fin n → K, (∀ l, v (e l) ≤ A v) ∧
        ∑ l ∈ univ.filter (·.val < s), ξ l • x l - w v =
          ∑ l ∈ univ.filter (·.val < s), e l • z v l
  | 0, _, w, hw => by
    obtain ⟨ξ₀, hξ₀, hA⟩ := happrox 0
    refine ⟨fun _ ↦ ξ₀, fun _ ↦ hξ₀, fun v hv ↦ ⟨0, fun _ ↦ ?_, ?_⟩⟩
    · simpa using (v.nonneg _).trans (hA v hv)
    · have : w v = 0 := by simpa using hw v
      simp [this]
  | s + 1, hs, w, hw => by
    classical
    set ls : Fin n := ⟨s, hs⟩
    have hset : {l : Fin n | l.val < s + 1} = insert ls {l | l.val < s} := by
      ext l
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, ls, Fin.ext_iff]
      omega
    have hfilter : univ.filter (fun l : Fin n ↦ l.val < s + 1) =
        insert ls (univ.filter (·.val < s)) := by
      ext l
      simp only [mem_filter, mem_univ, true_and, mem_insert, ls, Fin.ext_iff]
      omega
    have hls : ls ∉ univ.filter (fun l : Fin n ↦ l.val < s) := by simp [ls]
    -- Split off the coefficient of `z v ls` and approximate it at every place at once.
    have hdec (v : AbsoluteValue K ℝ) :
        ∃ a : K, ∃ w' ∈ span K (z v '' {l | l.val < s}), w v = a • z v ls + w' := by
      have := hw v
      rwa [hset, Set.image_insert_eq, mem_span_insert] at this
    choose a w' hw' hweq using hdec
    obtain ⟨ξs, hξs, hA⟩ := happrox fun v ↦ -a v
    have hw'' (v : AbsoluteValue K ℝ) :
        w' v + ξs • (z v ls - x ls) ∈ span K (z v '' {l | l.val < s}) := by
      refine add_mem (hw' v) (smul_mem _ _ ?_)
      have := (span_image_Iio_eq_span_image_Iio (hz v) ls).ge (hz v ls)
      rwa [Iio_eq_setOf_val_lt] at this
    obtain ⟨ξ, hξ, he⟩ := exists_sum_smul_sub_eq happrox hz s (Nat.le_of_succ_le hs)
      (fun v ↦ w' v + ξs • (z v ls - x ls)) hw''
    refine ⟨Function.update ξ ls ξs, fun l ↦ ?_, fun v hv ↦ ?_⟩
    · rcases eq_or_ne l ls with rfl | hl
      · simpa using hξs
      · simpa [hl] using hξ l
    obtain ⟨e, he_le, heq⟩ := he v hv
    refine ⟨Function.update e ls (ξs - a v), fun l ↦ ?_, ?_⟩
    · rcases eq_or_ne l ls with rfl | hl
      · simpa [sub_eq_add_neg] using hA v hv
      · simpa [hl] using he_le l
    have hξsum : ∑ l ∈ univ.filter (·.val < s), Function.update ξ ls ξs l • x l =
        ∑ l ∈ univ.filter (·.val < s), ξ l • x l :=
      sum_congr rfl fun l hl ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hl hls)]
    have hesum : ∑ l ∈ univ.filter (·.val < s), Function.update e ls (ξs - a v) l • z v l =
        ∑ l ∈ univ.filter (·.val < s), e l • z v l :=
      sum_congr rfl fun l hl ↦ by rw [Function.update_of_ne (ne_of_mem_of_not_mem hl hls)]
    rw [hfilter, sum_insert hls, sum_insert hls, hξsum, hesum, ← heq, hweq v,
      Function.update_self, Function.update_self]
    simp only [sub_smul, smul_sub]
    abel

/-- **The bound at one place.** Let `z` be triangular at `v` in the rows `π`, with values bounded
by `c ^ m * (ν r * μ j)` for a nondecreasing `μ`. Then `z j` corrected by a combination of the
earlier `z l` with coefficients of size at most `a` takes values at most
`c ^ (2 m + 1) * max 1 a * (ν (π i) * min (μ i) (μ j))` in the row `π i`. -/
private theorem apply_add_sum_le {m : ℕ} {v : AbsoluteValue K ℝ} {c : ℝ} (hc : 1 ≤ c)
    (hv : ∀ a b, v (a + b) ≤ c * max (v a) (v b)) {L : Fin m → Module.Dual K V}
    {π : Fin m → Fin m} {z : Fin m → V} (h₀ : ∀ i j, i < j → L (π i) (z j) = 0)
    {ν μ : Fin m → ℝ} (hbd : ∀ j r, v (L r (z j)) ≤ c ^ m * (ν r * μ j)) (hν : ∀ r, 0 < ν r)
    (hμ : Monotone μ) (hμ₀ : ∀ l, 0 ≤ μ l) {a : ℝ} {e : Fin m → K} (he : ∀ l, v (e l) ≤ a)
    (i j : Fin m) :
    v (L (π i) (z j + ∑ l ∈ univ.filter (· < j), e l • z l)) ≤
      c ^ (2 * m + 1) * max 1 a * (ν (π i) * min (μ i) (μ j)) := by
  rw [map_add, map_sum]
  set r := π i
  have hc₀ : 0 ≤ c := zero_le_one.trans hc
  have ha₀ : 0 ≤ max 1 a := zero_le_one.trans (le_max_left _ _)
  have hν₀ := (hν r).le
  set B := max 1 a * (c ^ m * (ν r * min (μ i) (μ j))) with hB
  have hB₀ : 0 ≤ B := by
    have := le_min (hμ₀ i) (hμ₀ j)
    positivity
  -- Every term vanishes or is bounded through the smaller of `μ i` and `μ j`.
  have hzj : v (L r (z j)) ≤ B := by
    rcases lt_or_ge i j with h | h
    · rw [h₀ i j h, map_zero]
      exact hB₀
    · rw [hB, min_eq_right (hμ h)]
      exact (hbd j r).trans (le_mul_of_one_le_left
        (mul_nonneg (pow_nonneg hc₀ _) (mul_nonneg hν₀ (hμ₀ j))) (le_max_left _ _))
  have hzl (l : Fin m) (hl : l ∈ univ.filter (· < j)) : v (L r (e l • z l)) ≤ B := by
    rw [map_smul, smul_eq_mul, map_mul]
    rcases lt_or_ge i l with h | h
    · rw [h₀ i l h, map_zero, mul_zero]
      exact hB₀
    · have hmin : μ l ≤ min (μ i) (μ j) := le_min (hμ h) (hμ (mem_filter.mp hl).2.le)
      refine mul_le_mul ((he l).trans (le_max_right _ _)) ((hbd l r).trans ?_) (v.nonneg _) ha₀
      gcongr
  have hsum := apply_sum_le_pow_mul hc hv _ _ hB₀ hzl
  have hcard : (univ.filter (fun l : Fin m ↦ l < j)).card ≤ m :=
    (card_filter_le _ _).trans (by simp)
  calc v (L r (z j) + ∑ l ∈ univ.filter (· < j), L r (e l • z l))
      ≤ c * max (v (L r (z j))) (v (∑ l ∈ univ.filter (· < j), L r (e l • z l))) := hv _ _
    _ ≤ c * (c ^ m * B) := by
        gcongr
        exact max_le (hzj.trans (le_mul_of_one_le_left hB₀ (one_le_pow₀ hc)))
          (hsum.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc hcard) hB₀))
    _ = c ^ (2 * m + 1) * max 1 a * (ν r * min (μ i) (μ j)) := by
        rw [hB]
        ring

/-- **Evertse's lemma** (Evertse; Bombieri–Gubler, Lemma 7.5.29), for a field `K` with a set `T`
of absolute values at which a subset `R` approximates every family of targets simultaneously,
`v (ξ + γ v) ≤ A v`. Let `x 0, …, x (m - 1)` be linearly independent in `V`, and at each `v ∈ T`
let the forms `L v k` separate the points of `V`, with weights `ν v k > 0` and a nondecreasing
`μ v` bounding `v (L v k (x j)) ≤ ν v k * μ v j`. Then there are coefficients `ξ j l ∈ R` and
permutations `π v` such that `y j = x j + ∑ l < j, ξ j l • x l` satisfies
`v (L v (π v i) (y j)) ≤ 2 ^ (2 m + 1) * max 1 (A v) * (ν v (π v i) * min (μ v i) (μ v j))`
at every `v ∈ T`, and the same bound without the constant at every nonarchimedean `v ∈ T` with
`A v ≤ 1`. -/
theorem exists_evertse_of_approx {m : ℕ} {T : Set (AbsoluteValue K ℝ)} {R : Set K}
    {A : AbsoluteValue K ℝ → ℝ}
    (happrox : ∀ γ : AbsoluteValue K ℝ → K, ∃ ξ ∈ R, ∀ v ∈ T, v (ξ + γ v) ≤ A v)
    {L : AbsoluteValue K ℝ → Fin m → Module.Dual K V}
    (hL : ∀ v ∈ T, ∀ z : V, (∀ k, L v k z = 0) → z = 0) {x : Fin m → V}
    (hx : LinearIndependent K x) {ν μ : AbsoluteValue K ℝ → Fin m → ℝ}
    (hν : ∀ v ∈ T, ∀ k, 0 < ν v k) (hμ : ∀ v ∈ T, Monotone (μ v))
    (hLx : ∀ v ∈ T, ∀ k j, v (L v k (x j)) ≤ ν v k * μ v j) :
    ∃ (ξ : Fin m → Fin m → K) (π : AbsoluteValue K ℝ → Equiv.Perm (Fin m)),
      (∀ j l, ξ j l ∈ R) ∧
      (∀ v ∈ T, ∀ i j, v (L v (π v i) (x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l)) ≤
        2 ^ (2 * m + 1) * max 1 (A v) * (ν v (π v i) * min (μ v i) (μ v j))) ∧
      ∀ v ∈ T, IsNonarchimedean v → A v ≤ 1 → ∀ i j,
        v (L v (π v i) (x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l)) ≤
          ν v (π v i) * min (μ v i) (μ v j) := by
  classical
  have hxI (j : Fin m) : x j ∉ span K (x '' Set.Iio j) := hx.notMem_span_image (lt_irrefl j)
  -- The growth factor of one addition at `v`: `1` if `v` is nonarchimedean, `2` otherwise.
  set c : AbsoluteValue K ℝ → ℝ := fun v ↦ if IsNonarchimedean v then 1 else 2 with hc_def
  have hc (v : AbsoluteValue K ℝ) : 1 ≤ c v := by
    simp only [hc_def]
    split_ifs <;> norm_num
  have hc₂ (v : AbsoluteValue K ℝ) : c v ≤ 2 := by
    simp only [hc_def]
    split_ifs <;> norm_num
  have hcv (v : AbsoluteValue K ℝ) (a b : K) : v (a + b) ≤ c v * max (v a) (v b) := by
    by_cases h : IsNonarchimedean v
    · simpa [hc_def, h] using h a b
    · simp only [hc_def, h, ↓reduceIte]
      linarith [v.add_le a b, le_max_left (v a) (v b), le_max_right (v a) (v b)]
  -- Step 1: an exactly triangular family at each place of `T`.
  have hloc (v : AbsoluteValue K ℝ) : ∃ (z : Fin m → V) (π : Fin m → Fin m),
      (∀ j, z j - x j ∈ span K (x '' Set.Iio j)) ∧ (v ∈ T →
        (∀ i j, i < j → L v (π i) (z j) = 0) ∧ (∀ j, L v (π j) (z j) ≠ 0) ∧
          ∀ j r, v (L v r (z j)) ≤ c v ^ m * (ν v r * μ v j)) := by
    by_cases hv : v ∈ T
    · obtain ⟨z, π, h₁, h₂, h₃, h₄⟩ := exists_triangular v (hc v) (hcv v) (L v) (hL v hv)
        (hν v hv) m x hxI (μ v) fun j r ↦ hLx v hv r j
      exact ⟨z, π, h₁, fun _ ↦ ⟨h₂, h₃, h₄⟩⟩
    · exact ⟨x, id, fun j ↦ by simp, fun h ↦ absurd h hv⟩
  choose z π hzx hz using hloc
  have hπ (v : AbsoluteValue K ℝ) (hv : v ∈ T) : Function.Injective (π v) := by
    intro i j hij
    obtain ⟨h₀, hp, -⟩ := hz v hv
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hp j (hij ▸ h₀ i j h)
    · exact hp i (hij.symm ▸ h₀ j i h)
  set σ : AbsoluteValue K ℝ → Equiv.Perm (Fin m) := fun v ↦
    if hv : v ∈ T then Equiv.ofBijective (π v) (Finite.injective_iff_bijective.mp (hπ v hv))
    else 1 with hσ_def
  have hσ (v : AbsoluteValue K ℝ) (hv : v ∈ T) (i : Fin m) : σ v i = π v i := by
    simp [hσ_def, hv]
  -- Step 2: glue the local families by simultaneous approximation, one vector at a time.
  have hglue (j : Fin m) := exists_sum_smul_sub_eq happrox hzx j.val j.isLt.le
    (fun v ↦ z v j - x j) fun v ↦ by
      have := (span_image_Iio_eq_span_image_Iio (hzx v) j).ge (hzx v j)
      rwa [Iio_eq_setOf_val_lt] at this
  choose ξ hξR he using hglue
  have hμ₀ (v : AbsoluteValue K ℝ) (hv : v ∈ T) (l : Fin m) : 0 ≤ μ v l :=
    (mul_nonneg_iff_of_pos_left (hν v hv l)).mp ((v.nonneg _).trans (hLx v hv l l))
  -- Step 3: at each place, `y j - z v j` is a small combination of the `z v l`, `l < j`.
  have key (v : AbsoluteValue K ℝ) (hv : v ∈ T) (i j : Fin m) :
      v (L v (σ v i) (x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l)) ≤
        c v ^ (2 * m + 1) * max 1 (A v) * (ν v (σ v i) * min (μ v i) (μ v j)) := by
    obtain ⟨e, he_le, heq⟩ := he j v hv
    obtain ⟨h₀, -, hbd⟩ := hz v hv
    have hy : x j + ∑ l ∈ univ.filter (· < j), ξ j l • x l =
        z v j + ∑ l ∈ univ.filter (· < j), e l • z v l := by
      rw [filter_congr fun l _ ↦ (Fin.lt_def (a := l) (b := j)), ← heq]
      abel
    rw [hy, hσ v hv]
    exact apply_add_sum_le (hc v) (hcv v) h₀ hbd (hν v hv) (hμ v hv) (hμ₀ v hv) he_le i j
  refine ⟨ξ, σ, hξR, fun v hv i j ↦ (key v hv i j).trans ?_, fun v hv hna hA i j ↦ ?_⟩
  · have h₀ : 0 ≤ max 1 (A v) * (ν v (σ v i) * min (μ v i) (μ v j)) := by
      have := le_min (hμ₀ v hv i) (hμ₀ v hv j)
      have := (hν v hv (σ v i)).le
      positivity
    rw [mul_assoc, mul_assoc]
    gcongr
    exact hc₂ v
  · simpa [hc_def, hna, max_eq_left hA] using key v hv i j

end AbsoluteValue
