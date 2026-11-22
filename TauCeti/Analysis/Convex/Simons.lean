/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Simons's inequality

Let `f n : X → ℝ` be a uniformly bounded sequence of real functions on a set `X`, and let
`B ⊆ X`. Suppose that every countable convex combination `∑' n, w n * f n` attains its
supremum over `X` at a point of `B`. **Simons's inequality** says that

`sup_{b ∈ B} limsup_n f n b ≥ inf_w sup_{x ∈ X} ∑' n, w n * f n x`,

where the infimum is over the convex weights `w`. We state it without suprema and limits
superior: if every convex combination takes a value at least `r` somewhere, then for each
`r' < r` some `b ∈ B` has `r' < f n b` for infinitely many `n`
(`TauCeti.exists_mem_frequently_lt_of_forall_exists_le`).

This is the combinatorial core of the modern proofs of James's theorem: applied to a
sequence in a Banach space, viewed as functions on a set of norming functionals, it gives
the sup-limsup theorem and the Rainwater–Simons theorem on weak convergence.

The proof chooses convex weights `w k`, supported on `[k, ∞)`, almost minimising the
supremum of `∑_{j < k} 2^{-(j+1)} f_{w j} + 2^{-k} f_{w k}`, where `f_w = ∑' n, w n * f n`.
A maximiser `b ∈ B` of `∑' j, 2^{-(j+1)} f_{w j}` then has tail averages
`τ k = ∑' j, 2^{-(j+1)} f_{w (j + k)} b` that decrease by at most `ε 2^{-k}` at each step, so they
stay above `r - 2ε`, which forces `f n b > r - 3ε` for infinitely many `n`.

## References

* S. Simons, *A convergence theorem with boundary*, Pacific J. Math. **40** (1972), 703–708.
* M. Fabian, P. Habala, P. Hájek, V. Montesinos and V. Zizler, *Banach Space Theory*,
  CMS Books in Mathematics, Springer (2011), Chapter 3.
-/

public section

open Filter Finset

namespace TauCeti

variable {X : Type*} {f : ℕ → X → ℝ} {M : ℝ}

/-- A sequence of convex weights supported on `[k, ∞)`. -/
private def IsTailWeight (k : ℕ) (w : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ w n) ∧ HasSum w 1 ∧ ∀ n < k, w n = 0

private theorem isTailWeight_indicator (k : ℕ) :
    IsTailWeight k fun n ↦ if n = k then 1 else 0 :=
  ⟨fun n ↦ by positivity, hasSum_ite_eq k 1, fun n hn ↦ by simp [hn.ne]⟩

private theorem summable_mul_of_abs_le (hf : ∀ n x, |f n x| ≤ M) {w : ℕ → ℝ}
    (hw0 : ∀ n, 0 ≤ w n) (hw : Summable w) (x : X) : Summable fun n ↦ w n * f n x :=
  Summable.of_norm_bounded (hw.mul_right M) fun n ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 n)]
    exact mul_le_mul_of_nonneg_left (hf n x) (hw0 n)

/-- A convex combination supported on `[k, ∞)` is at most any upper bound of its terms
from `k` on. -/
private theorem tsum_mul_le (hf : ∀ n x, |f n x| ≤ M) {k : ℕ} {w : ℕ → ℝ}
    (hw : IsTailWeight k w) {x : X} {c : ℝ} (hc : ∀ n, k ≤ n → f n x ≤ c) :
    ∑' n, w n * f n x ≤ c := by
  have hle : ∀ n, w n * f n x ≤ w n * c := fun n ↦ by
    rcases lt_or_ge n k with hn | hn
    · simp [hw.2.2 n hn]
    · exact mul_le_mul_of_nonneg_left (hc n hn) (hw.1 n)
  calc ∑' n, w n * f n x ≤ ∑' n, w n * c :=
        (summable_mul_of_abs_le hf hw.1 hw.2.1.summable x).tsum_le_tsum hle
          (hw.2.1.summable.mul_right c)
    _ = c := by rw [tsum_mul_right, hw.2.1.tsum_eq, one_mul]

private theorem abs_tsum_mul_le (hf : ∀ n x, |f n x| ≤ M) {k : ℕ} {w : ℕ → ℝ}
    (hw : IsTailWeight k w) (x : X) : |∑' n, w n * f n x| ≤ M := by
  have hf' : ∀ n x, |(-f) n x| ≤ M := fun n x ↦ by simpa using hf n x
  refine abs_le.2 ⟨?_, tsum_mul_le hf hw fun n _ ↦ (abs_le.1 (hf n x)).2⟩
  have := tsum_mul_le hf' hw (x := x) (c := M) fun n _ ↦ by
    simp only [Pi.neg_apply]; linarith [(abs_le.1 (hf n x)).1]
  simp only [Pi.neg_apply, mul_neg, tsum_neg] at this
  linarith

/-- A countable convex combination of convex weights is a convex weight. -/
private theorem hasSum_tsum_mul {c : ℕ → ℝ} {s : ℝ} (hc0 : ∀ j, 0 ≤ c j) (hc : HasSum c s)
    {w : ℕ → ℕ → ℝ} (hw0 : ∀ j n, 0 ≤ w j n) (hw : ∀ j, HasSum (w j) 1) :
    HasSum (fun n ↦ ∑' j, c j * w j n) s := by
  have hF : Summable (Function.uncurry fun j n ↦ c j * w j n) := by
    refine (summable_prod_of_nonneg fun p ↦ mul_nonneg (hc0 p.1) (hw0 p.1 p.2)).2
      ⟨fun j ↦ (hw j).summable.mul_left (c j), ?_⟩
    simpa only [tsum_mul_left, (hw _).tsum_eq, mul_one] using hc.summable
  have hsum : Summable fun n ↦ ∑' j, c j * w j n :=
    (summable_prod_of_nonneg fun p ↦ mul_nonneg (hc0 p.2) (hw0 p.2 p.1)).1
      ((Equiv.prodComm ℕ ℕ).summable_iff.2 hF) |>.2
  convert hsum.hasSum using 1
  rw [hF.tsum_comm]
  simp only [tsum_mul_left, (hw _).tsum_eq, mul_one, hc.tsum_eq]

/-- Evaluation of a countable convex combination of convex combinations. -/
private theorem tsum_tsum_mul_mul (hf : ∀ n x, |f n x| ≤ M) {c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j)
    (hc : Summable c) {w : ℕ → ℕ → ℝ} (hw0 : ∀ j n, 0 ≤ w j n) (hw : ∀ j, HasSum (w j) 1)
    (x : X) :
    ∑' n, (∑' j, c j * w j n) * f n x = ∑' j, c j * ∑' n, w j n * f n x := by
  have hF : Summable (Function.uncurry fun j n ↦ c j * w j n) := by
    refine (summable_prod_of_nonneg fun p ↦ mul_nonneg (hc0 p.1) (hw0 p.1 p.2)).2
      ⟨fun j ↦ (hw j).summable.mul_left (c j), ?_⟩
    simpa only [tsum_mul_left, (hw _).tsum_eq, mul_one] using hc
  have hG : Summable (Function.uncurry fun j n ↦ c j * w j n * f n x) := by
    refine Summable.of_norm_bounded (hF.mul_right M) fun p ↦ ?_
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc0 p.1),
      abs_of_nonneg (hw0 p.1 p.2)]
    exact mul_le_mul_of_nonneg_left (hf p.2 x) (mul_nonneg (hc0 p.1) (hw0 p.1 p.2))
  simp_rw [← tsum_mul_right, hG.tsum_comm, ← tsum_mul_left, mul_assoc]

/-- From the tail averages to frequent largeness: the real-number part of Simons's argument.

If `A = ∑_{j < k} 2^{-(j+1)} a j + 2^{-k} τ k` for all `k`, the near-optimality bound
`∑_{j < k} 2^{-(j+1)} a j + 2^{-k} a k ≤ A + ε 4^{-k}` holds, and `r ≤ A`, then every
`τ k` is at least `r - 2ε`. -/
private theorem le_of_sum_add_le {a τ : ℕ → ℝ} {A r ε : ℝ}
    (hA : ∀ k, A = ∑ j ∈ range k, (1 / 2) ^ (j + 1) * a j + (1 / 2) ^ k * τ k)
    (hopt : ∀ k, ∑ j ∈ range k, (1 / 2) ^ (j + 1) * a j + (1 / 2) ^ k * a k ≤
      A + ε * (1 / 4) ^ k)
    (hr : r ≤ A) (k : ℕ) : r - 2 * ε * (1 - (1 / 2) ^ k) ≤ τ k := by
  -- `a k ≤ τ k + ε 2^{-k}` and `τ (k + 1) = 2 τ k - a k`.
  have hak (k : ℕ) : a k ≤ τ k + ε * (1 / 2) ^ k := by
    have h := hopt k
    rw [hA k] at h
    have hpos : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have h4 : ε * (1 / 4 : ℝ) ^ k = (1 / 2) ^ k * (ε * (1 / 2) ^ k) := by
      rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num, mul_pow]; ring
    rw [h4] at h
    nlinarith
  have hτ (k : ℕ) : τ (k + 1) = 2 * τ k - a k := by
    have h := (hA k).symm.trans (hA (k + 1))
    rw [sum_range_succ, pow_succ] at h
    have hpos : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have h' : (1 / 2) ^ k * (2 * τ k - a k - τ (k + 1)) = 0 := by linarith
    linarith [(mul_eq_zero.1 h').resolve_left hpos.ne']
  induction k with
  | zero =>
    have h0 := hA 0
    simp only [range_zero, sum_empty, pow_zero, one_mul, zero_add] at h0
    simp only [pow_zero, sub_self, mul_zero, sub_zero]
    linarith
  | succ k ih =>
    rw [hτ k, pow_succ]
    nlinarith [hak k]

/-- Near-optimal tail weights for a bounded leading part `H`: some `w` supported on `[k, ∞)`
almost minimises the supremum of `H + 2^{-k} ∑' n, w n * f n` among such weights. -/
private theorem exists_isTailWeight_forall_le_iSup (hf : ∀ n x, |f n x| ≤ M) [Nonempty X]
    {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (H : X → ℝ) (hH : ∀ x, |H x| ≤ M) :
    ∃ w, IsTailWeight k w ∧ ∀ v, IsTailWeight k v → ∀ x,
      H x + (1 / 2) ^ k * ∑' n, w n * f n x ≤
        (⨆ y, H y + (1 / 2) ^ k * ∑' n, v n * f n y) + δ := by
  have hpos : (0 : ℝ) < (1 / 2) ^ k := by positivity
  have hbound (v : ℕ → ℝ) (hv : IsTailWeight k v) (y : X) :
      |H y + (1 / 2) ^ k * ∑' n, v n * f n y| ≤ M + (1 / 2) ^ k * M := by
    refine (abs_add_le _ _).trans (add_le_add (hH y) ?_)
    rw [abs_mul, abs_of_pos hpos]
    exact mul_le_mul_of_nonneg_left (abs_tsum_mul_le hf hv y) hpos.le
  have hbdd (v : ℕ → ℝ) (hv : IsTailWeight k v) :
      BddAbove (Set.range fun y ↦ H y + (1 / 2) ^ k * ∑' n, v n * f n y) :=
    ⟨_, by rintro _ ⟨y, rfl⟩; exact (abs_le.1 (hbound v hv y)).2⟩
  set val : (ℕ → ℝ) → ℝ := fun v ↦ ⨆ y, H y + (1 / 2) ^ k * ∑' n, v n * f n y
  set S := val '' {v | IsTailWeight k v}
  have hSne : S.Nonempty := ⟨_, Set.mem_image_of_mem _ (isTailWeight_indicator k)⟩
  have hSbdd : BddBelow S := ⟨-(M + (1 / 2) ^ k * M), by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y⟩ := ‹Nonempty X›
    exact (abs_le.1 (hbound v hv y)).1.trans (le_ciSup (hbdd v hv) y)⟩
  obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne (lt_add_of_pos_right (sInf S) hδ)
  refine ⟨w, hw, fun v hv x ↦ ?_⟩
  have h1 : H x + (1 / 2) ^ k * ∑' n, w n * f n x ≤ val w := le_ciSup (hbdd w hw) x
  have h2 : sInf S ≤ val v := csInf_le hSbdd (Set.mem_image_of_mem _ hv)
  linarith

/-- The recursive step of Simons's argument: a sequence of tail weights `w k`, each almost
minimising the supremum of `∑_{j < k} 2^{-(j+1)} f_{w j} + 2^{-k} f_{w k}` given its
predecessors, where `f_w = ∑' n, w n * f n`. -/
private theorem exists_seq_isTailWeight_forall_le_iSup (hf : ∀ n x, |f n x| ≤ M) [Nonempty X]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℕ → ℕ → ℝ, (∀ k, IsTailWeight k (w k)) ∧ ∀ k v, IsTailWeight k v → ∀ x,
      ∑ j ∈ range k, (1 / 2) ^ (j + 1) * ∑' n, w j n * f n x + (1 / 2) ^ k * ∑' n, w k n * f n x ≤
        (⨆ y, ∑ j ∈ range k, (1 / 2) ^ (j + 1) * ∑' n, w j n * f n y +
          (1 / 2) ^ k * ∑' n, v n * f n y) + ε * (1 / 4) ^ k := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty X›
  have hM : 0 ≤ M := (abs_nonneg _).trans (hf 0 x₀)
  choose! pick hpickW hpick using fun k ↦
    exists_isTailWeight_forall_le_iSup hf (by positivity : 0 < ε * (1 / 4) ^ k) k
  -- The leading parts, defined by recursion together with the chosen weights.
  let Hs : ℕ → X → ℝ := fun k ↦
    Nat.rec (fun _ ↦ 0) (fun k H x ↦ H x + (1 / 2) ^ (k + 1) * ∑' n, pick k H n * f n x) k
  have hHs_succ (k : ℕ) (x : X) :
      Hs (k + 1) x = Hs k x + (1 / 2) ^ (k + 1) * ∑' n, pick k (Hs k) n * f n x := rfl
  have hle_one (k : ℕ) : (1 - (1 / 2 : ℝ) ^ k) * M ≤ M :=
    mul_le_of_le_one_left hM (sub_le_self _ (by positivity))
  have hHs_abs (k : ℕ) (x : X) : |Hs k x| ≤ (1 - (1 / 2) ^ k) * M := by
    induction k generalizing x with
    | zero => simp [Hs]
    | succ k ih =>
      have h2 := abs_tsum_mul_le hf (hpickW k (Hs k) fun x ↦ (ih x).trans (hle_one k)) x
      rw [hHs_succ]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2) ^ (k + 1))]
      calc |Hs k x| + (1 / 2) ^ (k + 1) * |∑' n, pick k (Hs k) n * f n x|
          ≤ (1 - (1 / 2) ^ k) * M + (1 / 2) ^ (k + 1) * M := by gcongr; exact ih x
        _ = (1 - (1 / 2) ^ (k + 1)) * M := by ring
  have hHs_le (k : ℕ) (x : X) : |Hs k x| ≤ M := (hHs_abs k x).trans (hle_one k)
  have hHs_eq (k : ℕ) (x : X) :
      Hs k x = ∑ j ∈ range k, (1 / 2) ^ (j + 1) * ∑' n, pick j (Hs j) n * f n x := by
    induction k with
    | zero => simp [Hs]
    | succ k ih => rw [hHs_succ, ih, sum_range_succ]
  refine ⟨fun k ↦ pick k (Hs k), fun k ↦ hpickW k (Hs k) (hHs_le k), fun k v hv x ↦ ?_⟩
  simp_rw [← hHs_eq]
  exact hpick k (Hs k) (hHs_le k) v hv x

/-- The `k`-th tail `∑' j, 2^{-(j+1)} w (j + k)` of a sequence of tail weights is a tail weight
supported on `[k, ∞)`. -/
private theorem isTailWeight_tsum_half {w : ℕ → ℕ → ℝ} (hw : ∀ k, IsTailWeight k (w k))
    (k : ℕ) : IsTailWeight k fun n ↦ ∑' j, (1 / 2 : ℝ) ^ (j + 1) * w (j + k) n := by
  have hhalf : HasSum (fun j : ℕ ↦ (1 / 2 : ℝ) ^ (j + 1)) 1 := by
    convert (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 2) using 1
    · ext j; ring
    · norm_num
  refine ⟨fun n ↦ tsum_nonneg fun j ↦ mul_nonneg (by positivity) ((hw (j + k)).1 n),
    hasSum_tsum_mul (fun j ↦ by positivity) hhalf (fun j n ↦ (hw (j + k)).1 n)
      fun j ↦ (hw (j + k)).2.1, fun n hn ↦ ?_⟩
  dsimp only
  rw [tsum_congr fun j ↦ by rw [(hw (j + k)).2.2 n (by omega), mul_zero], tsum_zero]

/-- Splitting the combined weight `∑' j, 2^{-(j+1)} w j` into its first `k` terms and its
`k`-th tail. -/
private theorem tsum_tsum_half_mul_eq (hf : ∀ n x, |f n x| ≤ M) {w : ℕ → ℕ → ℝ}
    (hw : ∀ k, IsTailWeight k (w k)) (k : ℕ) (x : X) :
    ∑' n, (∑' j, (1 / 2) ^ (j + 1) * w (j + 0) n) * f n x =
      ∑ j ∈ range k, (1 / 2) ^ (j + 1) * ∑' n, w j n * f n x +
        (1 / 2) ^ k * ∑' n, (∑' j, (1 / 2) ^ (j + 1) * w (j + k) n) * f n x := by
  have hhalf : Summable fun j : ℕ ↦ (1 / 2 : ℝ) ^ (j + 1) := by
    simpa only [pow_succ] using (summable_geometric_two).mul_right (1 / 2)
  have hhalf0 (j : ℕ) : (0 : ℝ) ≤ (1 / 2) ^ (j + 1) := by positivity
  have heval (m : ℕ) := tsum_tsum_mul_mul hf hhalf0 hhalf (w := fun j ↦ w (j + m))
    (fun j n ↦ (hw (j + m)).1 n) (fun j ↦ (hw (j + m)).2.1) x
  have hs : Summable fun j ↦ (1 / 2 : ℝ) ^ (j + 1) * ∑' n, w j n * f n x :=
    Summable.of_norm_bounded (hhalf.mul_right M) fun j ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hhalf0 j)]
      exact mul_le_mul_of_nonneg_left (abs_tsum_mul_le hf (hw j) x) (hhalf0 j)
  have h0 := heval 0
  simp only [add_zero] at h0 ⊢
  rw [h0, heval k, ← hs.sum_add_tsum_nat_add k, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun j ↦ ?_
  rw [pow_add, pow_add, pow_add]
  ring

/-- **Simons's inequality.** Let `f n : X → ℝ` be uniformly bounded and `B ⊆ X`. Suppose every
countable convex combination `∑' n, w n * f n` attains its supremum over `X` at a point of `B`,
and takes a value at least `r` somewhere. Then for every `r' < r` there is `b ∈ B` with
`r' < f n b` for infinitely many `n`.

In terms of suprema: `sup_{b ∈ B} limsup_n f n b ≥ inf_w sup_X ∑' n, w n * f n`. -/
theorem exists_mem_frequently_lt_of_forall_exists_le {B : Set X} {r r' : ℝ}
    (hf : ∀ n x, |f n x| ≤ M)
    (hB : ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 →
      ∃ b ∈ B, ∀ x, ∑' n, w n * f n x ≤ ∑' n, w n * f n b)
    (hr : ∀ w : ℕ → ℝ, (∀ n, 0 ≤ w n) → HasSum w 1 → ∃ x, r ≤ ∑' n, w n * f n x)
    (hr' : r' < r) :
    ∃ b ∈ B, ∃ᶠ n in atTop, r' < f n b := by
  obtain ⟨x₀, -⟩ := hr _ (isTailWeight_indicator 0).1 (isTailWeight_indicator 0).2.1
  have : Nonempty X := ⟨x₀⟩
  have hε : 0 < (r - r') / 3 := by linarith
  obtain ⟨w, hw, hopt⟩ := exists_seq_isTailWeight_forall_le_iSup hf hε
  -- The tails `t k` of the combined weight `t 0`, and a maximiser `b ∈ B` of `f_{t 0}`.
  set t : ℕ → ℕ → ℝ := fun k n ↦ ∑' j, (1 / 2) ^ (j + 1) * w (j + k) n
  have ht := isTailWeight_tsum_half hw
  have hsplit (k : ℕ) (y : X) : ∑ j ∈ range k, (1 / 2) ^ (j + 1) * ∑' n, w j n * f n y +
      (1 / 2) ^ k * ∑' n, t k n * f n y = ∑' n, t 0 n * f n y :=
    (tsum_tsum_half_mul_eq hf hw k y).symm
  obtain ⟨b, hbB, hb⟩ := hB (t 0) (ht 0).1 (ht 0).2.1
  refine ⟨b, hbB, frequently_atTop.2 fun K ↦ ?_⟩
  have hsup (k : ℕ) : (⨆ y, ∑ j ∈ range k, (1 / 2) ^ (j + 1) * ∑' n, w j n * f n y +
      (1 / 2) ^ k * ∑' n, t k n * f n y) = ∑' n, t 0 n * f n b := by
    simp_rw [hsplit k]
    exact le_antisymm (ciSup_le hb) (le_ciSup ⟨_, by rintro _ ⟨y, rfl⟩; exact hb y⟩ b)
  -- The tail averages `∑' n, t k n * f n b` stay above `r - 2ε`.
  obtain ⟨x₁, hx₁⟩ := hr (t 0) (ht 0).1 (ht 0).2.1
  have hτ := le_of_sum_add_le (a := fun j ↦ ∑' n, w j n * f n b)
    (τ := fun k ↦ ∑' n, t k n * f n b) (fun k ↦ (hsplit k b).symm)
    (fun k ↦ hsup k ▸ hopt k (t k) (ht k) b) (hx₁.trans (hb x₁)) K
  -- If `f n b ≤ r'` from `K` on, the tail average at `K` is at most `r'`.
  by_contra! hK
  have hle := tsum_mul_le hf (ht K) (x := b) (c := r') fun n hn ↦ hK n hn
  have hpow : (0 : ℝ) ≤ (1 / 2) ^ K := by positivity
  nlinarith

end TauCeti
