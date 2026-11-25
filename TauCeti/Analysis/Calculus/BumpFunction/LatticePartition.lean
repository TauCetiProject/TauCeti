/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import TauCeti.Analysis.InnerProductSpace.Euclidean.IntegerPoints
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.PSeries.Shifted
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.Topology.Algebra.InfiniteSum.PiProd

/-!
# A smooth partition of unity by integer translates

This file constructs a smooth function `χ = TauCeti.latticeBump n` on `ℝⁿ` whose integer
translates form a partition of unity: `∑_{j ∈ ℤⁿ} χ(x - j) = 1` for every `x`
(`TauCeti.hasSum_latticeBump_sub`), with `0 ≤ χ ≤ 1` and `χ(x) = 0` unless every coordinate of
`x` lies in `(-1, 1)`. All translates are the same function moved around, so every derivative
bound for `χ` holds uniformly for the whole family. This is what makes such a partition useful
for decomposing operators into pieces localized at unit scale, as in the proof of the
Calderón–Vaillancourt theorem, where the estimates for each piece must be independent of where
it sits.

The construction is a product of one-dimensional bumps
`TauCeti.latticeBump₁ t = ψ(t + 1) - ψ(t)` for the smooth transition function `ψ` from `0` to
`1` on `[0, 1]` (`Real.smoothTransition`); their integer translates telescope to `1`.

## Main declarations

* `TauCeti.latticeBump n`: the smooth function `χ(x) = ∏ᵢ latticeBump₁ (xᵢ)`.
* `TauCeti.hasSum_latticeBump_sub`: `∑_{j ∈ ℤⁿ} χ(x - j) = 1`.
* `TauCeti.abs_lt_one_of_latticeBump_ne_zero`: `χ(x) ≠ 0` implies `|xᵢ| < 1` for every `i`.
* `TauCeti.tsupport_latticeBump_subset`: `χ` is supported in the closed ball of radius `√n`.
* `TauCeti.abs_sub_le_one_of_latticeBump_mul_ne_zero`: two integer translates of `χ` overlap only
  if their centres differ by at most one in every coordinate.
* `TauCeti.latticeWeight`: the summable weight `∏ᵢ (1 + |dᵢ|)⁻²` on `ℤⁿ`, which dominates the
  lattice sums of `(1 + ‖x - j‖²)⁻ⁿ` uniformly in `x`
  (`TauCeti.tsum_one_add_norm_sub_latticePoint_sq_pow_inv_le`). Moving `x` by at most one
  changes these weights by at most the factor `4ⁿ`
  (`TauCeti.one_add_norm_sub_latticePoint_sq_pow_inv_le_of_dist_le_one`).
* `TauCeti.contDiff_latticeBump_sub`, `TauCeti.hasTemperateGrowth_latticeBump_sub`: the
  translates `χ(· - j)` are smooth and of temperate growth, and
  `TauCeti.exists_norm_iteratedFDeriv_latticeBump_sub_le` bounds their derivatives independently
  of `j`.
* `TauCeti.norm_iteratedFDeriv_sum_latticeBump_sub_le`: the finite sums of translates of `χ` have
  derivatives bounded independently of the set of translates; so do these sums minus `1`
  (`TauCeti.norm_iteratedFDeriv_sum_latticeBump_sub_sub_one_le`).
-/

public section

open Finset Real

namespace TauCeti

/-! ### The one-dimensional bump -/

/-- The one-dimensional bump `ψ(t + 1) - ψ(t)` built from the smooth transition function `ψ`.
Its integer translates sum to one (`TauCeti.hasSum_latticeBump₁_sub`). -/
noncomputable def latticeBump₁ (t : ℝ) : ℝ :=
  smoothTransition (t + 1) - smoothTransition t

theorem latticeBump₁_def (t : ℝ) : latticeBump₁ t = smoothTransition (t + 1) - smoothTransition t :=
  (rfl)

theorem contDiff_latticeBump₁ {k : ℕ∞} : ContDiff ℝ k latticeBump₁ :=
  (smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).sub smoothTransition.contDiff

theorem latticeBump₁_nonneg (t : ℝ) : 0 ≤ latticeBump₁ t :=
  sub_nonneg.2 (smoothTransition.monotone (by linarith))

theorem latticeBump₁_le_one (t : ℝ) : latticeBump₁ t ≤ 1 := by
  have h₁ := smoothTransition.le_one (t + 1)
  have h₀ := smoothTransition.nonneg t
  rw [latticeBump₁_def]
  linarith

theorem latticeBump₁_eq_zero_of_one_le_abs {t : ℝ} (ht : 1 ≤ |t|) : latticeBump₁ t = 0 := by
  rcases le_abs'.1 ht with ht | ht
  · rw [latticeBump₁_def, smoothTransition.zero_of_nonpos (by linarith),
      smoothTransition.zero_of_nonpos (by linarith), sub_zero]
  · rw [latticeBump₁_def, smoothTransition.one_of_one_le (by linarith),
      smoothTransition.one_of_one_le ht, sub_self]

theorem abs_lt_one_of_latticeBump₁_ne_zero {t : ℝ} (ht : latticeBump₁ t ≠ 0) : |t| < 1 :=
  lt_of_not_ge fun h ↦ ht (latticeBump₁_eq_zero_of_one_le_abs h)

/-- At each `t`, the integer translates `latticeBump₁ (t - k)` vanish except for `k = ⌊t⌋` and
`k = ⌊t⌋ + 1`, and those two sum to one. -/
private theorem latticeBump₁_sub_eq_zero (t : ℝ) {k : ℤ}
    (hk : k ∉ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ)) : latticeBump₁ (t - k) = 0 := by
  simp only [mem_insert, mem_singleton, not_or] at hk
  refine latticeBump₁_eq_zero_of_one_le_abs ?_
  rcases lt_or_gt_of_ne hk.1 with h | h
  · have : (k : ℝ) + 1 ≤ ⌊t⌋ := by exact_mod_cast h
    have := Int.floor_le t
    rw [le_abs]
    left
    linarith
  · have : (⌊t⌋ : ℝ) + 2 ≤ k := by
      have : ⌊t⌋ + 2 ≤ k := by omega
      exact_mod_cast this
    have := Int.lt_floor_add_one t
    rw [le_abs]
    right
    linarith

private theorem sum_latticeBump₁_sub (t : ℝ) :
    ∑ k ∈ ({⌊t⌋, ⌊t⌋ + 1} : Finset ℤ), latticeBump₁ (t - k) = 1 := by
  rw [sum_pair (by omega)]
  have h₁ := Int.floor_le t
  have h₂ := Int.lt_floor_add_one t
  have e : t - ((⌊t⌋ + 1 : ℤ) : ℝ) + 1 = t - ⌊t⌋ := by push_cast; ring
  rw [latticeBump₁_def, latticeBump₁_def, e, smoothTransition.one_of_one_le (by linarith),
    smoothTransition.zero_of_nonpos (x := t - ((⌊t⌋ + 1 : ℤ) : ℝ)) (by push_cast; linarith)]
  ring

/-- The integer translates of the one-dimensional bump sum to one. -/
theorem hasSum_latticeBump₁_sub (t : ℝ) : HasSum (fun k : ℤ ↦ latticeBump₁ (t - k)) 1 := by
  rw [← sum_latticeBump₁_sub t]
  exact hasSum_sum_of_ne_finset_zero fun k hk ↦ latticeBump₁_sub_eq_zero t hk

/-! ### The bump on `ℝⁿ` -/

variable (n : ℕ)

/-- The smooth function `χ(x) = ∏ᵢ latticeBump₁ (xᵢ)` on `ℝⁿ`, whose integer translates form a
partition of unity (`TauCeti.hasSum_latticeBump_sub`). -/
noncomputable def latticeBump (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∏ i, latticeBump₁ (x i)

variable {n}

theorem latticeBump_def (x : EuclideanSpace ℝ (Fin n)) :
    latticeBump n x = ∏ i, latticeBump₁ (x i) :=
  (rfl)

theorem contDiff_latticeBump {k : ℕ∞} : ContDiff ℝ k (latticeBump n) :=
  contDiff_prod fun i _ ↦ contDiff_latticeBump₁.comp
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

theorem latticeBump_nonneg (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ latticeBump n x :=
  prod_nonneg fun _ _ ↦ latticeBump₁_nonneg _

theorem latticeBump_le_one (x : EuclideanSpace ℝ (Fin n)) : latticeBump n x ≤ 1 :=
  prod_le_one₀ (fun _ _ ↦ latticeBump₁_nonneg _) fun _ _ ↦ latticeBump₁_le_one _

/-- The bump vanishes unless every coordinate lies in `(-1, 1)`. -/
theorem abs_lt_one_of_latticeBump_ne_zero {x : EuclideanSpace ℝ (Fin n)}
    (hx : latticeBump n x ≠ 0) (i : Fin n) : |x i| < 1 :=
  abs_lt_one_of_latticeBump₁_ne_zero (prod_ne_zero_iff.1 hx i (mem_univ i))

private theorem norm_lt_of_latticeBump_ne_zero {x : EuclideanSpace ℝ (Fin n)}
    (hx : latticeBump n x ≠ 0) : ‖x‖ < √n ∨ n = 0 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exact .inr hn
  left
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_lt_sqrt (sum_nonneg fun _ _ ↦ sq_nonneg _) ?_
  calc ∑ i, ‖x i‖ ^ 2 < ∑ _i : Fin n, (1 : ℝ) := by
        refine sum_lt_sum_of_nonempty ⟨⟨0, hn⟩, mem_univ _⟩ fun i _ ↦ ?_
        rw [Real.norm_eq_abs, sq_lt_one_iff_abs_lt_one, abs_abs]
        exact abs_lt_one_of_latticeBump_ne_zero hx i
    _ = n := by simp

/-- The bump is supported in the closed ball of radius `√n` about the origin. -/
theorem tsupport_latticeBump_subset :
    tsupport (latticeBump n) ⊆ Metric.closedBall 0 √n := by
  refine closure_minimal (fun x hx ↦ ?_) Metric.isClosed_closedBall
  rw [mem_closedBall_zero_iff]
  rcases norm_lt_of_latticeBump_ne_zero hx with h | rfl
  · exact h.le
  · simp [Subsingleton.elim x 0]

theorem hasCompactSupport_latticeBump : HasCompactSupport (latticeBump n) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 √n)
    (subset_tsupport _ |>.trans tsupport_latticeBump_subset)

/-- The integer translates of the bump are smooth. -/
theorem contDiff_latticeBump_sub {k : ℕ∞} (j : Fin n → ℤ) :
    ContDiff ℝ k fun y ↦ latticeBump n (y - latticePoint j) :=
  contDiff_latticeBump.comp (contDiff_id.sub contDiff_const)

/-- The integer translates of the bump have temperate growth. -/
theorem hasTemperateGrowth_latticeBump_sub (j : Fin n → ℤ) :
    (fun y ↦ latticeBump n (y - latticePoint j)).HasTemperateGrowth :=
  (hasCompactSupport_latticeBump.comp_homeomorph
    (Homeomorph.subRight (latticePoint j))).hasTemperateGrowth (contDiff_latticeBump_sub j)

/-- A translate `χ(x - c)` of the bump is nonzero only on the closed ball of radius `√n` about
`c`. -/
theorem mem_closedBall_of_latticeBump_sub_ne_zero {x c : EuclideanSpace ℝ (Fin n)}
    (h : latticeBump n (x - c) ≠ 0) : x ∈ Metric.closedBall c √n := by
  have := tsupport_latticeBump_subset (subset_tsupport _ h)
  rwa [mem_closedBall_zero_iff, ← dist_eq_norm] at this

/-- The product of two values of the bump has norm at most one. -/
theorem norm_latticeBump_mul_le (x y : EuclideanSpace ℝ (Fin n)) :
    ‖latticeBump n x * latticeBump n y‖ ≤ 1 := by
  rw [norm_mul, Real.norm_of_nonneg (latticeBump_nonneg x),
    Real.norm_of_nonneg (latticeBump_nonneg y)]
  calc latticeBump n x * latticeBump n y ≤ 1 * 1 :=
        mul_le_mul (latticeBump_le_one x) (latticeBump_le_one y) (latticeBump_nonneg y)
          zero_le_one
    _ = 1 := one_mul 1

/-- Two integer translates of the bump overlap only if their centres differ by at most one in
every coordinate. -/
theorem abs_sub_le_one_of_latticeBump_mul_ne_zero {x : EuclideanSpace ℝ (Fin n)}
    {j j' : Fin n → ℤ}
    (h : latticeBump n (x - latticePoint j) * latticeBump n (x - latticePoint j') ≠ 0)
    (i : Fin n) : |j i - j' i| ≤ 1 := by
  have h₁ := abs_lt_one_of_latticeBump_ne_zero (left_ne_zero_of_mul h) i
  have h₂ := abs_lt_one_of_latticeBump_ne_zero (right_ne_zero_of_mul h) i
  simp only [PiLp.sub_apply, latticePoint_apply] at h₁ h₂
  have : |(j i : ℝ) - j' i| < 2 := by
    rw [abs_lt] at h₁ h₂ ⊢
    constructor <;> linarith
  have : |j i - j' i| < 2 := by exact_mod_cast this
  omega

/-- Two integer translates of the bump whose centres differ by more than one in some coordinate
have product zero. -/
theorem latticeBump_mul_eq_zero_of_one_lt_abs {j j' : Fin n → ℤ} {i : Fin n}
    (h : 1 < |j i - j' i|) (x : EuclideanSpace ℝ (Fin n)) :
    latticeBump n (x - latticePoint j) * latticeBump n (x - latticePoint j') = 0 :=
  by_contra fun h' ↦ (abs_sub_le_one_of_latticeBump_mul_ne_zero h' i).not_gt h

/-- **The integer translates of `latticeBump n` form a partition of unity:**
`∑_{j ∈ ℤⁿ} χ(x - j) = 1`. -/
theorem hasSum_latticeBump_sub (x : EuclideanSpace ℝ (Fin n)) :
    HasSum (fun j : Fin n → ℤ ↦ latticeBump n (x - latticePoint j)) 1 := by
  classical
  let t : Fin n → Finset ℤ := fun i ↦ {⌊x i⌋, ⌊x i⌋ + 1}
  have hsum : ∑ j ∈ Fintype.piFinset t, latticeBump n (x - latticePoint j) = 1 := by
    simp only [latticeBump_def, PiLp.sub_apply, latticePoint_apply]
    rw [← prod_univ_sum t fun i k ↦ latticeBump₁ (x i - k)]
    exact prod_eq_one fun i _ ↦ sum_latticeBump₁_sub (x i)
  rw [← hsum]
  refine hasSum_sum_of_ne_finset_zero fun j hj ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, j i ∉ t i := by simpa [Fintype.mem_piFinset] using hj
  exact prod_eq_zero (mem_univ i) (by simpa using latticeBump₁_sub_eq_zero (x i) hi)

/-- If a set `s` contains every lattice point of norm less than `R`, then the translate of
`latticeBump n` centred at a lattice point outside `s` vanishes on the ball of radius `R - √n`. -/
theorem latticeBump_sub_eq_zero_of_notMem {s : Set (Fin n → ℤ)} {R : ℝ}
    (hs : ∀ j, ‖latticePoint j‖ < R → j ∈ s) {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ + √n < R)
    {j : Fin n → ℤ} (hj : j ∉ s) : latticeBump n (y - latticePoint j) = 0 := by
  by_contra hne
  have hy' := mem_closedBall_of_latticeBump_sub_ne_zero hne
  rw [Metric.mem_closedBall, dist_eq_norm] at hy'
  refine hj (hs j ?_)
  calc ‖latticePoint j‖ = ‖y - (y - latticePoint j)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖y‖ + ‖y - latticePoint j‖ := norm_sub_le _ _
    _ < R := by linarith

/-- A finite sum of integer translates of `latticeBump n` that contains every lattice point of
norm less than `R` sums to `1` on the ball of radius `R - √n`. -/
theorem sum_latticeBump_sub_eq_one {s : Finset (Fin n → ℤ)} {R : ℝ}
    (hs : ∀ j, ‖latticePoint j‖ < R → j ∈ s) {y : EuclideanSpace ℝ (Fin n)} (hy : ‖y‖ + √n < R) :
    ∑ j ∈ s, latticeBump n (y - latticePoint j) = 1 :=
  ((hasSum_latticeBump_sub y).unique (hasSum_sum_of_ne_finset_zero fun _ hj ↦
    latticeBump_sub_eq_zero_of_notMem (s := (s : Set (Fin n → ℤ))) hs hy hj)).symm

/-! ### A summable weight on the lattice -/

/-- The weight `∏ᵢ (1 + |dᵢ|)⁻²` on `ℤⁿ`, which is summable (`TauCeti.summable_latticeWeight`).
It dominates the sums over the lattice of functions decaying like `(1 + ‖x - j‖)⁻²ⁿ`. -/
noncomputable def latticeWeight (d : Fin n → ℤ) : ℝ :=
  ∏ i, ((1 + |(d i : ℝ)|) ^ 2)⁻¹

theorem latticeWeight_def (d : Fin n → ℤ) : latticeWeight d = ∏ i, ((1 + |(d i : ℝ)|) ^ 2)⁻¹ :=
  (rfl)

theorem latticeWeight_nonneg (d : Fin n → ℤ) : 0 ≤ latticeWeight d :=
  prod_nonneg fun _ _ ↦ by positivity

theorem summable_latticeWeight : Summable (latticeWeight (n := n)) := by
  refine Summable.prod_pi_of_nonneg (ι := Fin n) (f := fun _ (m : ℤ) ↦ ((1 + |(m : ℝ)|) ^ 2)⁻¹)
    (fun _ ↦ ?_) fun _ m ↦ by positivity
  refine (summable_one_add_abs_int_rpow (r := -2) (by norm_num)).congr fun m ↦ ?_
  rw [Real.rpow_neg (by positivity)]
  norm_cast

/-- Decay like `(1 + ‖x - j‖²)⁻ⁿ` around a point `x` of `ℝⁿ` is dominated by the lattice weight of
the displacement of `j` from the integer part `⌊x⌋` of `x`. -/
theorem one_add_norm_sub_latticePoint_sq_pow_inv_le (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n → ℤ) :
    ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹ ≤ 8 ^ n * latticeWeight (fun i ↦ ⌊x i⌋ - j i) := by
  set y := x - latticePoint j
  have hy : 0 < (1 + ‖y‖ ^ 2) ^ n := by positivity
  have hfac (i : Fin n) : (1 + |((⌊x i⌋ - j i : ℤ) : ℝ)|) ^ 2 ≤ 8 * (1 + ‖y‖ ^ 2) := by
    have hyi : |x i - j i| ≤ ‖y‖ := by
      simpa [y, latticePoint_apply] using PiLp.norm_apply_le y i
    have hd : |((⌊x i⌋ - j i : ℤ) : ℝ)| ≤ ‖y‖ + 1 := by
      have h₁ := Int.floor_le (x i)
      have h₂ := Int.lt_floor_add_one (x i)
      rw [abs_le] at hyi ⊢
      push_cast
      constructor <;> linarith
    calc (1 + |((⌊x i⌋ - j i : ℤ) : ℝ)|) ^ 2 ≤ (2 + ‖y‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ ≤ 8 * (1 + ‖y‖ ^ 2) := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hprod : ∏ i, (1 + |((⌊x i⌋ - j i : ℤ) : ℝ)|) ^ 2 ≤ 8 ^ n * (1 + ‖y‖ ^ 2) ^ n := by
    calc ∏ i, (1 + |((⌊x i⌋ - j i : ℤ) : ℝ)|) ^ 2 ≤ ∏ _i : Fin n, 8 * (1 + ‖y‖ ^ 2) :=
          prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ hfac i
      _ = 8 ^ n * (1 + ‖y‖ ^ 2) ^ n := by rw [prod_const, card_univ, Fintype.card_fin, mul_pow]
  have hP : 0 < ∏ i, (1 + |((⌊x i⌋ - j i : ℤ) : ℝ)|) ^ 2 := prod_pos fun _ _ ↦ by positivity
  rw [latticeWeight_def, prod_inv_distrib, ← div_eq_mul_inv, inv_eq_one_div,
    div_le_div_iff₀ hy hP, one_mul]
  exact hprod

/-- Within distance one of `x`, the weight `(1 + ‖y - j‖²)⁻ⁿ` is at most `4ⁿ` times its value
at `x`. -/
theorem one_add_norm_sub_latticePoint_sq_pow_inv_le_of_dist_le_one
    {x y : EuclideanSpace ℝ (Fin n)} (hy : dist y x ≤ 1) (j : Fin n → ℤ) :
    ((1 + ‖y - latticePoint j‖ ^ 2) ^ n)⁻¹ ≤ 4 ^ n * ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹ := by
  have e (v : EuclideanSpace ℝ (Fin n)) :
      (1 + ‖v‖ ^ 2) ^ (-(2 * n : ℝ) / 2) = ((1 + ‖v‖ ^ 2) ^ n)⁻¹ := by
    rw [neg_div, mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_neg (by positivity),
      Real.rpow_natCast]
  have h4 : (2 : ℝ) ^ |-(2 * n : ℝ)| = 4 ^ n := by
    rw [abs_neg, abs_of_nonneg (by positivity), show (2 * n : ℝ) = ((2 * n : ℕ) : ℝ) by
      push_cast; ring, Real.rpow_natCast, pow_mul]
    norm_num
  have hyx : ‖y - latticePoint j - (x - latticePoint j)‖ ≤ 1 := by
    rwa [sub_sub_sub_cancel_right, ← dist_eq_norm]
  have h := one_add_norm_sq_rpow_le_of_norm_sub_le_one hyx (-(2 * n : ℝ))
  rwa [e, e, h4] at h

/-- The lattice sums of `(1 + ‖x - j‖²)⁻ⁿ` converge. -/
theorem summable_one_add_norm_sub_latticePoint_sq_pow_inv (x : EuclideanSpace ℝ (Fin n)) :
    Summable fun j : Fin n → ℤ ↦ ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹ :=
  Summable.of_nonneg_of_le (fun _ ↦ by positivity)
    (one_add_norm_sub_latticePoint_sq_pow_inv_le x)
    (((Equiv.subLeft fun i ↦ ⌊x i⌋).summable_iff.2 summable_latticeWeight).mul_left _)

/-- On the unit ball about `x`, the weights `(1 + ‖y - j‖²)⁻ⁿ` are bounded by a summable family
of the lattice points `j`. -/
theorem exists_summable_forall_one_add_norm_sub_latticePoint_sq_pow_inv_le
    (x : EuclideanSpace ℝ (Fin n)) : ∃ v : (Fin n → ℤ) → ℝ, Summable v ∧
      ∀ j, ∀ y ∈ Metric.ball x 1, ((1 + ‖y - latticePoint j‖ ^ 2) ^ n)⁻¹ ≤ v j :=
  ⟨fun j ↦ 4 ^ n * ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹,
    (summable_one_add_norm_sub_latticePoint_sq_pow_inv x).mul_left _,
    fun j _ hy ↦ one_add_norm_sub_latticePoint_sq_pow_inv_le_of_dist_le_one
      (Metric.mem_ball.1 hy).le j⟩

/-- The lattice sums of `(1 + ‖x - j‖²)⁻ⁿ` are bounded independently of `x`. -/
theorem tsum_one_add_norm_sub_latticePoint_sq_pow_inv_le (x : EuclideanSpace ℝ (Fin n)) :
    ∑' j : Fin n → ℤ, ((1 + ‖x - latticePoint j‖ ^ 2) ^ n)⁻¹ ≤
      8 ^ n * ∑' d : Fin n → ℤ, latticeWeight d := by
  have hs := (Equiv.subLeft fun i ↦ ⌊x i⌋).summable_iff.2 (summable_latticeWeight (n := n))
  refine ((summable_one_add_norm_sub_latticePoint_sq_pow_inv x).tsum_le_tsum
    (one_add_norm_sub_latticePoint_sq_pow_inv_le x) (hs.mul_left _)).trans_eq ?_
  rw [tsum_mul_left]
  congr 1
  exact (Equiv.subLeft fun i ↦ ⌊x i⌋).tsum_eq latticeWeight

/-! ### Derivatives of the translates -/

/-- The derivatives of `latticeBump n` are bounded. -/
theorem exists_norm_iteratedFDeriv_latticeBump_le (k : ℕ) :
    ∃ B, ∀ y, ‖iteratedFDeriv ℝ k (latticeBump n) y‖ ≤ B :=
  let ⟨B, _, hB⟩ := hasCompactSupport_latticeBump.exists_bound_iteratedFDeriv
    (contDiff_latticeBump (n := n)) k
  ⟨B, hB k le_rfl⟩

/-- The integer translates of `latticeBump n` have derivatives bounded independently of the
translation. -/
theorem exists_norm_iteratedFDeriv_latticeBump_sub_le (k : ℕ) :
    ∃ B, ∀ (j : Fin n → ℤ) (y : EuclideanSpace ℝ (Fin n)),
      ‖iteratedFDeriv ℝ k (fun y ↦ latticeBump n (y - latticePoint j)) y‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_norm_iteratedFDeriv_latticeBump_le (n := n) k
  exact ⟨B, fun j y ↦ by rw [iteratedFDeriv_comp_sub]; exact hB _⟩

/-- A derivative of the translate of `latticeBump n` to the lattice point `j` is bounded by the
weight `(1 + ‖y - j‖²)⁻ⁿ`, with a constant independent of `j`. -/
theorem norm_iteratedFDeriv_latticeBump_sub_le {k : ℕ} {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ k (latticeBump n) y‖ ≤ B) (j : Fin n → ℤ)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ k (fun y ↦ latticeBump n (y - latticePoint j)) y‖ ≤
      B * (1 + (n : ℝ)) ^ n * ((1 + ‖y - latticePoint j‖ ^ 2) ^ n)⁻¹ := by
  rw [iteratedFDeriv_comp_sub]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  by_cases hy : y - latticePoint j ∈ tsupport (latticeBump n)
  · have hn : ‖y - latticePoint j‖ ^ 2 ≤ n := by
      have h := mem_closedBall_zero_iff.1 (tsupport_latticeBump_subset hy)
      calc ‖y - latticePoint j‖ ^ 2 ≤ √n ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = n := Real.sq_sqrt (Nat.cast_nonneg n)
    have hpos : 0 < (1 + ‖y - latticePoint j‖ ^ 2) ^ n := by positivity
    have h1 : 1 ≤ (1 + (n : ℝ)) ^ n * ((1 + ‖y - latticePoint j‖ ^ 2) ^ n)⁻¹ := by
      rw [← div_eq_mul_inv, one_le_div hpos]
      exact pow_le_pow_left₀ (by positivity) (by linarith) n
    calc ‖iteratedFDeriv ℝ k (latticeBump n) (y - latticePoint j)‖ ≤ B * 1 :=
          (hB _).trans (mul_one B).ge
      _ ≤ B * ((1 + (n : ℝ)) ^ n * ((1 + ‖y - latticePoint j‖ ^ 2) ^ n)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 hB0
      _ = _ := by ring
  · rw [Function.notMem_support.1 fun h ↦ hy (support_iteratedFDeriv_subset k h), norm_zero]
    positivity

/-- The finite sums of translates of `latticeBump n` have derivatives bounded independently of the
finite set of lattice points. -/
theorem norm_iteratedFDeriv_sum_latticeBump_sub_le {k : ℕ} {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ k (latticeBump n) y‖ ≤ B) (s : Finset (Fin n → ℤ))
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ k (fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j)) y‖ ≤
      B * (1 + (n : ℝ)) ^ n * (8 ^ n * ∑' d : Fin n → ℤ, latticeWeight d) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [iteratedFDeriv_sum (f := fun j y ↦ latticeBump n (y - latticePoint j)) fun j _ ↦
    contDiff_latticeBump_sub (k := (k : ℕ∞)) j, Finset.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ ↦ norm_iteratedFDeriv_latticeBump_sub_le hB j y).trans ?_
  rw [← Finset.mul_sum]
  gcongr
  exact ((summable_one_add_norm_sub_latticePoint_sq_pow_inv y).sum_le_tsum s
    fun _ _ ↦ by positivity).trans (tsum_one_add_norm_sub_latticePoint_sq_pow_inv_le y)

/-- The finite sums of translates of `latticeBump n`, minus `1`, have derivatives bounded
independently of the finite set of lattice points. -/
theorem norm_iteratedFDeriv_sum_latticeBump_sub_sub_one_le {k : ℕ} {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ k (latticeBump n) y‖ ≤ B) (s : Finset (Fin n → ℤ))
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖iteratedFDeriv ℝ k (fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) - 1) y‖ ≤
      B * (1 + (n : ℝ)) ^ n * (8 ^ n * ∑' d : Fin n → ℤ, latticeWeight d) + 1 := by
  have hs : ContDiff ℝ k fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) :=
    ContDiff.sum fun j _ ↦ contDiff_latticeBump_sub j
  have e : (fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j) - 1) =
      (fun y ↦ ∑ j ∈ s, latticeBump n (y - latticePoint j)) - fun _ ↦ (1 : ℝ) := rfl
  rw [e, iteratedFDeriv_sub_apply hs.contDiffAt contDiff_const.contDiffAt]
  refine (norm_sub_le _ _).trans (add_le_add
    (norm_iteratedFDeriv_sum_latticeBump_sub_le hB s y) ?_)
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · simp [iteratedFDeriv_const_of_ne hk]

end TauCeti
