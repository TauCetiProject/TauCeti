/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Data.Pi.Interval
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

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

* `TauCeti.latticePoint j`: the point of `EuclideanSpace ℝ ι` with integer coordinates
  `j : ι → ℤ`; only finitely many of them lie in a ball
  (`TauCeti.finite_setOf_norm_latticePoint_lt`).
* `TauCeti.latticeBump n`: the smooth function `χ(x) = ∏ᵢ latticeBump₁ (xᵢ)`.
* `TauCeti.hasSum_latticeBump_sub`: `∑_{j ∈ ℤⁿ} χ(x - j) = 1`.
* `TauCeti.abs_lt_one_of_latticeBump_ne_zero`: `χ(x) ≠ 0` implies `|xᵢ| < 1` for every `i`.
* `TauCeti.tsupport_latticeBump_subset`: `χ` is supported in the closed ball of radius `√n`.
* `TauCeti.abs_sub_le_one_of_latticeBump_mul_ne_zero`: two integer translates of `χ` overlap only
  if their centres differ by at most one in every coordinate.
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

/-- The point of `EuclideanSpace ℝ ι` with integer coordinates `j`. -/
noncomputable def latticePoint {ι : Type*} (j : ι → ℤ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ (j i : ℝ)

@[simp]
theorem latticePoint_apply {ι : Type*} (j : ι → ℤ) (i : ι) : latticePoint j i = j i :=
  (rfl)

theorem latticePoint_sub {ι : Type*} (j j' : ι → ℤ) :
    latticePoint (j - j') = latticePoint j - latticePoint j' := by
  ext i
  simp

/-- Only finitely many lattice points lie in a ball. -/
theorem finite_setOf_norm_latticePoint_lt {ι : Type*} [Fintype ι] (R : ℝ) :
    {j : ι → ℤ | ‖latticePoint j‖ < R}.Finite := by
  classical
  refine (Set.finite_Icc (-fun _ : ι ↦ ⌈R⌉) fun _ ↦ ⌈R⌉).subset fun j hj ↦ ?_
  have hi : ∀ i, |(j i : ℝ)| ≤ R := fun i ↦ by
    simpa using (PiLp.norm_apply_le (latticePoint j) i).trans (le_of_lt hj)
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  · have h : (-(j i) : ℝ) ≤ ⌈R⌉ := by linarith [(abs_le.1 (hi i)).1, Int.le_ceil R]
    simp only [Pi.neg_apply, neg_le]
    exact_mod_cast h
  · exact Int.cast_le.1 ((abs_le.1 (hi i)).2.trans (Int.le_ceil R))

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

end TauCeti
