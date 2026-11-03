/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, Claude
-/
module

public import Mathlib.Analysis.Polynomial.Norm
public import Mathlib.FieldTheory.Minpoly.Basic
public import TauCeti.NumberTheory.DiophantineApproximation.Exponent
-- Proof-only: Dirichlet's theorem, and linear independence of powers.
import Mathlib.RingTheory.PowerBasis
import TauCeti.NumberTheory.DiophantineApproximation.Dirichlet
import TauCeti.RingTheory.Algebraic.LinearIndependent

/-!
# The linear-form exponent and Mahler's exponent

For `θ : ι → ℝ` with `ι` finite, the linear-form exponent `linearFormExponent θ` is the supremum
of the real exponents `w` for which infinitely many integer vectors `x = (x₀, (xᵢ)ᵢ)` satisfy
`0 < |x₀ + ∑ i, xᵢ θᵢ| ≤ ‖x‖ ^ (-w)`, where `‖x‖` is the sup norm over all coordinates of `x`,
including `x₀`. The supremum is taken in `ℝ≥0∞`, so negative exponents contribute `0`. Mahler's
exponent `mahlerExponent n ξ` is the linear-form exponent of `(ξ, ξ ^ 2, …, ξ ^ n)`, so it measures
how small nonzero values of integer polynomials of degree at most `n` can be at `ξ`.

## Main results

* `linearFormApproximations_antitone`: the solution sets shrink as the exponent grows.
* `linearFormExponent_comp_le`: forgetting coordinates along an injective reindexing can only
  decrease the exponent; in particular Mahler's exponent is monotone in the degree
  (`mahlerExponent_mono`).
* `linearFormExponent_of_isEmpty`: the empty vector has exponent `0`.
* `linearFormExponent_one_add`: for every real `ξ`, `w(ξ) + 1 = μ(ξ)`, where `μ` is the
  irrationality exponent. Consequently rational numbers have exponent `0`
  (`linearFormExponent_ratCast`) and exactly the Liouville numbers have exponent `⊤`
  (`linearFormExponent_eq_top_iff`).
* `card_le_linearFormExponent`: Dirichlet's lower bound `w(θ) ≥ n` when `1, θ₁, …, θₙ` satisfy no
  nontrivial integer relation; consequently `w_n(ξ) ≥ n` when `ξ` is not algebraic of degree at
  most `n` (`natCast_le_mahlerExponent`).
* `coeffVec` and `linearFormPoly`: the correspondence between integer polynomials of degree at
  most `n` and integer vectors `x = (x₀, (xⱼ)ⱼ)`, under which `P(ξ)` is the linear form of `x` at
  `ξ, ξ ^ 2, …, ξ ^ n`.

## References

* Y. Bugeaud, *Exponents of Diophantine approximation*, §1, Definition 1.2 and §2,
  Definition 2.1 and Theorem 2.5.
-/

public section

open Filter Function
open scoped ENNReal

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The integer vectors `x = (x₀, (xᵢ)ᵢ)` with `0 < |x₀ + ∑ i, xᵢ θᵢ| ≤ ‖x‖ ^ (-w)`; here `‖x‖` is
the sup norm over all coordinates of `x`, including `x₀`. -/
def linearFormApproximations (θ : ι → ℝ) (w : ℝ) : Set (ℤ × (ι → ℤ)) :=
  {x | 0 < |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ∧
    |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ ‖x‖ ^ (-w)}

/-- Membership in `linearFormApproximations θ w` unfolds to the two defining inequalities. -/
@[simp]
theorem mem_linearFormApproximations {θ : ι → ℝ} {w : ℝ} {x : ℤ × (ι → ℤ)} :
    x ∈ linearFormApproximations θ w ↔ 0 < |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ∧
      |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ ‖x‖ ^ (-w) :=
  Iff.rfl

/-- Every solution has sup norm at least one, since its linear form does not vanish. -/
private theorem one_le_norm_of_mem {θ : ι → ℝ} {w : ℝ} {x : ℤ × (ι → ℤ)}
    (hx : x ∈ linearFormApproximations θ w) : 1 ≤ ‖x‖ := by
  have hx₀ : x ≠ 0 := by
    intro h
    simp [h, mem_linearFormApproximations] at hx
  have hint {k : ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ ‖k‖ := by
    rw [Int.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  by_cases h₁ : x.1 = 0
  · obtain ⟨i, hi⟩ : ∃ i, x.2 i ≠ 0 := by
      by_contra! h
      exact hx₀ (Prod.ext h₁ (funext h))
    exact (hint hi).trans ((norm_le_pi_norm x.2 i).trans (norm_snd_le x))
  · exact (hint h₁).trans (norm_fst_le x)

/-- For a nonnegative exponent, every solution has linear form of absolute value at most one. -/
private theorem abs_le_one_of_mem {θ : ι → ℝ} {w : ℝ} (hw : 0 ≤ w) {x : ℤ × (ι → ℤ)}
    (hx : x ∈ linearFormApproximations θ w) :
    |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ 1 :=
  hx.2.trans (Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm_of_mem hx) (neg_nonpos.2 hw))

/-- The solution sets shrink as the exponent grows. -/
theorem linearFormApproximations_antitone (θ : ι → ℝ) :
    Antitone (linearFormApproximations θ) := fun _ _ hww' _ hx ↦
  ⟨hx.1, hx.2.trans (Real.rpow_le_rpow_of_exponent_le (one_le_norm_of_mem hx) (neg_le_neg hww'))⟩

/-- If the linear form `x₀ + ∑ i, xᵢ θᵢ` of an integer vector `x` has absolute value at most `δ`
and `‖(xᵢ)ᵢ‖ ≤ N`, then the sup norm of the full vector satisfies
`‖x‖ ≤ max (δ + N ∑ i, |θᵢ|) N`. -/
theorem norm_le_max_of_abs_add_sum_mul_le {θ : ι → ℝ} {δ N : ℝ} {x : ℤ × (ι → ℤ)}
    (hL : |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ δ) (hN : ‖x.2‖ ≤ N) :
    ‖x‖ ≤ max (δ + N * ∑ i, |θ i|) N := by
  rw [Prod.norm_def]
  refine max_le_max ?_ hN
  -- The coordinate `x₀` is the linear form minus the contribution of the other coordinates.
  have hsum : |∑ i, (x.2 i : ℝ) * θ i| ≤ N * ∑ i, |θ i| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [abs_mul, ← Int.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right ((norm_le_pi_norm x.2 i).trans hN) (abs_nonneg _)
  have h₁ : (x.1 : ℝ) = ((x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i) - ∑ i, (x.2 i : ℝ) * θ i := by ring
  rw [Int.norm_eq_abs, h₁]
  exact (abs_sub _ _).trans (add_le_add hL hsum)

/-- Only finitely many integer vectors have linear form of absolute value at most one and
coefficients `(xᵢ)ᵢ` of sup norm at most `N`. -/
private theorem finite_setOf_abs_le_one_norm_snd_le (θ : ι → ℝ) (N : ℝ) :
    {x : ℤ × (ι → ℤ) | |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ 1 ∧ ‖x.2‖ ≤ N}.Finite :=
  ((isCompact_closedBall (0 : ℤ × (ι → ℤ)) (max (1 + N * ∑ i, |θ i|) N)).finite_of_discrete
    ).subset fun _ ⟨hL, hN⟩ ↦ mem_closedBall_zero_iff.2 (norm_le_max_of_abs_add_sum_mul_le hL hN)

/-- The linear-form exponent `w(θ)` of `θ : ι → ℝ` is the supremum, in `ℝ≥0∞`, of the real
exponents `w` for which infinitely many integer vectors `x = (x₀, (xᵢ)ᵢ)` satisfy
`0 < |x₀ + ∑ i, xᵢ θᵢ| ≤ ‖x‖ ^ (-w)`. Negative exponents contribute `0`. -/
noncomputable def linearFormExponent (θ : ι → ℝ) : ℝ≥0∞ :=
  ⨆ (w : ℝ) (_ : (linearFormApproximations θ w).Infinite), ENNReal.ofReal w

/-- The linear-form exponent is the supremum of `ENNReal.ofReal w` over the exponents `w` with
infinitely many solutions. -/
theorem linearFormExponent_def (θ : ι → ℝ) :
    linearFormExponent θ =
      ⨆ (w : ℝ) (_ : (linearFormApproximations θ w).Infinite), ENNReal.ofReal w :=
  (rfl)

/-- An exponent with infinitely many solutions is at most the linear-form exponent. -/
theorem le_linearFormExponent_of_infinite {θ : ι → ℝ} {w : ℝ}
    (h : (linearFormApproximations θ w).Infinite) : ENNReal.ofReal w ≤ linearFormExponent θ :=
  le_iSup₂_of_le w h le_rfl

/-- The linear-form exponent is bounded by `a` exactly when every exponent with infinitely many
solutions maps below `a`. -/
theorem linearFormExponent_le_iff {θ : ι → ℝ} {a : ℝ≥0∞} :
    linearFormExponent θ ≤ a ↔
      ∀ w : ℝ, (linearFormApproximations θ w).Infinite → ENNReal.ofReal w ≤ a := by
  simp [linearFormExponent]

/-- A real exponent strictly below the linear-form exponent has infinitely many solutions. -/
theorem infinite_linearFormApproximations_of_lt {θ : ι → ℝ} {w : ℝ}
    (h : ENNReal.ofReal w < linearFormExponent θ) : (linearFormApproximations θ w).Infinite := by
  rw [linearFormExponent, lt_iSup_iff] at h
  obtain ⟨w', hw'⟩ := h
  rw [lt_iSup_iff] at hw'
  obtain ⟨hinf, hlt⟩ := hw'
  exact hinf.mono (linearFormApproximations_antitone θ (ENNReal.ofReal_lt_ofReal_iff'.mp hlt).1.le)

/-- Restricting `θ` along an injective reindexing can only decrease the linear-form exponent:
a solution for `θ ∘ f` extends by zero to a solution for `θ` with the same linear form and the
same norm. -/
theorem linearFormExponent_comp_le (θ : κ → ℝ) {f : ι → κ} (hf : Injective f) :
    linearFormExponent (θ ∘ f) ≤ linearFormExponent θ := by
  rw [linearFormExponent_le_iff]
  intro w hw
  let e : ℤ × (ι → ℤ) → ℤ × (κ → ℤ) := fun x ↦ (x.1, extend f x.2 0)
  have he : Injective e := fun x y hxy ↦ by
    simp only [e, Prod.mk.injEq] at hxy
    exact Prod.ext hxy.1 (funext fun i ↦ by simpa [hf.extend_apply] using congrFun hxy.2 (f i))
  refine le_linearFormExponent_of_infinite (hw.image he.injOn |>.mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  have hsum : ∑ k, ((extend f x.2 0 k : ℤ) : ℝ) * θ k = ∑ i, (x.2 i : ℝ) * θ (f i) := by
    rw [← Finset.sum_extend_zero_of_injective _ hf fun _ ↦ Finset.mem_univ _]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : ∃ i, f i = k
    · obtain ⟨i, rfl⟩ := hk
      simp [hf.extend_apply]
    · simp [extend_apply' _ _ _ hk]
  have hnorm : ‖extend f x.2 0‖ = ‖x.2‖ :=
    (hf.factorsThrough x.2).norm_extend (by simp)
  simpa [e, mem_linearFormApproximations, Prod.norm_def, hsum, hnorm] using hx

/-- The empty vector has linear-form exponent `0`: the linear form is then the integer `x₀`, which
is at most `|x₀| ^ (-w)` in absolute value only for `x₀ = ± 1` when `0 < w`. -/
@[simp]
theorem linearFormExponent_of_isEmpty [IsEmpty ι] (θ : ι → ℝ) : linearFormExponent θ = 0 := by
  refine le_antisymm (linearFormExponent_le_iff.2 fun w hw ↦ ?_) (by simp)
  rw [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero]
  by_contra! hw₀
  refine hw ((finite_setOf_abs_le_one_norm_snd_le θ 0).subset fun x hx ↦ ?_)
  exact ⟨abs_le_one_of_mem hw₀.le hx, by simp [Subsingleton.elim x.2 0]⟩

/-! ### Comparison with the irrationality exponent -/

/-- For a single real number `ξ`, the linear form is `x₀ + x₁ ξ`. -/
private theorem linearForm_fin_one (ξ : ℝ) (x : ℤ × (Fin 1 → ℤ)) :
    (x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * ![ξ] i = x.1 + x.2 0 * ξ := by
  simp

/-- Rewriting a nondegenerate one-variable linear form as the error of its associated rational
approximation. -/
private theorem linearForm_fin_one_eq_mul_sub (ξ : ℝ) (x : ℤ × (Fin 1 → ℤ))
    (hx : x.2 0 ≠ 0) :
    (x.1 : ℝ) + x.2 0 * ξ = x.2 0 * (ξ - (-x.1 / x.2 0)) := by
  have hx' : (x.2 0 : ℝ) ≠ 0 := by exact_mod_cast hx
  field_simp
  ring

/-- If the value of a one-variable linear form is at most its nonnegative linear coefficient,
then its full coefficient norm is controlled by that coefficient. -/
private theorem norm_le_abs_add_one_mul_of_abs_linearForm_le (ξ : ℝ)
    (x : ℤ × (Fin 1 → ℤ)) (hx₂ : 0 ≤ (x.2 0 : ℝ))
    (hL : |(x.1 : ℝ) + x.2 0 * ξ| ≤ (x.2 0 : ℝ)) :
    ‖x‖ ≤ (|ξ| + 1) * (x.2 0 : ℝ) := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [Int.norm_eq_abs]
    have hx₁ : (x.1 : ℝ) = ((x.1 : ℝ) + x.2 0 * ξ) - x.2 0 * ξ := by ring
    rw [hx₁]
    calc
      |(x.1 : ℝ) + x.2 0 * ξ - x.2 0 * ξ| ≤
          |(x.1 : ℝ) + x.2 0 * ξ| + |(x.2 0 : ℝ) * ξ| := abs_sub _ _
      _ ≤ (x.2 0 : ℝ) + (x.2 0 : ℝ) * |ξ| := by
        rw [abs_mul, abs_of_nonneg hx₂]
        gcongr
      _ = (|ξ| + 1) * (x.2 0 : ℝ) := by ring
  · rw [pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) hx₂)]
    intro i
    rw [Subsingleton.elim i 0, Int.norm_eq_abs, abs_of_nonneg hx₂]
    exact le_mul_of_one_le_left hx₂ (by linarith [abs_nonneg ξ])

/-- If a positive exponent `w` has infinitely many solutions for `![ξ]`, then `ξ` is a Liouville
number with exponent `1 + w`: a solution `(x₀, x₁)` with `x₁ ≠ 0` gives
`|ξ + x₀ / x₁| ≤ |x₁| ^ (-1 - w)`. -/
private theorem liouvilleWith_one_add_of_infinite {ξ w : ℝ} (hw : 0 < w)
    (h : (linearFormApproximations ![ξ] w).Infinite) : LiouvilleWith (1 + w) ξ := by
  refine ⟨2, Nat.frequently_atTop_iff_infinite.2 fun hfin ↦ h ?_⟩
  obtain ⟨N, hN⟩ := hfin.bddAbove
  -- Every solution has `|x₁| ≤ N`, so the solutions lie in a finite set.
  refine (finite_setOf_abs_le_one_norm_snd_le ![ξ] N).subset fun x hx ↦
    ⟨abs_le_one_of_mem hw.le hx, ?_⟩
  suffices hnat : (x.2 0).natAbs ≤ N by
    rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg N)]
    intro i
    rw [Subsingleton.elim i 0, Int.norm_eq_abs]
    have hz : |x.2 0| ≤ (N : ℤ) := by
      simpa only [Int.abs_eq_natAbs, Int.ofNat_le] using hnat
    exact_mod_cast hz
  by_cases h₀ : x.2 0 = 0
  · simp [h₀]
  obtain ⟨hpos, hle⟩ := hx
  rw [linearForm_fin_one] at hpos hle
  set n := (x.2 0).natAbs
  have habs : (n : ℝ) = |(x.2 0 : ℝ)| := by simp [n, Int.cast_abs]
  have hn : (0 : ℝ) < n := by simpa [habs] using h₀
  -- The candidate fraction is `-x₀ / x₁`, written with the positive denominator `n = |x₁|`.
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (m : ℝ) / n = -x.1 / x.2 0 := by
    rcases lt_or_gt_of_ne h₀ with hlt | hgt
    · refine ⟨x.1, ?_⟩
      rw [habs, abs_of_neg (by exact_mod_cast hlt), div_neg, neg_div]
    · refine ⟨-x.1, ?_⟩
      rw [habs, abs_of_pos (by exact_mod_cast hgt), Int.cast_neg]
  refine hN ⟨m, ?_⟩
  have hsub : ξ - (m : ℝ) / n = (x.1 + x.2 0 * ξ) / x.2 0 := by
    rw [hm, linearForm_fin_one_eq_mul_sub ξ x h₀]
    field_simp
  refine ⟨fun h ↦ hpos.ne' ?_, ?_⟩
  · have := sub_eq_zero.2 h
    rw [hsub, div_eq_zero_iff] at this
    simpa using this.resolve_right (by exact_mod_cast h₀)
  -- `|x₀ + x₁ ξ| ≤ ‖x‖ ^ (-w) ≤ n ^ (-w)`, and dividing by `n` gives the Liouville bound.
  have hnorm : (n : ℝ) ≤ ‖x‖ := by
    calc
      (n : ℝ) = ‖x.2 0‖ := by rw [habs, Int.norm_eq_abs]
      _ ≤ ‖x.2‖ := norm_le_pi_norm x.2 0
      _ ≤ ‖x‖ := norm_snd_le x
  have hbound : |(x.1 : ℝ) + x.2 0 * ξ| ≤ (n : ℝ) ^ (-w) :=
    hle.trans (Real.rpow_le_rpow_of_nonpos hn hnorm (neg_nonpos.2 hw.le))
  rw [hsub, abs_div, ← habs]
  calc |(x.1 : ℝ) + x.2 0 * ξ| / n ≤ (n : ℝ) ^ (-w) / n := by gcongr
    _ = 1 / (n : ℝ) ^ (1 + w) := by
      rw [Real.rpow_neg hn.le, Real.rpow_add hn, Real.rpow_one]
      field_simp
    _ < 2 / (n : ℝ) ^ (1 + w) := by gcongr; norm_num

/-- If `ξ` is a Liouville number with exponent `p` and `1 < r < p`, then `r - 1` has infinitely
many solutions for `![ξ]`: an approximation `|ξ - m / n| < n ^ (-q)` with `r < q < p` gives
`0 < |-m + n ξ| < n ^ (1 - q)`, while `‖(-m, n)‖ ≤ (|ξ| + 1) n`. -/
private theorem infinite_linearFormApproximations_of_liouvilleWith {ξ p r : ℝ}
    (h : LiouvilleWith p ξ) (hr : 1 < r) (hrp : r < p) :
    (linearFormApproximations ![ξ] (r - 1)).Infinite := by
  obtain ⟨q, hrq, hqp⟩ := exists_between hrp
  set C : ℝ := (|ξ| + 1) ^ (1 - r)
  have hC : 0 < C := by positivity
  have hsmall : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (r - q) ≤ C := by
    have := ((tendsto_rpow_neg_atTop (sub_pos.2 hrq)).comp
      tendsto_natCast_atTop_atTop).eventually (ge_mem_nhds hC)
    simpa only [comp_apply, neg_sub] using this
  -- The second coordinates of the solutions are unbounded.
  refine Set.Infinite.of_image (fun x : ℤ × (Fin 1 → ℤ) ↦ x.2 0) ?_
  refine Set.infinite_of_not_bddAbove fun ⟨B, hB⟩ ↦ ?_
  obtain ⟨n, ⟨hnB, hn₁, hnC⟩, m, hne, hlt⟩ := ((eventually_gt_atTop B.toNat).and
    ((eventually_ge_atTop 1).and hsmall)).and_frequently (h.frequently_lt_rpow_neg hqp) |>.exists
  have hn : (0 : ℝ) < n := by exact_mod_cast hn₁
  have hn₁' : (1 : ℝ) ≤ n := by exact_mod_cast hn₁
  set x : ℤ × (Fin 1 → ℤ) := (-m, fun _ ↦ (n : ℤ))
  suffices hx : x ∈ linearFormApproximations ![ξ] (r - 1) by
    have := hB ⟨x, hx, rfl⟩
    simp only [x] at this
    omega
  have hL : (x.1 : ℝ) + x.2 0 * ξ = n * (ξ - m / n) := by
    simpa [x, hn.ne'] using linearForm_fin_one_eq_mul_sub ξ x (by simpa [x] using hn.ne')
  -- `|-m + n ξ| < n · n ^ (-q) = n ^ (1 - q) ≤ 1`.
  have hLlt : |(x.1 : ℝ) + x.2 0 * ξ| < (n : ℝ) ^ (1 - q) := by
    rw [hL, abs_mul, abs_of_pos hn]
    calc (n : ℝ) * |ξ - m / n| < n * (n : ℝ) ^ (-q) := by gcongr
      _ = (n : ℝ) ^ (1 - q) := by rw [sub_eq_add_neg, Real.rpow_add hn, Real.rpow_one]
  have hLle : |(x.1 : ℝ) + x.2 0 * ξ| ≤ 1 :=
    hLlt.le.trans (Real.rpow_le_one_of_one_le_of_nonpos hn₁' (by linarith))
  -- The sup norm of `x = (-m, n)` lies between `n` and `(|ξ| + 1) n`.
  have hlower : (n : ℝ) ≤ ‖x‖ := by
    simp [x, Prod.norm_def, Int.norm_eq_abs]
  have hupper : ‖x‖ ≤ (|ξ| + 1) * n := by
    simpa [x] using
      norm_le_abs_add_one_mul_of_abs_linearForm_le ξ x hn.le (hLle.trans hn₁')
  rw [mem_linearFormApproximations, linearForm_fin_one, neg_sub]
  refine ⟨?_, hLlt.le.trans ?_⟩
  · rw [hL, abs_mul, abs_of_pos hn]
    exact mul_pos hn (abs_pos.2 (sub_ne_zero.2 hne))
  calc (n : ℝ) ^ (1 - q) = (n : ℝ) ^ (1 - r) * (n : ℝ) ^ (r - q) := by
        rw [← Real.rpow_add hn]
        ring_nf
    _ ≤ (n : ℝ) ^ (1 - r) * C := by gcongr
    _ = ((|ξ| + 1) * n) ^ (1 - r) := by
        rw [Real.mul_rpow (by positivity) hn.le, mul_comm]
    _ ≤ ‖x‖ ^ (1 - r) :=
        Real.rpow_le_rpow_of_nonpos (hn.trans_le hlower) hupper (by linarith)

/-- The linear-form exponent of a single real number `ξ` is its irrationality exponent minus
one: `w(ξ) + 1 = μ(ξ)`. Both sides equal `1` for rational `ξ`. -/
theorem linearFormExponent_one_add (ξ : ℝ) :
    linearFormExponent ![ξ] + 1 = irrationalityExponent ξ := by
  refine le_antisymm ?_ ?_
  · have hle : linearFormExponent ![ξ] ≤ irrationalityExponent ξ - 1 := by
      refine linearFormExponent_le_iff.2 fun w hw ↦
        ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top ?_
      rcases le_or_gt w 0 with hw₀ | hw₀
      · simpa [ENNReal.ofReal_of_nonpos hw₀] using one_le_irrationalityExponent ξ
      · have := le_irrationalityExponent_of_liouvilleWith
          (liouvilleWith_one_add_of_infinite hw₀ hw)
        rwa [ENNReal.ofReal_add zero_le_one hw₀.le, ENNReal.ofReal_one, add_comm] at this
    calc linearFormExponent ![ξ] + 1 ≤ irrationalityExponent ξ - 1 + 1 := by gcongr
      _ = irrationalityExponent ξ := tsub_add_cancel_of_le (one_le_irrationalityExponent ξ)
  · refine irrationalityExponent_le_iff.2 fun p hp ↦ ?_
    rcases le_or_gt p 1 with hp₁ | hp₁
    · exact (ENNReal.ofReal_le_ofReal hp₁).trans (by simp)
    -- Approximate `ENNReal.ofReal p` from below by exponents `r` with `1 < r < p`.
    refine le_of_forall_lt fun c hc ↦ ?_
    have hct : c ≠ ⊤ := hc.ne_top
    have hcp : c.toReal < p := (ENNReal.lt_ofReal_iff_toReal_lt hct).1 hc
    obtain ⟨r, hr_def⟩ : ∃ r, r = (max c.toReal 1 + p) / 2 := ⟨_, rfl⟩
    have hmax : max c.toReal 1 < p := max_lt hcp hp₁
    have hr : 1 < r := by linarith [le_max_right c.toReal 1]
    have hcr : c < ENNReal.ofReal r :=
      (ENNReal.lt_ofReal_iff_toReal_lt hct).2 (by linarith [le_max_left c.toReal 1])
    calc c < ENNReal.ofReal r := hcr
      _ = ENNReal.ofReal (r - 1) + 1 := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one, sub_add_cancel]
      _ ≤ linearFormExponent ![ξ] + 1 := by
        gcongr
        exact le_linearFormExponent_of_infinite
          (infinite_linearFormApproximations_of_liouvilleWith hp hr (by linarith))

/-- A rational number has linear-form exponent `0`. -/
@[simp]
theorem linearFormExponent_ratCast (q : ℚ) : linearFormExponent ![(q : ℝ)] = 0 := by
  have := linearFormExponent_one_add q
  rw [irrationalityExponent_ratCast] at this
  simpa using this

/-- A real number has infinite linear-form exponent exactly when it is a Liouville number. -/
theorem linearFormExponent_eq_top_iff (ξ : ℝ) :
    linearFormExponent ![ξ] = ⊤ ↔ Liouville ξ := by
  rw [← irrationalityExponent_eq_top_iff, ← linearFormExponent_one_add, ENNReal.add_eq_top]
  simp

/-! ### Dirichlet's lower bound -/

/-- **Dirichlet's theorem for one linear form, infinitely many solutions.** If `1` and the
`n ≥ 1` real numbers `θᵢ` satisfy no nontrivial integer relation, then every exponent `w < n` has
infinitely many solutions `0 < |x₀ + ∑ i, xᵢ θᵢ| ≤ ‖x‖ ^ (-w)`, with the sup norm taken over all
coordinates of `x`. -/
theorem infinite_linearFormApproximations_of_lt_card [Nonempty ι] {θ : ι → ℝ}
    (hθ : ∀ x : ℤ × (ι → ℤ), (x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i = 0 → x = 0) {w : ℝ}
    (hw : w < Fintype.card ι) : (linearFormApproximations θ w).Infinite := by
  wlog hw₀ : 0 ≤ w generalizing w
  · exact (this (Nat.cast_pos.2 Fintype.card_pos) le_rfl).mono
      (linearFormApproximations_antitone θ (le_of_not_ge hw₀))
  set n : ℝ := ((Fintype.card ι : ℕ) : ℝ)
  -- Dirichlet's theorem bounds the linear form by `‖(xᵢ)ᵢ‖ ^ (-n)`, without the coordinate `x₀`.
  set T := {x : ℤ × (ι → ℤ) | x.2 ≠ 0 ∧ |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ ‖x.2‖ ^ (-n)}
  have hT : T.Infinite := by
    have hD := dirichlet_linearForm_infinite θ fun y ⟨k, hk⟩ ↦ congrArg Prod.snd <|
      hθ (-k, y) (by push_cast; rw [← hk]; simp [mul_comm])
    refine (hD.image (neg_injective.prodMap injective_id).injOn).mono ?_
    rintro _ ⟨p, ⟨hp, hpL⟩, rfl⟩
    exact ⟨hp, by simpa [n, neg_add_eq_sub, mul_comm] using hpL⟩
  -- Every solution with `‖(xᵢ)ᵢ‖` large has `‖x‖ ≤ C ‖(xᵢ)ᵢ‖`, and the constant `C` is absorbed
  -- by the gap between `w` and `n`.
  set C : ℝ := 1 + ∑ i, |θ i|
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)
  obtain ⟨R, hR⟩ := eventually_atTop.1 <|
    (tendsto_rpow_atTop (sub_pos.2 hw)).eventually_ge_atTop (C ^ w)
  refine (hT.sdiff (finite_setOf_abs_le_one_norm_snd_le θ R)).mono ?_
  rintro x ⟨⟨hx, hxL⟩, hxR⟩
  set N := ‖x.2‖
  have hN : 1 ≤ N := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine le_trans ?_ (norm_le_pi_norm x.2 i)
    rw [Int.norm_eq_abs]
    exact_mod_cast Int.one_le_abs hi
  have hL₁ : |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ 1 :=
    hxL.trans (Real.rpow_le_one_of_one_le_of_nonpos hN (by simp [n]))
  have hNR : R ≤ N := (not_le.1 (not_and.1 hxR hL₁)).le
  have hxC : ‖x‖ ≤ C * N := (norm_le_max_of_abs_add_sum_mul_le hL₁ le_rfl).trans <| max_le
    (by nlinarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) ↦ abs_nonneg (θ i)])
    (le_mul_of_one_le_left (by linarith) hC)
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  refine ⟨abs_pos.2 fun h ↦ hx (congrArg Prod.snd (hθ x h)), hxL.trans ?_⟩
  calc N ^ (-n) = N ^ (-w) * (N ^ (n - w))⁻¹ := by
        rw [← Real.rpow_neg hN₀.le, ← Real.rpow_add hN₀]
        ring_nf
    _ ≤ N ^ (-w) * (C ^ w)⁻¹ := by gcongr; exact hR N hNR
    _ = (C * N) ^ (-w) := by
        rw [Real.mul_rpow (by linarith) hN₀.le, Real.rpow_neg (by linarith : (0 : ℝ) ≤ C) w,
          mul_comm]
    _ ≤ ‖x‖ ^ (-w) :=
        Real.rpow_le_rpow_of_nonpos (hN₀.trans_le (norm_snd_le x)) hxC (neg_nonpos.2 hw₀)

/-- **Dirichlet's lower bound for the linear-form exponent.** If `1` and the `n` real numbers
`θᵢ` satisfy no nontrivial integer relation, that is, if they are linearly independent over `ℚ`,
then the linear-form exponent of `θ` is at least `n`. -/
theorem card_le_linearFormExponent {θ : ι → ℝ}
    (hθ : ∀ x : ℤ × (ι → ℤ), (x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i = 0 → x = 0) :
    (Fintype.card ι : ℝ≥0∞) ≤ linearFormExponent θ := by
  cases isEmpty_or_nonempty ι
  · simp
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hr' : (r : ℝ) < Fintype.card ι := by exact_mod_cast hr
  simpa using
    le_linearFormExponent_of_infinite (infinite_linearFormApproximations_of_lt_card hθ hr')

/-! ### Mahler's exponent -/

/-- Mahler's exponent `w_n(ξ)` is the linear-form exponent of `(ξ, ξ ^ 2, …, ξ ^ n)`: the
supremum of the `w` for which infinitely many integer polynomials `P` of degree at most `n`
satisfy `0 < |P(ξ)| ≤ H(P) ^ (-w)`, where `H(P)` is the largest absolute value of a coefficient
of `P`. -/
noncomputable def mahlerExponent (n : ℕ) (ξ : ℝ) : ℝ≥0∞ :=
  linearFormExponent fun j : Fin n ↦ ξ ^ (j.val + 1)

/-- Mahler's exponent unfolds to the linear-form exponent of the powers `ξ, ξ ^ 2, …, ξ ^ n`. -/
theorem mahlerExponent_def (n : ℕ) (ξ : ℝ) :
    mahlerExponent n ξ = linearFormExponent fun j : Fin n ↦ ξ ^ (j.val + 1) :=
  (rfl)

section CoeffVec

open Polynomial

/-- The coefficients of `P` in degrees `0, 1, …, n`, split into the constant term and the
coefficients of `X, X ^ 2, …, X ^ n`. For `P` of degree at most `n`, the linear form of this vector
at `ξ, ξ ^ 2, …, ξ ^ n` is `P(ξ)`. -/
def coeffVec (n : ℕ) (P : ℤ[X]) : ℤ × (Fin n → ℤ) :=
  (P.coeff 0, fun j ↦ P.coeff (j.val + 1))

/-- The integer polynomial `x₀ + ∑ j, xⱼ X ^ (j + 1)` of degree at most `n`, a right inverse of
`coeffVec n`. Its value at `ξ` is the linear form of `x` at `ξ, ξ ^ 2, …, ξ ^ n`. -/
noncomputable def linearFormPoly {n : ℕ} (x : ℤ × (Fin n → ℤ)) : ℤ[X] :=
  C x.1 + ∑ j, C (x.2 j) * X ^ (j.val + 1)

/-- The first component of `coeffVec n P` is the constant coefficient of `P`. -/
@[simp]
theorem coeffVec_fst (n : ℕ) (P : ℤ[X]) : (coeffVec n P).1 = P.coeff 0 := by
  simp only [coeffVec]

/-- The `j`-th entry of the second component of `coeffVec n P` is the coefficient of
`X ^ (j + 1)` in `P`. -/
@[simp]
theorem coeffVec_snd (n : ℕ) (P : ℤ[X]) (j : Fin n) : (coeffVec n P).2 j = P.coeff (j.val + 1) := by
  simp only [coeffVec]

/-- For `P` of degree at most `n`, the linear form of `coeffVec n P` at the powers of `z` is
`P(z)`. -/
theorem coeffVec_linearForm {A : Type*} [CommRing A] {n : ℕ} {P : ℤ[X]}
    (hP : P.natDegree ≤ n) (z : A) :
    ((coeffVec n P).1 : A) + ∑ j, ((coeffVec n P).2 j : A) * z ^ (j.val + 1) = aeval z P := by
  simp only [coeffVec_fst, coeffVec_snd]
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hP), Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun j ↦ (P.coeff (j + 1) : A) * z ^ (j + 1)) n]
  simp [zsmul_eq_mul, add_comm]

/-- The sup norm of `coeffVec n P` is at most the coefficient sup norm of `P`. -/
theorem norm_coeffVec_le (n : ℕ) (P : ℤ[X]) : ‖coeffVec n P‖ ≤ P.supNorm :=
  max_le (P.le_supNorm 0) ((pi_norm_le_iff_of_nonneg P.supNorm_nonneg).2 fun _ ↦ P.le_supNorm _)

/-- Polynomials of degree at most `n` are determined by `coeffVec n`. -/
theorem coeffVec_injOn (n : ℕ) : Set.InjOn (coeffVec n) {P | P.natDegree ≤ n} := by
  intro P hP Q hQ h
  refine (ext_iff_natDegree_le hP hQ).2 fun i hi ↦ ?_
  rcases i with _ | i
  · exact congrArg Prod.fst h
  · exact congrFun (congrArg Prod.snd h) ⟨i, by omega⟩

/-- The polynomial `linearFormPoly x` has degree at most `n`. -/
theorem natDegree_linearFormPoly_le {n : ℕ} (x : ℤ × (Fin n → ℤ)) :
    (linearFormPoly x).natDegree ≤ n :=
  (natDegree_add_le _ _).trans <| max_le (by simp) <| natDegree_sum_le_of_forall_le _ _
    fun j _ ↦ (natDegree_C_mul_X_pow_le _ _).trans j.isLt

/-- `coeffVec n` recovers `x` from `linearFormPoly x`. -/
@[simp]
theorem coeffVec_linearFormPoly {n : ℕ} (x : ℤ × (Fin n → ℤ)) :
    coeffVec n (linearFormPoly x) = x := by
  refine Prod.ext (by simp [linearFormPoly]) (funext fun k ↦ ?_)
  simp only [coeffVec_snd, linearFormPoly, coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul_X_pow]
  simp [Fin.val_inj]

/-- On polynomials of degree at most `n`, `linearFormPoly` inverts `coeffVec n`. -/
theorem linearFormPoly_coeffVec {n : ℕ} {P : ℤ[X]} (hP : P.natDegree ≤ n) :
    linearFormPoly (coeffVec n P) = P :=
  coeffVec_injOn n (natDegree_linearFormPoly_le _) hP (coeffVec_linearFormPoly _)

/-- The constant coefficient of `linearFormPoly x` is `x₀`. -/
@[simp]
theorem coeff_linearFormPoly_zero {n : ℕ} (x : ℤ × (Fin n → ℤ)) :
    (linearFormPoly x).coeff 0 = x.1 := by
  rw [← coeffVec_fst n, coeffVec_linearFormPoly]

/-- The coefficient of `X ^ (j + 1)` in `linearFormPoly x` is `xⱼ`. -/
@[simp]
theorem coeff_linearFormPoly_succ {n : ℕ} (x : ℤ × (Fin n → ℤ)) (j : Fin n) :
    (linearFormPoly x).coeff (j.val + 1) = x.2 j := by
  rw [← coeffVec_snd n, coeffVec_linearFormPoly]

/-- The value of `linearFormPoly x` at `z` is the linear form of `x` at the powers of `z`. -/
theorem aeval_linearFormPoly {A : Type*} [CommRing A] {n : ℕ} (x : ℤ × (Fin n → ℤ)) (z : A) :
    aeval z (linearFormPoly x) = (x.1 : A) + ∑ j, (x.2 j : A) * z ^ (j.val + 1) := by
  rw [← coeffVec_linearForm (natDegree_linearFormPoly_le x), coeffVec_linearFormPoly]

/-- The coefficient sup norm of `linearFormPoly x` is at most the sup norm of `x`. -/
theorem supNorm_linearFormPoly_le {n : ℕ} (x : ℤ × (Fin n → ℤ)) :
    (linearFormPoly x).supNorm ≤ ‖x‖ := by
  rw [supNorm_eq_iSup]
  refine ciSup_le fun i ↦ ?_
  simp only [linearFormPoly, coeff_add, coeff_C, finsetSum_coeff, coeff_C_mul_X_pow]
  rcases i with _ | k
  · simpa using norm_fst_le x
  · by_cases hk : k < n
    · have h (j : Fin n) : k = j.val ↔ ⟨k, hk⟩ = j := (Fin.ext_iff (a := ⟨k, hk⟩)).symm
      simpa [h] using (norm_le_pi_norm x.2 ⟨k, hk⟩).trans (norm_snd_le x)
    · have h (j : Fin n) : k ≠ j.val := by
        have := j.isLt
        omega
      simp [h]

end CoeffVec

/-- Mahler's exponent is monotone in the degree. -/
theorem mahlerExponent_mono (ξ : ℝ) : Monotone (mahlerExponent · ξ) := fun m n hmn ↦ by
  simpa [mahlerExponent_def, comp_def] using
    linearFormExponent_comp_le (fun j : Fin n ↦ ξ ^ (j.val + 1)) (Fin.castLE_injective hmn)

/-- Constant integer polynomials give Mahler's exponent `0` in degree zero. -/
@[simp]
theorem mahlerExponent_zero (ξ : ℝ) : mahlerExponent 0 ξ = 0 :=
  linearFormExponent_of_isEmpty _

/-- Mahler's exponent in degree one is the irrationality exponent minus one. -/
theorem mahlerExponent_one_add_one (ξ : ℝ) : mahlerExponent 1 ξ + 1 = irrationalityExponent ξ := by
  have : (fun j : Fin 1 ↦ ξ ^ (j.val + 1)) = ![ξ] := by
    ext j
    fin_cases j
    simp
  rw [mahlerExponent_def, this, linearFormExponent_one_add]

/-- **Dirichlet's lower bound for Mahler's exponent.** If `ξ` is not algebraic of degree at
most `n`, then `w_n(ξ) ≥ n`. -/
theorem natCast_le_mahlerExponent {n : ℕ} {ξ : ℝ}
    (hξ : ¬(IsAlgebraic ℚ ξ ∧ (minpoly ℚ ξ).natDegree ≤ n)) :
    (n : ℝ≥0∞) ≤ mahlerExponent n ξ := by
  -- The powers `1, ξ, …, ξ ^ n` are linearly independent over `ℚ`.
  have hind : LinearIndependent ℚ fun k : Fin (n + 1) ↦ ξ ^ (k : ℕ) := by
    by_cases halg : IsAlgebraic ℚ ξ
    · have hle : n + 1 ≤ (minpoly ℚ ξ).natDegree := Nat.succ_le_of_lt (not_le.1 (hξ ⟨halg, ·⟩))
      exact (linearIndependent_pow ξ).comp (Fin.castLE hle) (Fin.castLE_injective hle)
    · exact (Transcendental.linearIndependent_pow halg).comp _ Fin.val_injective
  -- An integer relation is a rational relation among `1, ξ, …, ξ ^ n`.
  have hrel (x : ℤ × (Fin n → ℤ)) (hx : (x.1 : ℝ) + ∑ j, (x.2 j : ℝ) * ξ ^ (j.val + 1) = 0) :
      x = 0 := by
    have h0 := Fintype.linearIndependent_iff.1 hind (Fin.cons (x.1 : ℚ) fun j ↦ (x.2 j : ℚ))
      (by simpa [Fin.sum_univ_succ, Rat.smul_def] using hx)
    exact Prod.ext (by simpa using h0 0) (funext fun j ↦ by simpa using h0 j.succ)
  simpa [mahlerExponent_def] using card_le_linearFormExponent hrel

end TauCeti
