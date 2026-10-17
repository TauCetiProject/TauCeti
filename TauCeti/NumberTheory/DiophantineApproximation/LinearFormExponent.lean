/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, Claude
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Exponent

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

## References

* Y. Bugeaud, *Exponents of Diophantine approximation*, §1, Definition 1.2 and §2,
  Definition 2.1.
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

/-- A nonzero integer vector has sup norm at least one. -/
private theorem one_le_norm_of_ne_zero {x : ℤ × (ι → ℤ)} (hx : x ≠ 0) : 1 ≤ ‖x‖ := by
  have hint {k : ℤ} (hk : k ≠ 0) : (1 : ℝ) ≤ ‖k‖ := by
    rw [Int.norm_eq_abs, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  by_cases h₁ : x.1 = 0
  · obtain ⟨i, hi⟩ : ∃ i, x.2 i ≠ 0 := by
      by_contra! h
      exact hx (Prod.ext h₁ (funext h))
    exact (hint hi).trans ((norm_le_pi_norm x.2 i).trans (norm_snd_le x))
  · exact (hint h₁).trans (norm_fst_le x)

/-- Every solution has sup norm at least one, since its linear form does not vanish. -/
private theorem one_le_norm_of_mem {θ : ι → ℝ} {w : ℝ} {x : ℤ × (ι → ℤ)}
    (hx : x ∈ linearFormApproximations θ w) : 1 ≤ ‖x‖ := by
  refine one_le_norm_of_ne_zero fun h ↦ ?_
  simp [h, mem_linearFormApproximations] at hx

/-- For a nonnegative exponent, every solution has linear form of absolute value at most one. -/
private theorem abs_le_one_of_mem {θ : ι → ℝ} {w : ℝ} (hw : 0 ≤ w) {x : ℤ × (ι → ℤ)}
    (hx : x ∈ linearFormApproximations θ w) :
    |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ 1 :=
  hx.2.trans (Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm_of_mem hx) (neg_nonpos.2 hw))

/-- The solution sets shrink as the exponent grows. -/
theorem linearFormApproximations_antitone (θ : ι → ℝ) :
    Antitone (linearFormApproximations θ) := fun _ _ hww' _ hx ↦
  ⟨hx.1, hx.2.trans (Real.rpow_le_rpow_of_exponent_le (one_le_norm_of_mem hx) (neg_le_neg hww'))⟩

/-- Only finitely many integer vectors have linear form of absolute value at most one and
coefficients `(xᵢ)ᵢ` of sup norm at most `N`. -/
private theorem finite_setOf_abs_le_one_norm_snd_le (θ : ι → ℝ) (N : ℝ) :
    {x : ℤ × (ι → ℤ) | |(x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * θ i| ≤ 1 ∧ ‖x.2‖ ≤ N}.Finite := by
  refine ((isCompact_closedBall (0 : ℤ × (ι → ℤ)) (max (1 + N * ∑ i, |θ i|) N)).finite_of_discrete
    ).subset fun x ⟨hL, hN⟩ ↦ ?_
  rw [mem_closedBall_zero_iff, Prod.norm_def]
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

/-- A vector indexed by `Fin 1` has the norm of its only coordinate. -/
private theorem norm_fin_one (y : Fin 1 → ℤ) : ‖y‖ = ‖y 0‖ :=
  le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (Fin.forall_fin_one.2 le_rfl))
    (norm_le_pi_norm y 0)

/-- For a single real number `ξ`, the linear form is `x₀ + x₁ ξ`. -/
private theorem linearForm_fin_one (ξ : ℝ) (x : ℤ × (Fin 1 → ℤ)) :
    (x.1 : ℝ) + ∑ i, (x.2 i : ℝ) * ![ξ] i = x.1 + x.2 0 * ξ := by
  simp

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
  rw [norm_fin_one, Int.norm_eq_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast,
    Nat.cast_le]
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
    have : (x.2 0 : ℝ) ≠ 0 := by exact_mod_cast h₀
    rw [hm]
    field_simp
    ring
  refine ⟨fun h ↦ hpos.ne' ?_, ?_⟩
  · have := sub_eq_zero.2 h
    rw [hsub, div_eq_zero_iff] at this
    simpa using this.resolve_right (by exact_mod_cast h₀)
  -- `|x₀ + x₁ ξ| ≤ ‖x‖ ^ (-w) ≤ n ^ (-w)`, and dividing by `n` gives the Liouville bound.
  have hnorm : (n : ℝ) ≤ ‖x‖ := by
    rw [habs, ← Int.norm_eq_abs, ← norm_fin_one]
    exact norm_snd_le x
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
    simp only [x, Int.cast_neg, Int.cast_natCast]
    field_simp
    ring
  -- `|-m + n ξ| < n · n ^ (-q) = n ^ (1 - q) ≤ 1`.
  have hLlt : |(x.1 : ℝ) + x.2 0 * ξ| < (n : ℝ) ^ (1 - q) := by
    rw [hL, abs_mul, abs_of_pos hn]
    calc (n : ℝ) * |ξ - m / n| < n * (n : ℝ) ^ (-q) := by gcongr
      _ = (n : ℝ) ^ (1 - q) := by rw [sub_eq_add_neg, Real.rpow_add hn, Real.rpow_one]
  have hLle : |(x.1 : ℝ) + x.2 0 * ξ| ≤ 1 :=
    hLlt.le.trans (Real.rpow_le_one_of_one_le_of_nonpos hn₁' (by linarith))
  -- The sup norm of `x = (-m, n)` lies between `n` and `(|ξ| + 1) n`.
  have hnorm : ‖x‖ = max |(m : ℝ)| n := by
    simp [x, Prod.norm_def, Int.norm_eq_abs]
  have hm : |(m : ℝ)| ≤ (|ξ| + 1) * n := by
    have : (m : ℝ) = n * ξ - (x.1 + x.2 0 * ξ) := by simp [x]
    rw [this]
    calc |(n : ℝ) * ξ - (x.1 + x.2 0 * ξ)| ≤ |(n : ℝ) * ξ| + |(x.1 : ℝ) + x.2 0 * ξ| :=
          abs_sub _ _
      _ ≤ n * |ξ| + n := by rw [abs_mul, abs_of_pos hn]; linarith
      _ = (|ξ| + 1) * n := by ring
  have hupper : ‖x‖ ≤ (|ξ| + 1) * n := by
    rw [hnorm]
    exact max_le hm (le_mul_of_one_le_left hn.le (by linarith [abs_nonneg ξ]))
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
        Real.rpow_le_rpow_of_nonpos (by rw [hnorm]; exact hn.trans_le (le_max_right _ _)) hupper
          (by linarith)

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

end TauCeti
