/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.LogGauge.Basic

/-!
# Rational values of the logarithmic gauge

Let `ϖ` be a multiplicative pseudo-uniformiser of a seminormed ring `R`, so that
`0 < ‖ϖ‖ < 1`. The norm is *commensurable* with `ϖ` when every nonzero norm is a rational
power of `‖ϖ‖`: for every `x` with `‖x‖ ≠ 0` there are integers `m` and `n > 0` with
`‖x‖ ^ n = ‖ϖ‖ ^ m`. Equivalently, the logarithmic gauge `v_ϖ(x) = log ‖x‖ / log ‖ϖ‖` is rational
wherever it is finite, and such a witness computes it as `v_ϖ(x) = m / n`. This is the case for
a discretely normed field such as `ℚ_[p]`, where the nonzero norms are rational powers of `‖ϖ‖`,
and integer powers when `‖ϖ‖` generates the value group.
It also holds for the algebraic closure of `ℚ_[p]`, whose nonzero norms are rational powers of
`p`, although that field is not discretely normed.

Commensurability does not depend on the pseudo-uniformiser: if `ϖ'` is another one, then
`v_ϖ = v_ϖ(ϖ') · v_ϖ'` (`logGauge_eq_map_mul`), and `v_ϖ(ϖ')` is a positive rational number when
the norm is commensurable with `ϖ`.

For a multiplicative ultrametric norm commensurable with `ϖ`, the logarithmic gauge is the image
of the *rational-valued* additive valuation `ratAddValuation`, normalised by `v_ϖ(ϖ) = 1`. It is
the unique rational-valued additive valuation recovering the norm through
`‖x‖ = ‖ϖ‖ ^ v_ϖ(x)`, and its real form satisfies `-log ‖x‖ = (-log ‖ϖ‖) · v_ϖ(x)`. Rational
values let one state that a slope or a root valuation has a given denominator without passing
through real numbers.

## Main definitions

* `TauCeti.NormedRing.PseudoUniformizer.IsCommensurable`: every nonzero norm is a rational
  power of `‖ϖ‖`.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation`: for a multiplicative ultrametric norm
  commensurable with `ϖ`, the additive valuation with values in `WithTop ℚ` normalised by
  `v_ϖ(ϖ) = 1`.

## Main results

* `TauCeti.NormedRing.PseudoUniformizer.logGauge_eq_of_norm_pow_eq`: a witness
  `‖x‖ ^ n = ‖ϖ‖ ^ m` with `n > 0` gives `v_ϖ(x) = m / n`.
* `TauCeti.NormedRing.PseudoUniformizer.isCommensurable_iff_exists_rat`: commensurability says
  that the logarithmic gauge is rational wherever it is finite.
* `TauCeti.NormedRing.PseudoUniformizer.isCommensurable_iff_isCommensurable`: commensurability
  does not depend on the pseudo-uniformiser.
* `TauCeti.NormedRing.PseudoUniformizer.map_ratAddValuation`: the real image of the rational
  valuation is the logarithmic gauge, that is, the real additive valuation `ϖ.addValuation`.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation_eq_coe_iff`: norm recovery,
  `v_ϖ(x) = q ↔ ‖x‖ = ‖ϖ‖ ^ q`, and `eq_ratAddValuation`: uniqueness of the rational valuation
  with this property.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation_eq_map_mul`: the rational valuations for
  two pseudo-uniformisers differ by the factor `v_ϖ(ϖ')`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §§3–4.
-/

public section

namespace TauCeti.NormedRing.PseudoUniformizer

variable {R : Type*} [SeminormedRing R] (ϖ : PseudoUniformizer R)

/-- The norm is **commensurable** with the multiplicative pseudo-uniformiser `ϖ` when every
nonzero norm is a rational power of `‖ϖ‖`: for each `x` with `‖x‖ ≠ 0` there are integers `m`
and `n > 0` with `‖x‖ ^ n = ‖ϖ‖ ^ m`. -/
def IsCommensurable : Prop :=
  ∀ x : R, ‖x‖ ≠ 0 → ∃ m : ℤ, ∃ n : ℕ, 0 < n ∧ ‖x‖ ^ n = ‖(ϖ.unit : R)‖ ^ m

variable {ϖ} {x : R}

/-- **A commensurability witness computes the logarithmic gauge**: if `‖x‖ ^ n = ‖ϖ‖ ^ m` with
`n > 0`, then `v_ϖ(x) = m / n`. -/
theorem logGauge_eq_of_norm_pow_eq {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : ‖x‖ ^ n = ‖(ϖ.unit : R)‖ ^ m) : ϖ.logGauge x = (((m / n : ℚ) : ℝ) : WithTop ℝ) := by
  rw [logGauge_eq_coe_iff, ← Real.pow_rpow_inv_natCast (norm_nonneg x) hn.ne', h,
    ← Real.rpow_intCast, ← Real.rpow_mul ϖ.norm_pos.le, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast, div_eq_mul_inv]

/-- The norm is commensurable with `ϖ` exactly when the logarithmic gauge is rational at every
element of nonzero norm. -/
theorem isCommensurable_iff_exists_rat :
    ϖ.IsCommensurable ↔ ∀ x : R, ‖x‖ ≠ 0 → ∃ q : ℚ, ϖ.logGauge x = ((q : ℝ) : WithTop ℝ) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨m, n, hn, hmn⟩ := h x hx
    exact ⟨_, logGauge_eq_of_norm_pow_eq hn hmn⟩
  · obtain ⟨q, hq⟩ := h x hx
    refine ⟨q.num, q.den, q.pos, ?_⟩
    rw [logGauge_eq_coe_iff.1 hq, ← Real.rpow_natCast, ← Real.rpow_mul ϖ.norm_pos.le,
      ← Real.rpow_intCast]
    exact congrArg _ (mod_cast Rat.mul_den_eq_num q)

/-- If every nonzero norm is an integer power of `‖ϖ‖`, as for a discretely normed field with
`‖ϖ‖` generating its value group, then the norm is commensurable with `ϖ`. -/
theorem isCommensurable_of_forall_exists_zpow
    (h : ∀ x : R, ‖x‖ ≠ 0 → ∃ m : ℤ, ‖x‖ = ‖(ϖ.unit : R)‖ ^ m) : ϖ.IsCommensurable := by
  intro x hx
  obtain ⟨m, hm⟩ := h x hx
  exact ⟨m, 1, one_pos, by rw [pow_one, hm]⟩

/-- If the norm is commensurable with `ϖ`, it is commensurable with every multiplicative
pseudo-uniformiser `ϖ'`: the logarithmic gauges differ by the positive rational factor
`v_ϖ(ϖ')`. -/
private theorem isCommensurable_of_isCommensurable (hϖ : ϖ.IsCommensurable)
    (ϖ' : PseudoUniformizer R) : ϖ'.IsCommensurable := by
  rw [isCommensurable_iff_exists_rat] at hϖ ⊢
  intro x hx
  obtain ⟨s, hs⟩ := hϖ _ ϖ'.norm_pos.ne'
  obtain ⟨q, hq⟩ := hϖ x hx
  have hs0 : (s : ℝ) ≠ 0 := by
    have := (logGauge_pos_iff (ϖ := ϖ)).2 ϖ'.norm_lt_one
    rw [hs, WithTop.coe_pos] at this
    exact this.ne'
  refine ⟨q / s, ?_⟩
  rw [logGauge_eq_map_mul ϖ' hs, logGauge_of_norm_ne_zero hx, WithTop.map_coe,
    WithTop.coe_inj] at hq
  rw [logGauge_of_norm_ne_zero hx, WithTop.coe_inj, Rat.cast_div, ← hq,
    mul_div_cancel_left₀ _ hs0]

/-- Commensurability of the norm does not depend on the multiplicative pseudo-uniformiser. -/
theorem isCommensurable_iff_isCommensurable (ϖ ϖ' : PseudoUniformizer R) :
    ϖ.IsCommensurable ↔ ϖ'.IsCommensurable :=
  ⟨fun h ↦ isCommensurable_of_isCommensurable h ϖ',
    fun h ↦ isCommensurable_of_isCommensurable h ϖ⟩

section RatAddValuation

variable (hϖ : ϖ.IsCommensurable)

/-- The rational value of the logarithmic gauge, and `⊤` on elements of norm zero. -/
private noncomputable def ratLogGauge (x : R) : WithTop ℚ :=
  if hx : ‖x‖ = 0 then ⊤ else (isCommensurable_iff_exists_rat.1 hϖ x hx).choose

/-- The real image of `ratLogGauge` is the logarithmic gauge. -/
private theorem map_ratLogGauge (x : R) :
    (ratLogGauge hϖ x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x := by
  unfold ratLogGauge
  split_ifs with hx
  · rw [WithTop.map_top, logGauge_of_norm_eq_zero hx]
  · rw [WithTop.map_coe]
    exact (isCommensurable_iff_exists_rat.1 hϖ x hx).choose_spec.symm

variable [NormMulClass R] [IsUltrametricDist R]

/-- For a multiplicative ultrametric norm commensurable with `ϖ`, the **rational-valued additive
valuation** normalised by `v_ϖ(ϖ) = 1`. Its real image is the logarithmic gauge
(`map_ratAddValuation`), and it recovers the norm by `‖x‖ = ‖ϖ‖ ^ v_ϖ(x)`
(`ratAddValuation_eq_coe_iff`). -/
noncomputable def ratAddValuation : AddValuation R (WithTop ℚ) :=
  AddValuation.of (ratLogGauge hϖ)
    (WithTop.map_injective (Rat.cast_injective (α := ℝ)) <| by
      rw [map_ratLogGauge, WithTop.map_top, logGauge_zero])
    (WithTop.map_injective (Rat.cast_injective (α := ℝ)) <| by
      rw [map_ratLogGauge, logGauge_one]; simp)
    (fun x y ↦ by
      rw [min_le_iff]
      simpa only [← WithTop.map_le_iff ((↑) : ℚ → ℝ) Rat.cast_le, map_ratLogGauge, min_le_iff]
        using ϖ.min_le_logGauge_add x y)
    (fun x y ↦ WithTop.map_injective (Rat.cast_injective (α := ℝ)) <| by
      rw [← Rat.coe_castHom, WithTop.map_add, Rat.coe_castHom, map_ratLogGauge, map_ratLogGauge,
        map_ratLogGauge, logGauge_mul])

/-- **The real image of the rational valuation is the logarithmic gauge.** -/
@[simp]
theorem map_ratAddValuation (x : R) :
    (ϖ.ratAddValuation hϖ x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x :=
  map_ratLogGauge hϖ x

/-- The rational valuation is infinite exactly on the elements of norm zero. -/
@[simp]
theorem ratAddValuation_eq_top_iff : ϖ.ratAddValuation hϖ x = ⊤ ↔ ‖x‖ = 0 := by
  rw [← logGauge_eq_top_iff (ϖ := ϖ), ← map_ratAddValuation hϖ, WithTop.map_eq_top_iff]

/-- **Norm recovery**: the rational valuation takes the value `q` exactly when
`‖x‖ = ‖ϖ‖ ^ q`. -/
theorem ratAddValuation_eq_coe_iff {q : ℚ} :
    ϖ.ratAddValuation hϖ x = q ↔ ‖x‖ = ‖(ϖ.unit : R)‖ ^ (q : ℝ) := by
  rw [← logGauge_eq_coe_iff, ← map_ratAddValuation hϖ, ← WithTop.map_coe ((↑) : ℚ → ℝ) q,
    (WithTop.map_injective Rat.cast_injective).eq_iff]

/-- An element of nonzero norm has norm `‖ϖ‖ ^ v_ϖ(x)`. -/
theorem norm_eq_rpow_ratAddValuation (hx : ‖x‖ ≠ 0) :
    ‖x‖ = ‖(ϖ.unit : R)‖ ^
      ((ϖ.ratAddValuation hϖ x).untop ((ratAddValuation_eq_top_iff hϖ).not.2 hx) : ℝ) :=
  (ratAddValuation_eq_coe_iff hϖ).1 (WithTop.coe_untop _ _).symm

/-- The real form of the rational valuation: if `v_ϖ(x) = q`, then
`-log ‖x‖ = (-log ‖ϖ‖) · q`. -/
theorem neg_log_norm_eq_mul {q : ℚ} (hq : ϖ.ratAddValuation hϖ x = q) :
    -Real.log ‖x‖ = -Real.log ‖(ϖ.unit : R)‖ * q := by
  rw [(ratAddValuation_eq_coe_iff hϖ).1 hq, Real.log_rpow ϖ.norm_pos]
  ring

/-- **A commensurability witness computes the rational valuation**: if `‖x‖ ^ n = ‖ϖ‖ ^ m` with
`n > 0`, then `v_ϖ(x) = m / n`. -/
theorem ratAddValuation_eq_of_norm_pow_eq {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : ‖x‖ ^ n = ‖(ϖ.unit : R)‖ ^ m) : ϖ.ratAddValuation hϖ x = ((m / n : ℚ) : WithTop ℚ) :=
  (ratAddValuation_eq_coe_iff hϖ).2 (logGauge_eq_coe_iff.1 (logGauge_eq_of_norm_pow_eq hn h))

/-- If `‖x‖ = ‖ϖ‖ ^ m` for an integer `m`, then `v_ϖ(x) = m`. -/
theorem ratAddValuation_eq_intCast {m : ℤ} (h : ‖x‖ = ‖(ϖ.unit : R)‖ ^ m) :
    ϖ.ratAddValuation hϖ x = ((m : ℚ) : WithTop ℚ) := by
  simpa using ratAddValuation_eq_of_norm_pow_eq hϖ one_pos (by rwa [pow_one])

/-- The rational valuation reverses the order of the norm. -/
theorem ratAddValuation_le_ratAddValuation_iff {y : R} :
    ϖ.ratAddValuation hϖ x ≤ ϖ.ratAddValuation hϖ y ↔ ‖y‖ ≤ ‖x‖ := by
  rw [← WithTop.map_le_iff ((↑) : ℚ → ℝ) Rat.cast_le, map_ratAddValuation, map_ratAddValuation,
    logGauge_le_logGauge_iff]

/-- The rational valuation of `ϖ` is one. -/
@[simp]
theorem ratAddValuation_unit : ϖ.ratAddValuation hϖ (ϖ.unit : R) = 1 := by
  simpa using ratAddValuation_eq_intCast hϖ (m := 1) (by rw [zpow_one])

/-- **Uniqueness**: a rational-valued additive valuation recovering the norm through
`‖x‖ = ‖ϖ‖ ^ w(x)` is the rational valuation `ϖ.ratAddValuation hϖ`. -/
theorem eq_ratAddValuation {w : AddValuation R (WithTop ℚ)}
    (hw : ∀ (x : R) (q : ℚ), w x = q ↔ ‖x‖ = ‖(ϖ.unit : R)‖ ^ (q : ℝ)) :
    w = ϖ.ratAddValuation hϖ := by
  ext x
  by_cases hx : ‖x‖ = 0
  · rw [(ratAddValuation_eq_top_iff hϖ).2 hx, WithTop.eq_top_iff_forall_ne]
    intro q hq
    have h := (hw x q).1 hq.symm
    rw [hx] at h
    exact (Real.rpow_pos_of_pos ϖ.norm_pos _).ne h
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 ((ratAddValuation_eq_top_iff hϖ).not.2 hx)
    rw [← hq, hw, ← ratAddValuation_eq_coe_iff hϖ, hq]

/-- **Changing the pseudo-uniformiser** rescales the rational valuation: if `v_ϖ(ϖ') = s`, then
`v_ϖ(x) = s · v_ϖ'(x)`. -/
theorem ratAddValuation_eq_map_mul {ϖ' : PseudoUniformizer R} (hϖ' : ϖ'.IsCommensurable) {s : ℚ}
    (hs : ϖ.ratAddValuation hϖ (ϖ'.unit : R) = s) (x : R) :
    ϖ.ratAddValuation hϖ x = (ϖ'.ratAddValuation hϖ' x).map (s * ·) := by
  apply WithTop.map_injective (Rat.cast_injective (α := ℝ))
  have ht : ϖ.logGauge (ϖ'.unit : R) = ((s : ℝ) : WithTop ℝ) := by
    rw [← map_ratAddValuation hϖ, hs, WithTop.map_coe]
  rw [map_ratAddValuation, logGauge_eq_map_mul ϖ' ht, ← map_ratAddValuation hϖ', WithTop.map_map,
    WithTop.map_map]
  congr 1
  ext t
  simp

end RatAddValuation

end TauCeti.NormedRing.PseudoUniformizer
