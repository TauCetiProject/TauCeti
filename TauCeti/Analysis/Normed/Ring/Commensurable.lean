/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Ring.LogGauge
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import TauCeti.Analysis.Normed.Ring.UnitBall

/-!
# Rational valuations normalised at a commensurable pseudo-uniformiser

Let `R` be a seminormed ring with a multiplicative pseudo-uniformiser `ϖ`, so `0 < ‖ϖ‖ < 1`.
Its logarithmic gauge `v_ϖ(x) = log ‖x‖ / log ‖ϖ‖` is real valued. The pseudo-uniformiser is
*commensurable* when every nonzero norm is commensurable with `‖ϖ‖`: for each `x` of nonzero norm
there are integers `m` and `n > 0` with `‖x‖ ^ n = ‖ϖ‖ ^ m`. Such a witness forces
`v_ϖ(x) = m / n`, so commensurability says exactly that the logarithmic gauge takes rational values
away from the elements of norm zero.

For a multiplicative ultrametric norm the logarithmic gauge is an additive valuation, and for a
commensurable `ϖ` it therefore descends to a rational-valued additive valuation
`PseudoUniformizer.ratAddValuation`, the unique additive valuation with values in `WithTop ℚ`
whose real values are the logarithmic gauge. It takes the value one at `ϖ` and recovers the norm
by `‖x‖ = ‖ϖ‖ ^ v_ϖ(x)`, equivalently `-log ‖x‖ = (-log ‖ϖ‖) v_ϖ(x)`. The normalisation is the
explicit datum `ϖ` together with a proof of commensurability; nothing is installed as an instance.

When the nonzero norms are the integer powers of `‖ϖ‖`, as for a discretely valued field and a
uniformiser `ϖ`, commensurability holds with `n = 1` and the valuation takes integer values. In
particular, for a discrete valuation ring `O` mapping to `R` inside the closed unit ball and an
irreducible `π ∈ O` with `‖π‖ = ‖ϖ‖`, the rational valuation restricts on `O` to Mathlib's
normalised valuation `IsDiscreteValuationRing.addVal O`.

## Main definitions

* `TauCeti.NormedRing.PseudoUniformizer.IsCommensurable`: every nonzero norm has a positive
  power equal to an integer power of `‖ϖ‖`.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation`: for a multiplicative ultrametric norm
  and a commensurable `ϖ`, the additive valuation `R → WithTop ℚ` normalised by `v(ϖ) = 1`.

## Main results

* `TauCeti.NormedRing.PseudoUniformizer.isCommensurable_iff_exists_logGauge_eq`:
  commensurability means that the logarithmic gauge is rational on elements of nonzero norm.
* `TauCeti.NormedRing.PseudoUniformizer.map_ratAddValuation` and
  `TauCeti.NormedRing.PseudoUniformizer.eq_ratAddValuation_iff`: the real values of the rational
  valuation are the logarithmic gauge, and this characterises it.
* `TauCeti.NormedRing.PseudoUniformizer.isCommensurable_iff_exists_addValuation`: a
  rational-valued refinement of the logarithmic gauge exists exactly for commensurable `ϖ`.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation_eq_div`: a witness
  `‖x‖ ^ n = ‖ϖ‖ ^ m` gives `v_ϖ(x) = m / n`.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation_eq_coe_iff`,
  `TauCeti.NormedRing.PseudoUniformizer.norm_eq_rpow_ratAddValuation` and
  `TauCeti.NormedRing.PseudoUniformizer.neg_log_norm_eq_mul_ratAddValuation`: norm recovery.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation_map_eq_addVal`: comparison with the
  normalised valuation of a discrete valuation ring.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §§3–4.
-/

public section

namespace TauCeti.NormedRing.PseudoUniformizer

variable {R : Type*} [SeminormedRing R] (ϖ : PseudoUniformizer R)

/-- A multiplicative pseudo-uniformiser `ϖ` is **commensurable** when every nonzero norm is
commensurable with `‖ϖ‖`: for each `x` with `‖x‖ ≠ 0` there are `m : ℤ` and `n : ℕ`, `n ≠ 0`,
with `‖x‖ ^ n = ‖ϖ‖ ^ m`. -/
def IsCommensurable : Prop :=
  ∀ x : R, ‖x‖ ≠ 0 → ∃ m : ℤ, ∃ n : ℕ, n ≠ 0 ∧ ‖x‖ ^ n = ‖(ϖ.unit : R)‖ ^ m

variable {ϖ} {x y : R}

/-- Unfolding commensurability: every element of nonzero norm has a witness
`‖x‖ ^ n = ‖ϖ‖ ^ m` with `m : ℤ` and `n : ℕ`, `n ≠ 0`. -/
theorem isCommensurable_iff :
    ϖ.IsCommensurable ↔
      ∀ x : R, ‖x‖ ≠ 0 → ∃ m : ℤ, ∃ n : ℕ, n ≠ 0 ∧ ‖x‖ ^ n = ‖(ϖ.unit : R)‖ ^ m :=
  Iff.rfl

/-- A commensurability witness `‖x‖ ^ n = ‖ϖ‖ ^ m` gives the rational value `m / n` of the
logarithmic gauge. -/
theorem logGauge_eq_ratCast_div {m : ℤ} {n : ℕ} (hn : n ≠ 0)
    (h : ‖x‖ ^ n = ‖(ϖ.unit : R)‖ ^ m) :
    ϖ.logGauge x = (((m / n : ℚ) : ℝ) : WithTop ℝ) := by
  rw [logGauge_eq_coe_iff, ← Real.pow_rpow_inv_natCast (norm_nonneg x) hn, h,
    ← Real.rpow_intCast, ← Real.rpow_mul ϖ.norm_pos.le, Rat.cast_div, Rat.cast_intCast,
    Rat.cast_natCast, div_eq_mul_inv]

/-- **Commensurability is rationality of the logarithmic gauge**: `ϖ` is commensurable exactly
when the logarithmic gauge takes a rational value at every element of nonzero norm. -/
theorem isCommensurable_iff_exists_logGauge_eq :
    ϖ.IsCommensurable ↔ ∀ x : R, ‖x‖ ≠ 0 → ∃ q : ℚ, ϖ.logGauge x = ((q : ℝ) : WithTop ℝ) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨m, n, hn, hmn⟩ := h x hx
    exact ⟨m / n, logGauge_eq_ratCast_div hn hmn⟩
  · obtain ⟨q, hq⟩ := h x hx
    refine ⟨q.num, q.den, q.den_ne_zero, ?_⟩
    rw [logGauge_eq_coe_iff.1 hq, ← Real.rpow_natCast, ← Real.rpow_mul ϖ.norm_pos.le,
      ← Real.rpow_intCast]
    congr 1
    exact_mod_cast q.mul_den_eq_num

/-- If every nonzero norm is an integer power of `‖ϖ‖`, as for a uniformiser of a discretely
valued field, then `ϖ` is commensurable. -/
theorem isCommensurable_of_forall_norm_eq_zpow
    (h : ∀ x : R, ‖x‖ ≠ 0 → ∃ m : ℤ, ‖x‖ = ‖(ϖ.unit : R)‖ ^ m) : ϖ.IsCommensurable := by
  intro x hx
  obtain ⟨m, hm⟩ := h x hx
  exact ⟨m, 1, one_ne_zero, by rw [pow_one, hm]⟩

section Valuation

variable (hϖ : ϖ.IsCommensurable)

/-- The coercion `WithTop ℚ → WithTop ℝ` is injective. -/
private theorem map_ratCast_injective : Function.Injective (WithTop.map ((↑) : ℚ → ℝ)) :=
  WithTop.map_injective Rat.cast_injective

/-- The coercion `WithTop ℚ → WithTop ℝ` preserves and reflects the order. -/
private theorem map_ratCast_le_map_ratCast {a b : WithTop ℚ} :
    a.map ((↑) : ℚ → ℝ) ≤ b.map (↑) ↔ a ≤ b :=
  WithTop.map_le_iff _ Rat.cast_le

include hϖ in
/-- For a commensurable `ϖ`, every value of the logarithmic gauge is the image of a value in
`WithTop ℚ`. -/
private theorem exists_map_eq_logGauge (x : R) :
    ∃ q : WithTop ℚ, q.map ((↑) : ℚ → ℝ) = ϖ.logGauge x := by
  by_cases hx : ‖x‖ = 0
  · exact ⟨⊤, by rw [WithTop.map_top, logGauge_of_norm_eq_zero hx]⟩
  · obtain ⟨q, hq⟩ := isCommensurable_iff_exists_logGauge_eq.1 hϖ x hx
    exact ⟨q, by rw [WithTop.map_coe, hq]⟩

/-- The rational lift of the logarithmic gauge, before it is bundled as an additive valuation. -/
private noncomputable def ratLogGauge (x : R) : WithTop ℚ :=
  (exists_map_eq_logGauge hϖ x).choose

private theorem map_ratLogGauge (x : R) :
    (ratLogGauge hϖ x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x :=
  (exists_map_eq_logGauge hϖ x).choose_spec

private theorem ratLogGauge_zero : ratLogGauge hϖ 0 = ⊤ :=
  map_ratCast_injective (by rw [map_ratLogGauge, logGauge_zero, WithTop.map_top])

private theorem ratLogGauge_one : ratLogGauge hϖ 1 = 0 :=
  map_ratCast_injective (by simp [map_ratLogGauge])

variable [IsUltrametricDist R]

private theorem min_ratLogGauge_le_add (x y : R) :
    min (ratLogGauge hϖ x) (ratLogGauge hϖ y) ≤ ratLogGauge hϖ (x + y) := by
  rw [min_le_iff, ← map_ratCast_le_map_ratCast, ← map_ratCast_le_map_ratCast, map_ratLogGauge,
    map_ratLogGauge, map_ratLogGauge, ← min_le_iff]
  exact ϖ.min_le_logGauge_add x y

variable [NormMulClass R]

omit [IsUltrametricDist R] in
private theorem ratLogGauge_mul (x y : R) :
    ratLogGauge hϖ (x * y) = ratLogGauge hϖ x + ratLogGauge hϖ y :=
  map_ratCast_injective (by
    rw [map_ratLogGauge, logGauge_mul, ← map_ratLogGauge hϖ x, ← map_ratLogGauge hϖ y]
    exact (WithTop.map_add (Rat.castHom ℝ) _ _).symm)

/-- For a multiplicative ultrametric norm and a commensurable pseudo-uniformiser `ϖ`, the
**rational valuation** normalised at `ϖ`: the additive valuation with values in `WithTop ℚ`
whose real values are the logarithmic gauge `v_ϖ(x) = log ‖x‖ / log ‖ϖ‖`. -/
noncomputable def ratAddValuation : AddValuation R (WithTop ℚ) :=
  AddValuation.of (ratLogGauge hϖ) (ratLogGauge_zero hϖ) (ratLogGauge_one hϖ)
    (min_ratLogGauge_le_add hϖ) (ratLogGauge_mul hϖ)

/-- **Compatibility of rational and real values**: the rational valuation, viewed in
`WithTop ℝ`, is the logarithmic gauge. -/
@[simp]
theorem map_ratAddValuation (x : R) :
    (ϖ.ratAddValuation hϖ x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x := by
  rw [ratAddValuation, AddValuation.of_apply, map_ratLogGauge]

/-- **Uniqueness**: the rational valuation is the only additive valuation with values in
`WithTop ℚ` whose real values are the logarithmic gauge. -/
theorem eq_ratAddValuation_iff {v : AddValuation R (WithTop ℚ)} :
    v = ϖ.ratAddValuation hϖ ↔ ∀ x, (v x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x := by
  refine ⟨fun h x ↦ h ▸ map_ratAddValuation hϖ x, fun h ↦ AddValuation.ext fun x ↦ ?_⟩
  exact map_ratCast_injective (by rw [h, map_ratAddValuation])

omit hϖ in
/-- A rational-valued additive valuation refining the logarithmic gauge exists exactly when `ϖ`
is commensurable. -/
theorem isCommensurable_iff_exists_addValuation :
    ϖ.IsCommensurable ↔
      ∃ v : AddValuation R (WithTop ℚ), ∀ x, (v x).map ((↑) : ℚ → ℝ) = ϖ.logGauge x := by
  refine ⟨fun hϖ ↦ ⟨_, map_ratAddValuation hϖ⟩, fun ⟨v, hv⟩ ↦ ?_⟩
  refine isCommensurable_iff_exists_logGauge_eq.2 fun x hx ↦ ?_
  have hne : v x ≠ ⊤ := fun h ↦ hx (logGauge_eq_top_iff.1 (by rw [← hv, h, WithTop.map_top]))
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
  exact ⟨q, by rw [← hv, ← hq, WithTop.map_coe]⟩

/-- The rational valuation is infinite exactly on the elements of norm zero. -/
@[simp]
theorem ratAddValuation_eq_top_iff : ϖ.ratAddValuation hϖ x = ⊤ ↔ ‖x‖ = 0 := by
  rw [← map_ratCast_injective.eq_iff, map_ratAddValuation, WithTop.map_top, logGauge_eq_top_iff]

/-- **Norm recovery**: the rational valuation takes the finite value `q` exactly when
`‖x‖ = ‖ϖ‖ ^ q`. -/
theorem ratAddValuation_eq_coe_iff {q : ℚ} :
    ϖ.ratAddValuation hϖ x = q ↔ ‖x‖ = ‖(ϖ.unit : R)‖ ^ (q : ℝ) := by
  rw [← map_ratCast_injective.eq_iff, map_ratAddValuation, WithTop.map_coe, logGauge_eq_coe_iff]

/-- **The rational valuation reverses the order of the norm.** -/
theorem ratAddValuation_le_ratAddValuation_iff :
    ϖ.ratAddValuation hϖ x ≤ ϖ.ratAddValuation hϖ y ↔ ‖y‖ ≤ ‖x‖ := by
  rw [← map_ratCast_le_map_ratCast, map_ratAddValuation, map_ratAddValuation,
    logGauge_le_logGauge_iff]

/-- The rational valuation strictly reverses the order of the norm. -/
theorem ratAddValuation_lt_ratAddValuation_iff :
    ϖ.ratAddValuation hϖ x < ϖ.ratAddValuation hϖ y ↔ ‖y‖ < ‖x‖ := by
  rw [lt_iff_not_ge, ratAddValuation_le_ratAddValuation_iff, not_le]

/-- The rational valuation is nonnegative exactly on the closed unit ball. -/
theorem ratAddValuation_nonneg_iff : 0 ≤ ϖ.ratAddValuation hϖ x ↔ ‖x‖ ≤ 1 := by
  rw [← (ϖ.ratAddValuation hϖ).map_one, ratAddValuation_le_ratAddValuation_iff, ϖ.norm_one]

/-- The rational valuation is positive exactly on the open unit ball. -/
theorem ratAddValuation_pos_iff : 0 < ϖ.ratAddValuation hϖ x ↔ ‖x‖ < 1 := by
  rw [← (ϖ.ratAddValuation hϖ).map_one, ratAddValuation_lt_ratAddValuation_iff, ϖ.norm_one]

/-- A commensurability witness `‖x‖ ^ n = ‖ϖ‖ ^ m` gives the rational valuation `m / n`. -/
theorem ratAddValuation_eq_div {m : ℤ} {n : ℕ} (hn : n ≠ 0)
    (h : ‖x‖ ^ n = ‖(ϖ.unit : R)‖ ^ m) :
    ϖ.ratAddValuation hϖ x = ((m / n : ℚ) : WithTop ℚ) :=
  (ratAddValuation_eq_coe_iff hϖ).2 (logGauge_eq_coe_iff.1 (logGauge_eq_ratCast_div hn h))

/-- An element whose norm is the integer power `‖ϖ‖ ^ m` has rational valuation `m`. -/
theorem ratAddValuation_eq_intCast {m : ℤ} (h : ‖x‖ = ‖(ϖ.unit : R)‖ ^ m) :
    ϖ.ratAddValuation hϖ x = ((m : ℚ) : WithTop ℚ) := by
  rw [ratAddValuation_eq_coe_iff, h, Rat.cast_intCast, Real.rpow_intCast]

/-- The rational valuation of `ϖ ^ n` is `n`, for `n ∈ ℤ`. -/
@[simp]
theorem ratAddValuation_zpow (n : ℤ) :
    ϖ.ratAddValuation hϖ ((ϖ.unit ^ n : Rˣ) : R) = ((n : ℚ) : WithTop ℚ) :=
  map_ratCast_injective (by rw [map_ratAddValuation, logGauge_zpow, WithTop.map_coe,
    Rat.cast_intCast])

/-- The rational valuation of `ϖ ^ n` is `n`, for `n ∈ ℕ`. -/
theorem ratAddValuation_unit_pow (n : ℕ) :
    ϖ.ratAddValuation hϖ ((ϖ.unit : R) ^ n) = ((n : ℚ) : WithTop ℚ) := by
  simpa using ratAddValuation_zpow hϖ n

/-- The rational valuation of `ϖ` is one. -/
@[simp]
theorem ratAddValuation_unit : ϖ.ratAddValuation hϖ (ϖ.unit : R) = 1 := by
  simpa using ratAddValuation_zpow hϖ 1

/-- An element of nonzero norm has norm `‖ϖ‖ ^ v_ϖ(x)`, for its rational valuation `v_ϖ(x)`. -/
theorem norm_eq_rpow_ratAddValuation (hx : ‖x‖ ≠ 0) :
    ‖x‖ = ‖(ϖ.unit : R)‖ ^
      ((((ϖ.ratAddValuation hϖ x).untop ((ratAddValuation_eq_top_iff hϖ).not.2 hx)) : ℚ) : ℝ) :=
  (ratAddValuation_eq_coe_iff hϖ).1 (WithTop.coe_untop _ _).symm

/-- **The logarithmic form of norm recovery**: `-log ‖x‖ = (-log ‖ϖ‖) v_ϖ(x)` for an element of
nonzero norm. -/
theorem neg_log_norm_eq_mul_ratAddValuation (hx : ‖x‖ ≠ 0) :
    -Real.log ‖x‖ = -Real.log ‖(ϖ.unit : R)‖ *
      ((((ϖ.ratAddValuation hϖ x).untop ((ratAddValuation_eq_top_iff hϖ).not.2 hx)) : ℚ) : ℝ) := by
  conv_lhs => rw [norm_eq_rpow_ratAddValuation hϖ hx, Real.log_rpow ϖ.norm_pos]
  ring

/-- **Comparison with a discrete valuation ring.** Let `O` be a discrete valuation ring and
`φ : O →+* R` a ring homomorphism into the closed unit ball, mapping an irreducible `π` to an
element of norm `‖ϖ‖`, as for the valuation ring of a discretely valued field and a uniformiser
`ϖ = π`. Then the rational valuation restricts on `O` to the normalised valuation
`IsDiscreteValuationRing.addVal O`, with its values in `ℕ∞` read in `WithTop ℚ`. -/
theorem ratAddValuation_map_eq_addVal {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (φ : O →+* R) (hφ : ∀ a, ‖φ a‖ ≤ 1) {π : O} (hπ : Irreducible π)
    (hπϖ : ‖φ π‖ = ‖(ϖ.unit : R)‖) (a : O) :
    ϖ.ratAddValuation hϖ (φ a) =
      ENat.map ((↑) : ℕ → ℚ) (IsDiscreteValuationRing.addVal O a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  have := ϖ.normOneClass
  have h : ‖φ (u * π ^ n)‖ = ‖(ϖ.unit : R)‖ ^ (n : ℤ) := by
    rw [map_mul, map_pow, _root_.norm_mul, _root_.norm_pow,
      norm_map_eq_one_of_isUnit hφ u.isUnit, hπϖ, one_mul, zpow_natCast]
  rw [ratAddValuation_eq_intCast hϖ h, IsDiscreteValuationRing.addVal_def' u hπ n,
    ENat.map_natCast, Int.cast_natCast]

end Valuation

end TauCeti.NormedRing.PseudoUniformizer
