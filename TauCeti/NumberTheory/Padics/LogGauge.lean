/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.Analysis.Normed.Ring.LogGauge.Rational

/-!
# The logarithmic gauge on `ℚ_[p]`

On the `p`-adic field the norm is multiplicative and ultrametric with `‖p‖ = p⁻¹`. For a
multiplicative pseudo-uniformiser `ϖ` of norm `p⁻¹`, for instance `p` itself through
`TauCeti.padicPseudoUniformizer` (`TauCeti.NormedRing.PseudoUniformizer.ofAlgebraMap` and
`Padic.norm_p_lt_one`), the logarithmic gauge `v_ϖ(x) = log ‖x‖ / log ‖ϖ‖` is the `p`-adic
valuation: it agrees with Mathlib's integer-valued `Padic.addValuation` after viewing its integer
values as reals. Thus `TauCeti.padicRealValuation p :=
(TauCeti.padicPseudoUniformizer p).addValuation`, with values in `WithTop ℝ`, is the real form of
the `p`-adic valuation normalised by `v(p) = 1`.

Every nonzero norm on `ℚ_[p]` is an integer power of `p`, so the norm is commensurable with every
multiplicative pseudo-uniformiser, and the rational-valued additive valuation of a
pseudo-uniformiser of norm `p⁻¹` is `Padic.addValuation` with its integer values viewed as
rationals.

## Main definitions

* `TauCeti.padicPseudoUniformizer`: the canonical multiplicative pseudo-uniformiser `p` of `ℚ_[p]`,
  of norm `p⁻¹`.
* `TauCeti.padicRealValuation`: the real `p`-adic additive valuation on `ℚ_[p]` normalised by
  `v(p) = 1`.

## Main results

* `TauCeti.NormedRing.PseudoUniformizer.logGauge_eq_map_padicAddValuation` and
  `TauCeti.NormedRing.PseudoUniformizer.addValuation_eq_map_padicAddValuation`: the logarithmic
  gauge and additive valuation of a multiplicative pseudo-uniformiser of norm `p⁻¹` agree with
  `Padic.addValuation` cast to `ℝ`.
* `TauCeti.padicRealValuation_eq_map`, `TauCeti.padicRealValuation_p`,
  `TauCeti.norm_eq_rpow_neg_padicRealValuation`, and `TauCeti.exists_int_padicRealValuation`:
  comparison with `Padic.addValuation`, normalisation at `p`, norm recovery, and integrality on
  nonzero elements.
* `TauCeti.NormedRing.PseudoUniformizer.isCommensurable_padic`: the norm of `ℚ_[p]` is
  commensurable with every multiplicative pseudo-uniformiser.
* `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation_eq_map_padicAddValuation`: the rational
  valuation of a multiplicative pseudo-uniformiser of norm `p⁻¹` is `Padic.addValuation`.
-/

public section

namespace TauCeti.NormedRing.PseudoUniformizer

variable {p : ℕ} [Fact p.Prime]

/-- On `ℚ_[p]`, the logarithmic gauge of a multiplicative pseudo-uniformiser of norm `p⁻¹` is the
`p`-adic additive valuation `Padic.addValuation`, with its integer values viewed as reals. -/
theorem logGauge_eq_map_padicAddValuation (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) (x : ℚ_[p]) :
    ϖ.logGauge x = (Padic.addValuation x).map ((↑) : ℤ → ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hp : (0 : ℝ) < p := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  rw [Padic.addValuation.apply hx, WithTop.map_coe, logGauge_eq_coe_iff, hϖ,
    Padic.norm_eq_zpow_neg_valuation hx, Real.inv_rpow hp.le, ← Real.rpow_neg hp.le,
    ← Real.rpow_intCast, Int.cast_neg]

/-- On `ℚ_[p]`, the additive valuation attached to a multiplicative pseudo-uniformiser of norm
`p⁻¹` is `Padic.addValuation`, with its integer values viewed as reals. -/
theorem addValuation_eq_map_padicAddValuation (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) (x : ℚ_[p]) :
    ϖ.addValuation x = (Padic.addValuation x).map ((↑) : ℤ → ℝ) := by
  rw [addValuation_apply, logGauge_eq_map_padicAddValuation ϖ hϖ]

/-- On `ℚ_[p]`, a nonzero element has norm `‖ϖ‖ ^ v_p(x)` for a multiplicative
pseudo-uniformiser `ϖ` of norm `p⁻¹`. -/
private theorem norm_eq_zpow_valuation (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) {x : ℚ_[p]} (hx : x ≠ 0) :
    ‖x‖ = ‖(ϖ.unit : ℚ_[p])‖ ^ x.valuation := by
  rw [hϖ, Padic.norm_eq_zpow_neg_valuation hx, inv_zpow, zpow_neg]

/-- The norm of `ℚ_[p]` is commensurable with every multiplicative pseudo-uniformiser. -/
theorem isCommensurable_padic (ϖ : PseudoUniformizer ℚ_[p]) : ϖ.IsCommensurable := by
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  let ϖ₀ : PseudoUniformizer ℚ_[p] := ofAlgebraMap hp Padic.norm_p_lt_one
  have hϖ₀ : ‖(ϖ₀.unit : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [coe_unit_ofAlgebraMap, Algebra.algebraMap_self_apply, Padic.norm_p]
  refine (isCommensurable_iff_isCommensurable ϖ₀ ϖ).1
    (isCommensurable_of_forall_exists_zpow fun x hx ↦ ⟨x.valuation, ?_⟩)
  exact norm_eq_zpow_valuation ϖ₀ hϖ₀ (norm_ne_zero_iff.1 hx)

/-- On `ℚ_[p]`, the rational valuation of a multiplicative pseudo-uniformiser of norm `p⁻¹` is
the `p`-adic additive valuation `Padic.addValuation`, with its integer values viewed as
rationals. -/
theorem ratAddValuation_eq_map_padicAddValuation (ϖ : PseudoUniformizer ℚ_[p])
    (hϖ : ‖(ϖ.unit : ℚ_[p])‖ = (p : ℝ)⁻¹) (hc : ϖ.IsCommensurable) (x : ℚ_[p]) :
    ϖ.ratAddValuation hc x = (Padic.addValuation x).map ((↑) : ℤ → ℚ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [Padic.addValuation.apply hx, WithTop.map_coe,
    ratAddValuation_eq_intCast hc (norm_eq_zpow_valuation ϖ hϖ hx)]

end TauCeti.NormedRing.PseudoUniformizer

namespace TauCeti

variable (p : ℕ) [Fact p.Prime]

/-- The canonical multiplicative pseudo-uniformiser `p` of `ℚ_[p]`, of norm `p⁻¹`. -/
noncomputable def padicPseudoUniformizer : NormedRing.PseudoUniformizer ℚ_[p] :=
  NormedRing.PseudoUniformizer.ofAlgebraMap (K := ℚ_[p]) (A := ℚ_[p])
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) Padic.norm_p_lt_one

/-- The real `p`-adic additive valuation on `ℚ_[p]` normalised by `v(p) = 1`. -/
noncomputable def padicRealValuation : AddValuation ℚ_[p] (WithTop ℝ) :=
  (padicPseudoUniformizer p).addValuation

variable {p}

/-- The underlying unit of `padicPseudoUniformizer p` has `p`-adic norm `p⁻¹`. -/
@[simp]
theorem norm_unit_padicPseudoUniformizer :
    ‖((padicPseudoUniformizer p).unit : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  simp [padicPseudoUniformizer, Padic.norm_p]

/-- `padicRealValuation p` agrees with `Padic.addValuation` after casting integer values to `ℝ`. -/
theorem padicRealValuation_eq_map (x : ℚ_[p]) :
    padicRealValuation p x = (Padic.addValuation x).map ((↑) : ℤ → ℝ) :=
  (padicPseudoUniformizer p).addValuation_eq_map_padicAddValuation
    norm_unit_padicPseudoUniformizer x

/-- The uniformiser `p` has valuation `1` under `padicRealValuation p`. -/
@[simp]
theorem padicRealValuation_p : padicRealValuation p (p : ℚ_[p]) = 1 := by
  have h := (padicPseudoUniformizer p).logGauge_unit
  simpa [padicPseudoUniformizer, padicRealValuation] using h

/-- On `ℚ_[p]`, every nonzero element has norm `p ^ (-(padicRealValuation p x).untop₀)`. -/
theorem norm_eq_rpow_neg_padicRealValuation {x : ℚ_[p]} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(padicRealValuation p x).untop₀) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rw [padicRealValuation_eq_map, Padic.addValuation.apply hx, WithTop.map_coe, WithTop.untop₀_coe,
    Padic.norm_eq_zpow_neg_valuation hx, Real.rpow_neg hp0.le, Real.rpow_intCast, zpow_neg]

/-- On `ℚ_[p]`, `padicRealValuation p` takes integer values on nonzero elements. -/
theorem exists_int_padicRealValuation {x : ℚ_[p]} (hx : x ≠ 0) :
    ∃ n : ℤ, padicRealValuation p x = ((n : ℝ) : WithTop ℝ) :=
  ⟨Padic.valuation x, by rw [padicRealValuation_eq_map, Padic.addValuation.apply hx,
    WithTop.map_coe]⟩

end TauCeti
