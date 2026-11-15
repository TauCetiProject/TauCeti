/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.Analysis.Normed.Ring.LogGauge.Rational
public import TauCeti.NumberTheory.Padics.LogGauge
public import TauCeti.RingTheory.Valuation.Spectral
import TauCeti.Analysis.Normed.Ring.Commensurable
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Commensurable
import TauCeti.NumberTheory.Padics.Complex.Basic

/-!
# The rational and real valuations on `ℂ_p`

Every nonzero norm of the algebraic closure `PadicAlgCl p` of `ℚ_[p]` is a rational power of `p`,
because the norm of an algebraic element is a root of the norm of an element of `ℚ_[p]`. Every
nonzero norm of its completion `ℂ_[p]` is a norm of `PadicAlgCl p`, because in an ultrametric
field a sufficiently close approximation of a nonzero element has the same norm. So the norm of
`ℂ_[p]` is commensurable with `p`, and `ℂ_[p]` carries both the rational-valued additive valuation
`PadicComplex.addValuation p` (with values in `WithTop ℚ`) and the real-valued additive valuation
`PadicComplex.realValuation p` (with values in `WithTop ℝ`), both normalised by `v(p) = 1` and
recovering the norm through `‖x‖ = p ^ (-v(x))`.

`PadicComplex.realValuation p` agrees with `PadicComplex.addValuation p` cast to `ℝ`, equals
`AddValuation.ofNorm (p : ℝ) _` on `ℂ_[p]`, restricts on `ℚ_[p]` to `TauCeti.padicRealValuation p`,
and restricts on `PadicAlgCl p` to `TauCeti.spectralAddValuation ℚ_[p] (PadicAlgCl p) p _`.
Changing from base `p` to base `Real.exp 1` scales finite values by `Real.log p`.
Since `ℂ_[p]` is algebraically closed, every rational number is a value: a root `x` of
`x ^ n = p ^ m` with `n > 0` has `v(x) = m / n`. For example a cube root of `p` has valuation
`1 / 3`.

## Main definitions

* `PadicComplex.pseudoUniformizer`: the multiplicative pseudo-uniformiser `p` of `ℂ_[p]`.
* `PadicComplex.addValuation`: the additive valuation on `ℂ_[p]` with values in `WithTop ℚ`,
  normalised by `v(p) = 1`.
* `PadicComplex.realValuation`: the real additive valuation on `ℂ_[p]` with values in `WithTop ℝ`,
  normalised by `v(p) = 1`.

## Main results

* `PadicAlgCl.isCommensurable`, `PadicComplex.isCommensurable`: the norms of `PadicAlgCl p` and
  `ℂ_[p]` are commensurable with every multiplicative pseudo-uniformiser.
* `PadicComplex.addValuation_eq_coe_iff` and `PadicComplex.realValuation_eq_coe_iff`: norm
  recovery, `v(x) = t ↔ ‖x‖ = p ^ (-t)`, together with uniqueness
  (`PadicComplex.eq_addValuation`, `PadicComplex.eq_realValuation`).
* `PadicComplex.realValuation_eq_map_addValuation`, `PadicComplex.realValuation_eq_ofNorm`,
  `PadicComplex.realValuation_algebraMap`, and `PadicComplex.realValuation_coe`: compatibility
  between rational, real, `ℚ_[p]`, and `PadicAlgCl p` valuations.
* `PadicComplex.addValuation_eq_of_pow_eq_zpow`, `PadicComplex.realValuation_eq_of_pow_eq_zpow`,
  `PadicComplex.addValuation_surjective`, and `PadicComplex.exists_rat_realValuation`: values at
  roots of `x ^ n = p ^ m` and rationality of finite values.
* `PadicComplex.ofNorm_exp_one_eq_map_realValuation`: base change from `p` to `Real.exp 1` scales
  values by `Real.log p`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., Graduate Texts in
  Mathematics 58, Springer, 1984, Chapter III, §§3–4.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3.
-/

public section

open TauCeti.NormedRing

variable (p : ℕ) [Fact p.Prime]

/-- The norm of the algebraic closure `PadicAlgCl p` of `ℚ_[p]` is commensurable with every
multiplicative pseudo-uniformiser: its nonzero norms are rational powers of `p`. -/
theorem PadicAlgCl.isCommensurable (ϖ : PseudoUniformizer (PadicAlgCl p)) : ϖ.IsCommensurable :=
  PseudoUniformizer.isCommensurable_of_isAlgebraic
    (PseudoUniformizer.isCommensurable_padic (TauCeti.padicPseudoUniformizer p)) ϖ

namespace PadicComplex

/-- The norm of `ℂ_[p]` is commensurable with every multiplicative pseudo-uniformiser: its nonzero
norms are rational powers of `p`. -/
theorem isCommensurable (ϖ : PseudoUniformizer ℂ_[p]) : ϖ.IsCommensurable :=
  PseudoUniformizer.isCommensurable_of_denseRange
    (PadicAlgCl.isCommensurable p (PseudoUniformizer.ofAlgebraMap (K := ℚ_[p])
      (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) Padic.norm_p_lt_one))
    (norm_extends p) UniformSpace.Completion.denseRange_coe ϖ

/-- The multiplicative pseudo-uniformiser `p` of `ℂ_[p]`, of norm `p⁻¹`. -/
noncomputable def pseudoUniformizer : PseudoUniformizer ℂ_[p] :=
  PseudoUniformizer.ofAlgebraMap (K := ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    Padic.norm_p_lt_one

/-- The underlying element of `PadicComplex.pseudoUniformizer p` is `p`. -/
@[simp]
theorem coe_unit_pseudoUniformizer : ((pseudoUniformizer p).unit : ℂ_[p]) = p := by
  simp [pseudoUniformizer]

/-- The additive valuation on `ℂ_[p]` with values in `WithTop ℚ`, normalised by `v(p) = 1`. It
recovers the norm through `‖x‖ = p ^ (-v(x))` (`PadicComplex.addValuation_eq_coe_iff`). -/
noncomputable def addValuation : AddValuation ℂ_[p] (WithTop ℚ) :=
  (pseudoUniformizer p).ratAddValuation (isCommensurable p _)

/-- `PadicComplex.addValuation p` is the rational valuation of the pseudo-uniformiser `p`, so the
general API of `TauCeti.NormedRing.PseudoUniformizer.ratAddValuation` applies to it. -/
theorem addValuation_def :
    addValuation p = (pseudoUniformizer p).ratAddValuation (isCommensurable p _) := by
  rw [addValuation]

variable {p}

/-- `‖p‖ ^ q = p ^ (-q)` in `ℂ_[p]`, for real `q`. -/
private theorem norm_unit_pseudoUniformizer_rpow (q : ℝ) :
    ‖((pseudoUniformizer p).unit : ℂ_[p])‖ ^ q = (p : ℝ) ^ (-q) := by
  rw [coe_unit_pseudoUniformizer, norm_p, Real.inv_rpow (Nat.cast_nonneg p),
    Real.rpow_neg (Nat.cast_nonneg p)]

/-- **Norm recovery**: `v(x) = q` exactly when `‖x‖ = p ^ (-q)`. -/
theorem addValuation_eq_coe_iff {x : ℂ_[p]} {q : ℚ} :
    addValuation p x = q ↔ ‖x‖ = (p : ℝ) ^ (-(q : ℝ)) := by
  rw [addValuation_def, PseudoUniformizer.ratAddValuation_eq_coe_iff,
    norm_unit_pseudoUniformizer_rpow]

/-- **Uniqueness**: a rational-valued additive valuation `w` on `ℂ_[p]` recovering the norm through
`‖x‖ = p ^ (-w(x))` is `PadicComplex.addValuation p`. -/
theorem eq_addValuation {w : AddValuation ℂ_[p] (WithTop ℚ)}
    (hw : ∀ (x : ℂ_[p]) (q : ℚ), w x = q ↔ ‖x‖ = (p : ℝ) ^ (-(q : ℝ))) :
    w = addValuation p := by
  rw [addValuation_def]
  exact PseudoUniformizer.eq_ratAddValuation _ fun x q ↦ by
    rw [hw, norm_unit_pseudoUniformizer_rpow]

/-- The valuation reverses the order of the norm. -/
theorem addValuation_le_addValuation_iff {x y : ℂ_[p]} :
    addValuation p x ≤ addValuation p y ↔ ‖y‖ ≤ ‖x‖ := by
  rw [addValuation_def]
  exact PseudoUniformizer.ratAddValuation_le_ratAddValuation_iff _

/-- The valuation of `p` is one. -/
@[simp]
theorem addValuation_p : addValuation p (p : ℂ_[p]) = 1 := by
  rw [← coe_unit_pseudoUniformizer p, addValuation_def]
  exact PseudoUniformizer.ratAddValuation_unit _

/-- **Compatibility with `ℚ_[p]`**: on `ℚ_[p]` the valuation is the `p`-adic valuation
`Padic.addValuation`, with its integer values viewed as rationals. -/
@[simp]
theorem addValuation_algebraMap (x : ℚ_[p]) :
    addValuation p (algebraMap ℚ_[p] ℂ_[p] x) = (Padic.addValuation x).map ((↑) : ℤ → ℚ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [Padic.addValuation.apply hx, WithTop.map_coe, addValuation_eq_coe_iff, norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation hx, Rat.cast_intCast, ← Real.rpow_intCast, Int.cast_neg]

/-- **Roots of powers of `p`**: if `x ^ n = p ^ m` with `n > 0`, then `v(x) = m / n`. -/
theorem addValuation_eq_of_pow_eq_zpow {x : ℂ_[p]} {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : x ^ n = (p : ℂ_[p]) ^ m) : addValuation p x = ((m / n : ℚ) : WithTop ℚ) := by
  rw [addValuation_def]
  exact PseudoUniformizer.ratAddValuation_eq_of_norm_pow_eq _ hn <| by
    rw [← norm_pow, h, norm_zpow, coe_unit_pseudoUniformizer]

/-- **The value group is `ℚ`**: every element of `WithTop ℚ` is a value of the valuation. -/
theorem addValuation_surjective : Function.Surjective (addValuation p) := by
  intro v
  induction v using WithTop.recTopCoe with
  | top => exact ⟨0, (addValuation p).map_zero⟩
  | coe q =>
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((p : ℂ_[p]) ^ q.num) q.pos
    exact ⟨x, by rw [addValuation_eq_of_pow_eq_zpow q.pos hx, Rat.num_div_den]⟩

variable (p) in
/-- The real additive valuation on `ℂ_[p]` with values in `WithTop ℝ`, normalised by `v(p) = 1`.
It agrees with `PadicComplex.addValuation p` cast to `ℝ` and recovers the norm through
`‖x‖ = p ^ (-v(x))`. -/
noncomputable def realValuation : AddValuation ℂ_[p] (WithTop ℝ) :=
  (pseudoUniformizer p).addValuation

variable (p) in
/-- `PadicComplex.realValuation p` is the real additive valuation of the pseudo-uniformiser `p`. -/
theorem realValuation_def : realValuation p = (pseudoUniformizer p).addValuation :=
  (rfl)

/-- **Norm recovery**: `realValuation p x = t` if and only if `‖x‖ = p ^ (-t)`. -/
theorem realValuation_eq_coe_iff {x : ℂ_[p]} {t : ℝ} :
    realValuation p x = t ↔ ‖x‖ = (p : ℝ) ^ (-t) := by
  rw [realValuation_def, PseudoUniformizer.addValuation_apply,
    PseudoUniformizer.logGauge_eq_coe_iff, norm_unit_pseudoUniformizer_rpow]

/-- Every nonzero `x : ℂ_[p]` has norm `p ^ (-(realValuation p x).untop₀)`. -/
theorem norm_eq_rpow_neg_realValuation {x : ℂ_[p]} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(realValuation p x).untop₀) :=
  realValuation_eq_coe_iff.1
    (WithTop.coe_untop₀_of_ne_top ((realValuation p).ne_top_iff.2 hx)).symm

/-- `PadicComplex.realValuation p` equals `AddValuation.ofNorm` at base `p`. -/
theorem realValuation_eq_ofNorm :
    realValuation p = AddValuation.ofNorm (p : ℝ) (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt) :=
  AddValuation.eq_ofNorm_of_norm_eq_rpow (realValuation p) _ fun _ ↦
    norm_eq_rpow_neg_realValuation

/-- **Uniqueness**: any real additive valuation on `ℂ_[p]` recovering the norm at base `p` equals
`PadicComplex.realValuation p`. -/
theorem eq_realValuation {w : AddValuation ℂ_[p] (WithTop ℝ)}
    (hw : ∀ x ≠ 0, ‖x‖ = (p : ℝ) ^ (-(w x).untop₀)) : w = realValuation p :=
  (realValuation p).eq_of_norm_eq_rpow w (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ norm_eq_rpow_neg_realValuation) hw

/-- `PadicComplex.realValuation p` agrees with `PadicComplex.addValuation p` after casting rational
values to `ℝ`. -/
theorem realValuation_eq_map_addValuation (x : ℂ_[p]) :
    realValuation p x = (addValuation p x).map ((↑) : ℚ → ℝ) := by
  rw [realValuation_def, addValuation_def, PseudoUniformizer.addValuation_apply,
    PseudoUniformizer.map_ratAddValuation]

/-- `WithTop.untop₀` of `PadicComplex.realValuation p` is the real cast of
`(PadicComplex.addValuation p x).untop₀` for every `x`, including `0`. -/
@[simp]
theorem untop₀_realValuation (x : ℂ_[p]) :
    (realValuation p x).untop₀ = ((addValuation p x).untop₀ : ℝ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have htop : addValuation p x ≠ ⊤ := (addValuation p).ne_top_iff.2 hx
  rw [realValuation_eq_map_addValuation, ← WithTop.coe_untop₀_of_ne_top htop,
    WithTop.map_coe, WithTop.untop₀_coe, WithTop.untop₀_coe]

/-- `PadicComplex.realValuation p` reverses the order of the norm. -/
theorem realValuation_le_realValuation_iff {x y : ℂ_[p]} :
    realValuation p x ≤ realValuation p y ↔ ‖y‖ ≤ ‖x‖ := by
  simp only [realValuation_def, PseudoUniformizer.addValuation_apply,
    PseudoUniformizer.logGauge_le_logGauge_iff]

/-- `realValuation p x` is at least `t` if and only if `‖x‖ ≤ p ^ (-t)`. -/
theorem coe_le_realValuation_iff {x : ℂ_[p]} {t : ℝ} :
    (t : WithTop ℝ) ≤ realValuation p x ↔ ‖x‖ ≤ (p : ℝ) ^ (-t) := by
  rw [realValuation_def, PseudoUniformizer.addValuation_apply,
    PseudoUniformizer.coe_le_logGauge_iff, norm_unit_pseudoUniformizer_rpow]

/-- `realValuation p x` exceeds `t` if and only if `‖x‖ < p ^ (-t)`. -/
theorem coe_lt_realValuation_iff {x : ℂ_[p]} {t : ℝ} :
    (t : WithTop ℝ) < realValuation p x ↔ ‖x‖ < (p : ℝ) ^ (-t) := by
  rw [realValuation_def, PseudoUniformizer.addValuation_apply,
    PseudoUniformizer.coe_lt_logGauge_iff, norm_unit_pseudoUniformizer_rpow]

/-- The real valuation of `p` in `ℂ_[p]` is `1`. -/
@[simp]
theorem realValuation_p : realValuation p (p : ℂ_[p]) = 1 := by
  rw [realValuation_eq_map_addValuation, addValuation_p, ← WithTop.coe_one, WithTop.map_coe,
    Rat.cast_one, WithTop.coe_one]

/-- On `ℚ_[p]`, `PadicComplex.realValuation p` restricts to `TauCeti.padicRealValuation p`. -/
@[simp]
theorem realValuation_algebraMap (x : ℚ_[p]) :
    realValuation p (algebraMap ℚ_[p] ℂ_[p] x) = TauCeti.padicRealValuation p x := by
  rw [realValuation_eq_map_addValuation, addValuation_algebraMap,
    TauCeti.padicRealValuation_eq_map, WithTop.map_map]
  simp only [Function.comp_def, Rat.cast_intCast]

/-- Pulling `PadicComplex.realValuation p` back to `ℚ_[p]` gives `TauCeti.padicRealValuation p`. -/
@[simp]
theorem comap_realValuation :
    (realValuation p).comap (algebraMap ℚ_[p] ℂ_[p]) = TauCeti.padicRealValuation p :=
  AddValuation.ext realValuation_algebraMap

/-- On the algebraic closure `PadicAlgCl p`, `PadicComplex.realValuation p` agrees with the
canonical spectral additive valuation `TauCeti.spectralAddValuation` at base `p`. -/
@[simp]
theorem realValuation_coe (x : PadicAlgCl p) :
    realValuation p (x : ℂ_[p]) =
      TauCeti.spectralAddValuation ℚ_[p] (PadicAlgCl p) (p : ℝ)
        (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt) x := by
  rw [realValuation_eq_ofNorm, TauCeti.spectralAddValuation_eq_ofNorm]
  exact AddValuation.ofNorm_eq_of_norm_eq _ (norm_extends p x)

/-- Every nonzero element of `ℂ_[p]` has rational real valuation. -/
theorem exists_rat_realValuation {x : ℂ_[p]} (hx : x ≠ 0) :
    ∃ q : ℚ, realValuation p x = ((q : ℝ) : WithTop ℝ) := by
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 ((addValuation p).ne_top_iff.2 hx)
  exact ⟨q, by rw [realValuation_eq_map_addValuation, ← hq, WithTop.map_coe]⟩

/-- If `x ^ n = p ^ m` in `ℂ_[p]` with `n > 0`, then `realValuation p x = m / n`. -/
theorem realValuation_eq_of_pow_eq_zpow {x : ℂ_[p]} {m : ℤ} {n : ℕ} (hn : 0 < n)
    (h : x ^ n = (p : ℂ_[p]) ^ m) : realValuation p x = ((m / n : ℝ) : WithTop ℝ) := by
  rw [realValuation_eq_map_addValuation, addValuation_eq_of_pow_eq_zpow hn h, WithTop.map_coe,
    WithTop.coe_eq_coe]
  push_cast
  ring

/-- Changing from base `p` (`PadicComplex.realValuation p`) to base `Real.exp 1`
(`-Real.log ‖x‖`) multiplies finite valuation values by `Real.log p`. -/
theorem ofNorm_exp_one_eq_map_realValuation (x : ℂ_[p]) :
    AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one) x =
      (realValuation p x).map (Real.log p * ·) := by
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  rw [realValuation_eq_ofNorm,
    AddValuation.ofNorm_eq_map_ofNorm hp (Real.one_lt_exp_iff.2 zero_lt_one)]
  simp [Real.log_exp]

end PadicComplex
