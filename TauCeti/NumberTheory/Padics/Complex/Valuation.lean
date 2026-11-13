/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Complex
public import TauCeti.Analysis.Normed.Ring.LogGauge.Rational
import TauCeti.Analysis.Normed.Ring.Commensurable
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Commensurable
import TauCeti.NumberTheory.Padics.Complex.Basic
import TauCeti.NumberTheory.Padics.LogGauge

/-!
# The rational valuation on `ℂ_p`

Every nonzero norm of the algebraic closure `PadicAlgCl p` of `ℚ_[p]` is a rational power of `p`,
because the norm of an algebraic element is a root of the norm of an element of `ℚ_[p]`. Every
nonzero norm of its completion `ℂ_[p]` is a norm of `PadicAlgCl p`, because in an ultrametric
field a sufficiently close approximation of a nonzero element has the same norm. So the norm of
`ℂ_[p]` is commensurable with `p`, and `ℂ_[p]` carries the rational-valued additive valuation
`PadicComplex.addValuation p`, normalised by `v(p) = 1` and recovering the norm through
`‖x‖ = p ^ (-v(x))`.

On `ℚ_[p]` it restricts to Mathlib's `Padic.addValuation`. Since `ℂ_[p]` is algebraically closed,
every rational number is a value: a root `x` of `x ^ n = p ^ m` with `n > 0` has `v(x) = m / n`.
For example a cube root of `p` has valuation `1 / 3`. Consequently every rational power of `p` is
attained as a norm on `ℂ_[p]` (and hence on `PadicAlgCl p`), making both `ℂ_[p]` and `PadicAlgCl p`
densely normed fields.

## Main definitions

* `PadicComplex.pseudoUniformizer`: the multiplicative pseudo-uniformiser `p` of `ℂ_[p]`.
* `PadicComplex.addValuation`: the additive valuation on `ℂ_[p]` with values in `WithTop ℚ`,
  normalised by `v(p) = 1`.
* `PadicComplex.denselyNormedField`, `PadicAlgCl.denselyNormedField`: `ℂ_[p]` and `PadicAlgCl p`
  are densely normed fields.

## Main results

* `PadicAlgCl.isCommensurable`, `PadicComplex.isCommensurable`: the norms of `PadicAlgCl p` and
  `ℂ_[p]` are commensurable with every multiplicative pseudo-uniformiser.
* `PadicComplex.addValuation_eq_coe_iff`: norm recovery, `v(x) = q ↔ ‖x‖ = p ^ (-q)`, and
  `PadicComplex.eq_addValuation`: uniqueness of the rational valuation with this property.
* `PadicComplex.addValuation_algebraMap`: on `ℚ_[p]` the valuation is `Padic.addValuation`.
* `PadicComplex.addValuation_eq_of_pow_eq_zpow`: a root of `x ^ n = p ^ m` has valuation `m / n`.
* `PadicComplex.addValuation_surjective`: every rational number is a value.
* `PadicComplex.exists_norm_eq_rpow`, `PadicAlgCl.exists_norm_eq_rpow`: every rational power of `p`
  is attained as a norm on `ℂ_[p]` and on `PadicAlgCl p`.

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

/-- Every rational power of `p` is attained as a norm on `ℂ_[p]`. -/
theorem exists_norm_eq_rpow (q : ℚ) : ∃ x : ℂ_[p], ‖x‖ = (p : ℝ) ^ (q : ℝ) := by
  obtain ⟨x, hx⟩ := addValuation_surjective (p := p) (-q : ℚ)
  exact ⟨x, by simpa using addValuation_eq_coe_iff.mp hx⟩

variable (p) in
/-- **`ℂ_[p]` is densely normed**: since `PadicComplex.addValuation p` is surjective onto
`WithTop ℚ`, the rational powers of `p` are norms on `ℂ_[p]`, so its positive norms are dense in
`(0, ∞)`. -/
noncomputable instance denselyNormedField : DenselyNormedField ℂ_[p] where
  lt_norm_lt := by
    intro _ _ hr₁ hr
    exact PseudoUniformizer.exists_lt_norm_lt_of_surjective_ratAddValuation (isCommensurable p _)
      (addValuation_def p ▸ addValuation_surjective) hr₁ hr

-- Ensure that `DenselyNormedField` induces the existing normed and nontrivially normed field
-- instances on `ℂ_[p]`.
example : (inferInstance : NormedField ℂ_[p]) = PadicComplex.normedField p := by
  with_reducible_and_instances rfl

example :
    (inferInstance : NontriviallyNormedField ℂ_[p]) = PadicComplex.nontriviallyNormedField p := by
  with_reducible_and_instances rfl

end PadicComplex

namespace PadicAlgCl

variable {p}

/-- Every rational power of `p` is attained as a norm on `PadicAlgCl p`: an `n`-th root of
`p ^ (-m)` has norm `p ^ (m / n)`. -/
theorem exists_norm_eq_rpow (q : ℚ) : ∃ x : PadicAlgCl p, ‖x‖ = (p : ℝ) ^ (q : ℝ) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.2 (Fact.out : p.Prime).pos
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((p : PadicAlgCl p) ^ (-q.num)) q.pos
  refine ⟨x, ?_⟩
  have hpow : ‖x‖ ^ q.den = ((p : ℝ) ^ (q : ℝ)) ^ q.den := by
    rw [← norm_pow, hx, norm_zpow, ← PadicComplex.norm_extends p, PadicComplex.coe_natCast,
      PadicComplex.norm_p, inv_zpow, zpow_neg, inv_inv, ← Real.rpow_intCast,
      ← Real.rpow_natCast ((p : ℝ) ^ (q : ℝ)), ← Real.rpow_mul hp.le]
    exact congrArg _ (mod_cast (Rat.mul_den_eq_num q).symm)
  exact (pow_left_inj₀ (norm_nonneg x) (Real.rpow_nonneg hp.le _) q.pos.ne').mp hpow

variable (p) in
/-- **`PadicAlgCl p` is densely normed**: every rational power of `p` is attained as a norm. -/
noncomputable instance denselyNormedField : DenselyNormedField (PadicAlgCl p) where
  lt_norm_lt := by
    intro _ _ hr₁ hr
    let ϖ : PseudoUniformizer (PadicAlgCl p) :=
      PseudoUniformizer.ofAlgebraMap (K := ℚ_[p])
        (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) Padic.norm_p_lt_one
    refine PseudoUniformizer.exists_lt_norm_lt_of_forall_exists_norm_eq_rpow ϖ (fun q ↦ ?_) hr₁ hr
    obtain ⟨x, hx⟩ := exists_norm_eq_rpow (p := p) (-q)
    refine ⟨x, hx.trans ?_⟩
    have hp_norm : ‖(ϖ.unit : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
      simp [ϖ, ← PadicComplex.norm_extends p]
    rw [hp_norm, Real.inv_rpow (Nat.cast_nonneg p), Rat.cast_neg,
      Real.rpow_neg (Nat.cast_nonneg p)]

-- Ensure that `DenselyNormedField` induces the existing nontrivially normed field instance on
-- `PadicAlgCl p`.
example :
    (inferInstance : NontriviallyNormedField (PadicAlgCl p)) =
      PadicAlgCl.nontriviallyNormedField p := by
  with_reducible_and_instances rfl

end PadicAlgCl

