/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.Calculus.PeriodicDeriv
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# Fourier series of smooth functions on the torus

A function `f` on the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` is read through its lift
`x ↦ f (fun i ↦ (x i : UnitAddCircle))`, a `ℤ^d`-periodic function on `d → ℝ`. This file proves
that differentiating the lift multiplies the Fourier coefficients by the corresponding symbol, and
deduces that the Fourier coefficients of a `C^k` function decay like `‖n‖^(-k)`, with the constant
given by the sup norm of the `k`-th derivative. For `k` larger than the dimension `card d` the
coefficients are therefore absolutely summable, and the Fourier series converges to the function
uniformly, together with its termwise derivatives of order `j` when the lift is `C^(j + k)`.

The derivative formula comes from translation. Translating `f` by `v` multiplies its `n`-th
coefficient by the character `mFourier n v` (`mFourierCoeff_comp_add`). Differentiating this along
the line `t ↦ t • w`, under the integral on the left and explicitly on the right, gives the
coefficient of the directional derivative of `f` along `w`
(`mFourierCoeff_eq_smul_of_hasDerivAt`):

`mFourierCoeff g n = (2πi ∑ i, n i * w i) • mFourierCoeff f n`.

No integration by parts over a fundamental domain is needed. Iterating along the directions
`v 0, …, v (k - 1)` identifies the coefficients of the function whose lift is
`x ↦ iteratedFDeriv ℝ k F x v` (`mFourierCoeff_eq_prod_smul_of_iteratedFDeriv`). Taking all
directions equal to a coordinate vector of maximal `|n i|`, the coefficient bound
`‖mFourierCoeff g n‖ ≤ sup ‖g‖` gives the decay estimate
`(2π ‖n‖) ^ k * ‖mFourierCoeff f n‖ ≤ M` whenever `M` bounds `‖iteratedFDeriv ℝ k F‖`
(`pow_mul_norm_mFourierCoeff_le`). Here `‖n‖` is the sup norm on `d → ℤ`.

The `k`-th derivative of the lift of a mode `mFourier n` is bounded by `(2π ∑ i, |n i|) ^ k`
(`norm_iteratedFDeriv_mFourier_coe_le`). Against the decay estimate this makes the Fourier series
of a `C^K` function differentiable termwise `k` times when `K > card d + k`
(`iteratedFDeriv_eq_tsum_mFourier`), and its partial sums converge to the function in every `C^k`
norm (`tendstoUniformly_iteratedFDeriv_sum_mFourier`).

A smooth function `g` on `d → ℝ` supported in the open unit cube `‖x‖ < 1 / 2` (sup norm) agrees
there with its periodic extension `x ↦ ∑ᶠ m, g (x + m)`, which is the lift of a function on the
torus with smooth lift. Hence `g` is the limit, in every `C^k` norm on the cube, of trigonometric
polynomials `∑ n ∈ s, c n exp (2πi ∑ i, n i x i)`
(`exists_tendstoUniformlyOn_iteratedFDeriv_sum_cexp`). This expands test functions on a compact
coordinate box in Fourier modes, as in the Fourier-series proof that tensor products of test
functions are dense, the uniqueness part of the Schwartz kernel theorem.

## Main results

* `UnitAddTorus.mFourierCoeff_comp_add`: the coefficients of a translate.
* `TauCeti.UnitAddTorus.mFourierCoeff_eq_smul_of_hasDerivAt`: the coefficients of a directional
  derivative.
* `TauCeti.UnitAddTorus.exists_continuous_comp_coe_eq_iteratedFDeriv` and
  `TauCeti.UnitAddTorus.exists_forall_norm_iteratedFDeriv_le`: a continuous iterated derivative of
  the lift descends to a continuous function on the torus, and is bounded.
* `TauCeti.UnitAddTorus.mFourierCoeff_eq_prod_smul_of_iteratedFDeriv`: the coefficients of an
  iterated derivative of a `C^k` function.
* `TauCeti.UnitAddTorus.pow_mul_norm_mFourierCoeff_le`: the decay estimate in terms of a bound for
  the `k`-th derivative.
* `TauCeti.UnitAddTorus.exists_pow_mul_norm_mFourierCoeff_le`: `‖n‖ ^ k * ‖mFourierCoeff f n‖` is
  bounded for a `C^k` function.
* `TauCeti.UnitAddTorus.summable_norm_mFourierCoeff`: the coefficients of a `C^k` function are
  absolutely summable when `k` exceeds the dimension.
* `TauCeti.UnitAddTorus.hasSum_mFourier_series_of_contDiff`: the Fourier series of such a function
  converges to it uniformly.
* `TauCeti.UnitAddTorus.hasSum_mFourier_series_of_iteratedFDeriv`: so do its termwise derivatives.
* `TauCeti.UnitAddTorus.summable_pow_mul_norm_mFourierCoeff`: `∑ n, ‖n‖ ^ j ‖mFourierCoeff f n‖`
  converges for a `C^k` function when `k` exceeds `card d + j`.
* `TauCeti.UnitAddTorus.norm_iteratedFDeriv_mFourier_coe_le`: the derivatives of a mode.
* `TauCeti.UnitAddTorus.iteratedFDeriv_eq_tsum_mFourier`: termwise differentiation of the Fourier
  series in the multilinear norm.
* `TauCeti.UnitAddTorus.tendstoUniformly_iteratedFDeriv_sum_mFourier`: the partial sums of the
  Fourier series converge in every `C^k` norm.
* `TauCeti.UnitAddTorus.exists_tendstoUniformlyOn_iteratedFDeriv_sum_cexp`: a smooth function
  supported in the open unit cube is a `C^k` limit of trigonometric polynomials on the cube, for
  every `k`.

## References

* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 3.2 (decay of the Fourier coefficients of smooth functions on the torus).
-/

public section

noncomputable section

open MeasureTheory Complex Topology Set
open scoped Real ContDiff

namespace TauCeti

namespace UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*}

/-! ### The quotient map `(d → ℝ) → UnitAddTorus d` -/

/-- The quotient map from `d → ℝ` onto the unit torus. -/
private def toTorus (x : d → ℝ) : UnitAddTorus d := fun i ↦ (x i : UnitAddCircle)

private theorem toTorus_apply (x : d → ℝ) (i : d) : toTorus x i = (x i : UnitAddCircle) := rfl

private theorem toTorus_add (x y : d → ℝ) : toTorus (x + y) = toTorus x + toTorus y := by
  ext i
  simp [toTorus_apply]

private theorem toTorus_smul (t : ℝ) (w : d → ℝ) :
    toTorus (t • w) = fun i ↦ ((t * w i : ℝ) : UnitAddCircle) := rfl

end UnitAddTorus

end TauCeti

/-! ### Translation and the Fourier coefficients -/

namespace UnitAddTorus

variable {d : Type*} {E : Type*} [NormedAddCommGroup E] [Fintype d] [NormedSpace ℂ E]

/-- **Fourier coefficients of a translate.** Translating a function by `v` multiplies its `n`-th
Fourier coefficient by `mFourier n v`. -/
theorem mFourierCoeff_comp_add (f : UnitAddTorus d → E) (v : UnitAddTorus d) (n : d → ℤ) :
    mFourierCoeff (fun z ↦ f (z + v)) n = mFourier n v • mFourierCoeff f n := by
  simp only [TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume, ← integral_smul]
  rw [← integral_add_right_eq_self (fun z ↦ mFourier n v • mFourier (-n) z • f z) v]
  congr 1 with z
  rw [smul_smul, mFourier_apply_add, mul_left_comm, ← mFourier_add, add_neg_cancel, mFourier_zero,
    ContinuousMap.one_apply, mul_one]

end UnitAddTorus

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} {E : Type*} [NormedAddCommGroup E] [Fintype d] [NormedSpace ℂ E]

/-- The Fourier coefficients of `f` are bounded by any bound for `f`. -/
theorem norm_mFourierCoeff_le {f : UnitAddTorus d → E} {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (n : d → ℤ) : ‖mFourierCoeff f n‖ ≤ M := by
  rw [mFourierCoeff_eq_integral_volume]
  refine (norm_integral_le_of_norm_le_const (C := M)
    (Filter.Eventually.of_forall fun z ↦ ?_)).trans_eq (by simp)
  rw [norm_smul, norm_mFourier_apply, one_mul]
  exact hM z

/-! ### Derivatives and the Fourier coefficients -/

/-- **Fourier coefficients of a directional derivative.** If `g` is the derivative of `f` along
the direction `w : d → ℝ`, then the `n`-th Fourier coefficient of `g` is that of `f` multiplied by
`2πi ∑ i, n i * w i`. -/
theorem mFourierCoeff_eq_smul_of_hasDerivAt {f g : UnitAddTorus d → E}
    {w : d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ z, HasDerivAt (fun t : ℝ ↦ f (z + fun i ↦ ((t * w i : ℝ) : UnitAddCircle))) (g z) 0)
    (n : d → ℤ) :
    mFourierCoeff g n = (2 * π * I * ∑ i, (n i : ℂ) * w i) • mFourierCoeff f n := by
  set a : ℂ := 2 * π * I * ∑ i, (n i : ℂ) * w i
  set τ : ℝ → UnitAddTorus d := fun t ↦ toTorus (t • w)
  have hτ_add (s t : ℝ) : τ (s + t) = τ s + τ t := by
    simp only [τ, add_smul, toTorus_add]
  -- `toTorus (t • w)` is by definition the point of the torus appearing in `hfg`.
  have hfg' : ∀ z, HasDerivAt (fun t : ℝ ↦ f (z + τ t)) (g z) 0 := hfg
  -- The coefficients of the translates `f (· + τ t)` are `exp (a t)` times those of `f`.
  have hexp (t : ℝ) : mFourierCoeff (fun z ↦ f (z + τ t)) n = cexp (a * t) • mFourierCoeff f n := by
    rw [mFourierCoeff_comp_add, show mFourier n (τ t) = _ from mFourier_coe_apply n (t • w)]
    congr 2
    simp only [a, Pi.smul_apply, smul_eq_mul, ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1 with i
    ring
  have hderiv₁ : HasDerivAt (fun t : ℝ ↦ mFourierCoeff (fun z ↦ f (z + τ t)) n)
      (a • mFourierCoeff f n) 0 := by
    simp only [hexp]
    convert (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul a).cexp).smul_const
      (mFourierCoeff f n) using 1 <;> simp
  -- Differentiating under the integral sign gives the coefficients of `g`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ z, ‖g z‖ ≤ C :=
    ⟨‖(⟨g, hg⟩ : C(UnitAddTorus d, E))‖, fun z ↦ (ContinuousMap.mk g hg).norm_coe_le_norm z⟩
  have hdiff (z : UnitAddTorus d) (t : ℝ) :
      HasDerivAt (fun s : ℝ ↦ f (z + τ s)) (g (z + τ t)) t := by
    have h := HasDerivAt.comp_sub_const t t (f := fun s ↦ f (z + τ t + τ s))
      (by rw [sub_self]; exact hfg' (z + τ t))
    refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ ?_)
    simp only [add_assoc, ← hτ_add, add_sub_cancel]
  have hderiv₂ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (t : ℝ) (z : UnitAddTorus d) ↦ mFourier (-n) z • f (z + τ t))
    (F' := fun (t : ℝ) (z : UnitAddTorus d) ↦ mFourier (-n) z • g (z + τ t))
    (bound := fun _ ↦ C) (x₀ := 0) Filter.univ_mem
    (Filter.Eventually.of_forall fun t ↦ (by fun_prop : Continuous fun z ↦
      mFourier (-n) z • f (z + τ t)).aestronglyMeasurable)
    ((by fun_prop : Continuous fun z ↦
      mFourier (-n) z • f (z + τ 0)).integrable_of_hasCompactSupport (.of_compactSpace _))
    ((by fun_prop : Continuous fun z ↦ mFourier (-n) z • g (z + τ 0)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z t _ ↦ by
      rw [norm_smul, norm_mFourier_apply, one_mul]
      exact hC _)
    (integrable_const C)
    (Filter.Eventually.of_forall fun z t _ ↦ (hdiff z t).const_smul (mFourier (-n) z))
  have h := hderiv₂.2
  simp only [← mFourierCoeff_eq_integral_volume] at h
  have hτ0 : τ 0 = 0 := by simp [τ, toTorus_apply, funext_iff]
  simp only [hτ0, add_zero] at h
  exact h.unique hderiv₁

/-! ### Iterated derivatives -/

section Lift

variable (f : UnitAddTorus d → E)

/-- If the `j`-th derivative of the lift of a function `f` on the torus is continuous, then its
values on fixed directions `v` descend to a continuous function on the torus. -/
theorem exists_continuous_comp_coe_eq_iteratedFDeriv {j : ℕ}
    (hc : Continuous (iteratedFDeriv ℝ j fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)))
    (v : Fin j → d → ℝ) :
    ∃ g : UnitAddTorus d → E, Continuous g ∧ ∀ x : d → ℝ, g (fun i ↦ (x i : UnitAddCircle)) =
      iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x v :=
  exists_continuous_comp_coe_eq ((continuous_eval_const v).comp hc)
    fun m x ↦ by simp only [((periodic_comp_coe f m).iteratedFDeriv j) x]

/-- If the `j`-th derivative of the lift of a function `f` on the torus is continuous, then it is
bounded. -/
theorem exists_forall_norm_iteratedFDeriv_le {j : ℕ}
    (hc : Continuous (iteratedFDeriv ℝ j fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))) :
    ∃ M, ∀ x, ‖iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M := by
  obtain ⟨g, hg, hgx⟩ :=
    exists_continuous_comp_coe_eq hc fun m ↦ (periodic_comp_coe f m).iteratedFDeriv j
  refine ⟨‖(⟨g, hg⟩ : C(UnitAddTorus d, _))‖, fun x ↦ ?_⟩
  rw [← hgx]
  exact (ContinuousMap.mk g hg).norm_coe_le_norm _

end Lift

/-- **Fourier coefficients of an iterated derivative.** Let `f` be a function on the torus whose
lift `F` to `d → ℝ` is `C^k`, and let `g` be the function on the torus whose lift is the `k`-th
derivative of `F` in the directions `v 0, …, v (k - 1)`. Then the `n`-th Fourier coefficient of
`g` is that of `f` multiplied by `∏ l, 2πi ∑ i, n i * v l i`. -/
theorem mFourierCoeff_eq_prod_smul_of_iteratedFDeriv {f g : UnitAddTorus d → E}
    {k : ℕ} (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))
    (v : Fin k → d → ℝ)
    (hg : ∀ x : d → ℝ, g (fun i ↦ (x i : UnitAddCircle)) =
      iteratedFDeriv ℝ k (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x v)
    (n : d → ℤ) :
    mFourierCoeff g n = (∏ l, 2 * π * I * ∑ i, (n i : ℂ) * v l i) • mFourierCoeff f n := by
  -- Restate the hypotheses through the quotient map `toTorus`, which is by definition the map
  -- `x ↦ fun i ↦ (x i : UnitAddCircle)` appearing in them.
  change ContDiff ℝ k fun x ↦ f (toTorus x) at hf
  change ∀ x, g (toTorus x) = iteratedFDeriv ℝ k (fun x ↦ f (toTorus x)) x v at hg
  induction k generalizing g with
  | zero =>
    obtain rfl : g = f := funext fun z ↦ by
      obtain ⟨x, rfl⟩ : ∃ x, toTorus x = z := surjective_coe z
      rw [hg, iteratedFDeriv_zero_apply]
    simp
  | succ k ih =>
    obtain ⟨g', hg'c, hg'⟩ := exists_continuous_comp_coe_eq_iteratedFDeriv f
      (hf.continuous_iteratedFDeriv (by norm_cast; omega)) (Fin.tail v)
    change ∀ x, g' (toTorus x) = iteratedFDeriv ℝ k (fun x ↦ f (toTorus x)) x (Fin.tail v) at hg'
    have hgc : Continuous g := by
      refine isOpenQuotientMap_coe.isQuotientMap.continuous_iff.2 ?_
      change Continuous fun x ↦ g (toTorus x)
      simpa only [Function.comp_def, hg] using
        (continuous_eval_const v).comp (hf.continuous_iteratedFDeriv le_rfl)
    have hd := hf.differentiable_iteratedFDeriv (m := k) (by norm_cast; omega)
    -- `g` is the derivative of `g'` along `v 0`.
    have hderiv (z : UnitAddTorus d) : HasDerivAt
        (fun t : ℝ ↦ g' (z + fun i ↦ ((t * v 0 i : ℝ) : UnitAddCircle))) (g z) 0 := by
      obtain ⟨x, rfl⟩ : ∃ x, toTorus x = z := surjective_coe z
      have hline := ((hd x).hasFDerivAt.hasLineDerivAt (v 0) :)
      have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ d → ℝ) E
        (Fin.tail v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
      rw [hg, iteratedFDeriv_succ_apply_left]
      refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t ↦ ?_)
      simp only [Function.comp_apply, ContinuousMultilinearMap.apply_apply, ← hg']
      rw [← toTorus_smul, ← toTorus_add]
    rw [mFourierCoeff_eq_smul_of_hasDerivAt hg'c hgc hderiv,
      ih (hf := hf.of_le (by norm_cast; omega)) (v := Fin.tail v) (hg := hg'), smul_smul,
      Fin.prod_univ_succ]
    simp only [Fin.tail]

/-! ### Decay of the Fourier coefficients -/

/-- **Decay of the Fourier coefficients of a `C^k` function on the torus.** If the lift of `f` to
`d → ℝ` is `C^k` and its `k`-th derivative is bounded by `M`, then
`(2π ‖n‖) ^ k * ‖mFourierCoeff f n‖ ≤ M`, where `‖n‖` is the sup norm of `n : d → ℤ`. -/
theorem pow_mul_norm_mFourierCoeff_le {f : UnitAddTorus d → E} {k : ℕ}
    (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x‖ ≤ M)
    (n : d → ℤ) : (2 * π * ‖n‖) ^ k * ‖mFourierCoeff f n‖ ≤ M := by
  classical
  -- Restate the hypotheses through the quotient map `toTorus`, which is by definition the map
  -- `x ↦ fun i ↦ (x i : UnitAddCircle)` appearing in them.
  change ContDiff ℝ k fun x ↦ f (toTorus x) at hf
  change ∀ x, ‖iteratedFDeriv ℝ k (fun x ↦ f (toTorus x)) x‖ ≤ M at hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rcases isEmpty_or_nonempty d with hd | hd
  · -- In dimension zero the torus is a point and `n = 0`.
    have hn : ‖n‖ = 0 := by simp [Subsingleton.elim n 0]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine (one_mul _).trans_le (norm_mFourierCoeff_le (fun z ↦ ?_) n)
      obtain ⟨x, rfl⟩ : ∃ x, toTorus x = z := surjective_coe z
      simpa [norm_iteratedFDeriv_zero] using hM x
    · simpa [hn, zero_pow hk.ne'] using hM0
  -- Differentiate `k` times along a coordinate direction `i` with `|n i| = ‖n‖`.
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun i ↦ ‖n i‖₊
  have hni : ‖n‖ = |(n i : ℝ)| := by
    rw [← coe_nnnorm, Pi.nnnorm_def, hi, coe_nnnorm, Int.norm_eq_abs]
  obtain ⟨g, -, hg⟩ := exists_continuous_comp_coe_eq_iteratedFDeriv f
    (hf.continuous_iteratedFDeriv le_rfl) fun _ ↦ Pi.single i 1
  change ∀ x, g (toTorus x) = iteratedFDeriv ℝ k (fun x ↦ f (toTorus x)) x
    fun _ ↦ Pi.single i 1 at hg
  have hcoeff := mFourierCoeff_eq_prod_smul_of_iteratedFDeriv hf _ hg n
  have hsum : ∑ j, (n j : ℂ) * (((Pi.single i 1 : d → ℝ) j : ℝ) : ℂ) = n i := by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp
  rw [hsum, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcoeff
  have hgM : ∀ z, ‖g z‖ ≤ M := fun z ↦ by
    obtain ⟨x, rfl⟩ : ∃ x, toTorus x = z := surjective_coe z
    rw [hg]
    refine ((iteratedFDeriv ℝ k (fun x ↦ f (toTorus x)) x).le_opNorm
      fun _ ↦ Pi.single i 1).trans ?_
    simpa [Pi.norm_single] using hM x
  have h := norm_mFourierCoeff_le hgM n
  rw [hcoeff, norm_smul, norm_pow] at h
  convert h using 2
  simp [hni, abs_of_pos Real.pi_pos]

/-- If the lift of `f` to `d → ℝ` is `C^k`, then `‖n‖ ^ k * ‖mFourierCoeff f n‖` is bounded. -/
theorem exists_pow_mul_norm_mFourierCoeff_le {f : UnitAddTorus d → E} {k : ℕ}
    (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    ∃ C, ∀ n : d → ℤ, ‖n‖ ^ k * ‖mFourierCoeff f n‖ ≤ C := by
  obtain ⟨M, hM⟩ := exists_forall_norm_iteratedFDeriv_le f (hf.continuous_iteratedFDeriv le_rfl)
  refine ⟨M / (2 * π) ^ k, fun n ↦ ?_⟩
  rw [le_div_iff₀ (by positivity), mul_right_comm, ← mul_pow, mul_comm _ (2 * π)]
  exact pow_mul_norm_mFourierCoeff_le hf hM n

/-- If the lift of `f` to `d → ℝ` is `C^k` for some `k` exceeding `card d + j`, then
`∑ n, ‖n‖ ^ j * ‖mFourierCoeff f n‖ < ∞`. -/
theorem summable_pow_mul_norm_mFourierCoeff {f : UnitAddTorus d → E} {j k : ℕ}
    (hk : Fintype.card d + j < k)
    (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    Summable fun n ↦ ‖n‖ ^ j * ‖mFourierCoeff f n‖ := by
  obtain ⟨C, hC⟩ := exists_pow_mul_norm_mFourierCoeff_le hf
  refine Summable.of_norm_bounded_eventually ((summable_pi_int_norm_rpow ((j : ℝ) - k) (by
    have := (Nat.cast_lt (α := ℝ)).2 hk
    push_cast at this
    linarith)).mul_left C) ?_
  filter_upwards [(Set.finite_singleton (0 : d → ℤ)).compl_mem_cofinite] with n hn
  have hpos : 0 < ‖n‖ := norm_pos_iff.2 hn
  rw [norm_mul, norm_pow, norm_norm, norm_norm, Real.rpow_sub hpos, Real.rpow_natCast,
    Real.rpow_natCast, mul_div_assoc', le_div_iff₀ (by positivity)]
  calc ‖n‖ ^ j * ‖mFourierCoeff f n‖ * ‖n‖ ^ k = ‖n‖ ^ j * (‖n‖ ^ k * ‖mFourierCoeff f n‖) := by
        ring
    _ ≤ ‖n‖ ^ j * C := mul_le_mul_of_nonneg_left (hC n) (by positivity)
    _ = C * ‖n‖ ^ j := mul_comm _ _

/-- **Absolute convergence of the Fourier coefficients.** If the lift of `f` to `d → ℝ` is `C^k`
for some `k` exceeding the dimension `d`, then `∑ n, ‖mFourierCoeff f n‖ < ∞`. -/
theorem summable_norm_mFourierCoeff {f : UnitAddTorus d → E} {k : ℕ}
    (hk : Fintype.card d < k)
    (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    Summable fun n ↦ ‖mFourierCoeff f n‖ := by
  simpa using summable_pow_mul_norm_mFourierCoeff (j := 0) (by omega) hf

/-- **Uniform convergence of the Fourier series.** If the lift of a continuous function `f` on the
torus to `d → ℝ` is `C^k` for some `k` exceeding the dimension `d`, then its Fourier series
converges to `f` absolutely and uniformly. -/
theorem hasSum_mFourier_series_of_contDiff {f : C(UnitAddTorus d, ℂ)} {k : ℕ}
    (hk : Fintype.card d < k)
    (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    HasSum (fun n ↦ mFourierCoeff f n • mFourier n) f :=
  hasSum_mFourier_series_of_summable (summable_norm_mFourierCoeff hk hf).of_norm

/-- **Termwise differentiation of the Fourier series.** If the lift `F` of a continuous function
`f` on the torus is `C^(j + k)` for some `k` exceeding the dimension `d`, then the Fourier series
differentiated termwise `j` times in the directions `v 0, …, v (j - 1)` converges absolutely and
uniformly to the function `g` on the torus whose lift is the corresponding derivative of `F`. -/
theorem hasSum_mFourier_series_of_iteratedFDeriv {f g : C(UnitAddTorus d, ℂ)} {j k : ℕ}
    (hk : Fintype.card d < k)
    (hf : ContDiff ℝ (j + k) fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))
    (v : Fin j → d → ℝ)
    (hg : ∀ x : d → ℝ, g (fun i ↦ (x i : UnitAddCircle)) =
      iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x v) :
    HasSum (fun n ↦ ((∏ l, 2 * π * I * ∑ i, (n i : ℂ) * v l i) * mFourierCoeff f n) •
      mFourier n) g := by
  have hgk : ContDiff ℝ k fun x : d → ℝ ↦ g fun i ↦ (x i : UnitAddCircle) := by
    simp only [hg]
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ d → ℝ) ℂ v).contDiff.comp
      (hf.iteratedFDeriv_right (by norm_cast; omega))
  simpa only [mFourierCoeff_eq_prod_smul_of_iteratedFDeriv (hf.of_le (by norm_cast; omega)) v hg,
    smul_eq_mul] using hasSum_mFourier_series_of_contDiff hk hgk


/-! ### Convergence of the Fourier series in every `C^k` norm -/

/-- The lift of the Fourier mode `mFourier n` to `d → ℝ` is smooth. -/
theorem contDiff_mFourier_coe (n : d → ℤ) :
    ContDiff ℝ ∞ fun y : d → ℝ ↦ mFourier n fun i ↦ (y i : UnitAddCircle) := by
  have h : ContDiff ℝ ∞ fun t : ℝ ↦ (t : ℂ) := Complex.ofRealCLM.contDiff
  simp only [mFourier_coe_apply]
  fun_prop

/-- The lift of the Fourier mode `mFourier n` has `k`-th derivative bounded by
`(2π ∑ i, |n i|) ^ k`. -/
theorem norm_iteratedFDeriv_mFourier_coe_le (n : d → ℤ) (k : ℕ) (x : d → ℝ) :
    ‖iteratedFDeriv ℝ k (fun y : d → ℝ ↦ mFourier n fun i ↦ (y i : UnitAddCircle)) x‖ ≤
      (2 * π * ∑ i, |(n i : ℝ)|) ^ k := by
  -- The mode is `exp` composed with the real-linear map `y ↦ (∑ i, n i * y i) • 2πi`.
  set L : (d → ℝ) →L[ℝ] ℝ := ∑ i, (n i : ℝ) • ContinuousLinearMap.proj i
  have hLapply (y : d → ℝ) : L y = ∑ i, (n i : ℝ) * y i := by
    simp [L]
  have hL : ‖L‖ ≤ ∑ i, |(n i : ℝ)| := by
    refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) fun y ↦ ?_
    rw [hLapply, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (abs_nonneg _)
  set L' : (d → ℝ) →L[ℝ] ℂ := L.smulRight (2 * π * I)
  have heq : (fun y : d → ℝ ↦ mFourier n fun i ↦ (y i : UnitAddCircle)) = cexp ∘ L' := by
    funext y
    simp only [mFourier_coe_apply, Function.comp_apply, L', ContinuousLinearMap.smulRight_apply,
      hLapply, Complex.real_smul]
    push_cast
    ring_nf
  have hnorm : ‖L'‖ ≤ 2 * π * ∑ i, |(n i : ℝ)| := by
    rw [ContinuousLinearMap.norm_smulRight_apply, mul_comm]
    have h2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by
      simp [abs_of_pos Real.pi_pos]
    rw [h2π]
    exact mul_le_mul_of_nonneg_left hL (by positivity)
  rw [heq]
  refine (L'.norm_iteratedFDeriv_comp_right_le Complex.contDiff_exp x
    (mod_cast le_top)).trans ?_
  -- `L' x` is purely imaginary, so every derivative of `exp` there has norm one.
  have hre : (L' x).re = 0 := by
    simp [L', ContinuousLinearMap.smulRight_apply]
  rw [norm_iteratedFDeriv_real_cexp, Complex.norm_exp, hre, Real.exp_zero, one_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm k

/-- A multiple `c • mFourier n` of a Fourier mode, read on `d → ℝ`, has `j`-th derivative bounded
by `‖c‖ (2π card d) ^ j ‖n‖ ^ j`, where `‖n‖` is the sup norm. -/
private theorem norm_iteratedFDeriv_smul_mFourier_coe_le (c : ℂ) (n : d → ℤ) (j : ℕ)
    (x : d → ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : d → ℝ ↦ c • mFourier n fun i ↦ (y i : UnitAddCircle)) x‖ ≤
      ‖c‖ * (2 * π * Fintype.card d) ^ j * ‖n‖ ^ j := by
  have hsum_abs : ∑ i, |(n i : ℝ)| ≤ Fintype.card d * ‖n‖ := by
    calc ∑ i, |(n i : ℝ)| ≤ ∑ _i : d, ‖n‖ := Finset.sum_le_sum fun i _ ↦ by
          simpa [Int.norm_eq_abs] using norm_le_pi_norm n i
      _ = Fintype.card d * ‖n‖ := by simp
  rw [iteratedFDeriv_const_smul_apply' ((contDiff_mFourier_coe n).contDiffAt.of_le
    (mod_cast le_top : (j : WithTop ℕ∞) ≤ (⊤ : ℕ∞))), norm_smul, mul_assoc, ← mul_pow,
    mul_assoc (2 * π)]
  refine mul_le_mul_of_nonneg_left ((norm_iteratedFDeriv_mFourier_coe_le n j x).trans ?_)
    (norm_nonneg _)
  exact pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left hsum_abs (by positivity)) j

/-- **Termwise differentiation of the Fourier series.** If the lift of `f` to `d → ℝ` is `C^K` for
some `K` exceeding `card d + k`, then its `k`-th derivative is the sum of the `k`-th derivatives
of the terms `mFourierCoeff f n • mFourier n` of its Fourier series. -/
theorem iteratedFDeriv_eq_tsum_mFourier {f : UnitAddTorus d → ℂ} {k K : ℕ}
    (hK : Fintype.card d + k < K)
    (hf : ContDiff ℝ K fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) (x : d → ℝ) :
    iteratedFDeriv ℝ k (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) x =
      ∑' n, iteratedFDeriv ℝ k
        (fun y : d → ℝ ↦ mFourierCoeff f n • mFourier n fun i ↦ (y i : UnitAddCircle)) x := by
  have hfc : Continuous f := isOpenQuotientMap_coe.isQuotientMap.continuous_iff.2 hf.continuous
  have hlift : (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) =
      fun x ↦ ∑' n, mFourierCoeff f n • mFourier n fun i ↦ (x i : UnitAddCircle) := by
    funext x
    have h := (hasSum_mFourier_series_of_contDiff (f := ⟨f, hfc⟩) (by omega) hf).map
      (ContinuousMap.evalCLM ℂ fun i ↦ (x i : UnitAddCircle))
      (ContinuousMap.evalCLM ℂ _).continuous
    exact h.tsum_eq.symm
  rw [hlift]
  refine congrFun (iteratedFDeriv_tsum (N := k)
    (fun n ↦ ((contDiff_mFourier_coe n).const_smul _).of_le (mod_cast le_top))
    (fun j hj ↦ ?_) (fun j n x _ ↦ norm_iteratedFDeriv_smul_mFourier_coe_le _ n j x) le_rfl) x
  refine ((summable_pow_mul_norm_mFourierCoeff (j := j) (by norm_cast at hj; omega) hf).mul_left
    ((2 * π * Fintype.card d) ^ j)).congr fun n ↦ ?_
  ring

/-- **Convergence of the Fourier series in `C^k`.** If the lift of `f` to `d → ℝ` is `C^K` for
some `K` exceeding `card d + k`, then the `k`-th derivatives of the partial sums
`∑ n ∈ s, mFourierCoeff f n • mFourier n` of its Fourier series, read on `d → ℝ`, converge
uniformly to the `k`-th derivative of the lift as the finite set `s` of frequencies grows. -/
theorem tendstoUniformly_iteratedFDeriv_sum_mFourier {f : UnitAddTorus d → ℂ} {k K : ℕ}
    (hK : Fintype.card d + k < K)
    (hf : ContDiff ℝ K fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    TendstoUniformly
      (fun (s : Finset (d → ℤ)) (x : d → ℝ) ↦ iteratedFDeriv ℝ k
        (fun y : d → ℝ ↦ ∑ n ∈ s, mFourierCoeff f n • mFourier n fun i ↦ (y i : UnitAddCircle)) x)
      (iteratedFDeriv ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) Filter.atTop := by
  classical
  set e : (d → ℤ) → (d → ℝ) → ℂ :=
    fun n y ↦ mFourierCoeff f n • mFourier n fun i ↦ (y i : UnitAddCircle)
  -- A summable majorant of the `k`-th derivatives of the terms.
  set v : (d → ℤ) → ℝ := fun n ↦ ‖mFourierCoeff f n‖ * (2 * π * Fintype.card d) ^ k * ‖n‖ ^ k
  have hbound (n : d → ℤ) (x : d → ℝ) : ‖iteratedFDeriv ℝ k (e n) x‖ ≤ v n :=
    norm_iteratedFDeriv_smul_mFourier_coe_le _ n k x
  have hv : Summable v :=
    ((summable_pow_mul_norm_mFourierCoeff (j := k) (by omega) hf).mul_left
      ((2 * π * Fintype.card d) ^ k)).congr fun n ↦ by ring
  have hpartial (s : Finset (d → ℤ)) (x : d → ℝ) :
      iteratedFDeriv ℝ k (fun y ↦ ∑ n ∈ s, e n y) x = ∑ n ∈ s, iteratedFDeriv ℝ k (e n) x :=
    (congrFun (iteratedFDeriv_sum fun n _ ↦ ((contDiff_mFourier_coe n).const_smul _).of_le
      (mod_cast le_top : (k : WithTop ℕ∞) ≤ (⊤ : ℕ∞))) x).trans (Finset.sum_apply _ _ _)
  rw [funext (iteratedFDeriv_eq_tsum_mFourier hK hf)]
  convert tendstoUniformly_tsum hv hbound using 1
  exact funext fun s ↦ funext (hpartial s)

/-! ### Trigonometric approximation on the open unit cube -/

/-- The periodic extension `x ↦ ∑ᶠ m, g (x + m)` of a function `g` on `d → ℝ`. -/
private def periodize (g : (d → ℝ) → ℂ) (x : d → ℝ) : ℂ :=
  ∑ᶠ m : d → ℤ, g (x + fun i ↦ (m i : ℝ))

variable {g : (d → ℝ) → ℂ}

/-- Near any point, only finitely many integer translates of a function supported in the open
unit cube are nonzero. -/
private theorem exists_finset_periodize_eq (hg : Function.support g ⊆ Metric.ball 0 (1 / 2))
    (x₀ : d → ℝ) : ∃ T : Finset (d → ℤ), ∀ x ∈ Metric.ball x₀ (1 / 2),
      periodize g x = ∑ m ∈ T, g (x + fun i ↦ (m i : ℝ)) := by
  classical
  set N : ℤ := ⌈‖x₀‖⌉ + 1 with hN
  refine ⟨Fintype.piFinset fun _ ↦ Finset.Icc (-N) N, fun x hx ↦ ?_⟩
  refine finsum_eq_sum_of_support_subset _ fun m hm ↦ ?_
  have hball := hg hm
  rw [mem_ball_zero_iff] at hball
  rw [Metric.mem_ball, dist_eq_norm] at hx
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have h1 : |x i + m i| < 1 / 2 := by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm (x + fun i ↦ (m i : ℝ)) i).trans_lt hball
  have h2 : |x i| < ‖x₀‖ + 1 / 2 := by
    have := norm_le_pi_norm x i
    have := norm_sub_norm_le x x₀
    rw [Real.norm_eq_abs] at *
    linarith
  have h3 : ‖x₀‖ ≤ (⌈‖x₀‖⌉ : ℝ) := Int.le_ceil _
  have h4 : |(m i : ℝ)| < N := by
    have : |(m i : ℝ)| ≤ |x i + m i| + |x i| := by
      calc |(m i : ℝ)| = |(x i + m i) - x i| := by ring_nf
        _ ≤ |x i + m i| + |x i| := abs_sub _ _
    rw [hN]
    push_cast
    linarith
  rw [abs_lt] at h4
  exact ⟨by exact_mod_cast h4.1.le, by exact_mod_cast h4.2.le⟩

/-- The periodic extension of a smooth function supported in the open unit cube is smooth. -/
private theorem contDiff_periodize (hg : Function.support g ⊆ Metric.ball 0 (1 / 2))
    (hg' : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (periodize g) := by
  refine contDiff_iff_contDiffAt.2 fun x₀ ↦ ?_
  obtain ⟨T, hT⟩ := exists_finset_periodize_eq hg x₀
  have hsum : ContDiff ℝ ∞ fun x ↦ ∑ m ∈ T, g (x + fun i ↦ (m i : ℝ)) :=
    ContDiff.sum fun m _ ↦ hg'.comp (contDiff_id.add contDiff_const)
  exact hsum.contDiffAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem (Metric.ball_mem_nhds x₀ (by norm_num)) hT)

omit [Fintype d] in
/-- The periodic extension has every integer vector as a period. -/
private theorem periodize_add (x : d → ℝ) (n : d → ℤ) :
    periodize g (x + fun i ↦ (n i : ℝ)) = periodize g x := by
  unfold periodize
  calc ∑ᶠ m : d → ℤ, g (x + (fun i ↦ (n i : ℝ)) + fun i ↦ (m i : ℝ))
      = ∑ᶠ m : d → ℤ, (fun m' : d → ℤ ↦ g (x + fun i ↦ (m' i : ℝ))) (Equiv.addLeft n m) :=
        finsum_congr fun m ↦ congrArg g <| by
          ext i
          simp only [Pi.add_apply, Equiv.coe_addLeft, Int.cast_add]
          ring
    _ = ∑ᶠ m : d → ℤ, g (x + fun i ↦ (m i : ℝ)) :=
        finsum_comp_equiv (Equiv.addLeft n) (f := fun m' : d → ℤ ↦ g (x + fun i ↦ (m' i : ℝ)))

/-- On the open unit cube, the periodic extension of a function supported there is the function
itself. -/
private theorem periodize_eq_of_mem_ball (hg : Function.support g ⊆ Metric.ball 0 (1 / 2))
    {x : d → ℝ} (hx : x ∈ Metric.ball (0 : d → ℝ) (1 / 2)) : periodize g x = g x := by
  unfold periodize
  rw [finsum_eq_single _ 0 fun m hm ↦ ?_]
  · congr 1
    ext i
    simp
  · refine Function.notMem_support.1 fun hmem ↦ ?_
    have hball := hg hmem
    rw [mem_ball_zero_iff] at hball hx
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Function.ne_iff.1 hm
    have h1 : |x i + m i| < 1 / 2 := by
      simpa [Real.norm_eq_abs] using (norm_le_pi_norm (x + fun i ↦ (m i : ℝ)) i).trans_lt hball
    have h2 : |x i| < 1 / 2 := by
      simpa [Real.norm_eq_abs] using (norm_le_pi_norm x i).trans_lt hx
    have h3 : (1 : ℝ) ≤ |(m i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
    have : |(m i : ℝ)| ≤ |x i + m i| + |x i| := by
      calc |(m i : ℝ)| = |(x i + m i) - x i| := by ring_nf
        _ ≤ |x i + m i| + |x i| := abs_sub _ _
    linarith

/-- **Trigonometric approximation in `C^∞` on the open unit cube.** A smooth function `g` on
`d → ℝ` supported in the open unit cube `‖x‖ < 1 / 2` (sup norm) is approximated in every `C^k`
norm on that cube by trigonometric polynomials: there are coefficients `c n` (the Fourier
coefficients of the periodic extension of `g`) such that for every `k`, the `k`-th derivatives of
`∑ n ∈ s, c n exp (2πi ∑ i, n i x i)` converge to that of `g`, uniformly on the cube, as the
finite set `s` of frequencies grows. -/
theorem exists_tendstoUniformlyOn_iteratedFDeriv_sum_cexp
    (hg : ContDiff ℝ ∞ g) (hsupp : Function.support g ⊆ Metric.ball 0 (1 / 2)) :
    ∃ c : (d → ℤ) → ℂ, ∀ k : ℕ, TendstoUniformlyOn
      (fun (s : Finset (d → ℤ)) (x : d → ℝ) ↦ iteratedFDeriv ℝ k
        (fun y : d → ℝ ↦ ∑ n ∈ s, c n * cexp (2 * π * I * ∑ i, (n i : ℂ) * y i)) x)
      (iteratedFDeriv ℝ k g) Filter.atTop (Metric.ball 0 (1 / 2)) := by
  -- Descend the periodic extension to the torus and expand it in its Fourier series.
  have hG := contDiff_periodize hsupp hg
  obtain ⟨f, -, hf⟩ := exists_continuous_comp_coe_eq hG.continuous fun n x ↦ periodize_add x n
  have hlift : (fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) = periodize g := funext hf
  refine ⟨mFourierCoeff f, fun k ↦ ?_⟩
  have h := tendstoUniformly_iteratedFDeriv_sum_mFourier (k := k)
    (K := Fintype.card d + k + 1) (by omega) (hlift ▸ hG.of_le
      (mod_cast le_top : ((Fintype.card d + k + 1 : ℕ) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))
  simp only [mFourier_coe_apply, smul_eq_mul, hlift] at h
  refine h.tendstoUniformlyOn.congr_right fun x hx ↦ ?_
  -- On the open cube the periodic extension agrees with `g` near every point.
  refine (Filter.EventuallyEq.iteratedFDeriv ℝ (Filter.eventually_of_mem
    (Metric.isOpen_ball.mem_nhds hx) fun y hy ↦ periodize_eq_of_mem_ball hsupp hy) k).eq_of_nhds

end TauCeti.UnitAddTorus
