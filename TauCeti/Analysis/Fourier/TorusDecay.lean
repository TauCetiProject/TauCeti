/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Fourier.Monomial

/-!
# Fourier coefficients of smooth functions on the torus

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

Smooth periodic expansions of this kind are used to expand test functions on a compact coordinate
box, after periodic extension, in Fourier modes with rapidly decreasing coefficients, as in the
Fourier-series proof of the Schwartz kernel theorem.

## Main results

* `UnitAddTorus.mFourierCoeff_comp_add`: the coefficients of a translate.
* `TauCeti.UnitAddTorus.mFourierCoeff_eq_smul_of_hasDerivAt`: the coefficients of a directional
  derivative.
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

## References

* L. Grafakos, *Classical Fourier Analysis*, third edition, Graduate Texts in Mathematics 249,
  Springer, 2014, Section 3.2 (decay of the Fourier coefficients of smooth functions on the torus).
-/

public section

noncomputable section

open MeasureTheory Complex Topology Set
open scoped Real

/-- The measure on `ℝ / ℤ` is a probability measure. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

namespace TauCeti

/-- The sup norms of the integer vectors `n : d → ℤ` satisfy `∑ n, ‖n‖ ^ r < ∞` when
`r < -card d`. Here `‖0‖ ^ r = 0`. -/
theorem summable_pi_int_norm_rpow {d : Type*} [Fintype d] (r : ℝ) (hr : r < -Fintype.card d) :
    Summable fun n : d → ℤ ↦ ‖n‖ ^ r := by
  classical
  set L := Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))
  have hrank : Module.finrank ℤ L = Fintype.card d := by
    rw [ZLattice.rank ℝ L, Module.finrank_fintype_fun_eq_card]
  have hmem (n : d → ℤ) : (fun i ↦ (n i : ℝ)) ∈ L :=
    (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨n, by ext i; simp [Pi.single_apply]⟩
  have hinj : Function.Injective fun n : d → ℤ ↦ (⟨_, hmem n⟩ : L) := fun m n h ↦ by
    ext i
    simpa using congr_fun (congrArg Subtype.val h) i
  refine ((ZLattice.summable_norm_rpow L r (hrank ▸ hr)).comp_injective hinj).congr fun n ↦ ?_
  have hn (i : d) : ‖(n i : ℝ)‖₊ = ‖n i‖₊ := NNReal.eq (Int.norm_cast_real _)
  simp [Pi.norm_def, hn]

namespace UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} {E : Type*} [NormedAddCommGroup E]

/-! ### The quotient map `(d → ℝ) → UnitAddTorus d` -/

/-- The quotient map from `d → ℝ` onto the unit torus. -/
private def toTorus (x : d → ℝ) : UnitAddTorus d := fun i ↦ (x i : UnitAddCircle)

private theorem toTorus_apply (x : d → ℝ) (i : d) : toTorus x i = (x i : UnitAddCircle) := rfl

private theorem toTorus_add (x y : d → ℝ) : toTorus (x + y) = toTorus x + toTorus y := by
  ext i
  simp [toTorus_apply]

private theorem toTorus_smul (t : ℝ) (w : d → ℝ) :
    toTorus (t • w) = fun i ↦ ((t * w i : ℝ) : UnitAddCircle) := rfl

private theorem surjective_toTorus : Function.Surjective (toTorus (d := d)) := fun z ↦
  ⟨fun i ↦ (z i).out, by ext i; simp [toTorus_apply]⟩

private theorem isQuotientMap_toTorus : Topology.IsQuotientMap (toTorus (d := d)) :=
  (IsOpenQuotientMap.piMap fun _ ↦ QuotientAddGroup.isOpenQuotientMap_mk).isQuotientMap

private theorem toTorus_intCast (m : d → ℤ) : toTorus (fun i ↦ (m i : ℝ)) = 0 := by
  ext i
  simp [toTorus_apply]

/-- Two points of `d → ℝ` have the same image on the torus exactly when they differ by an integer
vector. -/
private theorem exists_eq_add_of_toTorus_eq {x y : d → ℝ} (h : toTorus x = toTorus y) :
    ∃ m : d → ℤ, y = x + fun i ↦ (m i : ℝ) := by
  choose m hm using fun i ↦ AddSubgroup.mem_zmultiples_iff.1
    (QuotientAddGroup.eq_iff_sub_mem.1 (congr_fun h i).symm)
  refine ⟨m, funext fun i ↦ ?_⟩
  simp only [Pi.add_apply]
  have := hm i
  simp only [zsmul_eq_mul, mul_one] at this
  linarith

/-- A function on `d → ℝ` which is invariant under integer translations descends to a function on
the torus, and the function is continuous when the lift is. -/
private theorem exists_continuous_comp_toTorus_eq {X : Type*} [TopologicalSpace X]
    {G : (d → ℝ) → X} (hG : Continuous G)
    (hper : ∀ (m : d → ℤ) (x : d → ℝ), G (x + fun i ↦ (m i : ℝ)) = G x) :
    ∃ g : UnitAddTorus d → X, Continuous g ∧ ∀ x, g (toTorus x) = G x := by
  have hfac : Function.FactorsThrough G toTorus := fun x y h ↦ by
    obtain ⟨m, rfl⟩ := exists_eq_add_of_toTorus_eq h
    exact (hper m x).symm
  refine ⟨isQuotientMap_toTorus.lift (f := ⟨toTorus, isQuotientMap_toTorus.continuous⟩)
    ⟨G, hG⟩ hfac, ContinuousMap.continuous _, fun x ↦ ?_⟩
  exact DFunLike.congr_fun (isQuotientMap_toTorus.lift_comp
    (f := ⟨toTorus, isQuotientMap_toTorus.continuous⟩) ⟨G, hG⟩ hfac) x

variable [Fintype d] [NormedSpace ℂ E]

/-! ### Translation and the Fourier coefficients -/

private theorem mFourier_toTorus (n : d → ℤ) (x : d → ℝ) :
    mFourier n (toTorus x) = cexp (2 * π * I * ∑ i, (n i : ℂ) * x i) :=
  mFourier_coe_apply n x

/-- The Fourier coefficients of `f` are integrals for the volume of the torus. Mathlib defines
`mFourierCoeff` using the Haar probability measure on each circle factor; this is the volume. -/
theorem mFourierCoeff_eq_integral_volume (f : UnitAddTorus d → E) (n : d → ℤ) :
    mFourierCoeff f n = ∫ z, mFourier (-n) z • f z := by
  have hvol : (volume : Measure (UnitAddTorus d)) = Measure.pi fun _ ↦ AddCircle.haarAddCircle := by
    rw [volume_pi]
    congr 1
    funext
    simp [AddCircle.volume_eq_smul_haarAddCircle]
  rw [hvol]
  -- Mathlib defines `mFourierCoeff` with its file-local normalization
  -- `volume = haarAddCircle` on `UnitAddCircle`, whose product measure is the measure above.
  rfl

end UnitAddTorus

end TauCeti

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
    rw [mFourierCoeff_comp_add, mFourier_toTorus]
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

/-- The iterated derivatives of the lift of a function on the torus are `ℤ^d`-periodic. -/
private theorem iteratedFDeriv_add_intCast (j : ℕ) (m : d → ℤ) (x : d → ℝ) :
    iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f (toTorus x)) (x + fun i ↦ (m i : ℝ)) =
      iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f (toTorus x)) x := by
  have h := congr_fun (iteratedFDeriv_comp_add_right' (𝕜 := ℝ)
    (f := fun x : d → ℝ ↦ f (toTorus x)) j fun i ↦ (m i : ℝ)) x
  simp only [toTorus_add, toTorus_intCast, add_zero] at h
  exact h.symm

/-- A continuous iterated derivative of the lift, evaluated on fixed directions, descends to a
continuous function on the torus. -/
private theorem exists_continuous_comp_toTorus_eq_iteratedFDeriv {j : ℕ}
    (hc : Continuous (iteratedFDeriv ℝ j fun x : d → ℝ ↦ f (toTorus x))) (v : Fin j → d → ℝ) :
    ∃ g : UnitAddTorus d → E, Continuous g ∧
      ∀ x, g (toTorus x) = iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f (toTorus x)) x v :=
  exists_continuous_comp_toTorus_eq ((continuous_eval_const v).comp hc)
    fun m x ↦ by simp only [iteratedFDeriv_add_intCast]

/-- A continuous iterated derivative of the lift is bounded. -/
private theorem exists_forall_norm_iteratedFDeriv_le {j : ℕ}
    (hc : Continuous (iteratedFDeriv ℝ j fun x : d → ℝ ↦ f (toTorus x))) :
    ∃ M, ∀ x, ‖iteratedFDeriv ℝ j (fun x : d → ℝ ↦ f (toTorus x)) x‖ ≤ M := by
  obtain ⟨g, hg, hgx⟩ := exists_continuous_comp_toTorus_eq hc (iteratedFDeriv_add_intCast f j)
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
      obtain ⟨x, rfl⟩ := surjective_toTorus z
      rw [hg, iteratedFDeriv_zero_apply]
    simp
  | succ k ih =>
    obtain ⟨g', hg'c, hg'⟩ := exists_continuous_comp_toTorus_eq_iteratedFDeriv f
      (hf.continuous_iteratedFDeriv (by norm_cast; omega)) (Fin.tail v)
    have hgc : Continuous g := by
      refine isQuotientMap_toTorus.continuous_iff.2 ?_
      simpa only [Function.comp_def, hg] using
        (continuous_eval_const v).comp (hf.continuous_iteratedFDeriv le_rfl)
    have hd := hf.differentiable_iteratedFDeriv (m := k) (by norm_cast; omega)
    -- `g` is the derivative of `g'` along `v 0`.
    have hderiv (z : UnitAddTorus d) : HasDerivAt
        (fun t : ℝ ↦ g' (z + fun i ↦ ((t * v 0 i : ℝ) : UnitAddCircle))) (g z) 0 := by
      obtain ⟨x, rfl⟩ := surjective_toTorus z
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
      obtain ⟨x, rfl⟩ := surjective_toTorus z
      simpa [norm_iteratedFDeriv_zero] using hM x
    · simpa [hn, zero_pow hk.ne'] using hM0
  -- Differentiate `k` times along a coordinate direction `i` with `|n i| = ‖n‖`.
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun i ↦ ‖n i‖₊
  have hni : ‖n‖ = |(n i : ℝ)| := by
    rw [← coe_nnnorm, Pi.nnnorm_def, hi, coe_nnnorm, Int.norm_eq_abs]
  obtain ⟨g, -, hg⟩ := exists_continuous_comp_toTorus_eq_iteratedFDeriv f
    (hf.continuous_iteratedFDeriv le_rfl) fun _ ↦ Pi.single i 1
  have hcoeff := mFourierCoeff_eq_prod_smul_of_iteratedFDeriv hf _ hg n
  have hsum : ∑ j, (n j : ℂ) * (((Pi.single i 1 : d → ℝ) j : ℝ) : ℂ) = n i := by
    rw [Finset.sum_eq_single i (fun j _ hj ↦ by simp [hj]) (by simp)]
    simp
  rw [hsum, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcoeff
  have hgM : ∀ z, ‖g z‖ ≤ M := fun z ↦ by
    obtain ⟨x, rfl⟩ := surjective_toTorus z
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

/-- **Absolute convergence of the Fourier coefficients.** If the lift of `f` to `d → ℝ` is `C^k`
for some `k` exceeding the dimension `d`, then `∑ n, ‖mFourierCoeff f n‖ < ∞`. -/
theorem summable_norm_mFourierCoeff {f : UnitAddTorus d → E} {k : ℕ}
    (hk : Fintype.card d < k)
    (hf : ContDiff ℝ k fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    Summable fun n ↦ ‖mFourierCoeff f n‖ := by
  obtain ⟨C, hC⟩ := exists_pow_mul_norm_mFourierCoeff_le hf
  refine Summable.of_norm_bounded_eventually ((summable_pi_int_norm_rpow (-k) (by
    simpa using (Nat.cast_lt (α := ℝ)).2 hk)).mul_left C) ?_
  filter_upwards [(Set.finite_singleton (0 : d → ℤ)).compl_mem_cofinite] with n hn
  have hpos : 0 < ‖n‖ := norm_pos_iff.2 hn
  rw [norm_norm, Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv,
    le_div_iff₀ (by positivity), mul_comm]
  exact hC n

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

end TauCeti.UnitAddTorus
