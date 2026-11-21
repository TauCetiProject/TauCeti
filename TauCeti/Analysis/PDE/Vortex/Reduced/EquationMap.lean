/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Regularity
public import TauCeti.Analysis.Sobolev.BesselPotential.Exp
public import TauCeti.Analysis.Sobolev.BesselPotential.Operator
public import TauCeti.MeasureTheory.Function.Lp.BoundedContinuous
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.AtInfinity
import TauCeti.Analysis.Polynomial.Monic.OfCoeff
import TauCeti.Analysis.Polynomial.NormSq
import TauCeti.Analysis.PDE.Vortex.Existence
import TauCeti.Analysis.PDE.Vortex.Reduced.Functional
import TauCeti.Analysis.PDE.Vortex.Reduced.Sobolev
import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# The reduced vortex equation as a smooth map of the divisor and the correction

For a monic polynomial `P_c = X ^ m + c_(m-1) X ^ (m-1) + ⋯ + c_0` of degree `m ≥ 1`, with
coefficients `c ∈ ℂ^m` (`TauCeti.Polynomial.monicOfCoeff c`), Taubes's plane vortex with zero
divisor `P_c` is reconstructed from the solution `w` of the reduced equation

`Δw = h_c (exp (2w) - 1) / 8 + k_c`,
`h_c = ‖P_c‖² / (1 + ‖P_c‖²)`,  `k_c = (h_c - 1) / 8 + 2 ‖P_c'‖² / (1 + ‖P_c‖²)²`

(`TauCeti.Vortex.reducedSource`). The coefficients `c` are the symmetric coordinates of the divisor
in `Sym^m ℂ`, so collisions of zeros are included. This file realizes the equation as a map

`Φ : ℂ^m × H²(ℂ) → L²(ℂ)`,  `Φ(c, u) = Δu - h_c (exp (2u) - 1) / 8 - k_c`

(`TauCeti.Vortex.reducedEquationMap`), on the complexified Sobolev space `H²(ℂ) = H^{2,2}(ℂ, ℂ)`,
and proves that it is smooth jointly in the coefficients and the correction
(`TauCeti.Vortex.contDiff_reducedEquationMap`), with partial derivative in `u`

`D_u Φ(c, u) v = Δv - h_c exp (2u) v / 4`

(`TauCeti.Vortex.hasFDerivAt_reducedEquationMap`, `TauCeti.Vortex.coeFn_reducedLinearization`).
At a real `C²` correction `u = w`, `Φ(c, w) = 0` exactly when `w` solves the reduced equation
classically (`TauCeti.Vortex.reducedEquationMap_eq_zero_iff`), and for every `c` the map
`Φ(c, ·)` has a zero whose `L²` function is a smooth real function, by Taubes's variational
existence theorem (`TauCeti.Vortex.exists_reducedEquationMap_eq_zero`). This is the
input of the implicit function theorem that makes the vortex depend smoothly on its divisor: at a
real solution the operator `D_u Φ` is `-(-Δ + h_c exp (2w) / 4)`, a Schrödinger operator with a
nonnegative potential that is positive at infinity. Its invertibility and the identification of
the resulting family with Taubes's minimizer are not treated here.

## Smoothness in the coefficients

The coefficients enter only through the defect `φ_c = 1 - h_c = (1 + ‖P_c‖²)⁻¹`
(`TauCeti.Vortex.backgroundDefect`), as a bounded continuous multiplier and as an element of `L²`,
and through `k_c ∈ L²`. Smoothness of `c ↦ φ_c` and `c ↦ k_c` is proved without estimating any
derivative in `c` pointwise. Fix `c₀` and write `φ₀ = φ_{c₀}`. Expanding `P_c` in its coefficients,

`ρ_c = (1 + ‖P_c‖²) φ₀ = φ₀ + ∑_{i, j ≤ m} conj (a_i(c)) a_j(c) conj z ^ i z ^ j φ₀`,

where `a_i(c)` are the coefficients of `P_c`, is a polynomial in `c` and `conj c` with values in the
Banach algebra of bounded continuous functions, since `‖z‖ ^ (i + j) ≤ C (1 + ‖P₀‖²)` for
`i, j ≤ m`. It equals `1` at `c₀`, so it is invertible near `c₀`, and there

`φ_c = φ₀ ρ_c⁻¹`,  `2 ‖P_c'‖² φ_c² = 2 σ_c ρ_c⁻² φ₀`,  `σ_c = ‖P_c'‖² φ₀`,

with `σ_c` another polynomial in `c`. Inversion is smooth in a complete normed algebra and
multiplication of `L²` by bounded continuous functions is a bounded bilinear map
(`BoundedContinuousFunction.mulLpL`), so `c ↦ φ_c` is smooth into the bounded continuous functions
and `c ↦ φ_c, k_c` are smooth into `L²` (`TauCeti.Vortex.contDiff_backgroundDefect_monicOfCoeff`,
`TauCeti.Vortex.contDiff_backgroundDefectLp`, `TauCeti.Vortex.contDiff_backgroundSourceLp`).

## Smoothness in the correction

The term `h_c (exp (2u) - 1) = (exp (2u) - 1) - φ_c (exp (2u) - 1)` uses the smooth exponential
`BesselPotentialSpace.expSubOne` of the algebra `H²(ℂ)`, the Laplacian
`BesselPotentialSpace.laplacianCLM : H²(ℂ) → H⁰(ℂ)`, and the inclusion `H²(ℂ) ⊆ L²(ℂ)`.

## Main definitions

* `TauCeti.Vortex.backgroundDefect P`: the bounded continuous function `(1 + ‖P‖²)⁻¹`.
* `TauCeti.Vortex.backgroundDefectLp hm c`, `TauCeti.Vortex.backgroundSourceLp hm c`: `φ_c` and
  `k_c` as elements of `L²(ℂ)`.
* `TauCeti.Vortex.reducedEquationMap hm c u`: the map `Φ(c, u)`.
* `TauCeti.Vortex.reducedLinearization hm c u`: its partial derivative in `u`.

## Main results

* `TauCeti.Vortex.coeFn_reducedEquationMap`: `Φ(c, u)` is almost everywhere
  `Δu - h_c (exp (2u) - 1) / 8 - k_c`.
* `TauCeti.Vortex.contDiff_reducedEquationMap`: `Φ` is smooth on `ℂ^m × H²(ℂ)`.
* `TauCeti.Vortex.hasFDerivAt_reducedEquationMap`, `TauCeti.Vortex.coeFn_reducedLinearization`:
  its partial derivative in `u` is `v ↦ Δv - h_c exp (2u) v / 4`.
* `TauCeti.Vortex.reducedEquationMap_eq_zero_iff`: at a real `C²` correction, `Φ(c, u) = 0` is the
  classical reduced equation.
* `TauCeti.Vortex.exists_reducedEquationMap_eq_zero`: `Φ(c, ·)` has a zero whose `L²` function
  is a smooth real function.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex _root_.MeasureTheory Module Filter BesselPotentialSpace BoundedContinuousFunction
  TauCeti.Polynomial
open _root_.Polynomial (X eval_eq_sum_range')
open scoped BesselPotentialSpace ContDiff Topology ComplexConjugate ENNReal Laplacian

/-! ### The defect of the background weight -/

/-- The defect `1 - h = (1 + ‖P‖²)⁻¹` of the background weight `h = ‖P‖² / (1 + ‖P‖²)`
(`TauCeti.Vortex.backgroundWeight`), as a bounded continuous complex function. -/
def backgroundDefect (P : _root_.Polynomial ℂ) : ℂ →ᵇ ℂ :=
  .ofNormedAddCommGroup (fun z ↦ (((1 + ‖P.eval z‖ ^ 2)⁻¹ : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp ((continuous_const.add (P.continuous.norm.pow 2)).inv₀
      fun z ↦ (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne')) 1 fun z ↦ by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [norm_nonneg (P.eval z)])

/-- The values of the defect `(1 + ‖P‖²)⁻¹`. -/
@[simp]
theorem backgroundDefect_apply (P : _root_.Polynomial ℂ) (z : ℂ) :
    backgroundDefect P z = (((1 + ‖P.eval z‖ ^ 2)⁻¹ : ℝ) : ℂ) :=
  (rfl)

/-- `1 + ‖P z‖² ≠ 0`, as a complex number. -/
private theorem one_add_norm_sq_ne_zero (P : _root_.Polynomial ℂ) (z : ℂ) :
    (1 + (‖P.eval z‖ : ℂ) ^ 2) ≠ 0 := by
  exact_mod_cast (by positivity : (0 : ℝ) < 1 + ‖P.eval z‖ ^ 2).ne'

/-- The source `k = (h - 1) / 8 + 2 ‖P'‖² / (1 + ‖P‖²)²` in terms of the defect `φ = 1 - h`:
`k = -φ / 8 + 2 ‖P'‖² φ²`. -/
private theorem backgroundSource_eq_backgroundDefect (P : _root_.Polynomial ℂ) (z : ℂ) :
    (backgroundSource (P.eval ·) z : ℂ) = -8⁻¹ * backgroundDefect P z +
      2 * ((‖P.derivative.eval z‖ ^ 2 : ℝ) : ℂ) * backgroundDefect P z ^ 2 := by
  rw [backgroundSource_def, backgroundWeight_eq_one_sub_inv, _root_.Polynomial.deriv,
    backgroundDefect_apply]
  have := one_add_norm_sq_ne_zero P z
  push_cast
  field_simp
  ring

/-! ### Expansion in the coefficients -/

section Expansion

variable (P₀ : _root_.Polynomial ℂ)

/-- For `i, j ≤ deg P₀`, the function `conj z ^ i z ^ j / (1 + ‖P₀ z‖²)` is bounded. -/
private theorem exists_norm_monomialWeight_le (hP₀ : P₀ ≠ 0) {i j : ℕ} (hi : i ≤ P₀.natDegree)
    (hj : j ≤ P₀.natDegree) :
    ∃ C, ∀ z : ℂ, ‖conj z ^ i * z ^ j * backgroundDefect P₀ z‖ ≤ C := by
  have hdeg {k : ℕ} (hk : k ≤ P₀.natDegree) :
      ((X : _root_.Polynomial ℂ) ^ k).degree ≤ P₀.degree := by
    rw [_root_.Polynomial.degree_X_pow, _root_.Polynomial.degree_eq_natDegree hP₀]
    exact_mod_cast hk
  obtain ⟨Ci, hCi0, hCi⟩ := _root_.Polynomial.exists_norm_eval_le_mul_one_add_norm_eval (hdeg hi)
  obtain ⟨Cj, hCj0, hCj⟩ := _root_.Polynomial.exists_norm_eval_le_mul_one_add_norm_eval (hdeg hj)
  refine ⟨2 * (Ci * Cj), fun z ↦ ?_⟩
  have hpos : 0 < 1 + ‖P₀.eval z‖ ^ 2 := by positivity
  simp only [backgroundDefect_apply, norm_mul, norm_pow, Complex.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  set a := ‖P₀.eval z‖
  have hzi : ‖z‖ ^ i ≤ Ci * (1 + a) := by simpa using hCi z
  have hzj : ‖z‖ ^ j ≤ Cj * (1 + a) := by simpa using hCj z
  calc ‖z‖ ^ i * ‖z‖ ^ j ≤ Ci * (1 + a) * (Cj * (1 + a)) :=
        mul_le_mul hzi hzj (by positivity) (by positivity)
    _ = Ci * Cj * (1 + a) ^ 2 := by ring
    _ ≤ Ci * Cj * (2 * (1 + a ^ 2)) := by
        gcongr; nlinarith [sq_nonneg (a - 1)]
    _ = 2 * (Ci * Cj) * (1 + a ^ 2) := by ring

/-- The bounded continuous function `conj z ^ i z ^ j / (1 + ‖P₀ z‖²)` for `i, j ≤ n ≤ deg P₀`. -/
private def monomialWeight (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree) (i j : Fin (n + 1)) :
    ℂ →ᵇ ℂ :=
  .ofNormedAddCommGroup (fun z ↦ conj z ^ (i : ℕ) * z ^ (j : ℕ) * backgroundDefect P₀ z)
    (by fun_prop) _ (exists_norm_monomialWeight_le P₀ hP₀ (i.is_le.trans hn)
      (j.is_le.trans hn)).choose_spec

/-- The bounded continuous function `‖Q‖² / (1 + ‖P₀‖²)` of a polynomial `Q` with coefficients
`a`, as the quadratic form `∑ conj (a i) a j conj z ^ i z ^ j / (1 + ‖P₀ z‖²)` in `a`. -/
private def normSqWeight (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree) (a : Fin (n + 1) → ℂ) :
    ℂ →ᵇ ℂ :=
  ∑ i, ∑ j, (conj (a i) * a j) • monomialWeight P₀ hP₀ hn i j

private theorem normSqWeight_apply (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree)
    {Q : _root_.Polynomial ℂ} (hQ : Q.natDegree < n + 1) (z : ℂ) :
    normSqWeight P₀ hP₀ hn (fun i ↦ Q.coeff i) z =
      ((‖Q.eval z‖ ^ 2 : ℝ) : ℂ) * backgroundDefect P₀ z := by
  rw [← RCLike.ofReal_eq_complex_ofReal, _root_.Polynomial.ofReal_norm_eval_sq_eq_sum hQ,
    Finset.sum_mul, normSqWeight]
  simp only [_root_.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_apply, smul_eq_mul, monomialWeight, coe_ofNormedAddCommGroup]
  ring

/-- The quadratic form `normSqWeight` depends smoothly on coefficients that depend smoothly on a
parameter. -/
private theorem contDiff_normSqWeight (hP₀ : P₀ ≠ 0) {n : ℕ} (hn : n ≤ P₀.natDegree)
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {a : Y → Fin (n + 1) → ℂ}
    (ha : ∀ i, ContDiff ℝ ∞ fun y ↦ a y i) :
    ContDiff ℝ ∞ fun y ↦ normSqWeight P₀ hP₀ hn (a y) := by
  unfold normSqWeight
  refine ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦ ?_
  exact (((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp (ha i)).mul
    (ha j)).smul contDiff_const

end Expansion

/-! ### Degree bounds for `P_c` and `P_c'` -/

section Coefficients

variable {m : ℕ}

private theorem natDegree_monicOfCoeff_lt (c : Fin m → ℂ) : (monicOfCoeff c).natDegree < m + 1 := by
  rw [natDegree_monicOfCoeff]
  exact Nat.lt_succ_self m

private theorem natDegree_derivative_monicOfCoeff_lt (c : Fin m → ℂ) :
    (monicOfCoeff c).derivative.natDegree < m + 1 :=
  (_root_.Polynomial.natDegree_derivative_le _).trans_lt
    ((Nat.sub_le _ _).trans_lt (natDegree_monicOfCoeff_lt c))

end Coefficients

/-! ### The defect and the source as functions of the coefficients -/

section Family

variable {m : ℕ}

/-- `(1 + ‖P_c‖²)⁻¹` is square integrable when `m ≥ 1`. -/
theorem memLp_backgroundDefect_monicOfCoeff (hm : 0 < m) (c : Fin m → ℂ) :
    MemLp (backgroundDefect (monicOfCoeff c)) 2 volume := by
  have h := (_root_.Polynomial.memLp_inv_one_add_norm_eval_sq
    (P := monicOfCoeff c) (by rwa [natDegree_monicOfCoeff])).ofReal (K := ℂ)
  exact h.ae_eq (.of_forall fun z ↦ by simp)

/-- The source `k_c` of the reduced equation, as a complex function, is square integrable when
`m ≥ 1`. -/
theorem memLp_backgroundSource_monicOfCoeff (hm : 0 < m) (c : Fin m → ℂ) :
    MemLp (fun z ↦ (backgroundSource ((monicOfCoeff c).eval ·) z : ℂ)) 2 volume := by
  have h := (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight
    (P := monicOfCoeff c) (by rwa [natDegree_monicOfCoeff])).ofReal (K := ℂ)
  refine h.ae_eq (.of_forall fun z ↦ ?_)
  beta_reduce
  congr 1
  rw [backgroundSource_def, backgroundWeight_eq_one_sub_inv, _root_.Polynomial.deriv]
  ring

/-- The defect `φ_c = (1 + ‖P_c‖²)⁻¹` as an element of `L²(ℂ)`, for `m ≥ 1`. -/
def backgroundDefectLp (hm : 0 < m) (c : Fin m → ℂ) : Lp ℂ 2 (volume : Measure ℂ) :=
  (memLp_backgroundDefect_monicOfCoeff hm c).toLp _

/-- The source `k_c = (h_c - 1) / 8 + 2 ‖P_c'‖² / (1 + ‖P_c‖²)²` of the reduced equation
(`TauCeti.Vortex.backgroundSource`) as an element of `L²(ℂ)`, for `m ≥ 1`. -/
def backgroundSourceLp (hm : 0 < m) (c : Fin m → ℂ) : Lp ℂ 2 (volume : Measure ℂ) :=
  (memLp_backgroundSource_monicOfCoeff hm c).toLp _

/-- The `L²` function of `backgroundDefectLp hm c` is `(1 + ‖P_c‖²)⁻¹`. -/
theorem coeFn_backgroundDefectLp (hm : 0 < m) (c : Fin m → ℂ) :
    backgroundDefectLp hm c =ᵐ[volume] backgroundDefect (monicOfCoeff c) :=
  MemLp.coeFn_toLp _

/-- The `L²` function of `backgroundSourceLp hm c` is the source `k_c`. -/
theorem coeFn_backgroundSourceLp (hm : 0 < m) (c : Fin m → ℂ) :
    backgroundSourceLp hm c =ᵐ[volume]
      fun z ↦ (backgroundSource ((monicOfCoeff c).eval ·) z : ℂ) :=
  MemLp.coeFn_toLp _

end Family

/-! ### Smoothness of the defect and the source in the coefficients -/

section Smooth

variable {m : ℕ}

/-- The local representation of the coefficient dependence near `c₀`: with
`ρ_c = (1 + ‖P_c‖²) φ₀` and `σ_c = ‖P_c'‖² φ₀`, where `φ₀ = φ_{c₀}`, both polynomial in `c` and
`conj c`. Since `ρ_{c₀} = 1`, `ρ_c` is invertible near `c₀`, with smooth inverse, and there
`φ_c = φ₀ ρ_c⁻¹`. -/
private theorem exists_local_repr (c₀ : Fin m → ℂ) :
    ∃ ρ σ : (Fin m → ℂ) → ℂ →ᵇ ℂ, ContDiff ℝ ∞ σ ∧
      ContDiffAt ℝ ∞ (fun c ↦ Ring.inverse (ρ c)) c₀ ∧
      (∀ᶠ c in 𝓝 c₀, backgroundDefect (monicOfCoeff c) =
        backgroundDefect (monicOfCoeff c₀) * Ring.inverse (ρ c)) ∧
      ∀ c z, σ c z = ((‖(monicOfCoeff c).derivative.eval z‖ ^ 2 : ℝ) : ℂ) *
        backgroundDefect (monicOfCoeff c₀) z := by
  set P₀ := monicOfCoeff c₀ with hP₀c
  have hP₀ : P₀ ≠ 0 := (monic_monicOfCoeff c₀).ne_zero
  have hn : m ≤ P₀.natDegree := (natDegree_monicOfCoeff c₀).ge
  set ρ : (Fin m → ℂ) → ℂ →ᵇ ℂ :=
    fun c ↦ backgroundDefect P₀ + normSqWeight P₀ hP₀ hn fun i ↦ (monicOfCoeff c).coeff i
  have hρ : ContDiff ℝ ∞ ρ := contDiff_const.add (contDiff_normSqWeight P₀ hP₀ hn
    fun i ↦ (contDiff_coeff_monicOfCoeff i).restrict_scalars ℝ)
  have hρz (c : Fin m → ℂ) (z : ℂ) :
      ρ c z = ((1 + ‖(monicOfCoeff c).eval z‖ ^ 2 : ℝ) : ℂ) * backgroundDefect P₀ z := by
    rw [add_apply, normSqWeight_apply P₀ hP₀ hn (natDegree_monicOfCoeff_lt c),
      Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul]
  have hρ₀ : ρ c₀ = 1 := by
    ext z
    rw [hρz, ← hP₀c, backgroundDefect_apply, one_apply]
    have := one_add_norm_sq_ne_zero P₀ z
    push_cast
    field_simp
  -- `ρ` is `1` at `c₀`, so it is a unit near `c₀` and its inverse is smooth there.
  have hinv : ContDiffAt ℝ ∞ (fun c ↦ Ring.inverse (ρ c)) c₀ := by
    have := contDiffAt_ringInverse ℝ (n := ∞) (1 : (ℂ →ᵇ ℂ)ˣ)
    rw [Units.val_one, ← hρ₀] at this
    exact this.comp c₀ hρ.contDiffAt
  have hunit : ∀ᶠ c in 𝓝 c₀, IsUnit (ρ c) := hρ.continuous.continuousAt.preimage_mem_nhds
    (Units.isOpen.mem_nhds ((hρ₀ ▸ isUnit_one : IsUnit (ρ c₀))))
  -- Near `c₀`, `φ_c = φ₀ ρ_c⁻¹`.
  have hdef : ∀ᶠ c in 𝓝 c₀, backgroundDefect (monicOfCoeff c) =
      backgroundDefect P₀ * Ring.inverse (ρ c) := by
    filter_upwards [hunit] with c hc
    ext z
    rw [mul_apply, ringInverse_apply hc, hρz, backgroundDefect_apply, backgroundDefect_apply]
    have := one_add_norm_sq_ne_zero (monicOfCoeff c) z
    have := one_add_norm_sq_ne_zero P₀ z
    push_cast
    field_simp
  refine ⟨ρ, fun c ↦ normSqWeight P₀ hP₀ hn fun i ↦ (monicOfCoeff c).derivative.coeff i,
    contDiff_normSqWeight P₀ hP₀ hn
      fun i ↦ (contDiff_coeff_derivative_monicOfCoeff i).restrict_scalars ℝ,
    hinv, hdef, fun c z ↦ ?_⟩
  exact normSqWeight_apply P₀ hP₀ hn (natDegree_derivative_monicOfCoeff_lt c) z

/-- **The defect depends smoothly on the coefficients**, as a bounded continuous function. -/
theorem contDiff_backgroundDefect_monicOfCoeff :
    ContDiff ℝ ∞ fun c : Fin m → ℂ ↦ backgroundDefect (monicOfCoeff c) := by
  refine contDiff_iff_contDiffAt.2 fun c₀ ↦ ?_
  obtain ⟨ρ, -, -, hinv, hdef, -⟩ := exists_local_repr c₀
  exact (contDiffAt_const.mul hinv).congr_of_eventuallyEq hdef

/-- **The defect depends smoothly on the coefficients**, as an element of `L²(ℂ)`. -/
theorem contDiff_backgroundDefectLp (hm : 0 < m) :
    ContDiff ℝ ∞ (backgroundDefectLp (m := m) hm) := by
  refine contDiff_iff_contDiffAt.2 fun c₀ ↦ ?_
  obtain ⟨ρ, -, -, hinv, hdef, -⟩ := exists_local_repr c₀
  have hmul : ContDiffAt ℝ ∞
      (fun c ↦ mulLpL volume 2 (Ring.inverse (ρ c)) (backgroundDefectLp hm c₀)) c₀ :=
    ((((mulLpL (𝕜 := ℂ) (E := ℂ) volume 2).flip
      (backgroundDefectLp hm c₀)).restrictScalars ℝ).contDiff.contDiffAt).comp c₀ hinv
  refine hmul.congr_of_eventuallyEq ?_
  filter_upwards [hdef] with c hc
  refine Lp.ext ?_
  filter_upwards [coeFn_backgroundDefectLp hm c,
    coeFn_mulLpL volume 2 (Ring.inverse (ρ c)) (backgroundDefectLp hm c₀),
    coeFn_backgroundDefectLp hm c₀] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃, hc, mul_apply, smul_eq_mul, mul_comm]

/-- **The source depends smoothly on the coefficients**, as an element of `L²(ℂ)`. -/
theorem contDiff_backgroundSourceLp (hm : 0 < m) :
    ContDiff ℝ ∞ (backgroundSourceLp (m := m) hm) := by
  refine contDiff_iff_contDiffAt.2 fun c₀ ↦ ?_
  obtain ⟨ρ, σ, hσ, hinv, hdef, hσz⟩ := exists_local_repr c₀
  have hmul : ContDiffAt ℝ ∞
      (fun c ↦ mulLpL volume 2 (σ c * Ring.inverse (ρ c) ^ 2)
        (backgroundDefectLp hm c₀)) c₀ :=
    ((((mulLpL (𝕜 := ℂ) (E := ℂ) volume 2).flip
      (backgroundDefectLp hm c₀)).restrictScalars ℝ).contDiff.contDiffAt).comp c₀
      (hσ.contDiffAt.mul (hinv.pow 2))
  refine (((contDiff_backgroundDefectLp hm).contDiffAt.const_smul (-(8⁻¹ : ℂ))).add
    (hmul.const_smul (2 : ℂ))).congr_of_eventuallyEq ?_
  filter_upwards [hdef] with c hc
  refine Lp.ext ?_
  filter_upwards [coeFn_backgroundSourceLp hm c, Lp.coeFn_add ((-(8⁻¹ : ℂ)) •
      backgroundDefectLp hm c) ((2 : ℂ) • mulLpL volume 2
        (σ c * Ring.inverse (ρ c) ^ 2)
        (backgroundDefectLp hm c₀)),
    Lp.coeFn_smul (-(8⁻¹ : ℂ)) (backgroundDefectLp hm c),
    Lp.coeFn_smul (2 : ℂ) (mulLpL volume 2 (σ c * Ring.inverse (ρ c) ^ 2)
      (backgroundDefectLp hm c₀)),
    coeFn_backgroundDefectLp hm c,
    coeFn_mulLpL volume 2 (σ c * Ring.inverse (ρ c) ^ 2) (backgroundDefectLp hm c₀),
    coeFn_backgroundDefectLp hm c₀] with z h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rw [h₁, h₂, Pi.add_apply, h₃, h₄, Pi.smul_apply, Pi.smul_apply, h₅, h₆, h₇,
    backgroundSource_eq_backgroundDefect, hc, mul_apply, mul_apply, pow_apply, hσz]
  simp only [smul_eq_mul]
  ring

end Smooth

/-! ### The reduced equation map -/

section EquationMap

variable {m : ℕ}

/-- `dim ℂ = 2 < 2 · 2`: `H²(ℂ)` is an algebra. -/
private theorem finrank_lt : (finrank ℝ ℂ : ℝ) < 2 * 2 :=
  finrank_real_complex_lt_two_mul one_lt_two

/-- The nonlinearity `exp (2u) - 1` as an element of `H²(ℂ)`. -/
private def expTwo (u : H^{2}(ℂ)) : H^{2}(ℂ) :=
  expSubOne finrank_lt ((2 : ℂ) • u)

private theorem contDiff_expTwo : ContDiff ℂ ∞ expTwo :=
  (contDiff_expSubOne finrank_lt).comp (contDiff_id.const_smul (2 : ℂ))

/-- The `L²` function of `expTwo u` is almost everywhere `exp (2u) - 1`. -/
private theorem coeFn_inclusionLp_expTwo (u : H^{2}(ℂ)) :
    ⇑(inclusionLp zero_le_two (expTwo u)) =ᵐ[volume]
      fun z ↦ Complex.exp (2 * inclusionLp zero_le_two u z) - 1 := by
  filter_upwards [coeFn_inclusionLp_expSubOne finrank_lt zero_le_two ((2 : ℂ) • u),
    coeFn_inclusionLp_smul_ae_eq zero_le_two (2 : ℂ) (u := u) .rfl] with z h₁ h₂
  rw [expTwo, h₁, h₂, smul_eq_mul]

/-- Multiplication of `L²(ℂ)` by the background weight `h_c = 1 - φ_c`. -/
private def backgroundWeightMulL (c : Fin m → ℂ) :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  ContinuousLinearMap.id ℂ _ - mulLpL volume 2 (backgroundDefect (monicOfCoeff c))

private theorem backgroundWeightMulL_apply (c : Fin m → ℂ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    backgroundWeightMulL c f = f - mulLpL volume 2 (backgroundDefect (monicOfCoeff c)) f :=
  rfl

/-- `backgroundWeightMulL c f` is almost everywhere `h_c f`. -/
private theorem coeFn_backgroundWeightMulL (c : Fin m → ℂ) (f : Lp ℂ 2 (volume : Measure ℂ)) :
    backgroundWeightMulL c f =ᵐ[volume]
      fun z ↦ (backgroundWeight ((monicOfCoeff c).eval ·) z : ℂ) * f z := by
  filter_upwards [Lp.coeFn_sub f (mulLpL volume 2 (backgroundDefect (monicOfCoeff c)) f),
    coeFn_mulLpL volume 2 (backgroundDefect (monicOfCoeff c)) f] with z h₁ h₂
  rw [backgroundWeightMulL_apply, h₁, Pi.sub_apply, h₂, backgroundDefect_apply,
    backgroundWeight_eq_one_sub_inv, smul_eq_mul]
  push_cast
  ring

/-- **The reduced vortex equation map.** For `m ≥ 1`, coefficients `c ∈ ℂ^m` and
`u ∈ H²(ℂ)`, the defect `Φ(c, u) = Δu - h_c (exp (2u) - 1) / 8 - k_c ∈ L²(ℂ)` of the reduced
equation for the zero divisor of `P_c = TauCeti.Polynomial.monicOfCoeff c`
(`TauCeti.Vortex.coeFn_reducedEquationMap`). Here `h_c (exp (2u) - 1)` is written as
`(exp (2u) - 1) - φ_c (exp (2u) - 1)` with the bounded defect `φ_c = 1 - h_c`. -/
def reducedEquationMap (hm : 0 < m) (c : Fin m → ℂ) (u : H^{2}(ℂ)) : Lp ℂ 2 (volume : Measure ℂ) :=
  inclusionLp le_rfl (laplacianCLM (by norm_num) u) -
    (8⁻¹ : ℂ) • backgroundWeightMulL c (inclusionLp zero_le_two (expTwo u)) -
    backgroundSourceLp hm c

/-- **The values of the reduced equation map.** `Φ(c, u)` is almost everywhere
`Δu - h_c (exp (2u) - 1) / 8 - k_c`, where `Δu` is the Laplacian of `u ∈ H²(ℂ)`, and
`h_c (exp (2u) - 1) / 8 + k_c` is `TauCeti.Vortex.reducedSource` when `u` is real. -/
theorem coeFn_reducedEquationMap (hm : 0 < m) (c : Fin m → ℂ) (u : H^{2}(ℂ)) :
    reducedEquationMap hm c u =ᵐ[volume] fun z ↦
      inclusionLp le_rfl (laplacianCLM (by norm_num) u) z -
        (backgroundWeight ((monicOfCoeff c).eval ·) z : ℂ) *
          (Complex.exp (2 * inclusionLp zero_le_two u z) - 1) / 8 -
        (backgroundSource ((monicOfCoeff c).eval ·) z : ℂ) := by
  set H := backgroundWeightMulL c (inclusionLp zero_le_two (expTwo u))
  filter_upwards [Lp.coeFn_sub (inclusionLp le_rfl (laplacianCLM (by norm_num) u) -
      (8⁻¹ : ℂ) • H) (backgroundSourceLp hm c),
    Lp.coeFn_sub (inclusionLp le_rfl (laplacianCLM (by norm_num) u)) ((8⁻¹ : ℂ) • H),
    Lp.coeFn_smul (8⁻¹ : ℂ) H, coeFn_backgroundWeightMulL c (inclusionLp zero_le_two (expTwo u)),
    coeFn_inclusionLp_expTwo u, coeFn_backgroundSourceLp hm c]
    with z h₁ h₂ h₃ h₄ h₅ h₆
  simp only [reducedEquationMap]
  rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₃, Pi.smul_apply, h₄, h₅, h₆, smul_eq_mul]
  ring

/-- **The reduced vortex equation map is smooth** jointly in the coefficients `c ∈ ℂ^m` and the
correction `u ∈ H²(ℂ)`. -/
theorem contDiff_reducedEquationMap (hm : 0 < m) :
    ContDiff ℝ ∞ fun p : (Fin m → ℂ) × H^{2}(ℂ) ↦ reducedEquationMap hm p.1 p.2 := by
  have hE : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × H^{2}(ℂ) ↦ inclusionLp zero_le_two (expTwo p.2) :=
    (((inclusionLp zero_le_two).contDiff.comp contDiff_expTwo).restrict_scalars ℝ).comp
      contDiff_snd
  have hΔ : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × H^{2}(ℂ) ↦
      inclusionLp le_rfl (laplacianCLM (r := 0) (s := 2) (by norm_num) p.2) :=
    ((((inclusionLp le_rfl).comp (laplacianCLM (by norm_num))).restrictScalars ℝ).contDiff).comp
      contDiff_snd
  have hmul : ContDiff ℝ ∞ fun p : (Fin m → ℂ) × H^{2}(ℂ) ↦
      mulLpL volume 2 (backgroundDefect (monicOfCoeff p.1))
        (inclusionLp zero_le_two (expTwo p.2)) :=
    ((mulLpL (𝕜 := ℂ) (E := ℂ) volume 2).isBoundedBilinearMap.contDiff.restrict_scalars ℝ).comp
      ((contDiff_backgroundDefect_monicOfCoeff.comp contDiff_fst).prodMk hE)
  simp only [reducedEquationMap, backgroundWeightMulL_apply]
  exact (hΔ.sub ((hE.sub hmul).const_smul (8⁻¹ : ℂ))).sub
    ((contDiff_backgroundSourceLp hm).comp contDiff_fst)

/-- The partial derivative `D_u Φ(c, u)` of the reduced equation map in `u`:
`v ↦ Δv - h_c exp (2u) v / 4` (`TauCeti.Vortex.coeFn_reducedLinearization`). -/
def reducedLinearization (c : Fin m → ℂ) (u : H^{2}(ℂ)) :
    H^{2}(ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (inclusionLp le_rfl).comp (laplacianCLM (by norm_num)) -
    (4⁻¹ : ℂ) • ((backgroundWeightMulL c).comp (inclusionLp zero_le_two)).comp
      (mulCLM finrank_lt (expTwo u) + ContinuousLinearMap.id ℂ _)

/-- **The partial derivative of the reduced equation map in the correction.** -/
theorem hasFDerivAt_reducedEquationMap (hm : 0 < m) (c : Fin m → ℂ) (u : H^{2}(ℂ)) :
    HasFDerivAt (reducedEquationMap hm c) (reducedLinearization c u) u := by
  have hexp : HasFDerivAt expTwo
      ((2 : ℂ) • (mulCLM finrank_lt (expTwo u) + ContinuousLinearMap.id ℂ _)) u := by
    refine ((hasFDerivAt_expSubOne finrank_lt ((2 : ℂ) • u)).comp u
      ((hasFDerivAt_id u).const_smul (2 : ℂ))).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      map_smul, expTwo]
  set A : H^{2}(ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
    (backgroundWeightMulL c).comp (inclusionLp zero_le_two)
  have hA : HasFDerivAt (fun u ↦ A (expTwo u)) (A.comp ((2 : ℂ) •
      (mulCLM finrank_lt (expTwo u) + ContinuousLinearMap.id ℂ _))) u :=
    A.hasFDerivAt.comp u hexp
  have h := ((((inclusionLp le_rfl).comp (laplacianCLM (by norm_num))).hasFDerivAt (x := u)).sub
    (hA.const_smul (8⁻¹ : ℂ))).sub_const (backgroundSourceLp hm c)
  refine h.congr_fderiv ?_ |>.congr_of_eventuallyEq (.of_forall fun w ↦ ?_)
  · ext v
    simp only [reducedLinearization, A, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      map_smul, smul_smul]
    norm_num
  · simp [reducedEquationMap, A]

/-- **The values of the partial derivative.** `D_u Φ(c, u) v` is almost everywhere
`Δv - h_c exp (2u) v / 4`. -/
theorem coeFn_reducedLinearization (c : Fin m → ℂ) (u v : H^{2}(ℂ)) :
    reducedLinearization c u v =ᵐ[volume] fun z ↦
      inclusionLp le_rfl (laplacianCLM (by norm_num) v) z -
        (backgroundWeight ((monicOfCoeff c).eval ·) z : ℂ) *
          Complex.exp (2 * inclusionLp zero_le_two u z) * inclusionLp zero_le_two v z / 4 := by
  set W := mulCLM finrank_lt (expTwo u) v + v
  have hW : ⇑(inclusionLp zero_le_two W) =ᵐ[volume] fun z ↦
      Complex.exp (2 * inclusionLp zero_le_two u z) * inclusionLp zero_le_two v z := by
    filter_upwards [coeFn_inclusionLp_add_ae_eq zero_le_two (u := mulCLM finrank_lt (expTwo u) v)
        (v := v) .rfl .rfl,
      coeFn_inclusionLp_mulCLM finrank_lt zero_le_two (expTwo u) v, coeFn_inclusionLp_expTwo u]
      with z h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    ring
  set H := backgroundWeightMulL c (inclusionLp zero_le_two W)
  have hval : reducedLinearization c u v =
      inclusionLp le_rfl (laplacianCLM (by norm_num) v) - (4⁻¹ : ℂ) • H := by
    simp only [reducedLinearization, sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
      add_apply, ContinuousLinearMap.id_apply, H, W]
  rw [hval]
  filter_upwards [Lp.coeFn_sub (inclusionLp le_rfl (laplacianCLM (by norm_num) v))
      ((4⁻¹ : ℂ) • H), Lp.coeFn_smul (4⁻¹ : ℂ) H,
    coeFn_backgroundWeightMulL c (inclusionLp zero_le_two W), hW]
    with z h₁ h₂ h₃ h₄
  rw [h₁, Pi.sub_apply, h₂, Pi.smul_apply, h₃, h₄, smul_eq_mul]
  ring

/-- **Zeros of the reduced equation map are the classical solutions.** Let the `L²` function of
`u ∈ H²(ℂ)` be a real `C²` function `w`. Then `Φ(c, u) = 0` exactly when `w` solves the reduced
equation `Δw = h_c (exp (2w) - 1) / 8 + k_c` (`TauCeti.Vortex.reducedSource`) everywhere. -/
theorem reducedEquationMap_eq_zero_iff (hm : 0 < m) (c : Fin m → ℂ) {u : H^{2}(ℂ)} {w : ℂ → ℝ}
    (hw : ContDiff ℝ 2 w) (hu : ⇑(inclusionLp zero_le_two u) =ᵐ[volume] fun z ↦ (w z : ℂ)) :
    reducedEquationMap hm c u = 0 ↔ ∀ z, Δ w z = reducedSource (monicOfCoeff c) w z := by
  set g : ℂ → ℂ := fun z ↦ ((Δ w z - reducedSource (monicOfCoeff c) w z : ℝ) : ℂ)
  have hae : reducedEquationMap hm c u =ᵐ[volume] g := by
    filter_upwards [coeFn_reducedEquationMap hm c u, coeFn_inclusionLp_laplacianCLM_ae_eq le_rfl
      (by norm_num : (0 : ℝ) = 2 - 2) hw hu, hu] with z h₁ h₂ h₃
    rw [h₁, h₂, h₃]
    simp only [g, reducedSource_def]
    push_cast
    ring
  have hcont : Continuous g := by
    have hΔ : Continuous (Δ w) := hw.continuous_laplacian
    have hP : Continuous ((monicOfCoeff c).eval ·) := (monicOfCoeff c).continuous
    refine Complex.continuous_ofReal.comp (hΔ.sub ?_)
    rw [funext (reducedSource_def (monicOfCoeff c) w)]
    exact ((continuous_backgroundWeight hP).mul
      (((continuous_const.mul hw.continuous).rexp).sub continuous_const)).div_const _ |>.add
        (continuous_backgroundSource (monicOfCoeff c).differentiable)
  have hzero : (0 : Lp ℂ 2 (volume : Measure ℂ)) =ᵐ[volume] (0 : ℂ → ℂ) := Lp.coeFn_zero _ _ _
  constructor
  · intro h0 z
    have hg : g = 0 := (hcont.ae_eq_iff_eq volume continuous_const).1
      (hae.symm.trans (h0 ▸ hzero))
    have := congrFun hg z
    simp only [g, Pi.zero_apply, Complex.ofReal_eq_zero] at this
    linarith
  · intro h
    refine Lp.ext (hae.trans (Filter.EventuallyEq.trans (.of_forall fun z ↦ ?_) hzero.symm))
    simp [g, h z]

/-- **The reduced equation map has a smooth real zero.** For every `c ∈ ℂ^m`, `m ≥ 1`, there are
`u ∈ H²(ℂ)` and a smooth real function `w` such that the `L²` function of `u` is almost everywhere
`w` and `Φ(c, u) = 0`.
The proof takes for `w` a smooth square-integrable solution of the reduced equation for `P_c`,
which exists by Taubes's variational construction
(`TauCeti.Vortex.exists_contDiff_memLp_laplacian_eq_reduced`), and shows that it lies in
`H²(ℂ)`. -/
theorem exists_reducedEquationMap_eq_zero (hm : 0 < m) (c : Fin m → ℂ) :
    ∃ (u : H^{2}(ℂ)) (w : ℂ → ℝ), ContDiff ℝ ∞ w ∧
      (⇑(inclusionLp zero_le_two u) =ᵐ[volume] fun z ↦ (w z : ℂ)) ∧
      reducedEquationMap hm c u = 0 := by
  have hP : 0 < (monicOfCoeff c).natDegree := by rwa [natDegree_monicOfCoeff]
  obtain ⟨w, hw, hw2, -, hΔ⟩ := exists_contDiff_memLp_laplacian_eq_reduced hP
  obtain ⟨u, hu⟩ := (TemperedDistribution.mem_realSobolevFunctions_iff_exists_inclusionLp_ae_eq
    zero_le_two).1 (mem_realSobolevFunctions_of_laplacian_eq_reduced hP (hw.of_le (by simp))
      hw2 hΔ 2)
  refine ⟨u, w, hw, hu, (reducedEquationMap_eq_zero_iff hm c (hw.of_le (by simp)) hu).2
    fun z ↦ ?_⟩
  rw [hΔ z, reducedSource_def, backgroundSource_def]
  ring

end EquationMap

end TauCeti.Vortex
