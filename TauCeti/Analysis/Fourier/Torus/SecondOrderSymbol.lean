/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import TauCeti.Analysis.Fourier.Torus.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Operations
import TauCeti.Analysis.Fourier.Torus.FourierCoeff
import TauCeti.Analysis.Fourier.Torus.Uniqueness
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Topology.Instances.AddCircle.UnitAddTorus

/-!
# The Fourier symbol of a constant-coefficient second-order operator on the torus

On `UnitAddTorus d`, the operator `-∑ i, ∑ j, A i j ∂ᵢ∂ⱼ` has real Fourier symbol
`(2π)² k ⬝ᵥ (A *ᵥ k)`. This uses the sign of the nonnegative Laplacian for a
positive definite coefficient matrix. The formula holds for any real matrix and includes
mixed derivatives, as needed for a flat metric in nonorthogonal coordinates.

The eigen-equation on functions with a `C²` lift holds exactly when every nonzero Fourier
coefficient has the prescribed symbol value. Every integer frequency gives a smooth eigenmode.

For a flat torus in lattice coordinates, take `A` to be the inverse Gram matrix of the
lattice basis. The eigenvalue criterion then reduces the spectral calculation to the values
of this quadratic form on integer frequencies.

## Related results

* `UnitAddTorus.mFourierCoeff_lineDeriv` and its coordinate specialization
  `UnitAddTorus.mFourierCoeff_lineDeriv_single`: first-order Fourier multipliers.
* `MeasureTheory.Integrable.ae_eq_of_forall_mFourierCoeff_eq`: Fourier uniqueness for integrable
  functions; `Continuous.eq_of_mFourierCoeff_eq` is the continuous-function counterpart.
-/

public section

noncomputable section

open Complex UnitAddTorus TauCeti.UnitAddTorus
open scoped Real ContDiff

namespace Matrix

variable {d : Type*} [Fintype d]

/-- The real Fourier symbol of `-∑ i, ∑ j, A i j ∂ᵢ∂ⱼ` on the unit torus. -/
def torusSecondOrderSymbol (A : Matrix d d ℝ) (k : d → ℤ) : ℝ :=
  (2 * π) ^ 2 * ((fun i ↦ (k i : ℝ)) ⬝ᵥ (A *ᵥ fun i ↦ (k i : ℝ)))

theorem torusSecondOrderSymbol_def (A : Matrix d d ℝ) (k : d → ℤ) :
    A.torusSecondOrderSymbol k =
      (2 * π) ^ 2 * ((fun i ↦ (k i : ℝ)) ⬝ᵥ (A *ᵥ fun i ↦ (k i : ℝ))) :=
  (rfl)

@[simp]
theorem torusSecondOrderSymbol_zero (A : Matrix d d ℝ) : A.torusSecondOrderSymbol 0 = 0 := by
  simp [torusSecondOrderSymbol]

@[simp]
theorem zero_torusSecondOrderSymbol (k : d → ℤ) :
    (0 : Matrix d d ℝ).torusSecondOrderSymbol k = 0 := by
  simp [torusSecondOrderSymbol]

open Classical in
/-- The constant-coefficient operator `-∑ i, ∑ j, A i j ∂ᵢ∂ⱼ` on the unit torus. -/
def torusSecondOrderOperator (A : Matrix d d ℝ) (f : UnitAddTorus d → ℂ) : UnitAddTorus d → ℂ :=
  ∑ i, ∑ j, -(A i j : ℂ) • lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1)

theorem torusSecondOrderOperator_apply [DecidableEq d] (A : Matrix d d ℝ) (f : UnitAddTorus d → ℂ)
    (x : UnitAddTorus d) :
    A.torusSecondOrderOperator f x =
      -(∑ i, ∑ j, (A i j : ℂ) * lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1) x) := by
  -- The definition uses classical coordinate directions to avoid a DecidableEq parameter.
  -- Pointwise equality identifies them with the caller's coordinate directions.
  have hsingle (i : d) :
      @Pi.single d (fun _ ↦ ℝ) (fun _ ↦ inferInstance) (Classical.decEq d) i 1 =
        (Pi.single i 1 : d → ℝ) := by
    ext j
    by_cases h : j = i <;> simp [h]
  simp only [torusSecondOrderOperator, hsingle, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    neg_mul, Finset.sum_neg_distrib]

@[simp]
theorem torusSecondOrderOperator_const (A : Matrix d d ℝ) (c : ℂ) :
    A.torusSecondOrderOperator (fun _ ↦ c) = 0 := by
  have hzero (w : d → ℝ) : lineDeriv (0 : UnitAddTorus d → ℂ) w = 0 := by
    simpa only [Pi.zero_def] using lineDeriv_const (d := d) 0 w
  simp [torusSecondOrderOperator, hzero]

@[simp]
theorem zero_torusSecondOrderOperator (f : UnitAddTorus d → ℂ) :
    (0 : Matrix d d ℝ).torusSecondOrderOperator f = 0 := by
  simp [torusSecondOrderOperator]

@[simp]
theorem torusSecondOrderOperator_zero (A : Matrix d d ℝ) :
    A.torusSecondOrderOperator 0 = 0 :=
  A.torusSecondOrderOperator_const 0

/-- A constant-coefficient second-order operator maps `C^(n+2)` lifts to `C^n` lifts. -/
theorem contDiff_torusSecondOrderOperator (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ} {n : ℕ∞ω}
    (hf : ContDiff ℝ (n + 2) fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    ContDiff ℝ n fun x : d → ℝ ↦ A.torusSecondOrderOperator f (fun i ↦ (x i : UnitAddCircle)) := by
  simp only [torusSecondOrderOperator, Finset.sum_apply, Pi.smul_apply]
  refine ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦ ?_
  exact (contDiff_lineDeriv (contDiff_lineDeriv
    (by simpa only [add_assoc, one_add_one_eq_two] using hf) _) _).const_smul _

/-- A constant-coefficient second-order operator preserves smoothness. -/
theorem torusSecondOrderOperator_mem_smoothFunctions (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) : A.torusSecondOrderOperator f ∈ smoothFunctions d :=
  mem_smoothFunctions.2 (A.contDiff_torusSecondOrderOperator (n := ∞)
    (by simpa only [← one_add_one_eq_two, ← add_assoc, ENat.coe_top_add_one]
      using mem_smoothFunctions.1 hf))

/-- For `f` with a `C²` lift, the `k`-th Fourier coefficient of `A.torusSecondOrderOperator f`
is the coefficient of `f` multiplied by the real quadratic symbol at `k`. -/
@[simp]
theorem mFourierCoeff_torusSecondOrderOperator (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ 2 fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) (k : d → ℤ) :
    mFourierCoeff (A.torusSecondOrderOperator f) k =
      (A.torusSecondOrderSymbol k : ℂ) * mFourierCoeff f k := by
  -- This local instance agrees with the classical coordinate directions in the definition.
  classical
  have hderiv (j : d) := contDiff_lineDeriv (n := 1) hf (Pi.single j 1)
  have hint (i j : d) : MeasureTheory.Integrable
      (-(A i j : ℂ) • lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1)) :=
    (Continuous.integrable_of_hasCompactSupport
      (continuous_comp_coe_iff.1
        (contDiff_lineDeriv (n := 0) (hderiv j) (Pi.single i 1)).continuous)
      (.of_compactSpace _)).smul _
  rw [torusSecondOrderOperator, mFourierCoeff_sum (f := fun i ↦ ∑ j,
    -(A i j : ℂ) • lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1))
    (fun i _ ↦ MeasureTheory.integrable_finsetSum' _ fun j _ ↦ hint i j)]
  simp only [mFourierCoeff_sum (fun j _ ↦ hint _ j), mFourierCoeff_smul,
    mFourierCoeff_lineDeriv_single (hderiv _),
    mFourierCoeff_lineDeriv_single (hf.of_le (by norm_num)), smul_eq_mul]
  conv_rhs => rw [torusSecondOrderSymbol, dot_mulVec_eq_sum_sum, Finset.sum_comm]
  simp only [ofReal_mul, ofReal_pow, ofReal_ofNat, ofReal_sum, ofReal_intCast, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination -(2 * π : ℂ) ^ 2 * A i j * k i * k j * mFourierCoeff f k * Complex.I_sq

/-- A function with a `C²` lift satisfies the eigen-equation exactly when its nonzero
coefficients lie at frequencies with the prescribed symbol value. -/
theorem torusSecondOrderOperator_eq_smul_iff (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ 2 fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) {μ : ℂ} :
    A.torusSecondOrderOperator f = μ • f ↔
      ∀ k, mFourierCoeff f k ≠ 0 → (A.torusSecondOrderSymbol k : ℂ) = μ := by
  constructor
  · intro h k hk
    have hcoeff := A.mFourierCoeff_torusSecondOrderOperator hf k
    rw [h, mFourierCoeff_smul, smul_eq_mul] at hcoeff
    exact mul_right_cancel₀ hk hcoeff.symm
  · intro h
    refine Continuous.eq_of_mFourierCoeff_eq
      (continuous_comp_coe_iff.1 (A.contDiff_torusSecondOrderOperator (n := 0) hf).continuous)
      (continuous_const.smul (continuous_comp_coe_iff.1 hf.continuous))
        fun k ↦ ?_
    rw [A.mFourierCoeff_torusSecondOrderOperator hf, mFourierCoeff_smul, smul_eq_mul]
    by_cases hk : mFourierCoeff f k = 0
    · simp [hk]
    · rw [h k hk]

/-- Every nonzero eigenfunction with a `C²` lift has a nonzero Fourier coefficient at a
frequency whose symbol is its eigenvalue. -/
theorem exists_torusSecondOrderSymbol_eq_of_eigenfunction (A : Matrix d d ℝ)
    {f : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ 2 fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))
    (hne : f ≠ 0) {μ : ℂ} (h : A.torusSecondOrderOperator f = μ • f) :
    ∃ k, mFourierCoeff f k ≠ 0 ∧ (A.torusSecondOrderSymbol k : ℂ) = μ := by
  have hc : Continuous f := continuous_comp_coe_iff.1 hf.continuous
  obtain ⟨k, hk⟩ := hc.exists_mFourierCoeff_ne_zero hne
  exact ⟨k, hk, (A.torusSecondOrderOperator_eq_smul_iff hf).1 h k hk⟩

/-- The Fourier monomial at `k` is a smooth eigenfunction with eigenvalue
`A.torusSecondOrderSymbol k`. -/
@[simp]
theorem torusSecondOrderOperator_mFourier (A : Matrix d d ℝ) (k : d → ℤ) :
    A.torusSecondOrderOperator (mFourier k) = (A.torusSecondOrderSymbol k : ℂ) • ⇑(mFourier k) := by
  classical
  refine (A.torusSecondOrderOperator_eq_smul_iff ((contDiff_mFourier_coe k).of_le (by simp))).2
    fun l hl ↦ ?_
  by_cases h : l = k
  · subst l
    rfl
  · exact (hl (by simp [mFourierCoeff_mFourier, h])).elim

/-- The second-order torus operator is additive on functions with `C²` lifts. -/
theorem torusSecondOrderOperator_add (A : Matrix d d ℝ) {f g : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ 2 fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle))
    (hg : ContDiff ℝ 2 fun x : d → ℝ ↦ g fun i ↦ (x i : UnitAddCircle)) :
    A.torusSecondOrderOperator (f + g) =
      A.torusSecondOrderOperator f + A.torusSecondOrderOperator g := by
  have hAc {u : UnitAddTorus d → ℂ}
      (hu : ContDiff ℝ 2 fun x : d → ℝ ↦ u fun i ↦ (x i : UnitAddCircle)) :=
    continuous_comp_coe_iff.1 (A.contDiff_torusSecondOrderOperator (n := 0) hu).continuous
  have hint {u : UnitAddTorus d → ℂ} (hu : Continuous u) : MeasureTheory.Integrable u :=
    hu.integrable_of_hasCompactSupport (.of_compactSpace _)
  refine (hAc (hf.add hg)).eq_of_mFourierCoeff_eq ((hAc hf).add (hAc hg)) fun k ↦ ?_
  rw [A.mFourierCoeff_torusSecondOrderOperator (hf.add hg),
    mFourierCoeff_add (hint (continuous_comp_coe_iff.1 hf.continuous))
      (hint (continuous_comp_coe_iff.1 hg.continuous)),
    mFourierCoeff_add (hint (hAc hf)) (hint (hAc hg)),
    A.mFourierCoeff_torusSecondOrderOperator hf, A.mFourierCoeff_torusSecondOrderOperator hg,
    mul_add]

/-- The second-order torus operator commutes with complex scalar multiplication on functions
with `C²` lifts. -/
theorem torusSecondOrderOperator_smul (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ 2 fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) (c : ℂ) :
    A.torusSecondOrderOperator (c • f) = c • A.torusSecondOrderOperator f := by
  have hAc := continuous_comp_coe_iff.1
    (A.contDiff_torusSecondOrderOperator (n := 0) hf).continuous
  refine Continuous.eq_of_mFourierCoeff_eq (continuous_comp_coe_iff.1
    (A.contDiff_torusSecondOrderOperator (f := c • f) (n := 0) (hf.const_smul c)).continuous)
    (continuous_const.smul hAc) fun k ↦ ?_
  rw [A.mFourierCoeff_torusSecondOrderOperator (hf.const_smul c),
    mFourierCoeff_smul, mFourierCoeff_smul, A.mFourierCoeff_torusSecondOrderOperator hf,
    smul_eq_mul, smul_eq_mul]
  ring

end Matrix
