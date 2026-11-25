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

The symbol calculation applies `UnitAddTorus.mFourierCoeff_lineDeriv` twice, through its
coordinate specialization `UnitAddTorus.mFourierCoeff_lineDeriv_single`. Fourier uniqueness
(`MeasureTheory.Integrable.ae_eq_of_forall_mFourierCoeff_eq`) recovers the eigen-equation;
this is the continuous counterpart of `TauCeti.UnitAddTorus.eq_of_mFourierCoeff_eq` for smooth
functions.
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

open Classical in
/-- The constant-coefficient operator `-∑ i, ∑ j, A i j ∂ᵢ∂ⱼ` on the unit torus. -/
def torusSecondOrderOperator (A : Matrix d d ℝ) (f : UnitAddTorus d → ℂ) : UnitAddTorus d → ℂ :=
  ∑ i, ∑ j, -(A i j : ℂ) • lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1)

open Classical in
theorem torusSecondOrderOperator_apply (A : Matrix d d ℝ) (f : UnitAddTorus d → ℂ)
    (x : UnitAddTorus d) :
    A.torusSecondOrderOperator f x =
      -(∑ i, ∑ j, (A i j : ℂ) * lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1) x) := by
  simp only [torusSecondOrderOperator, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, neg_mul,
    Finset.sum_neg_distrib]

@[simp]
theorem torusSecondOrderOperator_const (A : Matrix d d ℝ) (c : ℂ) :
    A.torusSecondOrderOperator (fun _ ↦ c) = 0 := by
  have hzero (w : d → ℝ) : lineDeriv (0 : UnitAddTorus d → ℂ) w = 0 := by
    simpa only [Pi.zero_def] using lineDeriv_const (d := d) 0 w
  simp [torusSecondOrderOperator, hzero]

/-- A constant-coefficient second-order operator preserves smoothness. -/
theorem torusSecondOrderOperator_mem_smoothFunctions (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) : A.torusSecondOrderOperator f ∈ smoothFunctions d := by
  refine (smoothFunctions d).sum_mem fun i _ ↦ (smoothFunctions d).sum_mem fun j _ ↦ ?_
  exact (smoothFunctions d).smul_mem _
    (lineDeriv_mem_smoothFunctions (lineDeriv_mem_smoothFunctions hf _) _)

/-- A constant-coefficient second-order operator maps `C^(n+2)` lifts to `C^n` lifts. -/
theorem contDiff_torusSecondOrderOperator (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ} {n : ℕ∞ω}
    (hf : ContDiff ℝ (n + 2) fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) :
    ContDiff ℝ n fun x : d → ℝ ↦ A.torusSecondOrderOperator f (fun i ↦ (x i : UnitAddCircle)) := by
  simp only [torusSecondOrderOperator, Finset.sum_apply, Pi.smul_apply]
  refine ContDiff.sum fun i _ ↦ ContDiff.sum fun j _ ↦ ?_
  exact (contDiff_lineDeriv (contDiff_lineDeriv
    (by simpa only [add_assoc, one_add_one_eq_two] using hf) _) _).const_smul _

/-- For `f` with a `C²` lift, the `k`-th Fourier coefficient of `A.torusSecondOrderOperator f`
is the coefficient of `f` multiplied by the real quadratic symbol at `k`. -/
@[simp]
theorem mFourierCoeff_torusSecondOrderOperator (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : ContDiff ℝ 2 fun x : d → ℝ ↦ f fun i ↦ (x i : UnitAddCircle)) (k : d → ℤ) :
    mFourierCoeff (A.torusSecondOrderOperator f) k =
      (A.torusSecondOrderSymbol k : ℂ) * mFourierCoeff f k := by
  classical
  have hderiv (j : d) := contDiff_lineDeriv (n := 1) hf (Pi.single j 1)
  have hint (i j : d) : MeasureTheory.Integrable
      (-(A i j : ℂ) • lineDeriv (lineDeriv f (Pi.single j 1)) (Pi.single i 1)) :=
    ((isOpenQuotientMap_coe.isQuotientMap.continuous_iff.2
      (contDiff_lineDeriv (n := 0) (hderiv j) (Pi.single i 1)).continuous
      ).integrable_of_hasCompactSupport (.of_compactSpace _)).smul _
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
    have hc : Continuous f := isOpenQuotientMap_coe.isQuotientMap.continuous_iff.2 hf.continuous
    have hAc : Continuous (A.torusSecondOrderOperator f) :=
      isOpenQuotientMap_coe.isQuotientMap.continuous_iff.2
        (A.contDiff_torusSecondOrderOperator (n := 0) hf).continuous
    refine MeasureTheory.Measure.eq_of_ae_eq
      ((hAc.integrable_of_hasCompactSupport (.of_compactSpace _)).ae_eq_of_forall_mFourierCoeff_eq
        ((continuous_const.smul hc).integrable_of_hasCompactSupport (.of_compactSpace _))
        fun k ↦ ?_) hAc (continuous_const.smul hc)
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
  have hc : Continuous f := isOpenQuotientMap_coe.isQuotientMap.continuous_iff.2 hf.continuous
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

/-- The second-order torus operator is additive on smooth functions. -/
theorem torusSecondOrderOperator_add (A : Matrix d d ℝ) {f g : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) (hg : g ∈ smoothFunctions d) :
    A.torusSecondOrderOperator (f + g) =
      A.torusSecondOrderOperator f + A.torusSecondOrderOperator g := by
  refine eq_of_mFourierCoeff_eq (A.torusSecondOrderOperator_mem_smoothFunctions
    ((smoothFunctions d).add_mem hf hg))
    ((smoothFunctions d).add_mem (A.torusSecondOrderOperator_mem_smoothFunctions hf)
      (A.torusSecondOrderOperator_mem_smoothFunctions hg)) fun k ↦ ?_
  simp only [mFourierCoeff_add (integrable_of_mem_smoothFunctions hf)
    (integrable_of_mem_smoothFunctions hg),
    mFourierCoeff_add
      (integrable_of_mem_smoothFunctions (A.torusSecondOrderOperator_mem_smoothFunctions hf))
      (integrable_of_mem_smoothFunctions (A.torusSecondOrderOperator_mem_smoothFunctions hg)),
    mFourierCoeff_torusSecondOrderOperator A ((mem_smoothFunctions.1 hf).of_le (by simp)),
    mFourierCoeff_torusSecondOrderOperator A ((mem_smoothFunctions.1 hg).of_le (by simp)),
    mFourierCoeff_torusSecondOrderOperator A
      ((mem_smoothFunctions.1 ((smoothFunctions d).add_mem hf hg)).of_le (by simp)), mul_add]

/-- The second-order torus operator commutes with complex scalar multiplication on smooth
functions. -/
theorem torusSecondOrderOperator_smul (A : Matrix d d ℝ) {f : UnitAddTorus d → ℂ}
    (hf : f ∈ smoothFunctions d) (c : ℂ) :
    A.torusSecondOrderOperator (c • f) = c • A.torusSecondOrderOperator f := by
  refine eq_of_mFourierCoeff_eq (A.torusSecondOrderOperator_mem_smoothFunctions
    ((smoothFunctions d).smul_mem c hf))
    ((smoothFunctions d).smul_mem c (A.torusSecondOrderOperator_mem_smoothFunctions hf)) fun k ↦ ?_
  rw [mFourierCoeff_torusSecondOrderOperator A
    ((mem_smoothFunctions.1 ((smoothFunctions d).smul_mem c hf)).of_le (by simp)),
    mFourierCoeff_smul, mFourierCoeff_smul,
    mFourierCoeff_torusSecondOrderOperator A ((mem_smoothFunctions.1 hf).of_le (by simp)),
    smul_eq_mul, smul_eq_mul]
  ring

end Matrix
