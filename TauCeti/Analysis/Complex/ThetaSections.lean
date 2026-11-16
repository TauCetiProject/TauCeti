/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import TauCeti.Analysis.Complex.Laurent.Expansion
import TauCeti.Analysis.Complex.PowerSeries.FourierCoeff

/-!
# Level-`k` theta sections on complex tori

Let `τ ∈ ℂ` be a period parameter and `α, β ∈ ℝ` be real characteristics. On the universal cover
`ℂ` of the complex torus `ℂ / (ℤ + τℤ)`, the level-`k` automorphy factor
`thetaFactor k τ α β m n z = exp (2πi(mα + nβ) - πikn²τ - 2πiknz)` satisfies the `ℤ²`-cocycle
identity for every integer level `k : ℤ`, whereas for non-integer real levels the two lattice
generators fail to commute by the phase `exp (-2πik)`.

The holomorphic sections of the corresponding level-`k` theta line bundle (`k : ℕ`) are realized
as the `ℂ`-submodule `TauCeti.thetaSections k τ α β` of entire functions `s : ℂ → ℂ` satisfying
`s (z + 1) = exp (2πiα) * s z` and `s (z + τ) = exp (2πiβ - πikτ - 2πikz) * s z`. The Gaussian
Hermitian weight `thetaMetric k τ z = exp (-2πk (im z)² / im τ)` makes `thetaMetric k τ z * ‖s z‖²`
doubly periodic on the lattice `ℤ + τℤ`, and its Wirtinger derivatives yield the constant Chern
curvature `-πk / im τ` (whose integral against `dx ∧ dy` over a fundamental parallelogram equals
`k`).

Via the exponential coordinate `w = exp (2πiz)` (`Function.Periodic.qParam 1`) and Laurent
expansion on `ℂ \ {0}` (`DifferentiableOn.hasLaurentSeriesOnAnnulus`), every entire function
quasi-periodic under `z ↦ z + 1` expands into a twisted Fourier series with coefficients
`thetaFourierCoeff α s m = ∫ t in 0..1, exp (-2πi(m + α)t) * s t`, and the `τ`-automorphy law is
equivalent to the exact shift-by-`k` recurrence
`c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m`.

## Main definitions

* `TauCeti.thetaFactor`: the `ℤ²`-automorphy cocycle at integer level `k : ℤ`.
* `TauCeti.thetaMetric`: the Gaussian Hermitian metric weight `exp (-2πk (im z)² / im τ)`.
* `TauCeti.thetaSections`: the `ℂ`-submodule of level-`k` holomorphic theta sections with
  characteristics `(α, β)`.
* `TauCeti.thetaFourierCoeff`: the `m`-th twisted Fourier coefficient on `[0, 1]`.
* `TauCeti.characteristicTheta`: the `r`-th level-`k` characteristic theta function built from
  Mathlib's `jacobiTheta₂`.
* `TauCeti.thetaSectionsBasis`: the explicit `Fin k`-indexed `ℂ`-basis of `thetaSections k τ α β`
  for `k > 0` and `0 < τ.im`.

## Main results

* `TauCeti.thetaFactor_cocycle` and `TauCeti.thetaFactor_commutator_real_eq_iff`: the `ℤ²`
  automorphy cocycle law and integrality obstruction for real levels.
* `TauCeti.thetaMetric_add_int_add_int_mul_tau`, `TauCeti.wirtingerDeriv_log_thetaMetric`, and
  `TauCeti.conjWirtingerDeriv_chernForm_thetaMetric`: descent of the Hermitian metric and its
  constant Chern curvature.
* `TauCeti.hasSum_thetaFourierCoeff` and `TauCeti.thetaSections_tau_iff_recurrence`: twisted
  Fourier expansion of quasi-periodic entire functions and exact equivalence with the coefficient
  recurrence.
* `TauCeti.characteristicTheta_mem_thetaSections`, `TauCeti.jacobiTheta₂_mem_thetaSections`, and
  `TauCeti.thetaFourierCoeff_characteristicTheta_fin`: the characteristic theta functions form
  sections dual to the first `k` twisted Fourier coefficients.
* `TauCeti.finrank_thetaSections`: for `0 < k` and `0 < τ.im`,
  `Module.finrank ℂ (thetaSections k τ α β) = k`.
* `TauCeti.thetaSections_eq_bot_of_im_nonpos`, `TauCeti.finrank_thetaSections_of_im_nonpos`, and
  `TauCeti.finrank_thetaSections_zero`: complete boundary classification for `τ.im ≤ 0` and
  `k = 0`.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, 2nd edition, Grundlehren
  der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
* Nicholas M. J. Woodhouse, *Geometric Quantization*, 2nd edition, Oxford University Press, 1992.
-/

public section

open Complex Filter Metric Set
open scoped Real ENNReal Topology

namespace TauCeti

/-! ### Automorphy factor and integrality obstruction -/

/-- The level-`k` automorphy factor on the lattice `ℤ + τℤ` with real characteristics `(α, β)`:
`thetaFactor k τ α β m n z = exp (2πi(mα + nβ) - πikn²τ - 2πiknz)`. -/
noncomputable def thetaFactor (k : ℤ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z)

/-- Defining formula for `thetaFactor`. -/
theorem thetaFactor_def (k : ℤ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    thetaFactor k τ α β m n z =
      cexp (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z) :=
  (rfl)

/-- The automorphy factor never vanishes. -/
theorem thetaFactor_ne_zero (k : ℤ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    thetaFactor k τ α β m n z ≠ 0 :=
  Complex.exp_ne_zero _

/-- At the lattice origin `(0, 0)`, the automorphy factor equals `1`. -/
@[simp]
theorem thetaFactor_zero_zero (k : ℤ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 0 0 z = 1 := by
  simp [thetaFactor_def]

/-- Along the first lattice generator `(1, 0)`, the automorphy factor is `exp (2πiα)`. -/
@[simp]
theorem thetaFactor_one_zero (k : ℤ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 1 0 z = cexp (2 * π * I * α) := by
  simp [thetaFactor_def]

/-- Along the second lattice generator `(0, 1)`, the automorphy factor is
`exp (2πiβ - πikτ - 2πikz)`. -/
@[simp]
theorem thetaFactor_zero_one (k : ℤ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 0 1 z = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) := by
  simp [thetaFactor_def]

/-- The `ℤ²`-cocycle identity for `thetaFactor` at any integer level `k : ℤ`. -/
theorem thetaFactor_cocycle (k : ℤ) (τ : ℂ) (α β : ℝ) (m₁ n₁ m₂ n₂ : ℤ) (z : ℂ) :
    thetaFactor k τ α β (m₁ + m₂) (n₁ + n₂) z =
      thetaFactor k τ α β m₁ n₁ (z + m₂ + n₂ * τ) * thetaFactor k τ α β m₂ n₂ z := by
  simp only [thetaFactor_def, ← Complex.exp_add]
  have h1 : cexp (((-(k * n₁ * m₂) : ℤ) : ℂ) * (2 * π * I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (-(k * n₁ * m₂))
  conv_lhs => rw [← mul_one (cexp _), ← h1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Shifting the characteristics `(α, β)` by integers leaves `thetaFactor` unchanged. -/
theorem thetaFactor_add_int (k : ℤ) (τ : ℂ) (α β : ℝ) (a b m n : ℤ) (z : ℂ) :
    thetaFactor k τ (α + a) (β + b) m n z = thetaFactor k τ α β m n z := by
  simp only [thetaFactor_def]
  have h1 : cexp (((m * a + n * b : ℤ) : ℂ) * (2 * π * I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (m * a + n * b)
  conv_rhs => rw [← mul_one (cexp _), ← h1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The automorphy factor is multiplicative in the level and characteristics. -/
theorem thetaFactor_add_level (k₁ k₂ : ℤ) (τ : ℂ) (α₁ β₁ α₂ β₂ : ℝ) (m n : ℤ) (z : ℂ) :
    thetaFactor (k₁ + k₂) τ (α₁ + α₂) (β₁ + β₂) m n z =
      thetaFactor k₁ τ α₁ β₁ m n z * thetaFactor k₂ τ α₂ β₂ m n z := by
  simp only [thetaFactor_def, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The modulus of `thetaFactor k τ α β m n z` is `exp (πkn² im τ + 2πkn im z)`. -/
theorem norm_thetaFactor (k : ℤ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    ‖thetaFactor k τ α β m n z‖ = Real.exp (π * k * n ^ 2 * τ.im + 2 * π * k * n * z.im) := by
  rw [thetaFactor_def, Complex.norm_exp]
  congr 1
  have hre :
      (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z).re =
        ((2 * π * (m * α + n * β) : ℝ) * I - (π * k * n ^ 2 : ℝ) * (I * τ) -
          (2 * π * k * n : ℝ) * (I * z)).re := by
    congr 1
    push_cast
    ring
  rw [hre]
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
    zero_sub, mul_one, mul_im]
  ring

/-- For an arbitrary real level `k : ℝ`, composing the `z ↦ z + 1` and `z ↦ z + τ` automorphy
factors in the two orders differs by the constant phase `exp (-2πik)`. -/
theorem thetaFactor_commutator_real (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + 1)) * cexp (2 * π * I * α) =
      cexp (-2 * π * I * k) *
        (cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z)) := by
  simp only [← Complex.exp_add]
  congr 1
  ring

/-- **Integrality obstruction for the torus automorphy factor.** The `z ↦ z + 1` and `z ↦ z + τ`
generator factors at real level `k : ℝ` satisfy the abelian compatibility relation if and only if
`k` is an integer. -/
theorem thetaFactor_commutator_real_eq_iff (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + 1)) * cexp (2 * π * I * α) =
        cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) ↔
      ∃ n : ℤ, (n : ℝ) = k := by
  rw [thetaFactor_commutator_real]
  have hne : cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  constructor
  · intro h
    have hexp : cexp (-2 * π * I * k) = 1 :=
      mul_right_cancel₀ hne (by simpa using h)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    have hmul : (-k : ℂ) * (2 * π * I) = (n : ℂ) * (2 * π * I) := by
      calc
        (-k : ℂ) * (2 * π * I) = -2 * π * I * k := by ring
        _ = (n : ℂ) * (2 * π * I) := hn
    have hEq : (-k : ℂ) = (n : ℂ) := mul_right_cancel₀ two_pi_I_ne_zero hmul
    refine ⟨-n, ?_⟩
    have hR : -k = (n : ℝ) := by exact_mod_cast hEq
    push_cast
    linarith
  · rintro ⟨n, rfl⟩
    have hexp : cexp (-2 * π * I * (n : ℂ)) = 1 := by
      rw [show (-2 * π * I * (n : ℂ)) = ((-n : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-n)
    rw [ofReal_intCast, hexp, one_mul]

/-! ### Gaussian Hermitian metric and Chern Wirtinger forms -/

/-- The Gaussian Hermitian metric weight `h(z) = exp (-2πk (im z)² / im τ)` for the level-`k`
theta line on `ℂ / (ℤ + τℤ)`. -/
noncomputable def thetaMetric (k : ℝ) (τ z : ℂ) : ℝ :=
  Real.exp (-2 * π * k * z.im ^ 2 / τ.im)

/-- Defining formula for `thetaMetric`. -/
theorem thetaMetric_def (k : ℝ) (τ z : ℂ) :
    thetaMetric k τ z = Real.exp (-2 * π * k * z.im ^ 2 / τ.im) :=
  (rfl)

/-- The Hermitian metric weight `thetaMetric` is strictly positive everywhere. -/
theorem thetaMetric_pos (k : ℝ) (τ z : ℂ) : 0 < thetaMetric k τ z :=
  Real.exp_pos _

/-- The Hermitian metric weight is invariant under real integer translations `z ↦ z + 1`. -/
@[simp]
theorem thetaMetric_add_one (k : ℝ) (τ z : ℂ) :
    thetaMetric k τ (z + 1) = thetaMetric k τ z := by
  simp [thetaMetric_def]

/-- Under any lattice translation `z ↦ z + m + n * τ`, the metric weight `thetaMetric` transforms
inversely to `‖thetaFactor‖²`, so `h(z) ‖s(z)‖²` descends to the torus whenever `τ.im ≠ 0`. -/
theorem thetaMetric_add_int_add_int_mul_tau (k : ℤ) {τ : ℂ} (hτ : τ.im ≠ 0) (α β : ℝ)
    (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖thetaFactor k τ α β m n z‖ ^ 2 = thetaMetric k τ z := by
  rw [thetaMetric_def, thetaMetric_def, norm_thetaFactor, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have him : (z + m + n * τ).im = z.im + n * τ.im := by simp
  rw [him]
  field_simp [hτ]
  ring

/-- Along the single generator shift `z ↦ z + τ` at any real level `k : ℝ`, the metric weight
transforms inversely to the squared modulus of the generator factor whenever `τ.im ≠ 0`. -/
theorem thetaMetric_add_tau_mul_norm_sq (k : ℝ) {τ : ℂ} (hτ : τ.im ≠ 0) (β : ℝ) (z : ℂ) :
    thetaMetric k τ (z + τ) * ‖cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z)‖ ^ 2 =
      thetaMetric k τ z := by
  rw [thetaMetric_def, thetaMetric_def, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  have hre :
      (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z).re =
        π * k * τ.im + 2 * π * k * z.im := by
    have hrew :
        (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z).re =
          ((2 * π * β : ℝ) * I - (π * k : ℝ) * (I * τ) - (2 * π * k : ℝ) * (I * z)).re := by
      congr 1
      push_cast
      ring
    rw [hrew]
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
      zero_sub, mul_one, mul_im]
    ring
  rw [hre, add_im]
  field_simp [hτ]
  ring

/-- The `(1, 0)`-Wirtinger derivative of `log (thetaMetric k τ z)` is the Chern connection
`(1, 0)`-form `∂ log h = 2πik (im z / im τ)`. -/
theorem wirtingerDeriv_log_thetaMetric (k : ℝ) (τ z : ℂ) :
    wirtingerDeriv (fun w : ℂ => (Real.log (thetaMetric k τ w) : ℂ)) z 1 =
      2 * π * I * k * (z.im / τ.im) := by
  have hfun :
      (fun w : ℂ => (Real.log (thetaMetric k τ w) : ℂ)) =
        fun w : ℂ => Complex.ofRealCLM ((-2 * π * k / τ.im) * (Complex.imCLM w) ^ 2) := by
    ext w
    simp only [thetaMetric_def, Real.log_exp, Complex.ofRealCLM_apply, Complex.imCLM_apply]
    congr 1
    ring
  have hsq : HasFDerivAt (fun w : ℂ => (Complex.imCLM w) ^ 2)
      ((2 * z.im) • Complex.imCLM) z := by
    simpa [pow_one, mul_comm] using (Complex.imCLM.hasFDerivAt (x := z)).pow 2
  have hreal : HasFDerivAt (fun w : ℂ => (-2 * π * k / τ.im) * (Complex.imCLM w) ^ 2)
      ((-2 * π * k / τ.im) • ((2 * z.im) • Complex.imCLM)) z :=
    hsq.const_mul (-2 * π * k / τ.im)
  have hf : HasFDerivAt (fun w : ℂ => (Real.log (thetaMetric k τ w) : ℂ))
      (Complex.ofRealCLM.comp ((-2 * π * k / τ.im) • ((2 * z.im) • Complex.imCLM))) z := by
    rw [hfun]
    exact Complex.ofRealCLM.hasFDerivAt.comp z hreal
  rw [wirtingerDeriv_apply, hf.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, Complex.imCLM_apply,
    Complex.one_im, Complex.I_im, smul_eq_mul, mul_zero, mul_one, Complex.ofRealCLM_apply,
    Complex.ofReal_zero, zero_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  ring

/-- The `(0, 1)`-Wirtinger derivative of the Chern `(1, 0)`-form `2πik (im z / im τ)` is the
constant curvature `-πk / im τ`, corresponding to first Chern class `(k / im τ) dx ∧ dy`. -/
theorem conjWirtingerDeriv_chernForm_thetaMetric (k : ℝ) (τ z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ => 2 * π * I * (k : ℂ) * (w.im / τ.im : ℂ)) z 1 =
      -(π : ℂ) * k / τ.im := by
  let c : ℂ := 2 * π * I * k / τ.im
  have hfun :
      (fun w : ℂ => 2 * π * I * (k : ℂ) * (w.im / τ.im : ℂ)) =
        fun w : ℂ => c • Complex.ofRealCLM (Complex.imCLM w) := by
    ext w
    simp only [c, Complex.ofRealCLM_apply, Complex.imCLM_apply, smul_eq_mul]
    ring
  have hf : HasFDerivAt (fun w : ℂ => 2 * π * I * (k : ℂ) * (w.im / τ.im : ℂ))
      (c • (Complex.ofRealCLM.comp Complex.imCLM)) z := by
    rw [hfun]
    exact (Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt).const_smul c
  rw [conjWirtingerDeriv_apply, hf.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, Complex.imCLM_apply,
    Complex.one_im, Complex.I_im, Complex.ofRealCLM_apply, Complex.ofReal_zero, Complex.ofReal_one,
    smul_eq_mul, mul_one, c]
  have hI : I * (2 * π * I * k / τ.im) = -(2 * π * k / τ.im) := by
    calc
      I * (2 * π * I * k / τ.im) = (I * I) * (2 * π * k / τ.im) := by ring
      _ = -(2 * π * k / τ.im) := by rw [I_mul_I]; ring
  rw [hI]
  ring

/-! ### Holomorphic theta sections -/

/-- The holomorphic sections of the level-`k` theta line with characteristics `(α, β)` on the
complex torus `ℂ / (ℤ + τℤ)`, realized as entire functions `s : ℂ → ℂ` satisfying
`s (z + 1) = exp (2πiα) * s z` and `s (z + τ) = exp (2πiβ - πikτ - 2πikz) * s z`. -/
noncomputable def thetaSections (k : ℕ) (τ : ℂ) (α β : ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {s | Differentiable ℂ s ∧
    (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
    ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z}
  add_mem' := by
    rintro f g ⟨hf, hf1, hfτ⟩ ⟨hg, hg1, hgτ⟩
    exact ⟨hf.add hg, fun z => by simp [hf1, hg1, mul_add],
      fun z => by simp [hfτ, hgτ, mul_add]⟩
  zero_mem' := ⟨differentiable_const 0, fun z => by simp, fun z => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf1, hfτ⟩
    exact ⟨hf.const_smul c, fun z => by simp [hf1]; ring, fun z => by simp [hfτ]; ring⟩

/-- Membership characterization for `thetaSections`. -/
theorem mem_thetaSections_iff {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ} :
    s ∈ thetaSections k τ α β ↔
      Differentiable ℂ s ∧
        (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
        ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z :=
  Iff.rfl

/-- Every theta section is an entire function. -/
theorem differentiable_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) : Differentiable ℂ s :=
  hs.1

/-- First generator automorphy law for a theta section. -/
theorem add_one_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s (z + 1) = cexp (2 * π * I * α) * s z :=
  hs.2.1 z

/-- Second generator automorphy law for a theta section. -/
theorem add_tau_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z :=
  hs.2.2 z

private lemma add_int_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m : ℤ) (z : ℂ) :
    s (z + m) = thetaFactor k τ α β m 0 z * s z := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ j ih =>
    have hstep : z + (((j : ℤ) + 1 : ℤ) : ℂ) = (z + (j : ℤ)) + 1 := by push_cast; ring
    rw [hstep, hs.2.1, ih, ← mul_assoc, ← thetaFactor_one_zero (k : ℤ) τ α β (z + (j : ℤ))]
    have hcoc := thetaFactor_cocycle (k : ℤ) τ α β 1 0 j 0 z
    simpa [add_comm] using congrArg (· * s z) hcoc.symm
  | pred j ih =>
    have hstep : z + ((-(j : ℤ) - 1 : ℤ) : ℂ) + 1 = z + ((-(j : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    have h1 := hs.2.1 (z + ((-(j : ℤ) - 1 : ℤ) : ℂ))
    rw [hstep, ih] at h1
    have hcoc := thetaFactor_cocycle (k : ℤ) τ α β 1 0 (-(j : ℤ) - 1) 0 z
    have hidx : (1 : ℤ) + (-(j : ℤ) - 1) = -(j : ℤ) := by ring
    rw [hidx, zero_add, Int.cast_zero, zero_mul, add_zero, thetaFactor_one_zero] at hcoc
    rw [hcoc, mul_assoc] at h1
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) h1).symm

private lemma add_int_mul_tau_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n : ℤ) (z : ℂ) :
    s (z + n * τ) = thetaFactor k τ α β 0 n z * s z := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ j ih =>
    have hstep : z + (((j : ℤ) + 1 : ℤ) : ℂ) * τ = (z + (j : ℤ) * τ) + τ := by push_cast; ring
    rw [hstep, hs.2.2, ih, ← mul_assoc]
    have hcoc := thetaFactor_cocycle (k : ℤ) τ α β 0 1 0 j z
    rw [thetaFactor_zero_one] at hcoc
    have hcoc' : thetaFactor (k : ℤ) τ α β 0 (j + 1) z =
        cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + (j : ℤ) * τ)) *
          thetaFactor (k : ℤ) τ α β 0 j z := by
      simpa [add_comm] using hcoc
    rw [← hcoc']
  | pred j ih =>
    have hstep : z + ((-(j : ℤ) - 1 : ℤ) : ℂ) * τ + τ = z + ((-(j : ℤ) : ℤ) : ℂ) * τ := by
      push_cast; ring
    have hτ := hs.2.2 (z + ((-(j : ℤ) - 1 : ℤ) : ℂ) * τ)
    rw [hstep, ih] at hτ
    have hcoc := thetaFactor_cocycle (k : ℤ) τ α β 0 1 0 (-(j : ℤ) - 1) z
    have hidx : (1 : ℤ) + (-(j : ℤ) - 1) = -(j : ℤ) := by ring
    rw [hidx, zero_add, Int.cast_zero, add_zero, thetaFactor_zero_one] at hcoc
    rw [hcoc, mul_assoc] at hτ
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) hτ).symm

/-- Full lattice automorphy law for a theta section under any translation `z ↦ z + m + n * τ`. -/
theorem add_int_add_int_mul_tau_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    s (z + m + n * τ) = thetaFactor k τ α β m n z * s z := by
  have hsum : z + m + n * τ = (z + n * τ) + m := by ring
  rw [hsum, add_int_of_mem_thetaSections hs m (z + n * τ),
    add_int_mul_tau_of_mem_thetaSections hs n z, ← mul_assoc]
  have hcoc := thetaFactor_cocycle (k : ℤ) τ α β m 0 0 n z
  simpa using congrArg (· * s z) hcoc.symm

/-- Shifting the characteristics `(α, β)` by integers does not change the space of theta
sections. -/
theorem thetaSections_add_int (k : ℕ) (τ : ℂ) (α β : ℝ) (a b : ℤ) :
    thetaSections k τ (α + a) (β + b) = thetaSections k τ α β := by
  ext s
  have hα : cexp (2 * π * I * (α + a : ℝ)) = cexp (2 * π * I * α) := by
    simpa [thetaFactor_one_zero] using thetaFactor_add_int k τ α β a b 1 0 0
  have hβ : ∀ z : ℂ,
      cexp (2 * π * I * (β + b : ℝ) - π * I * k * τ - 2 * π * I * k * z) =
        cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) := fun z => by
    simpa [thetaFactor_zero_one] using thetaFactor_add_int k τ α β a b 0 1 z
  simp only [mem_thetaSections_iff, hα, hβ]

/-- Pointwise multiplication of theta sections adds levels and characteristics. -/
theorem mul_mem_thetaSections {k₁ k₂ : ℕ} {τ : ℂ} {α₁ β₁ α₂ β₂ : ℝ} {s₁ s₂ : ℂ → ℂ}
    (hs₁ : s₁ ∈ thetaSections k₁ τ α₁ β₁) (hs₂ : s₂ ∈ thetaSections k₂ τ α₂ β₂) :
    (fun z => s₁ z * s₂ z) ∈ thetaSections (k₁ + k₂) τ (α₁ + α₂) (β₁ + β₂) := by
  refine ⟨hs₁.1.mul hs₂.1, fun z => ?_, fun z => ?_⟩
  · dsimp only
    rw [hs₁.2.1, hs₂.2.1]
    have hmul := thetaFactor_add_level k₁ k₂ τ α₁ β₁ α₂ β₂ 1 0 z
    simp only [thetaFactor_one_zero] at hmul
    rw [hmul]
    ring
  · dsimp only
    rw [hs₁.2.2, hs₂.2.2]
    have hmul := thetaFactor_add_level k₁ k₂ τ α₁ β₁ α₂ β₂ 0 1 z
    simp only [thetaFactor_zero_one] at hmul
    push_cast at hmul ⊢
    rw [hmul]
    ring

/-! ### Twisted Fourier coefficients and Laurent expansion -/

/-- The `m`-th twisted Fourier coefficient of `s : ℂ → ℂ` with real shift `α`:
`thetaFourierCoeff α s m = ∫ t in 0..1, exp (-2πi(m + α)t) * s t`. -/
noncomputable def thetaFourierCoeff (α : ℝ) (s : ℂ → ℂ) (m : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, cexp (-2 * π * I * (m + α) * t) * s t

/-- Defining integral formula for `thetaFourierCoeff`. -/
theorem thetaFourierCoeff_def (α : ℝ) (s : ℂ → ℂ) (m : ℤ) :
    thetaFourierCoeff α s m = ∫ t in (0 : ℝ)..1, cexp (-2 * π * I * (m + α) * t) * s t :=
  (rfl)

/-- The twisted Fourier coefficients of the zero function vanish. -/
@[simp]
theorem thetaFourierCoeff_zero (α : ℝ) (m : ℤ) :
    thetaFourierCoeff α 0 m = 0 := by
  simp [thetaFourierCoeff_def]

/-- `thetaFourierCoeff` commutes with complex scalar multiplication. -/
@[simp]
theorem thetaFourierCoeff_smul (α : ℝ) (c : ℂ) (s : ℂ → ℂ) (m : ℤ) :
    thetaFourierCoeff α (c • s) m = c * thetaFourierCoeff α s m := by
  simp only [thetaFourierCoeff_def, Pi.smul_apply, smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- `thetaFourierCoeff` is additive on functions interval-integrable on `[0, 1]`. -/
theorem thetaFourierCoeff_add {α : ℝ} {s₁ s₂ : ℂ → ℂ}
    (hs₁ : IntervalIntegrable (fun t : ℝ => s₁ t) MeasureTheory.volume 0 1)
    (hs₂ : IntervalIntegrable (fun t : ℝ => s₂ t) MeasureTheory.volume 0 1) (m : ℤ) :
    thetaFourierCoeff α (s₁ + s₂) m = thetaFourierCoeff α s₁ m + thetaFourierCoeff α s₂ m := by
  have hexp : ContinuousOn (fun t : ℝ => cexp (-2 * π * I * (m + α) * t)) (uIcc (0 : ℝ) 1) :=
    (by fun_prop : Continuous fun t : ℝ => cexp (-2 * π * I * (m + α) * t)).continuousOn
  have h1 : IntervalIntegrable (fun t : ℝ => cexp (-2 * π * I * (m + α) * t) * s₁ t)
      MeasureTheory.volume 0 1 :=
    hs₁.continuousOn_mul hexp
  have h2 : IntervalIntegrable (fun t : ℝ => cexp (-2 * π * I * (m + α) * t) * s₂ t)
      MeasureTheory.volume 0 1 :=
    hs₂.continuousOn_mul hexp
  rw [thetaFourierCoeff_def, thetaFourierCoeff_def, thetaFourierCoeff_def,
    ← intervalIntegral.integral_add h1 h2]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [Pi.add_apply, mul_add]

private noncomputable def twistedPeriodic (α : ℝ) (s : ℂ → ℂ) (z : ℂ) : ℂ :=
  cexp (-2 * π * I * α * z) * s z

private noncomputable def twistedCusp (α : ℝ) (s : ℂ → ℂ) : ℂ → ℂ :=
  Function.Periodic.cuspFunction 1 (twistedPeriodic α s)

private lemma periodic_twistedPeriodic {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    Function.Periodic (twistedPeriodic α s) 1 := by
  intro z
  simp only [twistedPeriodic, h1]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private lemma twistedCusp_qParam {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (z : ℂ) :
    twistedCusp α s (Function.Periodic.qParam 1 z) = twistedPeriodic α s z :=
  Function.Periodic.eq_cuspFunction one_ne_zero (periodic_twistedPeriodic h1) z

private lemma differentiableOn_twistedCusp {α : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    DifferentiableOn ℂ (twistedCusp α s) (eball 0 ⊤ \ closedBall 0 0) := by
  have hdiff : Differentiable ℂ (twistedPeriodic α s) :=
    ((differentiable_id.const_mul _).cexp).mul hs
  intro w hw
  have hw0 : w ≠ 0 := fun h => hw.2 (by simp [h])
  have hq : Function.Periodic.qParam 1 (Function.Periodic.invQParam 1 w) = w :=
    Function.Periodic.qParam_right_inv one_ne_zero hw0
  rw [← hq]
  exact (Function.Periodic.differentiableAt_cuspFunction one_ne_zero
    (periodic_twistedPeriodic h1) (hdiff _)).differentiableWithinAt

private lemma thetaFourierCoeff_eq_circleLaurentCoeff {α : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (m : ℤ) :
    thetaFourierCoeff α s m = circleLaurentCoeff (twistedCusp α s) 0 1 m := by
  rw [circleLaurentCoeff_def, circleIntegral_sub_zpow_sub_one_smul _ 0 one_ne_zero (-m),
    smul_smul, smul_eq_mul]
  have hcoef : (2 * π * I : ℂ)⁻¹ * I = ((2 * π)⁻¹ : ℝ) := by
    have h2pi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
    push_cast
    field_simp [h2pi, I_ne_zero]
  rw [hcoef, ← Complex.real_smul]
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun θ : ℝ => circleMap 0 1 θ ^ (-m) • twistedCusp α s (circleMap 0 1 θ))
    (a := (0 : ℝ)) (b := 1) Real.two_pi_pos.ne'
  simp only [mul_zero, mul_one, smul_eq_mul] at hsub ⊢
  rw [← hsub, thetaFourierCoeff_def]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hcmap : circleMap 0 1 (2 * π * t) = Function.Periodic.qParam 1 (t : ℂ) := by
    simp only [circleMap, Function.Periodic.qParam, zero_add, ofReal_one, one_mul, div_one,
      ofReal_mul, ofReal_ofNat]
    congr 1
    ring
  rw [hcmap, twistedCusp_qParam h1, twistedPeriodic, Function.Periodic.qParam, ofReal_one, div_one,
    ← Complex.exp_int_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma hasLaurentSeriesOnAnnulus_twistedCusp {α : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    HasLaurentSeriesOnAnnulus (twistedCusp α s) (thetaFourierCoeff α s) 0 0 ⊤ := by
  have hL := (differentiableOn_twistedCusp hs h1).hasLaurentSeriesOnAnnulus le_rfl zero_lt_one
    (ENNReal.ofReal_lt_top)
  have hcoeff : circleLaurentCoeff (twistedCusp α s) 0 1 = thetaFourierCoeff α s :=
    funext fun m => (thetaFourierCoeff_eq_circleLaurentCoeff h1 m).symm
  rwa [hcoeff] at hL

/-- **Twisted Fourier expansion.** Every entire function `s : ℂ → ℂ` satisfying
`s (z + 1) = exp (2πiα) * s z` is the sum of its twisted Fourier series at every `z ∈ ℂ`. -/
theorem hasSum_thetaFourierCoeff {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (z : ℂ) :
    HasSum (fun m : ℤ => thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * z)) (s z) := by
  have hL := hasLaurentSeriesOnAnnulus_twistedCusp hs h1
  have hq : Function.Periodic.qParam 1 z ∈ eball 0 ⊤ \ closedBall 0 0 := by
    refine ⟨by simp, fun hmem => ?_⟩
    exact Function.Periodic.qParam_ne_zero z (by simpa using hmem)
  have hsum := (hL.hasSum hq).mul_left (cexp (2 * π * I * α * z))
  have hrhs : cexp (2 * π * I * α * z) * twistedCusp α s (Function.Periodic.qParam 1 z) = s z := by
    rw [twistedCusp_qParam h1, twistedPeriodic, ← mul_assoc, ← Complex.exp_add]
    simp
  rw [hrhs] at hsum
  refine hsum.congr_fun fun m => ?_
  simp only [sub_zero, smul_eq_mul, Function.Periodic.qParam, ofReal_one, div_one,
    ← Complex.exp_int_mul]
  symm
  calc
    cexp (2 * π * I * α * z) * (cexp ((m : ℂ) * (2 * π * I * z)) * thetaFourierCoeff α s m) =
        thetaFourierCoeff α s m * (cexp (2 * π * I * α * z) * cexp ((m : ℂ) * (2 * π * I * z))) :=
      by ring
    _ = thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * z) := by
      rw [← Complex.exp_add]
      congr 2
      ring

/-- The twisted Fourier coefficients of a quasi-periodic entire function decay faster than every
exponential weight `exp (-2πmy)`. -/
theorem summable_norm_thetaFourierCoeff_mul_exp {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (y : ℝ) :
    Summable (fun m : ℤ => ‖thetaFourierCoeff α s m‖ * Real.exp (-2 * π * m * y)) := by
  have hL := hasLaurentSeriesOnAnnulus_twistedCusp hs h1
  have hsum := hL.summable_norm_mul_zpow (ρ := Real.exp (-2 * π * y)) (Real.exp_pos _)
    (ENNReal.ofReal_lt_top)
  refine hsum.congr fun m => ?_
  congr 1
  exact Complex.ofReal_injective (by
    push_cast
    rw [← Complex.exp_int_mul]
    congr 1
    ring)

/-- The twisted Fourier coefficients of a quasi-periodic entire function are absolutely summable. -/
theorem summable_norm_thetaFourierCoeff {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    Summable (fun m : ℤ => ‖thetaFourierCoeff α s m‖) := by
  simpa using summable_norm_thetaFourierCoeff_mul_exp hs h1 0

/-- The twisted Fourier coefficients of any function `s : ℂ → ℂ` tend to `0` along the cofinite
filter on `ℤ` (by the Riemann–Lebesgue lemma). -/
theorem tendsto_thetaFourierCoeff_zero (α : ℝ) (s : ℂ → ℂ) :
    Tendsto (thetaFourierCoeff α s) cofinite (𝓝 0) := by
  let f : ℝ → ℂ := Set.indicator (Ioc (0 : ℝ) 1) fun t => cexp (-2 * π * I * α * t) * s t
  have htend : Tendsto (fun m : ℤ => (m : ℝ)) cofinite (cocompact ℝ) := by
    simpa [Filter.cocompact_eq_cofinite] using Int.isClosedEmbedding_coe_real.tendsto_cocompact
  refine ((Real.tendsto_integral_exp_smul_cocompact f).comp htend).congr fun m => ?_
  dsimp only [Function.comp_def, f]
  rw [thetaFourierCoeff_def, intervalIntegral.integral_of_le zero_le_one,
    ← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Ioc (0 : ℝ) 1
  · simp only [Set.indicator_of_mem ht, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
      ← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp [Set.indicator_of_notMem ht]

private lemma fourierCoeffOn_twistedPeriodic_eq_thetaFourierCoeff (α : ℝ) (s : ℂ → ℂ) (m : ℤ) :
    fourierCoeffOn zero_lt_one (fun t : ℝ => cexp (-2 * π * I * α * t) * s t) m =
      thetaFourierCoeff α s m := by
  rw [fourierCoeffOn_eq_integral, thetaFourierCoeff_def]
  simp only [sub_zero, div_one, one_smul]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [smul_eq_mul, fourier_coe_apply, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- An entire function whose twisted Fourier coefficients all vanish is identically zero. -/
theorem eq_zero_of_thetaFourierCoeff_eq_zero {α : ℝ} {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h0 : ∀ m : ℤ, thetaFourierCoeff α s m = 0) : s = 0 := by
  let f : ℝ → ℂ := fun t => cexp (-2 * π * I * α * t) * s t
  have hf_cont : Continuous f :=
    ((continuous_const.mul continuous_ofReal).cexp).mul (hs.continuous.comp continuous_ofReal)
  have hL2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hf_cont.aestronglyMeasurable).2
      ((hf_cont.norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  have hint : ∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2 = 0 := by
    have hparseval := tsum_sq_fourierCoeffOn zero_lt_one hL2
    simp_rw [f, fourierCoeffOn_twistedPeriodic_eq_thetaFourierCoeff, h0] at hparseval
    simpa [f] using hparseval.symm
  have hae : (fun x : ℝ => ‖f x‖ ^ 2) =ᵐ[MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      ((hf_cont.norm.pow 2).intervalIntegrable 0 1)).mp hint
  have hIoc : ∀ t ∈ Ioc (0 : ℝ) 1, s t = 0 := fun t ht => by
    have hnorm := MeasureTheory.volume.eqOn_Ioc_of_ae_eq hae
      (hf_cont.norm.pow 2).continuousOn continuousOn_const ht
    exact (mul_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))).resolve_left
      (Complex.exp_ne_zero _)
  have hcl : ((1 / 2 : ℝ) : ℂ) ∈ closure ({z : ℂ | s z = 0} \ {((1 / 2 : ℝ) : ℂ)}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (1 / 4) (ε / 2)
    have hδpos : 0 < δ := lt_min (by norm_num) (half_pos hε)
    have hδle1 : δ ≤ 1 / 4 := min_le_left _ _
    have hδle2 : δ ≤ ε / 2 := min_le_right _ _
    refine ⟨(((1 / 2 : ℝ) + δ : ℝ) : ℂ), ⟨hIoc _ ⟨by linarith, by linarith⟩, ?_⟩, ?_⟩
    · intro hEq
      linarith [Complex.ofReal_injective (Set.mem_singleton_iff.mp hEq)]
    · rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
      have : (1 / 2 : ℝ) - ((1 / 2 : ℝ) + δ) = -δ := by ring
      rw [this, norm_neg, Real.norm_of_nonneg hδpos.le]
      linarith
  ext z
  exact (analyticOnNhd_univ_iff_differentiable.mpr hs).eqOn_zero_of_preconnected_of_mem_closure
    isPreconnected_univ (mem_univ _) hcl (mem_univ z)

private lemma twistedCusp_mul_qParam_eq {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    {w : ℂ} (hw0 : w ≠ 0) :
    twistedCusp α s (Function.Periodic.qParam 1 τ * w) =
      cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) * w ^ (-(k : ℤ)) *
        twistedCusp α s w := by
  set z := Function.Periodic.invQParam 1 w
  have hqz : Function.Periodic.qParam 1 z = w := Function.Periodic.qParam_right_inv one_ne_zero hw0
  have hqadd : Function.Periodic.qParam 1 τ * w = Function.Periodic.qParam 1 (z + τ) := by
    rw [← hqz]
    simp only [Function.Periodic.qParam, ofReal_one, div_one, ← Complex.exp_add]
    congr 1
    ring
  rw [hqadd, twistedCusp_qParam h1, twistedPeriodic, hτ z, ← hqz, twistedCusp_qParam h1,
    twistedPeriodic, Function.Periodic.qParam, ofReal_one, div_one, ← Complex.exp_int_mul]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma hasLaurentSeriesOnAnnulus_twistedCusp_mul_qParam_shift {k : ℕ} {τ : ℂ} {α β : ℝ}
    {s : ℂ → ℂ} (hs : Differentiable ℂ s)
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) :
    HasLaurentSeriesOnAnnulus (fun w => twistedCusp α s (Function.Periodic.qParam 1 τ * w))
      (fun n : ℤ =>
        cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) *
          thetaFourierCoeff α s (n + k)) 0 0 ⊤ := by
  have hL := hasLaurentSeriesOnAnnulus_twistedCusp hs h1
  refine ⟨le_rfl, ENNReal.ofReal_lt_top, fun {w} hw => ?_⟩
  have hw0 : w ≠ 0 := fun h => hw.2 (by simp [h])
  rw [twistedCusp_mul_qParam_eq h1 hτ hw0]
  have hmul := (hL.hasSum hw).mul_left
    (cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) * w ^ (-(k : ℤ)))
  rw [← (Equiv.addRight (k : ℤ)).hasSum_iff] at hmul
  refine hmul.congr_fun fun n => ?_
  simp only [Function.comp_def, Equiv.coe_addRight, sub_zero, smul_eq_mul]
  have hzpow : w ^ (-(k : ℤ)) * w ^ (n + (k : ℤ)) = w ^ n := by
    rw [← zpow_add₀ hw0]
    congr 1
    ring
  calc
    w ^ n * (cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) *
        thetaFourierCoeff α s (n + k)) =
        (w ^ (-(k : ℤ)) * w ^ (n + (k : ℤ))) *
          (cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) *
            thetaFourierCoeff α s (n + k)) := by rw [hzpow]
    _ = cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) * w ^ (-(k : ℤ)) *
          (w ^ (n + (k : ℤ)) * thetaFourierCoeff α s (n + k)) := by ring

private lemma thetaSections_tau_to_recurrence {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    (m : ℤ) :
    thetaFourierCoeff α s (m + k) =
      cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
        thetaFourierCoeff α s m := by
  have hL := hasLaurentSeriesOnAnnulus_twistedCusp hs h1
  have hL₁ : HasLaurentSeriesOnAnnulus
      (fun w => twistedCusp α s (Function.Periodic.qParam 1 τ * w))
      (fun n : ℤ => Function.Periodic.qParam 1 τ ^ n * thetaFourierCoeff α s n) 0 0 ⊤ := by
    refine ⟨le_rfl, ENNReal.ofReal_lt_top, fun {w} hw => ?_⟩
    have hw0 : w ≠ 0 := fun h => hw.2 (by simp [h])
    have hqw : Function.Periodic.qParam 1 τ * w ∈ eball 0 ⊤ \ closedBall 0 0 :=
      ⟨by simp, fun h => mul_ne_zero (Function.Periodic.qParam_ne_zero τ) hw0 (by simpa using h)⟩
    refine (hL.hasSum hqw).congr_fun fun n => ?_
    simp only [sub_zero, smul_eq_mul, mul_zpow]
    ring
  have hL₂ := hasLaurentSeriesOnAnnulus_twistedCusp_mul_qParam_shift hs h1 hτ
  have hm := congrFun (hL₁.coeff_unique hL₂) m
  have hinv : cexp (2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ) *
      cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) = 1 := by
    rw [← Complex.exp_add]
    have : 2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ +
        (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) = 0 := by ring
    rw [this, Complex.exp_zero]
  have hsol := congrArg (cexp (2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ) * ·) hm.symm
  rw [← mul_assoc, hinv, one_mul] at hsol
  rw [hsol]
  simp only [Function.Periodic.qParam, ofReal_one, div_one, ← Complex.exp_int_mul, ← mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

/-- **Fourier recurrence characterization.** For an entire function `s` satisfying
`s (z + 1) = exp (2πiα) * s z`, the second automorphy relation
`s (z + τ) = exp (2πiβ - πikτ - 2πikz) * s z` holds for all `z ∈ ℂ` if and only if its twisted
Fourier coefficients satisfy `c (m + k) = exp (2πi(m + α)τ - 2πiβ + πikτ) * c m` for all
`m ∈ ℤ`. -/
theorem thetaSections_tau_iff_recurrence {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : Differentiable ℂ s) (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) :
    (∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) ↔
      ∀ m : ℤ, thetaFourierCoeff α s (m + k) =
        cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
          thetaFourierCoeff α s m := by
  refine ⟨fun hτ m => thetaSections_tau_to_recurrence hs h1 hτ m, fun hrec z => ?_⟩
  have hL := hasSum_thetaFourierCoeff hs h1 (z + τ)
  have hR := (hasSum_thetaFourierCoeff hs h1 z).mul_left
    (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z))
  rw [← (Equiv.addRight (k : ℤ)).hasSum_iff] at hR
  have hR' : HasSum
      (fun m : ℤ => thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * (z + τ)))
      (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) := by
    refine hR.congr_fun fun m => ?_
    simp only [Function.comp_def, Equiv.coe_addRight, hrec m]
    calc
      thetaFourierCoeff α s m * cexp (2 * π * I * (m + α) * (z + τ)) =
          thetaFourierCoeff α s m *
            (cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
              cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
              cexp (2 * π * I * ((m + k : ℤ) + α) * z)) := by
        simp only [← Complex.exp_add]
        congr 2
        push_cast
        ring
      _ = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
            (cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
              thetaFourierCoeff α s m * cexp (2 * π * I * ((m + k : ℤ) + α) * z)) := by ring
  exact hL.unique hR'

/-! ### Vanishing for `τ.im ≤ 0` and metric descent -/

private lemma norm_thetaFourierCoeff_add_level {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n : ℤ) :
    ‖thetaFourierCoeff α s (n + k)‖ =
      Real.exp (-2 * π * ((n : ℝ) + α + (k : ℝ) / 2) * τ.im) * ‖thetaFourierCoeff α s n‖ := by
  have hrec := (thetaSections_tau_iff_recurrence hs.1 hs.2.1).mp hs.2.2 n
  rw [hrec, norm_mul, Complex.norm_exp]
  congr 2
  have hre :
      (2 * π * I * ((n : ℂ) + α) * τ - 2 * π * I * β + π * I * k * τ).re =
        ((2 * π * ((n : ℝ) + α) + π * k : ℝ) * (I * τ) - (2 * π * β : ℝ) * I).re := by
    congr 1
    push_cast
    ring
  rw [hre]
  simp only [sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
    zero_sub, mul_one, mul_im]
  ring

/-- When `k > 0` and `τ.im ≤ 0`, there are no nonzero holomorphic theta sections. -/
theorem thetaSections_eq_bot_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : thetaSections k τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  refine eq_zero_of_thetaFourierCoeff_eq_zero (α := α) hs.1 fun m => ?_
  have hrec := (thetaSections_tau_iff_recurrence hs.1 hs.2.1).mp hs.2.2
  have hzero_ge : ∀ n : ℤ, 0 ≤ (n : ℝ) + α + (k : ℝ) / 2 → thetaFourierCoeff α s n = 0 := by
    intro n hn
    have hle : ∀ j : ℕ, ‖thetaFourierCoeff α s n‖ ≤ ‖thetaFourierCoeff α s (n + j * k)‖ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hidx : n + ((j + 1 : ℕ) : ℤ) * k = (n + j * k) + k := by push_cast; ring
        rw [hidx, norm_thetaFourierCoeff_add_level hs]
        have hpos : 0 ≤ ((n + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2 := by
          push_cast
          have hjk : (0 : ℝ) ≤ (j : ℝ) * (k : ℝ) := by positivity
          linarith
        have harg : 0 ≤ -2 * π * (((n + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2) * τ.im :=
          mul_nonneg_of_nonpos_of_nonpos (by nlinarith [Real.pi_pos, hpos]) hτ
        exact ih.trans (le_mul_of_one_le_left (norm_nonneg _) (Real.one_le_exp harg))
    have hinj : Function.Injective (fun j : ℕ => n + (j : ℤ) * k) := fun j₁ j₂ h => by
      have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
      exact Int.ofNat.inj (mul_right_cancel₀ hk0 (add_left_cancel h))
    have htend : Tendsto (fun j : ℕ => ‖thetaFourierCoeff α s (n + j * k)‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, norm_zero] using
        (tendsto_thetaFourierCoeff_zero α s).norm.comp
          (Nat.cofinite_eq_atTop ▸ hinj.tendsto_cofinite)
    have hnorm0 : ‖thetaFourierCoeff α s n‖ ≤ 0 :=
      le_of_tendsto_of_tendsto' tendsto_const_nhds htend hle
    exact norm_eq_zero.mp (le_antisymm hnorm0 (norm_nonneg _))
  obtain ⟨j, hj⟩ := exists_nat_gt (-(m : ℝ) - α - (k : ℝ) / 2)
  have hge : 0 ≤ ((m + (j : ℤ) * (k : ℤ) : ℤ) : ℝ) + α + (k : ℝ) / 2 := by
    push_cast
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hj0 : thetaFourierCoeff α s (m + j * k) = 0 := hzero_ge _ hge
  clear hj hge
  induction j with
  | zero => simpa using hj0
  | succ j ih =>
    have hidx : m + ((j + 1 : ℕ) : ℤ) * k = (m + j * k) + k := by push_cast; ring
    rw [hidx, hrec, mul_eq_zero] at hj0
    exact ih (hj0.resolve_left (Complex.exp_ne_zero _))

/-- For positive level `k > 0` and `τ.im ≤ 0`, `thetaSections k τ α β` has dimension `0`. -/
theorem finrank_thetaSections_of_im_nonpos (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : τ.im ≤ 0)
    (α β : ℝ) : Module.finrank ℂ (thetaSections k τ α β) = 0 := by
  rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, finrank_bot]

/-- For every theta section `s`, the pointwise Hermitian norm squared `thetaMetric k τ z * ‖s z‖²`
is doubly periodic on the lattice `ℤ + τℤ`. -/
theorem thetaMetric_mul_norm_sq_add_int_add_int_mul_tau {k : ℕ} {τ : ℂ}
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖s (z + m + n * τ)‖ ^ 2 =
      thetaMetric k τ z * ‖s z‖ ^ 2 := by
  by_cases hτ : τ.im = 0
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [add_int_add_int_mul_tau_of_mem_thetaSections hs m n z, norm_mul, mul_pow,
        norm_thetaFactor]
      simp [thetaMetric_def]
    · rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ.le α β, Submodule.mem_bot] at hs
      simp [hs]
  · rw [add_int_add_int_mul_tau_of_mem_thetaSections hs m n z, norm_mul, mul_pow, ← mul_assoc]
    have hm := thetaMetric_add_int_add_int_mul_tau (k : ℤ) hτ α β m n z
    rw [Int.cast_natCast] at hm
    rw [hm]

/-! ### Characteristic theta basis functions -/

/-- The `r`-th level-`k` characteristic theta function with characteristics `(α, β)`, built from
Mathlib's two-variable Jacobi theta function `jacobiTheta₂`:
`characteristicTheta k τ α β r z = exp (2πi(r + α)z) * jacobiTheta₂ (kz + (r + α)τ - β) (kτ)`. -/
noncomputable def characteristicTheta (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (r + α) * z) * jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ)

/-- Defining formula for `characteristicTheta`. -/
theorem characteristicTheta_def (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r z =
      cexp (2 * π * I * (r + α) * z) * jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) :=
  (rfl)

/-- At level `k = 1`, zero characteristics, and `r = 0`, `characteristicTheta` reduces to
`jacobiTheta₂`. -/
@[simp]
theorem characteristicTheta_one_zero (τ z : ℂ) :
    characteristicTheta 1 τ 0 0 0 z = jacobiTheta₂ z τ := by
  simp [characteristicTheta_def]

/-- When `k = 0` or `τ.im ≤ 0`, `characteristicTheta` vanishes identically (inheriting the
junk-value convention `jacobiTheta₂_undef`). -/
theorem characteristicTheta_undef {k : ℕ} {τ : ℂ} (h : k = 0 ∨ τ.im ≤ 0) (α β : ℝ) (r : ℤ)
    (z : ℂ) : characteristicTheta k τ α β r z = 0 := by
  have him : (k * τ).im ≤ 0 := by
    rw [show (k : ℂ) * τ = ((k : ℝ) : ℂ) * τ by norm_cast, im_ofReal_mul]
    rcases h with rfl | hτ
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hτ
  simp [characteristicTheta_def, jacobiTheta₂_undef _ him]

/-- First generator automorphy law for `characteristicTheta`. -/
theorem characteristicTheta_add_one (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r (z + 1) =
      cexp (2 * π * I * α) * characteristicTheta k τ α β r z := by
  have hper : Function.Periodic (jacobiTheta₂ · (k * τ)) 1 := fun w => jacobiTheta₂_add_left w _
  have hshift :
      jacobiTheta₂ (k * (z + 1) + (r + α) * τ - β) (k * τ) =
        jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ) := by
    have harg : k * (z + 1) + (r + α) * τ - β = (k * z + (r + α) * τ - β) + (k : ℕ) * (1 : ℂ) := by
      ring
    rw [harg]
    exact hper.nat_mul k _
  rw [characteristicTheta_def, characteristicTheta_def, hshift, ← mul_assoc]
  congr 1
  have hr : cexp ((r : ℂ) * (2 * π * I)) = 1 := Complex.exp_int_mul_two_pi_mul_I r
  conv_rhs => rw [← Complex.exp_add, ← one_mul (cexp _), ← hr, ← Complex.exp_add]
  congr 1
  ring

/-- Second generator automorphy law for `characteristicTheta`. -/
theorem characteristicTheta_add_tau (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β r (z + τ) =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) *
        characteristicTheta k τ α β r z := by
  have harg : k * (z + τ) + (r + α) * τ - β = (k * z + (r + α) * τ - β) + k * τ := by ring
  rw [characteristicTheta_def, characteristicTheta_def, harg, jacobiTheta₂_add_left']
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

/-- Shifting the characteristic index `r` by the level `k` multiplies `characteristicTheta` by a
nonzero scalar depending only on `(k, τ, α, β, r)`. -/
theorem characteristicTheta_add_level (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    characteristicTheta k τ α β (r + k) z =
      cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * (r + α) * τ) *
        characteristicTheta k τ α β r z := by
  have harg : k * z + ((r + k : ℤ) + α) * τ - β = (k * z + (r + α) * τ - β) + k * τ := by
    push_cast
    ring
  rw [characteristicTheta_def, characteristicTheta_def, harg, jacobiTheta₂_add_left', ← mul_assoc,
    ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every `characteristicTheta k τ α β r` is an entire function of `z` (for all `k : ℕ` and
`τ : ℂ`). -/
theorem differentiable_characteristicTheta (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) :
    Differentiable ℂ (characteristicTheta k τ α β r) := by
  rcases le_or_gt (k * τ).im 0 with him | him
  · have hzero : characteristicTheta k τ α β r = 0 := by
      ext z
      simp [characteristicTheta_def, jacobiTheta₂_undef _ him]
    rw [hzero]
    exact differentiable_const 0
  · refine ((differentiable_id.const_mul _).cexp).mul fun z => ?_
    exact (differentiableAt_jacobiTheta₂_fst _ him).comp z
      (((differentiableAt_id.const_mul _).add_const _).sub_const _)

/-- Every characteristic theta function belongs to `thetaSections k τ α β`. -/
theorem characteristicTheta_mem_thetaSections (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) :
    characteristicTheta k τ α β r ∈ thetaSections k τ α β :=
  ⟨differentiable_characteristicTheta k τ α β r, characteristicTheta_add_one k τ α β r,
    characteristicTheta_add_tau k τ α β r⟩

/-- Mathlib's `jacobiTheta₂ · τ` is a level-`1` theta section with zero characteristics for every
`τ : ℂ`. -/
theorem jacobiTheta₂_mem_thetaSections (τ : ℂ) :
    (fun z => jacobiTheta₂ z τ) ∈ thetaSections 1 τ 0 0 := by
  have hfun : (fun z => jacobiTheta₂ z τ) = characteristicTheta 1 τ 0 0 0 :=
    funext fun z => (characteristicTheta_one_zero τ z).symm
  rw [hfun]
  exact characteristicTheta_mem_thetaSections 1 τ 0 0 0

/-- Explicit `ℤ`-indexed Fourier series of `characteristicTheta k τ α β r` supported on the
congruence class `r + kℤ`, for `0 < k` and `0 < τ.im`. -/
theorem hasSum_characteristicTheta {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r : ℤ) (z : ℂ) :
    HasSum
      (fun n : ℤ =>
        cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ) *
          cexp (2 * π * I * ((r + n * k : ℤ) + α) * z))
      (characteristicTheta k τ α β r z) := by
  have hkτ : 0 < (k * τ).im := by
    rw [show (k : ℂ) * τ = ((k : ℝ) : ℂ) * τ by norm_cast, im_ofReal_mul]
    exact mul_pos (Nat.cast_pos.mpr hk) hτ
  have hsum := (hasSum_jacobiTheta₂_term (k * z + (r + α) * τ - β) hkτ).mul_left
    (cexp (2 * π * I * (r + α) * z))
  rw [← characteristicTheta_def] at hsum
  refine hsum.congr_fun fun n => ?_
  simp only [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma hasLaurentSeriesOnAnnulus_twistedCusp_characteristicTheta {k : ℕ} (hk : 0 < k)
    {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) (r : ℤ) :
    HasLaurentSeriesOnAnnulus (twistedCusp α (characteristicTheta k τ α β r))
      (fun m' : ℤ =>
        if (k : ℤ) ∣ m' - r then
          let n : ℤ := (m' - r) / k
          cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ)
        else 0) 0 0 ⊤ := by
  have hs := characteristicTheta_mem_thetaSections k τ α β r
  refine ⟨le_rfl, ENNReal.ofReal_lt_top, fun {w} hw => ?_⟩
  have hw0 : w ≠ 0 := fun h => hw.2 (by simp [h])
  set z := Function.Periodic.invQParam 1 w
  have hqz : Function.Periodic.qParam 1 z = w :=
    Function.Periodic.qParam_right_inv one_ne_zero hw0
  have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have hsub : HasSum
      (fun n : ℤ =>
        (w - 0) ^ (r + n * (k : ℤ)) •
          (if (k : ℤ) ∣ (r + n * k) - r then
            let q : ℤ := ((r + n * k) - r) / k
            cexp (2 * π * I * q * ((r + α) * τ - β) + π * I * k * q ^ 2 * τ)
          else 0))
      (twistedCusp α (characteristicTheta k τ α β r) w) := by
    rw [← hqz, twistedCusp_qParam hs.2.1, twistedPeriodic]
    have hchar := (hasSum_characteristicTheta hk hτ α β r z).mul_left (cexp (-2 * π * I * α * z))
    refine hchar.congr_fun fun n => ?_
    have hdvd : (k : ℤ) ∣ (r + n * k) - r := by
      rw [add_sub_cancel_left]
      exact dvd_mul_left (k : ℤ) n
    have hdiv : ((r + n * (k : ℤ)) - r) / (k : ℤ) = n := by
      rw [add_sub_cancel_left, Int.mul_ediv_cancel n hk0]
    simp only [hdvd, ↓reduceIte, hdiv, sub_zero, smul_eq_mul,
      Function.Periodic.qParam, ofReal_one, div_one, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hinj : Function.Injective (fun n : ℤ => r + n * (k : ℤ)) := fun _ _ h =>
    mul_right_cancel₀ hk0 (add_left_cancel h)
  refine (hinj.hasSum_iff fun m' hm' => ?_).mp hsub
  have hndvd : ¬ (k : ℤ) ∣ m' - r := by
    rintro ⟨n, hn⟩
    exact hm' ⟨n, by linarith⟩
  simp [hndvd]

private lemma thetaFourierCoeff_characteristicTheta_eq {k : ℕ} (hk : 0 < k) {τ : ℂ}
    (hτ : 0 < τ.im) (α β : ℝ) (r m : ℤ) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) m =
      if (k : ℤ) ∣ m - r then
        let n : ℤ := (m - r) / k
        cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ)
      else 0 := by
  have hs := characteristicTheta_mem_thetaSections k τ α β r
  have hL₁ := hasLaurentSeriesOnAnnulus_twistedCusp hs.1 hs.2.1
  have hL₂ := hasLaurentSeriesOnAnnulus_twistedCusp_characteristicTheta hk hτ α β r
  exact congrFun (hL₁.coeff_unique hL₂) m

/-- On the congruence class `r + kℤ`, the twisted Fourier coefficients of `characteristicTheta`
are given by the explicit Gaussian exponentials. -/
theorem thetaFourierCoeff_characteristicTheta_add_mul {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (r n : ℤ) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) (r + n * k) =
      cexp (2 * π * I * n * ((r + α) * τ - β) + π * I * k * n ^ 2 * τ) := by
  have hk0 : (k : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hk.ne'
  have hdvd : (k : ℤ) ∣ (r + n * k) - r := by
    rw [add_sub_cancel_left]
    exact dvd_mul_left (k : ℤ) n
  have hdiv : ((r + n * (k : ℤ)) - r) / (k : ℤ) = n := by
    rw [add_sub_cancel_left, Int.mul_ediv_cancel n hk0]
  rw [thetaFourierCoeff_characteristicTheta_eq hk hτ α β r (r + n * k)]
  simp only [hdvd, ↓reduceIte, hdiv]

/-- Off the congruence class `r + kℤ`, all twisted Fourier coefficients of `characteristicTheta`
vanish. -/
theorem thetaFourierCoeff_characteristicTheta_eq_zero (k : ℕ) (τ : ℂ) (α β : ℝ) {r m : ℤ}
    (h : ¬ (k : ℤ) ∣ m - r) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) m = 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hzero : characteristicTheta 0 τ α β r = 0 :=
      funext fun z => characteristicTheta_undef (Or.inl rfl) α β r z
    simp [hzero]
  · rcases le_or_gt τ.im 0 with hτ | hτ
    · have hzero : characteristicTheta k τ α β r = 0 :=
        funext fun z => characteristicTheta_undef (Or.inr hτ) α β r z
      simp [hzero]
    · rw [thetaFourierCoeff_characteristicTheta_eq hk hτ α β r m, ite_eq_right h]

/-- Duality between the `k` characteristic theta functions and the first `k` twisted Fourier
coefficients. -/
@[simp]
theorem thetaFourierCoeff_characteristicTheta_fin {k : ℕ} {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (r r' : Fin k) :
    thetaFourierCoeff α (characteristicTheta k τ α β r) r' = if r' = r then 1 else 0 := by
  by_cases hrr : r' = r
  · subst hrr
    simpa using thetaFourierCoeff_characteristicTheta_add_mul r'.pos hτ α β (r' : ℤ) 0
  · rw [ite_eq_right hrr]
    refine thetaFourierCoeff_characteristicTheta_eq_zero k τ α β ?_
    rintro ⟨q, hq⟩
    have hr1 : (r : ℤ) < k := Int.ofNat_lt.mpr r.isLt
    have hr2 : (r' : ℤ) < k := Int.ofNat_lt.mpr r'.isLt
    have hq0 : q = 0 := by nlinarith [Int.natCast_nonneg r.1, Int.natCast_nonneg r'.1]
    rw [hq0, mul_zero] at hq
    have heq : (r' : ℤ) = r := sub_eq_zero.mp hq
    exact hrr (Fin.ext (Int.ofNat.inj heq))

/-! ### Explicit basis and dimension `k` -/

private lemma thetaFourierCoeff_eq_zero_of_fin_eq_zero {k : ℕ} (hk : 0 < k) {τ : ℂ} {α β : ℝ}
    {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β)
    (hfin : ∀ r : Fin k, thetaFourierCoeff α s r = 0) (m : ℤ) :
    thetaFourierCoeff α s m = 0 := by
  have hrec := (thetaSections_tau_iff_recurrence hs.1 hs.2.1).mp hs.2.2
  have hstep : ∀ n : ℤ, thetaFourierCoeff α s (n + k) = 0 ↔ thetaFourierCoeff α s n = 0 :=
    fun n => by rw [hrec n, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _)]
  have hshift : ∀ (r : ℤ) (q : ℤ),
      thetaFourierCoeff α s r = 0 → thetaFourierCoeff α s (r + q * k) = 0 := by
    intro r q hr
    refine Int.induction_on q (by simpa using hr) (fun j ih => ?_) (fun j ih => ?_)
    · have : r + ((j : ℤ) + 1) * k = (r + j * k) + k := by ring
      rw [this, hstep]
      exact ih
    · have : (r + (-(j : ℤ) - 1) * k) + k = r + (-(j : ℤ)) * k := by ring
      exact (hstep _).mp (this.symm ▸ ih)
  have hkpos : (0 : ℤ) < k := Int.natCast_pos.mpr hk
  have hrem_nn : 0 ≤ m % (k : ℤ) := Int.emod_nonneg m hkpos.ne'
  have hrem_lt : m % (k : ℤ) < k := Int.emod_lt_of_pos m hkpos
  let r : Fin k := ⟨(m % (k : ℤ)).toNat, by omega⟩
  have hr_cast : (r : ℤ) = m % (k : ℤ) := Int.toNat_of_nonneg hrem_nn
  have hm : m = r + (m / (k : ℤ)) * k := by
    rw [hr_cast, mul_comm]
    exact (Int.emod_add_mul_ediv m (k : ℤ)).symm
  rw [hm]
  exact hshift r (m / (k : ℤ)) (hfin r)

private noncomputable def thetaSectionsEquivFun (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : 0 < τ.im)
    (α β : ℝ) : thetaSections k τ α β ≃ₗ[ℂ] (Fin k → ℂ) :=
  let toLin : thetaSections k τ α β →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun s r => thetaFourierCoeff α s.1 r
      map_add' := fun s₁ s₂ => funext fun r =>
        thetaFourierCoeff_add ((s₁.2.1.continuous.comp continuous_ofReal).intervalIntegrable 0 1)
          ((s₂.2.1.continuous.comp continuous_ofReal).intervalIntegrable 0 1) r
      map_smul' := fun c s => funext fun r => thetaFourierCoeff_smul α c s.1 r }
  let inv : (Fin k → ℂ) → thetaSections k τ α β :=
    fun v => ∑ r : Fin k, v r • ⟨characteristicTheta k τ α β r,
      characteristicTheta_mem_thetaSections k τ α β r⟩
  have hright : Function.RightInverse inv toLin := fun v => by
    ext r'
    simp only [inv, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      toLin, LinearMap.coe_mk, AddHom.coe_mk, thetaFourierCoeff_characteristicTheta_fin hτ]
    simp
  LinearEquiv.ofLinearMap toLin
    { toFun := inv
      map_add' := fun v w => by
        simp only [inv, Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [inv, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
    (LinearMap.ext fun v => hright v)
    (LinearMap.ext fun s => by
      have hdiff : toLin (inv (toLin s) - s) = 0 := by
        rw [map_sub, hright (toLin s), sub_self]
      have hfin : ∀ r : Fin k, thetaFourierCoeff α (inv (toLin s) - s).1 r = 0 :=
        fun r => congrFun hdiff r
      have hzero : (inv (toLin s) - s).1 = 0 :=
        eq_zero_of_thetaFourierCoeff_eq_zero (inv (toLin s) - s).2.1
          (thetaFourierCoeff_eq_zero_of_fin_eq_zero hk (inv (toLin s) - s).2 hfin)
      exact sub_eq_zero.mp (Subtype.ext hzero))

/-- For `0 < k` and `0 < τ.im`, the `k` characteristic theta functions
`characteristicTheta k τ α β r` (`r : Fin k`) form a `ℂ`-basis of `thetaSections k τ α β`, with
coordinates given by the first `k` twisted Fourier coefficients. -/
noncomputable def thetaSectionsBasis (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ) :
    Module.Basis (Fin k) ℂ (thetaSections k τ α β) :=
  Module.Basis.ofEquivFun (thetaSectionsEquivFun k hk τ hτ α β)

/-- The `r`-th basis vector of `thetaSectionsBasis` is `characteristicTheta k τ α β r`. -/
@[simp]
theorem coe_thetaSectionsBasis (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ)
    (r : Fin k) :
    (thetaSectionsBasis k hk τ hτ α β r : ℂ → ℂ) = characteristicTheta k τ α β r := by
  have h := congrFun (Module.Basis.coe_ofEquivFun (thetaSectionsEquivFun k hk τ hτ α β)) r
  rw [thetaSectionsBasis, h]
  simp [thetaSectionsEquivFun, Pi.single_apply]

/-- The `r`-th coordinate of a section in `thetaSectionsBasis` is its `r`-th twisted Fourier
coefficient. -/
@[simp]
theorem thetaSectionsBasis_repr (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ)
    (s : thetaSections k τ α β) (r : Fin k) :
    (thetaSectionsBasis k hk τ hτ α β).repr s r = thetaFourierCoeff α (s : ℂ → ℂ) r :=
  Module.Basis.ofEquivFun_repr_apply (thetaSectionsEquivFun k hk τ hτ α β) s r

/-- Every level-`k` theta section (`0 < k`) is the finite linear combination of the `k`
characteristic theta functions weighted by its first `k` twisted Fourier coefficients. -/
theorem eq_sum_characteristicTheta_of_mem_thetaSections {k : ℕ} (hk : 0 < k) {τ : ℂ}
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s z = ∑ r : Fin k, thetaFourierCoeff α s r * characteristicTheta k τ α β r z := by
  rcases lt_or_ge 0 τ.im with hτ | hτ
  · have hrepr := (thetaSectionsBasis k hk τ hτ α β).sum_repr ⟨s, hs⟩
    have hval := congrFun (congrArg Subtype.val hrepr.symm) z
    simpa [Submodule.coe_sum, Finset.sum_apply, smul_eq_mul] using hval
  · rw [thetaSections_eq_bot_of_im_nonpos k hk τ hτ α β, Submodule.mem_bot] at hs
    simp [hs]

/-- **Dimension of the space of level-`k` theta sections.** For every positive level `k > 0`,
period `τ` in the upper half-plane (`0 < τ.im`), and real characteristics `(α, β)`, the space
`thetaSections k τ α β` has complex dimension `k`. -/
theorem finrank_thetaSections (k : ℕ) (hk : 0 < k) (τ : ℂ) (hτ : 0 < τ.im) (α β : ℝ) :
    Module.finrank ℂ (thetaSections k τ α β) = k := by
  simpa using Module.finrank_eq_card_basis (thetaSectionsBasis k hk τ hτ α β)

/-! ### Level-`0` classification -/

private lemma thetaFourierCoeff_zero_level_eq_zero_of_ne {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    {s : ℂ → ℂ} (hs : s ∈ thetaSections 0 τ α β) {m : ℤ} (hm : thetaFourierCoeff α s m ≠ 0) :
    (m : ℝ) + α = 0 ∧ ∃ b : ℤ, (b : ℝ) = β := by
  have hrec := (thetaSections_tau_iff_recurrence hs.1 hs.2.1).mp hs.2.2 m
  simp only [Nat.cast_zero, add_zero, mul_zero, zero_mul] at hrec
  have hexp : cexp (2 * π * I * (m + α) * τ - 2 * π * I * β) = 1 :=
    mul_right_cancel₀ hm (by simpa using hrec.symm)
  have hnorm_eq := norm_thetaFourierCoeff_add_level hs m
  simp only [Nat.cast_zero, add_zero, zero_div] at hnorm_eq
  have hnorm : Real.exp (-2 * π * ((m : ℝ) + α) * τ.im) = 1 :=
    mul_right_cancel₀ (norm_ne_zero_iff.mpr hm) (by simpa using hnorm_eq.symm)
  have hma : (m : ℝ) + α = 0 := by
    have hmul : -2 * π * ((m : ℝ) + α) * τ.im = 0 :=
      Real.exp_injective (by simpa using hnorm)
    have hne : -2 * π * τ.im ≠ 0 :=
      mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) Real.pi_pos.ne') hτ
    have : (-2 * π * τ.im) * ((m : ℝ) + α) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hne
  have hmaC : ((m : ℂ) + α) = 0 := by exact_mod_cast hma
  rw [hmaC, mul_zero, zero_mul, zero_sub] at hexp
  obtain ⟨b, hb⟩ := Complex.exp_eq_one_iff.mp hexp
  have hmul : (-β : ℂ) * (2 * π * I) = (b : ℂ) * (2 * π * I) := by
    calc
      (-β : ℂ) * (2 * π * I) = -(2 * π * I * β) := by ring
      _ = (b : ℂ) * (2 * π * I) := hb
  have hR : -β = (b : ℝ) := by exact_mod_cast mul_right_cancel₀ two_pi_I_ne_zero hmul
  exact ⟨hma, -b, by push_cast; linarith⟩

/-- At level `k = 0` with `τ.im ≠ 0` and integer characteristics `(α, β) ∈ ℤ × ℤ`, the theta
sections are precisely the constant functions. -/
theorem mem_thetaSections_zero_iff_const {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    (hα : ∃ a : ℤ, (a : ℝ) = α) (hβ : ∃ b : ℤ, (b : ℝ) = β) {s : ℂ → ℂ} :
    s ∈ thetaSections 0 τ α β ↔ ∃ c : ℂ, s = fun _ => c := by
  rcases hα with ⟨a, rfl⟩
  rcases hβ with ⟨b, rfl⟩
  constructor
  · intro hs
    refine ⟨thetaFourierCoeff a s (-a), ?_⟩
    ext z
    have hsum := hasSum_thetaFourierCoeff hs.1 hs.2.1 z
    have hsingle : HasSum
        (fun m : ℤ => thetaFourierCoeff a s m * cexp (2 * π * I * (m + a) * z))
        (thetaFourierCoeff a s (-a)) := by
      have hterm : thetaFourierCoeff a s (-a) * cexp (2 * π * I * (((-a : ℤ) : ℂ) + a) * z) =
          thetaFourierCoeff a s (-a) := by
        simp
      rw [← hterm]
      refine hasSum_ite_eq (-a) _ |>.congr_fun fun m => ?_
      by_cases hm : m = -a
      · subst hm; simp
      · rw [ite_eq_right hm]
        by_contra hne
        have hcne : thetaFourierCoeff a s m ≠ 0 := left_ne_zero_of_mul hne
        have hma := (thetaFourierCoeff_zero_level_eq_zero_of_ne hτ hs hcne).1
        have hmaZ : m + a = 0 := by exact_mod_cast hma
        exact hm (eq_neg_of_add_eq_zero_left hmaZ)
    exact hsum.unique hsingle
  · rintro ⟨c, rfl⟩
    refine ⟨differentiable_const c, fun z => ?_, fun z => ?_⟩
    · have ha : cexp (2 * π * I * (a : ℂ)) = 1 := by
        rw [show (2 * π * I * (a : ℂ)) = (a : ℂ) * (2 * π * I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I a
      simp [ha]
    · have hb : cexp (2 * π * I * (b : ℂ)) = 1 := by
        rw [show (2 * π * I * (b : ℂ)) = (b : ℂ) * (2 * π * I) by ring]
        exact Complex.exp_int_mul_two_pi_mul_I b
      simp [hb]

/-- At level `k = 0` with `τ.im ≠ 0`, non-trivial flat characteristics (`α ∉ ℤ` or `β ∉ ℤ`) admit
no nonzero holomorphic theta sections. -/
theorem thetaSections_zero_eq_bot_of_not_int {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    (h : ¬ ((∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β))) :
    thetaSections 0 τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  refine eq_zero_of_thetaFourierCoeff_eq_zero (α := α) hs.1 fun m => ?_
  by_contra hm
  obtain ⟨hma, hb⟩ := thetaFourierCoeff_zero_level_eq_zero_of_ne hτ hs hm
  exact h ⟨⟨-m, by push_cast; linarith⟩, hb⟩

open scoped Classical in
/-- **Complete dimension formula at level `k = 0`.** For any non-real period `τ` (`τ.im ≠ 0`), the
space `thetaSections 0 τ α β` has dimension `1` when both characteristics are integers (the
trivial flat line bundle) and dimension `0` otherwise. -/
theorem finrank_thetaSections_zero (τ : ℂ) (hτ : τ.im ≠ 0) (α β : ℝ) :
    Module.finrank ℂ (thetaSections 0 τ α β) =
      if (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β) then 1 else 0 := by
  by_cases h : (∃ a : ℤ, (a : ℝ) = α) ∧ (∃ b : ℤ, (b : ℝ) = β)
  · rw [ite_eq_left h]
    have h1 : (fun _ : ℂ => (1 : ℂ)) ∈ thetaSections 0 τ α β :=
      (mem_thetaSections_zero_iff_const hτ h.1 h.2).mpr ⟨1, rfl⟩
    refine finrank_eq_one ⟨fun _ => 1, h1⟩ ?_ fun s => ?_
    · intro h0
      have := congrFun (congrArg Subtype.val h0) 0
      exact one_ne_zero this
    · obtain ⟨c, hc⟩ := (mem_thetaSections_zero_iff_const hτ h.1 h.2).mp s.2
      refine ⟨c, Subtype.ext ?_⟩
      ext z
      simp [hc]
  · rw [ite_eq_right h, thetaSections_zero_eq_bot_of_not_int hτ h, finrank_bot]

end TauCeti
