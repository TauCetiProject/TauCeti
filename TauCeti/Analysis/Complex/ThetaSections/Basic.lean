/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Automorphy factors, Gaussian metrics, and holomorphic theta sections on complex tori

Let `τ ∈ ℂ` be a period parameter and `α, β ∈ ℝ` be real characteristics. On the universal cover
`ℂ` of the complex torus `ℂ / (ℤ + τℤ)`, the level-`k` automorphy factor (`k : ℝ`)
`thetaFactor k τ α β m n z = exp (2πi(mα + nβ) - πikn²τ - 2πiknz)` satisfies the `ℤ²`-cocycle
identity for every integer level `k : ℤ`, whereas for non-integer real levels the two lattice
generators fail to commute by the phase `exp (-2πik)`.

The holomorphic sections of the corresponding level-`k` theta line bundle (`k : ℕ`) are realized
as the `ℂ`-submodule `TauCeti.thetaSections k τ α β` of entire functions `s : ℂ → ℂ` satisfying
`s (z + 1) = exp (2πiα) * s z` and `s (z + τ) = exp (2πiβ - πikτ - 2πikz) * s z`. The Gaussian
Hermitian weight `thetaMetric k τ z = exp (-2πk (im z)² / im τ)` transforms inversely to
`‖thetaFactor‖²` under lattice translations whenever `τ.im ≠ 0`, and its Wirtinger derivatives
yield `∂̄∂ log h = -πk / im τ`, the `d(conj z) ∧ dz` coefficient of the Chern curvature 2-form
`Θ = (-πk / im τ) d(conj z) ∧ dz = (-2πik / im τ) dx ∧ dy`, whose first Chern form
`(i / 2π) Θ = (k / im τ) dx ∧ dy` integrates to `k` over a fundamental parallelogram when
`0 < im τ`.

## Main definitions

* `TauCeti.thetaFactor`: the level-`k` automorphy factor (`k : ℝ`), a `ℤ²`-cocycle at integer
  levels.
* `TauCeti.thetaMetric`: the Gaussian Hermitian metric weight `exp (-2πk (im z)² / im τ)`.
* `TauCeti.thetaSections`: the `ℂ`-submodule of level-`k` holomorphic theta sections with
  characteristics `(α, β)`.

## Main results

* `TauCeti.thetaFactor_mul_thetaFactor`, `TauCeti.thetaFactor_cocycle`, and
  `TauCeti.thetaFactor_commutator_real_eq_iff_exists_intCast_eq`: the real-level composition
  identity, the `ℤ²`-automorphy cocycle law at integer levels, and the integrality obstruction
  for real levels.
* `TauCeti.thetaMetric_add_int_add_int_mul_tau_mul_norm_thetaFactor_sq`,
  `TauCeti.wirtingerDeriv_log_thetaMetric`, and
  `TauCeti.conjWirtingerDeriv_wirtingerDeriv_log_thetaMetric`: descent of the Hermitian metric
  and its constant Chern curvature.
* `TauCeti.add_int_add_int_mul_tau_eq_thetaFactor_mul`,
  `TauCeti.add_int_add_int_mul_tau_of_mem_thetaSections`,
  `TauCeti.mem_thetaSections_iff_forall_add_int_add_int_mul_tau`,
  `TauCeti.thetaSections_add_int`, and `TauCeti.mul_mem_thetaSections`: full lattice automorphy,
  lattice-law membership equivalence, integer characteristic invariance, and level-additive
  multiplication of theta sections.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, 2nd edition, Grundlehren
  der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
* Nicholas M. J. Woodhouse, *Geometric Quantization*, 2nd edition, Oxford University Press, 1992.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-! ### Automorphy factor and integrality obstruction -/

/-- The level-`k` automorphy factor (`k : ℝ`) on the lattice `ℤ + τℤ` with real characteristics
`(α, β)`: `thetaFactor k τ α β m n z = exp (2πi(mα + nβ) - πikn²τ - 2πiknz)`. -/
noncomputable def thetaFactor (k : ℝ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z)

/-- Defining formula for `thetaFactor`. -/
theorem thetaFactor_def (k : ℝ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    thetaFactor k τ α β m n z =
      cexp (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z) :=
  (rfl)

/-- The automorphy factor never vanishes. -/
theorem thetaFactor_ne_zero (k : ℝ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    thetaFactor k τ α β m n z ≠ 0 :=
  Complex.exp_ne_zero _

/-- At the lattice origin `(0, 0)`, the automorphy factor equals `1`. -/
@[simp]
theorem thetaFactor_zero_zero (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 0 0 z = 1 := by
  simp [thetaFactor_def]

/-- Along the first lattice generator `(1, 0)`, the automorphy factor is `exp (2πiα)`. -/
@[simp]
theorem thetaFactor_one_zero (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 1 0 z = cexp (2 * π * I * α) := by
  simp [thetaFactor_def]

/-- Along the second lattice generator `(0, 1)`, the automorphy factor is
`exp (2πiβ - πikτ - 2πikz)`. -/
@[simp]
theorem thetaFactor_zero_one (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 0 1 z = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) := by
  simp [thetaFactor_def]

/-- General composition identity for `thetaFactor` at any real level `k : ℝ`: composing the
lattice factors for `(m₁, n₁)` and `(m₂, n₂)` introduces the phase `exp (-2πikn₁m₂)`. -/
theorem thetaFactor_mul_thetaFactor (k : ℝ) (τ : ℂ) (α β : ℝ) (m₁ n₁ m₂ n₂ : ℤ) (z : ℂ) :
    thetaFactor k τ α β m₁ n₁ (z + m₂ + n₂ * τ) * thetaFactor k τ α β m₂ n₂ z =
      cexp (-2 * π * I * k * n₁ * m₂) * thetaFactor k τ α β (m₁ + m₂) (n₁ + n₂) z := by
  simp only [thetaFactor_def, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The `ℤ²`-cocycle identity for `thetaFactor` at any integer level `k : ℤ`. -/
theorem thetaFactor_cocycle (k : ℤ) (τ : ℂ) (α β : ℝ) (m₁ n₁ m₂ n₂ : ℤ) (z : ℂ) :
    thetaFactor k τ α β (m₁ + m₂) (n₁ + n₂) z =
      thetaFactor k τ α β m₁ n₁ (z + m₂ + n₂ * τ) * thetaFactor k τ α β m₂ n₂ z := by
  rw [thetaFactor_mul_thetaFactor]
  have h1 : cexp (-2 * π * I * (k : ℝ) * n₁ * m₂) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I (-(k * n₁ * m₂)) using 2
    push_cast
    ring
  rw [h1, one_mul]

/-- Shifting the characteristics `(α, β)` by integers leaves `thetaFactor` unchanged. -/
theorem thetaFactor_add_int (k : ℝ) (τ : ℂ) (α β : ℝ) (a b m n : ℤ) (z : ℂ) :
    thetaFactor k τ (α + a) (β + b) m n z = thetaFactor k τ α β m n z := by
  simp only [thetaFactor_def]
  have h1 : cexp (((m * a + n * b : ℤ) : ℂ) * (2 * π * I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I (m * a + n * b)
  conv_rhs => rw [← mul_one (cexp _), ← h1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The automorphy factor is multiplicative in the level and characteristics. -/
theorem thetaFactor_add_level (k₁ k₂ : ℝ) (τ : ℂ) (α₁ β₁ α₂ β₂ : ℝ) (m n : ℤ) (z : ℂ) :
    thetaFactor (k₁ + k₂) τ (α₁ + α₂) (β₁ + β₂) m n z =
      thetaFactor k₁ τ α₁ β₁ m n z * thetaFactor k₂ τ α₂ β₂ m n z := by
  simp only [thetaFactor_def, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The modulus of `thetaFactor k τ α β m n z` is `exp (πkn² im τ + 2πkn im z)`. -/
theorem norm_thetaFactor (k : ℝ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    ‖thetaFactor k τ α β m n z‖ = Real.exp (π * k * n ^ 2 * τ.im + 2 * π * k * n * z.im) := by
  rw [thetaFactor_def, Complex.norm_exp]
  congr 1
  simp [sq]

/-- For an arbitrary real level `k : ℝ`, composing the `z ↦ z + 1` and `z ↦ z + τ` automorphy
factors in the two orders differs by the constant phase `exp (-2πik)`. -/
theorem thetaFactor_commutator_real (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 0 1 (z + 1) * thetaFactor k τ α β 1 0 z =
      cexp (-2 * π * I * k) *
        (thetaFactor k τ α β 1 0 (z + τ) * thetaFactor k τ α β 0 1 z) := by
  have h1 : thetaFactor k τ α β 0 1 (z + 1) * thetaFactor k τ α β 1 0 z =
      cexp (-2 * π * I * k) * thetaFactor k τ α β 1 1 z := by
    simpa [-thetaFactor_one_zero, -thetaFactor_zero_one] using
      thetaFactor_mul_thetaFactor k τ α β 0 1 1 0 z
  have h2 : thetaFactor k τ α β 1 0 (z + τ) * thetaFactor k τ α β 0 1 z =
      thetaFactor k τ α β 1 1 z := by
    simpa [-thetaFactor_one_zero, -thetaFactor_zero_one] using
      thetaFactor_mul_thetaFactor k τ α β 1 0 0 1 z
  rw [h1, h2]

/-- **Integrality obstruction for the torus automorphy factor.** The `z ↦ z + 1` and `z ↦ z + τ`
generator factors at real level `k : ℝ` satisfy the abelian compatibility relation if and only if
`k` is an integer. -/
theorem thetaFactor_commutator_real_eq_iff_exists_intCast_eq (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaFactor k τ α β 0 1 (z + 1) * thetaFactor k τ α β 1 0 z =
        thetaFactor k τ α β 1 0 (z + τ) * thetaFactor k τ α β 0 1 z ↔
      ∃ n : ℤ, (n : ℝ) = k := by
  rw [thetaFactor_commutator_real]
  have hne : thetaFactor k τ α β 1 0 (z + τ) * thetaFactor k τ α β 0 1 z ≠ 0 :=
    mul_ne_zero (thetaFactor_ne_zero _ _ _ _ _ _ _) (thetaFactor_ne_zero _ _ _ _ _ _ _)
  have hneg : -2 * π * I * (k : ℂ) = -(2 * π * I * k) := by ring
  rw [mul_eq_right₀ hne, hneg, Complex.exp_neg, inv_eq_one, Complex.exp_eq_one_iff]
  simp [mul_comm (2 * π * I), mul_left_inj' two_pi_I_ne_zero, ← ofReal_intCast, eq_comm]

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

/-- At level zero, the Gaussian Hermitian metric weight `thetaMetric` reduces to `1`. -/
@[simp]
theorem thetaMetric_zero (τ z : ℂ) : thetaMetric 0 τ z = 1 := by
  simp [thetaMetric_def]

/-- Under `τ.im = 0`, the Gaussian Hermitian metric weight `thetaMetric` reduces to `1`. -/
@[simp]
theorem thetaMetric_of_im_eq_zero (k : ℝ) {τ : ℂ} (hτ : τ.im = 0) (z : ℂ) :
    thetaMetric k τ z = 1 := by
  simp [thetaMetric_def, hτ]

/-- The Hermitian metric weight is invariant under real integer translations `z ↦ z + 1`. -/
@[simp]
theorem thetaMetric_add_one (k : ℝ) (τ z : ℂ) :
    thetaMetric k τ (z + 1) = thetaMetric k τ z := by
  simp [thetaMetric_def]

/-- Under any lattice translation `z ↦ z + m + n * τ` at any real level `k : ℝ`, the metric
weight `thetaMetric` transforms inversely to `‖thetaFactor‖²`, so `h(z) ‖s(z)‖²` descends to the
torus whenever `τ.im ≠ 0`. -/
theorem thetaMetric_add_int_add_int_mul_tau_mul_norm_thetaFactor_sq (k : ℝ) {τ : ℂ}
    (hτ : τ.im ≠ 0) (α β : ℝ) (m n : ℤ) (z : ℂ) :
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
  simpa [thetaFactor_zero_one] using
    thetaMetric_add_int_add_int_mul_tau_mul_norm_thetaFactor_sq k hτ 0 β 0 1 z

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
  simp
  ring

/-- The `(0, 1)`-Wirtinger derivative of the Chern `(1, 0)`-form `∂ log (thetaMetric k τ)` is the
constant curvature `-πk / im τ`, corresponding to first Chern form `(k / im τ) dx ∧ dy`. -/
theorem conjWirtingerDeriv_wirtingerDeriv_log_thetaMetric (k : ℝ) (τ z : ℂ) :
    conjWirtingerDeriv
      (fun w : ℂ => wirtingerDeriv (fun u : ℂ => (Real.log (thetaMetric k τ u) : ℂ)) w 1) z 1 =
      -(π : ℂ) * k / τ.im := by
  simp_rw [wirtingerDeriv_log_thetaMetric]
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
  simp [c]
  ring_nf
  simp

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

private lemma add_int_eq_thetaFactor_mul {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) (m : ℤ) (z : ℂ) :
    s (z + m) = thetaFactor k τ α β m 0 z * s z := by
  induction m using Int.induction_on with
  | zero => simp
  | succ j ih =>
    have hstep : z + (((j : ℤ) + 1 : ℤ) : ℂ) = (z + (j : ℤ)) + 1 := by push_cast; ring
    rw [hstep, h1, ih, ← mul_assoc, ← thetaFactor_one_zero (k : ℝ) τ α β (z + (j : ℤ))]
    have hcoc := thetaFactor_cocycle k τ α β 1 0 j 0 z
    simpa [add_comm] using congrArg (· * s z) hcoc.symm
  | pred j ih =>
    have hstep : z + ((-(j : ℤ) - 1 : ℤ) : ℂ) + 1 = z + ((-(j : ℤ) : ℤ) : ℂ) := by
      push_cast; ring
    have h1' := h1 (z + ((-(j : ℤ) - 1 : ℤ) : ℂ))
    rw [hstep, ih] at h1'
    have hcoc := thetaFactor_cocycle k τ α β 1 0 (-(j : ℤ) - 1) 0 z
    have hidx : (1 : ℤ) + (-(j : ℤ) - 1) = -(j : ℤ) := by ring
    rw [hidx, zero_add, Int.cast_zero, zero_mul, add_zero, thetaFactor_one_zero] at hcoc
    rw [hcoc, mul_assoc] at h1'
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) h1').symm

private lemma add_int_mul_tau_eq_thetaFactor_mul {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    (n : ℤ) (z : ℂ) :
    s (z + n * τ) = thetaFactor k τ α β 0 n z * s z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ j ih =>
    have hstep : z + (((j : ℤ) + 1 : ℤ) : ℂ) * τ = (z + (j : ℤ) * τ) + τ := by push_cast; ring
    rw [hstep, hτ, ih, ← mul_assoc]
    have hcoc := thetaFactor_cocycle k τ α β 0 1 0 j z
    rw [thetaFactor_zero_one] at hcoc
    have hcoc' : thetaFactor k τ α β 0 (j + 1) z =
        cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + (j : ℤ) * τ)) *
          thetaFactor k τ α β 0 j z := by
      simpa [add_comm] using hcoc
    rw [← hcoc']
  | pred j ih =>
    have hstep : z + ((-(j : ℤ) - 1 : ℤ) : ℂ) * τ + τ = z + ((-(j : ℤ) : ℤ) : ℂ) * τ := by
      push_cast; ring
    have hτ' := hτ (z + ((-(j : ℤ) - 1 : ℤ) : ℂ) * τ)
    rw [hstep, ih] at hτ'
    have hcoc := thetaFactor_cocycle k τ α β 0 1 0 (-(j : ℤ) - 1) z
    have hidx : (1 : ℤ) + (-(j : ℤ) - 1) = -(j : ℤ) := by ring
    rw [hidx, zero_add, Int.cast_zero, add_zero, thetaFactor_zero_one] at hcoc
    simp only [ofReal_intCast] at hcoc
    rw [hcoc, mul_assoc] at hτ'
    exact (mul_left_cancel₀ (Complex.exp_ne_zero _) hτ').symm

/-- Full lattice automorphy law for any function `s : ℂ → ℂ` (not necessarily holomorphic)
satisfying the two generator automorphy laws at integer level `k : ℤ`. -/
theorem add_int_add_int_mul_tau_eq_thetaFactor_mul {k : ℤ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (h1 : ∀ z, s (z + 1) = cexp (2 * π * I * α) * s z)
    (hτ : ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z)
    (m n : ℤ) (z : ℂ) :
    s (z + m + n * τ) = thetaFactor k τ α β m n z * s z := by
  have hsum : z + m + n * τ = (z + n * τ) + m := by ring
  rw [hsum, add_int_eq_thetaFactor_mul (k := k) (τ := τ) (β := β) h1 m (z + n * τ),
    add_int_mul_tau_eq_thetaFactor_mul (α := α) hτ n z, ← mul_assoc]
  have hcoc := thetaFactor_cocycle k τ α β m 0 0 n z
  simpa using congrArg (· * s z) hcoc.symm

/-- Full lattice automorphy law for a holomorphic theta section under any translation
`z ↦ z + m + n * τ`. -/
theorem add_int_add_int_mul_tau_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    s (z + m + n * τ) = thetaFactor k τ α β m n z * s z := by
  simpa using add_int_add_int_mul_tau_eq_thetaFactor_mul (k := (k : ℤ)) hs.2.1
    (by simpa using hs.2.2) m n z

/-- Membership in `thetaSections` is equivalent to being entire and satisfying the full
`ℤ²`-automorphy law with factor `thetaFactor`. -/
theorem mem_thetaSections_iff_forall_add_int_add_int_mul_tau {k : ℕ} {τ : ℂ} {α β : ℝ}
    {s : ℂ → ℂ} :
    s ∈ thetaSections k τ α β ↔
      Differentiable ℂ s ∧
        ∀ m n : ℤ, ∀ z : ℂ, s (z + m + n * τ) = thetaFactor k τ α β m n z * s z := by
  refine ⟨fun hs => ⟨hs.1, add_int_add_int_mul_tau_of_mem_thetaSections hs⟩, fun ⟨hs, h⟩ => ?_⟩
  refine mem_thetaSections_iff.mpr ⟨hs, fun z => ?_, fun z => ?_⟩
  · simpa [thetaFactor_one_zero] using h 1 0 z
  · simpa [thetaFactor_zero_one] using h 0 1 z

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


end TauCeti
