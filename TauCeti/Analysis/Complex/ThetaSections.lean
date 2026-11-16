/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Complex.FourierPeriodic
import TauCeti.Analysis.Fourier.FourierCoeffOn
import TauCeti.Topology.Algebra.InfiniteSum.NatInt

/-!
# Theta sections with characteristics on one-dimensional complex tori

For a level `k : ℕ`, a complex modulus `τ : ℂ`, and real characteristics `α, β : ℝ`, the complex
vector space `TauCeti.thetaSections k τ α β` consists of the entire functions `s : ℂ → ℂ`
satisfying the Appell–Humbert automorphy laws
`s (z + 1) = e^{2πiα} s z` and `s (z + τ) = e^{2πiβ - πikτ - 2πikz} s z`.
When `0 < k` and `0 < τ.im`, these are the global holomorphic sections of a degree-`k` line bundle
on the elliptic curve `ℂ / (ℤ + τℤ)` pulled back to its universal cover `ℂ`.

This file develops the lattice cocycle and Hermitian fiber metric of the automorphy system, expands
sections in twisted complex Fourier series, constructs the explicit basis of `k` characteristic
theta series from Mathlib's two-variable Jacobi theta function `jacobiTheta₂`, proves that
`Module.finrank ℂ (thetaSections k τ α β) = k` for `0 < k` and `0 < τ.im`, and establishes the
sharpness of both hypotheses by analyzing the boundary regimes `τ.im ≤ 0` and `k = 0`.

## Main definitions

* `TauCeti.thetaSections k τ α β`: the `ℂ`-submodule of `ℂ → ℂ` cut out by entire holomorphicity
  and the two automorphy laws of level `k` and characteristics `(α, β)`.
* `TauCeti.thetaAutomorphy k τ α β m n z`: the Appell–Humbert factor of automorphy along the
  lattice vector `m + n * τ`.
* `TauCeti.thetaMetric k τ z`: the Hermitian fiber weight `e^{-2πk (Im z)² / Im τ}` making the
  pointwise norm-squared of any theta section lattice-invariant when `τ.im ≠ 0`.
* `TauCeti.thetaFourierCoeff α m s`: the `m`-th Fourier coefficient on `[0, 1]` of the untwisted
  `1`-periodic function `x ↦ e^{-2πiαx} s x`.
* `TauCeti.thetaChar k τ α β r`: the `r`-th characteristic level-`k` theta function
  `z ↦ e^{2πi(r + α)z} jacobiTheta₂ (k z + (r + α)τ - β) (kτ)`.
* `TauCeti.thetaFourierEquiv hk hτ α β`: the linear equivalence
  `thetaSections k τ α β ≃ₗ[ℂ] (Fin k → ℂ)` given by the first `k` twisted Fourier coefficients.
* `TauCeti.thetaBasis hk hτ α β`: the resulting `Fin k`-indexed basis of
  `thetaSections k τ α β` consisting of the characteristic theta functions `thetaChar k τ α β r`.

## Main results

* `TauCeti.thetaAutomorphy_add` and `TauCeti.apply_add_int_add_int_mul_of_mem_thetaSections`:
  the 1-cocycle identity on `ℤ × ℤ` and full lattice transformation law of sections, together with
  the commutator integrality criterion `TauCeti.automorphy_commutator_eq_one_iff`.
* `TauCeti.thetaMetric_mul_norm_sq_add_int_add_int_mul`: lattice invariance of
  `z ↦ thetaMetric k τ z * ‖s z‖ ^ 2` for `τ.im ≠ 0`.
* `TauCeti.hasSum_thetaFourierCoeff_of_mem_thetaSections` and
  `TauCeti.thetaFourierCoeff_add_nat`: global expansion
  `s z = ∑' m, c_m e^{2πi(m + α)z}` and the `τ`-shift recurrence
  `c_{m + k} = e^{2πi(m + α)τ - 2πiβ + πikτ} c_m`.
* `TauCeti.thetaChar_mem_thetaSections` and `TauCeti.thetaFourierCoeff_thetaChar`: each
  `thetaChar k τ α β r` lies in `thetaSections k τ α β`, and for `r, m : Fin k` its `m`-th
  twisted Fourier coefficient is `δ_{r, m}`.
* `TauCeti.finrank_thetaSections`: `Module.finrank ℂ (thetaSections k τ α β) = k` when `0 < k`
  and `0 < τ.im`.
* `TauCeti.thetaSections_eq_bot_of_im_nonpos` and `TauCeti.nontrivial_thetaSections_iff`: for
  `0 < k`, `thetaSections k τ α β` is nontrivial if and only if `0 < τ.im`.
* `TauCeti.mem_thetaSections_zero_iff`, `TauCeti.nontrivial_thetaSections_zero_iff`, and
  `TauCeti.finrank_thetaSections_zero_zero`: at level `k = 0` with `τ.im ≠ 0`, nontrivial sections
  exist if and only if `α, β` are integers, in which case they are the constant functions of
  dimension `1`.

## References

* D. Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983, Chapter I,
  §§1–3.
* C. Birkenhake and H. Lange, *Complex Abelian Varieties*, second edition, Grundlehren der
  mathematischen Wissenschaften 302, Springer, 2004, Chapter 3, §§3.1–3.2.
* N. M. J. Woodhouse, *Geometric Quantization*, second edition, Oxford Mathematical Monographs,
  Clarendon Press, 1992, Chapters 8–9.
* B. C. Hall, *Quantum Theory for Mathematicians*, Graduate Texts in Mathematics 267, Springer,
  2013, Chapters 22–23.
-/

public section

open Complex MeasureTheory
open scoped Real

namespace TauCeti

/-! ### Space of theta sections and the Appell–Humbert lattice cocycle -/

/-- The `ℂ`-vector space of holomorphic level-`k` theta functions with real characteristics
`(α, β)` for the period lattice `ℤ + τℤ`: entire functions `s : ℂ → ℂ` satisfying
`s (z + 1) = e^{2πiα} s z` and `s (z + τ) = e^{2πiβ - πikτ - 2πikz} s z`. -/
def thetaSections (k : ℕ) (τ : ℂ) (α β : ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {s | Differentiable ℂ s ∧ (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
    ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z}
  add_mem' := by
    rintro f g ⟨hf, hf1, hfτ⟩ ⟨hg, hg1, hgτ⟩
    exact ⟨hf.add hg, fun z ↦ by simp [hf1, hg1, mul_add],
      fun z ↦ by simp [hfτ, hgτ, mul_add]⟩
  zero_mem' := ⟨differentiable_const 0, fun z ↦ by simp, fun z ↦ by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf1, hfτ⟩
    exact ⟨hf.const_smul c, fun z ↦ by simp [hf1]; ring, fun z ↦ by simp [hfτ]; ring⟩

@[simp]
theorem mem_thetaSections_iff {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ} :
    s ∈ thetaSections k τ α β ↔
      Differentiable ℂ s ∧ (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
        ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z :=
  Iff.rfl

theorem differentiable_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) : Differentiable ℂ s :=
  hs.1

theorem continuous_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) : Continuous s :=
  hs.1.continuous

theorem apply_add_one_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s (z + 1) = cexp (2 * π * I * α) * s z :=
  hs.2.1 z

theorem apply_add_tau_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z :=
  hs.2.2 z

/-- Shifting the real characteristics `(α, β)` by integers `(p, q)` leaves `thetaSections`
unchanged. -/
theorem thetaSections_add_int (k : ℕ) (τ : ℂ) (α β : ℝ) (p q : ℤ) :
    thetaSections k τ (α + p) (β + q) = thetaSections k τ α β := by
  ext s
  have hp : cexp (2 * π * I * (α + p : ℝ)) = cexp (2 * π * I * α) := by
    rw [ofReal_add, ofReal_intCast, mul_add, Complex.exp_add, mul_comm _ (p : ℂ),
      exp_int_mul_two_pi_mul_I, mul_one]
  have hq (z : ℂ) :
      cexp (2 * π * I * (β + q : ℝ) - π * I * k * τ - 2 * π * I * k * z) =
        cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) := by
    rw [ofReal_add, ofReal_intCast,
      show 2 * π * I * (β + (q : ℂ)) - π * I * k * τ - 2 * π * I * k * z =
        (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) + q * (2 * π * I) by ring,
      Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
  simp only [mem_thetaSections_iff, hp, hq]

/-- Comparing the automorphy factors along `(z + 1) + τ` and `(z + τ) + 1` for an arbitrary real
level parameter `κ : ℝ` produces the commutator phase `e^{-2πiκ}`. -/
theorem automorphy_commutator_eq_mul (κ : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    cexp (2 * π * I * β - π * I * κ * τ - 2 * π * I * κ * (z + 1)) * cexp (2 * π * I * α) =
      cexp (-2 * π * I * κ) *
        (cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * κ * τ - 2 * π * I * κ * z)) := by
  simp only [← Complex.exp_add]
  congr 1
  ring

/-- The commutator phase `e^{-2πiκ}` between the `1`- and `τ`-translations equals `1` if and only
if the level `κ` is an integer. -/
theorem automorphy_commutator_eq_one_iff (κ : ℝ) :
    cexp (-2 * π * I * κ) = 1 ↔ ∃ k : ℤ, κ = k := by
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hκ : (-(κ : ℂ)) * (2 * π * I) = (n : ℂ) * (2 * π * I) := by linear_combination hn
    exact_mod_cast neg_eq_iff_eq_neg.1 (mul_right_cancel₀ hpi hκ)
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    push_cast
    ring

/-- The Appell–Humbert factor of automorphy for the lattice vector `m + n * τ` (`m, n : ℤ`),
namely `e^{2πi(mα + nβ) - πikn²τ - 2πiknz}`. -/
noncomputable def thetaAutomorphy (k : ℕ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z)

@[simp]
theorem thetaAutomorphy_zero_zero (k : ℕ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaAutomorphy k τ α β 0 0 z = 1 := by
  simp [thetaAutomorphy]

theorem thetaAutomorphy_one_zero (k : ℕ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaAutomorphy k τ α β 1 0 z = cexp (2 * π * I * α) := by
  simp [thetaAutomorphy]

theorem thetaAutomorphy_zero_one (k : ℕ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    thetaAutomorphy k τ α β 0 1 z = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) := by
  simp [thetaAutomorphy]

theorem thetaAutomorphy_ne_zero (k : ℕ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    thetaAutomorphy k τ α β m n z ≠ 0 :=
  Complex.exp_ne_zero _

/-- **Lattice 1-cocycle identity.** The Appell–Humbert factors `thetaAutomorphy k τ α β` form a
1-cocycle for the action of `ℤ × ℤ` on `ℂ` via `(m, n) • z = z + m + n * τ`, because the cross term
`-2πik n₁ m₂` is an integer multiple of `2πi`. -/
theorem thetaAutomorphy_add (k : ℕ) (τ : ℂ) (α β : ℝ) (m₁ m₂ n₁ n₂ : ℤ) (z : ℂ) :
    thetaAutomorphy k τ α β (m₁ + m₂) (n₁ + n₂) z =
      thetaAutomorphy k τ α β m₁ n₁ (z + m₂ + n₂ * τ) * thetaAutomorphy k τ α β m₂ n₂ z := by
  rw [thetaAutomorphy, thetaAutomorphy, thetaAutomorphy, ← Complex.exp_add]
  let q : ℤ := -((k : ℤ) * n₁ * m₂)
  have hint : cexp ((q : ℂ) * (2 * π * I)) = 1 := exp_int_mul_two_pi_mul_I q
  rw [← mul_one (cexp _), ← hint, ← Complex.exp_add]
  congr 1
  push_cast [q]
  ring

/-- Every section `s ∈ thetaSections k τ α β` transforms by `thetaAutomorphy k τ α β m 0 z` under
an integer shift `z ↦ z + m` (`m : ℤ`). -/
theorem apply_add_int_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m : ℤ) (z : ℂ) :
    s (z + m) = thetaAutomorphy k τ α β m 0 z * s z := by
  induction m using Int.induction_on generalizing z with
  | zero => simp
  | succ m ih =>
    have hcoc := thetaAutomorphy_add k τ α β 1 m 0 0 z
    simp only [add_zero, Int.cast_zero, zero_mul, thetaAutomorphy_one_zero] at hcoc
    rw [Int.cast_add, Int.cast_one, ← add_assoc, hs.2.1, ih, ← mul_assoc,
      add_comm (m : ℤ) 1, hcoc]
  | pred m ih =>
    let p : ℤ := -(m : ℤ) - 1
    let q : ℤ := -(m : ℤ)
    have hzp : z + (p : ℂ) + 1 = z + (q : ℂ) := by push_cast [p, q]; ring
    have hpq : 1 + p = q := by omega
    have hcoc := thetaAutomorphy_add k τ α β 1 p 0 0 z
    simp only [hpq, add_zero, Int.cast_zero, zero_mul, thetaAutomorphy_one_zero] at hcoc
    have hmul : cexp (2 * π * I * α) * s (z + p) =
        cexp (2 * π * I * α) * (thetaAutomorphy k τ α β p 0 z * s z) := by
      rw [← hs.2.1 (z + p), hzp, ih z, hcoc, mul_assoc]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hmul

/-- Every section `s ∈ thetaSections k τ α β` transforms by `thetaAutomorphy k τ α β 0 n z` under
an integer period multiple `z ↦ z + n * τ` (`n : ℤ`). -/
theorem apply_add_int_mul_tau_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (n : ℤ) (z : ℂ) :
    s (z + n * τ) = thetaAutomorphy k τ α β 0 n z * s z := by
  induction n using Int.induction_on generalizing z with
  | zero => simp
  | succ n ih =>
    have hcoc := thetaAutomorphy_add k τ α β 0 0 1 n z
    simp only [add_zero, Int.cast_zero, thetaAutomorphy_zero_one] at hcoc
    rw [Int.cast_add, Int.cast_one, add_mul, one_mul, ← add_assoc, hs.2.2, ih, ← mul_assoc,
      add_comm (n : ℤ) 1, hcoc]
  | pred n ih =>
    let p : ℤ := -(n : ℤ) - 1
    let q : ℤ := -(n : ℤ)
    have hzp : z + (p : ℂ) * τ + τ = z + (q : ℂ) * τ := by push_cast [p, q]; ring
    have hpq : 1 + p = q := by omega
    have hcoc := thetaAutomorphy_add k τ α β 0 0 1 p z
    simp only [hpq, add_zero, Int.cast_zero, thetaAutomorphy_zero_one] at hcoc
    have hmul :
        cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + p * τ)) * s (z + p * τ) =
        cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + p * τ)) *
          (thetaAutomorphy k τ α β 0 p z * s z) := by
      rw [← hs.2.2 (z + p * τ), hzp, ih z, hcoc, mul_assoc]
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hmul

/-- Every section `s ∈ thetaSections k τ α β` transforms by `thetaAutomorphy k τ α β m n z` under
translation by any lattice vector `m + n * τ` (`m, n : ℤ`). -/
theorem apply_add_int_add_int_mul_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    s (z + m + n * τ) = thetaAutomorphy k τ α β m n z * s z := by
  have hcoc := thetaAutomorphy_add k τ α β 0 m n 0 z
  simp only [zero_add, add_zero, Int.cast_zero, zero_mul] at hcoc
  rw [apply_add_int_mul_tau_of_mem_thetaSections hs n (z + m),
    apply_add_int_of_mem_thetaSections hs m z, ← mul_assoc, ← hcoc]

/-! ### Hermitian fiber metric and lattice norm-square invariance -/

/-- The Hermitian fiber weight `h(z) = e^{-2πk (Im z)² / Im τ}` on the trivial line over `ℂ` for
the level-`k` automorphy factor. -/
noncomputable def thetaMetric (k : ℕ) (τ : ℂ) (z : ℂ) : ℝ :=
  Real.exp (-2 * π * k * z.im ^ 2 / τ.im)

theorem thetaMetric_pos (k : ℕ) (τ : ℂ) (z : ℂ) : 0 < thetaMetric k τ z :=
  Real.exp_pos _

@[simp]
theorem thetaMetric_zero_right (k : ℕ) (τ : ℂ) : thetaMetric k τ 0 = 1 := by
  simp [thetaMetric]

@[simp]
theorem thetaMetric_ofReal (k : ℕ) (τ : ℂ) (x : ℝ) : thetaMetric k τ x = 1 := by
  simp [thetaMetric]

@[simp]
theorem thetaMetric_add_real (k : ℕ) (τ : ℂ) (z : ℂ) (x : ℝ) :
    thetaMetric k τ (z + x) = thetaMetric k τ z := by
  simp [thetaMetric]

/-- Transformation of `thetaMetric` under `z ↦ z + n * τ` when `τ.im ≠ 0`. -/
theorem thetaMetric_add_int_mul_tau (k : ℕ) {τ : ℂ} (hτ : τ.im ≠ 0) (n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + n * τ) =
      Real.exp (-4 * π * k * n * z.im - 2 * π * k * n ^ 2 * τ.im) * thetaMetric k τ z := by
  rw [thetaMetric, thetaMetric, ← Real.exp_add]
  congr 1
  have him : (z + n * τ).im = z.im + n * τ.im := by simp
  rw [him]
  field_simp
  ring

/-- Transformation of `thetaMetric` under a single period shift `z ↦ z + τ` when `τ.im ≠ 0`. -/
theorem thetaMetric_add_tau (k : ℕ) {τ : ℂ} (hτ : τ.im ≠ 0) (z : ℂ) :
    thetaMetric k τ (z + τ) =
      Real.exp (-4 * π * k * z.im - 2 * π * k * τ.im) * thetaMetric k τ z := by
  simpa using thetaMetric_add_int_mul_tau k hτ 1 z

/-- Squared norm of the Appell–Humbert factor `thetaAutomorphy k τ α β m n z`: it cancels the
metric factor of `thetaMetric_add_int_mul_tau` independent of the real characteristics `(α, β)`. -/
theorem norm_sq_thetaAutomorphy (k : ℕ) (τ : ℂ) (α β : ℝ) (m n : ℤ) (z : ℂ) :
    ‖thetaAutomorphy k τ α β m n z‖ ^ 2 =
      Real.exp (4 * π * k * n * z.im + 2 * π * k * n ^ 2 * τ.im) := by
  rw [thetaAutomorphy, Complex.norm_exp, ← Real.exp_nat_mul]
  congr 1
  have hexp :
      (2 * π * I * (m * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z).re =
        2 * π * k * n * z.im + π * k * n ^ 2 * τ.im := by
    rw [show 2 * π * I * ((m : ℂ) * α + n * β) - π * I * k * n ^ 2 * τ - 2 * π * I * k * n * z =
        ((2 * π * (m * α + n * β) : ℝ) : ℂ) * I - ((π * k * n ^ 2 : ℝ) : ℂ) * τ * I -
          ((2 * π * k * n : ℝ) : ℂ) * z * I by push_cast; ring]
    simp only [sub_re, mul_I_re, ofReal_im, im_ofReal_mul]
    ring
  rw [hexp]
  push_cast
  ring

/-- **Hermitian norm invariance.** For `τ.im ≠ 0` and `s ∈ thetaSections k τ α β`, the pointwise
Hermitian norm-squared `z ↦ thetaMetric k τ z * ‖s z‖ ^ 2` is invariant under every lattice
translation `z ↦ z + m + n * τ`, so it descends to the complex torus `ℂ / (ℤ + τℤ)`. -/
theorem thetaMetric_mul_norm_sq_add_int_add_int_mul {k : ℕ} {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    thetaMetric k τ (z + m + n * τ) * ‖s (z + m + n * τ)‖ ^ 2 =
      thetaMetric k τ z * ‖s z‖ ^ 2 := by
  rw [apply_add_int_add_int_mul_of_mem_thetaSections hs, norm_mul, mul_pow,
    norm_sq_thetaAutomorphy, thetaMetric_add_int_mul_tau k hτ n (z + m),
    show (m : ℂ) = ((m : ℝ) : ℂ) by simp, thetaMetric_add_real k τ z (m : ℝ)]
  rw [show Real.exp (-4 * π * k * n * (z + ((m : ℝ) : ℂ)).im - 2 * π * k * n ^ 2 * τ.im) =
      Real.exp (-4 * π * k * n * z.im - 2 * π * k * n ^ 2 * τ.im) by simp,
    mul_comm _ (thetaMetric k τ z), mul_assoc, ← mul_assoc (Real.exp _), ← Real.exp_add]
  have hzero : -4 * π * k * n * z.im - 2 * π * k * n ^ 2 * τ.im +
      (4 * π * k * n * z.im + 2 * π * k * n ^ 2 * τ.im) = 0 := by ring
  rw [hzero, Real.exp_zero, one_mul]

/-- Invariance of `thetaMetric k τ z * ‖s z‖ ^ 2` under `z ↦ z + 1` (requiring no hypothesis on
`τ.im`). -/
theorem thetaMetric_mul_norm_sq_add_one {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    thetaMetric k τ (z + 1) * ‖s (z + 1)‖ ^ 2 = thetaMetric k τ z * ‖s z‖ ^ 2 := by
  have h1 : ‖cexp (2 * π * I * α)‖ = 1 := by
    rw [show (2 * π * I * α : ℂ) = ((2 * π * α : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I (2 * π * α)
  rw [hs.2.1 z, norm_mul, h1, one_mul, ← ofReal_one, thetaMetric_add_real]

/-- Invariance of `thetaMetric k τ z * ‖s z‖ ^ 2` under `z ↦ z + τ` when `τ.im ≠ 0`. -/
theorem thetaMetric_mul_norm_sq_add_tau {k : ℕ} {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    thetaMetric k τ (z + τ) * ‖s (z + τ)‖ ^ 2 = thetaMetric k τ z * ‖s z‖ ^ 2 := by
  simpa using thetaMetric_mul_norm_sq_add_int_add_int_mul hτ hs 0 1 z

/-! ### Twisted complex Fourier series and the `τ`-shift recurrence -/

/-- Untwisting `s : ℂ → ℂ` by `e^{-2πiαz}` turns the `1`-quasi-periodicity law
`s (z + 1) = e^{2πiα} s z` into genuine `1`-periodicity. -/
private theorem periodic_cexp_neg_mul_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) :
    Function.Periodic (fun z : ℂ ↦ cexp (-2 * π * I * α * z) * s z) 1 := fun z ↦ by
  dsimp only
  rw [hs.2.1 z, ← mul_assoc, ← Complex.exp_add]
  have hexp : -2 * π * I * α * (z + 1) + 2 * π * I * α = -2 * π * I * α * z := by ring
  rw [hexp]

private theorem differentiable_cexp_neg_mul_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ}
    {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) :
    Differentiable ℂ fun z : ℂ ↦ cexp (-2 * π * I * α * z) * s z :=
  (differentiable_exp.comp (differentiable_id.const_mul _)).mul hs.1

/-- The `m`-th twisted Fourier coefficient `∫₀¹ e^{-2πi(m + α)x} s(x) dx` of `s : ℂ → ℂ`, defined
as the `m`-th Fourier coefficient on `[0, 1]` of the untwisted function `x ↦ e^{-2πiαx} s x`. -/
noncomputable def thetaFourierCoeff (α : ℝ) (m : ℤ) (s : ℂ → ℂ) : ℂ :=
  fourierCoeffOn zero_lt_one (fun x : ℝ ↦ cexp (-2 * π * I * α * x) * s x) m

/-- Bundled `ℂ`-linear functional sending a theta section to its `m`-th twisted Fourier
coefficient. -/
noncomputable def thetaFourierCoeffLM (k : ℕ) (τ : ℂ) (α β : ℝ) (m : ℤ) :
    thetaSections k τ α β →ₗ[ℂ] ℂ where
  toFun s := thetaFourierCoeff α m (s : ℂ → ℂ)
  map_add' s t := by
    have hs : IntervalIntegrable (fun x : ℝ ↦ cexp (-2 * π * I * α * x) * (s : ℂ → ℂ) x)
        volume 0 1 :=
      ((differentiable_cexp_neg_mul_of_mem_thetaSections s.2).continuous.comp
        continuous_ofReal).intervalIntegrable 0 1
    have ht : IntervalIntegrable (fun x : ℝ ↦ cexp (-2 * π * I * α * x) * (t : ℂ → ℂ) x)
        volume 0 1 :=
      ((differentiable_cexp_neg_mul_of_mem_thetaSections t.2).continuous.comp
        continuous_ofReal).intervalIntegrable 0 1
    simp only [thetaFourierCoeff, Submodule.coe_add, Pi.add_apply, mul_add]
    exact fourierCoeffOn_add zero_lt_one hs ht m
  map_smul' c s := by
    simp only [thetaFourierCoeff, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    rw [show (fun x : ℝ ↦ cexp (-2 * π * I * α * x) * (c * (s : ℂ → ℂ) x)) =
        fun x : ℝ ↦ c * (cexp (-2 * π * I * α * x) * (s : ℂ → ℂ) x) by ext x; ring]
    exact fourierCoeffOn.const_mul _ c m zero_lt_one

@[simp]
theorem thetaFourierCoeffLM_apply (k : ℕ) (τ : ℂ) (α β : ℝ) (m : ℤ)
    (s : thetaSections k τ α β) :
    thetaFourierCoeffLM k τ α β m s = thetaFourierCoeff α m (s : ℂ → ℂ) :=
  (rfl)

/-- **Global complex Fourier expansion of a theta section.** Every `s ∈ thetaSections k τ α β`
expands throughout `ℂ` as `s z = ∑_{m ∈ ℤ} thetaFourierCoeff α m s * e^{2πi(m + α)z}`. -/
theorem hasSum_thetaFourierCoeff_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    HasSum (fun m : ℤ ↦ thetaFourierCoeff α m s * cexp (2 * π * I * (m + α) * z)) (s z) := by
  have hper : Function.Periodic (fun w : ℂ ↦ cexp (-2 * π * I * α * w) * s w) (1 : ℝ) := by
    simpa using periodic_cexp_neg_mul_of_mem_thetaSections hs
  have hdiff := differentiable_cexp_neg_mul_of_mem_thetaSections hs
  have hsum := (hdiff.hasSum_fourierCoeffOn_zero_mul_cexp zero_lt_one hper z).mul_right
    (cexp (2 * π * I * α * z))
  have hrhs : cexp (-2 * π * I * α * z) * s z * cexp (2 * π * I * α * z) = s z := by
    rw [mul_right_comm, ← Complex.exp_add, show -2 * π * I * α * z + 2 * π * I * α * z = 0 by ring,
      Complex.exp_zero, one_mul]
  rw [hrhs] at hsum
  refine hsum.congr_fun fun m ↦ ?_
  simp only [thetaFourierCoeff, ofReal_one, div_one, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem summable_thetaFourierCoeff_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    Summable fun m : ℤ ↦ thetaFourierCoeff α m s * cexp (2 * π * I * (m + α) * z) :=
  (hasSum_thetaFourierCoeff_of_mem_thetaSections hs z).summable

theorem tsum_thetaFourierCoeff_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    (∑' m : ℤ, thetaFourierCoeff α m s * cexp (2 * π * I * (m + α) * z)) = s z :=
  (hasSum_thetaFourierCoeff_of_mem_thetaSections hs z).tsum_eq

/-- A theta section whose twisted Fourier coefficients all vanish is identically zero. -/
theorem eq_zero_of_forall_thetaFourierCoeff_eq_zero {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (h : ∀ m : ℤ, thetaFourierCoeff α m s = 0) :
    s = 0 := by
  ext z
  rw [← tsum_thetaFourierCoeff_of_mem_thetaSections hs z]
  simp [h]

/-- **The `τ`-recurrence for twisted Fourier coefficients.** For every `s ∈ thetaSections k τ α β`
and `m : ℤ`, shifting the frequency by `k` multiplies the Fourier coefficient by
`e^{2πi(m + α)τ - 2πiβ + πikτ}`. -/
theorem thetaFourierCoeff_add_nat {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m : ℤ) :
    thetaFourierCoeff α (m + k) s =
      cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
        thetaFourierCoeff α m s := by
  let g : ℂ → ℂ := fun z ↦ cexp (-2 * π * I * α * z) * s z
  have hg : Differentiable ℂ g := differentiable_cexp_neg_mul_of_mem_thetaSections hs
  have hper : Function.Periodic g (1 : ℝ) := fun z ↦ by
    simpa [g] using periodic_cexp_neg_mul_of_mem_thetaSections hs z
  have hshift := hg.fourierCoeffOn_zero_comp_add zero_lt_one hper τ m
  simp only [ofReal_one, div_one, smul_eq_mul] at hshift
  -- Rewrite `g (x + τ)` via the `τ`-automorphy law of `s`, shifting frequency `m` to `m + k`.
  have haut : fourierCoeffOn zero_lt_one (fun x : ℝ ↦ g (x + τ)) m =
      cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) *
        thetaFourierCoeff α (m + k) s := by
    rw [thetaFourierCoeff, fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
    simp only [sub_zero, one_div_one, one_smul]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    simp only [g, hs.2.2 x, fourier_coe_apply, sub_zero, ofReal_one, div_one, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    symm
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [haut] at hshift
  calc thetaFourierCoeff α (m + k) s
      = cexp (2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ) *
          (cexp (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) *
            thetaFourierCoeff α (m + k) s) := by
        rw [← mul_assoc, ← Complex.exp_add,
          show 2 * π * I * α * τ - 2 * π * I * β + π * I * k * τ +
            (-2 * π * I * α * τ + 2 * π * I * β - π * I * k * τ) = 0 by ring,
          Complex.exp_zero, one_mul]
    _ = cexp (2 * π * I * (m + α) * τ - 2 * π * I * β + π * I * k * τ) *
          thetaFourierCoeff α m s := by
        rw [hshift, ← mul_assoc, ← Complex.exp_add]
        congr 2
        ring

/-- **Closed-form progression formula.** Iterating `thetaFourierCoeff_add_nat` along the residue
class `q * k + r` (`q, r : ℤ`) expresses every coefficient in that class as `jacobiTheta₂_term`
times the base coefficient at `r`. -/
theorem thetaFourierCoeff_int_mul_add {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (q r : ℤ) :
    thetaFourierCoeff α (q * k + r) s =
      jacobiTheta₂_term q ((r + α) * τ - β) (k * τ) * thetaFourierCoeff α r s := by
  induction q using Int.induction_on with
  | zero =>
    simp [jacobiTheta₂_term]
  | succ q ih =>
    have hstep := thetaFourierCoeff_add_nat hs ((q : ℤ) * k + r)
    rw [show ((q : ℤ) + 1) * (k : ℤ) + r = (q : ℤ) * k + r + k by ring, hstep, ih, ← mul_assoc,
      jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  | pred q ih =>
    have hstep := thetaFourierCoeff_add_nat hs ((-(q : ℤ) - 1) * k + r)
    rw [show (-(q : ℤ) - 1) * (k : ℤ) + r + k = -(q : ℤ) * k + r by ring, ih] at hstep
    have hmul :
        cexp (2 * π * I * (((-(q : ℤ) - 1) * (k : ℤ) + r : ℤ) + α) * τ - 2 * π * I * β +
            π * I * k * τ) * thetaFourierCoeff α ((-(q : ℤ) - 1) * k + r) s =
        cexp (2 * π * I * (((-(q : ℤ) - 1) * (k : ℤ) + r : ℤ) + α) * τ - 2 * π * I * β +
            π * I * k * τ) *
          (jacobiTheta₂_term (-(q : ℤ) - 1) ((r + α) * τ - β) (k * τ) *
            thetaFourierCoeff α r s) := by
      rw [← hstep, ← mul_assoc, jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) hmul

/-! ### Explicit basis of characteristic Jacobi theta functions and `finrank = k` -/

/-- The `r`-th characteristic theta function of level `k`, modulus `τ`, and characteristics
`(α, β)`, built from Mathlib's `jacobiTheta₂`:
`thetaChar k τ α β r z = e^{2πi(r + α)z} jacobiTheta₂ (k z + (r + α)τ - β) (kτ)`. -/
noncomputable def thetaChar (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) : ℂ :=
  cexp (2 * π * I * (r + α) * z) * jacobiTheta₂ (k * z + (r + α) * τ - β) (k * τ)

/-- At level `k = 1` and zero characteristics, `thetaChar 1 τ 0 0 0` is `jacobiTheta₂ · τ`. -/
@[simp]
theorem thetaChar_one_zero_zero (τ : ℂ) (z : ℂ) :
    thetaChar 1 τ 0 0 0 z = jacobiTheta₂ z τ := by
  simp [thetaChar]

@[simp]
theorem thetaChar_zero (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    thetaChar 0 τ α β r z = 0 := by
  simp [thetaChar, jacobiTheta₂_undef _ (by simp : (0 : ℂ).im ≤ 0)]

/-- When `τ.im ≤ 0`, the defining `jacobiTheta₂` series is not summable, so `thetaChar` takes the
junk value `0`. -/
theorem thetaChar_undef (k : ℕ) {τ : ℂ} (hτ : τ.im ≤ 0) (α β : ℝ) (r : ℤ) (z : ℂ) :
    thetaChar k τ α β r z = 0 := by
  have hkτ : ((k : ℂ) * τ).im ≤ 0 := by
    rw [← ofReal_natCast, im_ofReal_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hτ
  simp [thetaChar, jacobiTheta₂_undef _ hkτ]

/-- Shifting the characteristic index `r` by `k` rescales `thetaChar` by an explicit exponential
constant. -/
theorem thetaChar_add_nat (k : ℕ) (τ : ℂ) (α β : ℝ) (r : ℤ) (z : ℂ) :
    thetaChar k τ α β (r + k) z =
      cexp (2 * π * I * β - 2 * π * I * (r + α) * τ - π * I * k * τ) *
        thetaChar k τ α β r z := by
  simp only [thetaChar]
  have hw : (k : ℂ) * z + (((r + k : ℤ) : ℂ) + α) * τ - β =
      (k * z + (r + α) * τ - β) + k * τ := by
    push_cast
    ring
  rw [hw, jacobiTheta₂_add_left', ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Series expansion of `thetaChar k τ α β r z` along the progression `q * k + r` when `0 < k`
and `0 < τ.im`. -/
theorem hasSum_thetaChar {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) (r : ℤ) (z : ℂ) :
    HasSum (fun q : ℤ ↦
      jacobiTheta₂_term q ((r + α) * τ - β) (k * τ) * cexp (2 * π * I * (q * k + r + α) * z))
      (thetaChar k τ α β r z) := by
  have hkτ : 0 < ((k : ℂ) * τ).im := by
    rw [← ofReal_natCast, im_ofReal_mul]
    exact mul_pos (Nat.cast_pos.2 hk) hτ
  have hsum := (hasSum_jacobiTheta₂_term ((k : ℂ) * z + (r + α) * τ - β) hkτ).mul_left
    (cexp (2 * π * I * (r + α) * z))
  refine hsum.congr_fun fun q ↦ ?_
  simp only [jacobiTheta₂_term, ← Complex.exp_add]
  congr 1
  ring

/-- Each characteristic theta function `thetaChar k τ α β r` belongs to `thetaSections k τ α β`
when `0 < k` and `0 < τ.im`. -/
theorem thetaChar_mem_thetaSections {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r : ℤ) : thetaChar k τ α β r ∈ thetaSections k τ α β := by
  have hkτ : 0 < ((k : ℂ) * τ).im := by
    rw [← ofReal_natCast, im_ofReal_mul]
    exact mul_pos (Nat.cast_pos.2 hk) hτ
  refine ⟨?_, fun z ↦ ?_, fun z ↦ ?_⟩
  · refine (differentiable_exp.comp (differentiable_id.const_mul _)).mul fun z ↦ ?_
    exact (differentiableAt_jacobiTheta₂_fst _ hkτ).comp z
      (((differentiableAt_id.const_mul _).add_const _).sub_const _)
  · have hper1 : Function.Periodic (fun w : ℂ ↦ jacobiTheta₂ w (k * τ)) 1 :=
      fun w ↦ jacobiTheta₂_add_left w (k * τ)
    have hperk : ∀ w : ℂ, jacobiTheta₂ (w + k) (k * τ) = jacobiTheta₂ w (k * τ) := by
      simpa using hper1.nat_mul k
    simp only [thetaChar]
    rw [show (k : ℂ) * (z + 1) + (r + α) * τ - β = (k * z + (r + α) * τ - β) + k by ring,
      hperk, ← mul_assoc]
    have hexp : cexp (2 * π * I * ((r : ℂ) + α) * (z + 1)) =
        cexp (2 * π * I * α) * cexp (2 * π * I * (r + α) * z) := by
      rw [← Complex.exp_add, show 2 * π * I * ((r : ℂ) + α) * (z + 1) =
          (2 * π * I * α + 2 * π * I * (r + α) * z) + r * (2 * π * I) by ring,
        Complex.exp_add, exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, mul_assoc]
  · simp only [thetaChar]
    rw [show (k : ℂ) * (z + τ) + (r + α) * τ - β = (k * z + (r + α) * τ - β) + k * τ by ring,
      jacobiTheta₂_add_left', ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring

/-- Mathlib's `jacobiTheta₂ · τ` is a holomorphic section of `thetaSections 1 τ 0 0` when
`0 < τ.im`. -/
theorem jacobiTheta₂_mem_thetaSections {τ : ℂ} (hτ : 0 < τ.im) :
    (fun z ↦ jacobiTheta₂ z τ) ∈ thetaSections 1 τ 0 0 := by
  simpa [funext (thetaChar_one_zero_zero τ)] using
    thetaChar_mem_thetaSections zero_lt_one hτ 0 0 0

/-- Twisted Fourier coefficients of `thetaChar k τ α β r` at every integer frequency `m`:
supported on the arithmetic progression `q * k + r`, where the `(q * k + r)`-th coefficient is
`jacobiTheta₂_term q ((r + α) * τ - β) (k * τ)`. -/
private theorem thetaFourierCoeff_thetaChar_eq_extend {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (r m : ℤ) :
    thetaFourierCoeff α m (thetaChar k τ α β r) =
      Function.extend (fun q : ℤ ↦ q * k + r)
        (fun q ↦ jacobiTheta₂_term q ((r + α) * τ - β) (k * τ)) 0 m := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  let φ : ℤ → ℤ := fun q ↦ q * k + r
  have hφ : Function.Injective φ := fun a b hab ↦
    mul_right_cancel₀ (Nat.cast_ne_zero.2 hk.ne') (add_right_cancel hab)
  let c : ℤ → ℂ :=
    Function.extend φ (fun q ↦ jacobiTheta₂_term q ((r + α) * τ - β) (k * τ)) 0
  have hmem := thetaChar_mem_thetaSections hk hτ α β r
  have hperR : Function.Periodic
      (fun x : ℝ ↦ cexp (-2 * π * I * α * x) * thetaChar k τ α β r x) 1 := fun x ↦ by
    simpa using periodic_cexp_neg_mul_of_mem_thetaSections hmem x
  let G : AddCircle (1 : ℝ) → ℂ := hperR.lift
  have hsumG (y : AddCircle (1 : ℝ)) : HasSum (fun n : ℤ ↦ fourier n y • c n) (G y) := by
    refine QuotientAddGroup.induction_on y fun x : ℝ ↦ ?_
    rw [show G (x : AddCircle (1 : ℝ)) = cexp (-2 * π * I * α * x) * thetaChar k τ α β r x from
      hperR.lift_coe x]
    have hprog := (hasSum_thetaChar hk hτ α β r x).mul_left (cexp (-2 * π * I * α * x))
    have hcomp : HasSum (fun q : ℤ ↦ fourier (φ q) (x : AddCircle (1 : ℝ)) • c (φ q))
        (cexp (-2 * π * I * α * x) * thetaChar k τ α β r x) := by
      refine hprog.congr_fun fun q ↦ ?_
      simp only [c, hφ.extend_apply, fourier_coe_apply, ofReal_one, div_one, smul_eq_mul, φ]
      rw [mul_left_comm, ← Complex.exp_add, mul_comm]
      congr 2
      push_cast
      ring
    exact (hφ.hasSum_iff fun n hn ↦ by simp [c, Function.extend_apply' _ _ _ hn]).1 hcomp
  have hcoeff := congrFun (fourierCoeff_eq_of_hasSum hsumG) m
  have hFG : fourierCoeff G m = thetaFourierCoeff α m (thetaChar k τ α β r) := by
    rw [TauCeti.fourierCoeff_eq_fourierCoeffOn 0 G m]
    simp only [thetaFourierCoeff, G, hperR.lift_coe, fourierCoeffOn_eq_integral, zero_add]
  rw [← hFG, hcoeff]

/-- Along the progression `q * k + r`, the twisted Fourier coefficient of `thetaChar k τ α β r` is
`jacobiTheta₂_term q ((r + α) * τ - β) (k * τ)`. -/
theorem thetaFourierCoeff_int_mul_add_thetaChar {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) (q r : ℤ) :
    thetaFourierCoeff α (q * k + r) (thetaChar k τ α β r) =
      jacobiTheta₂_term q ((r + α) * τ - β) (k * τ) := by
  have hφ : Function.Injective (fun q : ℤ ↦ q * k + r) := fun a b hab ↦
    mul_right_cancel₀ (Nat.cast_ne_zero.2 hk.ne') (add_right_cancel hab)
  rw [thetaFourierCoeff_thetaChar_eq_extend hk hτ α β r (q * k + r), hφ.extend_apply]

/-- Outside the residue class of `r` modulo `k`, the twisted Fourier coefficients of
`thetaChar k τ α β r` vanish. -/
theorem thetaFourierCoeff_thetaChar_of_not_dvd {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im)
    (α β : ℝ) {r m : ℤ} (hndvd : ¬ (k : ℤ) ∣ m - r) :
    thetaFourierCoeff α m (thetaChar k τ α β r) = 0 := by
  rw [thetaFourierCoeff_thetaChar_eq_extend hk hτ α β r m, Function.extend_apply']
  · rfl
  · rintro ⟨q, hq⟩
    exact hndvd ⟨q, by linarith⟩

/-- **Duality between residue Fourier functionals and `thetaChar`.** On the fundamental residue
representatives `r, m : Fin k`, the `m`-th twisted Fourier coefficient of `thetaChar k τ α β r` is
`1` if `r = m` and `0` otherwise. -/
@[simp]
theorem thetaFourierCoeff_thetaChar {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r m : Fin k) :
    thetaFourierCoeff α m (thetaChar k τ α β r) = if r = m then 1 else 0 := by
  split_ifs with hrm
  · subst hrm
    simpa [jacobiTheta₂_term] using
      thetaFourierCoeff_int_mul_add_thetaChar hk hτ α β 0 (r : ℤ)
  · refine thetaFourierCoeff_thetaChar_of_not_dvd hk hτ α β fun hdvd ↦ hrm ?_
    have hlt : |(m : ℤ) - (r : ℤ)| < (k : ℤ) := by
      rw [abs_lt]
      have hr := r.isLt
      have hm := m.isLt
      omega
    have hzero : (m : ℤ) - (r : ℤ) = 0 :=
      Int.eq_zero_of_abs_lt_dvd hdvd hlt
    exact Fin.ext (by omega)

/-- **Basis expansion of any theta section.** For `0 < k` and `0 < τ.im`, every
`s ∈ thetaSections k τ α β` is the linear combination of `thetaChar k τ α β r` (`r : Fin k`)
weighted by its first `k` twisted Fourier coefficients `thetaFourierCoeff α r s`. -/
theorem eq_sum_thetaFourierCoeff_mul_thetaChar {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im)
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections k τ α β) (z : ℂ) :
    s z = ∑ r : Fin k, thetaFourierCoeff α r s * thetaChar k τ α β r z := by
  have : NeZero k := ⟨hk.ne'⟩
  rw [← tsum_thetaFourierCoeff_of_mem_thetaSections hs z,
    TauCeti.tsum_int_eq_sum_fin_tsum (summable_thetaFourierCoeff_of_mem_thetaSections hs z) k]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have hterm (q : ℤ) :
      thetaFourierCoeff α (q * k + (r : ℤ)) s *
          cexp (2 * π * I * ((q * k + (r : ℤ) : ℤ) + α) * z) =
        thetaFourierCoeff α (r : ℤ) s *
          (jacobiTheta₂_term q (((r : ℤ) + α) * τ - β) (k * τ) *
            cexp (2 * π * I * (q * k + (r : ℤ) + α) * z)) := by
    rw [thetaFourierCoeff_int_mul_add hs q (r : ℤ)]
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, (hasSum_thetaChar hk hτ α β (r : ℤ) z).tsum_eq]

/-- The `r`-th characteristic theta function bundled as an element of `thetaSections k τ α β`. -/
noncomputable def thetaCharSection {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r : Fin k) : thetaSections k τ α β :=
  ⟨thetaChar k τ α β r, thetaChar_mem_thetaSections hk hτ α β r⟩

@[simp]
theorem coe_thetaCharSection {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r : Fin k) :
    (thetaCharSection hk hτ α β r : ℂ → ℂ) = thetaChar k τ α β r :=
  (rfl)

/-- **Residue Fourier isomorphism.** For `0 < k` and `0 < τ.im`, restricting the twisted Fourier
coefficients to `Fin k` is a `ℂ`-linear isomorphism `thetaSections k τ α β ≃ₗ[ℂ] (Fin k → ℂ)`
whose inverse synthesizes linear combinations of `thetaCharSection`. -/
noncomputable def thetaFourierEquiv {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) :
    thetaSections k τ α β ≃ₗ[ℂ] (Fin k → ℂ) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun r : Fin k ↦ thetaFourierCoeffLM k τ α β r)
    (Fintype.linearCombination ℂ (thetaCharSection hk hτ α β))
    (LinearMap.ext fun v ↦ funext fun m ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply,
        Fintype.linearCombination_apply, map_sum, map_smul, thetaFourierCoeffLM_apply,
        coe_thetaCharSection, thetaFourierCoeff_thetaChar hk hτ α β, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, LinearMap.id_apply])
    (LinearMap.ext fun s ↦ Subtype.ext <| funext fun z ↦ by
      simp only [LinearMap.coe_comp, Function.comp_apply, Fintype.linearCombination_apply,
        LinearMap.pi_apply, thetaFourierCoeffLM_apply, Submodule.coe_sum,
        Submodule.coe_smul_of_tower, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        coe_thetaCharSection, LinearMap.id_apply]
      exact (eq_sum_thetaFourierCoeff_mul_thetaChar hk hτ s.2 z).symm)

@[simp]
theorem thetaFourierEquiv_apply {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (s : thetaSections k τ α β) (r : Fin k) :
    thetaFourierEquiv hk hτ α β s r = thetaFourierCoeff α r (s : ℂ → ℂ) :=
  (rfl)

@[simp]
theorem thetaFourierEquiv_symm_apply {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (v : Fin k → ℂ) :
    (thetaFourierEquiv hk hτ α β).symm v =
      ∑ r : Fin k, v r • thetaCharSection hk hτ α β r := by
  simp [thetaFourierEquiv, Fintype.linearCombination_apply]

/-- **Explicit basis of characteristic theta sections.** For `0 < k` and `0 < τ.im`, the `k`
characteristic theta sections `thetaCharSection hk hτ α β` form a `ℂ`-basis of
`thetaSections k τ α β` whose coordinate functionals are the first `k` twisted Fourier
coefficients. -/
noncomputable def thetaBasis {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) :
    Module.Basis (Fin k) ℂ (thetaSections k τ α β) :=
  Module.Basis.ofEquivFun (thetaFourierEquiv hk hτ α β)

@[simp]
theorem thetaBasis_apply {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) (r : Fin k) :
    thetaBasis hk hτ α β r = thetaCharSection hk hτ α β r := by
  rw [thetaBasis, Module.Basis.coe_ofEquivFun]
  simp [Pi.single_apply]

theorem coe_thetaBasis_apply {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (r : Fin k) :
    ((thetaBasis hk hτ α β r : thetaSections k τ α β) : ℂ → ℂ) = thetaChar k τ α β r := by
  simp

@[simp]
theorem thetaBasis_repr_apply {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ)
    (s : thetaSections k τ α β) (r : Fin k) :
    (thetaBasis hk hτ α β).repr s r = thetaFourierCoeff α r (s : ℂ → ℂ) := by
  rw [thetaBasis, Module.Basis.ofEquivFun_repr_apply, thetaFourierEquiv_apply]

/-- For `0 < k` and `0 < τ.im`, the space `thetaSections k τ α β` is finite-dimensional over
`ℂ`. -/
theorem finiteDimensional_thetaSections {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) :
    FiniteDimensional ℂ (thetaSections k τ α β) :=
  Module.Finite.of_basis (thetaBasis hk hτ α β)

/-- **Dimension of the Kähler theta-section space on a degree-`k` complex torus.** For every
positive integer level `k > 0`, modulus `τ` in the upper half-plane (`0 < τ.im`), and real
characteristics `α, β`, the space `thetaSections k τ α β` has complex dimension `k`. -/
theorem finrank_thetaSections {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : 0 < τ.im) (α β : ℝ) :
    Module.finrank ℂ (thetaSections k τ α β) = k := by
  rw [Module.finrank_eq_card_basis (thetaBasis hk hτ α β), Fintype.card_fin]

/-! ### Sharpness: non-positive imaginary modulus (`τ.im ≤ 0`) and level zero (`k = 0`) -/

/-- **Vanishing outside the upper half-plane.** When `0 < k` and `τ.im ≤ 0`, the progression
formula forces every nonzero Fourier residue class to diverge by `summable_jacobiTheta₂_term_iff`,
so `thetaSections k τ α β = ⊥`. -/
theorem thetaSections_eq_bot_of_im_nonpos {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : τ.im ≤ 0)
    (α β : ℝ) : thetaSections k τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  refine eq_zero_of_forall_thetaFourierCoeff_eq_zero hs fun r ↦ ?_
  by_contra hcr
  have hsum0 : Summable fun m : ℤ ↦ thetaFourierCoeff α m s := by
    simpa using summable_thetaFourierCoeff_of_mem_thetaSections hs 0
  have hφ : Function.Injective (fun q : ℤ ↦ q * k + r) := fun a b hab ↦
    mul_right_cancel₀ (Nat.cast_ne_zero.2 hk.ne') (add_right_cancel hab)
  have hprog : Summable fun q : ℤ ↦
      jacobiTheta₂_term q ((r + α) * τ - β) (k * τ) * thetaFourierCoeff α r s := by
    simpa [Function.comp_def, thetaFourierCoeff_int_mul_add hs] using hsum0.comp_injective hφ
  have hjac : Summable fun q : ℤ ↦ jacobiTheta₂_term q ((r + α) * τ - β) (k * τ) := by
    simpa [mul_inv_cancel_right₀ hcr] using hprog.mul_right (thetaFourierCoeff α r s)⁻¹
  have hkτ_pos : 0 < ((k : ℂ) * τ).im := (summable_jacobiTheta₂_term_iff _ _).1 hjac
  rw [← ofReal_natCast, im_ofReal_mul] at hkτ_pos
  have hkτ_nonpos : (k : ℝ) * τ.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hτ
  linarith

/-- When `0 < k` and `τ.im ≤ 0`, `thetaSections k τ α β` has complex dimension `0`. -/
theorem finrank_thetaSections_of_im_nonpos {k : ℕ} (hk : 0 < k) {τ : ℂ} (hτ : τ.im ≤ 0)
    (α β : ℝ) : Module.finrank ℂ (thetaSections k τ α β) = 0 := by
  rw [thetaSections_eq_bot_of_im_nonpos hk hτ α β, finrank_bot]

/-- For positive level `0 < k`, `thetaSections k τ α β` is nontrivial if and only if `0 < τ.im`. -/
theorem nontrivial_thetaSections_iff {k : ℕ} (hk : 0 < k) (τ : ℂ) (α β : ℝ) :
    Nontrivial (thetaSections k τ α β) ↔ 0 < τ.im := by
  constructor
  · intro hnt
    by_contra! hτ
    rw [thetaSections_eq_bot_of_im_nonpos hk hτ α β] at hnt
    exact not_nontrivial (⊥ : Submodule ℂ (ℂ → ℂ)) hnt
  · intro hτ
    have hfin := finrank_thetaSections hk hτ α β
    exact Module.nontrivial_of_finrank_pos (hfin ▸ hk)

/-- At level `k = 0` with `τ.im ≠ 0`, any nonzero `m`-th twisted Fourier coefficient of
`s ∈ thetaSections 0 τ α β` forces `α = -m` and `β ∈ Set.range Int.cast`. -/
private theorem eq_neg_intCast_of_thetaFourierCoeff_zero_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0)
    {α β : ℝ} {s : ℂ → ℂ} (hs : s ∈ thetaSections 0 τ α β) {m : ℤ}
    (hm : thetaFourierCoeff α m s ≠ 0) :
    α = -(m : ℝ) ∧ ∃ n : ℤ, β = n := by
  have hrec := thetaFourierCoeff_add_nat hs m
  simp only [Nat.cast_zero, add_zero, mul_zero, zero_mul] at hrec
  have hexp1 : cexp (2 * π * I * (m + α) * τ - 2 * π * I * β) = 1 :=
    mul_right_cancel₀ hm (by linear_combination hrec.symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 hexp1
  have hpi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hlin : ((m : ℂ) + α) * τ - β = n :=
    mul_right_cancel₀ hpi (by linear_combination hn)
  have him : ((m : ℝ) + α) * τ.im = 0 := by
    have := congrArg Complex.im hlin
    simpa [im_ofReal_mul] using this
  have hmα : (m : ℝ) + α = 0 := (mul_eq_zero.1 him).resolve_right hτ
  have hα : α = -(m : ℝ) := eq_neg_of_add_eq_zero_right hmα
  have hre : -β = (n : ℝ) := by
    have := congrArg Complex.re hlin
    simp only [sub_re, ofReal_re, intCast_re] at this
    have hzero : (((m : ℂ) + α) * τ).re = 0 := by
      have hc : (m : ℂ) + α = 0 := by exact_mod_cast hmα
      simp [hc]
    linarith
  exact ⟨hα, -n, by push_cast; linarith⟩

/-- **Level `k = 0` characterization.** For `τ.im ≠ 0`, `s ∈ thetaSections 0 τ α β` if and only if
either `s = 0` or both `α, β` are integers and `s` is a constant function. -/
theorem mem_thetaSections_zero_iff {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ} {s : ℂ → ℂ} :
    s ∈ thetaSections 0 τ α β ↔
      s = 0 ∨ ((∃ p : ℤ, α = p) ∧ (∃ q : ℤ, β = q) ∧ ∃ c : ℂ, s = Function.const ℂ c) := by
  constructor
  · intro hs
    by_cases hall : ∀ m : ℤ, thetaFourierCoeff α m s = 0
    · exact Or.inl (eq_zero_of_forall_thetaFourierCoeff_eq_zero hs hall)
    · push Not at hall
      obtain ⟨m₀, hm₀⟩ := hall
      obtain ⟨hα, n₀, hβ⟩ := eq_neg_intCast_of_thetaFourierCoeff_zero_ne_zero hτ hs hm₀
      refine Or.inr ⟨⟨-m₀, by push_cast; exact hα⟩, ⟨n₀, hβ⟩, thetaFourierCoeff α m₀ s, ?_⟩
      ext z
      rw [← tsum_thetaFourierCoeff_of_mem_thetaSections hs z, tsum_eq_single m₀]
      · simp [hα, Function.const_apply]
      · intro m hm
        by_contra hcm
        have hcm0 : thetaFourierCoeff α m s ≠ 0 := left_ne_zero_of_mul hcm
        obtain ⟨hα', -⟩ := eq_neg_intCast_of_thetaFourierCoeff_zero_ne_zero hτ hs hcm0
        have : (m : ℝ) = (m₀ : ℝ) := by linarith
        exact hm (Int.cast_injective this)
  · rintro (rfl | ⟨⟨p, rfl⟩, ⟨q, rfl⟩, c, rfl⟩)
    · exact (thetaSections 0 τ α β).zero_mem
    · have hpq := thetaSections_add_int 0 τ 0 0 p q
      simp only [zero_add] at hpq
      rw [hpq, mem_thetaSections_iff]
      exact ⟨differentiable_const c, fun _ ↦ by simp, fun _ ↦ by simp⟩

/-- At level `k = 0` with `τ.im ≠ 0`, if `(α, β)` is not in `ℤ × ℤ`, then
`thetaSections 0 τ α β = ⊥`. -/
theorem thetaSections_zero_eq_bot_of_not_int {τ : ℂ} (hτ : τ.im ≠ 0) {α β : ℝ}
    (h : ¬ ((∃ p : ℤ, α = p) ∧ ∃ q : ℤ, β = q)) :
    thetaSections 0 τ α β = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro s hs
  rcases (mem_thetaSections_zero_iff hτ).1 hs with rfl | ⟨hα, hβ, -⟩
  · rfl
  · exact False.elim (h ⟨hα, hβ⟩)

/-- At level `k = 0` and zero characteristics with `τ.im ≠ 0`, the doubly periodic entire functions
`thetaSections 0 τ 0 0` are precisely the constant functions. -/
theorem mem_thetaSections_zero_zero_iff {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℂ → ℂ} :
    s ∈ thetaSections 0 τ 0 0 ↔ ∃ c : ℂ, s = Function.const ℂ c := by
  rw [mem_thetaSections_zero_iff hτ]
  constructor
  · rintro (rfl | ⟨-, -, c, hc⟩)
    · exact ⟨0, rfl⟩
    · exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact Or.inr ⟨⟨0, by simp⟩, ⟨0, by simp⟩, c, hc⟩

/-- At level `k = 0` and zero characteristics with `τ.im ≠ 0`, `thetaSections 0 τ 0 0` has complex
dimension `1` (spanned by the constant function `1`), showing that `0 < k` cannot be dropped in
`finrank_thetaSections`. -/
theorem finrank_thetaSections_zero_zero {τ : ℂ} (hτ : τ.im ≠ 0) :
    Module.finrank ℂ (thetaSections 0 τ 0 0) = 1 := by
  let e : ℂ ≃ₗ[ℂ] thetaSections 0 τ 0 0 :=
    { toFun := fun c ↦ ⟨Function.const ℂ c, (mem_thetaSections_zero_zero_iff hτ).2 ⟨c, rfl⟩⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      invFun := fun s ↦ (s : ℂ → ℂ) 0
      left_inv := fun _ ↦ rfl
      right_inv := fun s ↦ Subtype.ext <| by
        obtain ⟨c, hc⟩ := (mem_thetaSections_zero_zero_iff hτ).1 s.2
        simp [hc] }
  simpa using e.symm.finrank_eq

/-- **Flat-bundle integrality dichotomy at `k = 0`.** For `τ.im ≠ 0`, `thetaSections 0 τ α β` is
nontrivial if and only if both characteristics `α` and `β` are integers. -/
theorem nontrivial_thetaSections_zero_iff {τ : ℂ} (hτ : τ.im ≠ 0) (α β : ℝ) :
    Nontrivial (thetaSections 0 τ α β) ↔ (∃ p : ℤ, α = p) ∧ ∃ q : ℤ, β = q := by
  constructor
  · intro hnt
    by_contra h
    rw [thetaSections_zero_eq_bot_of_not_int hτ h] at hnt
    exact not_nontrivial (⊥ : Submodule ℂ (ℂ → ℂ)) hnt
  · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
    have hpq := thetaSections_add_int 0 τ 0 0 p q
    simp only [zero_add] at hpq
    rw [hpq]
    exact Module.nontrivial_of_finrank_eq_succ (finrank_thetaSections_zero_zero hτ)

end TauCeti
