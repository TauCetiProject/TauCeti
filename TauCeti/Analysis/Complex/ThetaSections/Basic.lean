/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThetaLine
public import TauCeti.NumberTheory.ModularForms.JacobiTheta.Sections
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Lattice automorphy, integrality obstruction, and operations on theta sections

This file complements `TauCeti.Analysis.Complex.ThetaLine` and
`TauCeti.NumberTheory.ModularForms.JacobiTheta.Sections` with additional structural properties
of the automorphy factor `TauCeti.thetaFactor` and the section space `TauCeti.thetaSections`:

* `TauCeti.thetaFactor_add_int`: shifting the characteristics `(α, β)` by integers leaves
  `thetaFactor` invariant.
* `TauCeti.exp_thetaAutomorphy_commutator` and
  `TauCeti.exp_thetaAutomorphy_commutator_eq_iff_exists_intCast_eq`: for a real level `k : ℝ`,
  composing the `z ↦ z + 1` and `z ↦ z + τ` generator factors in the two orders differs by the
  phase `exp (-2πik)`, so they commute if and only if `k` is an integer.
* `TauCeti.add_int_add_int_mul_tau_of_mem_thetaSections` and
  `TauCeti.mem_thetaSections_iff_forall_add_int_add_int_mul_tau`: bridging `thetaSections` with
  full `ℤ²`-automorphy via `thetaFactor`.
* `TauCeti.thetaSections_add_int` and `TauCeti.mul_mem_thetaSections`: integer characteristic
  invariance and level-additive multiplication of theta sections.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §1–§4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, 2nd edition, Grundlehren
  der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

open Complex
open scoped Real

namespace TauCeti

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

/-- For an arbitrary real level `k : ℝ`, composing the `z ↦ z + 1` and `z ↦ z + τ` automorphy
factors in the two orders differs by the constant phase `exp (-2πik)`. -/
theorem exp_thetaAutomorphy_commutator (k : ℝ) (τ : ℂ) (α β : ℝ) (z : ℂ) :
    cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + 1)) * cexp (2 * π * I * α) =
      cexp (-2 * π * I * k) *
        (cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z)) := by
  simp only [← Complex.exp_add]
  congr 1
  ring

/-- **Integrality obstruction for the torus automorphy factor.** The `z ↦ z + 1` and `z ↦ z + τ`
generator factors at real level `k : ℝ` satisfy the abelian compatibility relation if and only if
`k` is an integer. -/
theorem exp_thetaAutomorphy_commutator_eq_iff_exists_intCast_eq (k : ℝ) (τ : ℂ) (α β : ℝ)
    (z : ℂ) :
    cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * (z + 1)) * cexp (2 * π * I * α) =
        cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) ↔
      ∃ n : ℤ, (n : ℝ) = k := by
  rw [exp_thetaAutomorphy_commutator]
  have hne :
      cexp (2 * π * I * α) * cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  have hneg : -2 * π * I * (k : ℂ) = -(2 * π * I * k) := by ring
  rw [mul_eq_right₀ hne, hneg, Complex.exp_neg, inv_eq_one,
    Complex.exp_two_pi_mul_I_mul_ofReal_eq_one_iff]

/-- Full lattice automorphy law for a holomorphic theta section under any translation
`z ↦ z + m + n * τ`. -/
theorem add_int_add_int_mul_tau_of_mem_thetaSections {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}
    (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    s (z + m + n * τ) = thetaFactor k τ α β m n z * s z := by
  rcases mem_thetaSections_iff.mp hs with ⟨_, h1, hτ⟩
  exact forall_add_eq_thetaFactor_mul_iff.mpr ⟨h1, by simpa using hτ⟩ m n z

/-- Membership in `thetaSections` is equivalent to being entire and satisfying the full
`ℤ²`-automorphy law with factor `thetaFactor`. -/
theorem mem_thetaSections_iff_forall_add_int_add_int_mul_tau {k : ℕ} {τ : ℂ} {α β : ℝ}
    {s : ℂ → ℂ} :
    s ∈ thetaSections k τ α β ↔
      Differentiable ℂ s ∧
        ∀ m n : ℤ, ∀ z : ℂ, s (z + m + n * τ) = thetaFactor k τ α β m n z * s z := by
  rw [mem_thetaSections_iff, forall_add_eq_thetaFactor_mul_iff]
  simp only [Int.cast_natCast]

/-- Shifting the characteristics `(α, β)` by integers does not change the space of theta
sections. -/
theorem thetaSections_add_int (k : ℕ) (τ : ℂ) (α β : ℝ) (a b : ℤ) :
    thetaSections k τ (α + a) (β + b) = thetaSections k τ α β := by
  ext s
  have hα : cexp (2 * π * I * (α + a : ℝ)) = cexp (2 * π * I * α) := by
    simpa only [thetaFactor_one_zero] using thetaFactor_add_int k τ α β a b 1 0 0
  have hβ : ∀ z : ℂ,
      cexp (2 * π * I * (β + b : ℝ) - π * I * k * τ - 2 * π * I * k * z) =
        cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) := fun z => by
    simpa only [thetaFactor_zero_one, Int.cast_natCast] using
      thetaFactor_add_int k τ α β a b 0 1 z
  simp only [mem_thetaSections_iff, hα, hβ]

/-- Pointwise multiplication of theta sections adds levels and characteristics. -/
theorem mul_mem_thetaSections {k₁ k₂ : ℕ} {τ : ℂ} {α₁ β₁ α₂ β₂ : ℝ} {s₁ s₂ : ℂ → ℂ}
    (hs₁ : s₁ ∈ thetaSections k₁ τ α₁ β₁) (hs₂ : s₂ ∈ thetaSections k₂ τ α₂ β₂) :
    (fun z => s₁ z * s₂ z) ∈ thetaSections (k₁ + k₂) τ (α₁ + α₂) (β₁ + β₂) := by
  rcases mem_thetaSections_iff.mp hs₁ with ⟨hd₁, h1₁, hτ₁⟩
  rcases mem_thetaSections_iff.mp hs₂ with ⟨hd₂, h1₂, hτ₂⟩
  refine mem_thetaSections_iff.mpr ⟨hd₁.mul hd₂, fun z => ?_, fun z => ?_⟩
  · rw [h1₁, h1₂]
    have hmul := thetaFactor_mul_thetaFactor (k := k₁) (τ := τ) (α := α₁) (β := β₁)
      k₂ α₂ β₂ 1 0 z
    simp only [thetaFactor_one_zero] at hmul
    rw [mul_mul_mul_comm, hmul]
  · rw [hτ₁, hτ₂]
    have hmul := thetaFactor_mul_thetaFactor (k := k₁) (τ := τ) (α := α₁) (β := β₁)
      k₂ α₂ β₂ 0 1 z
    simp only [thetaFactor_zero_one, Int.cast_add, Int.cast_natCast, Nat.cast_add] at hmul ⊢
    rw [mul_mul_mul_comm, hmul]

end TauCeti
