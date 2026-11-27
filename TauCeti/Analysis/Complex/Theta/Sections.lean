/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Theta.Factor

/-!
# Holomorphic sections of the level-`k` theta line

Fix `k : ℕ`, `τ : ℂ`, and real characteristics `α, β`. The entire functions `s : ℂ → ℂ` with the
automorphy laws `s (z + 1) = e^{2πiα} s z` and `s (z + τ) = e^{2πiβ - πikτ - 2πikz} s z` are the
holomorphic sections, pulled back to the universal cover `ℂ`, of the degree-`k` theta line on the
complex torus `ℂ / (ℤ + τℤ)`. They form the complex vector space `TauCeti.thetaSections k τ α β`.

## Main definitions

* `TauCeti.thetaSections k τ α β`: the submodule of entire functions satisfying the two
  automorphy laws.

## Main results

* `TauCeti.mem_thetaSections_iff`: membership criterion in `thetaSections`.
* `TauCeti.add_eq_thetaFactor_mul_of_mem_thetaSections` and
  `TauCeti.mem_thetaSections_iff_forall_add_eq_thetaFactor_mul`: bridging `thetaSections` with
  full `ℤ²`-automorphy via `thetaFactor`.
* `TauCeti.thetaSections_add_int` and `TauCeti.mul_mem_thetaSections`: integer characteristic
  invariance and level-additive multiplication of theta sections.

## References

* David Mumford, *Tata Lectures on Theta I*, Progress in Mathematics 28, Birkhäuser, 1983,
  Chapter I, §§1–4.
* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 2 and Chapter 3.
-/

public section

open Complex
open scoped Real

namespace TauCeti

/-- The holomorphic sections of the level-`k` theta line with characteristics `(α, β)` on the
complex torus `ℂ / (ℤ + τℤ)`, pulled back to the universal cover `ℂ`: the entire functions `s`
with `s (z + 1) = e^{2πiα} s z` and `s (z + τ) = e^{2πiβ - πikτ - 2πikz} s z` for all `z`. -/
def thetaSections (k : ℕ) (τ : ℂ) (α β : ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {s | Differentiable ℂ s ∧ (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
    ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z}
  add_mem' := by
    rintro f g ⟨hf, hf1, hfτ⟩ ⟨hg, hg1, hgτ⟩
    exact ⟨hf.add hg, fun z ↦ by simp [hf1, hg1, mul_add], fun z ↦ by simp [hfτ, hgτ, mul_add]⟩
  zero_mem' := ⟨differentiable_const 0, fun z ↦ by simp, fun z ↦ by simp⟩
  smul_mem' := by
    rintro c f ⟨hf, hf1, hfτ⟩
    exact ⟨hf.const_smul c, fun z ↦ by simp [hf1]; ring, fun z ↦ by simp [hfτ]; ring⟩

variable {k : ℕ} {τ : ℂ} {α β : ℝ} {s : ℂ → ℂ}

/-- Membership in `thetaSections k τ α β`: being entire with the two automorphy laws. -/
theorem mem_thetaSections_iff : s ∈ thetaSections k τ α β ↔ Differentiable ℂ s ∧
    (∀ z, s (z + 1) = cexp (2 * π * I * α) * s z) ∧
    ∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z :=
  Iff.rfl

/-- Full lattice automorphy law for a holomorphic theta section under any translation
`z ↦ z + m + n * τ`. -/
theorem add_eq_thetaFactor_mul_of_mem_thetaSections
    (hs : s ∈ thetaSections k τ α β) (m n : ℤ) (z : ℂ) :
    s (z + m + n * τ) = thetaFactor k τ α β m n z * s z := by
  rcases mem_thetaSections_iff.mp hs with ⟨_, h1, hτ⟩
  exact forall_add_eq_thetaFactor_mul_iff.mpr ⟨h1, by simpa only [Int.cast_natCast] using hτ⟩ m n z

/-- Membership in `thetaSections` is equivalent to being entire and satisfying the full
`ℤ²`-automorphy law with factor `thetaFactor`. -/
theorem mem_thetaSections_iff_forall_add_eq_thetaFactor_mul :
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
