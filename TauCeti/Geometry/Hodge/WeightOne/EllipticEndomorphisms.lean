/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Rational Hodge endomorphisms of an elliptic curve

For `τ ∈ ℂ` with `Im τ ≠ 0`, the rational homology of the elliptic curve `E_τ = ℂ / (ℤ + ℤτ)` is
the `ℚ`-span `L_τ = ℚ + ℚτ ⊆ ℂ`, and its rational Hodge endomorphisms are the multiplications by
complex numbers `α` preserving `L_τ`. They form a `ℚ`-subalgebra of `ℂ`,
`TauCeti.ellipticHodgeEndomorphisms τ`.

Multiplication by `α` preserves `L_τ` exactly when `α = a + cτ` and `ατ = b + dτ` for rational
`a, b, c, d` (`TauCeti.mem_ellipticHodgeEndomorphisms_iff`); then `cτ² + (a - d)τ - b = 0`. So the
algebra is `ℚ` unless `τ` satisfies a rational quadratic equation
(`TauCeti.ellipticHodgeEndomorphisms_eq_bot`), and when it does, that is when `τ` is imaginary
quadratic, the algebra contains `τ` (`TauCeti.mem_ellipticHodgeEndomorphisms_self_iff`), so it is
`ℚ(τ)`.

## Main declarations

* `TauCeti.ellipticHodgeEndomorphisms τ`: the `ℚ`-algebra of `α ∈ ℂ` with `α L_τ ⊆ L_τ`.
* `TauCeti.mem_ellipticHodgeEndomorphisms_iff`: `α = a + cτ` and `ατ = b + dτ`.
* `TauCeti.quadratic_relation_of_mem_ellipticHodgeEndomorphisms`: `cτ² + (a - d)τ - b = 0`.
* `TauCeti.ellipticHodgeEndomorphisms_eq_bot`: without a rational quadratic relation the algebra is
  `ℚ`.
* `TauCeti.mem_ellipticHodgeEndomorphisms_self_iff`: `τ` is a Hodge endomorphism exactly when
  `τ² ∈ L_τ`.

## References

* J. S. Milne, *Shimura varieties and moduli*, in *Handbook of Moduli* II (2013), Propositions
  6.3–6.4 and Corollary 6.5, pp. 494–495.
-/

public section

noncomputable section

namespace TauCeti

open Complex

/-- The rational span `L_τ = ℚ + ℚτ` of `1` and `τ` in `ℂ`. -/
abbrev ellipticRationalLattice (τ : ℂ) : Submodule ℚ ℂ :=
  Submodule.span ℚ {1, τ}

theorem mem_ellipticRationalLattice_iff {τ x : ℂ} :
    x ∈ ellipticRationalLattice τ ↔ ∃ a b : ℚ, x = a + b * τ := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by simp [Rat.smul_def]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by simp [Rat.smul_def]⟩

/-- **The rational Hodge endomorphisms of `E_τ`**: the `ℚ`-subalgebra of the `α ∈ ℂ` whose
multiplication preserves `L_τ = ℚ + ℚτ`. -/
def ellipticHodgeEndomorphisms (τ : ℂ) : Subalgebra ℚ ℂ where
  carrier := {α | ∀ x ∈ ellipticRationalLattice τ, α * x ∈ ellipticRationalLattice τ}
  mul_mem' {α β} hα hβ x hx := by
    rw [mul_assoc]
    exact hα _ (hβ x hx)
  add_mem' {α β} hα hβ x hx := by
    rw [add_mul]
    exact add_mem (hα x hx) (hβ x hx)
  algebraMap_mem' q x hx := by
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ q hx

theorem mem_ellipticHodgeEndomorphisms {τ α : ℂ} :
    α ∈ ellipticHodgeEndomorphisms τ ↔
      ∀ x ∈ ellipticRationalLattice τ, α * x ∈ ellipticRationalLattice τ :=
  Iff.rfl

/-- **Multiplication by `α` preserves `ℚ + ℚτ` exactly when `α = a + cτ` and `ατ = b + dτ`** for
rational `a, b, c, d`. -/
theorem mem_ellipticHodgeEndomorphisms_iff {τ α : ℂ} :
    α ∈ ellipticHodgeEndomorphisms τ ↔
      ∃ a b c d : ℚ, α = a + c * τ ∧ α * τ = b + d * τ := by
  constructor
  · intro h
    obtain ⟨a, c, hac⟩ := mem_ellipticRationalLattice_iff.mp
      (by simpa using h 1 (Submodule.subset_span (by simp)))
    obtain ⟨b, d, hbd⟩ := mem_ellipticRationalLattice_iff.mp
      (h τ (Submodule.subset_span (by simp)))
    exact ⟨a, b, c, d, hac, hbd⟩
  · rintro ⟨a, b, c, d, hα, hατ⟩ x hx
    obtain ⟨p, q, rfl⟩ := mem_ellipticRationalLattice_iff.mp hx
    rw [mem_ellipticRationalLattice_iff]
    refine ⟨p * a + q * b, p * c + q * d, ?_⟩
    rw [mul_add, mul_left_comm, hατ, mul_comm α, hα]
    push_cast
    ring

/-- A Hodge endomorphism `α = a + cτ` with `ατ = b + dτ` gives the rational quadratic relation
`cτ² + (a - d)τ - b = 0`. -/
theorem quadratic_relation_of_mem_ellipticHodgeEndomorphisms {τ α : ℂ} {a b c d : ℚ}
    (hα : α = a + c * τ) (hατ : α * τ = b + d * τ) :
    (c : ℂ) * τ ^ 2 + (a - d) * τ - b = 0 := by
  rw [hα] at hατ
  linear_combination hατ

/-- **Without a rational quadratic relation, the Hodge endomorphisms of `E_τ` are `ℚ`.** If `τ`
satisfies no equation `cτ² + eτ + f = 0` with rational `c ≠ 0`, every `α` preserving `ℚ + ℚτ` is
rational: writing `α = a + cτ`, the relation `cτ² + (a - d)τ - b = 0` forces `c = 0`. -/
theorem ellipticHodgeEndomorphisms_eq_bot {τ : ℂ}
    (hq : ∀ c e f : ℚ, (c : ℂ) * τ ^ 2 + e * τ + f = 0 → c = 0) :
    ellipticHodgeEndomorphisms τ = ⊥ := by
  refine eq_bot_iff.mpr fun α h ↦ ?_
  obtain ⟨a, b, c, d, hα, hατ⟩ := mem_ellipticHodgeEndomorphisms_iff.mp h
  have hc : c = 0 := hq c (a - d) (-b) (by
    push_cast
    linear_combination quadratic_relation_of_mem_ellipticHodgeEndomorphisms hα hατ)
  rw [hc, Rat.cast_zero, zero_mul, add_zero] at hα
  exact hα ▸ Subalgebra.algebraMap_mem ⊥ a

/-- `τ` is a Hodge endomorphism of `E_τ` exactly when `τ² ∈ ℚ + ℚτ`, that is when `τ` satisfies a
monic rational quadratic equation. -/
theorem mem_ellipticHodgeEndomorphisms_self_iff {τ : ℂ} :
    τ ∈ ellipticHodgeEndomorphisms τ ↔ ∃ b d : ℚ, τ ^ 2 = b + d * τ := by
  rw [mem_ellipticHodgeEndomorphisms_iff]
  constructor
  · rintro ⟨a, b, c, d, -, h⟩
    exact ⟨b, d, by rw [sq, h]⟩
  · rintro ⟨b, d, h⟩
    exact ⟨0, b, 1, d, by simp, by rw [← sq, h]⟩

end TauCeti
