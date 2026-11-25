/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Adjoin.Basic
public import TauCeti.RingTheory.IntegralOrder.LeftOrder

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
quadratic, the algebra contains `τ` (`TauCeti.mem_ellipticHodgeEndomorphisms_self_iff`) and is
`ℚ(τ)` (`TauCeti.ellipticHodgeEndomorphisms_eq_adjoin`).

The declarations take any `τ : ℂ` and describe the left order of `ℚ + ℚτ`; it is the algebra of
rational Hodge endomorphisms of `E_τ` when `Im τ ≠ 0`.

## Main declarations

* `TauCeti.ellipticHodgeEndomorphisms τ`: the `ℚ`-algebra of `α ∈ ℂ` with `α L_τ ⊆ L_τ`, the left
  order of `L_τ`.
* `TauCeti.mem_ellipticHodgeEndomorphisms_iff`: `α = a + cτ` and `ατ = b + dτ`.
* `TauCeti.quadratic_relation_of_eq_add_mul_of_mul_eq_add_mul`: `cτ² + (a - d)τ - b = 0`.
* `TauCeti.ellipticHodgeEndomorphisms_eq_bot`: without a rational quadratic relation the algebra is
  `ℚ`.
* `TauCeti.mem_ellipticHodgeEndomorphisms_self_iff`: `τ` lies in the algebra exactly when
  `τ² ∈ L_τ`.
* `TauCeti.ellipticHodgeEndomorphisms_eq_adjoin`: when `τ² ∈ L_τ` the algebra is `ℚ(τ)`.
-/

public section

noncomputable section

namespace TauCeti

open Complex

/-- The rational span `L_τ = ℚ + ℚτ` of `1` and `τ` in `ℂ`. -/
abbrev ellipticRationalSpan (τ : ℂ) : Submodule ℚ ℂ :=
  Submodule.span ℚ {1, τ}

theorem mem_ellipticRationalSpan_iff {τ x : ℂ} :
    x ∈ ellipticRationalSpan τ ↔ ∃ a b : ℚ, x = a + b * τ := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by simp [Rat.smul_def]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨a, b, by simp [Rat.smul_def]⟩

/-- **The rational Hodge endomorphisms of `E_τ`**: the `ℚ`-subalgebra of the `α ∈ ℂ` whose
multiplication preserves `L_τ = ℚ + ℚτ`, that is the left order `Submodule.leftOrder` of `L_τ`.
It is defined for every `τ : ℂ`; when `Im τ ≠ 0` it is the algebra of rational Hodge endomorphisms
of the elliptic curve `E_τ = ℂ / (ℤ + ℤτ)`. -/
abbrev ellipticHodgeEndomorphisms (τ : ℂ) : Subalgebra ℚ ℂ :=
  (ellipticRationalSpan τ).leftOrder

/-- **Multiplication by `α` preserves `ℚ + ℚτ` exactly when `α = a + cτ` and `ατ = b + dτ`** for
rational `a, b, c, d`. -/
theorem mem_ellipticHodgeEndomorphisms_iff {τ α : ℂ} :
    α ∈ ellipticHodgeEndomorphisms τ ↔
      ∃ a b c d : ℚ, α = a + c * τ ∧ α * τ = b + d * τ := by
  rw [Submodule.mem_leftOrder_iff]
  constructor
  · intro h
    obtain ⟨a, c, hac⟩ := mem_ellipticRationalSpan_iff.mp
      (by simpa using h 1 (Submodule.subset_span (by simp)))
    obtain ⟨b, d, hbd⟩ := mem_ellipticRationalSpan_iff.mp
      (h τ (Submodule.subset_span (by simp)))
    exact ⟨a, b, c, d, hac, hbd⟩
  · rintro ⟨a, b, c, d, hα, hατ⟩ x hx
    obtain ⟨p, q, rfl⟩ := mem_ellipticRationalSpan_iff.mp hx
    rw [mem_ellipticRationalSpan_iff]
    refine ⟨p * a + q * b, p * c + q * d, ?_⟩
    push_cast
    linear_combination (p : ℂ) * hα + (q : ℂ) * hατ

/-- If `α = a + cτ` and `ατ = b + dτ` for rational `a, b, c, d`, then `τ` satisfies the rational
quadratic relation `cτ² + (a - d)τ - b = 0`. -/
theorem quadratic_relation_of_eq_add_mul_of_mul_eq_add_mul {τ α : ℂ} {a b c d : ℚ}
    (hα : α = a + c * τ) (hατ : α * τ = b + d * τ) :
    (c : ℂ) * τ ^ 2 + (a - d) * τ - b = 0 := by
  rw [hα] at hατ
  linear_combination hατ

/-- **Without a rational quadratic relation, the left order of `ℚ + ℚτ` is `ℚ`.** If `τ`
satisfies no equation `cτ² + eτ + f = 0` with rational `c ≠ 0`, every `α` preserving `ℚ + ℚτ` is
rational. -/
theorem ellipticHodgeEndomorphisms_eq_bot {τ : ℂ}
    (hq : ∀ c e f : ℚ, (c : ℂ) * τ ^ 2 + e * τ + f = 0 → c = 0) :
    ellipticHodgeEndomorphisms τ = ⊥ := by
  refine eq_bot_iff.mpr fun α h ↦ ?_
  obtain ⟨a, b, c, d, hα, hατ⟩ := mem_ellipticHodgeEndomorphisms_iff.mp h
  have hc : c = 0 := hq c (a - d) (-b) (by
    push_cast
    linear_combination quadratic_relation_of_eq_add_mul_of_mul_eq_add_mul hα hατ)
  simpa [hα, hc] using Subalgebra.algebraMap_mem (⊥ : Subalgebra ℚ ℂ) a

/-- `τ` lies in the left order of `ℚ + ℚτ` exactly when `τ² ∈ ℚ + ℚτ`, that is when `τ` satisfies a
monic rational quadratic equation. -/
theorem mem_ellipticHodgeEndomorphisms_self_iff {τ : ℂ} :
    τ ∈ ellipticHodgeEndomorphisms τ ↔ ∃ b d : ℚ, τ ^ 2 = b + d * τ := by
  rw [mem_ellipticHodgeEndomorphisms_iff]
  constructor
  · rintro ⟨a, b, c, d, -, h⟩
    exact ⟨b, d, by rw [sq, h]⟩
  · rintro ⟨b, d, h⟩
    exact ⟨0, b, 1, d, by simp, by rw [← sq, h]⟩

/-- **In the quadratic case the left order of `ℚ + ℚτ` is `ℚ(τ)`.** If `τ² = b + dτ` for
rational `b, d`, the algebra is generated by `τ`. -/
theorem ellipticHodgeEndomorphisms_eq_adjoin {τ : ℂ} {b d : ℚ} (h : τ ^ 2 = b + d * τ) :
    ellipticHodgeEndomorphisms τ = Algebra.adjoin ℚ {τ} := by
  refine le_antisymm (fun α hα ↦ ?_) (Algebra.adjoin_le ?_)
  · obtain ⟨a, -, c, -, rfl, -⟩ := mem_ellipticHodgeEndomorphisms_iff.mp hα
    have hτ : τ ∈ Algebra.adjoin ℚ {τ} := Algebra.subset_adjoin rfl
    exact add_mem (algebraMap_mem _ a) (mul_mem (algebraMap_mem _ c) hτ)
  · exact Set.singleton_subset_iff.mpr (mem_ellipticHodgeEndomorphisms_self_iff.mpr ⟨b, d, h⟩)

end TauCeti
