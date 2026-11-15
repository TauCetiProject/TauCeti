/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Constructions

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Continuous homomorphisms from a compact monoid into the units of a normed ring

A continuous homomorphism `f` from a compact monoid into the units of a seminormed ring with
multiplicative norm and `‖1‖ = 1` (for instance a normed division ring) takes values of norm `1`:
the norms `‖f (g ^ n)‖ = ‖f g‖ ^ n` and `‖(f (g ^ n))⁻¹‖ = ‖(f g)⁻¹‖ ^ n` stay bounded for all
`n : ℕ`, so both `‖f g‖` and `‖(f g)⁻¹‖` are at most `1`, while their product is `1`.
For `𝕜 = ℂ` this says that a continuous character of a compact group is unitary.
-/

public section

namespace ContinuousMonoidHom

variable {M R : Type*} [Monoid M] [TopologicalSpace M] [CompactSpace M]
  [SeminormedRing R] [NormMulClass R] [NormOneClass R]

/-- **A continuous homomorphism from a compact monoid into the units of a seminormed ring with
multiplicative norm takes values of norm `1`.** -/
theorem norm_apply_eq_one_of_compactSpace (f : M →ₜ* Rˣ) (g : M) : ‖(f g : R)‖ = 1 := by
  -- A continuous map `u` with `u (g ^ n) = u g ^ n` has bounded norms, hence `‖u g‖ ≤ 1`.
  have hle (u : M → R) (hu : Continuous u) (hpow : ∀ n : ℕ, u (g ^ n) = u g ^ n) :
      ‖u g‖ ≤ 1 := by
    obtain ⟨B, hB⟩ := (isCompact_range hu.norm).bddAbove
    by_contra! h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B h
    exact hn.not_ge (by simpa [hpow, norm_pow] using hB ⟨g ^ n, rfl⟩)
  have h₁ := hle (fun x ↦ (f x : R)) (Units.continuous_val.comp f.continuous) fun n ↦ by simp
  have h₂ := hle (fun x ↦ (↑(f x)⁻¹ : R)) (Units.continuous_coe_inv.comp f.continuous)
    fun n ↦ by simp
  have hmul : ‖(f g : R)‖ * ‖(↑(f g)⁻¹ : R)‖ = 1 := by
    rw [← norm_mul, Units.mul_inv, norm_one]
  exact h₁.antisymm (hmul.symm.trans_le (mul_le_of_le_one_right (norm_nonneg _) h₂))

end ContinuousMonoidHom
