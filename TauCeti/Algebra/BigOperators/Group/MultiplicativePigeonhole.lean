/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Multiplicative pigeonhole principle on a finite group

Let `G` be a finite group and `a, b : G → R` nonnegative functions valued in a linearly ordered
strictly ordered commutative semiring `R`. If `v ^ Fintype.card G ≤ ∏ g : G, a g * b g`, then
every `ψ : G` admits a factorization `ψ = φ * χ` with `v ≤ a φ * b χ`.
Applying this to `x ↦ ‖ι x‖` for a multiplicative homomorphism `ι : M →* F` into a seminormed
commutative ring with multiplicative norm and `‖1‖ = 1` recovers the normed multiplicative
pigeonhole lemma: if `V ^ Fintype.card G = ∏ χ : G, a χ * b χ`, then every `ψ : G` factors as
`ψ = φ * χ` with `‖ι V‖ ≤ ‖ι (a φ * b χ)‖`.

## Provenance

Extracted and generalized from `grh-lean`
(https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC),
file `src/New/OneLift/HeckeValues/TwistedValueHeights.lean`
(`exists_mul_eq_norm_map_le_norm_map_mul`).
-/

public section

namespace TauCeti

/-- Multiplicative pigeonhole on a finite group `G`: if `a, b : G → R` are nonnegative and
`v ^ Fintype.card G ≤ ∏ g : G, a g * b g`, then every `ψ : G` factors as `φ * χ = ψ` with
`v ≤ a φ * b χ`. -/
theorem exists_mul_eq_le_mul_of_pow_le_prod {G R : Type*} [Group G] [Fintype G]
    [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    {a b : G → R} {v : R} (ha : ∀ g, 0 ≤ a g) (hb : ∀ g, 0 ≤ b g)
    (h : v ^ Fintype.card G ≤ ∏ g : G, a g * b g) (ψ : G) :
    ∃ φ χ : G, φ * χ = ψ ∧ v ≤ a φ * b χ := by
  obtain ⟨χ, -, h_max⟩ :=
    Finset.exists_max_image Finset.univ (fun χ ↦ a (ψ / χ) * b χ) Finset.univ_nonempty
  refine ⟨ψ / χ, χ, div_mul_cancel ψ χ,
    le_of_pow_le_pow_left₀ (n := Fintype.card G) Fintype.card_ne_zero
      (mul_nonneg (ha (ψ / χ)) (hb χ)) ?_⟩
  calc
    v ^ Fintype.card G ≤ ∏ g : G, a g * b g := h
    _ = ∏ g : G, a (ψ / g) * b g := by
      simp only [Finset.prod_mul_distrib]
      congr 1
      exact ((Equiv.divLeft ψ).prod_comp a).symm
    _ ≤ ∏ _g : G, a (ψ / χ) * b χ :=
      Finset.prod_le_prod₀ (fun g _ ↦ mul_nonneg (ha (ψ / g)) (hb g)) h_max
    _ = (a (ψ / χ) * b χ) ^ Fintype.card G := Finset.prod_const _

/-- Normed multiplicative pigeonhole on a finite group `G`: if `ι : M →* F` is a multiplicative
homomorphism into a seminormed commutative ring with multiplicative norm and `‖1‖ = 1`, and
`V ^ Fintype.card G = ∏ χ : G, a χ * b χ`, then every `ψ : G` factors as `φ * χ = ψ` with
`‖ι V‖ ≤ ‖ι (a φ * b χ)‖`. -/
theorem exists_mul_eq_norm_map_le_norm_map_mul {G M F : Type*} [Group G] [Fintype G]
    [CommMonoid M] [SeminormedCommRing F] [NormMulClass F] [NormOneClass F]
    (ι : M →* F) {a b : G → M} {V : M}
    (hV : V ^ Fintype.card G = ∏ χ : G, a χ * b χ) (ψ : G) :
    ∃ φ χ : G, φ * χ = ψ ∧ ‖ι V‖ ≤ ‖ι (a φ * b χ)‖ := by
  have hpow : ‖ι V‖ ^ Fintype.card G ≤ ∏ χ : G, ‖ι (a χ)‖ * ‖ι (b χ)‖ := by
    rw [← norm_pow, ← map_pow, hV, map_prod, norm_prod]
    exact le_of_eq (Finset.prod_congr rfl fun χ _ ↦ by rw [map_mul, norm_mul])
  obtain ⟨φ, χ, hmul, hle⟩ := exists_mul_eq_le_mul_of_pow_le_prod
    (fun g ↦ norm_nonneg (ι (a g))) (fun g ↦ norm_nonneg (ι (b g))) hpow ψ
  exact ⟨φ, χ, hmul, by simpa only [map_mul, norm_mul] using hle⟩

end TauCeti
