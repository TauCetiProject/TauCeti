/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
import TauCeti.Algebra.Order.BigOperators.MultiplicativePigeonhole

/-!
# Normed multiplicative pigeonhole principle on a finite group

Applying `TauCeti.exists_mul_eq_le_mul_of_pow_le_prod` to `x ↦ ‖ι x‖` for a multiplicative
homomorphism `ι : M →* F` into a seminormed commutative ring with multiplicative norm and `‖1‖ = 1`
recovers the normed multiplicative pigeonhole lemma: if `V ^ Fintype.card G = ∏ χ : G, a χ * b χ`,
then every `ψ : G` factors as `ψ = φ * χ` with `‖ι V‖ ≤ ‖ι (a φ * b χ)‖`.

## Provenance

Extracted and generalized from `grh-lean`
(https://github.com/lsernau/grh-lean at commit `72fead102f663d5c7a407964a13dc0cf9d977207`,
Apache 2.0, Copyright 2026 Anthropic, PBC),
file `src/New/OneLift/HeckeValues/TwistedValueHeights.lean`
(`exists_mul_eq_norm_map_le_norm_map_mul`).
-/

public section

/-- Normed multiplicative pigeonhole on a finite group `G`: if `ι : M →* F` is a multiplicative
homomorphism into a seminormed commutative ring with multiplicative norm and `‖1‖ = 1`, and
`V ^ Fintype.card G = ∏ χ : G, a χ * b χ`, then every `ψ : G` factors as `φ * χ = ψ` with
`‖ι V‖ ≤ ‖ι (a φ * b χ)‖`. -/
theorem MonoidHom.exists_mul_eq_norm_map_le_norm_map_mul {G M F : Type*} [Group G] [Fintype G]
    [CommMonoid M] [SeminormedCommRing F] [NormMulClass F] [NormOneClass F]
    (ι : M →* F) {a b : G → M} {V : M}
    (hV : V ^ Fintype.card G = ∏ χ : G, a χ * b χ) (ψ : G) :
    ∃ φ χ : G, φ * χ = ψ ∧ ‖ι V‖ ≤ ‖ι (a φ * b χ)‖ := by
  have hpow : ‖ι V‖ ^ Fintype.card G ≤ ∏ χ : G, ‖ι (a χ)‖ * ‖ι (b χ)‖ := by
    rw [← norm_pow, ← map_pow, hV, map_prod, norm_prod]
    exact le_of_eq (Finset.prod_congr rfl fun χ _ ↦ by rw [map_mul, norm_mul])
  obtain ⟨φ, χ, hmul, hle⟩ := TauCeti.exists_mul_eq_le_mul_of_pow_le_prod
    (fun g ↦ norm_nonneg (ι (a g))) (fun g ↦ norm_nonneg (ι (b g))) hpow ψ
  exact ⟨φ, χ, hmul, by simpa only [map_mul, norm_mul] using hle⟩
