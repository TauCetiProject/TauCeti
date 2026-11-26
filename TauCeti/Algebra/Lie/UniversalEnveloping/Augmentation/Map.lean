/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
import TauCeti.RingTheory.Ideal.Maps

/-!
# Enveloping maps preserve the augmentation filtration

A Lie algebra homomorphism `f : L → M` induces the algebra homomorphism
`TauCeti.UniversalEnvelopingAlgebra.map R f : U(L) → U(M)`. It sends the augmentation ideal
`U⁺(L)` into `U⁺(M)`, and hence every power `U⁺(L) ^ n` into `U⁺(M) ^ n`. So it descends to the
truncated enveloping algebras `U(L) ⧸ U⁺(L) ^ n → U(M) ⧸ U⁺(M) ^ n` (through
`Ideal.quotientMap`), where finite exponentials of classes of Lie elements live. This is how an
identity between exponentials in one truncated enveloping algebra, such as the defining property
of a universal Baker–Campbell–Hausdorff element, is transported along Lie homomorphisms.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.augmentation_le_comap_map`: `U⁺(L)` maps into `U⁺(M)`.
* `TauCeti.UniversalEnvelopingAlgebra.augmentation_pow_le_comap_map`: `U⁺(L) ^ n` maps into
  `U⁺(M) ^ n`.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R : Type*) {L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M]
  [LieAlgebra R M]

local notation "J" L => HopfIdeal.toIdeal (HopfIdeal.augmentation R
  (_root_.UniversalEnvelopingAlgebra R L))

/-- The algebra homomorphism of enveloping algebras induced by a Lie homomorphism sends the
augmentation ideal into the augmentation ideal. -/
theorem augmentation_le_comap_map (f : L →ₗ⁅R⁆ M) :
    (J L) ≤ (J M).comap (map R f) := by
  rw [augmentation_toIdeal_eq_span_range_ι R L, Ideal.span_le]
  rintro _ ⟨x, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, map_ι]
  exact HopfIdeal.mem_toIdeal.mpr (ι_mem_augmentation R M (f x))

/-- The algebra homomorphism of enveloping algebras induced by a Lie homomorphism sends each power
of the augmentation ideal into the same power of the augmentation ideal. -/
theorem augmentation_pow_le_comap_map (f : L →ₗ⁅R⁆ M) (n : ℕ) :
    (J L) ^ n ≤ ((J M) ^ n).comap (map R f) :=
  Ideal.pow_le_comap_pow_of_le_comap (map R f) (augmentation_le_comap_map R f) n

end TauCeti.UniversalEnvelopingAlgebra
