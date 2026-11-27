/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Lengths of quotients along flat local homomorphisms

Let `φ : A →+* B` be a ring homomorphism and `ψ : B →+* C` a flat local homomorphism of local
rings. For an ideal `I` of `A`, the lengths of the quotients by the extended ideals multiply:

```text
ℓ_C(C ⧸ I C) = ℓ_B(B ⧸ I B) · ℓ_C(C ⧸ m_B C).
```

Indeed `C ⧸ I C = C ⊗_B (B ⧸ I B)`, so this is Mathlib's `IsLocalRing.length_baseChange`. Applied
to the stalk maps of a composite `X → Y → Z` with `X → Y` flat, it is the multiplicativity of
the multiplicities of the pullback of cycles, the input to `(g f)^* = f^* g^*` for flat pullback
([Stacks, Section 42.14](https://stacks.math.columbia.edu/tag/02RA)). The identity holds in
`ℕ∞`, with no finiteness assumption.

## Main results

* `IsLocalRing.length_quotient_map_comp`: `ℓ_C(C ⧸ I C) = ℓ_B(B ⧸ I B) · ℓ_C(C ⧸ m_B C)`.
-/

public section

open IsLocalRing

namespace IsLocalRing

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]

/-- For `φ : A →+* B` and a flat local homomorphism `ψ : B →+* C` of local rings, the length of
the quotient of `C` by the extension of an ideal `I` of `A` is the product of the length of the
quotient of `B` by the extension of `I` and the length of `C ⧸ m_B C`. -/
theorem length_quotient_map_comp (φ : A →+* B) (ψ : B →+* C) [IsLocalHom ψ] (hψ : ψ.Flat)
    (I : Ideal A) :
    Module.length C (C ⧸ I.map (ψ.comp φ)) =
      Module.length B (B ⧸ I.map φ) * Module.length C (C ⧸ (maximalIdeal B).map ψ) := by
  algebraize [ψ]
  -- `C ⧸ I C = C ⊗_B (B ⧸ I B)`, and lengths multiply along the flat local extension `C / B`.
  have : IsLocalHom (algebraMap B C) := ‹IsLocalHom ψ›
  rw [← Ideal.map_map]
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C (I.map φ)).toLinearEquiv.length_eq
    |>.trans (length_baseChange B C (B ⧸ I.map φ))

end IsLocalRing
