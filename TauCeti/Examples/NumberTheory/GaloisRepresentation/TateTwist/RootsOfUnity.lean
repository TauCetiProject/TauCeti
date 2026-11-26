/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.GaloisRepresentation.TateTwist.RootsOfUnity

/-!
# Checks: `ℤ_ℓ(1)` and the Tate module of roots of unity

* Over `ℚ`, `ℤ_ℓ(1) ≅ PadicTateTwist ℓ ℚ^alg` as continuous representations of `G_ℚ`.
* In characteristic `ℓ` the comparison fails: `PadicTateTwist ℓ (𝔽_ℓ)^alg = 0`, while `ℤ_ℓ(1)` is
  the nonzero line `ℤ_ℓ`, so there is no isomorphism. The hypothesis `ℓ ≠ char F` is needed.
-/

public section

namespace TauCeti.Examples.TateTwist

open TauCeti ContinuousRep

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Over `ℚ`, `ℤ_ℓ(1)` is the Tate module of the roots of unity of `ℚ^alg`. -/
example : Nonempty (Iso (cyclotomicLine ℓ ℚ) (padicTateTwist ℓ ℚ)) :=
  nonempty_iso_cyclotomicLine_padicTateTwist ℓ ℚ

/-- In characteristic `ℓ`, `ℤ_ℓ(1) = ℤ_ℓ` is not isomorphic to `PadicTateTwist ℓ (𝔽_ℓ)^alg = 0`. -/
example : IsEmpty (Iso (cyclotomicLine ℓ (ZMod ℓ)) (padicTateTwist ℓ (ZMod ℓ))) := by
  have := PadicTateTwist.subsingleton_of_expChar ℓ (AlgebraicClosure (ZMod ℓ))
  exact ⟨fun e ↦ one_ne_zero (e.injective (Subsingleton.elim (e 1) (e 0)))⟩

end TauCeti.Examples.TateTwist
