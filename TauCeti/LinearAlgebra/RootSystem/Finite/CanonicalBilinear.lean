/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
import TauCeti.LinearAlgebra.RootSystem.PairingInvariance

/-!
# The sign of the canonical bilinear form on two roots

For a finite root pairing over a linearly ordered commutative ring, the canonical bilinear form
`RootPairing.RootForm` of two roots `αᵢ`, `αⱼ` has the same sign as the pairing `⟨αᵢ, αⱼ^∨⟩`.
Mathlib records this for the form `RootPairing.posRootForm` restricted to the span of the roots
and for `RootPairing.pairingIn`; this file states it for `RootPairing.RootForm` and
`RootPairing.pairing` themselves, with no integrality hypothesis.

## Main results

* `RootPairing.zero_lt_rootForm_root_root_iff`: `0 < B(αᵢ, αⱼ) ↔ 0 < ⟨αᵢ, αⱼ^∨⟩`.
* `RootPairing.rootForm_root_root_le_zero_iff`: `B(αᵢ, αⱼ) ≤ 0 ↔ ⟨αᵢ, αⱼ^∨⟩ ≤ 0`.
-/

public section

namespace RootPairing

variable {ι R M N : Type*} [Fintype ι] [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) {i j : ι}

/-- The canonical bilinear form of two roots is positive exactly when their pairing is. -/
lemma zero_lt_rootForm_root_root_iff :
    0 < P.RootForm (P.root i) (P.root j) ↔ 0 < P.pairing i j := by
  have h₁ := P.algebraMap_posRootForm_posForm R (P.rootSpanMem R i) (P.rootSpanMem R j)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h₁
  rw [← h₁, ← pairingIn_eq_pairing]
  exact (P.posRootForm R).zero_lt_apply_root_root_iff i j

/-- The canonical bilinear form of two roots is nonpositive exactly when their pairing is. -/
lemma rootForm_root_root_le_zero_iff :
    P.RootForm (P.root i) (P.root j) ≤ 0 ↔ P.pairing i j ≤ 0 := by
  rw [← not_iff_not, not_le, not_le, zero_lt_rootForm_root_root_iff]

end RootPairing
