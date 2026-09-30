/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
public import TauCeti.NumberTheory.LocalField.SquareClass

import TauCeti.NumberTheory.LocalField.InertiaDegree

/-!
# The number of square classes of a finite extension of a local field

Let `K` be a nonarchimedean local field with `2 ≠ 0` and let `M` be a field that is a finite
extension of `K`. A nonarchimedean local field `F` has `4 · #𝓀[F] ^ v_F(2)` square classes
(`TauCeti.card_squareClass`). Equipping `M` with its local-field structure
(`TauCeti.finiteExtensionValuativeRel`), the fundamental identity `e · f = [M : K]` and
`v_M(2) = e · v_K(2)` turn this into a count expressed in terms of `K` and the degree alone:

`#(Mˣ/(Mˣ)²) = 4 · (#𝓀[K] ^ v_K(2)) ^ [M : K]`.

The statement puts no structure on `M` beyond that of a finite `K`-algebra, since the square-class
group of a field depends only on the field.

## Main results

* `TauCeti.card_squareClass_eq_pow_finrank`: the count above.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5 and §6.
-/

public section

open ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- **The number of square classes of a finite extension.** If `M` is a finite extension of a
nonarchimedean local field `K` in which `2 ≠ 0`, then `Mˣ ⧸ (Mˣ)²` has
`4 · (#𝓀[K] ^ v_K(2)) ^ [M : K]` elements. -/
theorem card_squareClass_eq_pow_finrank (h2 : (2 : K) ≠ 0) (M : Type*) [Field M] [Algebra K M]
    [Module.Finite K M] :
    Nat.card (MultiplicativeSquareClassGroup M) =
      4 * (Nat.card 𝓀[K] ^ natCastValuation K 2 h2) ^ Module.finrank K M := by
  let _ := finiteExtensionValuativeRel K M
  let _ := finiteExtensionNormedFieldTopology K M
  have := finiteExtension_valuativeExtension K M
  have := finiteExtension_isNonarchimedeanLocalField K M
  have h2M : (2 : M) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K M)).mpr h2
  rw [card_squareClass h2M, natCastValuation_eq_ramificationIndex_mul 2 h2 h2M,
    natCard_residueField K M, ← ramificationIndex_mul_inertiaDegree K M]
  ring

end TauCeti
