/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard
-- Proof-only: the coset count the fiber cardinality is read off.
import TauCeti.GroupTheory.Coset.Fiber

/-!
# How many points `[n]` sends to a given one

The points that `[n]` carries to a fixed `T` form a coset of `ker [n]` as soon as there is one of
them, so there are exactly `#ker [n]` of them — and over an algebraically closed field with `n`
invertible that is `n ²`. The coset count itself is group theory, and lives in
`TauCeti/GroupTheory/Coset/Fiber.lean`; what is added here is the identification of the
kernel with `ker [n]` and the value `n ²`.

The count is what turns a sum over the places above a point into a sum of `n ²` terms, which is how
the pullback of a divisor along `[n]` is read.

## Main results

* `TauCeti.Isogeny.card_zsmul_fiber_eq_card_ker`: a nonempty `[n]`-fiber has as many points as
  `ker [n]`.
* `TauCeti.Isogeny.card_zsmul_fiber`: over an algebraically closed field, for `n` invertible
  there, that count is `n ²`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)
  [W.IsElliptic]

/-- **A nonempty `[n]`-fiber has as many points as `ker [n]`.** -/
theorem card_zsmul_fiber_eq_card_ker {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    {T P₀ : (W⁄F).toAffine.Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : (W⁄F).toAffine.Point // n • P = T} =
      Nat.card (mulByIntIsogeny W hn).ker := by
  rw [card_zsmul_fiber_eq_card_zsmul_eq_zero hP₀]
  exact Nat.card_congr
    (Equiv.subtypeEquivRight fun _ ↦ (mem_ker_mulByIntIsogeny_iff W hn).symm)

/-- **`[n]` is `n ²`-to-one where it hits at all**, over an algebraically closed field in which
`n` is invertible. -/
theorem card_zsmul_fiber [IsAlgClosed F] {n : ℤ} (hchar : (n : F) ≠ 0)
    {T P₀ : (W⁄F).toAffine.Point} (hP₀ : n • P₀ = T) :
    Nat.card {P : (W⁄F).toAffine.Point // n • P = T} = n.natAbs ^ 2 := by
  rw [card_zsmul_fiber_eq_card_ker W (psiFunctionField_ne_zero W hchar) hP₀,
    card_ker_mulByIntIsogeny W hchar]

end TauCeti.Isogeny

end
