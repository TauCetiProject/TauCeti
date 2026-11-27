/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# The number of lines of `k^ι`

Over a finite division ring `k` with `q` elements, the projective space `ℙ(k^n)` has
`(q^n − 1)/(q − 1)` points (`Projectivization.card''`), so `#ℙ(k^n) · (q − 1) ≤ q^n`. This file
states that bound with `Nat.card` for an arbitrary index type `ι`: when `ι` is infinite, `ℙ(k^ι)`
is infinite, so its `Nat.card` is `0` and the bound still holds. This is the form in which the
number of lines of `k^n` enters bounds by powers of `q`, such as those for the step weights of
Kneser's neighbour method.

## Main results

* `Projectivization.card_pi_mul_le_pow`: `#ℙ(k^ι) · (#k − 1) ≤ #k^{#ι}`.
-/

public section

namespace Projectivization

open scoped LinearAlgebra.Projectivization

/-- **The number of lines of `k^ι`.** Over a division ring `k`, the projective space of `k^ι` has
at most `#k^{#ι}/(#k − 1)` points: `#ℙ(k^ι) · (#k − 1) ≤ #k^{#ι}`, all read with `Nat.card`. -/
theorem card_pi_mul_le_pow (k ι : Type*) [DivisionRing k] :
    Nat.card (ℙ k (ι → k)) * (Nat.card k - 1) ≤ Nat.card k ^ Nat.card ι := by
  have hV : Nat.card (ι → k) ≤ Nat.card k ^ Nat.card ι := by
    rcases finite_or_infinite ι with hι | hι
    · rw [Nat.card_fun]
    · rw [Nat.card_eq_zero_of_infinite]
      exact Nat.zero_le _
  exact card k (ι → k) ▸ (Nat.sub_le _ _).trans hV

end Projectivization
