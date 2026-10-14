/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs

/-!
# Natural numbers invertible in the base ring of an algebra

A natural number that is a unit in `K` stays nonzero in every nontrivial `K`-algebra `L`. Results
stated over an extension, such as the separable closure `Kˢ`, often need `(m : L) ≠ 0`, while the
hypothesis available is `IsUnit (m : K)`.

## Main results

* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
-/

public section

/-- A natural number invertible in `K` is nonzero in every nontrivial `K`-algebra `L`. -/
theorem IsUnit.natCast_ne_zero_of_algebra {K L : Type*} [CommSemiring K] [Semiring L]
    [Nontrivial L] [Algebra K L] {m : ℕ} (hm : IsUnit (m : K)) : (m : L) ≠ 0 := by
  simpa using (hm.map (algebraMap K L)).ne_zero
