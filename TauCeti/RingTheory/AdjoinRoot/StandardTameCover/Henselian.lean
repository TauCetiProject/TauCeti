/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Henselian
public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.Henselian.Integral

/-!
# Strictly henselian root covers

If `A` is local, `f` belongs to its maximal ideal and `e > 0`, the root cover
`A[x]/(x^e - f)` is local and has the same residue field as `A`. If `A` is henselian,
so is the cover. In particular, extracting a root of a local equation of a divisor over a
strictly henselian base again gives a strictly henselian ring. Finite étale algebras over
that ring therefore split into products of copies of it.

No invertibility of `e`, regularity or Noetherianity is needed here. To use the residue-field
statements, install `standardTameCover_isLocalRing` as a local instance first.

## References

* The Stacks Project, Lemma 58.31.5, https://stacks.math.columbia.edu/tag/0EYG.
* The Stacks Project, Lemma 10.153.4, https://stacks.math.columbia.edu/tag/04GH.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {f : A} {e : ℕ}

/-- A positive-degree root cover along the maximal ideal of a henselian local ring is
henselian local. Combined with `standardTameCover_isSepClosed_residueField`, this shows that
root extraction preserves strict henselianity. -/
theorem standardTameCover_henselianLocalRing [HenselianLocalRing A]
    (hf : f ∈ maximalIdeal A) (he : e ≠ 0) :
    HenselianLocalRing (standardTameCover A f e) := by
  have := standardTameCover_isLocalRing hf he
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  exact HenselianLocalRing.of_finite A (standardTameCover A f e)

end TauCeti
