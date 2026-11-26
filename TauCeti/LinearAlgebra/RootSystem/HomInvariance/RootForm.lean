/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear
public import Mathlib.LinearAlgebra.RootSystem.Hom

import TauCeti.LinearAlgebra.RootSystem.HomInvariance

/-!
# Canonical bilinear forms under morphisms of root pairings

A morphism `f : P.Hom Q` of finite root pairings preserves the canonical root form `RootForm`:
its index bijection reindexes the sum of products of coroot values. This file lives downstream of
`TauCeti.LinearAlgebra.RootSystem.HomInvariance` and
`Mathlib.LinearAlgebra.RootSystem.Finite.CanonicalBilinear` without pulling in nondegeneracy,
invariant-form, or positive-definiteness theory.

## Main results

* `RootPairing.Hom.rootForm_weightMap`: a morphism of finite root pairings preserves the canonical
  root form.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.
-/

public section

namespace RootPairing.Hom

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}
  [Fintype ι] [Fintype ι₂]

/-- A morphism of finite root pairings preserves the canonical root form on weights. -/
@[simp]
theorem rootForm_weightMap (f : P.Hom Q) (x y : M) :
    Q.RootForm (f.weightMap x) (f.weightMap y) = P.RootForm x y := by
  simp only [RootPairing.rootForm_apply_apply]
  rw [← f.indexEquiv.sum_comp]
  simp only [coroot'_weightMap]

end RootPairing.Hom
