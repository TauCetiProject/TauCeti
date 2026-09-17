/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeD.RootGenerators
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Serre

/-!
# The Cartan action on the numbered root generators of the type-D Serre presentation

The numbered positive and negative root generators of the type-`Dₙ` Serre presentation are weight
vectors for its Cartan generators, and the weight is the one
`TauCeti.TypeDStd.rootGeneratorWeight` already attaches to the numbering through the split
orthogonal Lie algebra: the corresponding row of the type-`D` Cartan matrix for a raising generator
and its negative for a lowering generator. The statement mentions no representation of the
presentation, so it is shared by every Chevalley carrier built on the type-`Dₙ` presentation, and
it is what the pinning equation of each such carrier is proved against.

## Main results

* `TauCeti.TypeDStd.lie_serreH_serreRootGenerator`: each numbered Serre root generator is a Cartan
  weight vector with weight `TauCeti.TypeDStd.rootGeneratorWeight`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §18.
-/

public section

namespace TauCeti.TypeDStd

variable (n : ℕ)

/-- The numbered Serre root generators of the type-`Dₙ` presentation are weight vectors for its
Cartan generators, with the integral weight `TauCeti.TypeDStd.rootGeneratorWeight` already attached
to the numbering by the split orthogonal Lie algebra. The type-`D` Cartan matrix is symmetric, so
its row and column readings of that weight agree. -/
theorem lie_serreH_serreRootGenerator (k : Fin n ⊕ Fin n) (j : Fin n) :
    ⁅TauCeti.serreH ℚ (CartanMatrix.D n) j,
        TauCeti.serreRootGenerator (CartanMatrix.D n) k⁆ =
      ((rootGeneratorWeight n k j : ℤ) : ℚ) •
        TauCeti.serreRootGenerator (CartanMatrix.D n) k := by
  cases k with
  | inl i =>
      rw [TauCeti.lie_serreH_serreRootGenerator_inl,
        (CartanMatrix.D_isSymm n).apply i j, rootGeneratorWeight_inl]
  | inr i =>
      rw [TauCeti.lie_serreH_serreRootGenerator_inr,
        (CartanMatrix.D_isSymm n).apply i j, rootGeneratorWeight_inr]

end TauCeti.TypeDStd
