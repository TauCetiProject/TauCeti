/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.AffineDynkinType.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.MatrixRepresentation

/-!
# Quartic Hochschild classes and non-formality of the affine `Dₙ` zigzag algebras

In the numbering of `TauCeti.AffineDynkinType.graph (D n)`, for `n ≥ 5`, the nodes `1` and `n - 3`
are the two branch nodes of the affine `Dₙ` graph: the node `1` has the neighbours `0`, `2` and
`n - 1`, the node `n - 3` has the neighbours `n - 4`, `n - 2` and `n`, and they are joined by the
path `1 - 2 - ⋯ - (n - 3)`. The quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ`
zigzag algebra is nonzero over every nontrivial commutative ring, as a case of the result for every
graph containing an affine `Dₙ`
(`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`). Over every
nontrivial commutative ring the affine `Dₙ` zigzag algebra is moreover not intrinsically formal for
all `n ≥ 4`, as a case of
`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_D`. Explicit quartic
deformations of the affine `D₄` zigzag algebra, whose only branch node has four neighbours, are
constructed in `TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.Affine.D.Four`.

## Main results

* `TauCeti.not_hochschildVanishesAt_four_affineD`: `HH^{4, -2}` of the affine `Dₙ` zigzag algebra
  is nonzero for `n ≥ 5`.
* `TauCeti.not_isIntrinsicallyFormal_affineD`: the affine `Dₙ` zigzag algebra is not
  intrinsically formal for `n ≥ 4`, over every nontrivial commutative ring.
-/

public section

namespace TauCeti

universe w

variable {k : Type w} [CommRing k]

/-- **The quartic Hochschild cohomology `HH^{4, -2}` of the affine `Dₙ` zigzag algebra is nonzero**
for `n ≥ 5`, over every nontrivial commutative ring: this is the case `G = Dₙ` of
`TauCeti.not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained`. For `n = 4`
see `TauCeti.not_hochschildVanishesAt_four_affineD4`. -/
theorem not_hochschildVanishesAt_four_affineD [Nontrivial k] {n : ℕ} (hn : 5 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 (by omega)))).HochschildVanishesAt ⟨4, by norm_num⟩ :=
  not_hochschildVanishesAt_four_zigzagStrictAInfinityAlgebra_of_isContained (by omega) .rfl

/-- **The affine `Dₙ` zigzag algebra is not intrinsically formal** for `n ≥ 4`, over every
nontrivial commutative ring: some `A∞` algebra whose cohomology algebra is the path-graded zigzag
algebra is not formal. This is the case `G = Dₙ` of
`TauCeti.not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_D`. -/
theorem not_isIntrinsicallyFormal_affineD [Nontrivial k] {n : ℕ} (hn : 4 ≤ n) :
    ¬(zigzagStrictAInfinityAlgebra k (AffineDynkinType.exists_adj_graph (t := .D n)
      (AffineDynkinType.valid_D.2 hn))).IsIntrinsicallyFormal :=
  not_isIntrinsicallyFormal_zigzagStrictAInfinityAlgebra_of_isContained_D hn .rfl

end TauCeti
