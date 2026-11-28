/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.Equivalence
public import TauCeti.Topology.VectorBundle.FiniteRank.Bundle.ULift.Comparison

/-!
# Categorical equivalence for universe lifting of variable-rank vector bundles

Whenever `[UnivLE.{v, w}]` holds, `FiniteRankBundle.uliftFunctor 𝕜 X` is an equivalence
of categories, deduced from `uliftToAtlasNatIso` (`Bundle/ULift/Comparison.lean`) and the fact
that `toAtlasFunctor 𝕜 X` is an equivalence (`Bundle/Equivalence.lean`).

## References

* A. Hatcher, *Vector Bundles and K-Theory*, §1.1.
* D. Husemoller, *Fibre Bundles*, Chapter 3.
-/

public section

open CategoryTheory

namespace TauCeti.FiniteRankBundle

universe w w' u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜] {X : Type u} [TopologicalSpace X]

instance [UnivLE.{v, w}] : (uliftFunctor.{w, w'} 𝕜 X).IsEquivalence := by
  have : UnivLE.{v, max w w'} := @UnivLE.trans.{v, w, max w w'} ‹_› inferInstance
  have := Functor.isEquivalence_of_iso (uliftToAtlasNatIso.{w, w'} 𝕜 X).symm
  exact Functor.isEquivalence_of_comp_right (uliftFunctor 𝕜 X) (toAtlasFunctor 𝕜 X)

end TauCeti.FiniteRankBundle
