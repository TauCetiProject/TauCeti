/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.CommutativeGroup.Homology

/-!
# Checks for the first homology of a connected commutative Lie group

Two Checks of the roadmap AbelianSchemesAndArithmeticModuli, §A5.1, read on the identification
`TauCeti.lieExpFirstHomologyEquiv : H₁(G; ℤ) ≃ₗ[ℤ] ker exp`:

* multiplication by two on `G` acts as `λ ↦ 2λ` on the lattice;
* in dimension zero the Lie algebra and the lattice are zero, so `H₁(G; ℤ)` is zero.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Examples

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
  [IsMulCommutative G] [PreconnectedSpace G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

/-- Multiplication by two (squaring, in the multiplicative notation of `G`) acts on the lattice as
`λ ↦ 2λ`. -/
example (c : ((singularChains ℤ).obj (TopCat.of G)).homology 1) :
    lieExpFirstHomologyEquiv (I := I) (G := G)
        (ContinuousMap.singularHomologyMap ℤ 1 ⟨(· ^ 2), by
          have := topologicalGroup_of_lieGroup I ∞ (G := G)
          exact continuous_pow 2⟩ c) =
      2 • lieExpFirstHomologyEquiv (I := I) (G := G) c :=
  lieExpFirstHomologyEquiv_singularHomologyMap_pow 2 c

/-- In dimension zero the Lie algebra is zero. -/
example [Subsingleton E] : Subsingleton (LeftInvariantDerivation I G) :=
  -- The tangent space at the identity is the model space `E`.
  have : Subsingleton (GroupLieAlgebra I G) := inferInstanceAs (Subsingleton E)
  (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
    BoundarylessManifold.isInteriorPoint).injective.subsingleton

/-- In dimension zero the first homology vanishes. -/
example [Subsingleton E] : Subsingleton (((singularChains ℤ).obj (TopCat.of G)).homology 1) :=
  have : Subsingleton (GroupLieAlgebra I G) := inferInstanceAs (Subsingleton E)
  have : Subsingleton (LeftInvariantDerivation I G) :=
    (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint).injective.subsingleton
  (lieExpFirstHomologyEquiv (I := I) (G := G)).toEquiv.subsingleton

end TauCeti.Examples
