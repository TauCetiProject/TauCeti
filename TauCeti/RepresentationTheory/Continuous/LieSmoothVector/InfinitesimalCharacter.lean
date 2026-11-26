/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter.Basic
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Enveloping

/-!
# Infinitesimal characters of smooth vectors

Let `π` be a continuous representation of a real Lie group `G` on a real normed space `V`, with
coefficients in a commutative ring `R` (for instance `R = ℂ`), and let `𝔤 = R ⊗[ℝ] Lie(G)` be the
base change of the real Lie algebra of left-invariant derivations. By
`TauCeti/RepresentationTheory/Continuous/LieSmoothVector/Enveloping.lean`, the smooth vectors
`lieSmoothVectors I π` are a Lie module over `𝔤`
(`ContRepresentation.instLieModuleTensorProductLieSmoothVectors`), with `⁅x, v⁆ = dπ(x) v`, and
its representation of `U(𝔤)` is the enveloping action
`ContRepresentation.lieSmoothVectorsBaseChangeEnvelopingAction I π`
(`ContRepresentation.representation_lieSmoothVectors`).

So the infinitesimal-character API of
`TauCeti/Algebra/Lie/UniversalEnveloping/InfinitesimalCharacter.lean` applies to smooth vectors:
`π` **has infinitesimal character** `χ : Z(U(𝔤)) →ₐ[R] R` when every central element `z` acts on
the smooth vectors by the scalar `χ z`
(`ContRepresentation.hasInfinitesimalCharacter_lieSmoothVectors_iff`), and it is **generalized
`χ`-finite** when every smooth vector is annihilated by some power of `ker χ`
(`ContRepresentation.isGeneralizedCharacterFinite_lieSmoothVectors_iff`). Uniqueness, passage to
Lie submodules and quotients, duals and the generalized eigenspace come from that file.

## Main results

* `ContRepresentation.hasInfinitesimalCharacter_lieSmoothVectors_iff`,
  `ContRepresentation.isGeneralizedCharacterFinite_lieSmoothVectors_iff`: the two predicates in
  terms of the enveloping action on smooth vectors.

## References

* Bernstein, Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §4.1.
-/

public section

noncomputable section

open Manifold TauCeti.UniversalEnvelopingAlgebra
open scoped ContDiff Manifold TensorProduct

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] [Module R V] (π : ContRepresentation R G V)
  [Algebra ℝ R] [IsScalarTower ℝ R V] [ContinuousConstSMul R V]

/-- **Infinitesimal character of a representation**: `π` has infinitesimal character `χ` on its
smooth vectors exactly when every central element `z` of `U(𝔤)` acts on them by `χ z`. -/
theorem hasInfinitesimalCharacter_lieSmoothVectors_iff
    {χ : Subalgebra.center R
      (_root_.UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G)) →ₐ[R] R} :
    HasInfinitesimalCharacter R (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) χ ↔
      ∀ (z : Subalgebra.center R
        (_root_.UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G))) v,
        lieSmoothVectorsBaseChangeEnvelopingAction I π z v = χ z • v := by
  simp only [hasInfinitesimalCharacter_iff, centralAction_apply, representation_lieSmoothVectors]

/-- **Generalized infinitesimal character of a representation**: `π` is generalized `χ`-finite on
its smooth vectors exactly when every smooth vector is annihilated by some power of `ker χ`. -/
theorem isGeneralizedCharacterFinite_lieSmoothVectors_iff
    {χ : Subalgebra.center R
      (_root_.UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G)) →ₐ[R] R} :
    IsGeneralizedCharacterFinite R (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π)
        χ ↔
      ∀ v, ∃ n : ℕ, ∀ z ∈ RingHom.ker χ ^ n,
        lieSmoothVectorsBaseChangeEnvelopingAction I π z v = 0 := by
  rw [isGeneralizedCharacterFinite_iff_generalizedCharacter_eq_top, eq_top_iff]
  simp only [IsConcreteLE.le_iff, LieSubmodule.mem_top, true_implies, mem_generalizedCharacter,
    centralAction_apply, representation_lieSmoothVectors]

end ContRepresentation
