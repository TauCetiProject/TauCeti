/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.InfinitesimalCharacter
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector.Enveloping

/-!
# Infinitesimal characters of smooth vectors

Let `π` be a continuous representation of a real Lie group `G` on a real normed space `V`, with
coefficients in a commutative ring `R` (for instance `R = ℂ`), and let `𝔤 = R ⊗[ℝ] Lie(G)` be the
base change of the real Lie algebra of left-invariant derivations. The extended derived action
`ContRepresentation.lieSmoothVectorsBaseChangeDerivedAction I π` makes the smooth vectors
`lieSmoothVectors I π` a Lie module over `𝔤`
(`ContRepresentation.instLieModuleTensorProductLieSmoothVectors`), with `⁅x, v⁆ = dπ(x) v`.
Its representation of `U(𝔤)` is the enveloping action
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

## Main definitions

* `ContRepresentation.instLieRingModuleTensorProductLieSmoothVectors`,
  `ContRepresentation.instLieModuleTensorProductLieSmoothVectors`: the Lie module structure of the
  smooth vectors over `R ⊗[ℝ] Lie(G)`.

## Main results

* `ContRepresentation.representation_lieSmoothVectors`: the `U(𝔤)`-representation of this Lie
  module is `lieSmoothVectorsBaseChangeEnvelopingAction I π`.
* `ContRepresentation.centralAction_lieSmoothVectors_apply`: the centre acts through it.
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

/-- **The smooth vectors are a Lie module over `R ⊗[ℝ] Lie(G)`**, through the extended derived
action: `⁅x, v⁆ = dπ(x) v`. -/
instance instLieRingModuleTensorProductLieSmoothVectors :
    LieRingModule (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) :=
  LieRingModule.compLieHom _ (lieSmoothVectorsBaseChangeDerivedAction I π)

/-- The bracket of `x ∈ R ⊗[ℝ] Lie(G)` with a smooth vector is the extended derived action. -/
theorem lie_lieSmoothVectors_def (x : R ⊗[ℝ] LeftInvariantDerivation I G)
    (v : lieSmoothVectors I π) : ⁅x, v⁆ = lieSmoothVectorsBaseChangeDerivedAction I π x v := by
  rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]

/-- The bracket of `a ⊗ X` with a smooth vector is `a • dπ(X) v`. -/
@[simp]
theorem tmul_lie_lieSmoothVectors (a : R) (X : LeftInvariantDerivation I G)
    (v : lieSmoothVectors I π) : ⁅a ⊗ₜ[ℝ] X, v⁆ = a • lieSmoothVectorsDerivative I π X v := by
  rw [lie_lieSmoothVectors_def, lieSmoothVectorsBaseChangeDerivedAction_tmul, LinearMap.smul_apply]

/-- **The `R`-Lie module of smooth vectors** over `R ⊗[ℝ] Lie(G)`. -/
instance instLieModuleTensorProductLieSmoothVectors :
    LieModule R (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) :=
  LieModule.compLieHom _ (lieSmoothVectorsBaseChangeDerivedAction I π)

/-- **The `U(𝔤)`-representation of the Lie module of smooth vectors** is the enveloping action
`lieSmoothVectorsBaseChangeEnvelopingAction`. -/
theorem representation_lieSmoothVectors :
    representation R (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) =
      lieSmoothVectorsBaseChangeEnvelopingAction I π := by
  refine _root_.UniversalEnvelopingAlgebra.hom_ext R (LieHom.ext fun x ↦ ?_)
  rw [LieHom.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.toLieHom_apply,
    representation_ι, lieSmoothVectorsBaseChangeEnvelopingAction_ι]
  exact LinearMap.ext fun v ↦ by rw [LieModule.toEnd_apply_apply, lie_lieSmoothVectors_def]

/-- The centre of `U(𝔤)` acts on smooth vectors through the enveloping action. -/
theorem centralAction_lieSmoothVectors_apply
    (z : Subalgebra.center R
      (_root_.UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G)))
    (v : lieSmoothVectors I π) :
    centralAction R (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) z v =
      lieSmoothVectorsBaseChangeEnvelopingAction I π z v := by
  rw [centralAction_apply, representation_lieSmoothVectors]

/-- **Infinitesimal character of a representation**: `π` has infinitesimal character `χ` on its
smooth vectors exactly when every central element `z` of `U(𝔤)` acts on them by `χ z`. -/
theorem hasInfinitesimalCharacter_lieSmoothVectors_iff
    {χ : Subalgebra.center R
      (_root_.UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G)) →ₐ[R] R} :
    HasInfinitesimalCharacter R (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) χ ↔
      ∀ (z : Subalgebra.center R
        (_root_.UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G))) v,
        lieSmoothVectorsBaseChangeEnvelopingAction I π z v = χ z • v := by
  simp only [hasInfinitesimalCharacter_iff, centralAction_lieSmoothVectors_apply]

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
    centralAction_lieSmoothVectors_apply]

end ContRepresentation
