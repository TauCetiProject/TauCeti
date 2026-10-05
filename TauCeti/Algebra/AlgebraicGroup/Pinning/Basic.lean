/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.Over
public import TauCeti.Algebra.AlgebraicGroup.Borel.Over
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Tangent.RootSpace
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Smooth
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Tangent

/-!
# Pinnings with a chosen split maximal torus over a connected base

A pinning consists of a split maximal torus, a Borel containing it, and a generator of
its Lie algebra's root space for each simple root. The positive roots are the nontrivial
adjoint weights whose entire root space lies in the Lie algebra of the Borel. The simple
roots are the positive roots which cannot be written as the sum of two positive roots.
Thus the indexing of the generators is determined by the group, torus, and Borel; it is
not an independently supplied root system. The base spectrum is required to be connected:
on a disconnected base different components can select opposite positive systems, so global
characters alone need not index all fiberwise simple roots.

`Pinning` records generators as linear equivalences from the base ring onto the simple
root spaces. This expresses generation and freeness, rather than merely choosing nonzero
vectors, which would be insufficient over a ring. Smoothness and finite type remain
explicit hypotheses; reductivity over the base is certified by the data.

## References

* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1 (positive and simple roots).
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{u} R}
  [Algebra.FiniteType R H] {r : ℕ}

namespace SplitMaximalTorus

variable [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- A positive root relative to a closed subgroup is a nontrivial adjoint weight whose
root space lies in the subgroup's tangent Lie algebra. For a Borel containing the torus
in a reductive group over a connected base, this is its positive root system. Characters
are written additively in the exponent lattice of the torus. -/
def IsPositiveRoot (T : SplitMaximalTorus R H r) (B : HopfIdeal R H)
    (α : ULift.{u} (Fin r) →₀ ℤ) : Prop :=
  Multiplicative.ofAdd α ∈ Derivation.nontrivialAdjointWeights T.coordinateMap.hom ∧
    ∀ x ∈ Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd α),
      Derivation.cotangentLinearEquiv (B := R) x ∈ B.lieSubalgebra

/-- The adjoint-weight and tangent-containment characterization of positivity. -/
theorem isPositiveRoot_iff (T : SplitMaximalTorus R H r) (B : HopfIdeal R H)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.IsPositiveRoot B α ↔
      Multiplicative.ofAdd α ∈ Derivation.nontrivialAdjointWeights T.coordinateMap.hom ∧
        ∀ x ∈ Derivation.adjointWeightSpace T.coordinateMap.hom (Multiplicative.ofAdd α),
          Derivation.cotangentLinearEquiv (B := R) x ∈ B.lieSubalgebra := Iff.rfl

/-- A simple root is a positive root which is not the sum of two positive roots. -/
def IsSimpleRoot (T : SplitMaximalTorus R H r) (B : HopfIdeal R H)
    (α : ULift.{u} (Fin r) →₀ ℤ) : Prop :=
  T.IsPositiveRoot B α ∧ ∀ β γ, T.IsPositiveRoot B β → T.IsPositiveRoot B γ → α ≠ β + γ

/-- The indecomposable-positive-root characterization of simplicity. -/
theorem isSimpleRoot_iff (T : SplitMaximalTorus R H r) (B : HopfIdeal R H)
    (α : ULift.{u} (Fin r) →₀ ℤ) :
    T.IsSimpleRoot B α ↔ T.IsPositiveRoot B α ∧
      ∀ β γ, T.IsPositiveRoot B β → T.IsPositiveRoot B γ → α ≠ β + γ := Iff.rfl

end SplitMaximalTorus

/-- A pinning over a connected base of a smooth finite-type reductive affine group with a split
maximal torus: a Borel containing the torus and trivializations of all simple root spaces.
Only the intrinsically determined simple roots index the trivializations. -/
@[ext]
structure Pinning (R : Type u) [CommRing R] (H : CommHopfAlgCat.{u} R)
    [Algebra.FiniteType R H] [Algebra.Smooth R H]
    [ConnectedSpace (PrimeSpectrum R)] (r : ℕ) where
  /-- Reductivity over the base, including all geometric fibers. -/
  reductive : reductiveCommHopfAlgPropertyOver R (FiniteTypeCommHopfAlgCat.of R H)
  /-- The chosen parametrized split maximal torus. -/
  torus : SplitMaximalTorus R H r
  /-- The ideal cutting out the chosen Borel subgroup. -/
  borel : HopfIdeal R H
  /-- The subgroup is a Borel over the base. -/
  isBorel : borel.IsBorelOver R H
  /-- The torus lies in the Borel; inclusions of defining ideals reverse subgroup inclusions. -/
  borel_le_torus : borel ≤ torus.definingIdeal
  /-- A generator, including its rank-one freeness certificate, for every simple root space. -/
  rootSpaceEquiv : ∀ α : {α // torus.IsSimpleRoot borel α},
    R ≃ₗ[R] Derivation.adjointWeightSpace torus.coordinateMap.hom (Multiplicative.ofAdd α.val)

namespace Pinning

variable [Algebra.Smooth R H] [ConnectedSpace (PrimeSpectrum R)]

/-- The chosen root vector is the image of `1` in the trivialized simple root space. -/
noncomputable def rootVector (P : Pinning R H r)
    (α : {α // P.torus.IsSimpleRoot P.borel α}) :
    Module.Dual R (Bialgebra.CotangentSpace R H) :=
  (P.rootSpaceEquiv α 1).val

/-- A pinning's root vector is the image of the unit under its root-space equivalence. -/
@[simp]
theorem rootVector_def (P : Pinning R H r)
    (α : {α // P.torus.IsSimpleRoot P.borel α}) :
    P.rootVector α = (P.rootSpaceEquiv α 1).val := (rfl)

/-- A chosen root vector belongs to the weight space of its simple root. -/
@[simp↓]
theorem rootVector_mem (P : Pinning R H r)
    (α : {α // P.torus.IsSimpleRoot P.borel α}) :
    P.rootVector α ∈
      Derivation.adjointWeightSpace P.torus.coordinateMap.hom (Multiplicative.ofAdd α.val) :=
  (P.rootSpaceEquiv α 1).property

end Pinning

end TauCeti
