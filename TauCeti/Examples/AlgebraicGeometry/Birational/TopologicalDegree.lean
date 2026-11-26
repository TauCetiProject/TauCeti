/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.AlgebraicGeometry.Birational.RationalMap.Basic
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Birationality
public import TauCeti.AlgebraicGeometry.Birational.TopologicalDegree.Expand
import TauCeti.AlgebraicGeometry.Scheme.KrullDimension
import TauCeti.RingTheory.Spectrum.Prime.Topology

/-!
# Regression examples: the topological degree on affine space

Examples of the topological degree on affine space:

* `z ↦ z²` on the affine line over a field has topological degree `2` in every characteristic,
  including characteristic `2`, where `K(z) / K(z²)` is purely inseparable;
* the `K`-linear Frobenius `x_i ↦ x_i ^ p` of `𝔸^d_K` over a field of characteristic `p` has
  topological degree `p ^ d`, not its separable degree `1`;
* the linear projection `(x, y) ↦ x` from `𝔸²_K` to `𝔸¹_K` is dominant, and its topological
  degree is the junk value `0`, as `dim 𝔸² ≠ dim 𝔸¹`;
* `z ↦ z²` on the affine line is not birational: its topological degree is `2`, so its pullback
  of rational functions is not surjective and it is the rational map of no partial isomorphism.
  Yet the affine line is birational to itself in Mathlib's sense `Scheme.Birational`, through the
  identity, so "birational `f`" cannot be read through that relation on the pair.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.TopologicalDegreeExamples

variable (K : Type u) [Field K]

/-- The squaring map `z ↦ z²` of the affine line over `K`, as `Spec` of `MvPolynomial.expand 2`. -/
noncomputable abbrev squareMap :
    Spec (.of (MvPolynomial PUnit.{u + 1} K)) ⟶ Spec (.of (MvPolynomial PUnit.{u + 1} K)) :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.expand 2 : MvPolynomial PUnit.{u + 1} K →ₐ[K] _).toRingHom)

/-- `z ↦ z²` on the affine line has topological degree `2`, in every characteristic. -/
theorem topologicalDegree_squareMap : (squareMap K).toRationalMap.topologicalDegree = 2 := by
  rw [topologicalDegree_toRationalMap_SpecMap_expand, Nat.card_unique, pow_one]

-- In characteristic `2` as well: over `ZMod 2` the degree is still `2`.
example : (squareMap (ZMod 2)).toRationalMap.topologicalDegree = 2 :=
  topologicalDegree_squareMap _

-- The `K`-linear Frobenius of `𝔸^d_K` in characteristic `p` has topological degree `p ^ d`.
example (p d : ℕ) [Fact p.Prime] [CharP K p] :
    Scheme.RationalMap.topologicalDegree (Spec.map (CommRingCat.ofHom
      (MvPolynomial.expand p : MvPolynomial (Fin d) K →ₐ[K] _).toRingHom)
      ).toRationalMap = p ^ d := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [topologicalDegree_toRationalMap_SpecMap_expand, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The linear projection `(x, y) ↦ x`, as a `K`-algebra map of coordinate rings
`K[x] → K[x, y]`. -/
noncomputable abbrev projectionAlgHom :
    MvPolynomial (Fin 1) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.rename Fin.castSucc

/-- The linear projection `𝔸²_K → 𝔸¹_K`, `(x, y) ↦ x`. -/
noncomputable abbrev projection :
    Spec (.of (MvPolynomial (Fin 2) K)) ⟶ Spec (.of (MvPolynomial (Fin 1) K)) :=
  Spec.map (CommRingCat.ofHom (projectionAlgHom K).toRingHom)

/-- The projection is dominant: `K[x] → K[x, y]` is injective. -/
instance isDominant_projection : IsDominant (projection K) :=
  ⟨RingHom.denseRange_comap_of_injective _ <|
    MvPolynomial.rename_injective _ (Fin.castSucc_injective _)⟩

/-- The projection is a morphism over `K`. -/
instance isOver_projection : (projection K).IsOver (Spec (.of K)) where
  comp_over := by
    rw [specOverSpec_over, specOverSpec_over, projection, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact (projectionAlgHom K).comp_algebraMap

-- The linear projection `𝔸²_K → 𝔸¹_K` has the junk topological degree `0`.
example : (projection K).toRationalMap.topologicalDegree = 0 := by
  rw [Scheme.RationalMap.topologicalDegree_eq_zero_iff K,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_Spec_mvPolynomial,
    TauCeti.AlgebraicGeometry.topologicalKrullDim_Spec_mvPolynomial, ringKrullDim_eq_zero_of_field]
  norm_num

/-! ### `z ↦ z²` is not birational -/

/-- The pullback of rational functions along `z ↦ z²`, the inclusion `K(z²) ⊆ K(z)`, is not
surjective. -/
theorem not_surjective_functionFieldMap_squareMap :
    ¬ Function.Surjective (squareMap K).toRationalMap.functionFieldMap.hom := by
  rw [← Scheme.RationalMap.topologicalDegree_eq_one_iff_surjective, topologicalDegree_squareMap]
  decide

/-- `z ↦ z²` is the rational map of no partial isomorphism of the affine line: the rational map
of a partial isomorphism has topological degree `1`. -/
theorem toRationalMap_ne_squareMap
    (φ : Scheme.PartialIso (Spec (.of (MvPolynomial PUnit.{u + 1} K)))
      (Spec (.of (MvPolynomial PUnit.{u + 1} K)))) :
    φ.toRationalMap ≠ (squareMap K).toRationalMap := fun h => by
  have := (Scheme.RationalMap.topologicalDegree_congr h).symm.trans
    φ.topologicalDegree_toRationalMap
  rw [topologicalDegree_squareMap] at this
  exact absurd this (by decide)

-- Yet the affine line is birational to itself in Mathlib's sense, through the identity.
example : Scheme.Birational (Spec (.of (MvPolynomial PUnit.{u + 1} K)))
    (Spec (.of (MvPolynomial PUnit.{u + 1} K))) :=
  .refl _

end TauCeti.TopologicalDegreeExamples
