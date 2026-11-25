/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import TauCeti.AlgebraicGeometry.Birational.RationalMap.Basic
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
  degree is the junk value `0`, as `dim 𝔸² ≠ dim 𝔸¹`.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.TopologicalDegreeExamples

variable (K : Type u) [Field K]

-- `z ↦ z²` on the affine line has topological degree `2`, in every characteristic.
example : Scheme.RationalMap.topologicalDegree (Spec.map (CommRingCat.ofHom
    (MvPolynomial.expand 2 : MvPolynomial PUnit.{u + 1} K →ₐ[K] _).toRingHom)).toRationalMap =
    2 := by
  rw [topologicalDegree_toRationalMap_SpecMap_expand, Nat.card_unique, pow_one]

-- In characteristic `2` as well: over `ZMod 2` the degree is still `2`.
example : Scheme.RationalMap.topologicalDegree (Spec.map (CommRingCat.ofHom
    (MvPolynomial.expand 2 : MvPolynomial PUnit.{1} (ZMod 2) →ₐ[ZMod 2] _).toRingHom)
    ).toRationalMap = 2 := by
  rw [topologicalDegree_toRationalMap_SpecMap_expand, Nat.card_unique, pow_one]

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

end TauCeti.TopologicalDegreeExamples
