/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.ProjectiveLine
public import TauCeti.AlgebraicGeometry.VectorBundle.Degree

/-!
# Degrees of direct sums of twisting sheaves on the projective line

On the projective line `ℙ¹_k` over a field `k`, the direct sum `𝒪(a) ⊕ 𝒪(b)` of two twisting
sheaves is a vector bundle of rank two of degree `a + b`
(`TauCeti.AlgebraicGeometry.projectiveLine.vectorBundleDegree_biprod_twistingSheaf`). In particular
`𝒪(1) ⊕ 𝒪(-1)` has degree `0`, the degree of the trivial bundle of rank two.

The cohomology of every finite locally free sheaf on `ℙ¹_k` is finite-dimensional in degrees `0`
and `1`, so this is an instance of the additivity of the degree under direct sums,
`FiniteLocallyFreeSheaf.FixedRank.vectorBundleDegree_biprod`, combined with `deg 𝒪(n) = n`.

## References

* [The Stacks Project, Section 33.44, Degrees on curves](https://stacks.math.columbia.edu/tag/0AYR)
-/

public section

open CategoryTheory AlgebraicGeometry TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.FixedRank

namespace TauCeti.AlgebraicGeometry.projectiveLine

universe u

variable (k : Type u) [Field k]

local notation "𝒜" => SymmetricAlgebra.homogeneousSubmodule k (Fin 2 → k)
local notation "ℒ" => fun n : ℤ ↦
  (ObjectProperty.FullSubcategory.mk (Proj.twistingSheaf 𝒜 n) inferInstance :
    InvertibleSheaf (projectiveLine k))

local instance {r : ℕ} (E : FiniteLocallyFreeSheaf.FixedRank (projectiveLine k) r) :
    FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 0) :=
  finite_cohomology_zero k _

local instance {r : ℕ} (E : FiniteLocallyFreeSheaf.FixedRank (projectiveLine k) r) :
    FiniteDimensional k (Scheme.Modules.Cohomology E.obj.obj 1) :=
  finite_cohomology_one k _

/-- **The degree of `𝒪(a) ⊕ 𝒪(b)` on the projective line.** For all `a b : ℤ`, the direct sum of
the twisting sheaves `𝒪(a)` and `𝒪(b)` on `ℙ¹_k`, a vector bundle of rank two, has degree
`a + b`. -/
theorem vectorBundleDegree_biprod_twistingSheaf (a b : ℤ) :
    vectorBundleDegree k (((InvertibleSheaf.toFixedRankOne _).obj (ℒ a)).biprod
      ((InvertibleSheaf.toFixedRankOne _).obj (ℒ b))) = a + b := by
  rw [vectorBundleDegree_biprod, vectorBundleDegree_toFixedRankOne_obj,
    vectorBundleDegree_toFixedRankOne_obj, eulerDegree_twistingSheaf, eulerDegree_twistingSheaf]

end TauCeti.AlgebraicGeometry.projectiveLine
