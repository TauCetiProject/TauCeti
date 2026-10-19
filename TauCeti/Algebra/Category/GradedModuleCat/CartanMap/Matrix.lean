/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Basis
public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic

/-!
# The graded Cartan matrix

The graded Cartan map is a linear map over the Laurent polynomial ring
`ℤ[q,q⁻¹]`.  After choosing bases of the projective and module Grothendieck groups, its matrix is
the graded Cartan matrix.  Rows are coordinates in the module basis and columns are coordinates
in the projective basis, matching the convention for the ordinary Cartan matrix.

This file gives the basis-generic matrix interface.  An entry is a coordinate of the image of
a projective basis vector, a column reconstructs that image, and changing the two bases acts by
the usual left and right transition matrices.  In particular, the construction does not assume
that the chosen bases arise from simple modules and indecomposable projectives; those hypotheses
belong to later representation-theoretic identifications of the entries with graded composition
multiplicities.

## Main definitions

* `TauCeti.gradedCartanMatrix`: the matrix of `TauCeti.gradedCartanMap` in independently chosen
  projective and module bases.

## Main results

* `TauCeti.gradedCartanMatrix_apply`: entries are coordinates of images of projective basis
  vectors.
* `TauCeti.gradedCartanMatrix_apply_of`: when a projective basis vector is an object class, its
  column consists of the coordinates of the same object in the module Grothendieck group.
* `TauCeti.gradedCartanMatrix_mulVec_repr`: the matrix computes the coordinates of the graded
  Cartan map on every class.
* `TauCeti.gradedCartanMap_basis_apply_eq_sum`: a column reconstructs the corresponding image.
* `TauCeti.gradedCartanMatrix_basis_change`: the change-of-basis law for the graded Cartan matrix.

The matrix convention follows Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow
lattices", *Journal of Combinatorial Theory, Series A* **185** (2022), Section 2.2.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI uJ

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  (𝒜 : ℤ → Submodule k A)

variable {I : Type uI} {J : Type uJ} [Fintype I] [Finite J]

/-- **The graded Cartan matrix** in a projective basis `bP` and a module basis `bM`: the matrix
of the Laurent-linear graded Cartan map.  Rows are indexed by `bM` and columns by `bP`. -/
noncomputable def gradedCartanMatrix
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    Matrix J I (LaurentPolynomial ℤ) :=
  by
    classical
    exact LinearMap.toMatrix bP bM (gradedCartanMap 𝒜)

/-- A graded Cartan-matrix entry is the corresponding module-basis coordinate of the image of a
projective-basis vector. -/
@[simp]
theorem gradedCartanMatrix_apply
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) (i : J) (j : I) :
    gradedCartanMatrix 𝒜 bP bM i j = bM.repr (gradedCartanMap 𝒜 (bP j)) i := by
  classical
  rw [gradedCartanMatrix, LinearMap.toMatrix_apply]

/-- If a projective-basis vector is the class of a finite graded projective, its graded Cartan
column consists of the module-basis coordinates of the class of that same graded module. -/
theorem gradedCartanMatrix_apply_of
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (i : J) (j : I) (M : GradedModuleCat.{uA} 𝒜)
    (hM : gradedFiniteProjectiveModules 𝒜 M)
    (hj : bP j = LaurentK0.of.{uA}
      (gradedFiniteProjectiveModulesExactStructure 𝒜) ⟨M, hM⟩) :
    gradedCartanMatrix 𝒜 bP bM i j =
      bM.repr (LaurentK0.of.{uA} (gradedFiniteModulesExactStructure 𝒜)
        ⟨M, gradedFiniteProjectiveModules_le_finiteModules M hM⟩) i := by
  rw [gradedCartanMatrix_apply, hj, gradedCartanMap_of]

/-- A column of the graded Cartan matrix is the coordinate vector of the corresponding
projective-basis vector under the graded Cartan map. -/
theorem gradedCartanMatrix_col
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) (j : I) :
    (gradedCartanMatrix 𝒜 bP bM).col j = bM.repr (gradedCartanMap 𝒜 (bP j)) := by
  funext i
  exact gradedCartanMatrix_apply 𝒜 bP bM i j

/-- The graded Cartan matrix sends the coordinate vector of a class to the coordinate vector of
its image under the graded Cartan map. -/
theorem gradedCartanMatrix_mulVec_repr
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :
    Matrix.mulVec (gradedCartanMatrix 𝒜 bP bM) (bP.repr x) =
      bM.repr (gradedCartanMap 𝒜 x) := by
  classical
  exact LinearMap.toMatrix_mulVec_repr bP bM (gradedCartanMap 𝒜) x

/-- Reconstruct the image of a projective-basis vector from the corresponding column of the
graded Cartan matrix. -/
theorem gradedCartanMap_basis_apply_eq_sum [Fintype J]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) (j : I) :
    gradedCartanMap 𝒜 (bP j) = ∑ i, gradedCartanMatrix 𝒜 bP bM i j • bM i := by
  rw [← bM.sum_repr (gradedCartanMap 𝒜 (bP j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [gradedCartanMatrix_apply]

/-- **Change of basis for the graded Cartan matrix.**  The target transition matrix acts on the
left and the source transition matrix acts on the right. -/
theorem gradedCartanMatrix_basis_change
    {I' : Type*} {J' : Type*} [Fintype I'] [Fintype J] [Finite J']
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (bM : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜)))
    (cP : Module.Basis I' (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
    (cM : Module.Basis J' (LaurentPolynomial ℤ)
      (LaurentK0.{uA} (gradedFiniteModulesExactStructure 𝒜))) :
    cM.toMatrix bM * gradedCartanMatrix 𝒜 bP bM * bP.toMatrix cP =
      gradedCartanMatrix 𝒜 cP cM := by
  classical
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    cP bP cM bM (gradedCartanMap 𝒜)

end TauCeti
