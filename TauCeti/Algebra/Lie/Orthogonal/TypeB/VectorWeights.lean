/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.Root.Space
import TauCeti.Algebra.Lie.Weights.Basis

/-!
# The vector weights of the split odd orthogonal Lie algebra

The diagonal Cartan `diag(0, d, -d)` of `LieAlgebra.Orthogonal.typeB ι K` acts diagonally on the
standard basis of the standard module `Unit ⊕ ι ⊕ ι → K`: the middle basis vector has weight `0`,
and the basis vectors in the two copies of `ι` have the opposite coordinate weights `εᵢ` and `-εᵢ`.
These are all of its weights.

The **lattice of vector weights** is the `ℤ`-span of the coordinate functionals `εᵢ`, the weights
of the standard module. In coordinates it consists of the weights with integer coordinates. It is
the root lattice of type `B`, whose short roots are the `±εᵢ`. Having only vector weights is
preserved by the constructions that add weights or forget them: a tensor product of two
finite-dimensional triangularizable modules whose weights are vector weights again has only vector
weights (`TauCeti.exists_mem_weight_tensorProduct`), and so does every module that embeds in one of
them (`LieModuleHom.exists_mem_weight_of_injective`). Both hold for any additively closed set of
linear forms in place of the vector weights. Starting from the standard module, this covers every
tensor power of the standard module and every module that embeds in a tensor power, such as the
exterior and symmetric powers in characteristic zero.

The point of the lattice is what lies outside it: in characteristic zero and positive rank, the
weights `½(±ε₁ ± ⋯ ± εₗ)` of the spin module are not vector weights, so the spin module occurs in
no such construction.

## Main definitions

* `TauCeti.typeBVectorWeightLattice`: the lattice of vector weights, the `ℤ`-span of the
  coordinate functionals `εᵢ`.

## Main results

* `TauCeti.mem_typeBVectorWeightLattice_iff`: the vector weights are the weights with integer
  coordinates.
* `TauCeti.lie_typeBDiagonalCartan_single`: the diagonal Cartan acts on each standard basis vector
  by its coordinate weight `TauCeti.typeBCoordinateWeight`.
* `TauCeti.genWeightSpace_typeBStandard_ne_bot_iff`: the weights of the standard module are `0`
  and the `±εᵢ`.
* `TauCeti.typeBCoordinateWeight_mem_typeBVectorWeightLattice`: they are vector weights.
* `LieModule.Weight.exists_mem_typeBVectorWeightLattice_standard`: every weight of the standard
  module is a vector weight.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 19 and §20.1.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.
-/

public section

open LieModule Module

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v

section CommRing

variable (K : Type u) [CommRing K] (ι : Type v) [Fintype ι] [DecidableEq ι]

/-! ### The lattice of vector weights -/

/-- The **lattice of vector weights** of the split odd orthogonal Lie algebra: the `ℤ`-span of the
coordinate functionals `εᵢ` on its diagonal Cartan, which are the nonzero weights of the standard
module. It is the root lattice of type `B`. -/
noncomputable def typeBVectorWeightLattice :
    Submodule ℤ (Module.Dual K (typeBDiagonalCartan K ι)) :=
  Submodule.span ℤ (Set.range (typeBEpsilon (K := K) (ι := ι)))

variable {K ι}

/-- An integer coordinate vector is the corresponding integer combination of the coordinate
functionals. -/
theorem typeBWeightEquiv_intCast (m : ι → ℤ) :
    typeBWeightEquiv (K := K) (ι := ι) (fun i ↦ (m i : K)) = ∑ i, m i • typeBEpsilon i := by
  ext A
  simp [typeBEpsilon_apply, typeBWeightEquiv_apply, Finset.sum_apply, zsmul_eq_mul]

/-- The coordinate functional `εᵢ` is a vector weight. -/
@[simp]
theorem typeBEpsilon_mem_typeBVectorWeightLattice (i : ι) :
    typeBEpsilon i ∈ typeBVectorWeightLattice K ι :=
  Submodule.subset_span ⟨i, rfl⟩

/-- **The vector weights are the weights with integer coordinates.** -/
theorem mem_typeBVectorWeightLattice_iff {φ : Module.Dual K (typeBDiagonalCartan K ι)} :
    φ ∈ typeBVectorWeightLattice K ι ↔
      ∃ m : ι → ℤ, typeBWeightEquiv (K := K) (ι := ι) (fun i ↦ (m i : K)) = φ := by
  simp_rw [typeBWeightEquiv_intCast]
  exact Submodule.mem_span_range_iff_exists_fun ℤ

/-! ### The weights of the standard module -/

/-- **The diagonal Cartan acts on each standard basis vector by its coordinate weight.** -/
theorem lie_typeBDiagonalCartan_single (A : typeBDiagonalCartan K ι) (j : Unit ⊕ ι ⊕ ι) :
    ⁅A, Pi.single j (1 : K)⁆ = typeBCoordinateWeight j A • Pi.single j (1 : K) := by
  obtain ⟨d, rfl⟩ := (typeBDiagonalEquiv (K := K) (ι := ι)).surjective A
  have hd : typeBDiagonalMatrix d = Matrix.diagonal (typeBDiagonalValue d) :=
    Matrix.ext fun a b ↦ by rw [typeBDiagonalMatrix_apply, Matrix.diagonal_apply]
  rw [typeBCoordinateWeight_apply, LieSubalgebra.coe_bracket_of_module,
    LieSubalgebra.coe_bracket_of_module, coe_typeBDiagonalEquiv_apply, Matrix.lie_apply]
  simp only [hd, Matrix.diagonal_mulVec_single, Matrix.diagonal_apply_eq]
  rw [← smul_eq_mul, Pi.single_smul']

/-- The weights of the standard basis vectors of the standard module are vector weights. -/
@[simp]
theorem typeBCoordinateWeight_mem_typeBVectorWeightLattice (j : Unit ⊕ ι ⊕ ι) :
    typeBCoordinateWeight (K := K) j ∈ typeBVectorWeightLattice K ι := by
  rcases j with j | j | j <;> simp

end CommRing

section Field

variable {K : Type u} [Field K] {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- **The weights of the standard module are `0` and the `±εᵢ`**, the weights of its standard
basis vectors. -/
@[simp]
theorem genWeightSpace_typeBStandard_ne_bot_iff (χ : typeBDiagonalCartan K ι → K) :
    genWeightSpace (Unit ⊕ ι ⊕ ι → K) χ ≠ ⊥ ↔ ∃ j, (typeBCoordinateWeight j : _ → K) = χ := by
  refine (Pi.basisFun K (Unit ⊕ ι ⊕ ι)).genWeightSpace_ne_bot_iff_of_weight_basis
    (μ := typeBCoordinateWeight) (fun j A ↦ ?_) χ
  simpa only [Pi.basisFun_apply] using lie_typeBDiagonalCartan_single A j

/-- The diagonal Cartan acts triangularizably on the standard module: the standard basis
diagonalizes it. -/
instance instIsTriangularizableTypeBStandard :
    IsTriangularizable K (typeBDiagonalCartan K ι) (Unit ⊕ ι ⊕ ι → K) :=
  (Pi.basisFun K (Unit ⊕ ι ⊕ ι)).isTriangularizable_of_weight_basis
    (μ := typeBCoordinateWeight) fun j A ↦ by
      simpa only [Pi.basisFun_apply] using lie_typeBDiagonalCartan_single A j

end Field

end TauCeti

namespace LieModule.Weight

open TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every weight of the standard module is a vector weight. -/
theorem exists_mem_typeBVectorWeightLattice_standard
    (χ : Weight K (typeBDiagonalCartan K ι) (Unit ⊕ ι ⊕ ι → K)) :
    ∃ φ ∈ typeBVectorWeightLattice K ι, ⇑φ = ⇑χ := by
  obtain ⟨j, hj⟩ := (genWeightSpace_typeBStandard_ne_bot_iff (χ : _ → K)).mp
    (Weight.genWeightSpace_ne_bot _ χ)
  exact ⟨_, typeBCoordinateWeight_mem_typeBVectorWeightLattice j, hj⟩

end LieModule.Weight
