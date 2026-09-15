/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.E6.MinusculeWeight


/-!
# A 27-dimensional representation of the type-E6 Serre presentation

This file constructs a 27-dimensional representation of the type-`E₆` Serre presentation. The
coordinate basis is indexed by the Weyl orbit of the first fundamental weight enumerated by
`TauCeti.DynkinType.e6MinusculeWeight`.

For a simple root `i`, the raising matrix sends the basis vector of weight `μ` to the basis vector
of weight `μ + αᵢ` when `⟨μ, αᵢ∨⟩ = -1`, and to zero otherwise. The lowering matrix is defined
dually. The Cartan generator acts diagonally by the simple-coroot coordinate of the weight. These
integral matrices satisfy the Serre relations for the transposed type-`E₆` Cartan matrix.
Identifying this presentation with the split semisimple Lie algebra of type `E₆`, and hence
interpreting these matrices as a representation of that algebra, remains downstream.

This is the representation-theoretic input for the full-weight type-`E₆` Chevalley--Demazure
carrier required by Layer 9 of the ReductiveGroups roadmap. The weights span the full character
lattice by `TauCeti.DynkinType.span_range_e6MinusculeWeight_eq_top`; constructing the associated
Kostant carrier and its group scheme remains downstream.

## Main declarations

* `TauCeti.E6Minuscule.raisingMatrix`, `loweringMatrix`, and `cartanGeneratorMatrix`: the
  integral Chevalley generators on the minuscule weight basis.
* `TauCeti.E6Minuscule.weightTable`: the minuscule weight table the construction reads, with
  `weightTable_cartanMatrix`, `weightTable_weight` and `weightTable_reflection` evaluating its
  three data fields.
* `TauCeti.E6Minuscule.isSerreSystem`: the generators satisfy the type-`E₆` Serre relations.
* `TauCeti.E6Minuscule.serreRepresentation`: the induced homomorphism from the integral
  type-`E₆` Serre presentation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13.4 and 27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.2.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The weight table -/

/-- The coordinate change under a simple reflection, in the fundamental-weight basis. -/
private theorem e6MinusculeWeight_reflection_apply (i : Fin 6) (a : Fin 27) (j : Fin 6) :
    e6MinusculeWeight (e6MinusculeReflection i a) j =
      e6MinusculeWeight a j - e6MinusculeWeight a i * CartanMatrix.E 6 i j := by
  have h := congrFun (e6MinusculeWeight_reflection i a) j
  rw [root_e6SimpleIndex] at h
  simpa using h

/-- **The twenty-seven minuscule weights of type `E₆`, as a minuscule weight table.** The Cartan
matrix is transposed, which is the convention placing the coroot index first. -/
def weightTable : TauCeti.MinusculeWeightTable (Fin 6) (Fin 27) where
  cartanMatrix := (CartanMatrix.E 6)ᵀ
  weight := e6MinusculeWeight
  reflection i := e6MinusculeReflection i
  cartanMatrix_isSymm := by
    rw [CartanMatrix.E_transpose]
    exact CartanMatrix.E_isSymm 6
  cartanMatrix_diag i := by
    rw [Matrix.transpose_apply, CartanMatrix.E_diag]
  cartanMatrix_isSimplyLaced := by
    rw [Matrix.isSimplyLaced_transpose]
    exact CartanMatrix.isSimplyLaced_E 6
  weight_eq_neg_one_or_eq_zero_or_eq_one :=
    e6MinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one
  weight_reflection i a j := by
    rw [Matrix.transpose_apply, (CartanMatrix.E_isSymm 6).apply]
    exact e6MinusculeWeight_reflection_apply i a j
  weight_injective := e6MinusculeWeight_injective

/-- The Cartan matrix of the type-`E₆` minuscule weight table is the transposed `E₆` Cartan
matrix. -/
@[simp]
theorem weightTable_cartanMatrix : weightTable.cartanMatrix = (CartanMatrix.E 6)ᵀ :=
  (rfl)

/-- The weights of the type-`E₆` minuscule weight table are the minuscule weights. -/
@[simp]
theorem weightTable_weight : weightTable.weight = e6MinusculeWeight :=
  (rfl)

/-- The simple reflections of the type-`E₆` minuscule weight table are the minuscule
reflections. -/
@[simp]
theorem weightTable_reflection (i : Fin 6) :
    weightTable.reflection i = e6MinusculeReflection i :=
  (rfl)

/-- Reflection in a simple root negates the corresponding simple-coroot coordinate of a
minuscule weight. -/
@[simp]
theorem e6MinusculeWeight_reflection_apply_self (i : Fin 6) (a : Fin 27) :
    e6MinusculeWeight (e6MinusculeReflection i a) i = -e6MinusculeWeight a i :=
  weightTable.weight_reflection_self i a

/-! ## The Chevalley generators -/

/-- The raising matrix of the `i`-th simple root on the integral minuscule weight basis. -/
def raisingMatrix (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  weightTable.raisingMatrix i

/-- The lowering matrix of the `i`-th simple root on the integral minuscule weight basis. -/
def loweringMatrix (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  weightTable.loweringMatrix i

/-- The diagonal matrix of the `i`-th simple coroot on the integral minuscule weight basis. -/
def cartanGeneratorMatrix (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℤ :=
  weightTable.cartanGeneratorMatrix i

/-- The entry formula for a simple raising matrix. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 6) (a b : Fin 27) :
    raisingMatrix i a b =
      if e6MinusculeWeight b i = -1 ∧ a = e6MinusculeReflection i b then 1 else 0 :=
  weightTable.raisingMatrix_apply i a b

/-- The entry formula for a simple lowering matrix. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 6) (a b : Fin 27) :
    loweringMatrix i a b =
      if e6MinusculeWeight b i = 1 ∧ a = e6MinusculeReflection i b then 1 else 0 :=
  weightTable.loweringMatrix_apply i a b

/-- The entry formula for a simple Cartan generator matrix. -/
@[simp]
theorem cartanGeneratorMatrix_apply (i : Fin 6) (a b : Fin 27) :
    cartanGeneratorMatrix i a b = if a = b then e6MinusculeWeight b i else 0 :=
  weightTable.cartanGeneratorMatrix_apply i a b

/-- Every raising matrix of the minuscule weight table squares to zero. -/
@[simp]
theorem raisingMatrix_pow_two (i : Fin 6) : raisingMatrix i ^ 2 = 0 :=
  weightTable.raisingMatrix_pow_two i

/-- Every lowering matrix of the minuscule weight table squares to zero. -/
@[simp]
theorem loweringMatrix_pow_two (i : Fin 6) : loweringMatrix i ^ 2 = 0 :=
  weightTable.loweringMatrix_pow_two i

/-! ## The Serre relations -/

/-- At each simple node, the three integral minuscule matrices form an `sl₂` triple. -/
theorem isSl2Triple (i : Fin 6) :
    _root_.IsSl2Triple (cartanGeneratorMatrix i) (raisingMatrix i) (loweringMatrix i) :=
  weightTable.isSl2Triple i (exists_e6MinusculeWeight_apply_eq_neg_one i)

/-- **The integral `27`-dimensional minuscule matrices satisfy the Serre relations of type
`E₆`.** The transpose is the convention in which the coroot index precedes the root index. -/
theorem isSerreSystem :
    TauCeti.IsSerreSystem ℤ (CartanMatrix.E 6)ᵀ cartanGeneratorMatrix raisingMatrix
      loweringMatrix :=
  weightTable.isSerreSystem

/-- The integral `27`-dimensional minuscule representation of the type-`E₆` Serre
presentation. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.E 6)ᵀ →ₗ⁅ℤ⁆ Matrix (Fin 27) (Fin 27) ℤ :=
  weightTable.serreRepresentation

/-- The minuscule representation sends a Cartan generator to its diagonal weight matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 6) :
    serreRepresentation (TauCeti.serreH ℤ (CartanMatrix.E 6)ᵀ i) = cartanGeneratorMatrix i :=
  weightTable.serreRepresentation_serreH i

/-- The minuscule representation sends a positive generator to its raising matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 6) :
    serreRepresentation (TauCeti.serreE ℤ (CartanMatrix.E 6)ᵀ i) = raisingMatrix i :=
  weightTable.serreRepresentation_serreE i

/-- The minuscule representation sends a negative generator to its lowering matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 6) :
    serreRepresentation (TauCeti.serreF ℤ (CartanMatrix.E 6)ᵀ i) = loweringMatrix i :=
  weightTable.serreRepresentation_serreF i

end TauCeti.E6Minuscule
