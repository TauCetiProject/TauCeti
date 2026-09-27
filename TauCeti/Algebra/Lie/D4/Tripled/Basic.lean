/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.D.TripledWeight


/-!
# A tripled weight representation of the type-D4 Serre presentation

This file constructs a `24`-dimensional integral representation of the type-`D₄` Serre
presentation. Its coordinate basis is indexed by the table
`TauCeti.DynkinType.d4TripledWeight`, whose three blocks are the weights of the natural and two
half-spin representations.

For a simple root `i`, the raising matrix sends the basis vector of weight `μ` to the basis vector
of weight `μ + αᵢ` when `⟨μ, αᵢ∨⟩ = -1`, and to zero otherwise. The lowering matrix is defined
dually. The Cartan generator acts diagonally by the simple-coroot coordinate of the weight. Every
nonzero entry of a raising or lowering matrix is `1`, and the diagonal entries of the Cartan
generators are the weight coordinates, in `{-1, 0, 1}`: on a minuscule weight table no sign is
needed, which is what makes the triality symmetry of the table an unsigned symmetry of this
representation, recorded entrywise in `raisingMatrix_trialityPerm`,
`loweringMatrix_trialityPerm` and `cartanGeneratorMatrix_trialityPerm`. These integral matrices
satisfy the Serre relations for the type-`D₄` Cartan matrix. Identifying this
presentation with the split semisimple Lie algebra of type `D₄`, and hence interpreting these
matrices as a representation of that algebra, remains downstream.

This is the representation-theoretic input for the tripled type-`D₄` Chevalley carrier, a
full-weight carrier stable under triality. The weights span the full character lattice
by `TauCeti.DynkinType.span_range_d4TripledWeight_eq_top`; constructing the associated Kostant
carrier, its group scheme and its triality automorphism remains downstream.

## Main declarations

* `TauCeti.D4Tripled.weightTable`: the minuscule weight table the construction reads, with
  `weightTable_cartanMatrix`, `weightTable_weight` and `weightTable_reflection` evaluating its
  three data fields.
* `TauCeti.D4Tripled.raisingMatrix`, `loweringMatrix`, and `cartanGeneratorMatrix`: the integral
  Chevalley generators on the tripled weight basis.
* `TauCeti.D4Tripled.raisingMatrix_trialityPerm`, `loweringMatrix_trialityPerm`, and
  `cartanGeneratorMatrix_trialityPerm`: triality carries each generator at node `i` to the
  generator at node `trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`.
* `TauCeti.D4Tripled.isSerreSystem`: the generators satisfy the type-`D₄` Serre relations.
* `TauCeti.D4Tripled.serreRepresentation`: the induced homomorphism from the integral type-`D₄`
  Serre presentation.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13.4 and 27.
* R. W. Carter, *Simple Groups of Lie Type*, §12.2.
* The construction follows the formal template of `TauCeti.Algebra.Lie.E6.Minuscule.Basic`,
  specialized to the tripled weight table of type `D₄`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The weight table -/

/-- **The twenty-four tripled weights of type `D₄`, as a minuscule weight table.** The type-`D₄`
Cartan matrix is symmetric, so no transpose is needed to place the coroot index first. -/
def weightTable : TauCeti.MinusculeWeightTable (Fin 4) (Fin 24) where
  cartanMatrix := CartanMatrix.D 4
  weight := d4TripledWeight
  reflection i := d4TripledReflection i
  cartanMatrix_diag i := CartanMatrix.D_diag (n := 4) i
  cartanMatrix_offDiag_nonpos := CartanMatrix.D_off_diag_nonpos 4
  cartanMatrix_zero_comm i j := by rw [(CartanMatrix.D_isSymm 4).apply]
  weight_eq_neg_one_or_eq_zero_or_eq_one :=
    d4TripledWeight_apply_eq_neg_one_or_eq_zero_or_eq_one
  weight_reflection i a j := by
    rw [(CartanMatrix.D_isSymm 4).apply]
    exact d4TripledWeight_reflection_apply i a j
  weight_injective := d4TripledWeight_injective

/-- The Cartan matrix of the tripled type-`D₄` weight table is the `D₄` Cartan matrix. -/
@[simp]
theorem weightTable_cartanMatrix : weightTable.cartanMatrix = CartanMatrix.D 4 :=
  (rfl)

/-- The weights of the tripled type-`D₄` weight table are the tripled weights. -/
@[simp]
theorem weightTable_weight : weightTable.weight = d4TripledWeight :=
  (rfl)

/-- The simple reflections of the tripled type-`D₄` weight table are the tripled reflections. -/
@[simp]
theorem weightTable_reflection (i : Fin 4) :
    weightTable.reflection i = d4TripledReflection i :=
  (rfl)

/-! ## Triality symmetry -/

/-- **Triality as a symmetry of the tripled minuscule weight table.** It acts simultaneously on
the type-`D₄` nodes and on the twenty-four weight indices. -/
def trialitySymmetry : weightTable.Symmetry where
  nodePerm := trialityPermD4
  indexPerm := d4TripledTrialityPerm
  weight_apply := d4TripledWeight_d4TripledTrialityPerm_apply
  cartanMatrix_apply i j := by
    simpa only [weightTable_cartanMatrix, DynkinType.cartanMatrix_D] using
      cartanMatrix_D4_trialityPermD4 i j

/-- The node permutation of the bundled triality symmetry is diagram triality. -/
@[simp]
theorem trialitySymmetry_nodePerm : trialitySymmetry.nodePerm = trialityPermD4 :=
  (rfl)

/-- The weight-index permutation of the bundled triality symmetry is triality on the tripled
weight table. -/
@[simp]
theorem trialitySymmetry_indexPerm :
    trialitySymmetry.indexPerm = d4TripledTrialityPerm :=
  (rfl)

/-- The bundled triality symmetry has order dividing three. -/
@[simp]
theorem trialitySymmetry_pow_three : trialitySymmetry ^ 3 = 1 := by
  apply TauCeti.MinusculeWeightTable.Symmetry.ext
  · simpa only [pow_succ, pow_zero, one_mul,
      TauCeti.MinusculeWeightTable.Symmetry.mul_nodePerm,
      TauCeti.MinusculeWeightTable.Symmetry.one_nodePerm, trialitySymmetry_nodePerm,
      ] using trialityPermD4_pow_three
  · simpa only [pow_succ, pow_zero, one_mul,
      TauCeti.MinusculeWeightTable.Symmetry.mul_indexPerm,
      TauCeti.MinusculeWeightTable.Symmetry.one_indexPerm, trialitySymmetry_indexPerm,
      ] using d4TripledTrialityPerm_pow_three

/-! ## The Chevalley generators -/

/-- The raising matrix of the `i`-th simple root on the integral tripled weight basis. -/
def raisingMatrix (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℤ :=
  weightTable.raisingMatrix i

/-- The lowering matrix of the `i`-th simple root on the integral tripled weight basis. -/
def loweringMatrix (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℤ :=
  weightTable.loweringMatrix i

/-- The diagonal matrix of the `i`-th simple coroot on the integral tripled weight basis. -/
def cartanGeneratorMatrix (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℤ :=
  weightTable.cartanGeneratorMatrix i

/-- The entry formula for a simple raising matrix. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 4) (a b : Fin 24) :
    raisingMatrix i a b =
      if d4TripledWeight b i = -1 ∧ a = d4TripledReflection i b then 1 else 0 :=
  weightTable.raisingMatrix_apply i a b

/-- The entry formula for a simple lowering matrix. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 4) (a b : Fin 24) :
    loweringMatrix i a b =
      if d4TripledWeight b i = 1 ∧ a = d4TripledReflection i b then 1 else 0 :=
  weightTable.loweringMatrix_apply i a b

/-- The entry formula for a simple Cartan generator matrix. -/
@[simp]
theorem cartanGeneratorMatrix_apply (i : Fin 4) (a b : Fin 24) :
    cartanGeneratorMatrix i a b = if a = b then d4TripledWeight b i else 0 :=
  weightTable.cartanGeneratorMatrix_apply i a b

/-! ## Triality on the generators

Triality permutes the weight basis by `d4TripledTrialityPerm` and the nodes by `trialityPermD4`,
and it carries each Chevalley generator at a node to the generator at the image node, with no
change of sign: reading a generator at the image node in the image basis gives back the generator
at the original node.

None of the three equations is a `simp` lemma: the entry formulas `raisingMatrix_apply`,
`loweringMatrix_apply` and `cartanGeneratorMatrix_apply` are, and they already rewrite both sides
to conditions on the weight table, so the left-hand sides below are not `simp`-normal. -/

/-- Triality carries the raising matrix at node `i` to the raising matrix at node
`trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`. -/
theorem raisingMatrix_trialityPerm (i : Fin 4) (a b : Fin 24) :
    raisingMatrix (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b) =
      raisingMatrix i a b :=
  TauCeti.MinusculeWeightTable.Symmetry.raisingMatrix_apply
    (T := weightTable) trialitySymmetry i a b

/-- Triality carries the lowering matrix at node `i` to the lowering matrix at node
`trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`. -/
theorem loweringMatrix_trialityPerm (i : Fin 4) (a b : Fin 24) :
    loweringMatrix (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b) =
      loweringMatrix i a b :=
  TauCeti.MinusculeWeightTable.Symmetry.loweringMatrix_apply
    (T := weightTable) trialitySymmetry i a b

/-- Triality carries the Cartan generator at node `i` to the Cartan generator at node
`trialityPermD4 i`, entrywise along `d4TripledTrialityPerm`. -/
theorem cartanGeneratorMatrix_trialityPerm (i : Fin 4) (a b : Fin 24) :
    cartanGeneratorMatrix (trialityPermD4 i) (d4TripledTrialityPerm a) (d4TripledTrialityPerm b) =
      cartanGeneratorMatrix i a b :=
  TauCeti.MinusculeWeightTable.Symmetry.cartanGeneratorMatrix_apply
    (T := weightTable) trialitySymmetry i a b

/-- Triality carries the raising matrix at node `i` to the raising matrix at node
`trialityPermD4 i`, as a matrix reindexing identity. -/
@[simp]
theorem raisingMatrix_trialityPerm_submatrix (i : Fin 4) :
    (raisingMatrix (trialityPermD4 i)).submatrix d4TripledTrialityPerm
      d4TripledTrialityPerm = raisingMatrix i :=
  TauCeti.MinusculeWeightTable.Symmetry.raisingMatrix_submatrix
    (T := weightTable) trialitySymmetry i

/-- Triality carries the lowering matrix at node `i` to the lowering matrix at node
`trialityPermD4 i`, as a matrix reindexing identity. -/
@[simp]
theorem loweringMatrix_trialityPerm_submatrix (i : Fin 4) :
    (loweringMatrix (trialityPermD4 i)).submatrix d4TripledTrialityPerm
      d4TripledTrialityPerm = loweringMatrix i :=
  TauCeti.MinusculeWeightTable.Symmetry.loweringMatrix_submatrix
    (T := weightTable) trialitySymmetry i

/-- Triality carries the Cartan generator at node `i` to the Cartan generator at node
`trialityPermD4 i`, as a matrix reindexing identity. -/
@[simp]
theorem cartanGeneratorMatrix_trialityPerm_submatrix (i : Fin 4) :
    (cartanGeneratorMatrix (trialityPermD4 i)).submatrix d4TripledTrialityPerm
      d4TripledTrialityPerm = cartanGeneratorMatrix i :=
  TauCeti.MinusculeWeightTable.Symmetry.cartanGeneratorMatrix_submatrix
    (T := weightTable) trialitySymmetry i

/-- Every raising matrix of the tripled weight table squares to zero. -/
@[simp]
theorem raisingMatrix_pow_two (i : Fin 4) : raisingMatrix i ^ 2 = 0 :=
  weightTable.raisingMatrix_pow_two i

/-- Every lowering matrix of the tripled weight table squares to zero. -/
@[simp]
theorem loweringMatrix_pow_two (i : Fin 4) : loweringMatrix i ^ 2 = 0 :=
  weightTable.loweringMatrix_pow_two i

/-! ## The Serre relations -/

/-- At each simple node, the three integral tripled matrices form an `sl₂` triple. -/
theorem isSl2Triple (i : Fin 4) :
    _root_.IsSl2Triple (cartanGeneratorMatrix i) (raisingMatrix i) (loweringMatrix i) :=
  weightTable.isSl2Triple i (exists_d4TripledWeight_apply_eq_neg_one i)

/-- **The integral `24`-dimensional tripled matrices satisfy the Serre relations of type
`D₄`.** The type-`D₄` Cartan matrix is symmetric, so no transpose is needed to place the coroot
index first. -/
theorem isSerreSystem :
    TauCeti.IsSerreSystem ℤ (CartanMatrix.D 4) cartanGeneratorMatrix raisingMatrix
      loweringMatrix :=
  weightTable.isSerreSystem

/-- The integral `24`-dimensional tripled representation of the type-`D₄` Serre presentation. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ (CartanMatrix.D 4) →ₗ⁅ℤ⁆ Matrix (Fin 24) (Fin 24) ℤ :=
  weightTable.serreRepresentation

/-- The tripled representation sends a Cartan generator to its diagonal weight matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 4) :
    serreRepresentation (TauCeti.serreH ℤ (CartanMatrix.D 4) i) = cartanGeneratorMatrix i :=
  weightTable.serreRepresentation_serreH i

/-- The tripled representation sends a positive generator to its raising matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 4) :
    serreRepresentation (TauCeti.serreE ℤ (CartanMatrix.D 4) i) = raisingMatrix i :=
  weightTable.serreRepresentation_serreE i

/-- The tripled representation sends a negative generator to its lowering matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 4) :
    serreRepresentation (TauCeti.serreF ℤ (CartanMatrix.D 4) i) = loweringMatrix i :=
  weightTable.serreRepresentation_serreF i

end TauCeti.D4Tripled
