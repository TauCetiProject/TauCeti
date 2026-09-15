/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable

/-!
# The admissible lattice in the tripled type-D4 representation

This file reads the rational extension of the integral `24`-dimensional tripled representation of
the type-`D₄` Serre presentation, and the admissibility of its coordinate `ℤ`-lattice for the
Serre Kostant form, off the minuscule weight table `TauCeti.D4Tripled.weightTable`, where they are
proved for an arbitrary table.

Thus the tripled coordinate lattice is an admissible lattice for the explicit Serre-generator
Kostant form. Its weights already span the full type-`D₄` character lattice by
`TauCeti.DynkinType.span_range_d4TripledWeight_eq_top`. Together, these are the lattice inputs
needed to construct the tripled type-`D₄` Chevalley carrier.

## Main declarations

* `TauCeti.D4Tripled.rationalSerreRepresentation`: the rational tripled representation.
* `TauCeti.D4Tripled.rep`: its extension to the universal enveloping algebra.
* `TauCeti.D4Tripled.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.D4Tripled.rep_serreKostantForm_mem_lattice`: the Serre Kostant form preserves the
  lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* The file follows the formal template of `TauCeti.Algebra.Lie.E6.Minuscule.AdmissibleLattice`,
  specialized to the tripled type-`D₄` representation.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The rational representation -/

/-- The rational raising matrix obtained from the integral tripled representation. -/
noncomputable def raisingMatrixQ (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℚ :=
  weightTable.raisingMatrixQ i

/-- The rational lowering matrix obtained from the integral tripled representation. -/
noncomputable def loweringMatrixQ (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℚ :=
  weightTable.loweringMatrixQ i

/-- The rational Cartan matrix obtained from the integral tripled representation. -/
noncomputable def cartanGeneratorMatrixQ (i : Fin 4) : Matrix (Fin 24) (Fin 24) ℚ :=
  weightTable.cartanGeneratorMatrixQ i

/-- The entries of a rational raising matrix are the same zero-one coefficients as those of the
integral raising matrix. -/
@[simp]
theorem raisingMatrixQ_apply (i : Fin 4) (a b : Fin 24) :
    raisingMatrixQ i a b =
      if d4TripledWeight b i = -1 ∧ a = d4TripledReflection i b then 1 else 0 :=
  weightTable.raisingMatrixQ_apply i a b

/-- The entries of a rational lowering matrix are the same zero-one coefficients as those of the
integral lowering matrix. -/
@[simp]
theorem loweringMatrixQ_apply (i : Fin 4) (a b : Fin 24) :
    loweringMatrixQ i a b =
      if d4TripledWeight b i = 1 ∧ a = d4TripledReflection i b then 1 else 0 :=
  weightTable.loweringMatrixQ_apply i a b

/-- The rational Cartan generator is diagonal with the tripled weights on its diagonal. -/
@[simp]
theorem cartanGeneratorMatrixQ_apply (i : Fin 4) (a b : Fin 24) :
    cartanGeneratorMatrixQ i a b =
      if a = b then (d4TripledWeight b i : ℚ) else 0 :=
  weightTable.cartanGeneratorMatrixQ_apply i a b

/-- The rational tripled matrices satisfy the type-`D₄` Serre relations. -/
theorem isSerreSystemQ :
    TauCeti.IsSerreSystem ℚ (CartanMatrix.D 4) cartanGeneratorMatrixQ raisingMatrixQ
      loweringMatrixQ :=
  weightTable.isSerreSystemQ

/-- The rational `24`-dimensional tripled representation of the type-`D₄` Serre
presentation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.D 4) →ₗ⁅ℚ⁆ Matrix (Fin 24) (Fin 24) ℚ :=
  weightTable.rationalSerreRepresentation

/-- The rational representation sends each Cartan Serre generator to its diagonal tripled
matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 4) :
    rationalSerreRepresentation (TauCeti.serreH ℚ (CartanMatrix.D 4) i) =
      cartanGeneratorMatrixQ i :=
  weightTable.rationalSerreRepresentation_serreH i

/-- The rational representation sends each positive Serre generator to its raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 4) :
    rationalSerreRepresentation (TauCeti.serreE ℚ (CartanMatrix.D 4) i) = raisingMatrixQ i :=
  weightTable.rationalSerreRepresentation_serreE i

/-- The rational representation sends each negative Serre generator to its lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 4) :
    rationalSerreRepresentation (TauCeti.serreF ℚ (CartanMatrix.D 4) i) = loweringMatrixQ i :=
  weightTable.rationalSerreRepresentation_serreF i

/-! ## The enveloping-algebra representation -/

/-- The rational tripled representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ (CartanMatrix.D 4)) →ₐ[ℚ]
      Module.End ℚ (Fin 24 → ℚ) :=
  weightTable.rep

/-- The enveloping-algebra representation acts on an included Lie element by matrix-vector
multiplication. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.D 4)) (v : Fin 24 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v :=
  weightTable.rep_ι_apply x v

/-- Every rational raising matrix is square-zero. -/
@[simp]
theorem raisingMatrixQ_sq (i : Fin 4) : raisingMatrixQ i ^ 2 = 0 :=
  weightTable.raisingMatrixQ_pow_two i

/-- Every rational lowering matrix is square-zero. -/
@[simp]
theorem loweringMatrixQ_sq (i : Fin 4) : loweringMatrixQ i ^ 2 = 0 :=
  weightTable.loweringMatrixQ_pow_two i

/-- Every represented positive or negative Serre root generator is square-zero. -/
theorem rep_serreRootGenerator_sq (k : Fin 4 ⊕ Fin 4) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.D 4) k)) ^ 2 = 0 :=
  weightTable.rep_serreRootGenerator_pow_two k

/-- Every represented positive or negative Serre root generator acts nilpotently. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 4 ⊕ Fin 4) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.D 4) k))) :=
  weightTable.isNilpotent_rep_serreRootGenerator k

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational tripled module. -/
def lattice : Submodule ℤ (Fin 24 → ℚ) :=
  TauCeti.coordinateLattice (Fin 24)

/-- A tripled-module vector belongs to the lattice exactly when every coordinate is integral. -/
@[simp]
theorem mem_lattice_iff {v : Fin 24 → ℚ} :
    v ∈ lattice ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin 24)

/-- Every standard coordinate vector belongs to the tripled lattice. -/
theorem single_mem_lattice (a : Fin 24) : Pi.single a (1 : ℚ) ∈ lattice := by
  rw [← Pi.basisFun_apply]
  exact TauCeti.basisFun_mem_coordinateLattice (Fin 24) a

/-- The coordinate basis of the tripled lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 24) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 24)

/-- Coercing a tripled lattice-basis vector to the rational module gives the corresponding
coordinate vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 24) :
    ((latticeBasis a : lattice) : Fin 24 → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 24) a

/-- Every represented Serre root generator preserves the tripled coordinate lattice. -/
theorem rep_serreRootGenerator_mem_lattice (k : Fin 4 ⊕ Fin 4) {v : Fin 24 → ℚ}
    (hv : v ∈ lattice) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.D 4) k)) v ∈ lattice :=
  weightTable.rep_serreRootGenerator_mem_lattice k hv

/-- Each standard coordinate vector is a Cartan weight vector with its tripled weight. -/
theorem isCartanWeightVector_single (a : Fin 24) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.D 4)) rep (d4TripledWeight a) (Pi.single a 1) :=
  weightTable.isCartanWeightVector_single a

/-- Every tripled lattice-basis vector is a Cartan weight vector with its tripled weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 24) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.D 4)) rep (d4TripledWeight a)
      ((latticeBasis a : lattice) : Fin 24 → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single a

/-- **The tripled coordinate lattice is admissible for the type-`D₄` Serre Kostant form.** -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D 4))}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.D 4)) {v : Fin 24 → ℚ}
    (hv : v ∈ lattice) : rep u v ∈ lattice :=
  weightTable.rep_serreKostantForm_mem_lattice hu hv

/-- The tripled coordinate lattice is stable under the generic Kostant form built from the
type-`D₄` Serre generators. This is the form consumed by the carrier and base-change APIs. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D 4)))
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
      (TauCeti.serreRootGenerator (CartanMatrix.D 4))
      (TauCeti.serreH ℚ (CartanMatrix.D 4)))
    (v : Fin 24 → ℚ) (hv : v ∈ lattice) : rep u v ∈ lattice :=
  weightTable.rep_kostantForm_mem_lattice u hu v hv

end TauCeti.D4Tripled
