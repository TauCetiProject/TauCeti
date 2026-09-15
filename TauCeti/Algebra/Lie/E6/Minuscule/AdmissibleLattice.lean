/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable

/-!
# The admissible lattice in the type-E6 minuscule representation

The integral `27`-dimensional minuscule representation of the type-`E₆` Serre presentation extends
to a rational representation whose coordinate `ℤ`-lattice is stable under the Serre Kostant form.
The minuscule weights span the full type-`E₆` character lattice, so this admissible lattice supplies
the full-weight integral structure associated to the minuscule representation.

## Main declarations

* `TauCeti.E6Minuscule.rationalSerreRepresentation`: the rational minuscule representation.
* `TauCeti.E6Minuscule.rep`: its extension to the universal enveloping algebra.
* `TauCeti.E6Minuscule.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.E6Minuscule.rep_serreKostantForm_mem_lattice`: the Serre Kostant form preserves the
  lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
-/

public section

open scoped Matrix

namespace TauCeti.E6Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The rational representation -/

/-- The rational raising matrix obtained from the integral minuscule representation. -/
noncomputable def raisingMatrixQ (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℚ :=
  weightTable.raisingMatrixQ i

/-- The rational lowering matrix obtained from the integral minuscule representation. -/
noncomputable def loweringMatrixQ (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℚ :=
  weightTable.loweringMatrixQ i

/-- The rational Cartan matrix obtained from the integral minuscule representation. -/
noncomputable def cartanGeneratorMatrixQ (i : Fin 6) : Matrix (Fin 27) (Fin 27) ℚ :=
  weightTable.cartanGeneratorMatrixQ i

/-- The entries of a rational raising matrix are the same zero-one coefficients as those of the
integral raising matrix. -/
@[simp]
theorem raisingMatrixQ_apply (i : Fin 6) (a b : Fin 27) :
    raisingMatrixQ i a b =
      if e6MinusculeWeight b i = -1 ∧ a = e6MinusculeReflection i b then 1 else 0 :=
  weightTable.raisingMatrixQ_apply i a b

/-- The entries of a rational lowering matrix are the same zero-one coefficients as those of the
integral lowering matrix. -/
@[simp]
theorem loweringMatrixQ_apply (i : Fin 6) (a b : Fin 27) :
    loweringMatrixQ i a b =
      if e6MinusculeWeight b i = 1 ∧ a = e6MinusculeReflection i b then 1 else 0 :=
  weightTable.loweringMatrixQ_apply i a b

/-- The rational Cartan generator is diagonal with the minuscule weights on its diagonal. -/
@[simp]
theorem cartanGeneratorMatrixQ_apply (i : Fin 6) (a b : Fin 27) :
    cartanGeneratorMatrixQ i a b =
      if a = b then (e6MinusculeWeight b i : ℚ) else 0 :=
  weightTable.cartanGeneratorMatrixQ_apply i a b

/-- The rational minuscule matrices satisfy the type-`E₆` Serre relations. -/
theorem isSerreSystemQ :
    TauCeti.IsSerreSystem ℚ (CartanMatrix.E 6)ᵀ cartanGeneratorMatrixQ raisingMatrixQ
      loweringMatrixQ :=
  weightTable.isSerreSystemQ

/-- The rational `27`-dimensional minuscule representation of the type-`E₆` Serre
presentation. -/
noncomputable def rationalSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ →ₗ⁅ℚ⁆ Matrix (Fin 27) (Fin 27) ℚ :=
  weightTable.rationalSerreRepresentation

/-- The rational representation sends each Cartan Serre generator to its diagonal minuscule
matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreH (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ i) =
      cartanGeneratorMatrixQ i :=
  weightTable.rationalSerreRepresentation_serreH i

/-- The rational representation sends each positive Serre generator to its raising matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreE (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreE ℚ (CartanMatrix.E 6)ᵀ i) = raisingMatrixQ i :=
  weightTable.rationalSerreRepresentation_serreE i

/-- The rational representation sends each negative Serre generator to its lowering matrix. -/
@[simp]
theorem rationalSerreRepresentation_serreF (i : Fin 6) :
    rationalSerreRepresentation (TauCeti.serreF ℚ (CartanMatrix.E 6)ᵀ i) = loweringMatrixQ i :=
  weightTable.rationalSerreRepresentation_serreF i

/-! ## The enveloping-algebra representation -/

/-- The rational minuscule representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ) →ₐ[ℚ]
      Module.End ℚ (Fin 27 → ℚ) :=
  weightTable.rep

/-- The enveloping-algebra representation acts on an included Lie element by matrix-vector
multiplication. -/
theorem rep_ι_apply (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ) (v : Fin 27 → ℚ) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ x) v = rationalSerreRepresentation x *ᵥ v :=
  weightTable.rep_ι_apply x v

/-- Every rational raising matrix is square-zero. -/
@[simp]
theorem raisingMatrixQ_pow_two (i : Fin 6) : raisingMatrixQ i ^ 2 = 0 :=
  weightTable.raisingMatrixQ_pow_two i

/-- Every rational lowering matrix is square-zero. -/
@[simp]
theorem loweringMatrixQ_pow_two (i : Fin 6) : loweringMatrixQ i ^ 2 = 0 :=
  weightTable.loweringMatrixQ_pow_two i

/-- Every represented positive or negative Serre root generator is square-zero. -/
theorem rep_serreRootGenerator_pow_two (k : Fin 6 ⊕ Fin 6) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k)) ^ 2 = 0 :=
  weightTable.rep_serreRootGenerator_pow_two k

/-- Every represented positive or negative Serre root generator acts nilpotently. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 6 ⊕ Fin 6) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k))) :=
  weightTable.isNilpotent_rep_serreRootGenerator k

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational minuscule module. -/
def lattice : Submodule ℤ (Fin 27 → ℚ) :=
  TauCeti.coordinateLattice (Fin 27)

/-- A minuscule-module vector belongs to the lattice exactly when every coordinate is integral. -/
@[simp]
theorem mem_lattice_iff {v : Fin 27 → ℚ} :
    v ∈ lattice ↔ ∀ a, ∃ z : ℤ, (z : ℚ) = v a :=
  TauCeti.mem_coordinateLattice_iff (Fin 27)

/-- Every standard coordinate vector belongs to the minuscule lattice. -/
theorem single_mem_lattice (a : Fin 27) : Pi.single a (1 : ℚ) ∈ lattice := by
  rw [← Pi.basisFun_apply]
  exact TauCeti.basisFun_mem_coordinateLattice (Fin 27) a

/-- The coordinate basis of the minuscule lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 27) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 27)

/-- Coercing a minuscule lattice-basis vector to the rational module gives the corresponding
coordinate vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 27) :
    ((latticeBasis a : lattice) : Fin 27 → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 27) a

/-- Every represented Serre root generator preserves the minuscule coordinate lattice. -/
theorem rep_serreRootGenerator_mem_lattice (k : Fin 6 ⊕ Fin 6) {v : Fin 27 → ℚ}
    (hv : v ∈ lattice) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ k)) v ∈ lattice :=
  weightTable.rep_serreRootGenerator_mem_lattice k hv

/-- Each standard coordinate vector is a Cartan weight vector with its minuscule weight. -/
theorem isCartanWeightVector_single (a : Fin 27) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep (e6MinusculeWeight a) (Pi.single a 1) :=
  weightTable.isCartanWeightVector_single a

/-- Every minuscule lattice-basis vector is a Cartan weight vector with its minuscule weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 27) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ) rep (e6MinusculeWeight a)
      ((latticeBasis a : lattice) : Fin 27 → ℚ) := by
  rw [coe_latticeBasis]
  exact isCartanWeightVector_single a

/-- **The minuscule coordinate lattice is admissible for the type-`E₆` Serre Kostant form.** -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ)}
    (hu : u ∈ TauCeti.serreKostantForm (CartanMatrix.E 6)ᵀ) {v : Fin 27 → ℚ}
    (hv : v ∈ lattice) : rep u v ∈ lattice :=
  weightTable.rep_serreKostantForm_mem_lattice hu hv

/-- The minuscule coordinate lattice is stable under the generic Kostant form built from the
type-`E₆` Serre generators. This is the form consumed by the carrier and base-change APIs. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.E 6)ᵀ))
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
      (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ)
      (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ))
    (v : Fin 27 → ℚ) (hv : v ∈ lattice) : rep u v ∈ lattice :=
  weightTable.rep_kostantForm_mem_lattice u hu v hv

end TauCeti.E6Minuscule
