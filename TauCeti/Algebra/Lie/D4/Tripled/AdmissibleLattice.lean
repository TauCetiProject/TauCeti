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

* `TauCeti.D4Tripled.rep`: the rational representation of the universal enveloping algebra.
* `TauCeti.D4Tripled.isSl2Triple_rep_serreRootGenerator`: the represented generators at every
  node form an `sl₂` triple.
* `TauCeti.D4Tripled.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.D4Tripled.rep_kostantForm_mem_lattice`: the generic Kostant form preserves the
  lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* The rational representation and admissibility results specialize
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable`.
-/

public section

open scoped Matrix

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The enveloping-algebra representation -/

/-- The rational tripled representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ weightTable.cartanMatrix) →ₐ[ℚ]
      Module.End ℚ (Fin 24 → ℚ) :=
  weightTable.rep

/-- The rational tripled representation is the representation of the tripled weight table. -/
theorem rep_def : rep = weightTable.rep :=
  (rfl)

/-- Every represented positive or negative Serre root generator acts nilpotently. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 4 ⊕ Fin 4) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator weightTable.cartanMatrix k))) :=
  weightTable.isNilpotent_rep_serreRootGenerator k

/-- The represented Cartan, positive, and negative Serre generators at every node form an `sl₂`
triple: each simple-coroot coordinate takes the value `-1` on some tripled weight. -/
theorem isSl2Triple_rep_serreRootGenerator (i : Fin 4) :
    _root_.IsSl2Triple
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreH ℚ weightTable.cartanMatrix i)))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix (.inl i))))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix (.inr i)))) := by
  obtain ⟨a, ha⟩ := exists_d4TripledWeight_apply_eq_neg_one i
  exact weightTable.isSl2Triple_rep_serreRootGenerator i
    ⟨a, by rw [weightTable_weight, ha]; decide⟩

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational tripled module. -/
def lattice : Submodule ℤ (Fin 24 → ℚ) :=
  TauCeti.coordinateLattice (Fin 24)

/-- The tripled lattice is the standard coordinate lattice. -/
theorem lattice_def : lattice = TauCeti.coordinateLattice (Fin 24) :=
  (rfl)

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

/-- Every tripled lattice-basis vector is a Cartan weight vector with its tripled weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 24) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ weightTable.cartanMatrix) rep (d4TripledWeight a)
      ((latticeBasis a : lattice) : Fin 24 → ℚ) := by
  rw [coe_latticeBasis]
  simpa only [rep, weightTable_weight] using weightTable.isCartanWeightVector_single a

/-- The tripled coordinate lattice is stable under the generic Kostant form built from the
type-`D₄` Serre generators. This is the form consumed by the carrier and base-change APIs. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ weightTable.cartanMatrix))
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
      (TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (TauCeti.serreH ℚ weightTable.cartanMatrix))
    (v : Fin 24 → ℚ) (hv : v ∈ lattice) : rep u v ∈ lattice :=
  weightTable.rep_kostantForm_mem_lattice u hu v hv

end TauCeti.D4Tripled
