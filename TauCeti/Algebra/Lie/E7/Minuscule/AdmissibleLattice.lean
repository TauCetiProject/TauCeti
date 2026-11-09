/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E7.Minuscule.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable

/-!
# The admissible lattice in the type-E7 minuscule representation

This file reads the rational extension of the integral `56`-dimensional minuscule representation
of the type-`E₇` Serre presentation, and the admissibility of its coordinate `ℤ`-lattice for the
Serre Kostant form, off the minuscule weight table `TauCeti.E7Minuscule.weightTable`, where they
are proved for an arbitrary table.

Thus the minuscule coordinate lattice is an admissible lattice for the explicit Serre-generator
Kostant form. Its weights span the full type-`E₇` character lattice by
`TauCeti.DynkinType.span_range_e7MinusculeWeight_eq_top`. These are the lattice inputs needed for
the full-weight type-`E₇` Chevalley--Demazure carrier in Layer 9 of the ReductiveGroups roadmap.

## Main declarations

* `TauCeti.E7Minuscule.rep`: the rational minuscule representation of the universal enveloping
  algebra.
* `TauCeti.E7Minuscule.isSl2Triple_rep_serreRootGenerator`: the represented generators at every
  simple node form an `sl₂` triple.
* `TauCeti.E7Minuscule.isNilpotent_rep_serreRootGenerator`: the simple-root generators act
  nilpotently.
* `TauCeti.E7Minuscule.rep_serreRootGenerator_inl_latticeBasis_eq_sum` and
  `TauCeti.E7Minuscule.rep_serreRootGenerator_inr_latticeBasis_eq_sum`: the represented root
  generators act on the lattice basis by the raising and lowering matrices.
* `TauCeti.E7Minuscule.lattice`: the coordinate `ℤ`-lattice in the rational module.
* `TauCeti.E7Minuscule.rep_kostantForm_mem_lattice`: the generic Kostant form preserves the
  lattice.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VI.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§13 and 26--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.
* The rational representation and admissibility results specialize
  `TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.MinusculeWeightTable`.
-/

public section

open scoped Matrix

namespace TauCeti.E7Minuscule

open TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The enveloping-algebra representation -/

/-- The rational minuscule representation extended to the universal enveloping algebra. -/
noncomputable def rep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ weightTable.cartanMatrix) →ₐ[ℚ]
      Module.End ℚ (Fin 56 → ℚ) :=
  weightTable.rep

/-- The rational minuscule representation is the representation of the minuscule weight
table. -/
theorem rep_def : rep = weightTable.rep :=
  (rfl)

/-- Every represented positive or negative Serre root generator acts nilpotently. -/
theorem isNilpotent_rep_serreRootGenerator (k : Fin 7 ⊕ Fin 7) :
    IsNilpotent (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.serreRootGenerator weightTable.cartanMatrix k))) :=
  weightTable.isNilpotent_rep_serreRootGenerator k

/-- The represented Cartan, positive, and negative Serre generators at every node form an `sl₂`
triple: each simple-coroot coordinate takes the value `-1` on some minuscule weight. -/
theorem isSl2Triple_rep_serreRootGenerator (i : Fin 7) :
    _root_.IsSl2Triple
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ (TauCeti.serreH ℚ weightTable.cartanMatrix i)))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix (.inl i))))
      (rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix (.inr i)))) := by
  obtain ⟨a, ha⟩ := exists_e7MinusculeWeight_apply_eq_neg_one i
  exact weightTable.isSl2Triple_rep_serreRootGenerator i
    ⟨a, by rw [weightTable_weight, ha]; decide⟩

/-! ## The admissible coordinate lattice -/

/-- The coordinate `ℤ`-lattice in the rational minuscule module. -/
noncomputable def lattice : Submodule ℤ (Fin 56 → ℚ) :=
  TauCeti.coordinateLattice (Fin 56)

/-- The minuscule lattice is the standard coordinate lattice. -/
theorem lattice_def : lattice = TauCeti.coordinateLattice (Fin 56) :=
  (rfl)

/-- The coordinate basis of the minuscule lattice. -/
noncomputable def latticeBasis : Module.Basis (Fin 56) ℤ lattice :=
  TauCeti.coordinateLatticeBasis (Fin 56)

/-- Coercing a lattice basis vector to the rational module gives the corresponding coordinate
vector. -/
@[simp]
theorem coe_latticeBasis (a : Fin 56) :
    ((latticeBasis a : lattice) : Fin 56 → ℚ) = Pi.single a 1 := by
  rw [← Pi.basisFun_apply, latticeBasis]
  exact TauCeti.coe_coordinateLatticeBasis (Fin 56) a

/-- Every minuscule lattice-basis vector is a Cartan weight vector with its minuscule weight. -/
theorem isCartanWeightVector_latticeBasis (a : Fin 56) :
    TauCeti.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (TauCeti.serreH ℚ weightTable.cartanMatrix) rep (e7MinusculeWeight a)
      ((latticeBasis a : lattice) : Fin 56 → ℚ) := by
  rw [coe_latticeBasis]
  simpa only [rep, weightTable_weight] using weightTable.isCartanWeightVector_single a

/-- A represented positive Serre root generator acts on the minuscule lattice basis by the
raising matrix. -/
theorem rep_serreRootGenerator_inl_latticeBasis_eq_sum (i : Fin 7) (s : Fin 56) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix (.inl i)))
        ((latticeBasis s : lattice) : Fin 56 → ℚ) =
      ∑ r, raisingMatrix i r s • ((latticeBasis r : lattice) : Fin 56 → ℚ) := by
  rw [rep_def, ← weightTable_raisingMatrix]
  simpa only [coe_latticeBasis, TauCeti.coe_coordinateLatticeBasis, Pi.basisFun_apply] using
    weightTable.rep_serreRootGenerator_inl_coordinateLatticeBasis_eq_sum i s

/-- A represented negative Serre root generator acts on the minuscule lattice basis by the
lowering matrix. -/
theorem rep_serreRootGenerator_inr_latticeBasis_eq_sum (i : Fin 7) (s : Fin 56) :
    rep (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (TauCeti.serreRootGenerator weightTable.cartanMatrix (.inr i)))
        ((latticeBasis s : lattice) : Fin 56 → ℚ) =
      ∑ r, loweringMatrix i r s • ((latticeBasis r : lattice) : Fin 56 → ℚ) := by
  rw [rep_def, ← weightTable_loweringMatrix]
  simpa only [coe_latticeBasis, TauCeti.coe_coordinateLatticeBasis, Pi.basisFun_apply] using
    weightTable.rep_serreRootGenerator_inr_coordinateLatticeBasis_eq_sum i s

/-- The minuscule coordinate lattice is stable under the generic Kostant form built from the
type-`E₇` Serre generators. This is the form consumed by the carrier and base-change APIs. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ weightTable.cartanMatrix))
    (hu : u ∈ TauCeti.UniversalEnvelopingAlgebra.kostantForm
      (TauCeti.serreRootGenerator weightTable.cartanMatrix)
      (TauCeti.serreH ℚ weightTable.cartanMatrix))
    (v : Fin 56 → ℚ) (hv : v ∈ lattice.toAddSubgroup) : rep u v ∈ lattice.toAddSubgroup :=
  weightTable.rep_kostantForm_mem_lattice u hu v hv

end TauCeti.E7Minuscule
