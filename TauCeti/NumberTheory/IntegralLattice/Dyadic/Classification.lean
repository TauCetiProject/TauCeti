/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
public import TauCeti.NumberTheory.Padics.BilinearForm.JordanGaussSum
import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Basic

/-!
# Classification of dyadic localizations of integral lattices

This file transfers the complete classification of symmetric bilinear forms over `ℤ_[2]`
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_partialOddity_eq` and
`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_stdAddChar_partialOddity_eq`) to the dyadic
localizations `L.localIntegralForm 2` and `M.localIntegralForm 2` of integral lattices.

## Main results

In `namespace TauCeti.IntegralLattice`:

* `localIntegralForm_two_equivalent_iff_partialOddity_eq`: `ZMod 8` partial-residue
  classification of dyadic localizations of integral lattices.
* `localIntegralForm_two_equivalent_iff_stdAddChar_partialOddity_eq`: Gauss-sum formulation
  obtained by applying `ZMod.stdAddChar`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **Classification of dyadic localizations of integral lattices (`ZMod 8` partial residue form).**
Let `L` and `M` be integral lattices with Jordan splittings `N` and `N'` of their dyadic
localizations `L.localIntegralForm 2` and `M.localIntegralForm 2`. Then `L.localIntegralForm 2`
and `M.localIntegralForm 2` are isometric if and only if their Jordan constituents have equal
ranks and parity types at every scale, and their partial residues
`LinearMap.BilinForm.IsJordanSplitting.partialOddity` agree modulo `8` at every scale `j` with
`N (j + 1)` of type II. -/
theorem localIntegralForm_two_equivalent_iff_partialOddity_eq
    (L : IntegralLattice V) (M : IntegralLattice W)
    {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)}
    {N' : ℕ → Submodule ℤ_[2] (M.LocalCarrier 2)}
    (hN : (L.localIntegralForm 2).IsJordanSplitting 2 N)
    (hN' : (M.localIntegralForm 2).IsJordanSplitting 2 N') :
    (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ L.localIntegralForm 2 v v) ↔
        ∀ v ∈ N' i, 2 * 2 ^ i ∣ M.localIntegralForm 2 v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ L.localIntegralForm 2 v v) →
        hN.partialOddity (L.isSymm_localIntegralForm 2) j =
          hN'.partialOddity (M.isSymm_localIntegralForm 2) j :=
  hN.equivalent_iff_partialOddity_eq hN'
    (L.isSymm_localIntegralForm 2) (M.isSymm_localIntegralForm 2)

/-- **Classification of dyadic localizations of integral lattices (Gauss-sum form).** Obtained from
`TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_partialOddity_eq` by applying the
standard additive character `ZMod.stdAddChar`. -/
theorem localIntegralForm_two_equivalent_iff_stdAddChar_partialOddity_eq
    (L : IntegralLattice V) (M : IntegralLattice W)
    {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)}
    {N' : ℕ → Submodule ℤ_[2] (M.LocalCarrier 2)}
    (hN : (L.localIntegralForm 2).IsJordanSplitting 2 N)
    (hN' : (M.localIntegralForm 2).IsJordanSplitting 2 N') :
    (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ L.localIntegralForm 2 v v) ↔
        ∀ v ∈ N' i, 2 * 2 ^ i ∣ M.localIntegralForm 2 v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ L.localIntegralForm 2 v v) →
        stdAddChar (hN.partialOddity (L.isSymm_localIntegralForm 2) j) =
          stdAddChar (hN'.partialOddity (M.isSymm_localIntegralForm 2) j) :=
  hN.equivalent_iff_stdAddChar_partialOddity_eq hN'
    (L.isSymm_localIntegralForm 2) (M.isSymm_localIntegralForm 2)

end TauCeti.IntegralLattice
