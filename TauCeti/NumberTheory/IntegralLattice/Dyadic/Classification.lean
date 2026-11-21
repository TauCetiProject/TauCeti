/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
public import TauCeti.NumberTheory.IntegralLattice.Localization.Basic
import TauCeti.NumberTheory.Padics.BilinearForm.Classification.Basic

/-!
# Classification of dyadic localizations of integral lattices

This file transfers the complete classification of symmetric bilinear forms over `ℤ_[2]`
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq` and
`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_toZModPow_sum_add_eq`) to the dyadic
localizations `L.localIntegralForm 2` and `M.localIntegralForm 2` of integral lattices.

## Main results

In `namespace TauCeti.IntegralLattice`:

* `localIntegralForm_two_equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`: Gauss-sum
  classification of dyadic localizations of integral lattices.
* `localIntegralForm_two_equivalent_iff_toZModPow_sum_add_eq`: purely algebraic `ZMod 8`
  classification.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- **Classification of dyadic localizations of integral lattices (Gauss-sum form).** Let `L` and
`M` be integral lattices with Jordan splittings `N` and `N'` of their dyadic localizations
`L.localIntegralForm 2` and `M.localIntegralForm 2`, unimodular rescalings `C i` and `C' i`, bases
`d i` and `d' i`, and characteristic vectors `w i` and `w' i`. Then `L.localIntegralForm 2` and
`M.localIntegralForm 2` are isometric if and only if their Jordan constituents have equal ranks and
parity types at every scale, and the partial Gauss-sum invariants agree at every scale `j` with
`N (j + 1)` of type II. -/
theorem localIntegralForm_two_equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq
    (L : IntegralLattice V) (M : IntegralLattice W)
    {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)}
    {N' : ℕ → Submodule ℤ_[2] (M.LocalCarrier 2)}
    {α α' : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (α' i)] [∀ i, DecidableEq (α' i)]
    (hN : (L.localIntegralForm 2).IsJordanSplitting 2 N)
    (hN' : (M.localIntegralForm 2).IsJordanSplitting 2 N')
    (C : ∀ i, BilinForm ℤ_[2] (N i))
    (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = (L.localIntegralForm 2).restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i, (C i).IsCharacteristic (w i))
    (C' : ∀ i, BilinForm ℤ_[2] (N' i))
    (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = (M.localIntegralForm 2).restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i, (C' i).IsCharacteristic (w' i)) :
    (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ L.localIntegralForm 2 v v) ↔
        ∀ v ∈ N' i, 2 * 2 ^ i ∣ M.localIntegralForm 2 v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ L.localIntegralForm 2 v v) →
        (∏ i ∈ Finset.Iic j,
          ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^ (j + 1 - i)) *
            stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
        (∏ i ∈ Finset.Iic j,
          ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^ (j + 1 - i)) *
            stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i))) :=
  hN.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq hN'
    (L.isSymm_localIntegralForm 2) (M.isSymm_localIntegralForm 2)
    C hC d w hw C' hC' d' w' hw'

/-- **Classification of dyadic localizations of integral lattices (`ZMod 8` form).** Purely
algebraic formulation of
`TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`
without complex exponentials. -/
theorem localIntegralForm_two_equivalent_iff_toZModPow_sum_add_eq
    (L : IntegralLattice V) (M : IntegralLattice W)
    {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)}
    {N' : ℕ → Submodule ℤ_[2] (M.LocalCarrier 2)}
    {α α' : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (α' i)] [∀ i, DecidableEq (α' i)]
    (hN : (L.localIntegralForm 2).IsJordanSplitting 2 N)
    (hN' : (M.localIntegralForm 2).IsJordanSplitting 2 N')
    (C : ∀ i, BilinForm ℤ_[2] (N i))
    (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = (L.localIntegralForm 2).restrict (N i))
    (d : ∀ i, Basis (α i) ℤ_[2] (N i)) (w : ∀ i, N i)
    (hw : ∀ i, (C i).IsCharacteristic (w i))
    (C' : ∀ i, BilinForm ℤ_[2] (N' i))
    (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = (M.localIntegralForm 2).restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i, (C' i).IsCharacteristic (w' i)) :
    (L.localIntegralForm 2).Equivalent (M.localIntegralForm 2) ↔
      (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ v ∈ N i, 2 * 2 ^ i ∣ L.localIntegralForm 2 v v) ↔
        ∀ v ∈ N' i, 2 * 2 ^ i ∣ M.localIntegralForm 2 v v) ∧
      ∀ j, (∀ v ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ L.localIntegralForm 2 v v) →
        PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i)) +
          (if ∏ i ∈ Finset.Iic j,
              χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) ^ (j + 1 - i) = -1
            then 4 else 0) =
        PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i)) +
          (if ∏ i ∈ Finset.Iic j,
              χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) ^ (j + 1 - i) = -1
            then 4 else 0) :=
  hN.equivalent_iff_toZModPow_sum_add_eq hN'
    (L.isSymm_localIntegralForm 2) (M.isSymm_localIntegralForm 2)
    C hC d w hw C' hC' d' w' hw'

end TauCeti.IntegralLattice
