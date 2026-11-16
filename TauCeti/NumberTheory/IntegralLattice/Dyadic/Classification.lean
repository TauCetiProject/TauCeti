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

Every nondegenerate integral lattice `L` admits a Jordan splitting of its dyadic localization
`L_2 = ℤ_2 ⊗[ℤ] L` (`TauCeti.IntegralLattice.exists_isJordanSplitting_localIntegralForm`). Unlike
at odd primes
(`TauCeti.IntegralLattice.localIntegralForm_equivalent_iff_forall_equivalent_restrict`), the
individual Jordan constituents of `L_2` are not local isometry invariants: sign walking and oddity
fusion move signs and oddities across adjacent scales.

This file transfers the complete classification of symmetric bilinear forms over `ℤ_[2]`
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq` and
`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_toZModPow_sum_add_eq`) to the dyadic
localizations of integral lattices. Given Jordan splittings `N` and `N'` of `L_2` and `M_2`, the
two localizations are integrally isometric if and only if:

1. `N i` and `N' i` have equal rank at every scale `i`;
2. `N i` and `N' i` have the same parity type (type I or type II) at every scale `i`;
3. at every scale `j` such that `N (j + 1)` is of type II (including `N (j + 1) = ⊥`), the partial
   Gauss-sum invariant (equivalently, its `ZMod 8` residue) agrees for `L_2` and `M_2`.

## Main results

* `TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`:
  classification of dyadic localizations of integral lattices via the partial Gauss-sum invariants
  of Jordan splittings.
* `TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_toZModPow_sum_add_eq`: the purely
  algebraic `ZMod 8` formulation of the classification.

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
`L.localIntegralForm 2` and `M.localIntegralForm 2`. For each `i`, let `C i` and `C' i` be the
unimodular rescalings of `N i` and `N' i`, with bases `d i`, `d' i` and characteristic vectors
`w i`, `w' i`. Then `L.localIntegralForm 2` and `M.localIntegralForm 2` are isometric if and only
if:

1. `N i` and `N' i` have the same rank for every `i`,
2. `N i` is of type II if and only if `N' i` is of type II for every `i`, and
3. for every `j` such that `N (j + 1)` is of type II (including `N (j + 1) = ⊥`), the partial
   Gauss-sum invariants agree:
   ```text
   ∏_{i ≤ j} χ₈(det C i)^{j + 1 - i} · e((∑_{i ≤ j} C i (w i) (w i)) / 8)
     = ∏_{i ≤ j} χ₈(det C' i)^{j + 1 - i} · e((∑_{i ≤ j} C' i (w' i) (w' i)) / 8).
   ``` -/
theorem localIntegralForm_two_equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq
    (L : IntegralLattice V) (M : IntegralLattice W)
    {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)} {N' : ℕ → Submodule ℤ_[2] (M.LocalCarrier 2)}
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
        (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^
            (j + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
        (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^
            (j + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i))) :=
  hN.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq hN'
    (L.isSymm_localIntegralForm 2) (M.isSymm_localIntegralForm 2)
    C hC d w hw C' hC' d' w' hw'

/-- **Classification of dyadic localizations of integral lattices (`ZMod 8` form).** Purely
algebraic formulation of
`TauCeti.IntegralLattice.localIntegralForm_two_equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`
without complex exponentials: `L.localIntegralForm 2` and `M.localIntegralForm 2` are isometric if
and only if their Jordan constituents have equal ranks and parity types at every scale, and for
every `j` such that `N (j + 1)` is of type II,
```text
∑_{i ≤ j} C i (w i) (w i) + (if ∏_{i ≤ j} χ₈(det C i)^{j + 1 - i} = -1 then 4 else 0)
```
agrees modulo `8` for `L` and `M`. -/
theorem localIntegralForm_two_equivalent_iff_toZModPow_sum_add_eq
    (L : IntegralLattice V) (M : IntegralLattice W)
    {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)} {N' : ℕ → Submodule ℤ_[2] (M.LocalCarrier 2)}
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
