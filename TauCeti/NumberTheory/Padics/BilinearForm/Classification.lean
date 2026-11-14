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
import TauCeti.Algebra.Group.AddChar
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Modular
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.LegendreSymbol.Complex
import TauCeti.NumberTheory.Padics.BilinearForm.JordanGaussSum
import TauCeti.NumberTheory.Padics.BilinearForm.SignWalking
import TauCeti.NumberTheory.Padics.BilinearForm.Unimodular
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SerreSigns -- for `TauCeti.isUnit_five_padicInt`

/-!
# Dyadic forms without adjacent Jordan constituents of type I

Let `B` be a symmetric form on a finite free `ℤ_[2]`-module with a Jordan splitting `N` with
respect to `2`, so that `B` is `2 ^ i` times a unimodular form `C i` on `N i`. Write
`ε i = χ₈(det C i)` for the sign of `N i`, `t i` for its oddity, the self-pairing of a
characteristic vector of `C i` modulo `8`, and `e(t) = exp (2πi t)`. The ranks, the types and,
whenever `N (j + 1)` is of type II, the quantities

```text
∏_{i ≤ j} ε i^{j + 1 - i} · e((∑_{i ≤ j} t i) / 8)
```

are isometry invariants of `B`
(`LinearMap.BilinForm.IsJordanSplitting.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent`). This
file proves that they classify `B` when no two adjacent constituents of `N` are of type I, that is,
when every compartment of the Conway–Sloane `2`-adic symbol has a single constituent
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_of_forall_even_or_even`). This extends the
classification of the forms all of whose constituents are of type II
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_forall_equivalent_restrict_of_even`), in
which the constituents themselves are invariants, to forms such as
`⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]` whose constituents are not.

Two adjacent constituents of type I can also exchange oddity by oddity fusion
(`LinearMap.BilinForm.IsJordanSplitting.exists_oddityFusion_succ`); compartments with more than one
constituent are not treated here.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_of_forall_even_or_even`:
  two forms with Jordan splittings, the first without adjacent constituents of type I, are isometric
  exactly when their constituents have the same ranks and types and the sign-oddity invariants
  agree.

## Implementation notes

The proof compares two Jordan splittings `N` and `N'` with the same invariants one index at a
time, changing `N'` by sign walking
(`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_odd_of_even`,
`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_even_of_odd`,
`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_add_two_of_odd_of_odd`) until its
constituent of index `k` is isometric to that of `N`. A unimodular constituent is determined by its
rank, type, sign and oddity
(`LinearMap.BilinForm.IsSymm.equivalent_iff_two_dvd_iff_and_χ₈_eq_and_eight_dvd`). Once the
constituents below `k` agree, the invariant of index `k`, when it is defined, determines
`ε k · e(t k / 8)`, so the signs and oddities of the constituents of index `k` agree, or differ by
a sign walk. If `N k` is of type II and `N (k + 1)` of type I, the sign of `N k` is not an
invariant, and a sign walk with `N (k + 1)` corrects it. If `N k` is of type I, then `N (k + 1)`
is of type II; when it is zero, either `N (k + 2)` is of type I and a sign walk across it is
available, or the invariant of index `k + 1` also fixes `t k`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* D. Allcock, I. Gal and A. Mark, *The Conway–Sloane calculus for 2-adic lattices*, §4.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup M'] [Module ℤ_[2] M']
  {B : BilinForm ℤ_[2] M} {B' : BilinForm ℤ_[2] M'} {N : ℕ → Submodule ℤ_[2] M}
  {N' : ℕ → Submodule ℤ_[2] M'}

/-! ### Signs and oddities of single constituents -/

/-- **Constituents with the same rank, type, sign and oddity are isometric.** For Jordan
splittings `N` of `B` and `N'` of `B'` with respect to `2`, with unimodular rescalings `C` and `C'`
of the constituents of index `i`, bases of the same size and characteristic vectors `w` and `w'`,
the constituents are isometric exactly when they have the same type, the same sign and the same
oddity. -/
theorem IsJordanSplitting.equivalent_restrict_iff (h : B.IsJordanSplitting 2 N)
    (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm) (hB' : B'.IsSymm) {i : ℕ}
    {C : BilinForm ℤ_[2] (N i)} {C' : BilinForm ℤ_[2] (N' i)}
    (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i)) (hC' : (2 : ℤ_[2]) ^ i • C' = B'.restrict (N' i))
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (d : Basis ι ℤ_[2] (N i)) (d' : Basis ι' ℤ_[2] (N' i))
    (hcard : Fintype.card ι = Fintype.card ι')
    {w : N i} {w' : N' i} (hw : C.IsCharacteristic w) (hw' : C'.IsCharacteristic w') :
    (B.restrict (N i)).Equivalent (B'.restrict (N' i)) ↔
      ((∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N' i, 2 * 2 ^ i ∣ B' x x) ∧
        χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) =
          χ₈ (PadicInt.toZModPow 3 (C'.toMatrix d').det) ∧
        PadicInt.toZModPow 3 (C w w) = PadicInt.toZModPow 3 (C' w' w') := by
  have h2 : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))
  have hCs : C.IsSymm := IsSymm.of_smul h2 (hC ▸ hB.restrict (N i))
  have hC's : C'.IsSymm := IsSymm.of_smul h2 (hC' ▸ hB'.restrict (N' i))
  set d'' := d'.reindex (Fintype.equivOfCardEq hcard).symm
  rw [← hC, ← hC', equivalent_smul_iff h2,
    hCs.equivalent_iff_two_dvd_iff_and_χ₈_eq_and_eight_dvd hC's d d''
      ((h.isModular i).isUnit_det_of_smul_eq h2 hC d) ((h'.isModular i).isUnit_det_of_smul_eq h2 hC'
        d'') hw hw',
    det_toMatrix_reindex, forall_dvd_iff_of_smul_eq (isRegular_iff_mem_nonZeroDivisors.mpr h2).left
      hC 2,
    forall_dvd_iff_of_smul_eq (isRegular_iff_mem_nonZeroDivisors.mpr h2).left hC' 2,
    Subtype.forall, Subtype.forall,
    PadicInt.eight_dvd_sub_iff_toZModPow_three_eq]
  rfl

/-- A constituent of type II has oddity `0`. -/
theorem IsJordanSplitting.toZModPow_three_apply_self_eq_zero (h : B.IsJordanSplitting 2 N)
    {i : ℕ} [Module.Free ℤ_[2] (N i)] {C : BilinForm ℤ_[2] (N i)}
    (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i)) {w : N i} (hw : C.IsCharacteristic w)
    (heven : ∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) : PadicInt.toZModPow 3 (C w w) = 0 := by
  have := (h.isModular i).isPerfPair_of_smul_eq
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))) hC
  rw [← map_zero (PadicInt.toZModPow 3), eq_comm, ← PadicInt.eight_dvd_sub_iff_toZModPow_three_eq,
    sub_zero]
  exact hw.eight_dvd_apply_self_of_forall_two_dvd ((forall_dvd_iff_of_smul_eq
    (isRegular_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0)))).left
      hC 2).mpr (Subtype.forall.mpr heven))

/-- **The constituent produced by a sign walk.** Let `N` and `N'` be Jordan splittings of `B` and
`B'`, with constituents of index `k` of the same type and opposite signs, and let `N''` be a
Jordan splitting of `B'` whose constituent of index `k` has the Gram determinant of `N' k` times
`5` up to squares and the oddity of `N k`. Then `N k` and `N'' k` are isometric. -/
private theorem IsJordanSplitting.equivalent_restrict_of_isSquare_five_mul
    [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M'] {N'' : ℕ → Submodule ℤ_[2] M'}
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N')
    (h'' : B'.IsJordanSplitting 2 N'') (hB : B.IsSymm) (hB' : B'.IsSymm) {k : ℕ}
    {C : BilinForm ℤ_[2] (N k)} {C' : BilinForm ℤ_[2] (N' k)}
    (hC : (2 : ℤ_[2]) ^ k • C = B.restrict (N k)) (hC' : (2 : ℤ_[2]) ^ k • C' = B'.restrict (N' k))
    {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (d : Basis ι ℤ_[2] (N k)) (d' : Basis ι' ℤ_[2] (N' k))
    (hcard : Fintype.card ι = Fintype.card ι') {w : N k} (hw : C.IsCharacteristic w)
    (htype : (∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) ↔ ∀ x ∈ N' k, 2 * 2 ^ k ∣ B' x x)
    (hχ : χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) =
      -χ₈ (PadicInt.toZModPow 3 (C'.toMatrix d').det))
    (hdet : ∀ (n : ℕ) (d₁ : Basis (Fin n) ℤ_[2] (N' k)) (d₂ : Basis (Fin n) ℤ_[2] (N'' k)),
      IsSquare (5 * ((B'.restrict (N' k)).toMatrix d₁).det *
        ((B'.restrict (N'' k)).toMatrix d₂).det))
    (hodd : ∀ (C'' : BilinForm ℤ_[2] (N'' k)) (w'' : N'' k),
      (2 : ℤ_[2]) ^ k • C'' = B'.restrict (N'' k) → C''.IsCharacteristic w'' →
        PadicInt.toZModPow 3 (C w w) = PadicInt.toZModPow 3 (C'' w'' w'')) :
    (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) := by
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have := h''.free k
  have := h''.finite k
  obtain ⟨C'', hC'', hC''p⟩ := isModular_def.mp (h''.isModular k)
  have hC''s : C''.IsSymm := IsSymm.of_smul (mem_nonZeroDivisors_of_ne_zero
    (pow_ne_zero k (two_ne_zero : (2 : ℤ_[2]) ≠ 0))) (hC'' ▸ hB'.restrict (N'' k))
  obtain ⟨w'', hw''⟩ := hC''s.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  -- Bases of `N' k` and `N'' k` of the same size `n`.
  set n := Fintype.card ι'
  have hfr : finrank ℤ_[2] (N'' k) = n :=
    (h'.finrank_eq h'' two_ne_zero PadicInt.not_isUnit_two k).symm.trans
      (finrank_eq_card_basis d')
  set d₁ := d'.reindex (Fintype.equivFin ι')
  set d₂ := Module.finBasisOfFinrankEq ℤ_[2] (N'' k) hfr
  -- The rescaled determinants differ by `5` up to squares.
  have hsq := hdet n d₁ d₂
  rw [← hC', ← hC'', _root_.map_smul, _root_.map_smul, Matrix.det_smul, Matrix.det_smul,
    Fintype.card_fin, det_toMatrix_reindex] at hsq
  have hsq' : IsSquare (5 * (C'.toMatrix d').det * (C''.toMatrix d₂).det) :=
    IsSquare.of_mul_right (pow_ne_zero 2 (pow_ne_zero n (pow_ne_zero k two_ne_zero)))
      (by convert hsq using 1; ring) ⟨_, sq _⟩
  have hu' : IsUnit (C'.toMatrix d').det :=
    (h'.isModular k).isUnit_det_of_smul_eq (pow_mem h2 k) hC' d'
  have hu'' : IsUnit (C''.toMatrix d₂).det := (h''.isModular k).isUnit_det_of_smul_eq (pow_mem h2 k)
    hC'' d₂
  have h5 := (PadicInt.isSquare_mul_iff_toZModPow_three_eq
    (TauCeti.isUnit_five_padicInt.mul hu') hu'').mp hsq'
  rw [map_mul, map_ofNat] at h5
  refine (h.equivalent_restrict_iff h'' hB hB' hC hC'' d d₂ (by simp [hcard, n]) hw hw'').mpr
    ⟨htype.trans ⟨h'.forall_two_mul_pow_dvd_of_equivalent h'' (.refl _) h2 dvd_rfl,
      h''.forall_two_mul_pow_dvd_of_equivalent h' (.refl _) h2 dvd_rfl⟩, ?_,
      hodd C'' w'' hC'' hw''⟩
  rw [hχ, ← h5, map_mul, show χ₈ (5 : ZMod (2 ^ 3)) = -1 by decide, neg_one_mul]

/-! ### Matching the constituents one index at a time -/

section PrefixCancellation

variable (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm)
    (hB' : B'.IsSymm)
    {α α' : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] [∀ i, Fintype (α' i)]
    [∀ i, DecidableEq (α' i)] (C : ∀ i, BilinForm ℤ_[2] (N i))
    (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i)) (d : ∀ i, Basis (α i) ℤ_[2] (N i))
    (w : ∀ i, N i) (hw : ∀ i, (C i).IsCharacteristic (w i)) (C' : ∀ i, BilinForm ℤ_[2] (N' i))
    (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i, (C' i).IsCharacteristic (w' i))
    (hcard : ∀ i, Fintype.card (α i) = Fintype.card (α' i))
    (hgauss : ∀ j, (∀ x ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B x x) →
      (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^
          (j + 1 - i)) * stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
        (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^
          (j + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i))))

include h h' hB hB' in
/-- Matching constituents below `k` cancel from every sign-oddity invariant of index `j ≥ k - 1`.
No restriction on adjacent constituent types is needed. -/
theorem IsJordanSplitting.prod_χ₈_pow_mul_stdAddChar_eq_of_forall_equivalent_restrict {k : ℕ}
    (hC : ∀ i < k, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (hC' : ∀ i < k, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (hw : ∀ i < k, (C i).IsCharacteristic (w i))
    (hw' : ∀ i < k, (C' i).IsCharacteristic (w' i))
    (hcard : ∀ i < k, Fintype.card (α i) = Fintype.card (α' i))
    (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i)))
    (j : ℕ) (hkj : k ≤ j + 1) (hgauss : (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C
      i).toMatrix (d i)).det) : ℤ) : ℂ) ^
          (j + 1 - i)) * stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
        (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^
          (j + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i)))) :
      ∏ i ∈ Finset.Ico k (j + 1),
          ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^ (j + 1 - i) *
            stdAddChar (PadicInt.toZModPow 3 (C i (w i) (w i))) =
        ∏ i ∈ Finset.Ico k (j + 1),
          ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^ (j + 1 - i) *
            stdAddChar (PadicInt.toZModPow 3 (C' i (w' i) (w' i))) := by
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have hδ' (i : ℕ) (hi : i < k) := ((h'.isModular i).isUnit_det_of_smul_eq (pow_mem h2 i) (hC' i hi)
    (d' i)).map (PadicInt.toZModPow 3)
  have hlow' (i : ℕ) (hi : i < k) := (h.equivalent_restrict_iff h' hB hB' (hC i hi) (hC' i hi) (d i)
    (d' i) (hcard i hi) (hw i hi) (hw' i hi)).mp (hlow i hi)
  have hprod := hgauss
  simp only [map_sum, AddChar.map_sum_eq_prod, ← Finset.prod_mul_distrib,
    ← Nat.range_succ_eq_Iic] at hprod
  rw [← Finset.prod_range_mul_prod_Ico _ hkj, ← Finset.prod_range_mul_prod_Ico _ hkj] at hprod
  refine mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i hi ↦ ?_)
    ((congrArg (· * _) (Finset.prod_congr rfl fun i hi ↦ ?_)).symm.trans hprod)
  · exact mul_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.mpr (MulChar.apply_ne_zero_iff.mpr (hδ' i
    (Finset.mem_range.mp hi)))))
      (by rw [stdAddChar_apply]; exact Circle.coe_ne_zero _)
  · rw [(hlow' i (Finset.mem_range.mp hi)).2.1, (hlow' i (Finset.mem_range.mp hi)).2.2]

include h h' hB hB' in
/-- After cancelling matching lower constituents, the invariant of index `k` compares the
sign times the oddity character of the constituents of index `k`. -/
theorem IsJordanSplitting.χ₈_mul_stdAddChar_eq_of_forall_equivalent_restrict {k : ℕ}
    (hC : ∀ i < k, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (hC' : ∀ i < k, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (hw : ∀ i < k, (C i).IsCharacteristic (w i))
    (hw' : ∀ i < k, (C' i).IsCharacteristic (w' i))
    (hcard : ∀ i < k, Fintype.card (α i) = Fintype.card (α' i))
    (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i)))
    (hgauss : (∏ i ∈ Finset.Iic k, ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ)
      ^
          (k + 1 - i)) * stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic k, C i (w i) (w i))) =
        (∏ i ∈ Finset.Iic k, ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^
          (k + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic k, C' i (w' i) (w' i)))) :
      ((χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) : ℤ) : ℂ) *
          stdAddChar (PadicInt.toZModPow 3 (C k (w k) (w k))) =
        ((χ₈ (PadicInt.toZModPow 3 ((C' k).toMatrix (d' k)).det) : ℤ) : ℂ) *
          stdAddChar (PadicInt.toZModPow 3 (C' k (w' k) (w' k))) := by
  simpa [Nat.Ico_succ_singleton] using
    h.prod_χ₈_pow_mul_stdAddChar_eq_of_forall_equivalent_restrict h' hB hB' C d w C' d' w' hC hC' hw
      hw' hcard hlow k (by omega) hgauss

include h h' hB hB' in
/-- If the next constituents vanish, the invariant of index `k + 1` determines the oddity
of index `k` after cancelling matching lower constituents. -/
theorem
  IsJordanSplitting.toZModPow_three_apply_self_eq_of_forall_equivalent_restrict_of_card_eq_zero
    {k : ℕ}
    (hC : ∀ i ≤ k, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (hC' : ∀ i ≤ k, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (hw : ∀ i < k, (C i).IsCharacteristic (w i))
    (hw' : ∀ i < k, (C' i).IsCharacteristic (w' i))
    (hcard : ∀ i ≤ k + 1, Fintype.card (α i) = Fintype.card (α' i))
    (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i)))
    (hgauss : (∏ i ∈ Finset.Iic (k + 1), ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ)
      : ℂ) ^
          (k + 1 + 1 - i)) * stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic (k + 1), C i (w i)
            (w i))) =
        (∏ i ∈ Finset.Iic (k + 1), ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) :
          ℂ) ^
          (k + 1 + 1 - i)) *
          stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic (k + 1), C' i (w' i) (w' i))))
    (hz : Fintype.card (α (k + 1)) = 0) :
      PadicInt.toZModPow 3 (C k (w k) (w k)) = PadicInt.toZModPow 3 (C' k (w' k) (w' k)) := by
  have hcancelled := h.prod_χ₈_pow_mul_stdAddChar_eq_of_forall_equivalent_restrict
    h' hB hB' C d w C' d' w' (fun i hi ↦ hC i (by omega))
      (fun i hi ↦ hC' i (by omega)) hw hw' (fun i hi ↦ hcard i (by omega))
      hlow (k + 1) (by omega) hgauss
  have : IsEmpty (α (k + 1)) := Fintype.card_eq_zero_iff.mp hz
  have : IsEmpty (α' (k + 1)) := Fintype.card_eq_zero_iff.mp
    ((hcard (k + 1) le_rfl).symm.trans hz)
  have hw0 : w (k + 1) = 0 := (d (k + 1)).ext_elem fun i ↦ isEmptyElim i
  have hw0' : w' (k + 1) = 0 := (d' (k + 1)).ext_elem fun i ↦ isEmptyElim i
  rw [Finset.prod_Ico_succ_top (by omega : k ≤ k + 1),
    Finset.prod_Ico_succ_top (by omega : k ≤ k + 1), Nat.Ico_succ_singleton,
    Finset.prod_singleton, Finset.prod_singleton,
    Matrix.det_eq_one_of_card_eq_zero hz,
    Matrix.det_eq_one_of_card_eq_zero ((hcard (k + 1) le_rfl).symm.trans hz), map_one, map_one,
    show k + 1 + 1 - k = 2 by omega] at hcancelled
  have hε (X : ZMod (2 ^ 3)) (hX : IsUnit X) : ((χ₈ X : ℤ) : ℂ) ^ 2 = 1 := by
    have hsq : χ₈ X ^ 2 = 1 := by
      rw [← MulChar.pow_apply' _ two_ne_zero, isQuadratic_χ₈.sq_eq_one, MulChar.one_apply hX]
    exact_mod_cast hsq
  have h2 : (2 : ℤ_[2]) ^ k ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k (two_ne_zero : (2 : ℤ_[2]) ≠ 0))
  rw [hε _ (((h.isModular k).isUnit_det_of_smul_eq h2 (hC k le_rfl) (d k)).map _),
    hε _ (((h'.isModular k).isUnit_det_of_smul_eq h2 (hC' k le_rfl) (d' k)).map _)] at hcancelled
  simp only [hw0, hw0', map_zero, one_mul,
    Int.cast_one, one_pow, AddChar.map_zero_eq_one, mul_one] at hcancelled
  exact ZMod.injective_stdAddChar hcancelled

variable
    (htype : ∀ i, (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N' i, 2 * 2 ^ i ∣ B' x x)

include h h' hB hB' hC hC' hw hw' hcard hgauss htype in
/-- An even constituent can be matched by at most one sign walk, preserving the lower prefix. -/
theorem IsJordanSplitting.exists_equivalent_restrict_of_even
    [Module.Finite ℤ_[2] M']
    {k : ℕ} (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i)))
    (hTk : ∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧ (∀ i < k, N'' i = N' i) ∧
      (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) := by
  have : Module.Free ℤ_[2] M' := .of_basis (h'.isInternal.collectedBasis d')
  have : Module.Free ℤ_[2] (N k) := .of_basis (d k)
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have hδ (i : ℕ) := ((h.isModular i).isUnit_det_of_smul_eq (pow_mem h2 i) (hC i)
    (d i)).map (PadicInt.toZModPow 3)
  have hδ' (i : ℕ) := ((h'.isModular i).isUnit_det_of_smul_eq (pow_mem h2 i) (hC' i)
    (d' i)).map (PadicInt.toZModPow 3)
  have h4 : ∀ X : ZMod (2 ^ 3), X ≠ X + 4 := by decide
  have hG0 := h.χ₈_mul_stdAddChar_eq_of_forall_equivalent_restrict h' hB hB' C d w C' d' w'
    (fun i _ ↦ hC i) (fun i _ ↦ hC' i) (fun i _ ↦ hw i) (fun i _ ↦ hw' i)
    (fun i _ ↦ hcard i) hlow
  -- Both oddities vanish.
  have hTk' := (htype k).mp hTk
  have ht : PadicInt.toZModPow 3 (C k (w k) (w k)) =
      PadicInt.toZModPow 3 (C' k (w' k) (w' k)) := by
    rw [h.toZModPow_three_apply_self_eq_zero (hC k) (hw k) hTk,
      h'.toZModPow_three_apply_self_eq_zero (hC' k) (hw' k) hTk']
  by_cases hχ : χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) =
      χ₈ (PadicInt.toZModPow 3 ((C' k).toMatrix (d' k)).det)
  · exact ⟨N', h', fun _ _ ↦ rfl, (h.equivalent_restrict_iff h' hB hB' (hC k) (hC' k) (d k) (d' k)
    (hcard k) (hw k) (hw' k)).mpr ⟨htype k, hχ, ht⟩⟩
  have hχ' : χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) =
      -χ₈ (PadicInt.toZModPow 3 ((C' k).toMatrix (d' k)).det) := by
    rcases (isQuadratic_χ₈ _).resolve_left (MulChar.apply_ne_zero_iff.mpr (hδ k)) with hX | hX <;>
      rcases (isQuadratic_χ₈ _).resolve_left (MulChar.apply_ne_zero_iff.mpr (hδ' k)) with
        hY | hY <;> simp_all
  by_cases hk1 : ∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x
  · -- The invariant of index `k` fixes the sign of `N k`.
    rcases χ₈_eq_and_eq_or_of_mul_stdAddChar_eq (hδ k) (hδ' k) (hG0 (hgauss k hk1)) with
      ⟨hχ'', -⟩ | ⟨-, ht'⟩
    · exact absurd hχ'' hχ
    · exact absurd (ht.symm.trans ht') (h4 _)
  -- Otherwise `N (k + 1)` is of type I, and a sign walk corrects the sign of `N' k`.
  have hne : N' k ≠ ⊥ := fun hbot ↦ by
    have h0 : Fintype.card (α' k) = 0 := by
      rw [← finrank_eq_card_basis (d' k), hbot, finrank_bot]
    exact hχ (by
      rw [Matrix.det_eq_one_of_card_eq_zero ((hcard k).trans h0),
        Matrix.det_eq_one_of_card_eq_zero h0, map_one, map_one])
  obtain ⟨N'', h'', hagree, hdk, -, -⟩ := h'.exists_signWalk_succ_of_even_of_odd hB' hTk' hne
    fun H ↦ hk1 ((htype (k + 1)).mpr H)
  refine ⟨N'', h'', fun i hi ↦ hagree i (by omega) (by omega),
    h.equivalent_restrict_of_isSquare_five_mul h' h'' hB hB' (hC k) (hC' k) (d k) (d' k)
      (hcard k) (hw k) (htype k) hχ' hdk fun C'' w'' hC'' hw'' ↦ ?_⟩
  rw [h.toZModPow_three_apply_self_eq_zero (hC k) (hw k) hTk,
    h''.toZModPow_three_apply_self_eq_zero hC'' hw''
    (h'.forall_two_mul_pow_dvd_of_equivalent h'' (.refl _) h2 dvd_rfl hTk')]

include h h' hB hB' hC hC' hw hw' hcard hgauss htype in
/-- An odd constituent followed by an even one can be matched while preserving the lower prefix. -/
theorem IsJordanSplitting.exists_equivalent_restrict_of_odd_of_even
    [Module.Finite ℤ_[2] M']
    {k : ℕ} (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i)))
    (hTk : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hk1 : ∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧ (∀ i < k, N'' i = N' i) ∧
      (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) := by
  have : Module.Free ℤ_[2] M' := .of_basis (h'.isInternal.collectedBasis d')
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have hδ (i : ℕ) := ((h.isModular i).isUnit_det_of_smul_eq (pow_mem h2 i) (hC i)
    (d i)).map (PadicInt.toZModPow 3)
  have hδ' (i : ℕ) := ((h'.isModular i).isUnit_det_of_smul_eq (pow_mem h2 i) (hC' i)
    (d' i)).map (PadicInt.toZModPow 3)
  have h4 : ∀ X : ZMod (2 ^ 3), X ≠ X + 4 := by decide
  have hG0 := h.χ₈_mul_stdAddChar_eq_of_forall_equivalent_restrict h' hB hB' C d w C' d' w'
    (fun i _ ↦ hC i) (fun i _ ↦ hC' i) (fun i _ ↦ hw i) (fun i _ ↦ hw' i)
    (fun i _ ↦ hcard i) hlow
  have hG1 := h.toZModPow_three_apply_self_eq_of_forall_equivalent_restrict_of_card_eq_zero
    h' hB hB' C d w C' d' w' (fun i _ ↦ hC i) (fun i _ ↦ hC' i)
    (fun i _ ↦ hw i) (fun i _ ↦ hw' i) (fun i _ ↦ hcard i) hlow
  rcases χ₈_eq_and_eq_or_of_mul_stdAddChar_eq (hδ k) (hδ' k) (hG0 (hgauss k hk1)) with ⟨hχ, ht⟩ |
    ⟨hχ, ht⟩
  · exact ⟨N', h', fun _ _ ↦ rfl, (h.equivalent_restrict_iff h' hB hB' (hC k) (hC' k) (d k) (d' k)
      (hcard k) (hw k) (hw' k)).mpr ⟨htype k, hχ, ht⟩⟩
  -- After a sign walk, the oddity of the new constituent of index `k` is that of `N k`.
  have hodd (N'' : ℕ → Submodule ℤ_[2] M')
      (h8 : ∀ (C₁ : BilinForm ℤ_[2] (N' k)) (C₂ : BilinForm ℤ_[2] (N'' k)) (w₁ : N' k)
        (w₂ : N'' k), (2 : ℤ_[2]) ^ k • C₁ = B'.restrict (N' k) →
        (2 : ℤ_[2]) ^ k • C₂ = B'.restrict (N'' k) → C₁.IsCharacteristic w₁ →
        C₂.IsCharacteristic w₂ → (8 : ℤ_[2]) ∣ C₂ w₂ w₂ - C₁ w₁ w₁ - 4)
      (C'' : BilinForm ℤ_[2] (N'' k)) (w'' : N'' k)
      (hC'' : (2 : ℤ_[2]) ^ k • C'' = B'.restrict (N'' k)) (hw'' : C''.IsCharacteristic w'') :
      PadicInt.toZModPow 3 (C k (w k) (w k)) = PadicInt.toZModPow 3 (C'' w'' w'') := by
    have := h8 (C' k) C'' (w' k) w'' (hC' k) hC'' (hw' k) hw''
    rw [sub_sub, PadicInt.eight_dvd_sub_iff_toZModPow_three_eq, map_add, map_ofNat] at this
    rw [ht, this]
  by_cases hz : Fintype.card (α' (k + 1)) = 0
  · by_cases hk2 : ∀ x ∈ N (k + 1 + 1), 2 * 2 ^ (k + 1 + 1) ∣ B x x
    · -- The invariant of index `k + 1` fixes the oddity of `N k`.
      exact absurd ((hG1 (hgauss (k + 1) hk2) ((hcard (k + 1)).trans hz)).symm.trans ht) (h4 _)
    -- Otherwise `N (k + 2)` is of type I, and a sign walk across the zero constituent is possible.
    obtain ⟨N'', h'', hagree, hdk, -, hok, -⟩ := h'.exists_signWalk_add_two_of_odd_of_odd hB'
      (fun H ↦ hTk ((htype k).mpr H)) fun H ↦ hk2 ((htype (k + 2)).mpr H)
    exact ⟨N'', h'', fun i hi ↦ hagree i (by omega) (by omega),
      h.equivalent_restrict_of_isSquare_five_mul h' h'' hB hB' (hC k) (hC' k) (d k) (d' k)
        (hcard k) (hw k) (htype k) hχ hdk (hodd N'' hok)⟩
  -- If `N' (k + 1)` is nonzero, a sign walk with it is possible.
  have hne : N' (k + 1) ≠ ⊥ := fun hbot ↦ hz (by
    rw [← finrank_eq_card_basis (d' (k + 1)), hbot, finrank_bot])
  obtain ⟨N'', h'', hagree, hdk, -, hok⟩ := h'.exists_signWalk_succ_of_odd_of_even hB'
    (fun H ↦ hTk ((htype k).mpr H)) ((htype (k + 1)).mp hk1) hne
  exact ⟨N'', h'', fun i hi ↦ hagree i (by omega) (by omega),
    h.equivalent_restrict_of_isSquare_five_mul h' h'' hB hB' (hC k) (hC' k) (d k) (d' k)
      (hcard k) (hw k) (htype k) hχ hdk (hodd N'' hok)⟩


include h h' hB hB' hC hC' hw hw' hcard hgauss htype in
/-- Match the next constituent when at least one of it and its successor is even. -/
private theorem IsJordanSplitting.exists_equivalent_restrict
    [Module.Finite ℤ_[2] M']
    (hadj : ∀ i, (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ∨ ∀ x ∈ N (i + 1), 2 * 2 ^ (i + 1) ∣ B x x)
    {k : ℕ} (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i))) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧ (∀ i < k, N'' i = N' i) ∧
      (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) := by
  by_cases hTk : ∀ x ∈ N k, 2 * 2 ^ k ∣ B x x
  · exact h.exists_equivalent_restrict_of_even h' hB hB' C hC d w hw C' hC' d' w' hw'
      hcard hgauss htype hlow hTk
  · exact h.exists_equivalent_restrict_of_odd_of_even h' hB hB' C hC d w hw C' hC' d' w' hw'
      hcard hgauss htype hlow hTk
      ((hadj k).resolve_left hTk)

end PrefixCancellation

/-! ### The classification -/

/-- **Classification of dyadic forms without adjacent Jordan constituents of type I.** Let `B` and
`B'` be symmetric forms on finite free `ℤ_[2]`-modules with Jordan splittings `N` and `N'` with
respect to `2`, such that of any two adjacent constituents `N i` and `N (i + 1)` at least one is
of type II, that is, even at its own scale. Let `C i` and `C' i` be the unimodular rescalings of
the constituents, with bases `d i`, `d' i` and characteristic vectors `w i`, `w' i`, and write
`ε i = χ₈(det C i)`, `t i = C i (w i) (w i)` and `e(t) = exp (2πi t)`. Then `B` and `B'` are
isometric exactly when

* the constituents `N i` and `N' i` have the same rank and the same type for every `i`, and
* `∏_{i ≤ j} ε i^{j + 1 - i} · e((∑_{i ≤ j} t i) / 8) = ∏_{i ≤ j} ε' i^{j + 1 - i} ·
  e((∑_{i ≤ j} t' i) / 8)` whenever `N (j + 1)` is of type II.

The constituents themselves need not be isometric: `⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]`
(`TauCeti.equivalent_toBilin'_unary_two_hyperbolic`), although `⟨1⟩` and `⟨5⟩` have different
signs. The invariants beyond the last nonzero constituent are needed as well: the forms
`!![0, 1; 1, 0] ⊥ ⟨2⟩` and `!![2, 1; 1, 2] ⊥ ⟨2⟩` have the same ranks, types and invariant of
index `1`, and their invariants of index `2` first separate them, through the signs `χ₈(-1) = 1`
and `χ₈(3) = -1` of their constituents of index `0`. -/
theorem IsJordanSplitting.equivalent_iff_of_forall_even_or_even [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm)
    (hB' : B'.IsSymm)
    (hadj : ∀ i, (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ∨ ∀ x ∈ N (i + 1), 2 * 2 ^ (i + 1) ∣ B x x)
    {α α' : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)] [∀ i, Fintype (α' i)]
    [∀ i, DecidableEq (α' i)] (C : ∀ i, BilinForm ℤ_[2] (N i))
    (hC : ∀ i, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i)) (d : ∀ i, Basis (α i) ℤ_[2] (N i))
    (w : ∀ i, N i) (hw : ∀ i, (C i).IsCharacteristic (w i)) (C' : ∀ i, BilinForm ℤ_[2] (N' i))
    (hC' : ∀ i, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (d' : ∀ i, Basis (α' i) ℤ_[2] (N' i)) (w' : ∀ i, N' i)
    (hw' : ∀ i, (C' i).IsCharacteristic (w' i)) :
    B.Equivalent B' ↔ (∀ i, finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i)) ∧
      (∀ i, (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N' i, 2 * 2 ^ i ∣ B' x x) ∧
      ∀ j, (∀ x ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B x x) →
        (∏ i ∈ Finset.Iic j, ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^
            (j + 1 - i)) *
            stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C i (w i) (w i))) =
          (∏ i ∈ Finset.Iic j,
              ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^ (j + 1 - i)) *
            stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic j, C' i (w' i) (w' i))) := by
  classical
  let : Module.Free ℤ_[2] M := .of_basis (h.isInternal.collectedBasis d)
  let : Module.Free ℤ_[2] M' := .of_basis (h'.isInternal.collectedBasis d')
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  refine ⟨fun hBB' ↦ ?_, fun ⟨hrank, htype, hgauss⟩ ↦ ?_⟩
  · obtain ⟨e⟩ := hBB'
    have hBB' : B.Equivalent B' := ⟨e⟩
    let : Module.Finite ℤ_[2] M' := Module.Finite.equiv e.toLinearEquiv
    exact ⟨h.finrank_eq_of_equivalent h' hBB' two_ne_zero PadicInt.not_isUnit_two,
    fun i ↦ ⟨h.forall_two_mul_pow_dvd_of_equivalent h' hBB' h2 dvd_rfl,
      h'.forall_two_mul_pow_dvd_of_equivalent h hBB'.symm h2 dvd_rfl⟩,
    fun j hj ↦ h.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h' hB hBB' hj C (fun i _ ↦ hC i)
      d w (fun i _ ↦ hw i) C' (fun i _ ↦ hC' i) d' w' (fun i _ ↦ hw' i)⟩
  · let (i : ℕ) : Module.Free ℤ_[2] (N' i) := .of_basis (d' i)
    let (i : ℕ) : Module.Finite ℤ_[2] (N' i) := Module.Finite.of_basis (d' i)
    let : Module.Finite ℤ_[2] M' := h.finite_of_finrank_eq h' hrank
    apply h.equivalent_of_forall_exists_equivalent_restrict h' two_ne_zero
      PadicInt.not_isUnit_two hrank
    intro k
    induction k with
    | zero => exact ⟨N', h', fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
    | succ k ih =>
      obtain ⟨N'', h'', hlow⟩ := ih
      choose C'' hC'' hC''p using fun i ↦ isModular_def.mp (h''.isModular i)
      choose w'' hw'' using fun i ↦ by
        have := h''.free i
        have := hC''p i
        exact (IsSymm.of_smul (mem_nonZeroDivisors_of_ne_zero
          (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0)))
          (hC'' i ▸ hB'.restrict (N'' i))).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
      let (i : ℕ) := h''.free i
      let (i : ℕ) := h''.finite i
      let d'' (i : ℕ) := Module.finBasis ℤ_[2] (N'' i)
      have htype'' (i : ℕ) : (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N'' i, 2 * 2 ^ i ∣ B' x x :=
        (htype i).trans ⟨h'.forall_two_mul_pow_dvd_of_equivalent h'' (.refl _) h2 dvd_rfl,
          h''.forall_two_mul_pow_dvd_of_equivalent h' (.refl _) h2 dvd_rfl⟩
      obtain ⟨N₁, h₁, hagree, hk⟩ := h.exists_equivalent_restrict h'' hB hB' C hC
        d w hw C'' hC'' d'' w'' hw'' (fun i ↦ by
          rw [Fintype.card_fin, ← finrank_eq_card_basis (d i), hrank i,
            h'.finrank_eq h'' two_ne_zero PadicInt.not_isUnit_two i])
        (fun j hj ↦ (hgauss j hj).trans
          (h'.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h'' hB' (.refl _)
            ((htype (j + 1)).mp hj) C' (fun i _ ↦ hC' i) d' w' (fun i _ ↦ hw' i) C''
            (fun i _ ↦ hC'' i) d'' w'' (fun i _ ↦ hw'' i))) htype'' hadj hlow
      refine ⟨N₁, h₁, fun i hi ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hagree i hi]
        exact hlow i hi
      · exact hk

end LinearMap.BilinForm
