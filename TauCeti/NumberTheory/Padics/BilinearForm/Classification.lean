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
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_of_forall_or`). This extends the
classification of the forms all of whose constituents are of type II
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_forall_equivalent_restrict_of_even`), in
which the constituents themselves are invariants, to forms such as
`⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]` whose constituents are not.

Two adjacent constituents of type I can also exchange oddity by oddity fusion
(`LinearMap.BilinForm.IsJordanSplitting.exists_oddityFusion_succ`); compartments with more than one
constituent are not treated here.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_of_forall_or`: two forms with Jordan
  splittings, the first without adjacent constituents of type I, are isometric exactly when their
  constituents have the same ranks and types and the sign-oddity invariants agree.

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

/-- If `ε · e(s / 8) = ε' · e(t / 8)` for signs `ε = χ₈ x`, `ε' = χ₈ y` of units, then either the
signs and the residues agree, or both differ, the residues by `4`. -/
private theorem χ₈_eq_and_eq_or_of_mul_stdAddChar_eq {x y s t : ZMod (2 ^ 3)} (hx : x * x = 1)
    (hy : y * y = 1)
    (h : ((χ₈ x : ℤ) : ℂ) * stdAddChar s = ((χ₈ y : ℤ) : ℂ) * stdAddChar t) :
    χ₈ x = χ₈ y ∧ s = t ∨ χ₈ x = -χ₈ y ∧ s = t + 4 := by
  -- `e(4 / 8) = -1`.
  have h4 : (stdAddChar (4 : ZMod (2 ^ 3)) : ℂ) = -1 := by
    have hsq : (stdAddChar (4 : ZMod (2 ^ 3)) : ℂ) * stdAddChar (4 : ZMod (2 ^ 3)) = 1 := by
      rw [← AddChar.map_add_eq_mul, show (4 + 4 : ZMod (2 ^ 3)) = 0 by decide,
        AddChar.map_zero_eq_one]
    refine (mul_self_eq_one_iff.mp hsq).resolve_left fun h1 ↦ ?_
    exact absurd (ZMod.injective_stdAddChar (h1.trans (AddChar.map_zero_eq_one _).symm))
      (by decide)
  have hχ : ∀ z : ZMod (2 ^ 3), z * z = 1 → χ₈ z = 1 ∨ χ₈ z = -1 := by decide
  have hz (z : ZMod (2 ^ 3)) (hz : z * z = 1) :
      ((χ₈ z : ℤ) : ℂ) = stdAddChar (if χ₈ z = 1 then 0 else 4 : ZMod (2 ^ 3)) := by
    rcases hχ z hz with h | h <;> simp [h, h4]
  rw [hz x hx, hz y hy, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul] at h
  have h' := ZMod.injective_stdAddChar h
  clear h
  rcases hχ x hx with hx' | hx' <;> rcases hχ y hy with hy' | hy' <;>
    simp only [hx', hy', ite_true, ite_false, show (-1 : ℤ) ≠ 1 by decide] at h' ⊢ <;>
    revert s t <;> decide

/-- The rescaling of a constituent is even exactly when the constituent is of type II. -/
private theorem forall_two_dvd_iff_of_smul_eq {i : ℕ} {P : Submodule ℤ_[2] M}
    {C : BilinForm ℤ_[2] P} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict P) :
    (∀ x, (2 : ℤ_[2]) ∣ C x x) ↔ ∀ x ∈ P, 2 * 2 ^ i ∣ B x x := by
  have hBC (x : P) : B x x = 2 ^ i * C x x := by
    simpa using (LinearMap.congr_fun₂ hC x x).symm
  refine ⟨fun H x hx ↦ ?_, fun H x ↦ ?_⟩
  · have := mul_dvd_mul_left (2 ^ i) (H ⟨x, hx⟩)
    rwa [← hBC, mul_comm] at this
  · have := H x x.2
    rw [hBC, mul_comm 2] at this
    exact (mul_dvd_mul_iff_left (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).mp this

/-- **Constituents with the same rank, type, sign and oddity are isometric.** For Jordan
splittings `N` of `B` and `N'` of `B'` with respect to `2`, with unimodular rescalings `C` and `C'`
of the constituents of index `i`, bases of the same size and characteristic vectors `w` and `w'`,
the constituents are isometric exactly when they have the same type, the same sign and the same
oddity. -/
private theorem IsJordanSplitting.restrict_equivalent_iff (h : B.IsJordanSplitting 2 N)
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
  have hCp := (h.isModular i).isPerfPair_of_smul_eq h2 hC
  have hC'p := (h'.isModular i).isPerfPair_of_smul_eq h2 hC'
  have hCs : C.IsSymm := IsSymm.of_smul h2 (hC ▸ hB.restrict (N i))
  have hC's : C'.IsSymm := IsSymm.of_smul h2 (hC' ▸ hB'.restrict (N' i))
  set d'' := d'.reindex (Fintype.equivOfCardEq hcard).symm
  rw [← hC, ← hC', equivalent_smul_iff h2,
    hCs.equivalent_iff_two_dvd_iff_and_χ₈_eq_and_eight_dvd hC's d d''
      (d.isUnit_det_of_isPerfPair d C hCp) (d''.isUnit_det_of_isPerfPair d'' C' hC'p) hw hw',
    det_toMatrix_reindex, forall_two_dvd_iff_of_smul_eq hC, forall_two_dvd_iff_of_smul_eq hC',
    PadicInt.eight_dvd_sub_iff_toZModPow_three_eq]

/-- A constituent of type II has oddity `0`. -/
private theorem IsJordanSplitting.toZModPow_apply_self_eq_zero [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) {i : ℕ} {C : BilinForm ℤ_[2] (N i)}
    (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i)) {w : N i} (hw : C.IsCharacteristic w)
    (heven : ∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) : PadicInt.toZModPow 3 (C w w) = 0 := by
  have := h.free i
  have := (h.isModular i).isPerfPair_of_smul_eq
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))) hC
  rw [← map_zero (PadicInt.toZModPow 3), eq_comm, ← PadicInt.eight_dvd_sub_iff_toZModPow_three_eq,
    sub_zero]
  exact hw.eight_dvd_apply_self_of_forall_two_dvd ((forall_two_dvd_iff_of_smul_eq hC).mpr heven)

/-- A zero constituent has sign `1` and oddity `0`. -/
private theorem χ₈_det_toMatrix_eq_one_and_toZModPow_apply_self_eq_zero {P : Type*}
    [AddCommGroup P] [Module ℤ_[2] P] {C : BilinForm ℤ_[2] P} {ι : Type*} [Fintype ι]
    [DecidableEq ι] (d : Basis ι ℤ_[2] P) (hι : Fintype.card ι = 0) (w : P) :
    χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) = 1 ∧ PadicInt.toZModPow 3 (C w w) = 0 := by
  have := Fintype.card_eq_zero_iff.mp hι
  refine ⟨by rw [Matrix.det_isEmpty, map_one, map_one], ?_⟩
  rw [show w = 0 from d.ext_elem fun i ↦ isEmptyElim i]
  simp

/-- **The constituent produced by a sign walk.** Let `N` and `N'` be Jordan splittings of `B` and
`B'`, with constituents of index `k` of the same type and opposite signs, and let `N''` be a
Jordan splitting of `B'` whose constituent of index `k` has the Gram determinant of `N' k` times
`5` up to squares and the oddity of `N k`. Then `N k` and `N'' k` are isometric. -/
private theorem IsJordanSplitting.restrict_equivalent_of_isSquare_five_mul
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
    d'.isUnit_det_of_isPerfPair d' C' ((h'.isModular k).isPerfPair_of_smul_eq (pow_mem h2 k) hC')
  have hu'' : IsUnit (C''.toMatrix d₂).det := d₂.isUnit_det_of_isPerfPair d₂ C'' hC''p
  have h5 := (PadicInt.isSquare_mul_iff_toZModPow_three_eq
    (TauCeti.isUnit_five_padicInt.mul hu') hu'').mp hsq'
  rw [map_mul, map_ofNat] at h5
  have key : ∀ X : ZMod (2 ^ 3), X * X = 1 → χ₈ (5 * X) = -χ₈ X := by decide
  refine (h.restrict_equivalent_iff h'' hB hB' hC hC'' d d₂ (by simp [hcard, n]) hw hw'').mpr
    ⟨htype.trans ⟨h'.forall_two_mul_pow_dvd_of_equivalent h'' (.refl _) h2 dvd_rfl,
      h''.forall_two_mul_pow_dvd_of_equivalent h' (.refl _) h2 dvd_rfl⟩, ?_,
      hodd C'' w'' hC'' hw''⟩
  rw [hχ, ← h5, key _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hu')]

/-! ### Matching the constituents one index at a time -/

/-- **The inductive step.** Let `N` and `N'` be Jordan splittings of `B` and `B'` with the same
types and sign-oddity invariants and with bases of the same sizes, no two adjacent constituents of
`N` being of type I, whose constituents of index below `k` are isometric. Then a sign walk, if
needed, changes `N'` into a Jordan splitting `N''` of `B'` agreeing with `N'` below `k` whose
constituent of index `k` is isometric to `N k`. -/
private theorem IsJordanSplitting.exists_restrict_equivalent [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm)
    (hB' : B'.IsSymm)
    (hadj : ∀ i, (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ∨ ∀ x ∈ N (i + 1), 2 * 2 ^ (i + 1) ∣ B x x)
    (htype : ∀ i, (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N' i, 2 * 2 ^ i ∣ B' x x)
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
    {k : ℕ} (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i))) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧ (∀ i < k, N'' i = N' i) ∧
      (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) := by
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have hδ (i : ℕ) : PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det *
      PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det = 1 :=
    PadicInt.isUnit_iff_toZModPow_three_mul_self.mp
      ((d i).isUnit_det_of_isPerfPair (d i) (C i)
        ((h.isModular i).isPerfPair_of_smul_eq (pow_mem h2 i) (hC i)))
  have hδ' (i : ℕ) : PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det *
      PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det = 1 :=
    PadicInt.isUnit_iff_toZModPow_three_mul_self.mp
      ((d' i).isUnit_det_of_isPerfPair (d' i) (C' i)
        ((h'.isModular i).isPerfPair_of_smul_eq (pow_mem h2 i) (hC' i)))
  have hχ0 : ∀ X : ZMod (2 ^ 3), X * X = 1 → χ₈ X ≠ 0 := by decide
  have hχ2 : ∀ X : ZMod (2 ^ 3), X * X = 1 → χ₈ X ^ 2 = 1 := by decide
  have h4 : ∀ X : ZMod (2 ^ 3), X ≠ X + 4 := by decide
  have hequiv (hχ : χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) =
      χ₈ (PadicInt.toZModPow 3 ((C' k).toMatrix (d' k)).det))
      (ht : PadicInt.toZModPow 3 (C k (w k) (w k)) = PadicInt.toZModPow 3 (C' k (w' k) (w' k))) :
      ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧ (∀ i < k, N'' i = N' i) ∧
        (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) :=
    ⟨N', h', fun _ _ ↦ rfl, (h.restrict_equivalent_iff h' hB hB' (hC k) (hC' k) (d k) (d' k)
      (hcard k) (hw k) (hw' k)).mpr ⟨htype k, hχ, ht⟩⟩
  -- The constituents below `k` have the same signs and oddities, so they cancel from the
  -- sign-oddity invariants of index at least `k`.
  have hlow' (i : ℕ) (hi : i < k) := (h.restrict_equivalent_iff h' hB hB' (hC i) (hC' i) (d i)
    (d' i) (hcard i) (hw i) (hw' i)).mp (hlow i hi)
  have hcancel (j : ℕ) (hkj : k ≤ j + 1) (hj : ∀ x ∈ N (j + 1), 2 * 2 ^ (j + 1) ∣ B x x) :
      ∏ i ∈ Finset.Ico k (j + 1),
          ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix (d i)).det) : ℤ) : ℂ) ^ (j + 1 - i) *
            stdAddChar (PadicInt.toZModPow 3 (C i (w i) (w i))) =
        ∏ i ∈ Finset.Ico k (j + 1),
          ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix (d' i)).det) : ℤ) : ℂ) ^ (j + 1 - i) *
            stdAddChar (PadicInt.toZModPow 3 (C' i (w' i) (w' i))) := by
    have hprod := hgauss j hj
    simp only [map_sum, AddChar.map_sum_eq_prod, ← Finset.prod_mul_distrib,
      ← Nat.range_succ_eq_Iic] at hprod
    rw [← Finset.prod_range_mul_prod_Ico _ hkj, ← Finset.prod_range_mul_prod_Ico _ hkj] at hprod
    refine mul_left_cancel₀ (Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_)
      ((congrArg (· * _) (Finset.prod_congr rfl fun i hi ↦ ?_)).symm.trans hprod)
    · exact mul_ne_zero (pow_ne_zero _ (Int.cast_ne_zero.mpr (hχ0 _ (hδ' i))))
        (by rw [stdAddChar_apply]; exact Circle.coe_ne_zero _)
    · rw [(hlow' i (Finset.mem_range.mp hi)).2.1, (hlow' i (Finset.mem_range.mp hi)).2.2]
  -- The invariant of index `k`.
  have hG0 (hk1 : ∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) :
      ((χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) : ℤ) : ℂ) *
          stdAddChar (PadicInt.toZModPow 3 (C k (w k) (w k))) =
        ((χ₈ (PadicInt.toZModPow 3 ((C' k).toMatrix (d' k)).det) : ℤ) : ℂ) *
          stdAddChar (PadicInt.toZModPow 3 (C' k (w' k) (w' k))) := by
    simpa [Nat.Ico_succ_singleton] using hcancel k (by omega) hk1
  -- The invariant of index `k + 1`, when the constituents of index `k + 1` are zero.
  have hG1 (hk2 : ∀ x ∈ N (k + 1 + 1), 2 * 2 ^ (k + 1 + 1) ∣ B x x)
      (hz : Fintype.card (α (k + 1)) = 0) :
      PadicInt.toZModPow 3 (C k (w k) (w k)) = PadicInt.toZModPow 3 (C' k (w' k) (w' k)) := by
    have := hcancel (k + 1) (by omega) hk2
    rw [Finset.prod_Ico_succ_top (by omega : k ≤ k + 1),
      Finset.prod_Ico_succ_top (by omega : k ≤ k + 1), Nat.Ico_succ_singleton,
      Finset.prod_singleton, Finset.prod_singleton,
      (χ₈_det_toMatrix_eq_one_and_toZModPow_apply_self_eq_zero (d (k + 1)) hz
        (w (k + 1))).1,
      (χ₈_det_toMatrix_eq_one_and_toZModPow_apply_self_eq_zero (d (k + 1)) hz
        (w (k + 1))).2,
      (χ₈_det_toMatrix_eq_one_and_toZModPow_apply_self_eq_zero (d' (k + 1))
        ((hcard (k + 1)).symm.trans hz) (w' (k + 1))).1,
      (χ₈_det_toMatrix_eq_one_and_toZModPow_apply_self_eq_zero (d' (k + 1))
        ((hcard (k + 1)).symm.trans hz) (w' (k + 1))).2,
      show k + 1 + 1 - k = 2 by omega] at this
    have hε (X : ZMod (2 ^ 3)) (hX : X * X = 1) : ((χ₈ X : ℤ) : ℂ) ^ 2 = 1 := by
      exact_mod_cast hχ2 X hX
    simp only [hε _ (hδ k), hε _ (hδ' k), one_mul, Int.cast_one, one_pow, AddChar.map_zero_eq_one,
      mul_one] at this
    exact ZMod.injective_stdAddChar this
  by_cases hTk : ∀ x ∈ N k, 2 * 2 ^ k ∣ B x x
  · -- `N k` is of type II, so both oddities vanish.
    have hTk' := (htype k).mp hTk
    have ht : PadicInt.toZModPow 3 (C k (w k) (w k)) =
        PadicInt.toZModPow 3 (C' k (w' k) (w' k)) := by
      rw [h.toZModPow_apply_self_eq_zero (hC k) (hw k) hTk,
        h'.toZModPow_apply_self_eq_zero (hC' k) (hw' k) hTk']
    by_cases hχ : χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) =
        χ₈ (PadicInt.toZModPow 3 ((C' k).toMatrix (d' k)).det)
    · exact hequiv hχ ht
    have hχ' : χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) =
        -χ₈ (PadicInt.toZModPow 3 ((C' k).toMatrix (d' k)).det) := by
      have key : ∀ X Y : ZMod (2 ^ 3), X * X = 1 → Y * Y = 1 → χ₈ X ≠ χ₈ Y →
          χ₈ X = -χ₈ Y := by decide
      exact key _ _ (hδ k) (hδ' k) hχ
    by_cases hk1 : ∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x
    · -- The invariant of index `k` fixes the sign of `N k`.
      rcases χ₈_eq_and_eq_or_of_mul_stdAddChar_eq (hδ k) (hδ' k) (hG0 hk1) with
        ⟨hχ'', -⟩ | ⟨-, ht'⟩
      · exact absurd hχ'' hχ
      · exact absurd (ht.symm.trans ht') (h4 _)
    -- Otherwise `N (k + 1)` is of type I, and a sign walk corrects the sign of `N' k`.
    have hne : N' k ≠ ⊥ := fun hbot ↦ by
      have h0 : Fintype.card (α' k) = 0 := by
        rw [← finrank_eq_card_basis (d' k), hbot, finrank_bot]
      exact hχ (by
        rw [(χ₈_det_toMatrix_eq_one_and_toZModPow_apply_self_eq_zero (d k) ((hcard k).trans h0)
          (w k)).1, (χ₈_det_toMatrix_eq_one_and_toZModPow_apply_self_eq_zero (d' k) h0 (w' k)).1])
    obtain ⟨N'', h'', hagree, hdk, -, -⟩ := h'.exists_signWalk_succ_of_even_of_odd hB' hTk' hne
      fun H ↦ hk1 ((htype (k + 1)).mpr H)
    refine ⟨N'', h'', fun i hi ↦ hagree i (by omega) (by omega),
      h.restrict_equivalent_of_isSquare_five_mul h' h'' hB hB' (hC k) (hC' k) (d k) (d' k)
        (hcard k) (hw k) (htype k) hχ' hdk fun C'' w'' hC'' hw'' ↦ ?_⟩
    rw [h.toZModPow_apply_self_eq_zero (hC k) (hw k) hTk, h''.toZModPow_apply_self_eq_zero hC'' hw''
      (h'.forall_two_mul_pow_dvd_of_equivalent h'' (.refl _) h2 dvd_rfl hTk')]
  -- `N k` is of type I, so `N (k + 1)` is of type II, and the invariant of index `k` determines
  -- the sign and the oddity of `N k` up to a sign walk.
  have hk1 := (hadj k).resolve_left hTk
  rcases χ₈_eq_and_eq_or_of_mul_stdAddChar_eq (hδ k) (hδ' k) (hG0 hk1) with ⟨hχ, ht⟩ | ⟨hχ, ht⟩
  · exact hequiv hχ ht
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
      exact absurd ((hG1 hk2 ((hcard (k + 1)).trans hz)).symm.trans ht) (h4 _)
    -- Otherwise `N (k + 2)` is of type I, and a sign walk across the zero constituent is possible.
    obtain ⟨N'', h'', hagree, hdk, -, hok, -⟩ := h'.exists_signWalk_add_two_of_odd_of_odd hB'
      (fun H ↦ hTk ((htype k).mpr H)) fun H ↦ hk2 ((htype (k + 2)).mpr H)
    exact ⟨N'', h'', fun i hi ↦ hagree i (by omega) (by omega),
      h.restrict_equivalent_of_isSquare_five_mul h' h'' hB hB' (hC k) (hC' k) (d k) (d' k)
        (hcard k) (hw k) (htype k) hχ hdk (hodd N'' hok)⟩
  -- If `N' (k + 1)` is nonzero, a sign walk with it is possible.
  have hne : N' (k + 1) ≠ ⊥ := fun hbot ↦ hz (by
    rw [← finrank_eq_card_basis (d' (k + 1)), hbot, finrank_bot])
  obtain ⟨N'', h'', hagree, hdk, -, hok⟩ := h'.exists_signWalk_succ_of_odd_of_even hB'
    (fun H ↦ hTk ((htype k).mpr H)) ((htype (k + 1)).mp hk1) hne
  exact ⟨N'', h'', fun i hi ↦ hagree i (by omega) (by omega),
    h.restrict_equivalent_of_isSquare_five_mul h' h'' hB hB' (hC k) (hC' k) (d k) (d' k)
      (hcard k) (hw k) (htype k) hχ hdk (hodd N'' hok)⟩

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
index `1`, and only their invariants of index `2` separate them, through the signs `χ₈(-1) = 1`
and `χ₈(3) = -1` of their constituents of index `0`. -/
theorem IsJordanSplitting.equivalent_iff_of_forall_or [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] [Module.Free ℤ_[2] M'] [Module.Finite ℤ_[2] M']
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
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  refine ⟨fun hBB' ↦ ⟨h.finrank_eq_of_equivalent h' hBB' two_ne_zero PadicInt.not_isUnit_two,
    fun i ↦ ⟨h.forall_two_mul_pow_dvd_of_equivalent h' hBB' h2 dvd_rfl,
      h'.forall_two_mul_pow_dvd_of_equivalent h hBB'.symm h2 dvd_rfl⟩,
    fun j hj ↦ h.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h' hB hBB' hj C (fun i _ ↦ hC i)
      d w (fun i _ ↦ hw i) C' (fun i _ ↦ hC' i) d' w' (fun i _ ↦ hw' i)⟩,
    fun ⟨hrank, htype, hgauss⟩ ↦ ?_⟩
  -- Match the constituents of index below `k`, changing `N'` by sign walks.
  have key (k : ℕ) : ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧
      ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N'' i)) := by
    induction k with
    | zero => exact ⟨N', h', fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
    | succ k ih =>
      obtain ⟨N'', h'', hlow⟩ := ih
      -- Rescalings, bases and characteristic vectors of the constituents of `N''`.
      choose C'' hC'' hC''p using fun i ↦ isModular_def.mp (h''.isModular i)
      have hC''s (i : ℕ) : (C'' i).IsSymm := IsSymm.of_smul (mem_nonZeroDivisors_of_ne_zero
        (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))) (hC'' i ▸ hB'.restrict (N'' i))
      have hw'' (i : ℕ) : ∃ w, (C'' i).IsCharacteristic w := by
        have := h''.free i
        have := hC''p i
        exact (hC''s i).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
      choose w'' hw'' using hw''
      have hd'' (i : ℕ) : Nonempty (Basis (Fin (finrank ℤ_[2] (N'' i))) ℤ_[2] (N'' i)) := by
        have := h''.free i
        have := h''.finite i
        exact ⟨Module.finBasis ℤ_[2] (N'' i)⟩
      have htype'' (i : ℕ) : (∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) ↔ ∀ x ∈ N'' i, 2 * 2 ^ i ∣ B' x x :=
        (htype i).trans ⟨h'.forall_two_mul_pow_dvd_of_equivalent h'' (.refl _) h2 dvd_rfl,
          h''.forall_two_mul_pow_dvd_of_equivalent h' (.refl _) h2 dvd_rfl⟩
      obtain ⟨N₁, h₁, hagree, hk⟩ := h.exists_restrict_equivalent h'' hB hB' hadj htype'' C hC
        d w hw C'' hC'' (fun i ↦ (hd'' i).some) w'' hw'' (fun i ↦ by
          rw [Fintype.card_fin, ← finrank_eq_card_basis (d i), hrank i,
            h'.finrank_eq h'' two_ne_zero PadicInt.not_isUnit_two i])
        (fun j hj ↦ (hgauss j hj).trans
          (h'.prod_χ₈_pow_mul_stdAddChar_sum_eq_of_equivalent h'' hB' (.refl _)
            ((htype (j + 1)).mp hj) C' (fun i _ ↦ hC' i) d' w' (fun i _ ↦ hw' i) C''
            (fun i _ ↦ hC'' i) (fun i ↦ (hd'' i).some) w'' (fun i _ ↦ hw'' i))) hlow
      refine ⟨N₁, h₁, fun i hi ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hagree i hi]
        exact hlow i hi
      · exact hk
  -- Beyond the nonzero constituents of `N`, both splittings vanish.
  obtain ⟨K, hK⟩ := h.hasFiniteSupport.bddAbove
  obtain ⟨N'', h'', hlow⟩ := key (K + 1)
  refine equivalent_of_isInternal h.isInternal h''.isInternal h.apply_eq_zero h''.apply_eq_zero
    fun i ↦ ?_
  by_cases hi : i < K + 1
  · exact hlow i hi
  have hN : N i = ⊥ := by
    by_contra hne
    exact hi (Nat.lt_succ_of_le (hK hne))
  have hN'' : N'' i = ⊥ := by
    have := h''.finite i
    rw [← Submodule.finrank_eq_zero, ← h'.finrank_eq h'' two_ne_zero PadicInt.not_isUnit_two i,
      ← hrank i, hN, finrank_bot]
  have := Submodule.subsingleton_iff_eq_bot.mpr hN
  have := Submodule.subsingleton_iff_eq_bot.mpr hN''
  exact ⟨⟨LinearEquiv.ofSubsingleton _ _, fun x y ↦ by
    rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
    simp⟩⟩

end LinearMap.BilinForm
