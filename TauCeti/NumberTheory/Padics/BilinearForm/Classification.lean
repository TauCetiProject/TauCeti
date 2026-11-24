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
import TauCeti.Algebra.Group.AddChar.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Modular
import TauCeti.LinearAlgebra.BilinearForm.Odd.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.LegendreSymbol.Complex
import TauCeti.NumberTheory.Padics.BilinearForm.JordanGaussSum
import TauCeti.NumberTheory.Padics.BilinearForm.Oddity.Fusion
import TauCeti.NumberTheory.Padics.BilinearForm.SignWalking
import TauCeti.NumberTheory.Padics.BilinearForm.Unimodular
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SerreSigns -- for `TauCeti.isUnit_five_padicInt`

/-!
# Classification of dyadic forms

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
file proves that they classify `B`
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`). This
extends the classification of the forms all of whose constituents are of type II
(`LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_forall_equivalent_restrict_of_even`), in
which the constituents themselves are invariants, to forms such as
`⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]` and `⟨1⟩ ⊥ ⟨14⟩ ≅ ⟨7⟩ ⊥ ⟨2⟩`, whose
constituents are not.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq`:
  two forms with Jordan splittings are isometric exactly when their constituents have the same
  ranks and types and the sign-oddity invariants agree.
* `LinearMap.BilinForm.IsJordanSplitting.exists_equivalent_restrict_of_even`,
  `LinearMap.BilinForm.IsJordanSplitting.exists_equivalent_restrict_of_odd_of_even` and
  `LinearMap.BilinForm.IsJordanSplitting.exists_equivalent_restrict_of_odd_of_odd`: the three
  steps of the proof, according to the types of `N k` and `N (k + 1)`.

## Implementation notes

The proof compares two Jordan splittings `N` and `N'` with the same invariants one index at a
time, changing `N'` by sign walking and oddity fusion until its constituent of index `k` is
isometric to that of `N`. A unimodular constituent is determined by its rank, type, sign and
oddity (`LinearMap.BilinForm.IsSymm.equivalent_iff_two_dvd_iff_and_χ₈_eq_and_eight_dvd`). Once the
constituents below `k` agree, the invariant of index `k`, when it is defined, determines
`ε k · e(t k / 8)`, so the signs and oddities of the constituents of index `k` agree, or differ by
a sign walk. If `N k` is of type II and `N (k + 1)` of type I, the sign of `N k` is not an
invariant, and a sign walk with `N (k + 1)` corrects it. If `N k` is of type I and `N (k + 1)` of
type II, then when `N (k + 1)` is zero either `N (k + 2)` is of type I and a sign walk across it is
available, or the invariant of index `k + 1` also fixes `t k`.

If `N k` and `N (k + 1)` are both of type I, they lie in one compartment of the Conway–Sloane
symbol. The move `⟨a, 2 b⟩ ≅ ⟨a + 2 b, 2 a b (a + 2 b)⟩` between them multiplies both signs by
`χ₈(a (a + 2 b))` and adds `2 b` and `2 a` to the two oddities, so it depends only on `a` and `b`
modulo `4`. The residues modulo `4` of the unit values of an odd unimodular form are read off its
rank, sign and oddity through an orthogonal basis `b`: in rank `1` only `t`, in rank `2` one or
both residues according to `t` modulo `4`, and from rank `3` on both residues, the second one
from `b 0 + b 1 + b 2` if needed. If `N (k + 2)` is of type I as well, at most two moves and one
sign walk across `N (k + 1)` give `N' k` any sign and oddity of its rank. Otherwise the invariant
of index `k + 1` compares `ε (k + 1) · e((t k + t (k + 1)) / 8)`, and a case analysis on residues
modulo `8` shows that at most two moves achieve every change of `N' k` it allows. For example, it
separates `⟨1⟩ ⊥ ⟨2⟩` and `⟨5⟩ ⊥ ⟨10⟩`, which have the same determinant class and total oddity,
through the signs `χ₈(1) = 1` and `χ₈(5) = -1` of their constituents of index `1`.

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
  have h2r : IsLeftRegular ((2 : ℤ_[2]) ^ i) := (isRegular_iff_mem_nonZeroDivisors.mpr h2).left
  have hCs : C.IsSymm := h2r.isSMulRegular.isSymm_smul_iff.mp (hC ▸ hB.restrict (N i))
  have hC's : C'.IsSymm := h2r.isSMulRegular.isSymm_smul_iff.mp (hC' ▸ hB'.restrict (N' i))
  set d'' := d'.reindex (Fintype.equivOfCardEq hcard).symm
  rw [← hC, ← hC', equivalent_smul_iff (isLeftRegular_iff_isRegular.mp h2r),
    hCs.equivalent_iff_two_dvd_iff_and_χ₈_eq_and_eight_dvd hC's d d''
      ((h.isModular i).isUnit_det_of_smul_eq h2 hC d) ((h'.isModular i).isUnit_det_of_smul_eq h2 hC'
        d'') hw hw',
    det_toMatrix_reindex, forall_dvd_iff_of_smul_eq h2r hC 2, forall_dvd_iff_of_smul_eq h2r hC' 2,
    Subtype.forall, Subtype.forall,
    PadicInt.eight_dvd_sub_iff_toZModPow_three_eq]
  simp only [restrict_apply, LinearMap.domRestrict_apply]

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
      hC 2).mpr fun x ↦ by
        simpa only [restrict_apply, LinearMap.domRestrict_apply] using heven x.val x.property)

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
  have hC''s : C''.IsSymm := (IsSMulRegular.of_ne_zero
    (pow_ne_zero k (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).isSymm_smul_iff.mp
      (hC'' ▸ hB'.restrict (N'' k))
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

/-! ### Unit values of odd unimodular forms modulo `4`

An odd unimodular form over `ℤ_[2]` of rank `n`, sign `ε` and oddity `t` has an orthogonal basis
whose self-pairings are units `d₀, …, d_{n-1}`, with `ε = χ₈(∏ dᵢ)` and `t ≡ ∑ dᵢ` modulo `8`. The
moves between adjacent constituents of type I depend only on the residues modulo `4` of the unit
values they use. This section records, as conditions on residues modulo `8`, which signs and
oddities occur in ranks `1` and `2`, which residues modulo `4` the unit values take, and how the
moves act on these data. -/

/-- The sign `ε` and the oddity `t` occur for an odd unimodular form over `ℤ_[2]` of rank `n`, up
to the parity condition `t ≡ n` modulo `2`: in rank `1` the oddity is the value `t` and the sign is
`χ₈ t`; in rank `2` the oddities `0` and `4` force the signs `1` and `-1`. -/
private def Realizable : ℕ → ℤ → ZMod (2 ^ 3) → Prop
  | 1, ε, t => ε = χ₈ t ∧ t * t = 1
  | 2, ε, t => t = 0 ∧ ε = 1 ∨ t = 4 ∧ ε = -1 ∨ (t = 2 ∨ t = 6) ∧ (ε = 1 ∨ ε = -1)
  | _, ε, _ => ε = 1 ∨ ε = -1

/-- An odd unimodular form over `ℤ_[2]` of rank `n`, sign `ε` and oddity `t` takes a unit value
congruent to `β` modulo `4`. In rank `1` this is `β ≡ t`; in rank `2` both residues occur when
`t ≡ 0` modulo `4`, and otherwise only `t / 2` or `t / 2 + 2` according to the sign; in any other
rank every unit residue occurs. -/
private def Represents : ℕ → ℤ → ZMod (2 ^ 3) → ZMod (2 ^ 3) → Prop
  | 1, ε, t, β => ε = χ₈ t ∧ t * t = 1 ∧ 2 * β = 2 * t
  | 2, ε, t, β => β * β = 1 ∧ (t = 0 ∧ ε = 1 ∨ t = 4 ∧ ε = -1 ∨ ε = 1 ∧ 2 * β = t ∨
      ε = -1 ∧ 2 * β = t + 4)
  | _, _, _, β => β * β = 1

/-- The factor `χ₈ (a (a + 2 b))` by which the move `⟨a, 2 b⟩ ≅ ⟨a + 2 b, 2 a b (a + 2 b)⟩`
changes the signs of both constituents: `-1` when `a ≡ b` modulo `4`, and `1` otherwise. -/
private def moveSign (a b : ZMod (2 ^ 3)) : ℤ := if 2 * a = 2 * b then -1 else 1

/-- The ranks `n` and oddities `t` for which every unit diagonal of an odd unimodular form has two
entries congruent modulo `4`: `n ≥ 3`, or `n = 2` and `t ≡ 2` modulo `4`. The rank `0`, which no
constituent of type I has, is included to keep the definition simple. -/
private def Flexible (n : ℕ) (t : ZMod (2 ^ 3)) : Prop := n ≠ 1 ∧ (n = 2 → t = 2 ∨ t = 6)

private theorem moveSign_comm (a b : ZMod (2 ^ 3)) : moveSign a b = moveSign b a := by
  unfold moveSign; revert a b; decide

private theorem moveSign_mul_self (a b : ZMod (2 ^ 3)) : moveSign a b * moveSign a b = 1 := by
  unfold moveSign; split_ifs <;> rfl

private theorem moveSign_mul_moveSign_add_two {a b : ZMod (2 ^ 3)} (ha : a * a = 1)
    (hb : b * b = 1) : moveSign a b * moveSign a (b + 2) = -1 := by
  unfold moveSign; revert a b; decide

private theorem eq_one_or_eq_neg_one_of_realizable :
    ∀ (n : ℕ) (ε : ℤ) (t : ZMod (2 ^ 3)), Realizable n ε t → ε = 1 ∨ ε = -1
  | 0, _, _, h => h
  | 1, _, t, h => by
    obtain ⟨rfl, h⟩ := h
    revert t; decide
  | 2, _, t, h => by
    simp only [Realizable] at h
    rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, h⟩ <;> simp_all
  | _ + 3, _, _, h => h

private theorem mul_self_eq_one_of_represents :
    ∀ (n : ℕ) (ε : ℤ) (t β : ZMod (2 ^ 3)), Represents n ε t β → β * β = 1
  | 0, _, _, _, hβ => hβ
  | 1, _, t, β, hβ => by
    obtain ⟨-, ht, hβ⟩ := hβ
    revert t β; decide
  | 2, _, _, _, hβ => hβ.1
  | _ + 3, _, _, _, hβ => hβ

private theorem exists_represents :
    ∀ (n : ℕ) (ε : ℤ) (t : ZMod (2 ^ 3)), Realizable n ε t → ∃ β, Represents n ε t β
  | 0, _, _, _ => ⟨1, (by decide : (1 : ZMod (2 ^ 3)) * 1 = 1)⟩
  | 1, _, t, h => ⟨t, h.1, h.2, rfl⟩
  | 2, ε, t, h => by
    rcases eq_one_or_eq_neg_one_of_realizable 2 ε t h with rfl | rfl <;>
      simp +decide only [Realizable, Represents, and_true, true_and, and_false, false_and,
        or_false, false_or] at * <;> revert t <;> decide
  | _ + 3, _, _, _ => ⟨1, (by decide : (1 : ZMod (2 ^ 3)) * 1 = 1)⟩

/-- The rank, sign and oddity of a form with a unit diagonal `A` are realizable. -/
private theorem realizable_of_mul_self_eq_one :
    ∀ (n : ℕ) (A : Fin n → ZMod (2 ^ 3)), (∀ j, A j * A j = 1) →
      Realizable n (χ₈ (∏ j, A j)) (∑ j, A j)
  | 0, _, _ => .inl (by simp)
  | 1, A, hA => by simpa [Realizable] using hA 0
  | 2, A, hA => by
    simp only [Fin.prod_univ_two, Fin.sum_univ_two]
    have h0 := hA 0
    have h1 := hA 1
    generalize A 0 = x at *
    generalize A 1 = y at *
    revert x y; simp only [Realizable]; decide
  | _ + 3, _, hA => (isQuadratic_χ₈ _).resolve_left (MulChar.apply_ne_zero_iff.mpr
      (IsUnit.prod_univ_iff.mpr fun j ↦ IsUnit.of_mul_eq_one _ (hA j)))

/-- A residue represented by a form with unit diagonal `A` is that of an entry `A j`, or, in rank
at least `3`, that of `A 0 + A 1 + A 2`. -/
private theorem exists_two_mul_eq_of_represents :
    ∀ (n : ℕ) (A : Fin n → ZMod (2 ^ 3)) (β : ZMod (2 ^ 3)), 0 < n → (∀ j, A j * A j = 1) →
      Represents n (χ₈ (∏ j, A j)) (∑ j, A j) β → (∃ j, 2 * A j = 2 * β) ∨
        ∃ h : 3 ≤ n, 2 * (A ⟨0, by omega⟩ + A ⟨1, by omega⟩ + A ⟨2, by omega⟩) = 2 * β
  | 1, _, _, _, _, hβ => .inl ⟨0, by simpa [Represents] using hβ.2.2.symm⟩
  | 2, A, β, _, hA, hβ => by
    simp only [Fin.prod_univ_two, Fin.sum_univ_two, Fin.exists_fin_two] at hβ ⊢
    have h0 := hA 0
    have h1 := hA 1
    generalize A 0 = x at *
    generalize A 1 = y at *
    refine .inl ?_
    revert x y β; simp only [Represents]; decide
  | n + 3, A, β, _, hA, hβ => by
    have key : ∀ x y z b : ZMod (2 ^ 3), x * x = 1 → y * y = 1 → z * z = 1 → b * b = 1 →
        2 * x = 2 * b ∨ 2 * y = 2 * b ∨ 2 * z = 2 * b ∨ 2 * (x + y + z) = 2 * b := by
      decide
    rcases key _ _ _ β (hA _) (hA _) (hA _) hβ with h | h | h | h
    · exact .inl ⟨_, h⟩
    · exact .inl ⟨_, h⟩
    · exact .inl ⟨_, h⟩
    · exact .inr ⟨by omega, h⟩

/-- After a move with a partner of residue `β`, the residue `α + 2` is represented. -/
private theorem represents_move_add_two :
    ∀ (n : ℕ) (ε : ℤ) (t α β : ZMod (2 ^ 3)), (ε = 1 ∨ ε = -1) → Represents n ε t α →
      β * β = 1 → Represents n (ε * moveSign α β) (t + 2 * β) (α + 2)
  | 0, _, _, α, _, _, hα, _ => by simp only [Represents] at *; revert α; decide
  | 1, _, t, α, β, hε, hα, hβ => by
    rcases hε with rfl | rfl <;> simp only [Represents, moveSign] at * <;> revert t α β <;>
      decide
  | 2, _, t, α, β, hε, hα, hβ => by
    rcases hε with rfl | rfl <;> simp only [Represents, moveSign] at * <;> revert t α β <;>
      decide
  | _ + 3, _, _, α, _, _, hα, _ => by simp only [Represents] at *; revert α; decide

/-- For a flexible form, a move keeps the residue `α` of the vector it used represented. -/
private theorem represents_move_of_flexible :
    ∀ (n : ℕ) (ε : ℤ) (t α β : ZMod (2 ^ 3)), (ε = 1 ∨ ε = -1) → Flexible n t →
      Represents n ε t α → β * β = 1 → Represents n (ε * moveSign α β) (t + 2 * β) α
  | 0, _, _, _, _, _, _, hα, _ => hα
  | 1, _, _, _, _, _, h, _, _ => absurd rfl h.1
  | 2, _, t, α, β, hε, h, hα, hβ => by
    have ht := h.2 rfl
    clear h
    rcases hε with rfl | rfl <;> simp only [Represents, moveSign] at * <;> revert t α β <;>
      decide
  | _ + 3, _, _, _, _, _, _, hα, _ => hα

/-- If both signs occur with the oddity `t`, the form is flexible. -/
private theorem flexible_of_realizable_neg :
    ∀ (n : ℕ) (ε : ℤ) (t : ZMod (2 ^ 3)), Realizable n ε t → Realizable n (-ε) t → Flexible n t
  | 0, _, _, _, _ => ⟨by decide, fun h ↦ absurd h (by decide)⟩
  | 1, _, t, h, h' => by
    obtain ⟨rfl, ht⟩ := h
    obtain ⟨h', -⟩ := h'
    exfalso
    revert t; decide
  | 2, ε, t, h, h' => by
    refine ⟨by decide, fun _ ↦ ?_⟩
    rcases eq_one_or_eq_neg_one_of_realizable 2 ε t h with rfl | rfl <;>
      simp only [Realizable] at * <;> revert t <;> decide
  | _ + 3, _, _, _, _ => ⟨by omega, by omega⟩

/-- If the sign `ε` occurs with the oddities `t` and `t + 4`, the form is flexible. -/
private theorem flexible_of_realizable_add_four :
    ∀ (n : ℕ) (ε : ℤ) (t : ZMod (2 ^ 3)), Realizable n ε t → Realizable n ε (t + 4) →
      Flexible n t
  | 0, _, _, _, _ => ⟨by decide, fun h ↦ absurd h (by decide)⟩
  | 1, _, t, h, h' => by
    obtain ⟨rfl, ht⟩ := h
    obtain ⟨h', -⟩ := h'
    exfalso
    revert t; decide
  | 2, ε, t, h, h' => by
    refine ⟨by decide, fun _ ↦ ?_⟩
    rcases eq_one_or_eq_neg_one_of_realizable 2 ε t h with rfl | rfl <;>
      simp only [Realizable] at * <;> revert t <;> decide
  | _ + 3, _, _, _, _ => ⟨by omega, by omega⟩

/-- Two forms of the same rank whose sign-oddity characters `η · e(u / 8)` differ by `e(4 / 8)`
are flexible. -/
private theorem flexible_of_realizable_of_eq :
    ∀ (m : ℕ) (η η' : ℤ) (u u' : ZMod (2 ^ 3)), Realizable m η u → Realizable m η' u' →
      (η' = η ∧ u' + 4 = u ∨ η' = -η ∧ u' = u) → Flexible m u
  | 0, _, _, _, _, _, _, _ => ⟨by decide, fun h ↦ absurd h (by decide)⟩
  | 1, _, _, u, u', h, h', hinv => by
    obtain ⟨rfl, hu⟩ := h
    obtain ⟨rfl, hu'⟩ := h'
    exfalso
    revert u u'; decide
  | 2, η, η', u, u', h, h', hinv => by
    refine ⟨by decide, fun _ ↦ ?_⟩
    rcases eq_one_or_eq_neg_one_of_realizable 2 η u h with rfl | rfl <;>
      rcases eq_one_or_eq_neg_one_of_realizable 2 η' u' h' with rfl | rfl <;>
      simp +decide only [Realizable, and_true, true_and, and_false, false_and, or_false,
        false_or] at * <;> revert u u' <;> decide
  | _ + 3, _, _, _, _, _, _, _ => ⟨by omega, by omega⟩

/-- If the sign-oddity characters `η · e(u / 8)` of two forms of the same rank differ by
`e(2 β / 8)` for a unit `β`, then the first form represents the residue `β`. -/
private theorem represents_of_realizable_of_eq :
    ∀ (m : ℕ) (η η' : ℤ) (u u' β : ZMod (2 ^ 3)), Realizable m η u → Realizable m η' u' →
      β * β = 1 → (η' = η ∧ u' + 2 * β = u ∨ η' = -η ∧ u' + 2 * β = u + 4) →
        Represents m η u β
  | 0, _, _, _, _, _, _, _, hβ, _ => hβ
  | 1, _, _, u, u', β, h, h', hβ, hinv => by
    obtain ⟨rfl, hu⟩ := h
    obtain ⟨rfl, hu'⟩ := h'
    simp only [Represents]
    revert u u' β; decide
  | 2, η, η', u, u', β, h, h', hβ, hinv => by
    rcases eq_one_or_eq_neg_one_of_realizable 2 η u h with rfl | rfl <;>
      rcases eq_one_or_eq_neg_one_of_realizable 2 η' u' h' with rfl | rfl <;>
      simp +decide only [Realizable, Represents, and_true, true_and, and_false, false_and,
        or_false, false_or] at * <;> revert u u' β <;> decide
  | _ + 3, _, _, _, _, _, _, _, hβ, _ => hβ

/-- If `(ε, t)` and `(ε', t + 2 β)` are realizable in the same rank, a single move with a partner
of residue `β` turns the first into the second. -/
private theorem exists_represents_moveSign_eq :
    ∀ (n : ℕ) (ε ε' : ℤ) (t β : ZMod (2 ^ 3)), Realizable n ε t → Realizable n ε' (t + 2 * β) →
      β * β = 1 → ∃ α, Represents n ε t α ∧ ε * moveSign α β = ε'
  | 0, _, _, _, β, h, h', hβ => by
    rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp only [Represents, moveSign] <;>
      revert β <;> decide
  | 1, _, _, t, β, h, h', hβ => by
    obtain ⟨rfl, ht⟩ := h
    obtain ⟨rfl, -⟩ := h'
    simp only [Represents, moveSign]
    revert t β; decide
  | 2, ε, ε', t, β, h, h', hβ => by
    rcases eq_one_or_eq_neg_one_of_realizable 2 ε t h with rfl | rfl <;>
      rcases eq_one_or_eq_neg_one_of_realizable 2 ε' _ h' with rfl | rfl <;>
      simp +decide only [Realizable, Represents, moveSign, and_true, true_and, and_false,
        false_and, or_false, false_or] at * <;> revert t β <;> decide
  | _ + 3, _, _, _, β, h, h', hβ => by
    rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp only [Represents, moveSign] <;>
      revert β <;> decide

/-! ### Moves inside a compartment

Let `N k` and `N (k + 1)` be constituents of type I. Up to isometry, the constituent `N k` is
determined by its sign and oddity, recorded by `HasSignOddity` for every unimodular rescaling,
basis and characteristic vector. The moves `⟨a, 2 b⟩ ≅ ⟨a + 2 b, 2 a b (a + 2 b)⟩` of
`LinearMap.BilinForm.IsJordanSplitting.exists_oddityFusion_succ` and
`LinearMap.BilinForm.IsJordanSplitting.exists_signWalk_succ_of_odd_of_odd` multiply both signs by
`moveSign a b` and add `2 b` and `2 a` to the two oddities. Combining at most two of them, together
with sign walking across `N (k + 1)` when `N (k + 2)` is of type I, gives `N k` any sign and oddity
compatible with the invariants. -/

section Compartment

/-- The submodule `S` is `2 ^ i`-modular for `B`, and its unimodular rescaling has sign `ε` and
oddity `t`: for every unimodular rescaling `C` of `B` on `S`, every basis and every characteristic
vector `w`, the Gram determinant of `C` has `χ₈`-value `ε` and `C w w ≡ t` modulo `8`. -/
private def HasSignOddity (B : BilinForm ℤ_[2] M) (S : Submodule ℤ_[2] M) (i : ℕ) (ε : ℤ)
    (t : ZMod (2 ^ 3)) : Prop :=
  ∀ (C : BilinForm ℤ_[2] S) (n : ℕ) (d : Basis (Fin n) ℤ_[2] S) (w : S),
    (2 : ℤ_[2]) ^ i • C = B.restrict S → C.IsCharacteristic w →
      χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) = ε ∧ PadicInt.toZModPow 3 (C w w) = t

/-- The sign and oddity computed from one rescaling, basis and characteristic vector are those of
every other choice. -/
private theorem IsJordanSplitting.hasSignOddity (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {i : ℕ} {C : BilinForm ℤ_[2] (N i)} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : Basis ι ℤ_[2] (N i)) {w : N i}
    (hw : C.IsCharacteristic w) :
    HasSignOddity B (N i) i (χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det))
      (PadicInt.toZModPow 3 (C w w)) := by
  intro C' n d' w' hC' hw'
  obtain ⟨-, hχ, ht⟩ := (h.equivalent_restrict_iff h hB hB hC hC' d d' (by
    rw [← finrank_eq_card_basis d, finrank_eq_card_basis d']) hw hw').mp (.refl _)
  exact ⟨hχ.symm, ht.symm⟩

/-- Types are the same in two Jordan splittings of one form. -/
private theorem IsJordanSplitting.not_forall_two_mul_pow_dvd {P : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (hP : B.IsJordanSplitting 2 P) {i : ℕ}
    (hodd : ¬∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) : ¬∀ x ∈ P i, 2 * 2 ^ i ∣ B x x := fun H ↦
  hodd (hP.forall_two_mul_pow_dvd_of_equivalent h (.refl _)
    (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl H)

variable [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]

private theorem IsJordanSplitting.exists_hasSignOddity (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) (i : ℕ) : ∃ ε t, HasSignOddity B (N i) i ε t := by
  have := h.free i
  have := h.finite i
  obtain ⟨C, hC, hCp⟩ := isModular_def.mp (h.isModular i)
  have hCs : C.IsSymm := (IsSMulRegular.of_ne_zero
    (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).isSymm_smul_iff.mp (hC ▸ hB.restrict (N i))
  obtain ⟨w, hw⟩ := hCs.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  exact ⟨_, _, h.hasSignOddity hB hC (Module.finBasis ℤ_[2] (N i)) hw⟩

/-- **Sign and oddity after a move.** If passing from the splitting `N` to the splitting `P`
multiplies the Gram determinant of the constituent of index `i` by `c` up to squares and changes
the oddity by `r` modulo `8`, then the sign is multiplied by `χ₈ c` and `r` is added to the
oddity. -/
private theorem IsJordanSplitting.hasSignOddity_of_isSquare {P : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (hP : B.IsJordanSplitting 2 P) (hB : B.IsSymm) {i : ℕ}
    {ε : ℤ} {t : ZMod (2 ^ 3)} (hN : HasSignOddity B (N i) i ε t) {c r : ℤ_[2]} (hc : IsUnit c)
    (hdet : ∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N i)) (d' : Basis (Fin n) ℤ_[2] (P i)),
      IsSquare (c * ((B.restrict (N i)).toMatrix d).det * ((B.restrict (P i)).toMatrix d').det))
    (hodd : ∀ (C : BilinForm ℤ_[2] (N i)) (C' : BilinForm ℤ_[2] (P i)) (w : N i) (w' : P i),
      (2 : ℤ_[2]) ^ i • C = B.restrict (N i) → (2 : ℤ_[2]) ^ i • C' = B.restrict (P i) →
      C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - r) :
    HasSignOddity B (P i) i (χ₈ (PadicInt.toZModPow 3 c) * ε) (t + PadicInt.toZModPow 3 r) := by
  intro C' n d' w' hC' hw'
  have h2 : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  have := h.free i
  have := h.finite i
  obtain ⟨C, hC, hCp⟩ := isModular_def.mp (h.isModular i)
  have hCs : C.IsSymm := (IsSMulRegular.of_ne_zero
    (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).isSymm_smul_iff.mp (hC ▸ hB.restrict (N i))
  obtain ⟨w, hw⟩ := hCs.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  have hfr : finrank ℤ_[2] (N i) = n := by
    rw [h.finrank_eq hP two_ne_zero PadicInt.not_isUnit_two i, finrank_eq_card_basis d',
      Fintype.card_fin]
  set d := Module.finBasisOfFinrankEq ℤ_[2] (N i) hfr
  obtain ⟨hε, ht⟩ := hN C n d w hC hw
  have hu := (h.isModular i).isUnit_det_of_smul_eq h2 hC d
  have hu' := (hP.isModular i).isUnit_det_of_smul_eq h2 hC' d'
  refine ⟨?_, ?_⟩
  · have hsq := hdet n d d'
    rw [← hC, ← hC', _root_.map_smul, _root_.map_smul, Matrix.det_smul, Matrix.det_smul,
      Fintype.card_fin] at hsq
    have hsq' : IsSquare (c * (C.toMatrix d).det * (C'.toMatrix d').det) :=
      IsSquare.of_mul_right (pow_ne_zero 2 (pow_ne_zero n (pow_ne_zero i two_ne_zero)))
        (by convert hsq using 1; ring) ⟨_, sq _⟩
    rw [← (PadicInt.isSquare_mul_iff_toZModPow_three_eq (hc.mul hu) hu').mp (by
      simpa only [mul_assoc] using hsq'), map_mul, map_mul, hε]
  · have := hodd C C' w w' hC hC' hw hw'
    rw [sub_sub, PadicInt.eight_dvd_sub_iff_toZModPow_three_eq, map_add] at this
    rw [← this, ht]

/-- A constituent of type I with sign `ε` and oddity `t` has an orthogonal family of vectors with
unit self-pairings `2 ^ i a j` spanning it, with `ε = χ₈ (∏ j, a j)` and `t ≡ ∑ j, a j`. -/
private theorem IsJordanSplitting.exists_iIsOrtho_of_hasSignOddity (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {i : ℕ} {ε : ℤ} {t : ZMod (2 ^ 3)} (hN : HasSignOddity B (N i) i ε t)
    (hodd : ¬∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) :
    ∃ (v : Fin (finrank ℤ_[2] (N i)) → M) (a : Fin (finrank ℤ_[2] (N i)) → ℤ_[2]),
      (∀ j, v j ∈ N i) ∧ (∀ j, IsUnit (a j)) ∧ (∀ j, B (v j) (v j) = 2 ^ i * a j) ∧
      (∀ j l, j ≠ l → B (v j) (v l) = 0) ∧
      ε = χ₈ (∏ j, PadicInt.toZModPow 3 (a j)) ∧ t = ∑ j, PadicInt.toZModPow 3 (a j) := by
  have := h.free i
  have := h.finite i
  have h2 : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  obtain ⟨C, hC, -⟩ := isModular_def.mp (h.isModular i)
  have hBC (y z : N i) : B y z = 2 ^ i * C y z := by
    simpa using (LinearMap.congr_fun₂ hC y z).symm
  have hCs : C.IsSymm := (IsSMulRegular.of_ne_zero
    (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).isSymm_smul_iff.mp (hC ▸ hB.restrict (N i))
  obtain ⟨x, hx, a, ha, hxx⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd
  have hCx : C ⟨x, hx⟩ ⟨x, hx⟩ = a :=
    (mul_cancel_left_mem_nonZeroDivisors h2).mp ((hBC ⟨x, hx⟩ ⟨x, hx⟩).symm.trans hxx)
  let b₀ := Module.finBasis ℤ_[2] (N i)
  obtain ⟨c, hc, hcu⟩ := hCs.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self b₀
    ((h.isModular i).isUnit_det_of_smul_eq h2 hC b₀) ⟨_, hCx ▸ ha⟩
  obtain ⟨hε, ht⟩ := hN C _ c _ hC (hc.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
  refine ⟨fun j ↦ c j, fun j ↦ C (c j) (c j), fun j ↦ (c j).property, hcu, fun j ↦ hBC _ _,
    fun j l hjl ↦ by rw [hBC, iIsOrtho_def.mp hc j l hjl, mul_zero], ?_, ?_⟩
  · rw [← hε, hc.det_toMatrix, map_prod]
  · rw [← ht, hc.apply_sum_sum, map_sum]

/-- The sign and oddity of a constituent of type I are realizable in its rank, and the oddity is
the rank modulo `2`. -/
private theorem IsJordanSplitting.realizable_of_hasSignOddity (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {i : ℕ} {ε : ℤ} {t : ZMod (2 ^ 3)} (hN : HasSignOddity B (N i) i ε t)
    (hodd : ¬∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) :
    Realizable (finrank ℤ_[2] (N i)) ε t ∧ ∃ e, t = finrank ℤ_[2] (N i) + 2 * e := by
  obtain ⟨v, a, -, hau, -, -, rfl, rfl⟩ := h.exists_iIsOrtho_of_hasSignOddity hB hN hodd
  have hA (j) := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp (hau j)
  refine ⟨realizable_of_mul_self_eq_one _ _ hA, ?_⟩
  -- Each unit residue is `1 + 2 e j`.
  have hodd (x : ZMod (2 ^ 3)) (hx : x * x = 1) : ∃ e, x = 1 + 2 * e := by revert x; decide
  choose e he using fun j ↦ hodd _ (hA j)
  exact ⟨∑ j, e j, by simp [he, Finset.sum_add_distrib, Finset.mul_sum]⟩

/-- A constituent of type I takes a unit value `2 ^ i a` in each residue modulo `4` that
`Represents` allows. -/
private theorem IsJordanSplitting.exists_mem_of_represents (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {i : ℕ} {ε : ℤ} {t : ZMod (2 ^ 3)} (hN : HasSignOddity B (N i) i ε t)
    (hodd : ¬∀ x ∈ N i, 2 * 2 ^ i ∣ B x x) {β : ZMod (2 ^ 3)}
    (hβ : Represents (finrank ℤ_[2] (N i)) ε t β) :
    ∃ x ∈ N i, ∃ a : ℤ_[2], IsUnit a ∧ B x x = 2 ^ i * a ∧
      2 * PadicInt.toZModPow 3 a = 2 * β := by
  obtain ⟨v, a, hv, hau, hva, horth, rfl, rfl⟩ := h.exists_iIsOrtho_of_hasSignOddity hB hN hodd
  have hA (j) := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp (hau j)
  have hpos : 0 < finrank ℤ_[2] (N i) := by
    have := h.free i
    have := h.finite i
    obtain ⟨x, hx, b, hb, hxx⟩ := h.exists_mem_apply_self_eq_two_pow_mul hodd
    refine Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨x, hx⟩, fun h0 ↦ hb.ne_zero ?_⟩
    have : (2 : ℤ_[2]) ^ i * b = 0 := by
      simpa [show x = 0 by simpa using congrArg Subtype.val h0] using hxx.symm
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero i two_ne_zero)
  rcases exists_two_mul_eq_of_represents _ _ β hpos hA hβ with ⟨j, hj⟩ | ⟨h3, h3β⟩
  · exact ⟨v j, hv j, a j, hau j, hva j, hj⟩
  -- Otherwise the residue is that of `v 0 + v 1 + v 2`.
  set j₀ : Fin (finrank ℤ_[2] (N i)) := ⟨0, by omega⟩
  set j₁ : Fin (finrank ℤ_[2] (N i)) := ⟨1, by omega⟩
  set j₂ : Fin (finrank ℤ_[2] (N i)) := ⟨2, by omega⟩
  have h01 : j₀ ≠ j₁ := by simp [j₀, j₁, Fin.ext_iff]
  have h02 : j₀ ≠ j₂ := by simp [j₀, j₂, Fin.ext_iff]
  have h12 : j₁ ≠ j₂ := by simp [j₁, j₂, Fin.ext_iff]
  refine ⟨v j₀ + v j₁ + v j₂, add_mem (add_mem (hv j₀) (hv j₁)) (hv j₂), a j₀ + a j₁ + a j₂,
    ?_, ?_, by simpa [map_add] using h3β⟩
  · clear h3β
    rw [PadicInt.isUnit_iff_toZModPow_three_mul_self, map_add, map_add]
    have := hA j₀
    have := hA j₁
    have := hA j₂
    generalize PadicInt.toZModPow 3 (a j₀) = x at *
    generalize PadicInt.toZModPow 3 (a j₁) = y at *
    generalize PadicInt.toZModPow 3 (a j₂) = z at *
    revert x y z; decide
  · simp only [map_add, LinearMap.add_apply, hva, horth _ _ h01, horth _ _ h02, horth _ _ h12,
      horth _ _ h01.symm, horth _ _ h02.symm, horth _ _ h12.symm]
    ring

/-- **One move between adjacent constituents of type I.** For `x ∈ N k` and `y ∈ N (k + 1)` with
unit values `2 ^ k a` and `2 ^ (k + 1) b`, there is a Jordan splitting agreeing with `N` below `k`
in which both signs are multiplied by `moveSign a b`, and the oddities change by `2 b` and
`2 a`. -/
private theorem IsJordanSplitting.exists_move (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {k : ℕ} {ε η : ℤ} {t u : ZMod (2 ^ 3)} (hX : HasSignOddity B (N k) k ε t)
    (hY : HasSignOddity B (N (k + 1)) (k + 1) η u) {x y : M} (hx : x ∈ N k)
    (hy : y ∈ N (k + 1)) {a b : ℤ_[2]} (ha : IsUnit a) (hb : IsUnit b)
    (hxx : B x x = 2 ^ k * a) (hyy : B y y = 2 ^ (k + 1) * b) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k (ε * moveSign (PadicInt.toZModPow 3 a) (PadicInt.toZModPow 3 b))
        (t + 2 * PadicInt.toZModPow 3 b) ∧
      HasSignOddity B (P (k + 1)) (k + 1)
        (η * moveSign (PadicInt.toZModPow 3 a) (PadicInt.toZModPow 3 b))
        (u + 2 * PadicInt.toZModPow 3 a) := by
  have hA := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp ha
  have hB' := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hb
  have h2 : PadicInt.toZModPow 3 (2 : ℤ_[2]) = 2 := map_ofNat _ 2
  by_cases hab : 2 * PadicInt.toZModPow 3 a = 2 * PadicInt.toZModPow 3 b
  · -- Sign walking: both signs change.
    obtain ⟨P, hP, hagree, hdk, hdl, hok, hol⟩ := h.exists_signWalk_succ_of_odd_of_odd hB hx hy
      ha hb hxx hyy (PadicInt.four_dvd_iff_two_mul_toZModPow_three_eq_zero.mpr (by
        rw [map_sub, mul_sub, hab, sub_self]))
    have h3 : IsUnit (3 : ℤ_[2]) := by
      rw [PadicInt.isUnit_iff_toZModPow_three_mul_self, map_ofNat]; decide
    have hs : χ₈ (PadicInt.toZModPow 3 (3 : ℤ_[2])) =
        moveSign (PadicInt.toZModPow 3 a) (PadicInt.toZModPow 3 b) := by
      rw [moveSign, ite_eq_left hab, map_ofNat (PadicInt.toZModPow 3) 3]; decide
    refine ⟨P, hP, fun i hi ↦ hagree i (by omega) (by omega), ?_, ?_⟩
    · have := h.hasSignOddity_of_isSquare hP hB hX h3 hdk hok
      rwa [hs, mul_comm, map_mul, h2] at this
    · have := h.hasSignOddity_of_isSquare hP hB hY h3 hdl hol
      rwa [hs, mul_comm, map_mul, h2, ← hab] at this
  · -- Oddity fusion: both signs are kept.
    have key : ∀ x y : ZMod (2 ^ 3), x * x = 1 → y * y = 1 → ¬2 * x = 2 * y →
        2 * (x + y) = 0 ∧ -(2 * y) = 2 * x := by decide
    obtain ⟨h4, hneg⟩ := key _ _ hA hB' hab
    obtain ⟨P, hP, hagree, hdk, hdl, hok, hol⟩ := h.exists_oddityFusion_succ hB hx hy
      ha hb hxx hyy (PadicInt.four_dvd_iff_two_mul_toZModPow_three_eq_zero.mpr (by
        rw [map_add]; exact h4))
    have hs : χ₈ (PadicInt.toZModPow 3 (-1 : ℤ_[2])) =
        moveSign (PadicInt.toZModPow 3 a) (PadicInt.toZModPow 3 b) := by
      rw [moveSign, ite_eq_right hab, map_neg, map_one]; decide
    refine ⟨P, hP, fun i hi ↦ hagree i (by omega) (by omega), ?_, ?_⟩
    · have := h.hasSignOddity_of_isSquare hP hB hX isUnit_one.neg
        (fun n d d' ↦ by simpa using hdk n d d') hok
      rwa [hs, mul_comm, map_mul, h2] at this
    · have := h.hasSignOddity_of_isSquare hP hB hY isUnit_one.neg (r := -(2 * b))
        (fun n d d' ↦ by simpa using hdl n d d') (fun C C' w w' hC hC' hw hw' ↦ by
          simpa [sub_neg_eq_add] using hol C C' w w' hC hC' hw hw')
      rwa [hs, mul_comm, map_neg, map_mul, h2, hneg] at this

/-- One move between adjacent constituents of type I, with partners of prescribed residues
`α` and `β` modulo `4`. -/
private theorem IsJordanSplitting.exists_move_of_represents (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {k : ℕ} {ε η : ℤ} {t u : ZMod (2 ^ 3)} (hX : HasSignOddity B (N k) k ε t)
    (hY : HasSignOddity B (N (k + 1)) (k + 1) η u) (hoddX : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hoddY : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) {α β : ZMod (2 ^ 3)}
    (hα : Represents (finrank ℤ_[2] (N k)) ε t α)
    (hβ : Represents (finrank ℤ_[2] (N (k + 1))) η u β) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k (ε * moveSign α β) (t + 2 * β) ∧
      HasSignOddity B (P (k + 1)) (k + 1) (η * moveSign α β) (u + 2 * α) := by
  obtain ⟨x, hx, a, ha, hxx, h2a⟩ := h.exists_mem_of_represents hB hX hoddX hα
  obtain ⟨y, hy, b, hb, hyy, h2b⟩ := h.exists_mem_of_represents hB hY hoddY hβ
  obtain ⟨P, hP, hagree, hX', hY'⟩ := h.exists_move hB hX hY hx hy ha hb hxx hyy
  have hs : moveSign (PadicInt.toZModPow 3 a) (PadicInt.toZModPow 3 b) = moveSign α β := by
    simp only [moveSign, h2a, h2b]
  rw [hs, h2b] at hX'
  rw [hs, h2a] at hY'
  exact ⟨P, hP, hagree, hX', hY'⟩

/-- Two moves between adjacent constituents of type I, with partners of prescribed residues
modulo `4`. -/
private theorem IsJordanSplitting.exists_move_move (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {k : ℕ} {ε η ε' : ℤ} {t u t' : ZMod (2 ^ 3)}
    (hX : HasSignOddity B (N k) k ε t) (hY : HasSignOddity B (N (k + 1)) (k + 1) η u)
    (hoddX : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hoddY : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    {α β α' β' : ZMod (2 ^ 3)} (hα : Represents (finrank ℤ_[2] (N k)) ε t α)
    (hβ : Represents (finrank ℤ_[2] (N (k + 1))) η u β)
    (hα' : Represents (finrank ℤ_[2] (N k)) (ε * moveSign α β) (t + 2 * β) α')
    (hβ' : Represents (finrank ℤ_[2] (N (k + 1))) (η * moveSign α β) (u + 2 * α) β')
    (hε : ε * moveSign α β * moveSign α' β' = ε') (ht : t + 2 * β + 2 * β' = t') :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k ε' t' := by
  obtain ⟨P₁, h₁, hagree₁, hX₁, hY₁⟩ := h.exists_move_of_represents hB hX hY hoddX hoddY hα hβ
  have hr := h.finrank_eq h₁ two_ne_zero PadicInt.not_isUnit_two
  obtain ⟨P₂, h₂, hagree₂, hX₂, -⟩ := h₁.exists_move_of_represents hB hX₁ hY₁
    (h.not_forall_two_mul_pow_dvd h₁ hoddX) (h.not_forall_two_mul_pow_dvd h₁ hoddY)
    (by rwa [← hr]) (by rwa [← hr])
  refine ⟨P₂, h₂, fun i hi ↦ (hagree₂ i hi).trans (hagree₁ i hi), ?_⟩
  rwa [hε, ht] at hX₂

/-- **Changing the sign of `N k` alone**, when `N k` and `N (k + 1)` are of type I and the
opposite sign occurs with the same oddity. -/
private theorem IsJordanSplitting.exists_hasSignOddity_neg (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {k : ℕ} {ε : ℤ} {t : ZMod (2 ^ 3)} (hX : HasSignOddity B (N k) k ε t)
    (hoddX : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hoddY : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (hreal : Realizable (finrank ℤ_[2] (N k)) (-ε) t) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k (-ε) t := by
  obtain ⟨η, u, hY⟩ := h.exists_hasSignOddity hB (k + 1)
  have hRX := (h.realizable_of_hasSignOddity hB hX hoddX).1
  have hRY := (h.realizable_of_hasSignOddity hB hY hoddY).1
  obtain ⟨α, hα⟩ := exists_represents _ _ _ hRX
  obtain ⟨β, hβ⟩ := exists_represents _ _ _ hRY
  have hαu := mul_self_eq_one_of_represents _ _ _ _ hα
  have hβu := mul_self_eq_one_of_represents _ _ _ _ hβ
  -- The moves with partners `(α, β)` and `(α, β + 2)`.
  refine h.exists_move_move hB hX hY hoddX hoddY hα hβ
    (represents_move_of_flexible _ _ _ _ _ (eq_one_or_eq_neg_one_of_realizable _ _ _ hRX)
      (flexible_of_realizable_neg _ _ _ hRX hreal) hα hβu)
    (moveSign_comm α β ▸ represents_move_add_two _ _ _ _ _
      (eq_one_or_eq_neg_one_of_realizable _ _ _ hRY) hβ hαu)
    (by rw [mul_assoc, moveSign_mul_moveSign_add_two hαu hβu, mul_neg_one]) ?_
  have key : ∀ x : ZMod (2 ^ 3), x * x = 1 → 2 * x + 2 * (x + 2) = 0 := by decide
  rw [add_assoc, key β hβu, add_zero]

/-- **Adding `4` to the oddity of `N k`**, with either sign, when `N k` and `N (k + 1)` are of
type I and `N (k + 1)` is flexible. -/
private theorem IsJordanSplitting.exists_hasSignOddity_add_four (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {k : ℕ} {ε η : ℤ} {t u : ZMod (2 ^ 3)} (hX : HasSignOddity B (N k) k ε t)
    (hY : HasSignOddity B (N (k + 1)) (k + 1) η u)
    (hoddX : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hoddY : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (hflex : Flexible (finrank ℤ_[2] (N (k + 1))) u) {ε' : ℤ} (hε' : ε' = ε ∨ ε' = -ε)
    (hreal : Realizable (finrank ℤ_[2] (N k)) ε' (t + 4)) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k ε' (t + 4) := by
  have hRX := (h.realizable_of_hasSignOddity hB hX hoddX).1
  have hRY := (h.realizable_of_hasSignOddity hB hY hoddY).1
  obtain ⟨α, hα⟩ := exists_represents _ _ _ hRX
  obtain ⟨β, hβ⟩ := exists_represents _ _ _ hRY
  have hαu := mul_self_eq_one_of_represents _ _ _ _ hα
  have hβu := mul_self_eq_one_of_represents _ _ _ _ hβ
  have hβ' := moveSign_comm α β ▸ represents_move_of_flexible _ _ _ _ _
    (eq_one_or_eq_neg_one_of_realizable _ _ _ hRY) hflex hβ hαu
  have h4 : t + 2 * β + 2 * β = t + 4 := by
    have key : ∀ x : ZMod (2 ^ 3), x * x = 1 → 2 * x + 2 * x = 4 := by decide
    rw [add_assoc, key β hβu]
  rcases hε' with rfl | rfl
  · -- The moves with partners `(α, β)` and `(α, β)`.
    exact h.exists_move_move hB hX hY hoddX hoddY hα hβ
      (represents_move_of_flexible _ _ _ _ _ (eq_one_or_eq_neg_one_of_realizable _ _ _ hRX)
        (flexible_of_realizable_add_four _ _ _ hRX hreal) hα hβu) hβ'
      (by rw [mul_assoc, moveSign_mul_self, mul_one]) h4
  · -- The moves with partners `(α, β)` and `(α + 2, β)`.
    refine h.exists_move_move hB hX hY hoddX hoddY hα hβ
      (represents_move_add_two _ _ _ _ _ (eq_one_or_eq_neg_one_of_realizable _ _ _ hRX) hα hβu)
      hβ' ?_ h4
    rw [mul_assoc, moveSign_comm α β, moveSign_comm (α + 2) β,
      moveSign_mul_moveSign_add_two hβu hαu, mul_neg_one]

/-- With `N k` and `N (k + 2)` of type I, sign walking across `N (k + 1)` changes the sign of
`N k` and adds `4` to its oddity. -/
private theorem IsJordanSplitting.exists_hasSignOddity_neg_add_four (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {k : ℕ} {ε : ℤ} {t : ZMod (2 ^ 3)} (hX : HasSignOddity B (N k) k ε t)
    (hodd : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hodd' : ¬∀ x ∈ N (k + 2), 2 * 2 ^ (k + 2) ∣ B x x) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k (-ε) (t + 4) := by
  obtain ⟨P, hP, hagree, hdk, -, hok, -⟩ := h.exists_signWalk_add_two_of_odd_of_odd hB hodd hodd'
  refine ⟨P, hP, fun i hi ↦ hagree i (by omega) (by omega), ?_⟩
  have := h.hasSignOddity_of_isSquare hP hB hX TauCeti.isUnit_five_padicInt hdk hok
  rwa [map_ofNat (PadicInt.toZModPow 3) 5, map_ofNat (PadicInt.toZModPow 3) 4,
    show χ₈ (5 : ZMod (2 ^ 3)) = -1 by decide, neg_one_mul] at this

/-- With `N k` and `N (k + 1)` of type I, the constituent `N k` can be given either sign
compatible with its rank and oddity. -/
private theorem IsJordanSplitting.exists_hasSignOddity_of_eq (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {k : ℕ} {ε ε' : ℤ} {t : ZMod (2 ^ 3)} (hX : HasSignOddity B (N k) k ε t)
    (hoddX : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hoddY : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (hε' : ε' = ε ∨ ε' = -ε) (hreal : Realizable (finrank ℤ_[2] (N k)) ε' t) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k ε' t := by
  rcases hε' with rfl | rfl
  · exact ⟨N, h, fun _ _ ↦ rfl, hX⟩
  · exact h.exists_hasSignOddity_neg hB hX hoddX hoddY hreal

/-- With `N k`, `N (k + 1)` and `N (k + 2)` of type I, the constituent `N k` can be given any
sign and oddity realizable in its rank with an oddity of the same parity. -/
private theorem IsJordanSplitting.exists_hasSignOddity_of_odd_add_two
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {k : ℕ} {ε ε' : ℤ} {t t' : ZMod (2 ^ 3)}
    (hX : HasSignOddity B (N k) k ε t) (hoddX : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x)
    (hoddY : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (hodd2 : ¬∀ x ∈ N (k + 2), 2 * 2 ^ (k + 2) ∣ B x x)
    (hreal : Realizable (finrank ℤ_[2] (N k)) ε' t') {e : ZMod (2 ^ 3)} (he : t' = t + 2 * e) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k ε' t' := by
  -- First the case where the oddities differ by `0` or `4`.
  have key {P : ℕ → Submodule ℤ_[2] M} (hP : B.IsJordanSplitting 2 P) {ε₁ : ℤ}
      {t₁ : ZMod (2 ^ 3)} (hX₁ : HasSignOddity B (P k) k ε₁ t₁) (h₁ : t' = t₁ ∨ t' = t₁ + 4) :
      ∃ Q : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 Q ∧ (∀ i < k, Q i = P i) ∧
        HasSignOddity B (Q k) k ε' t' := by
    have hoddX₁ := h.not_forall_two_mul_pow_dvd hP hoddX
    have hoddY₁ := h.not_forall_two_mul_pow_dvd hP hoddY
    have hε₁ := eq_one_or_eq_neg_one_of_realizable _ _ _
      (hP.realizable_of_hasSignOddity hB hX₁ hoddX₁).1
    have hεε : ε' = ε₁ ∨ ε' = -ε₁ := by
      have := eq_one_or_eq_neg_one_of_realizable _ _ _ hreal
      omega
    rw [h.finrank_eq hP two_ne_zero PadicInt.not_isUnit_two k] at hreal
    rcases h₁ with rfl | rfl
    · exact hP.exists_hasSignOddity_of_eq hB hX₁ hoddX₁ hoddY₁ hεε hreal
    -- Sign walking across `N (k + 1)`, followed if necessary by a change of sign.
    obtain ⟨P₁, h₁, hagree₁, hX₂⟩ := hP.exists_hasSignOddity_neg_add_four hB hX₁ hoddX₁
      (h.not_forall_two_mul_pow_dvd hP hodd2)
    rcases hεε with rfl | rfl
    · obtain ⟨P₂, h₂, hagree₂, hX₃⟩ := h₁.exists_hasSignOddity_neg hB hX₂
        (hP.not_forall_two_mul_pow_dvd h₁ hoddX₁) (hP.not_forall_two_mul_pow_dvd h₁ hoddY₁)
        (by rwa [neg_neg, ← hP.finrank_eq h₁ two_ne_zero PadicInt.not_isUnit_two k])
      rw [neg_neg] at hX₃
      exact ⟨P₂, h₂, fun i hi ↦ (hagree₂ i hi).trans (hagree₁ i hi), hX₃⟩
    · exact ⟨P₁, h₁, hagree₁, hX₂⟩
  have hcases : ∀ x : ZMod (2 ^ 3), 2 * x = 0 ∨ 2 * x = 4 ∨
      ∀ γ : ZMod (2 ^ 3), γ * γ = 1 → 2 * x - 2 * γ = 0 ∨ 2 * x - 2 * γ = 4 := by decide
  rcases hcases e with h0 | h4 | hmove
  · exact key h hX (.inl (by rw [he, h0, add_zero]))
  · exact key h hX (.inr (by rw [he, h4]))
  -- Otherwise one move first makes the oddities differ by `0` or `4`.
  obtain ⟨η, u, hY⟩ := h.exists_hasSignOddity hB (k + 1)
  obtain ⟨α, hα⟩ := exists_represents _ _ _ (h.realizable_of_hasSignOddity hB hX hoddX).1
  obtain ⟨β, hβ⟩ := exists_represents _ _ _ (h.realizable_of_hasSignOddity hB hY hoddY).1
  obtain ⟨P₁, h₁, hagree₁, hX₁, -⟩ := h.exists_move_of_represents hB hX hY hoddX hoddY hα hβ
  obtain ⟨P₂, h₂, hagree₂, hX₂⟩ := key h₁ hX₁ (by
    rcases hmove β (mul_self_eq_one_of_represents _ _ _ _ hβ) with h0 | h4
    · exact .inl (by rw [he]; linear_combination h0)
    · exact .inr (by rw [he]; linear_combination h4))
  exact ⟨P₂, h₂, fun i hi ↦ (hagree₂ i hi).trans (hagree₁ i hi), hX₂⟩

/-- With `N k` and `N (k + 1)` of type I, the constituent `N k` can be given a sign `ε₀` and an
oddity `t₀` of the same parity realizable in its rank, as soon as some `(η₀, u₀)` realizable in the
rank of `N (k + 1)` satisfies `η₀ · e((t₀ + u₀) / 8) = η · e((t + u) / 8)`. When `N (k + 2)` is of
type II, the invariant of index `k + 1` provides this. -/
private theorem IsJordanSplitting.exists_hasSignOddity_of_eq_or_eq (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) {k : ℕ} {ε ε₀ η η₀ : ℤ} {t t₀ u u₀ : ZMod (2 ^ 3)}
    (hX : HasSignOddity B (N k) k ε t) (hY : HasSignOddity B (N (k + 1)) (k + 1) η u)
    (hoddX : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hoddY : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x)
    (hR₀ : Realizable (finrank ℤ_[2] (N k)) ε₀ t₀) {e : ZMod (2 ^ 3)} (he : t₀ = t + 2 * e)
    (hRY₀ : Realizable (finrank ℤ_[2] (N (k + 1))) η₀ u₀)
    (hinv : η₀ = η ∧ t₀ + u₀ = t + u ∨ η₀ = -η ∧ t₀ + u₀ = t + u + 4) :
    ∃ P : ℕ → Submodule ℤ_[2] M, B.IsJordanSplitting 2 P ∧ (∀ i < k, P i = N i) ∧
      HasSignOddity B (P k) k ε₀ t₀ := by
  obtain ⟨hR, -⟩ := h.realizable_of_hasSignOddity hB hX hoddX
  obtain ⟨hRY, -⟩ := h.realizable_of_hasSignOddity hB hY hoddY
  have hε : ε₀ = ε ∨ ε₀ = -ε := by
    have := eq_one_or_eq_neg_one_of_realizable _ _ _ hR₀
    have := eq_one_or_eq_neg_one_of_realizable _ _ _ hR
    omega
  -- The oddities differ by `0`, by `4`, or by `2 β` for a unit `β`.
  have hcases : ∀ x : ZMod (2 ^ 3), 2 * x = 0 ∨ 2 * x = 4 ∨ x * x = 1 := by decide
  rcases hcases e with h0 | h4 | hx
  · rw [h0, add_zero] at he
    subst he
    exact h.exists_hasSignOddity_of_eq hB hX hoddX hoddY hε hR₀
  · -- The constituent `N (k + 1)` is flexible.
    rw [h4] at he
    subst he
    refine h.exists_hasSignOddity_add_four hB hX hY hoddX hoddY
      (flexible_of_realizable_of_eq _ _ _ _ _ hRY hRY₀ ?_) hε hR₀
    rcases hinv with ⟨hη, hs⟩ | ⟨hη, hs⟩
    · exact .inl ⟨hη, by linear_combination hs⟩
    · exact .inr ⟨hη, by linear_combination hs⟩
  · -- The constituent `N (k + 1)` takes a unit value `≡ e` modulo `4`, and one move with it
    -- suffices.
    subst he
    have hv := represents_of_realizable_of_eq _ _ _ _ _ _ hRY hRY₀ hx (by
      rcases hinv with ⟨hη, hs⟩ | ⟨hη, hs⟩
      · exact .inl ⟨hη, by linear_combination hs⟩
      · exact .inr ⟨hη, by linear_combination hs⟩)
    obtain ⟨α, hα, hsgn⟩ := exists_represents_moveSign_eq _ _ _ _ _ hR hR₀ hx
    obtain ⟨P, hP, hagree, hX', -⟩ := h.exists_move_of_represents hB hX hY hoddX hoddY hα hv
    rw [hsgn] at hX'
    exact ⟨P, hP, hagree, hX'⟩

end Compartment

/-- A constituent with the type, sign and oddity of `N k` is isometric to `N k`. -/
private theorem IsJordanSplitting.equivalent_restrict_of_hasSignOddity [Module.Free ℤ_[2] M']
    [Module.Finite ℤ_[2] M'] {P : ℕ → Submodule ℤ_[2] M'} (h : B.IsJordanSplitting 2 N)
    (hP : B'.IsJordanSplitting 2 P) (hB : B.IsSymm) (hB' : B'.IsSymm) {k : ℕ}
    {C : BilinForm ℤ_[2] (N k)} (hC : (2 : ℤ_[2]) ^ k • C = B.restrict (N k)) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (d : Basis ι ℤ_[2] (N k)) {w : N k} (hw : C.IsCharacteristic w)
    (hcard : Fintype.card ι = finrank ℤ_[2] (P k))
    (htype : (∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) ↔ ∀ x ∈ P k, 2 * 2 ^ k ∣ B' x x)
    (hP' : HasSignOddity B' (P k) k (χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det))
      (PadicInt.toZModPow 3 (C w w))) :
    (B.restrict (N k)).Equivalent (B'.restrict (P k)) := by
  have := hP.free k
  have := hP.finite k
  obtain ⟨C', hC', hC'p⟩ := isModular_def.mp (hP.isModular k)
  obtain ⟨w', hw'⟩ := ((IsSMulRegular.of_ne_zero (pow_ne_zero k
    (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).isSymm_smul_iff.mp (hC' ▸ hB'.restrict (P k))
    ).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  obtain ⟨hχ, ht⟩ := hP' C' _ (Module.finBasis ℤ_[2] (P k)) w' hC' hw'
  exact (h.equivalent_restrict_iff hP hB hB' hC hC' d (Module.finBasis ℤ_[2] (P k))
    (by rw [hcard, Fintype.card_fin]) hw hw').mpr ⟨htype, hχ.symm, ht.symm⟩

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

include h h' hB hB' in
/-- After cancelling matching lower constituents, the invariant of index `k + 1` compares the sign
of the constituents of index `k + 1` times the oddity character of the constituents of indices `k`
and `k + 1` together. -/
theorem IsJordanSplitting.χ₈_mul_stdAddChar_add_eq_of_forall_equivalent_restrict {k : ℕ}
    (hC : ∀ i ≤ k, (2 : ℤ_[2]) ^ i • C i = B.restrict (N i))
    (hC' : ∀ i ≤ k, (2 : ℤ_[2]) ^ i • C' i = B'.restrict (N' i))
    (hw : ∀ i < k, (C i).IsCharacteristic (w i))
    (hw' : ∀ i < k, (C' i).IsCharacteristic (w' i))
    (hcard : ∀ i < k, Fintype.card (α i) = Fintype.card (α' i))
    (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i)))
    (hgauss : (∏ i ∈ Finset.Iic (k + 1), ((χ₈ (PadicInt.toZModPow 3 ((C i).toMatrix
      (d i)).det) : ℤ) : ℂ) ^ (k + 1 + 1 - i)) *
        stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic (k + 1), C i (w i) (w i))) =
      (∏ i ∈ Finset.Iic (k + 1), ((χ₈ (PadicInt.toZModPow 3 ((C' i).toMatrix
        (d' i)).det) : ℤ) : ℂ) ^ (k + 1 + 1 - i)) *
        stdAddChar (PadicInt.toZModPow 3 (∑ i ∈ Finset.Iic (k + 1), C' i (w' i) (w' i)))) :
    ((χ₈ (PadicInt.toZModPow 3 ((C (k + 1)).toMatrix (d (k + 1))).det) : ℤ) : ℂ) *
        stdAddChar (PadicInt.toZModPow 3 (C k (w k) (w k)) +
          PadicInt.toZModPow 3 (C (k + 1) (w (k + 1)) (w (k + 1)))) =
      ((χ₈ (PadicInt.toZModPow 3 ((C' (k + 1)).toMatrix (d' (k + 1))).det) : ℤ) : ℂ) *
        stdAddChar (PadicInt.toZModPow 3 (C' k (w' k) (w' k)) +
          PadicInt.toZModPow 3 (C' (k + 1) (w' (k + 1)) (w' (k + 1)))) := by
  have hcancelled := h.prod_χ₈_pow_mul_stdAddChar_eq_of_forall_equivalent_restrict
    h' hB hB' C d w C' d' w' (fun i hi ↦ hC i (by omega)) (fun i hi ↦ hC' i (by omega)) hw hw'
    hcard hlow (k + 1) (by omega) hgauss
  have h2 : (2 : ℤ_[2]) ^ k ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k (two_ne_zero : (2 : ℤ_[2]) ≠ 0))
  have hsq (X : ZMod (2 ^ 3)) (hX : IsUnit X) : ((χ₈ X : ℤ) : ℂ) ^ 2 = 1 := by
    have : χ₈ X ^ 2 = 1 := by
      rw [← MulChar.pow_apply' _ two_ne_zero, isQuadratic_χ₈.sq_eq_one, MulChar.one_apply hX]
    exact_mod_cast this
  rw [Finset.prod_Ico_succ_top (by omega : k ≤ k + 1),
    Finset.prod_Ico_succ_top (by omega : k ≤ k + 1), Nat.Ico_succ_singleton,
    Finset.prod_singleton, Finset.prod_singleton, show k + 1 + 1 - k = 2 by omega,
    show k + 1 + 1 - (k + 1) = 1 by omega, pow_one, pow_one,
    hsq _ (((h.isModular k).isUnit_det_of_smul_eq h2 (hC k le_rfl) (d k)).map _),
    hsq _ (((h'.isModular k).isUnit_det_of_smul_eq h2 (hC' k le_rfl) (d' k)).map _)]
    at hcancelled
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  linear_combination hcancelled

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
/-- **A constituent of type I followed by one of type I** can be matched while preserving the
lower prefix. If `N (k + 2)` is of type II, the invariant of index `k + 1` leaves at most two
moves between `N' k` and `N' (k + 1)` to make; otherwise sign walking across `N' (k + 1)` is
available as well, and no invariant is needed. -/
theorem IsJordanSplitting.exists_equivalent_restrict_of_odd_of_odd [Module.Finite ℤ_[2] M]
    [Module.Finite ℤ_[2] M'] {k : ℕ}
    (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i)))
    (hTk : ¬∀ x ∈ N k, 2 * 2 ^ k ∣ B x x) (hTk1 : ¬∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧ (∀ i < k, N'' i = N' i) ∧
      (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) := by
  have : Module.Free ℤ_[2] M := .of_basis (h.isInternal.collectedBasis d)
  have : Module.Free ℤ_[2] M' := .of_basis (h'.isInternal.collectedBasis d')
  have h2 : (2 : ℤ_[2]) ∈ nonZeroDivisors ℤ_[2] := mem_nonZeroDivisors_of_ne_zero two_ne_zero
  have hrank (i : ℕ) : finrank ℤ_[2] (N i) = finrank ℤ_[2] (N' i) := by
    rw [finrank_eq_card_basis (d i), finrank_eq_card_basis (d' i), hcard i]
  have hTk' : ¬∀ x ∈ N' k, 2 * 2 ^ k ∣ B' x x := fun H ↦ hTk ((htype k).mpr H)
  have hTk1' : ¬∀ x ∈ N' (k + 1), 2 * 2 ^ (k + 1) ∣ B' x x :=
    fun H ↦ hTk1 ((htype (k + 1)).mpr H)
  -- It suffices to give the constituent of index `k` the sign and oddity of `N k`.
  suffices ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧
      (∀ i < k, N'' i = N' i) ∧ HasSignOddity B' (N'' k) k
        (χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det))
        (PadicInt.toZModPow 3 (C k (w k) (w k))) by
    obtain ⟨N'', h'', hagree, hX''⟩ := this
    refine ⟨N'', h'', hagree, h.equivalent_restrict_of_hasSignOddity h'' hB hB' (hC k) (d k)
      (hw k) ?_ ?_ hX''⟩
    · rw [← finrank_eq_card_basis (d k), hrank k,
        h'.finrank_eq h'' two_ne_zero PadicInt.not_isUnit_two k]
    · exact (htype k).trans ⟨h'.forall_two_mul_pow_dvd_of_equivalent h'' (.refl _) h2 dvd_rfl,
        h''.forall_two_mul_pow_dvd_of_equivalent h' (.refl _) h2 dvd_rfl⟩
  -- The invariant of index `k + 1`, when it is defined.
  have hinv (hk2 : ∀ x ∈ N (k + 1 + 1), 2 * 2 ^ (k + 1 + 1) ∣ B x x) :=
    χ₈_eq_and_eq_or_of_mul_stdAddChar_eq
      (((h.isModular (k + 1)).isUnit_det_of_smul_eq (pow_mem h2 _) (hC _) (d _)).map _)
      (((h'.isModular (k + 1)).isUnit_det_of_smul_eq (pow_mem h2 _) (hC' _) (d' _)).map _)
      (h.χ₈_mul_stdAddChar_add_eq_of_forall_equivalent_restrict h' hB hB' C d w C' d' w'
        (fun i _ ↦ hC i) (fun i _ ↦ hC' i) (fun i _ ↦ hw i) (fun i _ ↦ hw' i)
        (fun i _ ↦ hcard i) hlow (hgauss (k + 1) hk2))
  -- The signs and oddities of the constituents of indices `k` and `k + 1`.
  have hX₀ := h.hasSignOddity hB (hC k) (d k) (hw k)
  have hY₀ := h.hasSignOddity hB (hC (k + 1)) (d (k + 1)) (hw (k + 1))
  have hX := h'.hasSignOddity hB' (hC' k) (d' k) (hw' k)
  have hY := h'.hasSignOddity hB' (hC' (k + 1)) (d' (k + 1)) (hw' (k + 1))
  obtain ⟨hR₀, e₀, he₀⟩ := h.realizable_of_hasSignOddity hB hX₀ hTk
  obtain ⟨-, e, he⟩ := h'.realizable_of_hasSignOddity hB' hX hTk'
  obtain ⟨hRY₀, -⟩ := h.realizable_of_hasSignOddity hB hY₀ hTk1
  rw [hrank] at hR₀ he₀ hRY₀
  generalize χ₈ (PadicInt.toZModPow 3 ((C k).toMatrix (d k)).det) = ε₀ at *
  generalize PadicInt.toZModPow 3 (C k (w k) (w k)) = t₀ at *
  generalize PadicInt.toZModPow 3 (C' k (w' k) (w' k)) = t at *
  generalize χ₈ (PadicInt.toZModPow 3 ((C (k + 1)).toMatrix (d (k + 1))).det) = η₀ at *
  generalize PadicInt.toZModPow 3 (C (k + 1) (w (k + 1)) (w (k + 1))) = u₀ at *
  have hδ : t₀ = t + 2 * (e₀ - e) := by rw [he₀, he]; ring
  by_cases hk2 : ∀ x ∈ N (k + 1 + 1), 2 * 2 ^ (k + 1 + 1) ∣ B x x
  · exact h'.exists_hasSignOddity_of_eq_or_eq hB' hX hY hTk' hTk1' hR₀ hδ hRY₀ (hinv hk2)
  · -- If `N (k + 2)` is of type I, sign walking across `N' (k + 1)` is available.
    exact h'.exists_hasSignOddity_of_odd_add_two hB' hX hTk' hTk1'
      (fun H ↦ hk2 ((htype (k + 2)).mpr H)) hR₀ hδ

include h h' hB hB' hC hC' hw hw' hcard hgauss htype in
/-- Match the next constituent, preserving the lower prefix. -/
private theorem IsJordanSplitting.exists_equivalent_restrict [Module.Finite ℤ_[2] M]
    [Module.Finite ℤ_[2] M'] {k : ℕ}
    (hlow : ∀ i < k, (B.restrict (N i)).Equivalent (B'.restrict (N' i))) :
    ∃ N'' : ℕ → Submodule ℤ_[2] M', B'.IsJordanSplitting 2 N'' ∧ (∀ i < k, N'' i = N' i) ∧
      (B.restrict (N k)).Equivalent (B'.restrict (N'' k)) := by
  by_cases hTk : ∀ x ∈ N k, 2 * 2 ^ k ∣ B x x
  · exact h.exists_equivalent_restrict_of_even h' hB hB' C hC d w hw C' hC' d' w' hw'
      hcard hgauss htype hlow hTk
  by_cases hTk1 : ∀ x ∈ N (k + 1), 2 * 2 ^ (k + 1) ∣ B x x
  · exact h.exists_equivalent_restrict_of_odd_of_even h' hB hB' C hC d w hw C' hC' d' w' hw'
      hcard hgauss htype hlow hTk hTk1
  · exact h.exists_equivalent_restrict_of_odd_of_odd h' hB hB' C hC d w hw C' hC' d' w' hw'
      hcard hgauss htype hlow hTk hTk1

end PrefixCancellation

/-! ### The classification -/

/-- **Classification of dyadic forms.** Let `B` and `B'` be symmetric forms on finite free
`ℤ_[2]`-modules with Jordan splittings `N` and `N'` with respect to `2`. Let `C i` and `C' i` be
the unimodular rescalings of the constituents, with bases `d i`, `d' i` and characteristic vectors
`w i`, `w' i`, and write `ε i = χ₈(det C i)`, `t i = C i (w i) (w i)` and `e(t) = exp (2πi t)`.
Then `B` and `B'` are isometric exactly when

* the constituents `N i` and `N' i` have the same rank and the same type for every `i`, and
* `∏_{i ≤ j} ε i^{j + 1 - i} · e((∑_{i ≤ j} t i) / 8) = ∏_{i ≤ j} ε' i^{j + 1 - i} ·
  e((∑_{i ≤ j} t' i) / 8)` whenever `N (j + 1)` is of type II.

The constituents themselves need not be isometric: `⟨1⟩ ⊥ 2 !![0, 1; 1, 0] ≅ ⟨5⟩ ⊥ 2 !![2, 1; 1, 2]`
(`TauCeti.equivalent_toBilin'_unary_two_hyperbolic`), although `⟨1⟩` and `⟨5⟩` have different
signs. The invariants beyond the last nonzero constituent are needed as well: the forms
`!![0, 1; 1, 0] ⊥ ⟨2⟩` and `!![2, 1; 1, 2] ⊥ ⟨2⟩` have the same ranks, types and invariant of
index `1`, and their invariants of index `2` first separate them, through the signs `χ₈(-1) = 1`
and `χ₈(3) = -1` of their constituents of index `0`. -/
theorem IsJordanSplitting.equivalent_iff_prod_χ₈_pow_mul_stdAddChar_sum_eq [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (h' : B'.IsJordanSplitting 2 N') (hB : B.IsSymm)
    (hB' : B'.IsSymm) {α α' : ℕ → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Fintype (α' i)] [∀ i, DecidableEq (α' i)] (C : ∀ i, BilinForm ℤ_[2] (N i))
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
        exact ((IsSMulRegular.of_ne_zero
          (pow_ne_zero i (two_ne_zero : (2 : ℤ_[2]) ≠ 0))).isSymm_smul_iff.mp
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
            (fun i _ ↦ hC'' i) d'' w'' (fun i _ ↦ hw'' i))) htype'' hlow
      refine ⟨N₁, h₁, fun i hi ↦ ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [hagree i hi]
        exact hlow i hi
      · exact hk

end LinearMap.BilinForm
