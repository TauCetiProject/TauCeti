/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Even.Henselian
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.Odd.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.BilinearForm.Prod
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.BilinearForm.OddUnimodular
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Henselian.Basic

/-!
# Unimodular forms over `ℤ_[2]`

A symmetric bilinear form over `ℤ_[2]` with unit Gram determinant is either *even*, when `2`
divides every self-pairing `B x x` (type II), or *odd*, when some `B x x` is a unit (type I). Its
*oddity* is the self-pairing of a characteristic vector modulo `8`, which is well defined
(`LinearMap.BilinForm.IsCharacteristic.eight_dvd_apply_self_sub_apply_self`) and is `0` for even
forms (`LinearMap.BilinForm.IsCharacteristic.eight_dvd_apply_self_of_forall_two_dvd`).

This file proves that the rank, the type, the determinant square class and the oddity classify
unimodular forms over `ℤ_[2]`. It assembles the even classification
`LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det_of_even` and the odd one
`LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det_and_eight_dvd_of_odd`; the type is
an isometry invariant by `LinearMap.BilinForm.Equivalent.forall_two_dvd_apply_self_iff`. The type
is not determined by the other three: the hyperbolic plane `!![0, 1; 1, 0]` and the diagonal form
`⟨1, -1⟩` both have rank two, determinant `-1` and oddity `0`, and only the second represents a
unit.

Moreover, for any unimodular symmetric form of rank `n` with characteristic vector `w`, the Gram
determinant satisfies `det ≡ 1 + B w w - n` modulo `4`
(`LinearMap.BilinForm.IsSymm.four_dvd_det_toMatrix_sub`), so the rank, oddity modulo `8`, and sign
`χ₈(det)` together determine the determinant square class.

## Main results

* `LinearMap.BilinForm.IsSymm.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd`:
  two unimodular forms of the same rank over `ℤ_[2]` are isometric exactly when they have the same
  type, the product of their Gram determinants is a square, and their characteristic vectors have
  the same self-pairing modulo `8`.
* `LinearMap.BilinForm.IsSymm.four_dvd_det_toMatrix_sub`: for a unimodular symmetric form over
  `ℤ_[2]` of rank `n` with characteristic vector `w`, `det ≡ 1 + B w w - n` modulo `4`.
* `LinearMap.BilinForm.IsSymm.equivalent_iff_card_eq_and_two_dvd_iff_and_χ₈_det_eq_and_eight_dvd`
  classifies unimodular symmetric forms over `ℤ_[2]` by rank, parity type, sign `χ₈(det)`, and
  oddity modulo `8`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M N : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup N] [Module ℤ_[2] N]
  {B : BilinForm ℤ_[2] M} {C : BilinForm ℤ_[2] N}

/-- **Classification of unimodular forms over `ℤ_[2]`.** Let `B` and `C` be symmetric forms over
`ℤ_[2]` with unit Gram determinants in bases of the same size, and let `w` and `w'` be
characteristic vectors for `B` and `C`. Then `B` and `C` are isometric exactly when

* `B` is even if and only if `C` is even,
* the product of their Gram determinants is a square, and
* `B w w ≡ C w' w'` modulo `8`, that is, their oddities agree. -/
theorem IsSymm.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd
    (hB : B.IsSymm) (hC : C.IsSymm) {n : ℕ} (b : Basis (Fin n) ℤ_[2] M)
    (c : Basis (Fin n) ℤ_[2] N) (hBdet : IsUnit (B.toMatrix b).det)
    (hCdet : IsUnit (C.toMatrix c).det) {w : M} {w' : N} (hw : B.IsCharacteristic w)
    (hw' : C.IsCharacteristic w') :
    B.Equivalent C ↔ ((∀ x, (2 : ℤ_[2]) ∣ B x x) ↔ ∀ y, (2 : ℤ_[2]) ∣ C y y) ∧
      IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) ∧ (8 : ℤ_[2]) ∣ C w' w' - B w w := by
  have : Free ℤ_[2] N := .of_basis c
  have : C.IsPerfPair := c.isPerfPair_of_isUnit_det c C hCdet
  refine ⟨fun h ↦ ⟨h.forall_two_dvd_apply_self_iff, h.isSquare_det_mul_det b c, ?_⟩,
    fun ⟨hpar, hsq, h8⟩ ↦ ?_⟩
  · -- An isometry carries `w` to a characteristic vector of `C`.
    obtain ⟨f⟩ := h
    have hfw : C.IsCharacteristic (f w) := f.isCharacteristic_apply_iff.mpr hw
    simpa only [IsometryEquiv.map_app] using hfw.eight_dvd_apply_self_sub_apply_self hC hw'
  by_cases hBe : ∀ x, (2 : ℤ_[2]) ∣ B x x
  · exact (hB.equivalent_iff_isSquare_det_mul_det_of_even (PadicInt.card_residueField 2)
      PadicInt.not_isSquare_neg_three hC hBe (hpar.mp hBe) b c hBdet hCdet).mpr hsq
  · exact (hB.equivalent_iff_isSquare_det_mul_det_and_eight_dvd_of_odd hC b c hBdet hCdet
      (exists_isUnit_apply_self_of_not_forall_two_dvd hBe)
      (exists_isUnit_apply_self_of_not_forall_two_dvd (mt hpar.mpr hBe)) hw hw').mpr ⟨hsq, h8⟩

/-- In `ZMod 4`, the product of units `u i` satisfies `∏ u i = 1 + ∑ u i - n` and `∑ u i - n`
is even. -/
private theorem zmod_four_prod_eq_of_mul_self_eq_one {ι : Type*} (s : Finset ι)
    (u : ι → ZMod (2 ^ 2)) (hu : ∀ i ∈ s, u i * u i = 1) :
    ∏ i ∈ s, u i = 1 + ∑ i ∈ s, u i - s.card ∧ 2 * (∑ i ∈ s, u i - s.card) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨hp, he⟩ := ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one, hp]
    have h := (by decide : ∀ x y : ZMod (2 ^ 2), x * x = 1 → 2 * y = 0 →
      x * (1 + y) = 1 + (x - 1 + y) ∧ 2 * (x - 1 + y) = 0)
      (u a) (∑ i ∈ s, u i - s.card) (hu a (Finset.mem_insert_self a s)) he
    exact ⟨by convert h.1 using 1 <;> ring, by convert h.2 using 1; ring⟩

/-- For an orthogonal basis with unit self-pairings over `ℤ_[2]`, the Gram determinant in any
basis is congruent to `1 + B w w - n` modulo `4`. -/
private theorem iIsOrtho.four_dvd_det_toMatrix_sub {n : ℕ}
    {c : Basis (Fin n) ℤ_[2] M} (hc : B.iIsOrtho c) (hcu : ∀ i, IsUnit (B (c i) (c i)))
    (e : Basis (Fin n) ℤ_[2] M) {w : M} (hw : B.IsCharacteristic w) :
    (4 : ℤ_[2]) ∣ (B.toMatrix e).det - (1 + B w w - n) := by
  have : Free ℤ_[2] M := .of_basis c
  have : B.IsPerfPair := c.isPerfPair_of_isUnit_det c B (hc.isUnit_det_toMatrix hcu)
  have h48 : (4 : ℤ_[2]) ∣ 8 := ⟨2, by norm_num⟩
  have hsq4 {z : ℤ_[2]} (hz : IsUnit z) : PadicInt.toZModPow 2 (z ^ 2) = 1 :=
    (PadicInt.four_dvd_sub_iff_toZModPow_two_eq.mp
      (h48.trans (PadicInt.eight_dvd_sq_sub_one_of_isUnit hz))).symm.trans (map_one _)
  rw [PadicInt.four_dvd_sub_iff_toZModPow_two_eq, det_toMatrix_eq_det_sq_mul_det c e, map_mul,
    hsq4 (Matrix.isUnit_det_of_right_inverse (c.toMatrix_mul_toMatrix_flip e)), one_mul,
    hc.det_toMatrix, map_prod]
  have hw8 := hw.eight_dvd_apply_self_sub_apply_self hc.isSymm
    (hc.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
  rw [hc.apply_sum_sum] at hw8
  have hw4 := PadicInt.four_dvd_sub_iff_toZModPow_two_eq.mp (h48.trans hw8)
  have hprod := (zmod_four_prod_eq_of_mul_self_eq_one Finset.univ
    (fun i ↦ PadicInt.toZModPow 2 (B (c i) (c i)))
    (fun i _ ↦ by simpa [sq, map_mul] using hsq4 (hcu i))).1
  simp only [Finset.card_univ, Fintype.card_fin] at hprod
  rw [hprod, map_sub, map_add, map_one, hw4, map_sum, map_natCast]

/-- **Determinant congruence modulo `4` for unimodular forms over `ℤ_[2]`.** Let `B` be a
symmetric form over `ℤ_[2]` with unit Gram determinant in a basis `b` of size `n`, and let `w` be
a characteristic vector of `B`. Then `det (B.toMatrix b) ≡ 1 + B w w - n` modulo `4`.

In particular, together with the rank and the oddity `B w w` modulo `8`, the sign `χ₈(det)`
determines the determinant modulo `8` (hence its square class). -/
theorem IsSymm.four_dvd_det_toMatrix_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hB : B.IsSymm) (b : Basis ι ℤ_[2] M)
    (hdet : IsUnit (B.toMatrix b).det) {w : M} (hw : B.IsCharacteristic w) :
    (4 : ℤ_[2]) ∣ (B.toMatrix b).det - (1 + B w w - Fintype.card ι) := by
  set D : BilinForm ℤ_[2] (M × ℤ_[2]) := B.prod (LinearMap.mul ℤ_[2] ℤ_[2])
  set d := b.prod (Basis.singleton Unit ℤ_[2])
  have hDd : D.toMatrix d = Matrix.fromBlocks (B.toMatrix b) 0 0 1 := by
    ext (i | i) (j | j) <;> simp [D, d, toMatrix_apply, prod_apply, Basis.prod_apply]
  have hDs : D.IsSymm := isSymm_prod_iff.2
    ⟨hB, ⟨fun x y ↦ by rw [LinearMap.mul_apply', LinearMap.mul_apply', mul_comm]⟩⟩
  set e := d.reindex (Fintype.equivFin (ι ⊕ Unit))
  have hedet : (D.toMatrix e).det = (B.toMatrix b).det := by
    rw [det_toMatrix_reindex, hDd, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  obtain ⟨c, hc, hcu⟩ := hDs.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self e
    (hedet ▸ hdet) ⟨(0, 1), by simp [D, prod_apply]⟩
  have hw' : D.IsCharacteristic (w, 1) := isCharacteristic_iff.mpr fun x ↦ by
    have h := dvd_sub (isCharacteristic_iff.mp hw x.1) (PadicInt.two_dvd_sq_sub_self x.2)
    simpa only [D, prod_apply, LinearMap.mul_apply'] using by convert h using 1; ring
  have hD := hc.four_dvd_det_toMatrix_sub hcu e hw'
  rw [hedet, show D (w, 1) (w, 1) = B w w + 1 by simp [D, prod_apply],
    show ((Fintype.card (ι ⊕ Unit) : ℕ) : ℤ_[2]) = Fintype.card ι + 1 by simp] at hD
  convert hD using 1; ring

/-- **Classification of unimodular forms over `ℤ_[2]` by rank, type, sign and oddity.** Let `B`
and `C` be symmetric forms over `ℤ_[2]` with unit Gram determinants in bases `b` and `c`, and let
`w` and `w'` be characteristic vectors for `B` and `C`. Then `B` and `C` are isometric iff their
ranks, parity types, signs `χ₈(det)`, and oddities `B w w ≡ C w' w' (mod 8)` agree. -/
theorem IsSymm.equivalent_iff_card_eq_and_two_dvd_iff_and_χ₈_det_eq_and_eight_dvd
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (hB : B.IsSymm) (hC : C.IsSymm) (b : Basis ι ℤ_[2] M) (c : Basis κ ℤ_[2] N)
    (hBdet : IsUnit (B.toMatrix b).det) (hCdet : IsUnit (C.toMatrix c).det)
    {w : M} {w' : N} (hw : B.IsCharacteristic w) (hw' : C.IsCharacteristic w') :
    B.Equivalent C ↔
      Fintype.card ι = Fintype.card κ ∧
      ((∀ x, (2 : ℤ_[2]) ∣ B x x) ↔ ∀ y, (2 : ℤ_[2]) ∣ C y y) ∧
      χ₈ (PadicInt.toZModPow 3 (B.toMatrix b).det) =
        χ₈ (PadicInt.toZModPow 3 (C.toMatrix c).det) ∧
      (8 : ℤ_[2]) ∣ C w' w' - B w w := by
  by_cases hcard : Fintype.card ι = Fintype.card κ
  · let b' := b.reindex (Fintype.equivFin ι)
    let c' := c.reindex (Fintype.equivFinOfCardEq hcard.symm)
    have hb' := det_toMatrix_reindex b (Fintype.equivFin ι) B
    have hc' := det_toMatrix_reindex c (Fintype.equivFinOfCardEq hcard.symm) C
    rw [hB.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd hC b' c'
      (hb'.symm ▸ hBdet) (hc'.symm ▸ hCdet) hw hw', hb', hc',
      PadicInt.isSquare_mul_iff_toZModPow_three_eq hBdet hCdet]
    refine ⟨fun ⟨hpar, hdet, h8⟩ ↦ ⟨hcard, hpar, congrArg χ₈ hdet, h8⟩,
      fun ⟨_, hpar, hχ, h8⟩ ↦ ⟨hpar, ?_, h8⟩⟩
    obtain ⟨r, hr⟩ := dvd_sub (dvd_sub (hB.four_dvd_det_toMatrix_sub b hBdet hw)
      (hC.four_dvd_det_toMatrix_sub c hCdet hw')) (dvd_trans ⟨2, by norm_num⟩ h8)
    have h8det : (8 : ℤ_[2]) ∣ 2 * (B.toMatrix b).det - 2 * (C.toMatrix c).det :=
      ⟨r, by rw [hcard] at hr; linear_combination 2 * hr⟩
    have h2det : 2 * PadicInt.toZModPow 3 (B.toMatrix b).det =
        2 * PadicInt.toZModPow 3 (C.toMatrix c).det := by
      simpa only [map_mul, map_ofNat] using
        (PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp h8det).symm
    exact (by decide : ∀ x y : ZMod (2 ^ 3),
        x * x = 1 → y * y = 1 → χ₈ x = χ₈ y → 2 * x = 2 * y → x = y) _ _
      (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hBdet)
      (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hCdet) hχ h2det
  · exact ⟨fun ⟨ε⟩ ↦ absurd (by
        rw [← finrank_eq_card_basis b, ← finrank_eq_card_basis c, ε.toLinearEquiv.finrank_eq])
      hcard, fun h ↦ absurd h.1 hcard⟩

end LinearMap.BilinForm
