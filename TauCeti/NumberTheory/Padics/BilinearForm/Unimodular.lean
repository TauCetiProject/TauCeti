/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
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

The determinant square class may be replaced by the sign `χ₈(det)`, the entry of the Conway–Sloane
`2`-adic symbol: modulo `4` the determinant is `1 + t - n` for the oddity `t` and the rank `n`, and
a unit modulo `8` is determined by its residue modulo `4` and its value under `χ₈`.

## Main results

* `LinearMap.BilinForm.IsSymm.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd`:
  two unimodular forms of the same rank over `ℤ_[2]` are isometric exactly when they have the same
  type, the product of their Gram determinants is a square, and their characteristic vectors have
  the same self-pairing modulo `8`.
* `LinearMap.BilinForm.IsSymm.four_dvd_det_toMatrix_sub_one_sub_apply_self_add_card`: the
  determinant of a unimodular form over `ℤ_[2]` is `1 + t - n` modulo `4`.
* `LinearMap.BilinForm.IsSymm.equivalent_iff_two_dvd_iff_and_χ₈_eq_and_eight_dvd`: unimodular forms
  of the same rank over `ℤ_[2]` are classified by their type, sign and oddity.

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

/-! ### The determinant modulo `4`, and the classification by sign and oddity -/

/-- For units `u i` of `ℤ_[2]`, the product is `1 + ∑ u i - #s` modulo `4`, and the sum is `#s`
modulo `2`. -/
private theorem four_dvd_prod_sub_one_sub_sum_add_card {ι : Type*} (s : Finset ι)
    {u : ι → ℤ_[2]} (hu : ∀ i ∈ s, IsUnit (u i)) :
    (4 : ℤ_[2]) ∣ ∏ i ∈ s, u i - 1 - ∑ i ∈ s, u i + s.card ∧
      (2 : ℤ_[2]) ∣ ∑ i ∈ s, u i - s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    obtain ⟨⟨f, hf⟩, ⟨e, he⟩⟩ := ih fun i hi ↦ hu i (Finset.mem_insert_of_mem hi)
    -- A unit of `ℤ_[2]` is odd.
    obtain ⟨c, hc⟩ : (2 : ℤ_[2]) ∣ u a - 1 := by
      have hua := hu a (Finset.mem_insert_self a s)
      obtain ⟨c, hc⟩ := PadicInt.two_dvd_sq_sub_self (u a)
      refine ⟨↑hua.unit⁻¹ * c, ?_⟩
      calc u a - 1 = ↑hua.unit⁻¹ * (u a * (u a - 1)) := by
            rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
        _ = 2 * (↑hua.unit⁻¹ * c) := by rw [show u a * (u a - 1) = u a ^ 2 - u a by ring, hc]; ring
    rw [Finset.prod_insert has, Finset.sum_insert has, Finset.card_insert_of_notMem has]
    push_cast
    exact ⟨⟨f + c * (2 * f + e), by
      linear_combination (∏ i ∈ s, u i - 1) * hc + (1 + 2 * c) * hf + 2 * c * he⟩,
      ⟨c + e, by linear_combination hc + he⟩⟩

/-- **The determinant of a unimodular form over `ℤ_[2]` modulo `4`.** Let `B` be a symmetric form
over `ℤ_[2]` whose Gram matrix in a basis `b` of size `n` has a unit determinant, and let `w` be a
characteristic vector. Then `det ≡ 1 + B w w - n` modulo `4`: the determinant modulo `4` is
determined by the rank and the oddity. For instance the hyperbolic plane `!![0, 1; 1, 0]`, of
rank `2` and oddity `0`, has determinant `-1 ≡ 1 + 0 - 2`, and `⟨3, 3⟩`, of oddity `6`, has
determinant `9 ≡ 1 + 6 - 2`. -/
theorem IsSymm.four_dvd_det_toMatrix_sub_one_sub_apply_self_add_card (hB : B.IsSymm) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ_[2] M) (hdet : IsUnit (B.toMatrix b).det) {w : M}
    (hw : B.IsCharacteristic w) :
    (4 : ℤ_[2]) ∣ (B.toMatrix b).det - 1 - B w w + Fintype.card ι := by
  -- The orthogonal sum `D = B ⊥ ⟨1⟩` on `M × ℤ_[2]`, with the basis `d` extending `b`.
  set D : BilinForm ℤ_[2] (M × ℤ_[2]) := B.prod (LinearMap.mul ℤ_[2] ℤ_[2])
  set d := b.prod (Basis.singleton Unit ℤ_[2])
  have hDd : D.toMatrix d = Matrix.fromBlocks (B.toMatrix b) 0 0 1 := by
    ext (i | i) (j | j) <;> simp [D, d, toMatrix_apply, prod_apply, Basis.prod_apply]
  have hDs : D.IsSymm := isSymm_prod_iff.2
    ⟨hB, ⟨fun x y ↦ by rw [LinearMap.mul_apply', LinearMap.mul_apply', mul_comm]⟩⟩
  -- `D` represents the unit `1`, so it has an orthogonal basis `c` with unit self-pairings.
  set e := d.reindex (Fintype.equivFin (ι ⊕ Unit))
  have hedet : (D.toMatrix e).det = (B.toMatrix b).det := by
    rw [det_toMatrix_reindex, hDd, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  obtain ⟨c, hc, hcu⟩ := hDs.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self e
    (hedet ▸ hdet) ⟨(0, 1), by simp [D, prod_apply]⟩
  -- `(w, 1)` and `∑ i, c i` are characteristic vectors of `D`.
  have hw' : D.IsCharacteristic (w, 1) := isCharacteristic_iff.mpr fun x ↦ by
    have h := dvd_sub (isCharacteristic_iff.mp hw x.1) (PadicInt.two_dvd_sq_sub_self x.2)
    simp only [D, prod_apply, LinearMap.mul_apply']
    convert h using 1
    ring
  have : Module.Free ℤ_[2] (M × ℤ_[2]) := .of_basis c
  have : D.IsPerfPair := c.isPerfPair_of_isUnit_det c D (hc.isUnit_det_toMatrix hcu)
  obtain ⟨r, hr⟩ := hw'.eight_dvd_apply_self_sub_apply_self hDs
    (hc.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
  have hD1 : D (w, 1) (w, 1) = B w w + 1 := by simp [D, prod_apply]
  rw [hc.apply_sum_sum, hD1] at hr
  -- The determinants in `e` and in `c` differ by the square of a unit.
  have hP : IsUnit (c.toMatrix e).det :=
    Matrix.isUnit_det_of_right_inverse (c.toMatrix_mul_toMatrix_flip e)
  obtain ⟨s, hs⟩ := PadicInt.eight_dvd_sq_sub_one_of_isUnit hP
  obtain ⟨⟨f, hf⟩, -⟩ := four_dvd_prod_sub_one_sub_sum_add_card Finset.univ fun i _ ↦ hcu i
  have hdet' := det_toMatrix_eq_det_sq_mul_det c e D
  rw [hedet, hc.det_toMatrix] at hdet'
  simp only [Finset.card_univ, Fintype.card_fin, Fintype.card_sum, Fintype.card_unit] at hf
  refine ⟨f + 2 * s * ∏ i, D (c i) (c i) + 2 * r, ?_⟩
  rw [hdet']
  push_cast at hf ⊢
  linear_combination (∏ i, D (c i) (c i)) * hs + hf + hr

/-- **Classification of unimodular forms over `ℤ_[2]` by type, sign and oddity.** Let `B` and `C`
be symmetric forms over `ℤ_[2]` with unit Gram determinants in bases of the same size, and let `w`
and `w'` be characteristic vectors. Then `B` and `C` are isometric exactly when they have the same
type, the same sign `χ₈(det)`, and the same oddity modulo `8`. These are the entries of the
Conway–Sloane `2`-adic symbol of a unimodular constituent; the determinant square class is
recovered from them by
`LinearMap.BilinForm.IsSymm.four_dvd_det_toMatrix_sub_one_sub_apply_self_add_card`. -/
theorem IsSymm.equivalent_iff_two_dvd_iff_and_χ₈_eq_and_eight_dvd (hB : B.IsSymm) (hC : C.IsSymm)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ_[2] M) (c : Basis ι ℤ_[2] N)
    (hBdet : IsUnit (B.toMatrix b).det) (hCdet : IsUnit (C.toMatrix c).det) {w : M} {w' : N}
    (hw : B.IsCharacteristic w) (hw' : C.IsCharacteristic w') :
    B.Equivalent C ↔ ((∀ x, (2 : ℤ_[2]) ∣ B x x) ↔ ∀ y, (2 : ℤ_[2]) ∣ C y y) ∧
      χ₈ (PadicInt.toZModPow 3 (B.toMatrix b).det) = χ₈ (PadicInt.toZModPow 3 (C.toMatrix c).det) ∧
        (8 : ℤ_[2]) ∣ C w' w' - B w w := by
  set b' := b.reindex (Fintype.equivFin ι)
  set c' := c.reindex (Fintype.equivFin ι)
  rw [hB.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd hC b' c'
    (by rwa [det_toMatrix_reindex]) (by rwa [det_toMatrix_reindex]) hw hw',
    det_toMatrix_reindex, det_toMatrix_reindex,
    PadicInt.isSquare_mul_iff_toZModPow_three_eq hBdet hCdet]
  refine and_congr_right fun _ ↦ ⟨fun ⟨h, h8⟩ ↦ ⟨by rw [h], h8⟩, fun ⟨hχ, h8⟩ ↦ ⟨?_, h8⟩⟩
  -- The determinants agree modulo `4`, and a unit modulo `8` is determined by its residue
  -- modulo `4` and its sign.
  obtain ⟨u, hu⟩ := hB.four_dvd_det_toMatrix_sub_one_sub_apply_self_add_card b hBdet hw
  obtain ⟨v, hv⟩ := hC.four_dvd_det_toMatrix_sub_one_sub_apply_self_add_card c hCdet hw'
  obtain ⟨r, hr⟩ := h8
  have h4 : (B.toMatrix b).det = (C.toMatrix c).det + 4 * (u - v - 2 * r) := by
    linear_combination hu - hv - hr
  have hX := PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hCdet
  rw [h4, map_add, map_mul, map_ofNat] at hχ ⊢
  generalize PadicInt.toZModPow 3 (C.toMatrix c).det = X at hX hχ ⊢
  generalize PadicInt.toZModPow 3 (u - v - 2 * r) = Y at hχ ⊢
  revert X Y
  decide

end LinearMap.BilinForm
