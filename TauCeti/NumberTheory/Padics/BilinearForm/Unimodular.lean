/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Even.Henselian
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.BilinearForm.OddUnimodular
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

## Main results

* `LinearMap.BilinForm.IsSymm.equivalent_iff_two_dvd_iff_and_isSquare_det_mul_det_and_eight_dvd`:
  two unimodular forms of the same rank over `ℤ_[2]` are isometric exactly when they have the same
  type, the product of their Gram determinants is a square, and their characteristic vectors have
  the same self-pairing modulo `8`.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M N : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup N] [Module ℤ_[2] N]
  {B : BilinForm ℤ_[2] M} {C : BilinForm ℤ_[2] N}

/-- A form over `ℤ_[2]` that is not even represents a unit. -/
private theorem exists_isUnit_apply_self_of_not_forall_two_dvd (h : ¬∀ x, (2 : ℤ_[2]) ∣ B x x) :
    ∃ x, IsUnit (B x x) := by
  push Not at h
  obtain ⟨x, hx⟩ := h
  exact ⟨x, by_contra fun hu ↦ hx (by simpa using PadicInt.not_isUnit_iff_dvd.mp hu)⟩

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
  have : C.IsPerfPair := c.isPerfPair_of_isUnit_det C hCdet
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

end LinearMap.BilinForm
