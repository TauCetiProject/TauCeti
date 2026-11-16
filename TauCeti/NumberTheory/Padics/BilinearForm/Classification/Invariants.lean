/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic
import Mathlib.Data.ZMod.Basic
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# Constituent signs and oddities of a dyadic Jordan splitting

Let `B` be a symmetric bilinear form on a finite free `ℤ_[2]`-module `M`, and let `N` be a Jordan
splitting of `B` with respect to `2`, so that `B` restricted to `N i` is `2 ^ i • C i` for a unique
unimodular form `C i`. Each constituent `N i` has two local invariants used in the Conway–Sloane
symbol and in the classification of dyadic forms:

* its **sign** `χ₈(det C i) ∈ {1, -1}` (`LinearMap.BilinForm.IsJordanSplitting.constituentSign`),
  which is independent of the choice of finite basis of `N i`
  (`LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq`);
* its **oddity** `C i w w mod 8` (`LinearMap.BilinForm.IsJordanSplitting.constituentOddity`), where
  `w` is any characteristic vector of `C i`, which is independent of the choice of `w`
  (`LinearMap.BilinForm.IsJordanSplitting.constituentOddity_eq`).

Unlike the constituent ranks and parity types, the individual signs and oddities depend on the
chosen Jordan splitting; this file records their basic properties and how they transform under
determinant and characteristic-vector congruences, as used by sign walking and oddity fusion.

## Main definitions

* `LinearMap.BilinForm.IsJordanSplitting.constituentSign`: the sign `χ₈(det C i) ∈ {1, -1}` of the
  `i`-th Jordan constituent.
* `LinearMap.BilinForm.IsJordanSplitting.constituentOddity`: the oddity `C i w w mod 8` of the
  `i`-th Jordan constituent.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq`,
  `LinearMap.BilinForm.IsJordanSplitting.constituentOddity_eq`: the constituent sign and oddity are
  computed by any unimodular rescaling, finite basis, and characteristic vector.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_one_or_neg_one`: every constituent sign
  is `1` or `-1`.
* `LinearMap.BilinForm.IsJordanSplitting.prod_constituentSign_eq_ite`: a product of constituent
  signs is `-1` iff the corresponding sum of `4` in `ZMod 8` equals `4`.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_of_eq`,
  `LinearMap.BilinForm.IsJordanSplitting.constituentOddity_eq_of_eq`: equal constituents of two
  Jordan splittings of `B` have the same sign and oddity.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_of_eq_bot`,
  `LinearMap.BilinForm.IsJordanSplitting.constituentOddity_of_eq_bot`,
  `LinearMap.BilinForm.IsJordanSplitting.constituentOddity_of_even`: a zero constituent has sign `1`
  and oddity `0`, and any type-II constituent has oddity `0`.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_mul_of_isSquare_det`,
  `LinearMap.BilinForm.IsJordanSplitting.constituentOddity_eq_add_of_eight_dvd`: transformation of
  constituent signs and oddities under elementary Jordan-splitting moves.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-- The unimodular rescaling of a Jordan constituent over `ℤ_[2]` is unique. -/
private theorem eq_of_two_pow_smul_eq {k : ℕ} {P : Submodule ℤ_[2] M}
    {C₁ C₂ : BilinForm ℤ_[2] P} (h₁ : (2 : ℤ_[2]) ^ k • C₁ = B.restrict P)
    (h₂ : (2 : ℤ_[2]) ^ k • C₂ = B.restrict P) : C₁ = C₂ := by
  have h2k : (2 : ℤ_[2]) ^ k ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero)
  refine LinearMap.ext₂ fun x y ↦ (mul_cancel_left_mem_nonZeroDivisors h2k).mp ?_
  simpa using (LinearMap.congr_fun₂ h₁ x y).trans (LinearMap.congr_fun₂ h₂ x y).symm

/-- Choice of unimodular rescaling of `N i` for a dyadic Jordan splitting. -/
private noncomputable def constituentForm (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    BilinForm ℤ_[2] (N i) :=
  (isModular_def.mp (h.isModular i)).choose

private theorem two_pow_smul_constituentForm (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    (2 : ℤ_[2]) ^ i • constituentForm h i = B.restrict (N i) :=
  (isModular_def.mp (h.isModular i)).choose_spec.1

private theorem isPerfPair_constituentForm (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    (constituentForm h i).IsPerfPair :=
  (isModular_def.mp (h.isModular i)).choose_spec.2

private theorem isSymm_constituentForm (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) (i : ℕ) :
    (constituentForm h i).IsSymm :=
  IsSymm.of_smul (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero))
    ((two_pow_smul_constituentForm h i).symm ▸ hB.restrict (N i))

/-- The sign `χ₈(det C i) ∈ {1, -1}` of the `i`-th constituent of a dyadic Jordan splitting, where
`C i` is the unimodular rescaling of `B` on `N i`.

By `IsJordanSplitting.constituentSign_eq`, this value is independent of the choice of unimodular
rescaling and finite basis of `N i`. -/
noncomputable def IsJordanSplitting.constituentSign [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (i : ℕ) : ℤ :=
  have := h.free i
  have := h.finite i
  χ₈ (PadicInt.toZModPow 3
    ((constituentForm h i).toMatrix (Module.finBasis ℤ_[2] (N i))).det)

/-- The oddity modulo `8` of the `i`-th constituent of a dyadic Jordan splitting: the residue
modulo `8` of `C i w w` for any characteristic vector `w` of the unimodular rescaling `C i` of `B`
on `N i`.

By `IsJordanSplitting.constituentOddity_eq`, this value is independent of the choice of unimodular
rescaling and characteristic vector. -/
noncomputable def IsJordanSplitting.constituentOddity [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) (i : ℕ) : ZMod (2 ^ 3) :=
  have := h.free i
  have := isPerfPair_constituentForm h i
  let w := ((isSymm_constituentForm h hB i).exists_isCharacteristic
    PadicInt.two_dvd_sq_sub_self).choose
  PadicInt.toZModPow 3 (constituentForm h i w w)

/-- `constituentSign` is independent of the choice of unimodular rescaling and finite basis. -/
theorem IsJordanSplitting.constituentSign_eq [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) {i : ℕ} {C : BilinForm ℤ_[2] (N i)}
    (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : Basis ι ℤ_[2] (N i)) :
    h.constituentSign i = χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) := by
  have := h.free i
  have := h.finite i
  have hCeq : C = constituentForm h i := eq_of_two_pow_smul_eq hC (two_pow_smul_constituentForm h i)
  rw [hCeq]
  unfold IsJordanSplitting.constituentSign
  dsimp only
  let d' := d.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis d).symm)
  have hd' : ((constituentForm h i).toMatrix d').det = ((constituentForm h i).toMatrix d).det :=
    det_toMatrix_reindex d _ _
  rw [← hd', det_toMatrix_eq_det_sq_mul_det d' (Module.finBasis ℤ_[2] (N i)), map_mul, map_pow,
    map_mul, map_pow]
  have hP : IsUnit (d'.toMatrix (Module.finBasis ℤ_[2] (N i))).det :=
    Matrix.isUnit_det_of_right_inverse (d'.toMatrix_mul_toMatrix_flip (Module.finBasis ℤ_[2] (N i)))
  have hsq : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x ^ 2 = 1 := by decide
  rw [hsq _ (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hP), one_mul]

/-- Every constituent sign of a dyadic Jordan splitting is `1` or `-1`. -/
theorem IsJordanSplitting.constituentSign_eq_one_or_neg_one [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    h.constituentSign i = 1 ∨ h.constituentSign i = -1 := by
  have := h.free i
  have := h.finite i
  let d := Module.finBasis ℤ_[2] (N i)
  have hdet : IsUnit ((constituentForm h i).toMatrix d).det :=
    d.isUnit_det_of_isPerfPair d _ (isPerfPair_constituentForm h i)
  rw [h.constituentSign_eq (two_pow_smul_constituentForm h i) d]
  exact (by decide : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x = 1 ∨ χ₈ x = -1) _
    (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hdet)

/-- The product of `h.constituentSign` over a finite set `u` is `-1` iff the sum of `4` over the
indices in `u` with sign `-1` equals `4` in `ZMod 8`. -/
theorem IsJordanSplitting.prod_constituentSign_eq_ite [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (u : Finset ℕ) :
    ∏ i ∈ u, h.constituentSign i =
      if (∑ i ∈ u, if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) = 4
      then -1 else 1 := by
  classical
  have h04 : ∀ v : Finset ℕ,
      (∑ i ∈ v, if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) = 0 ∨
      (∑ i ∈ v, if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) = 4 := by
    intro v
    induction v using Finset.induction_on with
    | empty => left; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hkey : ∀ x y : ZMod (2 ^ 3), (x = 0 ∨ x = 4) → (y = 0 ∨ y = 4) →
          x + y = 0 ∨ x + y = 4 := by decide
      refine hkey _ _ ?_ ih
      by_cases hfa : h.constituentSign a = -1 <;> simp [hfa]
  induction u using Finset.induction_on with
  | empty => simp [show (0 : ZMod (2 ^ 3)) ≠ 4 by decide]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    rcases h.constituentSign_eq_one_or_neg_one a with hfa | hfa <;>
      rcases h04 s with hs | hs <;> (rw [hfa, hs]; decide)

/-- `constituentOddity` is independent of the choice of unimodular rescaling and characteristic
vector. -/
theorem IsJordanSplitting.constituentOddity_eq [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {i : ℕ} {C : BilinForm ℤ_[2] (N i)}
    (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i)) {w : N i} (hw : C.IsCharacteristic w) :
    h.constituentOddity hB i = PadicInt.toZModPow 3 (C w w) := by
  have := h.free i
  have hCeq : C = constituentForm h i := eq_of_two_pow_smul_eq hC (two_pow_smul_constituentForm h i)
  rw [hCeq] at hw ⊢
  have : (constituentForm h i).IsPerfPair := isPerfPair_constituentForm h i
  have hCs : (constituentForm h i).IsSymm := isSymm_constituentForm h hB i
  have hw0 := (hCs.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose_spec
  exact (PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp
    (hw.eight_dvd_apply_self_sub_apply_self hCs hw0)).symm

/-- Equal constituents of two Jordan splittings of `B` have equal signs. -/
theorem IsJordanSplitting.constituentSign_eq_of_eq [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N')
    {i : ℕ} (hEq : N' i = N i) : h'.constituentSign i = h.constituentSign i := by
  have := h.free i
  have := h.finite i
  let f : (N' i) ≃ₗ[ℤ_[2]] (N i) := LinearEquiv.ofEq _ _ hEq
  let C := constituentForm h i
  let C' : BilinForm ℤ_[2] (N' i) := C.comp f.toLinearMap f.toLinearMap
  have hC' : (2 : ℤ_[2]) ^ i • C' = B.restrict (N' i) := by
    refine LinearMap.ext₂ fun x y ↦ ?_
    simpa [C', f] using LinearMap.congr_fun₂ (two_pow_smul_constituentForm h i) (f x) (f y)
  let d := Module.finBasis ℤ_[2] (N i)
  let d' := d.map f.symm
  have hmat : C'.toMatrix d' = C.toMatrix d := by ext a b; simp [C', d', toMatrix_apply]
  rw [h'.constituentSign_eq hC' d', h.constituentSign_eq (two_pow_smul_constituentForm h i) d, hmat]

/-- Equal constituents of two Jordan splittings of `B` have equal oddities. -/
theorem IsJordanSplitting.constituentOddity_eq_of_eq [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N')
    (hB : B.IsSymm) {i : ℕ} (hEq : N' i = N i) :
    h'.constituentOddity hB i = h.constituentOddity hB i := by
  have := h.free i
  let f : (N' i) ≃ₗ[ℤ_[2]] (N i) := LinearEquiv.ofEq _ _ hEq
  let C := constituentForm h i
  let C' : BilinForm ℤ_[2] (N' i) := C.comp f.toLinearMap f.toLinearMap
  have hC' : (2 : ℤ_[2]) ^ i • C' = B.restrict (N' i) := by
    refine LinearMap.ext₂ fun x y ↦ ?_
    simpa [C', f] using LinearMap.congr_fun₂ (two_pow_smul_constituentForm h i) (f x) (f y)
  have hCs : C.IsSymm := isSymm_constituentForm h hB i
  have : C.IsPerfPair := isPerfPair_constituentForm h i
  obtain ⟨w, hw⟩ := hCs.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self
  have hw' : C'.IsCharacteristic (f.symm w) := isCharacteristic_iff.mpr fun x ↦ by
    simpa [C'] using isCharacteristic_iff.mp hw (f x)
  rw [h'.constituentOddity_eq hB hC' hw',
    h.constituentOddity_eq hB (two_pow_smul_constituentForm h i) hw]
  simp [C', C]

/-- A zero constituent has sign `1`. -/
theorem IsJordanSplitting.constituentSign_of_eq_bot [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) {i : ℕ} (hbot : N i = ⊥) : h.constituentSign i = 1 := by
  have hsub : Subsingleton (N i) := by rw [hbot]; infer_instance
  let d : Basis (Fin 0) ℤ_[2] (N i) := Basis.empty (N i)
  rw [h.constituentSign_eq (two_pow_smul_constituentForm h i) d,
    show ((constituentForm h i).toMatrix d).det = 1 by simp [Matrix.det_isEmpty], map_one, map_one]

/-- A zero constituent has oddity `0`. -/
theorem IsJordanSplitting.constituentOddity_of_eq_bot [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {i : ℕ} (hbot : N i = ⊥) :
    h.constituentOddity hB i = 0 := by
  have hsub : Subsingleton (N i) := by rw [hbot]; infer_instance
  have hw : (constituentForm h i).IsCharacteristic 0 := isCharacteristic_iff.mpr fun x ↦ by
    rw [Subsingleton.elim x 0]; simp
  rw [h.constituentOddity_eq hB (two_pow_smul_constituentForm h i) hw]
  simp

/-- A type-II constituent has oddity `0`. -/
theorem IsJordanSplitting.constituentOddity_of_even [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) {i : ℕ}
    (heven : ∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) :
    h.constituentOddity hB i = 0 := by
  have h2i : (2 : ℤ_[2]) ^ i ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i two_ne_zero)
  have hw : (constituentForm h i).IsCharacteristic 0 := by
    rw [isCharacteristic_zero_iff]
    intro x
    obtain ⟨c, hc⟩ := heven x x.2
    have hBC : (2 : ℤ_[2]) ^ i * constituentForm h i x x = B x x := by
      simpa using LinearMap.congr_fun₂ (two_pow_smul_constituentForm h i) x x
    exact ⟨c, (mul_cancel_left_mem_nonZeroDivisors h2i).mp (by rw [hBC]; linear_combination hc)⟩
  rw [h.constituentOddity_eq hB (two_pow_smul_constituentForm h i) hw]
  simp

/-- Multiplying the Gram determinant of a constituent by a unit `c` (up to squares) multiplies its
constituent sign by `χ₈(c)`. -/
theorem IsJordanSplitting.constituentSign_eq_mul_of_isSquare_det [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N)
    (h' : B.IsJordanSplitting 2 N') {k : ℕ} {c : ℤ_[2]} (hc : IsUnit c)
    (hsq : ∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
      IsSquare (c * ((B.restrict (N k)).toMatrix d).det * ((B.restrict (N' k)).toMatrix d').det)) :
    h'.constituentSign k = χ₈ (PadicInt.toZModPow 3 c) * h.constituentSign k := by
  have := h.free k; have := h.finite k; have := h'.free k; have := h'.finite k
  have hrank : finrank ℤ_[2] (N k) = finrank ℤ_[2] (N' k) :=
    h.finrank_eq h' two_ne_zero PadicInt.not_isUnit_two k
  let d := Module.finBasis ℤ_[2] (N k)
  let d' := (Module.finBasis ℤ_[2] (N' k)).reindex (finCongr hrank.symm)
  have hC := two_pow_smul_constituentForm h k
  have hC' := two_pow_smul_constituentForm h' k
  have hdetC : IsUnit ((constituentForm h k).toMatrix d).det :=
    d.isUnit_det_of_isPerfPair d _ (isPerfPair_constituentForm h k)
  have hdetC' : IsUnit ((constituentForm h' k).toMatrix d').det :=
    d'.isUnit_det_of_isPerfPair d' _ (isPerfPair_constituentForm h' k)
  have hscale : ((B.restrict (N k)).toMatrix d).det =
      ((2 : ℤ_[2]) ^ k) ^ finrank ℤ_[2] (N k) * ((constituentForm h k).toMatrix d).det := by
    rw [← hC, LinearEquiv.map_smul, Matrix.det_smul, Fintype.card_fin]
  have hscale' : ((B.restrict (N' k)).toMatrix d').det =
      ((2 : ℤ_[2]) ^ k) ^ finrank ℤ_[2] (N k) * ((constituentForm h' k).toMatrix d').det := by
    rw [← hC', LinearEquiv.map_smul, Matrix.det_smul, Fintype.card_fin]
  have hsqC : IsSquare (c * ((constituentForm h k).toMatrix d).det *
      ((constituentForm h' k).toMatrix d').det) := by
    have h0 := hsq (finrank ℤ_[2] (N k)) d d'
    rw [hscale, hscale'] at h0
    have hreg : IsRegular (((2 : ℤ_[2]) ^ k) ^ finrank ℤ_[2] (N k)) :=
      isRegular_iff_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
    refine hreg.isSquare_sq_mul_iff.mp ?_
    convert h0 using 1
    ring
  have hmod := (PadicInt.isSquare_mul_iff_toZModPow_three_eq (hc.mul hdetC) hdetC').mp hsqC
  rw [map_mul] at hmod
  rw [h.constituentSign_eq hC d, h'.constituentSign_eq hC' d', ← hmod, map_mul]

/-- Updating `constituentOddity` from a characteristic-vector congruence modulo `8`. -/
theorem IsJordanSplitting.constituentOddity_eq_add_of_eight_dvd [Module.Free ℤ_[2] M]
    [Module.Finite ℤ_[2] M] {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N)
    (h' : B.IsJordanSplitting 2 N') (hB : B.IsSymm) {k : ℕ} {δ : ℤ_[2]}
    (ho : ∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
      (2 : ℤ_[2]) ^ k • C = B.restrict (N k) → (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
      C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - δ) :
    h'.constituentOddity hB k = h.constituentOddity hB k + PadicInt.toZModPow 3 δ := by
  have := h.free k; have := h'.free k
  have := isPerfPair_constituentForm h k; have := isPerfPair_constituentForm h' k
  obtain ⟨w, hw⟩ := (isSymm_constituentForm h hB k).exists_isCharacteristic
    PadicInt.two_dvd_sq_sub_self
  obtain ⟨w', hw'⟩ := (isSymm_constituentForm h' hB k).exists_isCharacteristic
    PadicInt.two_dvd_sq_sub_self
  have h8 := ho _ _ w w' (two_pow_smul_constituentForm h k) (two_pow_smul_constituentForm h' k)
    hw hw'
  rw [h.constituentOddity_eq hB (two_pow_smul_constituentForm h k) hw,
    h'.constituentOddity_eq hB (two_pow_smul_constituentForm h' k) hw', ← map_add]
  exact (PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp (by convert h8 using 1; ring)).symm

end LinearMap.BilinForm
