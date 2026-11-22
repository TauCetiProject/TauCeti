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
import TauCeti.Algebra.BigOperators.Ring.Finset
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.NumberTheory.Padics.SerreSigns
import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# Constituent signs and oddities of a dyadic Jordan splitting

For a symmetric bilinear form `B` on a finite free `ℤ_[2]`-module `M` with a Jordan splitting `N`
with respect to `2`, each constituent `N i` has a unique unimodular rescaling `C i` with
`2 ^ i • C i = B.restrict (N i)`
(`LinearMap.BilinForm.IsJordanSplitting.constituentForm`) and two local Conway–Sloane invariants:

* its **sign** `χ₈(det C i) ∈ {1, -1}`
  (`LinearMap.BilinForm.IsJordanSplitting.constituentSign`), independent of the chosen finite
  basis (`constituentSign_eq`);
* its **oddity** `C i w w mod 8` (`LinearMap.BilinForm.IsJordanSplitting.constituentOddity`), where
  `w` is any characteristic vector of `C i` (`constituentOddity_eq`).

## Main definitions and results

* `LinearMap.BilinForm.IsJordanSplitting.constituentForm`, `two_pow_smul_constituentForm`,
  `eq_constituentForm_iff`, `isPerfPair_constituentForm`, `isSymm_constituentForm`,
  `constituentCharVec`, `isCharacteristic_constituentCharVec`: canonical unimodular rescaling and
  characteristic vector for each Jordan constituent.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign`, `constituentOddity`,
  `constituentSign_eq`, `constituentOddity_eq`: definition and independence of choices.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_one_or_neg_one`,
  `sum_if_constituentSign_eq_neg_one`, `prod_constituentSign_eq_ite`: sign values and products.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_of_eq`, `constituentOddity_eq_of_eq`,
  `constituentSign_of_eq_bot`, `constituentOddity_of_eq_bot`, `constituentOddity_of_even`:
  agreement on equal constituents, zero constituents, and type-II constituents.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_mul_of_isSquare_det`,
  `constituentOddity_eq_add_of_eight_dvd`, `constituentSign_eq_neg_of_isSquare_five`,
  `constituentSign_eq_neg_and_oddity_eq_add_four_of_isSquare_five`: transformation under elementary
  Jordan-splitting moves.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-- Canonical unimodular rescaling of the `i`-th constituent of a dyadic Jordan splitting,
satisfying `2 ^ i • h.constituentForm i = B.restrict (N i)`. -/
noncomputable def IsJordanSplitting.constituentForm (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    BilinForm ℤ_[2] (N i) :=
  (isModular_def.mp (h.isModular i)).choose

/-- The `i`-th canonical constituent form rescales by `2 ^ i` to `B.restrict (N i)`. -/
theorem IsJordanSplitting.two_pow_smul_constituentForm (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    (2 : ℤ_[2]) ^ i • h.constituentForm i = B.restrict (N i) :=
  (isModular_def.mp (h.isModular i)).choose_spec.1

/-- Characterization of the canonical constituent form: `C` equals `h.constituentForm i` iff
`2 ^ i • C = B.restrict (N i)`. -/
theorem IsJordanSplitting.eq_constituentForm_iff (h : B.IsJordanSplitting 2 N) {i : ℕ}
    {C : BilinForm ℤ_[2] (N i)} :
    (2 : ℤ_[2]) ^ i • C = B.restrict (N i) ↔ C = h.constituentForm i :=
  ⟨fun hC ↦ eq_of_smul_eq (PadicInt.isLeftRegular_p_pow i) hC
      (h.two_pow_smul_constituentForm i),
    fun hC ↦ hC ▸ h.two_pow_smul_constituentForm i⟩

/-- The canonical constituent form of a dyadic Jordan splitting is a perfect pairing. -/
theorem IsJordanSplitting.isPerfPair_constituentForm (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    (h.constituentForm i).IsPerfPair :=
  (isModular_def.mp (h.isModular i)).choose_spec.2

/-- The canonical constituent form of a symmetric dyadic Jordan splitting is symmetric. -/
theorem IsJordanSplitting.isSymm_constituentForm (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    (i : ℕ) : (h.constituentForm i).IsSymm :=
  (IsSMulRegular.of_ne_zero (pow_ne_zero i two_ne_zero)).isSymm_smul_iff.mp
    ((h.two_pow_smul_constituentForm i).symm ▸ hB.restrict (N i))

private theorem transport_constituentForm {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) {i : ℕ} (hEq : N' i = N i) :
    let f := LinearEquiv.ofEq _ _ hEq
    (2 : ℤ_[2]) ^ i • ((h.constituentForm i).comp f.toLinearMap f.toLinearMap) =
      B.restrict (N' i) := by
  refine LinearMap.ext₂ fun x y ↦ ?_
  simpa using LinearMap.congr_fun₂ (h.two_pow_smul_constituentForm i)
    (LinearEquiv.ofEq _ _ hEq x) (LinearEquiv.ofEq _ _ hEq y)

section FreeFinite

variable [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]

/-- Canonical characteristic vector for the `i`-th canonical constituent form of a symmetric
dyadic Jordan splitting. -/
noncomputable def IsJordanSplitting.constituentCharVec (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) (i : ℕ) : N i :=
  have := h.free i; have := h.isPerfPair_constituentForm i
  ((h.isSymm_constituentForm hB i).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose

/-- `h.constituentCharVec hB i` is characteristic for `h.constituentForm i`. -/
theorem IsJordanSplitting.isCharacteristic_constituentCharVec (h : B.IsJordanSplitting 2 N)
    (hB : B.IsSymm) (i : ℕ) :
    (h.constituentForm i).IsCharacteristic (h.constituentCharVec hB i) :=
  have := h.free i; have := h.isPerfPair_constituentForm i
  ((h.isSymm_constituentForm hB i).exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose_spec

/-- The sign `χ₈(det C i) ∈ {1, -1}` of the `i`-th constituent of a dyadic Jordan splitting,
where `C i` is the unimodular rescaling of `B` on `N i`.

By `IsJordanSplitting.constituentSign_eq`, this value is independent of the choice of unimodular
rescaling and finite basis of `N i`. -/
noncomputable def IsJordanSplitting.constituentSign
    (h : B.IsJordanSplitting 2 N) (i : ℕ) : ℤ :=
  have := h.free i; have := h.finite i
  χ₈ (PadicInt.toZModPow 3
    ((h.constituentForm i).toMatrix (Module.finBasis ℤ_[2] (N i))).det)

/-- The oddity modulo `8` of the `i`-th constituent of a dyadic Jordan splitting: the residue
modulo `8` of `C i w w` for any characteristic vector `w` of the unimodular rescaling `C i` of `B`
on `N i`.

By `IsJordanSplitting.constituentOddity_eq`, this value is independent of the choice of unimodular
rescaling and characteristic vector. -/
noncomputable def IsJordanSplitting.constituentOddity
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) (i : ℕ) : ZMod (2 ^ 3) :=
  PadicInt.toZModPow 3 (h.constituentForm i (h.constituentCharVec hB i) (h.constituentCharVec hB i))

/-- `constituentSign` is independent of the choice of unimodular rescaling and finite basis. -/
theorem IsJordanSplitting.constituentSign_eq (h : B.IsJordanSplitting 2 N) {i : ℕ}
    {C : BilinForm ℤ_[2] (N i)} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : Basis ι ℤ_[2] (N i)) :
    h.constituentSign i = χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) := by
  have := h.free i; have := h.finite i
  rw [h.eq_constituentForm_iff.mp hC]
  unfold IsJordanSplitting.constituentSign; dsimp only
  let d' := d.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis d).symm)
  rw [← det_toMatrix_reindex d (Fintype.equivFinOfCardEq (finrank_eq_card_basis d).symm),
    det_toMatrix_eq_det_sq_mul_det d' (Module.finBasis ℤ_[2] (N i)), map_mul, map_pow, map_mul,
    map_pow]
  have hP := Matrix.isUnit_det_of_right_inverse
    (d'.toMatrix_mul_toMatrix_flip (Module.finBasis ℤ_[2] (N i)))
  rw [(by decide : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x ^ 2 = 1) _
    (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp hP), one_mul]

/-- Every constituent sign of a dyadic Jordan splitting is `1` or `-1`. -/
theorem IsJordanSplitting.constituentSign_eq_one_or_neg_one
    (h : B.IsJordanSplitting 2 N) (i : ℕ) :
    h.constituentSign i = 1 ∨ h.constituentSign i = -1 := by
  have := h.free i; have := h.finite i
  let d := Module.finBasis ℤ_[2] (N i)
  rw [h.constituentSign_eq (h.two_pow_smul_constituentForm i) d]
  exact (by decide : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x = 1 ∨ χ₈ x = -1) _
    (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp
      (d.isUnit_det_of_isPerfPair d _ (h.isPerfPair_constituentForm i)))

/-- The sum of `4` in `ZMod 8` over constituents in `u` of sign `-1` equals `4` iff the product of
their signs is `-1`. -/
theorem IsJordanSplitting.sum_if_constituentSign_eq_neg_one
    (h : B.IsJordanSplitting 2 N) (u : Finset ℕ) :
    (∑ i ∈ u, if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
      if ∏ i ∈ u, h.constituentSign i = -1 then 4 else 0 := by
  classical
  suffices ((∏ i ∈ u, h.constituentSign i) = 1 ∨ (∏ i ∈ u, h.constituentSign i) = -1) ∧
      (∑ i ∈ u, if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) =
        if ∏ i ∈ u, h.constituentSign i = -1 then 4 else 0 from this.2
  induction u using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih.2]
    rcases h.constituentSign_eq_one_or_neg_one a with h1 | h1 <;>
      rcases ih.1 with h2 | h2 <;> (rw [h1, h2]; decide)

/-- The product of `h.constituentSign` over a finite set `u` is `-1` iff the sum of `4` over the
indices in `u` with sign `-1` equals `4` in `ZMod 8`. -/
theorem IsJordanSplitting.prod_constituentSign_eq_ite
    (h : B.IsJordanSplitting 2 N) (u : Finset ℕ) :
    ∏ i ∈ u, h.constituentSign i =
      if (∑ i ∈ u, if h.constituentSign i = -1 then (4 : ZMod (2 ^ 3)) else 0) = 4
      then -1 else 1 := by
  rw [h.sum_if_constituentSign_eq_neg_one]
  have hpm := Finset.prod_eq_one_or_neg_one u fun i _ ↦ h.constituentSign_eq_one_or_neg_one i
  have h04 : (0 : ZMod (2 ^ 3)) ≠ 4 := by decide
  rcases hpm with hp | hp <;> simp [hp, h04]

/-- `constituentOddity` is independent of the choice of unimodular rescaling and characteristic
vector. -/
theorem IsJordanSplitting.constituentOddity_eq (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {i : ℕ} {C : BilinForm ℤ_[2] (N i)} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    {w : N i} (hw : C.IsCharacteristic w) :
    h.constituentOddity hB i = PadicInt.toZModPow 3 (C w w) := by
  have := h.free i
  rw [h.eq_constituentForm_iff.mp hC] at hw ⊢
  have := h.isPerfPair_constituentForm i
  exact (PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp
    (hw.eight_dvd_apply_self_sub_apply_self (h.isSymm_constituentForm hB i)
      (h.isCharacteristic_constituentCharVec hB i))).symm

/-- Equal constituents of two Jordan splittings of `B` have equal signs. -/
theorem IsJordanSplitting.constituentSign_eq_of_eq {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') {i : ℕ} (hEq : N' i = N i) :
    h'.constituentSign i = h.constituentSign i := by
  have := h.free i; have := h.finite i
  let f := LinearEquiv.ofEq _ _ hEq
  let d := Module.finBasis ℤ_[2] (N i)
  have hmat : ((h.constituentForm i).comp f.toLinearMap f.toLinearMap).toMatrix (d.map f.symm) =
      (h.constituentForm i).toMatrix d := by
    ext a b
    simp [toMatrix_apply, comp_apply]
  rw [h'.constituentSign_eq (transport_constituentForm h hEq) (d.map f.symm),
    h.constituentSign_eq (h.two_pow_smul_constituentForm i) d, hmat]

/-- Equal constituents of two Jordan splittings of `B` have equal oddities. -/
theorem IsJordanSplitting.constituentOddity_eq_of_eq {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') (hB : B.IsSymm) {i : ℕ}
    (hEq : N' i = N i) : h'.constituentOddity hB i = h.constituentOddity hB i := by
  have := h.free i
  let f := LinearEquiv.ofEq _ _ hEq
  let w := h.constituentCharVec hB i
  have hw := h.isCharacteristic_constituentCharVec hB i
  have hw' : ((h.constituentForm i).comp f.toLinearMap f.toLinearMap).IsCharacteristic (f.symm w) :=
    isCharacteristic_iff.mpr fun x ↦ by simpa using isCharacteristic_iff.mp hw (f x)
  rw [h'.constituentOddity_eq hB (transport_constituentForm h hEq) hw',
    h.constituentOddity_eq hB (h.two_pow_smul_constituentForm i) hw]
  exact congrArg (fun x ↦ PadicInt.toZModPow 3 (h.constituentForm i x x)) (f.apply_symm_apply w)

/-- A zero constituent has sign `1`. -/
@[simp]
theorem IsJordanSplitting.constituentSign_of_eq_bot (h : B.IsJordanSplitting 2 N) {i : ℕ}
    (hbot : N i = ⊥) : h.constituentSign i = 1 := by
  have : Subsingleton (N i) := by rw [hbot]; infer_instance
  let e : Basis Empty ℤ_[2] (N i) := Basis.empty (N i)
  have hdet : ((h.constituentForm i).toMatrix e).det = 1 := Matrix.det_isEmpty
  rw [h.constituentSign_eq (h.two_pow_smul_constituentForm i) e, hdet, map_one, map_one]

/-- A type-II constituent has oddity `0`. -/
theorem IsJordanSplitting.constituentOddity_of_even (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {i : ℕ} (heven : ∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) : h.constituentOddity hB i = 0 := by
  have hw : (h.constituentForm i).IsCharacteristic 0 :=
    isCharacteristic_zero_iff.mpr
      ((forall_dvd_restrict_iff_of_smul_eq (PadicInt.isLeftRegular_p_pow i)
        (h.two_pow_smul_constituentForm i) 2).mpr heven)
  simp [h.constituentOddity_eq hB (h.two_pow_smul_constituentForm i) hw]

/-- A zero constituent has oddity `0`. -/
@[simp]
theorem IsJordanSplitting.constituentOddity_of_eq_bot (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {i : ℕ} (hbot : N i = ⊥) : h.constituentOddity hB i = 0 :=
  h.constituentOddity_of_even hB fun v hv ↦ by
    have hv0 : v = 0 := by simpa [hbot] using hv
    simp [hv0]

/-- Multiplying the Gram determinant of a constituent by a unit `c` (up to squares) multiplies its
constituent sign by `χ₈(c)`. -/
theorem IsJordanSplitting.constituentSign_eq_mul_of_isSquare_det {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') {k : ℕ} {c : ℤ_[2]}
    (hc : IsUnit c)
    (hsq : ∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
      IsSquare (c * ((B.restrict (N k)).toMatrix d).det * ((B.restrict (N' k)).toMatrix d').det)) :
    h'.constituentSign k = χ₈ (PadicInt.toZModPow 3 c) * h.constituentSign k := by
  have := h.free k; have := h.finite k; have := h'.free k; have := h'.finite k
  have hrank := h.finrank_eq h' two_ne_zero PadicInt.not_isUnit_two k
  let d := Module.finBasis ℤ_[2] (N k)
  let d' := (Module.finBasis ℤ_[2] (N' k)).reindex (finCongr hrank.symm)
  have hC := h.two_pow_smul_constituentForm k
  have hC' := h'.two_pow_smul_constituentForm k
  have hdetC : IsUnit ((h.constituentForm k).toMatrix d).det :=
    d.isUnit_det_of_isPerfPair d _ (h.isPerfPair_constituentForm k)
  have hdetC' : IsUnit ((h'.constituentForm k).toMatrix d').det :=
    d'.isUnit_det_of_isPerfPair d' _ (h'.isPerfPair_constituentForm k)
  have h0 := hsq (finrank ℤ_[2] (N k)) d d'
  rw [← hC, ← hC', LinearEquiv.map_smul, LinearEquiv.map_smul, Matrix.det_smul, Matrix.det_smul,
    Fintype.card_fin] at h0
  have hreg : IsRegular (((2 : ℤ_[2]) ^ k) ^ finrank ℤ_[2] (N k)) :=
    isRegular_iff_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
  have hsqC : IsSquare (c * ((h.constituentForm k).toMatrix d).det *
      ((h'.constituentForm k).toMatrix d').det) :=
    hreg.isSquare_sq_mul_iff.mp (by convert h0 using 1; ring)
  have hmod := (PadicInt.isSquare_mul_iff_toZModPow_three_eq (hc.mul hdetC) hdetC').mp hsqC
  rw [map_mul] at hmod
  rw [h.constituentSign_eq hC d, h'.constituentSign_eq hC' d', ← hmod, map_mul]

/-- Updating `constituentOddity` from a characteristic-vector congruence modulo `8`. -/
theorem IsJordanSplitting.constituentOddity_eq_add_of_eight_dvd {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') (hB : B.IsSymm) {k : ℕ}
    {δ : ℤ_[2]}
    (ho : ∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
      (2 : ℤ_[2]) ^ k • C = B.restrict (N k) →
      (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
      C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - δ) :
    h'.constituentOddity hB k = h.constituentOddity hB k + PadicInt.toZModPow 3 δ := by
  have h8 := ho _ _ (h.constituentCharVec hB k) (h'.constituentCharVec hB k)
    (h.two_pow_smul_constituentForm k) (h'.two_pow_smul_constituentForm k)
    (h.isCharacteristic_constituentCharVec hB k) (h'.isCharacteristic_constituentCharVec hB k)
  rw [h.constituentOddity_eq hB (h.two_pow_smul_constituentForm k)
      (h.isCharacteristic_constituentCharVec hB k),
    h'.constituentOddity_eq hB (h'.two_pow_smul_constituentForm k)
      (h'.isCharacteristic_constituentCharVec hB k),
    ← map_add]
  exact (PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp (by convert h8 using 1; ring)).symm

/-- Multiplying the Gram determinant of a constituent by `5` (up to squares) negates its
constituent sign. -/
theorem IsJordanSplitting.constituentSign_eq_neg_of_isSquare_five
    {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N')
    {k : ℕ}
    (hdk : ∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
      IsSquare (5 * ((B.restrict (N k)).toMatrix d).det * ((B.restrict (N' k)).toMatrix d').det)) :
    h'.constituentSign k = -h.constituentSign k := by
  have hsk := h.constituentSign_eq_mul_of_isSquare_det h' TauCeti.isUnit_five_padicInt hdk
  have hχ5 : χ₈ (PadicInt.toZModPow 3 (5 : ℤ_[2])) = -1 := by rw [map_ofNat]; decide
  rwa [hχ5, neg_one_mul] at hsk

/-- Updating both `constituentSign` (negated) and `constituentOddity` (shifted by `4` modulo `8`)
under a `5`-twist Jordan-splitting move. -/
theorem IsJordanSplitting.constituentSign_eq_neg_and_oddity_eq_add_four_of_isSquare_five
    {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N')
    (hB : B.IsSymm) {k : ℕ}
    (hdk : ∀ (n : ℕ) (d : Basis (Fin n) ℤ_[2] (N k)) (d' : Basis (Fin n) ℤ_[2] (N' k)),
      IsSquare (5 * ((B.restrict (N k)).toMatrix d).det * ((B.restrict (N' k)).toMatrix d').det))
    (hok : ∀ (C : BilinForm ℤ_[2] (N k)) (C' : BilinForm ℤ_[2] (N' k)) (w : N k) (w' : N' k),
      (2 : ℤ_[2]) ^ k • C = B.restrict (N k) →
      (2 : ℤ_[2]) ^ k • C' = B.restrict (N' k) →
      C.IsCharacteristic w → C'.IsCharacteristic w' → (8 : ℤ_[2]) ∣ C' w' w' - C w w - 4) :
    h'.constituentSign k = -h.constituentSign k ∧
      h'.constituentOddity hB k = h.constituentOddity hB k + 4 :=
  ⟨h.constituentSign_eq_neg_of_isSquare_five h' hdk,
    by simpa [map_ofNat] using h.constituentOddity_eq_add_of_eight_dvd h' hB (δ := 4) hok⟩

end FreeFinite

end LinearMap.BilinForm
