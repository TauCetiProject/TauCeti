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
import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Parity
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# Constituent signs and oddities of a dyadic Jordan splitting

For a symmetric bilinear form `B` on a finite free `ℤ_[2]`-module `M` with a Jordan splitting `N`
with respect to `2`, each constituent `N i` has a unique unimodular rescaling `C i` with
`2 ^ i • C i = B.restrict (N i)` and two local Conway–Sloane invariants:

* its **sign** `χ₈(det C i) ∈ {1, -1}`
  (`LinearMap.BilinForm.IsJordanSplitting.constituentSign`), independent of the chosen finite
  basis (`constituentSign_eq`);
* its **oddity** `C i w w mod 8` (`LinearMap.BilinForm.IsJordanSplitting.constituentOddity`), where
  `w` is any characteristic vector of `C i` (`constituentOddity_eq`).

## Main definitions and results

* `LinearMap.BilinForm.IsJordanSplitting.constituentSign`, `constituentOddity`,
  `constituentSign_eq`, `constituentOddity_eq`: definition and independence of choices.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_one_or_neg_one`,
  `sum_if_constituentSign_eq_neg_one`, `prod_constituentSign_eq_ite`: sign values and products.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_of_eq`, `constituentOddity_eq_of_eq`,
  `constituentSign_of_eq_bot`, `constituentOddity_of_eq_bot`, `constituentOddity_of_even`:
  agreement on equal constituents, zero constituents, and type-II constituents.
* `LinearMap.BilinForm.IsJordanSplitting.constituentSign_eq_mul_of_isSquare_det`,
  `constituentOddity_eq_add_of_eight_dvd`: transformation under elementary Jordan-splitting moves.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module ZMod
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M}

/-- Two dyadic Jordan splittings of `B` have the same parity type at every scale. -/
theorem IsJordanSplitting.forall_two_mul_pow_dvd_iff_of_isJordanSplitting
    {N' : ℕ → Submodule ℤ_[2] M} (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N')
    (i : ℕ) : (∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) ↔ ∀ v ∈ N' i, 2 * 2 ^ i ∣ B v v :=
  (h.forall_two_mul_pow_dvd_iff (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl).trans
    (h'.forall_two_mul_pow_dvd_iff (mem_nonZeroDivisors_of_ne_zero two_ne_zero) dvd_rfl).symm

/-- The unimodular rescaling of a Jordan constituent over `ℤ_[2]` is unique. -/
private theorem eq_of_two_pow_smul_eq {k : ℕ} {P : Submodule ℤ_[2] M}
    {C₁ C₂ : BilinForm ℤ_[2] P} (h₁ : (2 : ℤ_[2]) ^ k • C₁ = B.restrict P)
    (h₂ : (2 : ℤ_[2]) ^ k • C₂ = B.restrict P) : C₁ = C₂ := by
  have h2k := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k (two_ne_zero (α := ℤ_[2])))
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

private theorem transport_constituentForm {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) {i : ℕ} (hEq : N' i = N i) :
    let f := LinearEquiv.ofEq _ _ hEq
    (2 : ℤ_[2]) ^ i • ((constituentForm h i).comp f.toLinearMap f.toLinearMap) =
      B.restrict (N' i) := by
  refine LinearMap.ext₂ fun x y ↦ ?_
  simpa using LinearMap.congr_fun₂ (two_pow_smul_constituentForm h i)
    (LinearEquiv.ofEq _ _ hEq x) (LinearEquiv.ofEq _ _ hEq y)

section FreeFinite

variable [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]

/-- The sign `χ₈(det C i) ∈ {1, -1}` of the `i`-th constituent of a dyadic Jordan splitting,
where `C i` is the unimodular rescaling of `B` on `N i`.

By `IsJordanSplitting.constituentSign_eq`, this value is independent of the choice of unimodular
rescaling and finite basis of `N i`. -/
noncomputable def IsJordanSplitting.constituentSign
    (h : B.IsJordanSplitting 2 N) (i : ℕ) : ℤ :=
  have := h.free i; have := h.finite i
  χ₈ (PadicInt.toZModPow 3
    ((constituentForm h i).toMatrix (Module.finBasis ℤ_[2] (N i))).det)

/-- The oddity modulo `8` of the `i`-th constituent of a dyadic Jordan splitting: the residue
modulo `8` of `C i w w` for any characteristic vector `w` of the unimodular rescaling `C i` of `B`
on `N i`.

By `IsJordanSplitting.constituentOddity_eq`, this value is independent of the choice of unimodular
rescaling and characteristic vector. -/
noncomputable def IsJordanSplitting.constituentOddity
    (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm) (i : ℕ) : ZMod (2 ^ 3) :=
  have := h.free i; have := isPerfPair_constituentForm h i
  let w := ((isSymm_constituentForm h hB i).exists_isCharacteristic
    PadicInt.two_dvd_sq_sub_self).choose
  PadicInt.toZModPow 3 (constituentForm h i w w)

/-- `constituentSign` is independent of the choice of unimodular rescaling and finite basis. -/
theorem IsJordanSplitting.constituentSign_eq (h : B.IsJordanSplitting 2 N) {i : ℕ}
    {C : BilinForm ℤ_[2] (N i)} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : Basis ι ℤ_[2] (N i)) :
    h.constituentSign i = χ₈ (PadicInt.toZModPow 3 (C.toMatrix d).det) := by
  have := h.free i; have := h.finite i
  rw [eq_of_two_pow_smul_eq hC (two_pow_smul_constituentForm h i)]
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
  rw [h.constituentSign_eq (two_pow_smul_constituentForm h i) d]
  exact (by decide : ∀ x : ZMod (2 ^ 3), x * x = 1 → χ₈ x = 1 ∨ χ₈ x = -1) _
    (PadicInt.isUnit_iff_toZModPow_three_mul_self.mp
      (d.isUnit_det_of_isPerfPair d _ (isPerfPair_constituentForm h i)))

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
  have hpm : (∏ i ∈ u, h.constituentSign i) = 1 ∨ (∏ i ∈ u, h.constituentSign i) = -1 :=
    Finset.prod_induction _ (fun x ↦ x = 1 ∨ x = -1)
      (fun _ _ ha hb ↦ by rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num)
      (Or.inl rfl) fun i _ ↦ h.constituentSign_eq_one_or_neg_one i
  rcases hpm with hp | hp <;> simp [hp, show (0 : ZMod (2 ^ 3)) ≠ 4 by decide]

/-- `constituentOddity` is independent of the choice of unimodular rescaling and characteristic
vector. -/
theorem IsJordanSplitting.constituentOddity_eq (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {i : ℕ} {C : BilinForm ℤ_[2] (N i)} (hC : (2 : ℤ_[2]) ^ i • C = B.restrict (N i))
    {w : N i} (hw : C.IsCharacteristic w) :
    h.constituentOddity hB i = PadicInt.toZModPow 3 (C w w) := by
  have := h.free i
  rw [eq_of_two_pow_smul_eq hC (two_pow_smul_constituentForm h i)] at hw ⊢
  have := isPerfPair_constituentForm h i
  have hCs := isSymm_constituentForm h hB i
  have hw0 := (hCs.exists_isCharacteristic PadicInt.two_dvd_sq_sub_self).choose_spec
  exact (PadicInt.eight_dvd_sub_iff_toZModPow_three_eq.mp
    (hw.eight_dvd_apply_self_sub_apply_self hCs hw0)).symm

/-- Equal constituents of two Jordan splittings of `B` have equal signs. -/
theorem IsJordanSplitting.constituentSign_eq_of_eq {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') {i : ℕ} (hEq : N' i = N i) :
    h'.constituentSign i = h.constituentSign i := by
  have := h.free i; have := h.finite i
  let f := LinearEquiv.ofEq _ _ hEq
  let d := Module.finBasis ℤ_[2] (N i)
  rw [h'.constituentSign_eq (transport_constituentForm h hEq) (d.map f.symm),
    h.constituentSign_eq (two_pow_smul_constituentForm h i) d]
  congr 3

/-- Equal constituents of two Jordan splittings of `B` have equal oddities. -/
theorem IsJordanSplitting.constituentOddity_eq_of_eq {N' : ℕ → Submodule ℤ_[2] M}
    (h : B.IsJordanSplitting 2 N) (h' : B.IsJordanSplitting 2 N') (hB : B.IsSymm) {i : ℕ}
    (hEq : N' i = N i) : h'.constituentOddity hB i = h.constituentOddity hB i := by
  have := h.free i; have := isPerfPair_constituentForm h i
  let f := LinearEquiv.ofEq _ _ hEq
  obtain ⟨w, hw⟩ := (isSymm_constituentForm h hB i).exists_isCharacteristic
    PadicInt.two_dvd_sq_sub_self
  have hw' : ((constituentForm h i).comp f.toLinearMap f.toLinearMap).IsCharacteristic (f.symm w) :=
    isCharacteristic_iff.mpr fun x ↦ by simpa using isCharacteristic_iff.mp hw (f x)
  rw [h'.constituentOddity_eq hB (transport_constituentForm h hEq) hw',
    h.constituentOddity_eq hB (two_pow_smul_constituentForm h i) hw]
  exact congrArg (fun x ↦ PadicInt.toZModPow 3 (constituentForm h i x x)) (f.apply_symm_apply w)

/-- A zero constituent has sign `1`. -/
theorem IsJordanSplitting.constituentSign_of_eq_bot (h : B.IsJordanSplitting 2 N) {i : ℕ}
    (hbot : N i = ⊥) : h.constituentSign i = 1 := by
  have : Subsingleton (N i) := by rw [hbot]; infer_instance
  let e : Basis Empty ℤ_[2] (N i) := Basis.empty (N i)
  rw [h.constituentSign_eq (two_pow_smul_constituentForm h i) e,
    show ((constituentForm h i).toMatrix e).det = 1 by simp [Matrix.det_isEmpty],
    map_one, map_one]

/-- A type-II constituent has oddity `0`. -/
theorem IsJordanSplitting.constituentOddity_of_even (h : B.IsJordanSplitting 2 N) (hB : B.IsSymm)
    {i : ℕ} (heven : ∀ v ∈ N i, 2 * 2 ^ i ∣ B v v) : h.constituentOddity hB i = 0 := by
  have h2i := mem_nonZeroDivisors_of_ne_zero (pow_ne_zero i (two_ne_zero (α := ℤ_[2])))
  have hw : (constituentForm h i).IsCharacteristic 0 := isCharacteristic_zero_iff.mpr fun x ↦ by
    obtain ⟨c, hc⟩ := heven x x.2
    have hBC : (2 : ℤ_[2]) ^ i * constituentForm h i x x = B x x := by
      simpa using LinearMap.congr_fun₂ (two_pow_smul_constituentForm h i) x x
    exact ⟨c, (mul_cancel_left_mem_nonZeroDivisors h2i).mp (by rw [hBC]; linear_combination hc)⟩
  simp [h.constituentOddity_eq hB (two_pow_smul_constituentForm h i) hw]

/-- A zero constituent has oddity `0`. -/
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
  have hC := two_pow_smul_constituentForm h k
  have hC' := two_pow_smul_constituentForm h' k
  have hdetC : IsUnit ((constituentForm h k).toMatrix d).det :=
    d.isUnit_det_of_isPerfPair d _ (isPerfPair_constituentForm h k)
  have hdetC' : IsUnit ((constituentForm h' k).toMatrix d').det :=
    d'.isUnit_det_of_isPerfPair d' _ (isPerfPair_constituentForm h' k)
  have h0 := hsq (finrank ℤ_[2] (N k)) d d'
  rw [← hC, ← hC', LinearEquiv.map_smul, LinearEquiv.map_smul, Matrix.det_smul, Matrix.det_smul,
    Fintype.card_fin] at h0
  have hreg : IsRegular (((2 : ℤ_[2]) ^ k) ^ finrank ℤ_[2] (N k)) :=
    isRegular_iff_ne_zero.mpr (pow_ne_zero _ (pow_ne_zero _ two_ne_zero))
  have hsqC : IsSquare (c * ((constituentForm h k).toMatrix d).det *
      ((constituentForm h' k).toMatrix d').det) :=
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

end FreeFinite

end LinearMap.BilinForm
