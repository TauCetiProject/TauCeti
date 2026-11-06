/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Finset.Inversions
public import TauCeti.GroupTheory.Perm.Coxeter
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Bruhat

/-!
# Unitriangular coordinates on the Bruhat cells of `GLₙ`

Let `B` be the upper-triangular subgroup of `GL ι R`, `U` its upper-unitriangular subgroup, and
`P_w = TauCeti.permutationGL w` the permutation matrix of `w : Equiv.Perm ι`. The **Bruhat cell**
of `w` is the image `B P_w B / B` of the double coset `B P_w B` in the flag quotient `GL ι R ⧸ B`.
This file parametrizes it, as a set, by the matrix entries at the inversions of `w⁻¹`, so that
over a finite field with `q` elements it has `q ^ ℓ(w)` points. Only this set-level
parametrization and point count are established; no variety structure or geometric dimension of
the cell is claimed.

The coordinates come from two subgroups of `U`, cut out by which entries above the diagonal may be
nonzero. A pair of indices `i < j` is an *inversion* of `w⁻¹` when `w⁻¹ j < w⁻¹ i`; these are the
pairs in `Finset.univ.inversions w.symm`.

* `U_w = TauCeti.unitriangularInversionGroup R w` consists of the upper-unitriangular matrices
  whose entries above the diagonal vanish off the inversions. It is `U ∩ P_w B⁻ P_w⁻¹`, for `B⁻`
  the lower-triangular matrices.
* `U'_w = TauCeti.unitriangularStabilizerGroup R w` consists of those whose entries above the
  diagonal vanish on the inversions. It is `U ∩ P_w B P_w⁻¹`, the stabilizer in `U` of the point
  `P_w B` of the flag quotient.

These two subgroups meet trivially, and every upper-unitriangular matrix factors as `j * h` with
`j ∈ U_w` and `h ∈ U'_w`. It follows that every element of `B P_w B` is uniquely
`j * P_w * b` with `j ∈ U_w` and `b ∈ B`, the **normal form** of the Bruhat cell. Consequently
`j ↦ j P_w B` is a bijection from `U_w` onto the Bruhat cell, and reading off the entries at the
inversions identifies `U_w` with `R ^ {inversions of w⁻¹}`. All of this holds over any
commutative ring.

For `ι = Fin n` the number of inversions is the Coxeter length of `w`
(`TauCeti.permCoxeterSystem_length_eq_card_inversion`), which gives the point-count formula
`|B P_w B / B| = q ^ ℓ(w)` over a finite ring with `q` elements. Over a field the cells cover the
flag quotient, by the Bruhat decomposition `TauCeti.exists_mem_doubleCoset_permutationGL`.

## Main definitions

* `TauCeti.unitriangularInversionGroup R w`: the subgroup `U_w = U ∩ P_w B⁻ P_w⁻¹`.
* `TauCeti.unitriangularStabilizerGroup R w`: the subgroup `U'_w = U ∩ P_w B P_w⁻¹`.
* `TauCeti.bruhatCell R w`: the Bruhat cell `B P_w B / B` in `GL ι R ⧸ B`.
* `TauCeti.unitriangularInversionGroupEquivBruhatCell R w`: the bijection `j ↦ j P_w B` from `U_w`
  onto the Bruhat cell.
* `TauCeti.unitriangularInversionGroupEquivFun R w`: the coordinates of `U_w`, its entries at the
  inversions of `w⁻¹`; the `@[simp]` lemmas `unitriangularInversionGroupEquivFun_symm_apply_*`
  evaluate the entries of the matrix with prescribed coordinates.

## Main results

* `TauCeti.unitriangularStabilizerGroup_eq_inf_stabilizer`: `U'_w` is the stabilizer in `U` of
  the point `P_w B`.
* `TauCeti.unitriangularInversionGroup_inf_unitriangularStabilizerGroup` and
  `TauCeti.coe_unitriangularInversionGroup_mul_coe_unitriangularStabilizerGroup`: `U_w ∩ U'_w = 1`
  and `U_w U'_w = U`.
* `TauCeti.mem_doubleCoset_permutationGL_iff` and
  `TauCeti.eq_and_eq_of_mul_permutationGL_mul_eq`: the normal form `j * P_w * b` of the elements
  of `B P_w B`, and its uniqueness.
* `TauCeti.mem_bruhatCell_iff`: the points of the Bruhat cell are the cosets `j P_w B`, `j ∈ U_w`.
* `TauCeti.natCard_bruhatCell` and `TauCeti.natCard_bruhatCell_eq_pow_length`: the Bruhat cell of
  `w` has `|R| ^ N` points, for `N` the number of inversions of `w⁻¹`; for `ι = Fin n` this is
  `|R| ^ ℓ(w)`.
* `TauCeti.iUnion_bruhatCell`: over a field the Bruhat cells cover the flag quotient.

## References

* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 28.4, the normal form in `G`.
* T. A. Springer, *Linear Algebraic Groups*, second edition (1998), Section 8.3.
-/

public section

open Matrix
open scoped Pointwise

namespace TauCeti

noncomputable section

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

section CommRing

variable (R : Type*) [CommRing R]

/-! ### The two unitriangular subgroups attached to a permutation -/

/-- The subgroup `U_w = U ∩ P_w B⁻ P_w⁻¹` of upper-unitriangular matrices `g` for which the
conjugate `P_w⁻¹ g P_w` is lower triangular, that is, upper triangular for the reversed order
`ιᵒᵈ`. Its entries above the diagonal vanish off the inversions of `w⁻¹`
(`TauCeti.mem_unitriangularInversionGroup_iff`). -/
def unitriangularInversionGroup (w : Equiv.Perm ι) : Subgroup (GL ι R) :=
  upperUnitriangularGroup ι R ⊓
    (upperTriangularGroup ιᵒᵈ R).comap (MulAut.conj (permutationGL (k := R) w)⁻¹).toMonoidHom

/-- The subgroup `U'_w = U ∩ P_w B P_w⁻¹` of upper-unitriangular matrices `g` for which the
conjugate `P_w⁻¹ g P_w` is upper triangular. Its entries above the diagonal vanish on the
inversions of `w⁻¹` (`TauCeti.mem_unitriangularStabilizerGroup_iff`), and it is the stabilizer
in `U` of the point `P_w B` of the flag quotient
(`TauCeti.unitriangularStabilizerGroup_eq_inf_stabilizer`). -/
def unitriangularStabilizerGroup (w : Equiv.Perm ι) : Subgroup (GL ι R) :=
  upperUnitriangularGroup ι R ⊓
    (upperTriangularGroup ι R).comap (MulAut.conj (permutationGL (k := R) w)⁻¹).toMonoidHom

variable {R}

/-- **Membership in `U_w`**: an upper-unitriangular matrix whose entries vanish at every pair
`i < j` that `w⁻¹` keeps in order, so that its free entries sit at the inversions of `w⁻¹`. -/
@[simp]
theorem mem_unitriangularInversionGroup_iff {w : Equiv.Perm ι} {g : GL ι R} :
    g ∈ unitriangularInversionGroup R w ↔ (g : Matrix ι ι R).IsUpperUnitriangular ∧
      ∀ i j, i < j → w.symm i < w.symm j → (g : Matrix ι ι R) i j = 0 := by
  -- Upper triangularity over `ιᵒᵈ` is lower triangularity over `ι` by definition.
  have hB : g ∈ (upperTriangularGroup ιᵒᵈ R).comap
      (MulAut.conj (permutationGL (k := R) w)⁻¹).toMonoidHom ↔
      (((permutationGL (k := R) w)⁻¹ * g * permutationGL (k := R) w : GL ι R) :
        Matrix ι ι R).IsLowerTriangular :=
    Subgroup.mem_comap.trans UpperTriangularGroup.mem_iff
  rw [unitriangularInversionGroup, Subgroup.mem_inf, UpperUnitriangularGroup.mem_iff, hB]
  exact and_congr_right fun hg ↦ isLowerTriangular_permutationGL_inv_mul_mul_iff
    hg.isUpperTriangular

/-- **Membership in `U'_w`**: an upper-unitriangular matrix whose entries vanish at the inversions
of `w⁻¹`. -/
@[simp]
theorem mem_unitriangularStabilizerGroup_iff {w : Equiv.Perm ι} {g : GL ι R} :
    g ∈ unitriangularStabilizerGroup R w ↔ (g : Matrix ι ι R).IsUpperUnitriangular ∧
      ∀ i j, i < j → w.symm j < w.symm i → (g : Matrix ι ι R) i j = 0 := by
  simp only [unitriangularStabilizerGroup, Subgroup.mem_inf, UpperUnitriangularGroup.mem_iff,
    Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    UpperTriangularGroup.permutationGL_inv_mul_mul_permutationGL_mem_iff]
  refine and_congr_right fun hg ↦ ⟨fun h i j _ hw ↦ by simpa using h hw, fun h a b hba ↦ ?_⟩
  rcases lt_trichotomy (w a) (w b) with hlt | heq | hgt
  · exact h _ _ hlt (by simpa using hba)
  · exact absurd (w.injective heq) hba.ne'
  · exact hg.isUpperTriangular hgt

/-- `U_w` consists of upper-unitriangular matrices. -/
theorem unitriangularInversionGroup_le_upperUnitriangularGroup (w : Equiv.Perm ι) :
    unitriangularInversionGroup R w ≤ upperUnitriangularGroup ι R :=
  fun _ hg ↦ UpperUnitriangularGroup.mem_iff.mpr (mem_unitriangularInversionGroup_iff.mp hg).1

/-- `U'_w` consists of upper-unitriangular matrices. -/
theorem unitriangularStabilizerGroup_le_upperUnitriangularGroup (w : Equiv.Perm ι) :
    unitriangularStabilizerGroup R w ≤ upperUnitriangularGroup ι R :=
  inf_le_left

/-- `U'_w` is the stabilizer in `U` of the point `P_w B` of the flag quotient. -/
theorem unitriangularStabilizerGroup_eq_inf_stabilizer (w : Equiv.Perm ι) :
    unitriangularStabilizerGroup R w = upperUnitriangularGroup ι R ⊓
      MulAction.stabilizer (GL ι R)
        (QuotientGroup.mk (permutationGL (k := R) w) : GL ι R ⧸ upperTriangularGroup ι R) := by
  ext g
  simp only [unitriangularStabilizerGroup, Subgroup.mem_inf, Subgroup.mem_comap,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, MulAction.mem_stabilizer_iff,
    MulAction.Quotient.smul_mk, QuotientGroup.eq]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [mul_assoc] using (upperTriangularGroup ι R).inv_mem h
  · simpa [mul_assoc] using (upperTriangularGroup ι R).inv_mem h

/-- `U_w` meets the conjugate `P_w B P_w⁻¹` of the upper-triangular group trivially: an element of
both has no nonzero entry above the diagonal. -/
theorem unitriangularInversionGroup_inf_comap_upperTriangularGroup (w : Equiv.Perm ι) :
    unitriangularInversionGroup R w ⊓ (upperTriangularGroup ι R).comap
      (MulAut.conj (permutationGL (k := R) w)⁻¹).toMonoidHom = ⊥ := by
  refine eq_bot_iff.mpr fun g hg' ↦ ?_
  obtain ⟨hg, hgB⟩ := Subgroup.mem_inf.mp hg'
  obtain ⟨hU, hinv⟩ := mem_unitriangularInversionGroup_iff.mp hg
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    UpperTriangularGroup.permutationGL_inv_mul_mul_permutationGL_mem_iff] at hgB
  rw [Subgroup.mem_bot]
  refine Units.ext (hU.ext isUpperUnitriangular_one fun i j hij ↦ ?_)
  rw [Units.val_one, one_apply_ne hij.ne]
  rcases lt_or_gt_of_ne (w.symm.injective.ne hij.ne) with hw | hw
  · exact hinv i j hij hw
  · simpa using hgB hw

/-- `U_w ∩ U'_w = 1`. -/
theorem unitriangularInversionGroup_inf_unitriangularStabilizerGroup (w : Equiv.Perm ι) :
    unitriangularInversionGroup R w ⊓ unitriangularStabilizerGroup R w = ⊥ :=
  eq_bot_iff.mpr <| (inf_le_inf_left _ inf_le_right).trans
    (unitriangularInversionGroup_inf_comap_upperTriangularGroup w).le

/-! ### The factorization `U = U_w U'_w` -/

omit [Fintype ι] in
/-- Replacing the column `a` of a matrix of `U'_w`-shape by a column that is `1` at `a` and
supported on the rows `l < a` with `w⁻¹ l < w⁻¹ a`, together with `a`, keeps the shape. -/
private theorem updateCol_shape (w : Equiv.Perm ι) {H : Matrix ι ι R}
    (hH : H.IsUpperUnitriangular) (hHw : ∀ i j, i < j → w.symm j < w.symm i → H i j = 0) (a : ι)
    (y : ι → R) (S : Finset ι) (hS : ∀ l ∈ S, l < a ∧ w.symm l < w.symm a)
    (hya : y a = 1) (hy : ∀ l, l ∉ S → l ≠ a → y l = 0) :
    (H.updateCol a y).IsUpperUnitriangular ∧
      ∀ i j, i < j → w.symm j < w.symm i → H.updateCol a y i j = 0 := by
  refine ⟨(isUpperUnitriangular_def _).mpr ⟨fun i j hji ↦ ?_, fun i ↦ ?_⟩, fun i j hij hw ↦ ?_⟩
  · have hji : j < i := hji
    rw [updateCol_apply]
    split_ifs with hja
    · subst hja
      exact hy _ (fun h ↦ (hS _ h).1.asymm hji) hji.ne'
    · exact hH.isUpperTriangular hji
  · rw [updateCol_apply]
    split_ifs with hia
    · rw [hia, hya]
    · exact hH.apply_diag i
  · rw [updateCol_apply]
    split_ifs with hja
    · subst hja
      exact hy _ (fun h ↦ (hS _ h).2.asymm hw) hij.ne
    · exact hHw i j hij hw

/-- **The column step of the factorization.** Given factors `J` of `U_w`-shape and `H` of
`U'_w`-shape, the column `a` of both can be replaced so that the shapes are kept and the column
`a` of the product becomes the column `a` of any upper-unitriangular `u`. -/
private theorem exists_updateCol_mul_updateCol (w : Equiv.Perm ι) {u J H : Matrix ι ι R}
    (hu : u.IsUpperUnitriangular) (hJ : J.IsUpperUnitriangular)
    (hJw : ∀ i j, i < j → w.symm i < w.symm j → J i j = 0)
    (hH : H.IsUpperUnitriangular) (hHw : ∀ i j, i < j → w.symm j < w.symm i → H i j = 0) (a : ι) :
    ∃ x y : ι → R, (J.updateCol a x).IsUpperUnitriangular ∧
      (∀ i j, i < j → w.symm i < w.symm j → J.updateCol a x i j = 0) ∧
      (H.updateCol a y).IsUpperUnitriangular ∧
      (∀ i j, i < j → w.symm j < w.symm i → H.updateCol a y i j = 0) ∧
      ∀ i, (J.updateCol a x * H.updateCol a y) i a = u i a := by
  -- The new column `y` of `H` is supported on a set `S` of rows, where it solves a unitriangular
  -- system; the new column `x` of `J` is the remainder. After the construction come the shape
  -- conditions on both factors and the computation of the column `a` of the product.
  -- `S` is the set of rows where the new column of `H` may be nonzero above the diagonal.
  let S : Finset ι := {l | l < a ∧ w.symm l < w.symm a}
  have hS {l : ι} : l ∈ S ↔ l < a ∧ w.symm l < w.symm a := by simp [S]
  have haS : a ∉ S := fun h ↦ (hS.mp h).1.false
  obtain ⟨y, hya, hy', hyS⟩ :=
    Matrix.exists_sum_mul_eq_of_isUpperUnitriangular hJ (fun i ↦ u i a) a S haS
  let σ : ι → R := fun i ↦ ∑ l ∈ S, J i l * y l
  -- The new column of `J` is then read off.
  let x : ι → R := fun i ↦ if i = a then 1 else if i ∈ S then 0 else u i a - σ i
  have hy {l : ι} (hl : l ∉ S) (hla : l ≠ a) : y l = 0 := hy' l hl hla
  have hσ {i : ι} (hai : a ≤ i) : σ i = 0 :=
    Finset.sum_eq_zero fun l hl ↦ by
      rw [hJ.isUpperTriangular ((hS.mp hl).1.trans_le hai), zero_mul]
  have hσS {i : ι} (hi : i ∈ S) : σ i = u i a := hyS i hi
  have hprod (i : ι) : (J.updateCol a x * H.updateCol a y) i a = x i + σ i :=
    Matrix.updateCol_mul_updateCol_apply_self a x y S haS hya hy' i
  obtain ⟨hH', hHw'⟩ := updateCol_shape w hH hHw a y S (fun l hl ↦ hS.mp hl) hya hy'
  refine ⟨x, y, (isUpperUnitriangular_def _).mpr ⟨fun i j hji ↦ ?_, fun i ↦ ?_⟩,
    fun i j hij hw ↦ ?_, hH', hHw', fun i ↦ ?_⟩
  · -- `J.updateCol a x` is upper triangular.
    have hji : j < i := hji
    rw [updateCol_apply]
    split_ifs with hja
    · subst hja
      have hi : i ∉ S := fun h ↦ (hS.mp h).1.asymm hji
      simp [x, hji.ne', hi, hu.isUpperTriangular hji, hσ hji.le]
    · exact hJ.isUpperTriangular hji
  · rw [updateCol_apply]
    split_ifs with hia
    · simp [x, hia]
    · exact hJ.apply_diag i
  · rw [updateCol_apply]
    split_ifs with hja
    · subst hja
      simp [x, hij.ne, hS.mpr ⟨hij, hw⟩]
    · exact hJw i j hij hw
  · -- The column `a` of the product is the column `a` of `u`.
    rw [hprod]
    by_cases hia : i = a
    · subst hia
      simp [x, hσ le_rfl, hu.apply_diag]
    · by_cases hi : i ∈ S
      · simp [x, hia, hi, hσS hi]
      · simp [x, hia, hi]

/-- **Every upper-unitriangular matrix factors as a matrix of `U_w`-shape times a matrix of
`U'_w`-shape.** -/
private theorem exists_mul_eq_of_isUpperUnitriangular (w : Equiv.Perm ι) {u : Matrix ι ι R}
    (hu : u.IsUpperUnitriangular) :
    ∃ J H : Matrix ι ι R, J.IsUpperUnitriangular ∧
      (∀ i j, i < j → w.symm i < w.symm j → J i j = 0) ∧ H.IsUpperUnitriangular ∧
      (∀ i j, i < j → w.symm j < w.symm i → H i j = 0) ∧ J * H = u := by
  -- The factors are built column by column with `exists_updateCol_mul_updateCol`, in increasing
  -- order of columns, so that the earlier columns of the product are kept.
  suffices h : ∀ s : Finset ι, ∃ J H : Matrix ι ι R, J.IsUpperUnitriangular ∧
      (∀ i j, i < j → w.symm i < w.symm j → J i j = 0) ∧ H.IsUpperUnitriangular ∧
      (∀ i j, i < j → w.symm j < w.symm i → H i j = 0) ∧ ∀ i, ∀ c ∈ s, (J * H) i c = u i c by
    obtain ⟨J, H, hJ, hJw, hH, hHw, hJH⟩ := h Finset.univ
    exact ⟨J, H, hJ, hJw, hH, hHw, Matrix.ext fun i c ↦ hJH i c (Finset.mem_univ c)⟩
  intro s
  induction s using Finset.induction_on_max with
  | empty =>
    exact ⟨1, 1, isUpperUnitriangular_one, fun i j hij _ ↦ one_apply_ne hij.ne,
      isUpperUnitriangular_one, fun i j hij _ ↦ one_apply_ne hij.ne, by simp⟩
  | insert a s hs ih =>
    obtain ⟨J, H, hJ, hJw, hH, hHw, hJH⟩ := ih
    obtain ⟨x, y, hJ', hJw', hH', hHw', hcol⟩ :=
      exists_updateCol_mul_updateCol w hu hJ hJw hH hHw a
    refine ⟨J.updateCol a x, H.updateCol a y, hJ', hJw', hH', hHw', fun i c hc ↦ ?_⟩
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact hcol i
    · rw [updateCol_mul_updateCol_apply_of_lt hH.isUpperTriangular (hs c hc), hJH i c hc]

/-- **`U = U_w U'_w`**: every upper-unitriangular matrix is a product `j * h` with `j ∈ U_w` and
`h ∈ U'_w`. Together with `TauCeti.unitriangularInversionGroup_inf_unitriangularStabilizerGroup`
the factorization is unique. -/
theorem coe_unitriangularInversionGroup_mul_coe_unitriangularStabilizerGroup
    (w : Equiv.Perm ι) :
    (unitriangularInversionGroup R w : Set (GL ι R)) * (unitriangularStabilizerGroup R w :
      Set (GL ι R)) = upperUnitriangularGroup ι R := by
  refine subset_antisymm ?_ fun u hu ↦ ?_
  · rintro _ ⟨j, hj, h, hh, rfl⟩
    exact (upperUnitriangularGroup ι R).mul_mem
      (unitriangularInversionGroup_le_upperUnitriangularGroup w hj)
      (unitriangularStabilizerGroup_le_upperUnitriangularGroup w hh)
  · obtain ⟨J, H, hJ, hJw, hH, hHw, hJH⟩ := exists_mul_eq_of_isUpperUnitriangular w
      (UpperUnitriangularGroup.mem_iff.mp hu)
    refine ⟨hJ.toGL, mem_unitriangularInversionGroup_iff.mpr ?_, hH.toGL,
      mem_unitriangularStabilizerGroup_iff.mpr ?_, Units.ext ?_⟩
    · simpa using ⟨hJ, hJw⟩
    · simpa using ⟨hH, hHw⟩
    · simpa using hJH

/-! ### The normal form of the elements of `B P_w B` -/

/-- **The normal form of the Bruhat cell.** An element of `GL ι R` lies in the double coset
`B P_w B` exactly when it is `j * P_w * b` with `j ∈ U_w` and `b` upper triangular. -/
theorem mem_doubleCoset_permutationGL_iff (w : Equiv.Perm ι) {g : GL ι R} :
    g ∈ DoubleCoset.doubleCoset (permutationGL (k := R) w) (upperTriangularGroup ι R)
        (upperTriangularGroup ι R) ↔
      ∃ j ∈ unitriangularInversionGroup R w, ∃ b ∈ upperTriangularGroup ι R,
        g = j * permutationGL (k := R) w * b := by
  set P := permutationGL (k := R) w
  constructor
  · intro hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
    -- Split off the diagonal of `b₁` and factor its unitriangular part as `j * h`.
    set t := UpperTriangularGroup.diag ⟨b₁, hb₁⟩
    have hu : b₁ * (diagGL t)⁻¹ ∈ upperUnitriangularGroup ι R :=
      (UpperTriangularGroup.mul_inv_diagGL_mem_upperUnitriangularGroup_iff ⟨b₁, hb₁⟩ t).mpr rfl
    rw [← SetLike.mem_coe,
      ← coe_unitriangularInversionGroup_mul_coe_unitriangularStabilizerGroup w] at hu
    obtain ⟨j, hj, h, hh, hjh⟩ := Set.mem_mul.mp hu
    -- Both `h` and the diagonal factor move across `P` into the upper-triangular group.
    have hhB : P⁻¹ * h * P ∈ upperTriangularGroup ι R := by
      simpa [P] using (Subgroup.mem_inf.mp hh).2
    have htB : P⁻¹ * diagGL t * P ∈ upperTriangularGroup ι R := by
      rw [UpperTriangularGroup.permutationGL_inv_mul_mul_permutationGL_mem_iff]
      intro a b hba
      simp [diagGL_apply, w.injective.ne hba.ne']
    refine ⟨j, hj, P⁻¹ * h * P * (P⁻¹ * diagGL t * P * b₂),
      mul_mem hhB (mul_mem htB hb₂), ?_⟩
    have hb₁ : b₁ = j * h * diagGL t := by rw [hjh, inv_mul_cancel_right]
    rw [hb₁]
    group
  · rintro ⟨j, hj, b, hb, rfl⟩
    exact DoubleCoset.mem_doubleCoset.mpr ⟨j,
      UpperTriangularGroup.upperUnitriangularGroup_le_upperTriangularGroup
        (unitriangularInversionGroup_le_upperUnitriangularGroup w hj), b, hb, rfl⟩

/-- **Uniqueness of the normal form**: if `j * P_w * b = j' * P_w * b'` with `j, j' ∈ U_w` and
`b, b'` upper triangular, then `j = j'` and `b = b'`. -/
theorem eq_and_eq_of_mul_permutationGL_mul_eq {w : Equiv.Perm ι} {j j' b b' : GL ι R}
    (hj : j ∈ unitriangularInversionGroup R w) (hj' : j' ∈ unitriangularInversionGroup R w)
    (hb : b ∈ upperTriangularGroup ι R) (hb' : b' ∈ upperTriangularGroup ι R)
    (h : j * permutationGL (k := R) w * b = j' * permutationGL (k := R) w * b') :
    j = j' ∧ b = b' := by
  set P := permutationGL (k := R) w
  have hj_eq : j = j' * P * b' * b⁻¹ * P⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq, h]
  -- `j'⁻¹ * j` lies in `U_w` and in `P_w B P_w⁻¹`, so it is trivial.
  have hmem : j'⁻¹ * j ∈ unitriangularInversionGroup R w ⊓ (upperTriangularGroup ι R).comap
      (MulAut.conj P⁻¹).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hj') hj, ?_⟩
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    convert mul_mem hb' (inv_mem hb) using 1
    rw [hj_eq]
    group
  rw [unitriangularInversionGroup_inf_comap_upperTriangularGroup, Subgroup.mem_bot,
    inv_mul_eq_one] at hmem
  subst hmem
  exact ⟨rfl, mul_left_cancel h⟩

/-! ### The parametrization of the Bruhat cell by inversion coordinates -/

variable (R) in
/-- The **Bruhat cell** of `w`: the image `B P_w B / B` of the double coset `B P_w B` in the flag
quotient `GL ι R ⧸ B`. -/
def bruhatCell (w : Equiv.Perm ι) : Set (GL ι R ⧸ upperTriangularGroup ι R) :=
  QuotientGroup.mk '' DoubleCoset.doubleCoset (permutationGL (k := R) w)
    (upperTriangularGroup ι R) (upperTriangularGroup ι R)

/-- The coset `j P_w B` of an element `j ∈ U_w` lies in the Bruhat cell of `w`. -/
theorem mk_mul_permutationGL_mem_bruhatCell {w : Equiv.Perm ι} {j : GL ι R}
    (hj : j ∈ unitriangularInversionGroup R w) :
    (QuotientGroup.mk (j * permutationGL (k := R) w) : GL ι R ⧸ upperTriangularGroup ι R) ∈
      bruhatCell R w :=
  ⟨_, (mem_doubleCoset_permutationGL_iff w).mpr ⟨j, hj, 1, one_mem _, (mul_one _).symm⟩, rfl⟩

/-- **The points of the Bruhat cell**: they are the cosets `j P_w B` with `j ∈ U_w`. -/
theorem mem_bruhatCell_iff {w : Equiv.Perm ι} {x : GL ι R ⧸ upperTriangularGroup ι R} :
    x ∈ bruhatCell R w ↔
      ∃ j ∈ unitriangularInversionGroup R w,
        QuotientGroup.mk (j * permutationGL (k := R) w) = x := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨j, hj, b, hb, rfl⟩ := (mem_doubleCoset_permutationGL_iff w).mp hg
    exact ⟨j, hj, QuotientGroup.eq.mpr (by rwa [inv_mul_cancel_left])⟩
  · rintro ⟨j, hj, rfl⟩
    exact mk_mul_permutationGL_mem_bruhatCell hj

variable (R) in
/-- **The Bruhat cell is parametrized by `U_w`**: `j ↦ j P_w B` is a bijection from `U_w` onto
the Bruhat cell `B P_w B / B`. -/
def unitriangularInversionGroupEquivBruhatCell (w : Equiv.Perm ι) :
    unitriangularInversionGroup R w ≃ bruhatCell R w :=
  Equiv.ofBijective
    (fun j ↦ ⟨QuotientGroup.mk (j * permutationGL (k := R) w),
      mk_mul_permutationGL_mem_bruhatCell j.2⟩)
    ⟨fun j j' hjj' ↦ Subtype.ext (eq_and_eq_of_mul_permutationGL_mul_eq j.2 j'.2
        (QuotientGroup.eq.mp (congrArg Subtype.val hjj')) (one_mem _) (by group)).1,
      fun ⟨x, hx⟩ ↦ by
        obtain ⟨j, hj, rfl⟩ := mem_bruhatCell_iff.mp hx
        exact ⟨⟨j, hj⟩, rfl⟩⟩

/-- The point of the Bruhat cell attached to `j ∈ U_w` is the coset `j P_w B`. -/
@[simp]
theorem coe_unitriangularInversionGroupEquivBruhatCell_apply (w : Equiv.Perm ι)
    (j : unitriangularInversionGroup R w) :
    (unitriangularInversionGroupEquivBruhatCell R w j : GL ι R ⧸ upperTriangularGroup ι R) =
      QuotientGroup.mk ((j : GL ι R) * permutationGL (k := R) w) :=
  (rfl)

/-- The upper-unitriangular matrix with the prescribed entries `c` at the inversions of `w⁻¹`
and zero entries elsewhere above the diagonal. -/
private def inversionMatrix (w : Equiv.Perm ι) (c : Finset.univ.inversions ⇑w.symm → R) :
    Matrix ι ι R :=
  fun i j ↦ if i = j then 1 else if h : (i, j) ∈ Finset.univ.inversions ⇑w.symm then c ⟨_, h⟩
    else 0

private theorem isUpperUnitriangular_inversionMatrix (w : Equiv.Perm ι)
    (c : Finset.univ.inversions ⇑w.symm → R) : (inversionMatrix w c).IsUpperUnitriangular := by
  refine (isUpperUnitriangular_def _).mpr ⟨fun i j hji ↦ ?_, fun i ↦ by simp [inversionMatrix]⟩
  have hji : j < i := hji
  simp [inversionMatrix, hji.ne', hji.asymm]

private theorem inversionMatrix_mem (w : Equiv.Perm ι) (c : Finset.univ.inversions ⇑w.symm → R) :
    (isUpperUnitriangular_inversionMatrix w c).toGL ∈ unitriangularInversionGroup R w := by
  refine mem_unitriangularInversionGroup_iff.mpr ⟨by
    simpa using isUpperUnitriangular_inversionMatrix w c, fun i j hij hw ↦ ?_⟩
  simpa [inversionMatrix, hij.ne] using fun _ hq ↦ absurd hq hw.asymm

variable (R) in
/-- **The coordinates of `U_w`**: an element of `U_w` is determined by its entries at the
inversions of `w⁻¹`, and these entries are arbitrary. -/
def unitriangularInversionGroupEquivFun (w : Equiv.Perm ι) :
    unitriangularInversionGroup R w ≃ (Finset.univ.inversions ⇑w.symm → R) where
  toFun j p := ((j : GL ι R) : Matrix ι ι R) p.1.1 p.1.2
  invFun c := ⟨_, inversionMatrix_mem w c⟩
  left_inv j := by
    obtain ⟨hU, hw⟩ := mem_unitriangularInversionGroup_iff.mp j.2
    refine Subtype.ext (Units.ext ?_)
    simp only [IsUpperUnitriangular.coe_toGL]
    refine (isUpperUnitriangular_inversionMatrix w _).ext hU fun a b hab ↦ ?_
    by_cases hinv : (a, b) ∈ Finset.univ.inversions ⇑w.symm
    · simp only [inversionMatrix, hab.ne, hinv, ↓reduceIte, ↓reduceDIte]
    · have hlt : w.symm a < w.symm b := by
        refine lt_of_le_of_ne (not_lt.mp fun h ↦ hinv ?_) (w.symm.injective.ne hab.ne)
        simpa using ⟨hab, h⟩
      simp only [inversionMatrix, hab.ne, hinv, ↓reduceIte, ↓reduceDIte, hw a b hab hlt]
  right_inv c := by
    funext p
    have hp := (Finset.mem_inversions.mp p.2).2.2.1
    simp [inversionMatrix, hp.ne]

/-- The coordinates of `j ∈ U_w` are its entries at the inversions of `w⁻¹`. -/
@[simp]
theorem unitriangularInversionGroupEquivFun_apply (w : Equiv.Perm ι)
    (j : unitriangularInversionGroup R w) (p : Finset.univ.inversions ⇑w.symm) :
    unitriangularInversionGroupEquivFun R w j p = ((j : GL ι R) : Matrix ι ι R) p.1.1 p.1.2 :=
  (rfl)

/-- The element of `U_w` with coordinates `c` has the entry `c (i, j)` at an inversion `(i, j)` of
`w⁻¹`. -/
@[simp]
theorem unitriangularInversionGroupEquivFun_symm_apply_of_mem_inversions (w : Equiv.Perm ι)
    (c : Finset.univ.inversions ⇑w.symm → R) {i j : ι}
    (h : (i, j) ∈ Finset.univ.inversions ⇑w.symm) :
    (((unitriangularInversionGroupEquivFun R w).symm c : GL ι R) : Matrix ι ι R) i j =
      c ⟨(i, j), h⟩ := by
  have hij : i ≠ j := (Finset.mem_inversions.mp h).2.2.1.ne
  simp [unitriangularInversionGroupEquivFun, inversionMatrix, hij, h]

/-- The element of `U_w` with coordinates `c` has the diagonal entries `1`. -/
@[simp]
theorem unitriangularInversionGroupEquivFun_symm_apply_self (w : Equiv.Perm ι)
    (c : Finset.univ.inversions ⇑w.symm → R) (i : ι) :
    (((unitriangularInversionGroupEquivFun R w).symm c : GL ι R) : Matrix ι ι R) i i = 1 := by
  simp [unitriangularInversionGroupEquivFun, inversionMatrix]

/-- The element of `U_w` with coordinates `c` has the entry `0` off the diagonal and off the
inversions of `w⁻¹`. -/
@[simp]
theorem unitriangularInversionGroupEquivFun_symm_apply_of_notMem_inversions (w : Equiv.Perm ι)
    (c : Finset.univ.inversions ⇑w.symm → R) {i j : ι} (hij : i ≠ j)
    (h : (i, j) ∉ Finset.univ.inversions ⇑w.symm) :
    (((unitriangularInversionGroupEquivFun R w).symm c : GL ι R) : Matrix ι ι R) i j = 0 := by
  simp [unitriangularInversionGroupEquivFun, inversionMatrix, hij, h]

/-- **The number of points of the Bruhat cell**: it is `|R| ^ N`, where `N` is the number of
inversions of `w⁻¹`. Cardinalities are `Nat.card`, so for an infinite ring and `N > 0` both sides
are `0`. -/
theorem natCard_bruhatCell (w : Equiv.Perm ι) :
    Nat.card (bruhatCell R w) = Nat.card R ^ (Finset.univ.inversions ⇑w.symm).card := by
  rw [Nat.card_congr ((unitriangularInversionGroupEquivBruhatCell R w).symm.trans
    (unitriangularInversionGroupEquivFun R w)), Nat.card_fun, Nat.card_eq_finsetCard]

/-- **The point-count formula**: the Bruhat cell of a permutation `w` of `Fin n` has
`|R| ^ ℓ(w)` points, for `ℓ` the Coxeter length. -/
theorem natCard_bruhatCell_eq_pow_length {n : ℕ} (w : Equiv.Perm (Fin n)) :
    Nat.card (bruhatCell R w) = Nat.card R ^ (permCoxeterSystem n).length w := by
  rw [natCard_bruhatCell, ← (permCoxeterSystem n).length_inv,
    permCoxeterSystem_length_eq_card_inversion, Finset.inversions_univ, Equiv.Perm.coe_inv]

end CommRing

/-- **The Bruhat cells cover the flag quotient** of `GLₘ` over a field. -/
theorem iUnion_bruhatCell {k : Type*} [Field k] {m : ℕ} :
    ⋃ w : Equiv.Perm (Fin m), bruhatCell k w = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨w, hw⟩ := exists_mem_doubleCoset_permutationGL g
  exact Set.mem_iUnion.mpr ⟨w, g, hw, rfl⟩

end

end TauCeti
