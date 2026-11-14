/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Sort
public import TauCeti.Combinatorics.Young.StandardTableau.Reading

/-!
# Row-standard Young tableaux

A **row-standard Young tableau** of shape `μ` is a bijective filling of the cells of `μ` by
`Fin μ.card` whose entries increase strictly from left to right along each row, with no
monotonicity condition down the columns.

Because each row of `μ` has a unique strictly increasing enumeration of any prescribed set of
labels, a row-standard tableau is determined by the map `YoungTableau.rowIndex` assigning each
label to its row (`TauCeti.RowStandardTableau.rowIndex_injective`). Conversely, sorting each row
of an arbitrary `μ`-tableau `t` produces the unique row-standard tableau
`TauCeti.YoungTableau.rowStandardize t` sharing its row assignment. Row-standard tableaux
therefore serve as canonical representatives of `μ`-tabloids and index the standard basis of
Young permutation modules of symmetric groups and type-`A` Iwahori–Hecke algebras.

Relabeling followed by row-standardization equips `RowStandardTableau μ` with a transitive left
`Equiv.Perm (Fin μ.card)`-action. When two consecutive labels `a` and `a + 1` lie in distinct
rows of a row-standard tableau `t`, swapping them leaves every row strictly increasing without
re-sorting (`TauCeti.RowStandardTableau.toTableau_swap_smul_of_rowIndex_ne`).

## Main definitions

* `TauCeti.RowStandardTableau`: bijective cell fillings of shape `μ` strictly increasing along
  each row.
* `TauCeti.StandardYoungTableau.toRowStandard`: the underlying row-standard tableau of a standard
  Young tableau.
* `TauCeti.RowStandardTableau.rowSuperstandard`: the row-superstandard tableau viewed as a
  row-standard tableau.
* `TauCeti.YoungTableau.rowStandardize`: the row-standard tableau obtained by sorting each row of
  a `μ`-tableau.

## Main results

* `TauCeti.RowStandardTableau.rowIndex_injective`: a row-standard tableau is uniquely determined
  by the row of each label.
* `TauCeti.YoungTableau.rowIndex_rowStandardize`: row-standardization preserves the row of every
  label.
* `TauCeti.RowStandardTableau.toTableau_swap_smul_of_rowIndex_ne`: swapping consecutive labels in
  distinct rows preserves row-standardness on the nose.

## References

* R. Dipper and G. James, *Representations of Hecke algebras of general linear groups*,
  Proc. London Math. Soc. (3) 52 (1986), 20–52, Section 3.
* A. Mathas, *Iwahori–Hecke algebras and Schur algebras of the symmetric group*,
  University Lecture Series 15, AMS (1999), Section 3.1.
-/

public section

namespace TauCeti

/-- A row-standard Young tableau of shape `μ` is a bijective labeling of the cells of `μ` by
`Fin μ.card` whose entries increase strictly from left to right along each row. -/
structure RowStandardTableau (μ : YoungDiagram) where
  /-- The underlying Young tableau. -/
  toTableau : YoungTableau μ
  /-- Labels increase strictly from left to right along each row. -/
  row_strict' : ∀ {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ),
    toTableau ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ < toTableau ⟨(i, j₂), hcell⟩

namespace RowStandardTableau

variable {μ : YoungDiagram}

/-- A row-standard tableau coerces to its cell-labeling function `↥μ.cells → Fin μ.card`. -/
instance instFunLike : FunLike (RowStandardTableau μ) ↥μ.cells (Fin μ.card) where
  coe t := t.toTableau
  coe_injective t u h := by
    cases t
    cases u
    congr
    exact Equiv.ext (congrFun h)

/-- The underlying function of a row-standard tableau is its underlying tableau. -/
@[simp]
theorem coe_toTableau (t : RowStandardTableau μ) : ⇑t.toTableau = t :=
  (rfl)

/-- Evaluating the underlying tableau agrees with evaluating the row-standard tableau. -/
@[simp]
theorem toTableau_apply (t : RowStandardTableau μ) (c : ↥μ.cells) : t.toTableau c = t c :=
  (rfl)

/-- Two row-standard tableaux are equal when all of their entries agree. -/
@[ext]
theorem ext {t u : RowStandardTableau μ} (h : ∀ c, t c = u c) : t = u :=
  DFunLike.ext t u h

/-- The entries of a row-standard tableau form a bijection. -/
theorem bijective (t : RowStandardTableau μ) : Function.Bijective t :=
  t.toTableau.bijective

/-- The entries of a row-standard tableau are injective. -/
theorem injective (t : RowStandardTableau μ) : Function.Injective t :=
  t.toTableau.injective

/-- Every label occurs in a row-standard tableau. -/
theorem surjective (t : RowStandardTableau μ) : Function.Surjective t :=
  t.toTableau.surjective

/-- Entries of a row-standard tableau increase strictly from left to right along each row. -/
theorem row_strict (t : RowStandardTableau μ) {i j₁ j₂ : ℕ} (h : j₁ < j₂) (hcell : (i, j₂) ∈ μ) :
    t ⟨(i, j₁), μ.up_left_mem le_rfl h.le hcell⟩ < t ⟨(i, j₂), hcell⟩ :=
  t.row_strict' h hcell

/-- Row-standard tableaux of a fixed shape form a finite type. -/
noncomputable instance instFintype (μ : YoungDiagram) : Fintype (RowStandardTableau μ) :=
  FunLike.fintype (RowStandardTableau μ)

/-! ### Uniqueness from the row assignment -/

/-- Along a common row assignment, the column index in `u` of the `j`-th entry of a row in `t`
is at least `j`. -/
private theorem le_colIndex_of_rowIndex_eq {t u : RowStandardTableau μ}
    (h : YoungTableau.rowIndex t.toTableau = YoungTableau.rowIndex u.toTableau)
    (i j : ℕ) (hc : (i, j) ∈ μ) :
    j ≤ YoungTableau.colIndex u.toTableau (t ⟨(i, j), hc⟩) := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    have hc' : (i, j) ∈ μ := μ.up_left_mem le_rfl (Nat.le_succ j) hc
    have hj := ih hc'
    set k₁ := t ⟨(i, j), hc'⟩
    set k₂ := t ⟨(i, j + 1), hc⟩
    have hlt : k₁ < k₂ := t.row_strict (Nat.lt_succ_self j) hc
    have hr₁ : YoungTableau.rowIndex u.toTableau k₁ = i := by
      rw [← congrFun h k₁]
      exact YoungTableau.rowIndex_apply t.toTableau ⟨(i, j), hc'⟩
    have hr₂ : YoungTableau.rowIndex u.toTableau k₂ = i := by
      rw [← congrFun h k₂]
      exact YoungTableau.rowIndex_apply t.toTableau ⟨(i, j + 1), hc⟩
    have hc₁ : (i, YoungTableau.colIndex u.toTableau k₁) ∈ μ :=
      hr₁ ▸ YoungTableau.rowIndex_colIndex_mem u.toTableau k₁
    have hc₂ : (i, YoungTableau.colIndex u.toTableau k₂) ∈ μ :=
      hr₂ ▸ YoungTableau.rowIndex_colIndex_mem u.toTableau k₂
    have hu₁ : u ⟨(i, YoungTableau.colIndex u.toTableau k₁), hc₁⟩ = k₁ :=
      YoungTableau.rowIndex_colIndex_injective u.toTableau
        (Prod.ext ((YoungTableau.rowIndex_apply _ _).trans hr₁.symm)
          (YoungTableau.colIndex_apply _ _))
    have hu₂ : u ⟨(i, YoungTableau.colIndex u.toTableau k₂), hc₂⟩ = k₂ :=
      YoungTableau.rowIndex_colIndex_injective u.toTableau
        (Prod.ext ((YoungTableau.rowIndex_apply _ _).trans hr₂.symm)
          (YoungTableau.colIndex_apply _ _))
    by_contra hnot
    have hcol : YoungTableau.colIndex u.toTableau k₂ ≤ YoungTableau.colIndex u.toTableau k₁ := by
      omega
    rcases hcol.eq_or_lt with heq | hcol_lt
    · have : k₂ = k₁ := by
        rw [← hu₂, ← hu₁]
        exact congrArg u (Subtype.ext (Prod.ext rfl heq))
      exact hlt.ne' this
    · have hult := u.row_strict hcol_lt hc₁
      rw [hu₂, hu₁] at hult
      exact lt_asymm hlt hult

/-- **A row-standard tableau is uniquely determined by the row of each label.** -/
theorem rowIndex_injective :
    Function.Injective (fun t : RowStandardTableau μ => YoungTableau.rowIndex t.toTableau) := by
  intro t u h
  dsimp only at h
  refine ext fun ⟨⟨i, j⟩, hc⟩ => ?_
  have h₁ := le_colIndex_of_rowIndex_eq h i j hc
  set k := t ⟨(i, j), hc⟩
  have hr : YoungTableau.rowIndex u.toTableau k = i := by
    rw [← congrFun h k]
    exact YoungTableau.rowIndex_apply t.toTableau ⟨(i, j), hc⟩
  have hc' : (i, YoungTableau.colIndex u.toTableau k) ∈ μ :=
    hr ▸ YoungTableau.rowIndex_colIndex_mem u.toTableau k
  have hu : u ⟨(i, YoungTableau.colIndex u.toTableau k), hc'⟩ = k :=
    YoungTableau.rowIndex_colIndex_injective u.toTableau
      (Prod.ext ((YoungTableau.rowIndex_apply _ _).trans hr.symm)
        (YoungTableau.colIndex_apply _ _))
  have h₂ := le_colIndex_of_rowIndex_eq h.symm i (YoungTableau.colIndex u.toTableau k) hc'
  have hcol : YoungTableau.colIndex t.toTableau k = j :=
    YoungTableau.colIndex_apply t.toTableau ⟨(i, j), hc⟩
  rw [hu, hcol] at h₂
  exact (YoungTableau.rowIndex_colIndex_injective u.toTableau
    (Prod.ext ((YoungTableau.rowIndex_apply _ _).trans hr.symm)
      ((YoungTableau.colIndex_apply _ _).trans (le_antisymm h₂ h₁).symm))).symm

/-- Two row-standard tableaux have the same row assignment exactly when they are equal. -/
@[simp]
theorem rowIndex_eq_iff {t u : RowStandardTableau μ} :
    YoungTableau.rowIndex t.toTableau = YoungTableau.rowIndex u.toTableau ↔ t = u :=
  rowIndex_injective.eq_iff

end RowStandardTableau

namespace StandardYoungTableau

variable {μ : YoungDiagram}

/-- Forget column monotonicity to view a standard Young tableau as a row-standard tableau. -/
def toRowStandard (T : StandardYoungTableau μ) : RowStandardTableau μ where
  toTableau := T.toTableau
  row_strict' := T.row_strict'

/-- The underlying tableau of `T.toRowStandard` is `T.toTableau`. -/
@[simp]
theorem toRowStandard_toTableau (T : StandardYoungTableau μ) :
    T.toRowStandard.toTableau = T.toTableau :=
  (rfl)

/-- Evaluating `T.toRowStandard` agrees with evaluating `T`. -/
@[simp]
theorem toRowStandard_apply (T : StandardYoungTableau μ) (c : ↥μ.cells) :
    T.toRowStandard c = T c :=
  (rfl)

/-- Viewing standard Young tableaux as row-standard tableaux is injective. -/
theorem toRowStandard_injective : Function.Injective (toRowStandard (μ := μ)) :=
  fun _ _ h => ext fun c => congrArg (· c) h

end StandardYoungTableau

namespace RowStandardTableau

/-- The row-superstandard tableau of shape `μ`, viewed as a row-standard tableau. -/
noncomputable def rowSuperstandard (μ : YoungDiagram) : RowStandardTableau μ :=
  (StandardYoungTableau.rowSuperstandard μ).toRowStandard

/-- The underlying tableau of `RowStandardTableau.rowSuperstandard` is that of
`StandardYoungTableau.rowSuperstandard`. -/
@[simp]
theorem rowSuperstandard_toTableau (μ : YoungDiagram) :
    (rowSuperstandard μ).toTableau = (StandardYoungTableau.rowSuperstandard μ).toTableau :=
  (rfl)

/-- The row-superstandard tableau labels each cell by its reading index. -/
@[simp]
theorem rowSuperstandard_apply_val (μ : YoungDiagram) (c : ↥μ.cells) :
    (rowSuperstandard μ c).val = YoungDiagram.readingIndex μ c.1 :=
  StandardYoungTableau.rowSuperstandard_apply_val μ c

/-- Every Young diagram carries a row-standard tableau. -/
instance instNonempty (μ : YoungDiagram) : Nonempty (RowStandardTableau μ) :=
  ⟨rowSuperstandard μ⟩

end RowStandardTableau

namespace YoungTableau

variable {μ : YoungDiagram}

/-- The entry in cell `c` obtained after sorting each row of `t` in increasing order. -/
private def rowStandardizeFun (t : YoungTableau μ) (c : ↥μ.cells) : Fin μ.card :=
  (Finset.univ.filter fun y => rowIndex t y = c.1.1).orderEmbOfFin
    (card_filter_rowIndex_eq t c.1.1) ⟨c.1.2, YoungDiagram.mem_iff_lt_rowLen.mp c.2⟩

private theorem rowStandardizeFun_surjective (t : YoungTableau μ) :
    Function.Surjective (rowStandardizeFun t) := by
  intro x
  set i := rowIndex t x
  have hx : x ∈ (Finset.univ.filter fun y => rowIndex t y = i : Set (Fin μ.card)) := by
    simp [i]
  rw [← Finset.range_orderEmbOfFin _ (card_filter_rowIndex_eq t i)] at hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨⟨(i, j.1), YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩, hj⟩

/-- **Row-standardization** of a `μ`-tableau `t`: the unique row-standard tableau obtained by
sorting the labels of each row of `t` into strictly increasing order. -/
noncomputable def rowStandardize (t : YoungTableau μ) : RowStandardTableau μ where
  toTableau := Equiv.ofBijective (rowStandardizeFun t)
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨rowStandardizeFun_surjective t, by simp⟩)
  row_strict' {i j₁ j₂} h hcell := by
    simp only [Equiv.ofBijective_apply]
    exact ((Finset.univ.filter fun y => rowIndex t y = i).orderEmbOfFin
      (card_filter_rowIndex_eq t i)).strictMono (Fin.lt_def.mpr h)

/-- Row-standardization preserves the row of every label. -/
@[simp]
theorem rowIndex_rowStandardize (t : YoungTableau μ) :
    rowIndex (rowStandardize t).toTableau = rowIndex t := by
  funext x
  obtain ⟨c, rfl⟩ := (rowStandardize t).toTableau.surjective x
  rw [rowIndex_apply]
  have hmem : (rowStandardize t).toTableau c ∈
      Finset.univ.filter fun y => rowIndex t y = c.1.1 := by
    rw [rowStandardize, Equiv.ofBijective_apply]
    exact Finset.orderEmbOfFin_mem _ _ _
  exact (Finset.mem_filter.mp hmem).2.symm

/-- Row-standardizing an already row-standard tableau returns it unchanged. -/
@[simp]
theorem rowStandardize_toTableau (t : RowStandardTableau μ) :
    rowStandardize t.toTableau = t :=
  RowStandardTableau.rowIndex_injective (rowIndex_rowStandardize t.toTableau)

/-- Two tableaux have the same row-standardization exactly when they put every label in the
same row. -/
theorem rowStandardize_eq_iff {t u : YoungTableau μ} :
    rowStandardize t = rowStandardize u ↔ rowIndex t = rowIndex u := by
  rw [← RowStandardTableau.rowIndex_eq_iff, rowIndex_rowStandardize, rowIndex_rowStandardize]

end YoungTableau

namespace RowStandardTableau

variable {μ : YoungDiagram}

/-- Permutations of `Fin μ.card` act on row-standard `μ`-tableaux by relabeling and sorting each
row into strictly increasing order. -/
noncomputable instance instSMul :
    SMul (Equiv.Perm (Fin μ.card)) (RowStandardTableau μ) where
  smul σ t := YoungTableau.rowStandardize (YoungTableau.relabel σ t.toTableau)

/-- Acting by `σ` relabels the underlying tableau and row-standardizes the result. -/
theorem smul_def (σ : Equiv.Perm (Fin μ.card)) (t : RowStandardTableau μ) :
    σ • t = YoungTableau.rowStandardize (YoungTableau.relabel σ t.toTableau) :=
  (rfl)

/-- Acting by `σ` moves each label `k` to the row occupied by `σ⁻¹ k` in `t`. -/
@[simp]
theorem rowIndex_smul (σ : Equiv.Perm (Fin μ.card)) (t : RowStandardTableau μ)
    (k : Fin μ.card) :
    YoungTableau.rowIndex (σ • t).toTableau k = YoungTableau.rowIndex t.toTableau (σ⁻¹ k) := by
  rw [smul_def, YoungTableau.rowIndex_rowStandardize, YoungTableau.rowIndex_relabel]

/-- Relabeling followed by row-standardization is a left `Equiv.Perm (Fin μ.card)`-action on
row-standard `μ`-tableaux. -/
noncomputable instance instMulAction :
    MulAction (Equiv.Perm (Fin μ.card)) (RowStandardTableau μ) where
  one_smul t := rowIndex_injective <| by
    dsimp only
    ext k
    rw [rowIndex_smul, inv_one, Equiv.Perm.one_apply]
  mul_smul σ τ t := rowIndex_injective <| by
    dsimp only
    ext k
    simp only [rowIndex_smul, mul_inv_rev, Equiv.Perm.mul_apply]

/-- Row-standardization is equivariant with respect to relabeling. -/
@[simp]
theorem _root_.TauCeti.YoungTableau.rowStandardize_relabel
    (σ : Equiv.Perm (Fin μ.card)) (t : YoungTableau μ) :
    YoungTableau.rowStandardize (YoungTableau.relabel σ t) = σ • YoungTableau.rowStandardize t :=
  rowIndex_injective <| by
    dsimp only
    ext k
    simp

/-- The symmetric group acts transitively on the row-standard tableaux of a fixed shape. -/
theorem exists_smul_eq (t u : RowStandardTableau μ) :
    ∃ σ : Equiv.Perm (Fin μ.card), σ • t = u := by
  obtain ⟨σ, hσ⟩ := YoungTableau.exists_relabel_eq t.toTableau u.toTableau
  exact ⟨σ, by rw [smul_def, hσ, YoungTableau.rowStandardize_toTableau]⟩

/-- Swapping two labels that lie in the same row fixes the row-standard tableau. -/
theorem swap_smul_eq_self_of_rowIndex_eq {t : RowStandardTableau μ} {a b : Fin μ.card}
    (hrow : YoungTableau.rowIndex t.toTableau a = YoungTableau.rowIndex t.toTableau b) :
    Equiv.swap a b • t = t :=
  rowIndex_injective <| by
    dsimp only
    ext k
    rw [rowIndex_smul, Equiv.Perm.inv_def, Equiv.symm_swap]
    rcases eq_or_ne k a with rfl | hka
    · rw [Equiv.swap_apply_left, hrow]
    · rcases eq_or_ne k b with rfl | hkb
      · rw [Equiv.swap_apply_right, hrow]
      · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

/-- **Swapping consecutive labels in distinct rows preserves row-standardness without
re-sorting.** Since no label lies strictly between `a` and `a + 1` and they occupy distinct
rows, relabeling `t` by `Equiv.swap a b` already leaves every row strictly increasing. -/
theorem toTableau_swap_smul_of_rowIndex_ne {t : RowStandardTableau μ} {a b : Fin μ.card}
    (hab : (a : ℕ) + 1 = (b : ℕ))
    (hrow : YoungTableau.rowIndex t.toTableau a ≠ YoungTableau.rowIndex t.toTableau b) :
    (Equiv.swap a b • t).toTableau = YoungTableau.relabel (Equiv.swap a b) t.toTableau := by
  let u : RowStandardTableau μ :=
    { toTableau := YoungTableau.relabel (Equiv.swap a b) t.toTableau
      row_strict' := fun {i j₁ j₂} hlt hcell => by
        simp only [YoungTableau.relabel_apply, toTableau_apply]
        set x := t ⟨(i, j₁), μ.up_left_mem le_rfl hlt.le hcell⟩ with hx_def
        set y := t ⟨(i, j₂), hcell⟩ with hy_def
        have hxy : (x : ℕ) < (y : ℕ) := Fin.lt_def.mp (t.row_strict hlt hcell)
        have hnot : ¬ (x = a ∧ y = b) := by
          rintro ⟨rfl, rfl⟩
          apply hrow
          rw [hx_def, hy_def, ← toTableau_apply, ← toTableau_apply,
            YoungTableau.rowIndex_apply, YoungTableau.rowIndex_apply]
        have hxne : x ≠ a → (x : ℕ) ≠ (a : ℕ) := Fin.val_ne_of_ne
        have hxbne : x ≠ b → (x : ℕ) ≠ (b : ℕ) := Fin.val_ne_of_ne
        have hyne : y ≠ a → (y : ℕ) ≠ (a : ℕ) := Fin.val_ne_of_ne
        have hybne : y ≠ b → (y : ℕ) ≠ (b : ℕ) := Fin.val_ne_of_ne
        rw [Fin.lt_def, Equiv.swap_apply_def, Equiv.swap_apply_def]
        split_ifs <;> omega }
  have hu : Equiv.swap a b • t = u := by
    rw [smul_def]
    exact YoungTableau.rowStandardize_toTableau u
  exact congrArg toTableau hu

end RowStandardTableau

end TauCeti
