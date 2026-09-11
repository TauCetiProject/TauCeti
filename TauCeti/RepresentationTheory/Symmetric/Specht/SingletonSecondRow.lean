/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Partition.Basic
public import TauCeti.GroupTheory.GroupAction.Transitive
public import TauCeti.RepresentationTheory.Rep.OfMulAction
public import TauCeti.RepresentationTheory.Symmetric.Specht.Module
public import TauCeti.RepresentationTheory.Symmetric.Standard

/-!
# The Specht module of the shape `(n-1, 1)` is the standard representation

The third of the named small irreducible representations of `Sₙ`, beside the trivial
representation `S^{(n)}` and the sign representation `S^{(1ⁿ)}` of
`TauCeti.RepresentationTheory.Symmetric.Specht.Extremes`, is the `(n-1)`-dimensional **standard
representation** `S^{(n-1,1)}`.  Unlike those two it is not a line, and identifying it needs the
tabloid combinatorics of a shape with two rows.  This file supplies that combinatorics and proves
the identification.

The shape is pinned by its row lengths: `μ.rowLen 1 = 1` says the second row is a single cell, and
`μ.rowLen 2 = 0` says there is no third row, so `μ` is a shape `(m, 1)`; the partition `(n+1, 1)`
of `n+2` is `TauCeti.Nat.Partition.singletonSecondRow n`, and both hypotheses hold for its diagram.
Everything is stated on the diagram, where the polytabloids live, and specialized to that partition
at the end.

Three facts about such a shape drive the whole file, and each is elementary once the two row
lengths are fixed.  The second row holds a single label, `TauCeti.YoungTableau.secondRowLabel`; the
first column holds exactly two, that one and `TauCeti.YoungTableau.firstColumnLabel`; and every
other column holds exactly one.  Hence the column group of a tableau is
`{1, (firstColumnLabel secondRowLabel)}` (`TauCeti.YoungTableau.mem_colSubgroup_iff`), so the
antisymmetrization defining the polytabloid has just two terms and

`e_t = {t} - (a b) · {t}`

is a **difference of two tabloid basis vectors**
(`TauCeti.YoungTableau.polytabloid_eq_single_sub_single`).  Differences of basis vectors span
exactly the vectors whose coefficients sum to zero, which is what
`TauCeti.augmentationSubrepresentation` is; and conversely *every* such difference is a
polytabloid, because a tableau can be relabelled, without moving the label of its short row, so
that the top of its first column carries any prescribed other label.  The Specht module is
therefore the augmentation subrepresentation of the Young permutation module
(`TauCeti.spechtSubrepresentation_eq_augmentationSubrepresentation`), which is what
`TauCeti.standardRepresentation` is by definition.

To read that on the labels rather than on the tabloids, the file also names the tabloids of such a
shape by the labels: a tabloid splits the labels into the long row and a single short one, so it is
named by the label of the short row, equivariantly
(`TauCeti.labelTabloidEquiv`, `TauCeti.labelTabloid_smul`).  Transporting `ℚ[Fin μ.card]` along
that naming carries the standard representation of `Fin μ.card` onto the Specht module
(`TauCeti.standardRepresentationEquivSpechtSubrepresentation`), and the dimension `μ.card - 1`
follows.

The parallel statement one level up, `M^{(n-1,1)} = triv ⊕ standard`, is proved for the partition
`(n+1, 1)` itself in
`TauCeti.RepresentationTheory.Symmetric.PermutationModule.SingletonSecondRow`; that file names the
tabloids by the labels through the Young subgroup, which is the stabilizer of a point, whereas the
naming here is built from the tableau combinatorics, so that it is available on the diagram the
polytabloids are indexed by.

## Main definitions

* `TauCeti.YoungTableau.secondRowLabel` and `TauCeti.YoungTableau.firstColumnLabel`: the label of
  the single cell of the second row, and the label above it.
* `TauCeti.labelTabloid` and `TauCeti.labelTabloidEquiv`: the tabloids of a shape `(m, 1)` are the
  labels, `TauCeti.labelTabloidRepresentationEquiv` being the induced identification of `M^μ` with
  the permutation module on the labels.
* `TauCeti.standardRepresentationEquivSpechtSubrepresentation`: **`S^{(n-1,1)}` is the standard
  representation**.

## Main results

* `TauCeti.YoungTableau.mem_colSubgroup_iff`: the column group of a tableau of a shape `(m, 1)` has
  two elements, and `TauCeti.YoungTableau.rowSubgroup_eq_stabilizer`: its row group is the
  stabilizer of the label of the short row.
* `TauCeti.YoungTableau.polytabloid_eq_single_sub_single`: a polytabloid of such a shape is a
  difference of two tabloids, and `TauCeti.YoungTableau.tabloid_eq_iff_secondRowLabel_eq`: a
  tabloid is named by the label of its short row.
* `TauCeti.spechtSubrepresentation_eq_augmentationSubrepresentation`: **the Specht module of a
  shape `(m, 1)` is the augmentation subrepresentation of `M^μ`**.
* `TauCeti.finrank_spechtSubrepresentation_of_rowLen` and
  `TauCeti.finrank_spechtModule_singletonSecondRow`: its dimension is one less than the number of
  labels, so `S^{(n+1,1)}` has dimension `n+1`.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 5, where
  `S^{(n-1,1)}` is identified with the standard representation.
* [W. Fulton, *Young Tableaux*][fulton1997], Section 7.2.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 4, "the named small irreducibles", which asks for `S^{(n-1,1)}` to be the
  `(n-1)`-dimensional standard representation.
-/

public section

namespace TauCeti

namespace YoungTableau

variable {μ : YoungDiagram}

/-! ## The two cells of the first column -/

private theorem oneZero_mem_cells (h1 : μ.rowLen 1 = 1) : ((1, 0) : ℕ × ℕ) ∈ μ.cells := by
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, h1]
  omega

private theorem zeroZero_mem_cells (h1 : μ.rowLen 1 = 1) : ((0, 0) : ℕ × ℕ) ∈ μ.cells := by
  have h := μ.rowLen_anti 0 1 (by omega)
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen]
  omega

/-- The label a tableau puts in the single cell of the second row. -/
def secondRowLabel (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) : Fin μ.card :=
  t ⟨(1, 0), oneZero_mem_cells h1⟩

/-- The label a tableau puts in the top cell of the first column. -/
def firstColumnLabel (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) : Fin μ.card :=
  t ⟨(0, 0), zeroZero_mem_cells h1⟩

@[simp]
theorem rowIndex_secondRowLabel (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) :
    rowIndex t (secondRowLabel h1 t) = 1 :=
  rowIndex_apply t _

@[simp]
theorem colIndex_secondRowLabel (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) :
    colIndex t (secondRowLabel h1 t) = 0 :=
  colIndex_apply t _

@[simp]
theorem rowIndex_firstColumnLabel (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) :
    rowIndex t (firstColumnLabel h1 t) = 0 :=
  rowIndex_apply t _

@[simp]
theorem colIndex_firstColumnLabel (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) :
    colIndex t (firstColumnLabel h1 t) = 0 :=
  colIndex_apply t _

/-- Relabelling moves the second-row label along. -/
@[simp]
theorem secondRowLabel_relabel (h1 : μ.rowLen 1 = 1) (σ : Equiv.Perm (Fin μ.card))
    (t : YoungTableau μ) : secondRowLabel h1 (relabel σ t) = σ (secondRowLabel h1 t) :=
  relabel_apply σ t _

/-- Relabelling moves the top label of the first column along. -/
@[simp]
theorem firstColumnLabel_relabel (h1 : μ.rowLen 1 = 1) (σ : Equiv.Perm (Fin μ.card))
    (t : YoungTableau μ) : firstColumnLabel h1 (relabel σ t) = σ (firstColumnLabel h1 t) :=
  relabel_apply σ t _

/-- On a shape with no third row every label lies in the first or the second row. -/
theorem rowIndex_le_one (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ) (k : Fin μ.card) :
    rowIndex t k ≤ 1 := by
  by_contra hk
  have hmem := rowIndex_colIndex_mem t k
  rw [YoungDiagram.mem_iff_lt_rowLen] at hmem
  have := μ.rowLen_anti 2 (rowIndex t k) (by omega)
  omega

private theorem colIndex_eq_zero_of_rowIndex_eq_one (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ)
    {k : Fin μ.card} (hk : rowIndex t k = 1) : colIndex t k = 0 := by
  have hmem := rowIndex_colIndex_mem t k
  rw [hk, YoungDiagram.mem_iff_lt_rowLen, h1] at hmem
  omega

/-- **The second row holds exactly one label.** -/
theorem rowIndex_eq_one_iff (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) {k : Fin μ.card} :
    rowIndex t k = 1 ↔ k = secondRowLabel h1 t := by
  refine ⟨fun hk => rowIndex_colIndex_injective t ?_, fun hk => by rw [hk, rowIndex_secondRowLabel]⟩
  simp only [Prod.mk.injEq]
  exact ⟨by rw [hk, rowIndex_secondRowLabel],
    by rw [colIndex_eq_zero_of_rowIndex_eq_one h1 t hk, colIndex_secondRowLabel]⟩

/-- The second-row label and the top label of the first column are distinct: they lie in different
rows. -/
theorem secondRowLabel_ne_firstColumnLabel (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) :
    secondRowLabel h1 t ≠ firstColumnLabel h1 t := fun h => by
  have := rowIndex_secondRowLabel h1 t
  rw [h, rowIndex_firstColumnLabel] at this
  omega

/-- **The first column holds exactly two labels.** -/
theorem colIndex_eq_zero_iff (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ)
    {k : Fin μ.card} :
    colIndex t k = 0 ↔ k = firstColumnLabel h1 t ∨ k = secondRowLabel h1 t := by
  refine ⟨fun hk => ?_, ?_⟩
  · rcases Nat.lt_or_ge (rowIndex t k) 1 with hrow | hrow
    · refine Or.inl (rowIndex_colIndex_injective t ?_)
      simp only [Prod.mk.injEq]
      refine ⟨?_, by rw [hk, colIndex_firstColumnLabel]⟩
      rw [rowIndex_firstColumnLabel]
      omega
    · exact Or.inr ((rowIndex_eq_one_iff h1 t).mp
        (le_antisymm (rowIndex_le_one h2 t k) hrow))
  · rintro (rfl | rfl)
    · exact colIndex_firstColumnLabel h1 t
    · exact colIndex_secondRowLabel h1 t

/-! ## The row and the column group -/

/-- **On a shape `(m, 1)` the row group is the stabilizer of the second-row label.**  A permutation
keeps every label in its row exactly when it fixes the one label of the short row. -/
theorem rowSubgroup_eq_stabilizer (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (t : YoungTableau μ) :
    rowSubgroup t = MulAction.stabilizer (Equiv.Perm (Fin μ.card)) (secondRowLabel h1 t) := by
  ext σ
  rw [mem_rowSubgroup, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
  refine ⟨fun hσ => ?_, fun hσ k => ?_⟩
  · have h := hσ (secondRowLabel h1 t)
    rw [rowIndex_secondRowLabel] at h
    exact (rowIndex_eq_one_iff h1 t).mp h
  · rcases eq_or_ne k (secondRowLabel h1 t) with rfl | hk
    · rw [hσ]
    · have hk' : σ k ≠ secondRowLabel h1 t := fun h =>
        hk (σ.injective (h.trans hσ.symm))
      have h1k : rowIndex t k ≠ 1 := fun h => hk ((rowIndex_eq_one_iff h1 t).mp h)
      have h2k : rowIndex t (σ k) ≠ 1 := fun h => hk' ((rowIndex_eq_one_iff h1 t).mp h)
      have := rowIndex_le_one h2 t k
      have := rowIndex_le_one h2 t (σ k)
      omega

/-- **On a shape `(m, 1)` the column group has two elements**: the identity and the transposition
of the two labels of the first column. -/
theorem mem_colSubgroup_iff (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ)
    {σ : Equiv.Perm (Fin μ.card)} :
    σ ∈ colSubgroup t ↔
      σ = 1 ∨ σ = Equiv.swap (firstColumnLabel h1 t) (secondRowLabel h1 t) := by
  classical
  have hab : firstColumnLabel h1 t ≠ secondRowLabel h1 t :=
    (secondRowLabel_ne_firstColumnLabel h1 t).symm
  have hcola : colIndex t (firstColumnLabel h1 t) = 0 := colIndex_firstColumnLabel h1 t
  have hcolb : colIndex t (secondRowLabel h1 t) = 0 := colIndex_secondRowLabel h1 t
  rw [mem_colSubgroup]
  refine ⟨fun hσ => ?_, ?_⟩
  · -- away from the first column the fibers of the column index are singletons
    have hfix : ∀ k, colIndex t k ≠ 0 → σ k = k := by
      intro k hk
      have hk' : colIndex t (σ k) ≠ 0 := by rw [hσ k]; exact hk
      have hrow : rowIndex t k = 0 := by
        have hne : k ≠ secondRowLabel h1 t := fun h => hk (by rw [h, hcolb])
        have hle := rowIndex_le_one h2 t k
        have hone : rowIndex t k ≠ 1 := fun h => hne ((rowIndex_eq_one_iff h1 t).mp h)
        omega
      have hrow' : rowIndex t (σ k) = 0 := by
        have hne : σ k ≠ secondRowLabel h1 t := fun h => hk' (by rw [h, hcolb])
        have hle := rowIndex_le_one h2 t (σ k)
        have hone : rowIndex t (σ k) ≠ 1 := fun h => hne ((rowIndex_eq_one_iff h1 t).mp h)
        omega
      exact rowIndex_colIndex_injective t
        (by simp only [Prod.mk.injEq]; exact ⟨by rw [hrow, hrow'], hσ k⟩)
    -- on the first column it permutes the two labels there
    have hmem : ∀ k, colIndex t k = 0 →
        σ k = firstColumnLabel h1 t ∨ σ k = secondRowLabel h1 t := fun k hk =>
      (colIndex_eq_zero_iff h1 h2 t).mp (by rw [hσ k]; exact hk)
    rcases hmem _ hcola with hsa | hsa
    · refine Or.inl (Equiv.ext fun k => (?_ : σ k = k))
      rcases eq_or_ne (colIndex t k) 0 with hk | hk
      · rcases (colIndex_eq_zero_iff h1 h2 t).mp hk with rfl | rfl
        · exact hsa
        · rcases hmem _ hcolb with h | h
          · exact absurd (σ.injective (h.trans hsa.symm)) hab.symm
          · exact h
      · exact hfix k hk
    · refine Or.inr (Equiv.ext fun k => ?_)
      have hsb : σ (secondRowLabel h1 t) = firstColumnLabel h1 t := by
        rcases hmem _ hcolb with h | h
        · exact h
        · exact absurd (σ.injective (h.trans hsa.symm)) hab.symm
      rcases eq_or_ne (colIndex t k) 0 with hk | hk
      · rcases (colIndex_eq_zero_iff h1 h2 t).mp hk with rfl | rfl
        · rw [hsa, Equiv.swap_apply_left]
        · rw [hsb, Equiv.swap_apply_right]
      · have hka : k ≠ firstColumnLabel h1 t := fun h => hk (by rw [h, hcola])
        have hkb : k ≠ secondRowLabel h1 t := fun h => hk (by rw [h, hcolb])
        rw [hfix k hk, Equiv.swap_apply_of_ne_of_ne hka hkb]
  · rintro (rfl | rfl) k
    · rfl
    · rcases eq_or_ne k (firstColumnLabel h1 t) with rfl | hka
      · rw [Equiv.swap_apply_left, hcola, hcolb]
      · rcases eq_or_ne k (secondRowLabel h1 t) with rfl | hkb
        · rw [Equiv.swap_apply_right, hcola, hcolb]
        · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]

/-! ## The polytabloid of a shape `(m, 1)` -/

/-- The transposition of the two labels of the first column does move the tabloid: the two labels
lie in different rows. -/
theorem swap_smul_tabloid_ne (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ) :
    Equiv.swap (firstColumnLabel h1 t) (secondRowLabel h1 t) • tabloid t ≠ tabloid t := by
  rw [Ne, smul_tabloid_eq_self_iff, rowSubgroup_eq_stabilizer h1 h2 t,
    MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Equiv.swap_apply_right]
  exact (secondRowLabel_ne_firstColumnLabel h1 t).symm

/-- **The polytabloid of a shape `(m, 1)` is a difference of two tabloids.**  The column group of
`t` consists of the identity and the transposition of the two labels of the first column, so the
antisymmetrization of `{t}` has just two terms, with opposite signs. -/
theorem polytabloid_eq_single_sub_single (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (t : YoungTableau μ) :
    polytabloid t = MonoidAlgebra.single (tabloid t) (1 : ℚ) -
      MonoidAlgebra.single
        (Equiv.swap (firstColumnLabel h1 t) (secondRowLabel h1 t) • tabloid t) (1 : ℚ) := by
  classical
  have hab : firstColumnLabel h1 t ≠ secondRowLabel h1 t :=
    (secondRowLabel_ne_firstColumnLabel h1 t).symm
  have hswap : Equiv.swap (firstColumnLabel h1 t) (secondRowLabel h1 t) ∈ colSubgroup t :=
    (mem_colSubgroup_iff h1 h2 t).mpr (Or.inr rfl)
  have hne := swap_smul_tabloid_ne h1 h2 t
  rw [← MonoidAlgebra.coeff_inj]
  ext X
  rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_single,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
  rcases eq_or_ne X (tabloid t) with rfl | hX
  · rw [polytabloid_coeff_tabloid]
    simp [hne]
  rcases eq_or_ne X (Equiv.swap (firstColumnLabel h1 t) (secondRowLabel h1 t) • tabloid t) with
    rfl | hX'
  · have hcoeff : (polytabloid t).coeff
        (Equiv.swap (firstColumnLabel h1 t) (secondRowLabel h1 t) • tabloid t) = -1 := by
      simpa [hab] using polytabloid_coeff_smul_tabloid t ⟨_, hswap⟩
    rw [hcoeff]
    simp [Ne.symm hne]
  · have hzero : (polytabloid t).coeff X = 0 := by
      refine polytabloid_coeff_eq_zero_of_forall_ne t fun q hq => ?_
      rcases (mem_colSubgroup_iff h1 h2 t).mp hq with rfl | rfl
      · simpa using Ne.symm hX
      · exact Ne.symm hX'
    rw [hzero]
    simp [Ne.symm hX, Ne.symm hX']


/-- **A tabloid of a shape `(m, 1)` is named by the label of its short row.** -/
theorem tabloid_eq_iff_secondRowLabel_eq (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    {t u : YoungTableau μ} :
    tabloid t = tabloid u ↔ secondRowLabel h1 t = secondRowLabel h1 u := by
  rw [tabloid_eq_iff_rowIndex_eq]
  refine ⟨fun h => ?_, fun h => funext fun k => ?_⟩
  · have hk : rowIndex u (secondRowLabel h1 t) = 1 := by
      rw [← congrFun h (secondRowLabel h1 t), rowIndex_secondRowLabel]
    exact (rowIndex_eq_one_iff h1 u).mp hk
  · have ht := rowIndex_le_one h2 t k
    have hu := rowIndex_le_one h2 u k
    rcases eq_or_ne k (secondRowLabel h1 t) with rfl | hk
    · rw [rowIndex_secondRowLabel, h, rowIndex_secondRowLabel]
    · have htk : rowIndex t k ≠ 1 := fun hh => hk ((rowIndex_eq_one_iff h1 t).mp hh)
      have huk : rowIndex u k ≠ 1 := fun hh =>
        hk (((rowIndex_eq_one_iff h1 u).mp hh).trans h.symm)
      omega

end YoungTableau

/-! ## The Specht module of a shape `(m, 1)` -/

open YoungTableau

variable {μ : YoungDiagram}

/-- **A polytabloid of a shape `(m, 1)` has vanishing coefficient sum**: it is a difference of two
tabloids. -/
theorem polytabloid_mem_augmentationSubrepresentation (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (t : YoungTableau μ) :
    polytabloid t ∈ augmentationSubrepresentation ℚ (Equiv.Perm (Fin μ.card))
      (Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)) := by
  rw [polytabloid_eq_single_sub_single h1 h2 t]
  exact single_sub_single_mem_augmentationSubrepresentation _ _

/-- **Every difference of two tabloids of a shape `(m, 1)` is a polytabloid**, hence lies in the
Specht module: a tableau whose short row carries the label naming the first tabloid can be
relabelled, without moving that label, so that the top of its first column carries the label naming
the second. -/
theorem single_sub_single_mem_spechtSubrepresentation (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (X Y : Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)) :
    (MonoidAlgebra.single X (1 : ℚ) - MonoidAlgebra.single Y 1) ∈ spechtSubrepresentation μ := by
  rcases eq_or_ne X Y with rfl | hXY
  · rw [sub_self]
    exact Submodule.zero_mem _
  obtain ⟨t, rfl⟩ := tabloid_surjective X
  obtain ⟨u, rfl⟩ := tabloid_surjective Y
  have hbc : secondRowLabel h1 t ≠ secondRowLabel h1 u := fun h =>
    hXY ((tabloid_eq_iff_secondRowLabel_eq h1 h2).mpr h)
  obtain ⟨σ, hσa, hσb⟩ : ∃ σ : Equiv.Perm (Fin μ.card),
      σ (firstColumnLabel h1 t) = secondRowLabel h1 u ∧
        σ (secondRowLabel h1 t) = secondRowLabel h1 t :=
    ⟨Equiv.swap (firstColumnLabel h1 t) (secondRowLabel h1 u), Equiv.swap_apply_left _ _,
      Equiv.swap_apply_of_ne_of_ne (secondRowLabel_ne_firstColumnLabel h1 t) hbc⟩
  have hsecond : secondRowLabel h1 (relabel σ t) = secondRowLabel h1 t := by
    rw [secondRowLabel_relabel, hσb]
  have hfirst : firstColumnLabel h1 (relabel σ t) = secondRowLabel h1 u := by
    rw [firstColumnLabel_relabel, hσa]
  have htab : tabloid (relabel σ t) = tabloid t :=
    (tabloid_eq_iff_secondRowLabel_eq h1 h2).mpr hsecond
  have hswaptab :
      Equiv.swap (secondRowLabel h1 u) (secondRowLabel h1 t) • tabloid t = tabloid u := by
    rw [← tabloid_relabel]
    refine (tabloid_eq_iff_secondRowLabel_eq h1 h2).mpr ?_
    rw [secondRowLabel_relabel, Equiv.swap_apply_right]
  have hpoly := polytabloid_eq_single_sub_single h1 h2 (relabel σ t)
  rw [hfirst, hsecond, htab, hswaptab] at hpoly
  rw [← hpoly]
  exact polytabloid_mem_spechtSubrepresentation _

/-- **The Specht module of a shape `(m, 1)` is the standard representation of the tabloids.**  The
polytabloids of such a shape are exactly the differences of two tabloid basis vectors, and those
span the subrepresentation on which the coefficients sum to zero.

Since `TauCeti.standardRepresentation` is by definition the action carried by the augmentation
subrepresentation of a permutation module, this is the identification `S^{(n-1,1)} = standard`,
read on the tabloids; `TauCeti.tabloidEquivLabel` names the tabloids by the labels. -/
theorem spechtSubrepresentation_eq_augmentationSubrepresentation (h1 : μ.rowLen 1 = 1)
    (h2 : μ.rowLen 2 = 0) :
    spechtSubrepresentation μ =
      augmentationSubrepresentation ℚ (Equiv.Perm (Fin μ.card))
        (Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)) := by
  refine Subrepresentation.toSubmodule_injective (le_antisymm ?_ ?_)
  · rw [spechtSubrepresentation_toSubmodule, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact polytabloid_mem_augmentationSubrepresentation h1 h2 t
  · obtain ⟨t₀⟩ := YoungTableau.nonempty μ
    rw [toSubmodule_augmentationSubrepresentation,
      ker_sumCoords_basis_eq_span ℚ _ (tabloid t₀), Submodule.span_le]
    rintro _ ⟨X, rfl⟩
    exact single_sub_single_mem_spechtSubrepresentation h1 h2 X (tabloid t₀)



/-! ## The tabloids of a shape `(m, 1)` are the labels -/

/-- **The tabloid named by a label**: relabel a fixed tableau by the transposition carrying its own
short-row label to the prescribed one. -/
noncomputable def labelTabloid (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) (k : Fin μ.card) :
    Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ) :=
  tabloid (relabel (Equiv.swap (secondRowLabel h1 t) k) t)

theorem labelTabloid_def (h1 : μ.rowLen 1 = 1) (t : YoungTableau μ) (k : Fin μ.card) :
    labelTabloid h1 t k = tabloid (relabel (Equiv.swap (secondRowLabel h1 t) k) t) :=
  -- `(rfl)`, not `rfl`: the body of `labelTabloid` is not `@[expose]`d, so this must not be
  -- inferred `@[defeq]`.
  (rfl)

theorem labelTabloid_bijective (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ) :
    Function.Bijective (labelTabloid h1 t) := by
  constructor
  · intro k l hkl
    rw [labelTabloid_def, labelTabloid_def, tabloid_eq_iff_secondRowLabel_eq h1 h2] at hkl
    simpa using hkl
  · intro X
    obtain ⟨u, rfl⟩ := tabloid_surjective X
    refine ⟨secondRowLabel h1 u, ?_⟩
    rw [labelTabloid_def, tabloid_eq_iff_secondRowLabel_eq h1 h2]
    simp

/-- Naming a tabloid by the label of its short row is equivariant. -/
theorem labelTabloid_smul (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ)
    (σ : Equiv.Perm (Fin μ.card)) (k : Fin μ.card) :
    labelTabloid h1 t (σ • k) = σ • labelTabloid h1 t k := by
  rw [labelTabloid_def, labelTabloid_def, ← tabloid_relabel,
    tabloid_eq_iff_secondRowLabel_eq h1 h2]
  simp

/-- **The tabloids of a shape `(m, 1)` are the labels.**  A tabloid of such a shape splits the
labels into a long row and a single short one, so it is named by the label of the short row. -/
noncomputable def labelTabloidEquiv (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (t : YoungTableau μ) :
    Fin μ.card ≃ (Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)) :=
  Equiv.ofBijective _ (labelTabloid_bijective h1 h2 t)

@[simp]
theorem labelTabloidEquiv_apply (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ)
    (k : Fin μ.card) : labelTabloidEquiv h1 h2 t k = labelTabloid h1 t k :=
  -- `(rfl)`, not `rfl`: the body of `labelTabloidEquiv` is not `@[expose]`d.
  (rfl)

/-- **The Young permutation module of a shape `(m, 1)` is the permutation module on the labels.** -/
noncomputable def labelTabloidRepresentationEquiv (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (t : YoungTableau μ) :
    (Representation.ofMulAction ℚ (Equiv.Perm (Fin μ.card)) (Fin μ.card)).Equiv
      (permutationModule (shapePartition μ)).ρ :=
  ofMulActionEquivCongr ℚ (labelTabloidEquiv h1 h2 t) fun g k => by
    rw [labelTabloidEquiv_apply, labelTabloidEquiv_apply]
    exact labelTabloid_smul h1 h2 t g k

@[simp]
theorem labelTabloidRepresentationEquiv_apply_single (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (t : YoungTableau μ) (k : Fin μ.card) (r : ℚ) :
    labelTabloidRepresentationEquiv h1 h2 t (MonoidAlgebra.single k r) =
      MonoidAlgebra.single (labelTabloid h1 t k) r := by
  rw [labelTabloidRepresentationEquiv, ofMulActionEquivCongr_apply_single, labelTabloidEquiv_apply]

/-- The transport of `ℚ[Fin μ.card]` onto the Young permutation module carries the augmentation
subrepresentation of the labels onto the Specht module of the shape. -/
private theorem map_augmentationSubrepresentation (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0)
    (t : YoungTableau μ) :
    Submodule.map
        ((labelTabloidRepresentationEquiv h1 h2 t).toLinearEquiv :
          MonoidAlgebra ℚ (Fin μ.card) →ₗ[ℚ] (permutationModule (shapePartition μ)).V)
        (augmentationSubrepresentation ℚ (Equiv.Perm (Fin μ.card)) (Fin μ.card)).toSubmodule =
      (spechtSubrepresentation μ).toSubmodule := by
  have hsingle : ∀ (k : Fin μ.card) (r : ℚ),
      ((labelTabloidRepresentationEquiv h1 h2 t).toLinearEquiv :
          MonoidAlgebra ℚ (Fin μ.card) →ₗ[ℚ] (permutationModule (shapePartition μ)).V)
        (MonoidAlgebra.single k r) = MonoidAlgebra.single (labelTabloid h1 t k) r :=
    fun k r => labelTabloidRepresentationEquiv_apply_single h1 h2 t k r
  have hsum : (MonoidAlgebra.basis
        (Equiv.Perm (Fin μ.card) ⧸ youngSubgroup (shapePartition μ)) ℚ).sumCoords ∘ₗ
        ((labelTabloidRepresentationEquiv h1 h2 t).toLinearEquiv :
          MonoidAlgebra ℚ (Fin μ.card) →ₗ[ℚ] (permutationModule (shapePartition μ)).V) =
      (MonoidAlgebra.basis (Fin μ.card) ℚ).sumCoords :=
    Module.Basis.ext (MonoidAlgebra.basis (Fin μ.card) ℚ) fun k => by
      rw [LinearMap.comp_apply, MonoidAlgebra.basis_apply, hsingle]
      simp
  rw [spechtSubrepresentation_eq_augmentationSubrepresentation h1 h2,
    toSubmodule_augmentationSubrepresentation, toSubmodule_augmentationSubrepresentation,
    ← hsum, LinearMap.ker_comp]
  exact Submodule.map_comap_eq_of_surjective
    (labelTabloidRepresentationEquiv h1 h2 t).toLinearEquiv.surjective _

/-- **The Specht module of a shape `(m, 1)` is the standard representation.**  Naming the tabloids
by the labels of their short rows carries `ℚ[Fin μ.card]` onto the Young permutation module and its
augmentation subrepresentation -- the standard representation -- onto the Specht module, which
`TauCeti.spechtSubrepresentation_eq_augmentationSubrepresentation` identifies as the augmentation
subrepresentation on the tabloids.

This is the third of the named small irreducibles of `Sₙ`, beside the trivial representation
`S^{(n)}` and the sign representation `S^{(1ⁿ)}` of
`TauCeti.RepresentationTheory.Symmetric.Specht.Extremes`. -/
noncomputable def standardRepresentationEquivSpechtSubrepresentation (h1 : μ.rowLen 1 = 1)
    (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ) :
    (standardRepresentation ℚ (Fin μ.card)).Equiv (spechtSubrepresentation μ).toRepresentation :=
  Representation.Equiv.mk
    (LinearEquiv.ofSubmodules (labelTabloidRepresentationEquiv h1 h2 t).toLinearEquiv _ _
      (map_augmentationSubrepresentation h1 h2 t))
    fun g => LinearMap.ext fun v => Subtype.ext <| by
      simp only [← toRepresentation_augmentationSubrepresentation, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.ofSubmodules_apply,
        Subrepresentation.toRepresentation_apply, LinearMap.coe_restrict_apply,
        Representation.Equiv.toLinearEquiv_apply]
      exact Representation.IntertwiningMap.isIntertwining _ _
        (labelTabloidRepresentationEquiv h1 h2 t).toIntertwiningMap g v

/-- The underlying equivalence of the identification is the transport of the tabloids. -/
@[simp]
theorem coe_standardRepresentationEquivSpechtSubrepresentation (h1 : μ.rowLen 1 = 1)
    (h2 : μ.rowLen 2 = 0) (t : YoungTableau μ)
    (v : (augmentationSubrepresentation ℚ (Equiv.Perm (Fin μ.card)) (Fin μ.card)).toSubmodule) :
    (standardRepresentationEquivSpechtSubrepresentation h1 h2 t v :
        (permutationModule (shapePartition μ)).V) =
      labelTabloidRepresentationEquiv h1 h2 t (v : MonoidAlgebra ℚ (Fin μ.card)) :=
  -- `(rfl)`, not `rfl`: the body of the equivalence is not `@[expose]`d.
  (rfl)

/-- **The Specht module of a shape `(m, 1)` has dimension one less than the number of labels**:
the standard representation of `Sₙ` has dimension `n - 1`. -/
theorem finrank_spechtSubrepresentation_of_rowLen (h1 : μ.rowLen 1 = 1) (h2 : μ.rowLen 2 = 0) :
    Module.finrank ℚ (spechtSubrepresentation μ).toSubmodule = μ.card - 1 := by
  obtain ⟨t⟩ := YoungTableau.nonempty μ
  rw [← (standardRepresentationEquivSpechtSubrepresentation h1 h2 t).toLinearEquiv.finrank_eq,
    finrank_augmentationSubrepresentation, Fintype.card_fin]

/-! ## The shape `(n+1, 1)` -/

/-- The second row of the diagram of `(n+1, 1)` is a single cell. -/
theorem rowLen_one_diagramOf_singletonSecondRow (n : ℕ) :
    (diagramOf (Nat.Partition.singletonSecondRow n)).rowLen 1 = 1 := by
  rw [rowLen_diagramOf, Nat.Partition.sort_parts_singletonSecondRow]
  rfl

/-- The diagram of `(n+1, 1)` has no third row. -/
theorem rowLen_two_diagramOf_singletonSecondRow (n : ℕ) :
    (diagramOf (Nat.Partition.singletonSecondRow n)).rowLen 2 = 0 := by
  rw [rowLen_diagramOf, Nat.Partition.sort_parts_singletonSecondRow]
  rfl

/-- **`S^{(n-1,1)}` has dimension `n - 1`**: the Specht module of the shape `(n+1, 1)` of `n + 2`
is the `(n+1)`-dimensional standard representation of `S_{n+2}`. -/
@[simp]
theorem finrank_spechtModule_singletonSecondRow (n : ℕ) :
    Module.finrank ℚ (spechtModule (Nat.Partition.singletonSecondRow n)) = n + 1 := by
  exact (finrank_spechtSubrepresentation_of_rowLen
    (rowLen_one_diagramOf_singletonSecondRow n)
    (rowLen_two_diagramOf_singletonSecondRow n)).trans (by rw [card_diagramOf]; omega)

end TauCeti
