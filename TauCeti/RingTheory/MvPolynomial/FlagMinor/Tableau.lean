/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Tableau
public import TauCeti.RingTheory.MvPolynomial.FlagMinor.Basic
public import TauCeti.RingTheory.MvPolynomial.MultiHomogeneous
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Basic
import TauCeti.Data.Finset.Sort

/-!
# Tableau products of flag minors, pattern comparisons, and multigradings

A bounded semistandard Young tableau `T : BoundedSSYT n μ` of shape `μ` with entries in
`{0, …, n - 1}` has strictly increasing columns, so its `m`-th column determines a set
`T.colFinset m` of `μ.colLen m` rows of the generic `n × n` matrix. Multiplying the corresponding
flag minors across the nonempty columns `m < μ.rowLen 0` produces the **tableau product**
`T.flagMinorProd R`.

Under the row-major lexicographic order on the matrix variables, each `T.flagMinorProd R` is monic,
and the partial column sums of its leading exponent form the Gelfand-Tsetlin pattern
`SemistandardYoungTableau.toGTPattern T.1 n` attached to `T`. Composing the shape-to-weight
correspondence `TauCeti.shapeEquivPolynomialWeight` with `TauCeti.gtPatternEquivSSYT` identifies
the additive monoid `AddSubmonoid.nonneg (GTPattern n)` of polynomial Gelfand-Tsetlin patterns with
the sigma type of bounded semistandard tableaux over all shapes `μ` with at most `n` rows
(`TauCeti.GTPattern.nonnegEquivBoundedSSYT`). Consequently, the tableau products have pairwise
distinct leading exponents whose range is the diagonal-exponent monoid
`AddSubmonoid.closure (Set.range flagDiagonalExponent)`.

Finally, `T.flagMinorProd R` is doubly multihomogeneous:
* for the **row multigrading** `MvPolynomial.IsMultiHomogeneous`, its multidegree is the content
  `⇑T.weight` of the tableau (`TauCeti.BoundedSSYT.isMultiHomogeneous_flagMinorProd`);
* for the **fundamental column multigrading** `TauCeti.flagColWeight`, its degree in column `c` of
  the generic matrix is `μ.rowLen c`, so each flag minor `flagMinor R I` has column multidegree the
  fundamental weight of `#I` and each `T.flagMinorProd R` has column multidegree the shape `μ`
  (`TauCeti.BoundedSSYT.isWeightedHomogeneous_flagColWeight_flagMinorProd`).

## Main definitions

* `TauCeti.BoundedSSYT.colOrderEmb` and `TauCeti.BoundedSSYT.colFinset`: the sorted entries and row
  subset of column `m` of a bounded semistandard tableau.
* `TauCeti.GTPattern.nonnegEquivBoundedSSYT`: the bijection between nonnegative Gelfand-Tsetlin
  patterns with `n` rows and bounded semistandard tableaux across all shapes with at most `n` rows.
* `TauCeti.BoundedSSYT.flagMinorProd`: the product of the flag minors of the columns of a bounded
  semistandard tableau.
* `TauCeti.flagColWeight`: the indicator weight of column `c` of the generic `n × n` matrix.

## Main results

* `TauCeti.BoundedSSYT.sum_rowSubset_colFinset`: the row-subset patterns of the columns of `T` sum
  to `SemistandardYoungTableau.toGTPattern T.1 n`.
* `TauCeti.BoundedSSYT.monic_rename_toLex_flagMinorProd`,
  `TauCeti.BoundedSSYT.degree_rename_toLex_flagMinorProd`, and
  `TauCeti.BoundedSSYT.exponentEntries_degree_rename_toLex_flagMinorProd`: `T.flagMinorProd R` is
  monic and its leading exponent records `toGTPattern T.1 n`.
* `TauCeti.BoundedSSYT.degree_rename_toLex_flagMinorProd_injective` and
  `TauCeti.BoundedSSYT.range_degree_rename_toLex_flagMinorProd`: the leading exponents of the
  tableau products biject onto `AddSubmonoid.closure (Set.range flagDiagonalExponent)`.
* `TauCeti.BoundedSSYT.isMultiHomogeneous_flagMinorProd` and
  `TauCeti.BoundedSSYT.isWeightedHomogeneous_flagColWeight_flagMinorProd`: row-content and
  column-shape multihomogeneity of `T.flagMinorProd R`.

## References

* E. Miller and B. Sturmfels, *Combinatorial Commutative Algebra*, GTM 227, Springer, 2005,
  Chapter 14.
* M. Kogan and E. Miller, *Toric degeneration of Schubert varieties and Gelfand-Tsetlin
  polytopes*, Adv. Math. **193** (2005), 1-17.
* W. Fulton, *Young Tableaux*, LMSST 35, Cambridge University Press, 1997, §8.1 and §9.1.
-/

public section

namespace TauCeti

open Finset MvPolynomial MonomialOrder

variable {n : ℕ} {μ : YoungDiagram}

/-! ### Columns of a bounded semistandard Young tableau -/

namespace BoundedSSYT

/-- The `m`-th column of a bounded semistandard Young tableau `T`, read as an order embedding
`Fin (μ.colLen m) ↪o Fin n`: entries increase strictly down each column of `μ` and lie below `n`. -/
def colOrderEmb (T : BoundedSSYT n μ) (m : ℕ) : Fin (μ.colLen m) ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨T.1 i m, T.entry_lt (YoungDiagram.mem_iff_lt_colLen.mpr i.2)⟩)
    fun _ _ h ↦ Fin.lt_def.mpr (T.1.col_strict h (YoungDiagram.mem_iff_lt_colLen.mpr ‹Fin _›.2))

@[simp]
theorem coe_colOrderEmb_apply (T : BoundedSSYT n μ) (m : ℕ) (i : Fin (μ.colLen m)) :
    (T.colOrderEmb m i : ℕ) = T.1 i m :=
  (rfl)

/-- The set of row indices appearing in column `m` of a bounded semistandard Young tableau `T`. -/
def colFinset (T : BoundedSSYT n μ) (m : ℕ) : Finset (Fin n) :=
  univ.map (T.colOrderEmb m).toEmbedding

theorem colFinset_def (T : BoundedSSYT n μ) (m : ℕ) :
    T.colFinset m = univ.map (T.colOrderEmb m).toEmbedding :=
  (rfl)

@[simp]
theorem card_colFinset (T : BoundedSSYT n μ) (m : ℕ) : #(T.colFinset m) = μ.colLen m := by
  simp [colFinset_def]

/-- A row index `r : Fin n` belongs to `T.colFinset m` if and only if it appears at some cell
`(i, m)` of column `m` of `μ`. -/
theorem mem_colFinset_iff (T : BoundedSSYT n μ) {m : ℕ} {r : Fin n} :
    r ∈ T.colFinset m ↔ ∃ i < μ.colLen m, T.1 i m = r := by
  rw [colFinset_def, mem_map]
  refine ⟨fun ⟨i, _, hi⟩ ↦ ⟨i, i.2, by simpa [Fin.ext_iff] using hi⟩, ?_⟩
  rintro ⟨i, hi, hir⟩
  exact ⟨⟨i, hi⟩, mem_univ _, Fin.ext hir⟩

/-- Columns past `μ.rowLen 0` are empty. -/
@[simp]
theorem colFinset_eq_empty_of_rowLen_zero_le (T : BoundedSSYT n μ) {m : ℕ}
    (hm : μ.rowLen 0 ≤ m) : T.colFinset m = ∅ := by
  rw [← card_eq_zero, card_colFinset]
  by_contra h
  exact (YoungDiagram.mem_iff_lt_rowLen.mp
    (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero h))).not_ge hm

/-- Columns strictly before `μ.rowLen 0` are nonempty. -/
theorem colFinset_nonempty_of_lt_rowLen_zero (T : BoundedSSYT n μ) {m : ℕ}
    (hm : m < μ.rowLen 0) : (T.colFinset m).Nonempty := by
  rw [← card_pos, card_colFinset]
  exact YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hm)

/-- Sorting `T.colFinset m` recovers the column order embedding `T.colOrderEmb m`. -/
theorem orderEmbOfFin_colFinset (T : BoundedSSYT n μ) (m : ℕ) :
    (T.colFinset m).orderEmbOfFin (T.card_colFinset m) = T.colOrderEmb m :=
  (orderEmbOfFin_unique' (T.card_colFinset m) fun i ↦ by
    rw [colFinset_def]
    exact mem_map_of_mem _ (mem_univ i)).symm

@[simp]
theorem coe_orderEmbOfFin_colFinset_apply (T : BoundedSSYT n μ) (m : ℕ) {k : ℕ}
    (hk : #(T.colFinset m) = k) (i : Fin k) :
    ((T.colFinset m).orderEmbOfFin hk i : ℕ) = T.1 i m := by
  obtain rfl : k = μ.colLen m := hk.symm.trans (T.card_colFinset m)
  rw [T.orderEmbOfFin_colFinset m, coe_colOrderEmb_apply]

/-- **Column decomposition of a tableau pattern.** Summing the row-subset Gelfand-Tsetlin patterns
of the nonempty columns of a bounded semistandard tableau `T` produces the pattern
`SemistandardYoungTableau.toGTPattern T.1 n` attached to `T`. -/
@[simp]
theorem sum_rowSubset_colFinset (T : BoundedSSYT n μ) :
    ∑ m ∈ range (μ.rowLen 0), GTPattern.rowSubset (T.colFinset m) =
      SemistandardYoungTableau.toGTPattern T.1 n := by
  ext i j
  rw [GTPattern.coe_sum, Finset.sum_apply, Finset.sum_apply,
    SemistandardYoungTableau.toGTPattern_apply, SemistandardYoungTableau.patternEntry_def]
  by_cases hnj : n < j
  · rw [ite_eq_left hnj]
    exact sum_eq_zero fun m _ ↦ by simp [GTPattern.rowSubset_apply, show ¬ j ≤ n by omega]
  · have hjn : j ≤ n := not_lt.mp hnj
    rw [ite_eq_right hnj]
    -- In column `m`, `i < #{r ∈ T.colFinset m | r < j}` holds precisely when `(i, m) ∈ μ`
    -- and `T i m < j`.
    have hcol (m : ℕ) :
        i < #{r ∈ T.colFinset m | r.val < j} ↔ m < μ.rowLen i ∧ T.1 i m < j := by
      by_cases him : i < μ.colLen m
      · have hmem : m < μ.rowLen i :=
          YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr him)
        have hlt := lt_card_filter_iff_apply_orderEmbOfFin_of_imp (T.colFinset m)
          (T.card_colFinset m) ⟨i, him⟩ (fun r : Fin n ↦ r.val < j)
          fun _ _ hba hp ↦ lt_of_le_of_lt (Fin.le_iff_val_le_val.1 hba) hp
        simpa [hmem] using hlt
      · have hle : #{r ∈ T.colFinset m | r.val < j} ≤ i :=
          (card_filter_le _ _).trans ((T.card_colFinset m).le.trans (not_lt.mp him))
        have hnot : ¬ m < μ.rowLen i := fun hm ↦
          him (YoungDiagram.mem_iff_lt_colLen.mp (YoungDiagram.mem_iff_lt_rowLen.mpr hm))
        simp [hle.not_gt, hnot]
    simp only [GTPattern.rowSubset_apply, hjn, true_and, hcol]
    rw [sum_boole]
    congr 2
    ext m
    simp only [mem_filter, mem_range]
    have hrow := μ.rowLen_anti 0 i (Nat.zero_le i)
    omega

end BoundedSSYT

/-! ### Nonnegative Gelfand-Tsetlin patterns and bounded tableaux across all shapes -/

namespace GTPattern

/-- **Nonnegative Gelfand-Tsetlin patterns are bounded semistandard tableaux.** A nonnegative
pattern `P` with `n` rows has a polynomial top weight, naming a shape `μ` with at most `n` rows via
`TauCeti.shapeEquivPolynomialWeight`, and `TauCeti.gtPatternEquivSSYT` identifies the patterns with
that top row with `BoundedSSYT n μ`. -/
def nonnegEquivBoundedSSYT (n : ℕ) :
    AddSubmonoid.nonneg (GTPattern n) ≃
      Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.1 :=
  let f : AddSubmonoid.nonneg (GTPattern n) → {l : DominantWeight n // l.IsPolynomial} :=
    fun P ↦ ⟨P.1.topWeight, zero_le_iff_isPolynomial.mp P.2⟩
  ((Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrLeft (shapeEquivPolynomialWeight n)).symm).trans
    (Equiv.sigmaCongrRight fun μ ↦
      ({ toFun := fun q ↦
           ⟨q.1.1, fun i ↦ by simpa [f, topWeight_coe] using congrArg (fun x ↦ x.1.1 i) q.2⟩
         invFun := fun r ↦
           ⟨⟨r.1, zero_le_iff_topRow.mpr fun i ↦ (r.2 i).symm ▸ Int.natCast_nonneg _⟩,
             Subtype.ext (Subtype.ext (funext fun i ↦ by simpa [f, topWeight_coe] using r.2 i))⟩
         left_inv := fun _ ↦ rfl
         right_inv := fun _ ↦ rfl } :
        {P : AddSubmonoid.nonneg (GTPattern n) // f P = shapeEquivPolynomialWeight n μ} ≃
          {P : GTPattern n // ∀ i : Fin n, P.topRow i = (μ.1.rowLen i : ℤ)}).trans
      (gtPatternEquivSSYT n μ.1 μ.2))

@[simp]
theorem fst_nonnegEquivBoundedSSYT_apply (P : AddSubmonoid.nonneg (GTPattern n)) :
    ((nonnegEquivBoundedSSYT n P).1 : YoungDiagram) = (P : GTPattern n).topWeight.shape :=
  (rfl)

@[simp]
theorem coe_nonnegEquivBoundedSSYT_symm_apply
    (s : Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.1) :
    ((nonnegEquivBoundedSSYT n).symm s : GTPattern n) =
      SemistandardYoungTableau.toGTPattern s.2.1 n :=
  gtPatternEquivSSYT_symm_apply_coe n s.1.1 s.1.2 s.2

end GTPattern

/-! ### Tableau products of flag minors and their leading terms -/

namespace BoundedSSYT

/-- **The tableau product of flag minors**: for a bounded semistandard tableau `T` of shape `μ`, the
product of the flag minors of its nonempty columns `T.colFinset m`, `m < μ.rowLen 0`. -/
noncomputable def flagMinorProd (R : Type*) [CommRing R] (T : BoundedSSYT n μ) :
    MvPolynomial (Fin n × Fin n) R :=
  ∏ m ∈ range (μ.rowLen 0), flagMinor R (T.colFinset m)

theorem flagMinorProd_def (R : Type*) [CommRing R] (T : BoundedSSYT n μ) :
    T.flagMinorProd R = ∏ m ∈ range (μ.rowLen 0), flagMinor R (T.colFinset m) :=
  (rfl)

@[simp]
theorem flagMinorProd_bot (R : Type*) [CommRing R] (T : BoundedSSYT n (⊥ : YoungDiagram)) :
    T.flagMinorProd R = 1 := by
  simp [flagMinorProd_def]

/-- Tableau products of flag minors commute with a change of coefficient ring. -/
@[simp]
theorem map_flagMinorProd {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T : BoundedSSYT n μ) : map f (T.flagMinorProd R) = T.flagMinorProd S := by
  simp [flagMinorProd_def, map_prod]

/-- Under the row-major lexicographic order, every tableau product of flag minors is monic. -/
@[simp]
theorem monic_rename_toLex_flagMinorProd (R : Type*) [CommRing R] (T : BoundedSSYT n μ) :
    lex.Monic (rename toLex (T.flagMinorProd R)) := by
  rw [flagMinorProd_def, map_prod]
  exact Monic.prod fun m _ ↦ monic_rename_toLex_flagMinor R (T.colFinset m)

/-- Under the row-major lexicographic order, the leading exponent of `T.flagMinorProd R` is the sum
of the diagonal exponents of its columns. -/
@[simp]
theorem degree_rename_toLex_flagMinorProd (R : Type*) [CommRing R] [Nontrivial R]
    (T : BoundedSSYT n μ) :
    lex.degree (rename toLex (T.flagMinorProd R)) =
      ∑ m ∈ range (μ.rowLen 0), flagDiagonalExponent (T.colFinset m) := by
  rw [flagMinorProd_def, map_prod, lex.degree_prod_of_regular fun m _ ↦ by
    rw [(monic_rename_toLex_flagMinor R (T.colFinset m)).leadingCoeff_eq_one]
    exact isRegular_one]
  exact sum_congr rfl fun m _ ↦ degree_rename_toLex_flagMinor R (T.colFinset m)

/-- **Pattern comparison for tableau products.** The partial column sums of the leading exponent of
`T.flagMinorProd R` form the Gelfand-Tsetlin pattern `toGTPattern T.1 n`. -/
theorem exponentEntries_degree_rename_toLex_flagMinorProd (R : Type*) [CommRing R] [Nontrivial R]
    (T : BoundedSSYT n μ) :
    GTPattern.exponentEntries (lex.degree (rename toLex (T.flagMinorProd R))) =
      ⇑(SemistandardYoungTableau.toGTPattern T.1 n) := by
  rw [T.degree_rename_toLex_flagMinorProd R, map_sum, ← T.sum_rowSubset_colFinset,
    GTPattern.coe_sum]
  exact sum_congr rfl fun m _ ↦ GTPattern.exponentEntries_flagDiagonalExponent _

/-- Under the row-major lexicographic order, the leading term of `T.flagMinorProd R` is the product
of the diagonal monomials of its columns. -/
@[simp]
theorem leadingTerm_rename_toLex_flagMinorProd (R : Type*) [CommRing R] (T : BoundedSSYT n μ) :
    lex.leadingTerm (rename toLex (T.flagMinorProd R)) =
      monomial (∑ m ∈ range (μ.rowLen 0), flagDiagonalExponent (T.colFinset m)) 1 := by
  nontriviality R
  rw [MonomialOrder.leadingTerm, T.degree_rename_toLex_flagMinorProd R,
    (T.monic_rename_toLex_flagMinorProd R).leadingCoeff_eq_one]

@[simp]
theorem flagMinorProd_ne_zero (R : Type*) [CommRing R] [Nontrivial R] (T : BoundedSSYT n μ) :
    T.flagMinorProd R ≠ 0 := fun h ↦
  (T.monic_rename_toLex_flagMinorProd R).ne_zero (by rw [h, map_zero])

/-- **Distinct bounded tableaux have distinct leading exponents**, across all shapes `μ` with at
most `n` rows. -/
theorem degree_rename_toLex_flagMinorProd_injective (R : Type*) [CommRing R] [Nontrivial R] :
    Function.Injective
      (fun s : (Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.1) ↦
        lex.degree (rename toLex (s.2.flagMinorProd R))) := by
  intro s₁ s₂ h
  apply (GTPattern.nonnegEquivBoundedSSYT n).symm.injective
  apply Subtype.ext
  apply DFunLike.coe_injective
  rw [GTPattern.coe_nonnegEquivBoundedSSYT_symm_apply,
    GTPattern.coe_nonnegEquivBoundedSSYT_symm_apply,
    ← s₁.2.exponentEntries_degree_rename_toLex_flagMinorProd R,
    ← s₂.2.exponentEntries_degree_rename_toLex_flagMinorProd R]
  exact congrArg GTPattern.exponentEntries h

/-- **The leading exponents of the tableau products exhaust the diagonal-exponent monoid.** -/
theorem range_degree_rename_toLex_flagMinorProd (R : Type*) [CommRing R] [Nontrivial R] :
    Set.range
      (fun s : (Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.1) ↦
        lex.degree (rename toLex (s.2.flagMinorProd R))) =
      (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))) :
        Set (Fin n ×ₗ Fin n →₀ ℕ)) := by
  refine Set.Subset.antisymm (Set.range_subset_iff.mpr fun s ↦ ?_) ?_
  · rw [SetLike.mem_coe, s.2.degree_rename_toLex_flagMinorProd R]
    exact AddSubmonoid.sum_mem _ fun m _ ↦ AddSubmonoid.subset_closure ⟨_, rfl⟩
  · intro e he
    let P := GTPattern.flagExponentEquiv ⟨e, he⟩
    let s := GTPattern.nonnegEquivBoundedSSYT n P
    refine ⟨s, GTPattern.exponentEntries_injective ?_⟩
    rw [s.2.exponentEntries_degree_rename_toLex_flagMinorProd R,
      ← GTPattern.coe_nonnegEquivBoundedSSYT_symm_apply s, Equiv.symm_apply_apply,
      GTPattern.coe_flagExponentEquiv_apply]

end BoundedSSYT

/-! ### Row-content and fundamental column-shape multigradings -/

/-- Each flag minor `flagMinor R I` is multihomogeneous for the row multigrading on the generic
`n × n` matrix, of multidegree the indicator function of `I`. -/
theorem isMultiHomogeneous_flagMinor (R : Type*) [CommRing R] (I : Finset (Fin n)) :
    IsMultiHomogeneous (fun r : Fin n ↦ if r ∈ I then 1 else 0) (flagMinor R I) := by
  rw [flagMinor_def, Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.det_apply]
  refine IsMultiHomogeneous.sum univ _ fun σ _ ↦ ?_
  have hprod : IsMultiHomogeneous
      (∑ c : Fin #I, (Pi.single (I.orderEmbOfFin rfl (σ c)) 1 : Fin n → ℕ))
      (∏ c : Fin #I, X (I.orderEmbOfFin rfl (σ c), Fin.castLE (card_finset_fin_le I) c) :
        MvPolynomial (Fin n × Fin n) R) :=
    IsMultiHomogeneous.prod univ _ _ fun c _ ↦ isMultiHomogeneous_X _ _
  have hdeg : (∑ c : Fin #I, (Pi.single (I.orderEmbOfFin rfl (σ c)) 1 : Fin n → ℕ)) =
      fun r : Fin n ↦ if r ∈ I then 1 else 0 := by
    rw [Equiv.sum_comp σ fun c ↦ (Pi.single (I.orderEmbOfFin rfl c) 1 : Fin n → ℕ)]
    ext r
    rw [Finset.sum_apply]
    by_cases hr : r ∈ I
    · obtain ⟨c, rfl⟩ := (Finset.range_orderEmbOfFin I rfl).symm.subset hr
      rw [Fintype.sum_eq_single c fun d hd ↦
        Pi.single_eq_of_ne ((I.orderEmbOfFin rfl).injective.ne hd.symm) 1]
      simp [hr]
    · simp only [hr, ↓reduceIte]
      exact Fintype.sum_eq_zero _ fun c ↦ Pi.single_eq_of_ne
        (by rintro rfl; exact hr (I.orderEmbOfFin_mem rfl c)) 1
  rw [hdeg] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rwa [hσ, one_smul]
  · rw [hσ, Units.neg_smul, one_smul]
    exact hprod.neg

/-- Indicator weight of column `c` of the generic `n × n` matrix `(z_(r,c))`. -/
def flagColWeight (c : Fin n) : Fin n × Fin n → ℕ :=
  fun p ↦ if p.2 = c then 1 else 0

@[simp]
theorem flagColWeight_apply (c : Fin n) (p : Fin n × Fin n) :
    flagColWeight c p = if p.2 = c then 1 else 0 :=
  (rfl)

/-- Each flag minor `flagMinor R I` is weighted homogeneous for the indicator weight of column `c`,
of degree `1` if `c < #I` and `0` otherwise — the fundamental weight `(rowSubset I).topRow c`. -/
theorem isWeightedHomogeneous_flagColWeight_flagMinor (R : Type*) [CommRing R]
    (I : Finset (Fin n)) (c : Fin n) :
    (flagMinor R I).IsWeightedHomogeneous (flagColWeight c) (if (c : ℕ) < #I then 1 else 0) := by
  rw [flagMinor_def, Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum univ _ _ fun σ _ ↦ ?_
  have hprod :
      (∏ d : Fin #I, X (I.orderEmbOfFin rfl (σ d), Fin.castLE (card_finset_fin_le I) d) :
        MvPolynomial (Fin n × Fin n) R).IsWeightedHomogeneous (flagColWeight c)
        (∑ d : Fin #I, flagColWeight c
          (I.orderEmbOfFin rfl (σ d), Fin.castLE (card_finset_fin_le I) d)) :=
    IsWeightedHomogeneous.prod univ _ _ fun d _ ↦ isWeightedHomogeneous_X R _ _
  have hdeg :
      (∑ d : Fin #I, flagColWeight c
        (I.orderEmbOfFin rfl (σ d), Fin.castLE (card_finset_fin_le I) d)) =
        if (c : ℕ) < #I then 1 else 0 := by
    simp only [flagColWeight_apply]
    by_cases hc : (c : ℕ) < #I
    · rw [ite_eq_left hc, Fintype.sum_eq_single ⟨c, hc⟩ fun d hd ↦ ite_eq_right fun h ↦ hd ?_]
      · simp
      · exact Fin.ext (by simpa using congrArg Fin.val h)
    · rw [ite_eq_right hc]
      exact Fintype.sum_eq_zero _ fun d ↦
        ite_eq_right fun h ↦ hc (by simp [← h])
  rw [hdeg] at hprod
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
  · rwa [hσ, one_smul]
  · rw [hσ, Units.neg_smul, one_smul]
    exact hprod.neg

namespace BoundedSSYT

/-- Counting the columns of `T` containing a letter `r : Fin n` recovers the content
`T.weight r`. -/
theorem sum_ite_mem_colFinset_eq_weight (T : BoundedSSYT n μ) (r : Fin n) :
    (∑ m ∈ range (μ.rowLen 0), if r ∈ T.colFinset m then 1 else 0) = T.weight r := by
  rw [weight_apply, SemistandardYoungTableau.content_apply, sum_boole]
  -- Map each column `m` containing `r` at `(i, m)` to that unique cell of `μ`.
  refine Finset.card_bij
    (fun m hm ↦
      let hex := (T.mem_colFinset_iff.mp (mem_filter.mp hm).2)
      (Classical.choose hex, m))
    (fun m hm ↦ ?_) (fun _ _ _ _ h ↦ congrArg Prod.snd h) fun c hc ↦ ?_
  · obtain ⟨_, hmem⟩ := mem_filter.mp hm
    have hspec := Classical.choose_spec (T.mem_colFinset_iff.mp hmem)
    exact mem_filter.mpr ⟨(μ.mem_cells _).mpr
      (YoungDiagram.mem_iff_lt_colLen.mpr hspec.1), hspec.2⟩
  · obtain ⟨hcμ, hcr⟩ := mem_filter.mp hc
    have hcμ' := (μ.mem_cells _).mp hcμ
    have hm0 : c.2 < μ.rowLen 0 :=
      (YoungDiagram.mem_iff_lt_rowLen.mp hcμ').trans_le (μ.rowLen_anti 0 c.1 (Nat.zero_le _))
    have hrm : r ∈ T.colFinset c.2 :=
      T.mem_colFinset_iff.mpr ⟨c.1, YoungDiagram.mem_iff_lt_colLen.mp hcμ', hcr⟩
    refine ⟨c.2, mem_filter.mpr ⟨mem_range.mpr hm0, hrm⟩, ?_⟩
    have hspec := Classical.choose_spec (T.mem_colFinset_iff.mp hrm)
    refine Prod.ext ?_ rfl
    -- Column strictness makes the row index `i` with `T i c.2 = r` unique.
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (T.1.col_strict hlt hcμ').ne (hspec.2.trans hcr.symm)
    · exact (T.1.col_strict hgt (YoungDiagram.mem_iff_lt_colLen.mpr hspec.1)).ne
        (hcr.trans hspec.2.symm)

/-- **Content comparison for tableau products.** Every `T.flagMinorProd R` is multihomogeneous for
the row multigrading, of multidegree the content `⇑T.weight` of the tableau `T`. -/
theorem isMultiHomogeneous_flagMinorProd (R : Type*) [CommRing R] (T : BoundedSSYT n μ) :
    IsMultiHomogeneous (⇑(BoundedSSYT.weight T)) (T.flagMinorProd R) := by
  rw [flagMinorProd_def]
  have h := IsMultiHomogeneous.prod (range (μ.rowLen 0))
    (fun m ↦ flagMinor R (T.colFinset m))
    (fun m r ↦ if r ∈ T.colFinset m then 1 else 0)
    fun m _ ↦ isMultiHomogeneous_flagMinor R (T.colFinset m)
  convert h using 1
  ext r
  rw [Finset.sum_apply, T.sum_ite_mem_colFinset_eq_weight r]

/-- **Fundamental multigrading for tableau products.** Every `T.flagMinorProd R` is weighted
homogeneous for the indicator weight `flagColWeight c` of column `c`, of degree `μ.rowLen c`: the
column multidegree of a tableau product is the dominant weight of its shape `μ`. -/
theorem isWeightedHomogeneous_flagColWeight_flagMinorProd (R : Type*) [CommRing R]
    (T : BoundedSSYT n μ) (c : Fin n) :
    (T.flagMinorProd R).IsWeightedHomogeneous (flagColWeight c) (μ.rowLen c) := by
  rw [flagMinorProd_def]
  have h := IsWeightedHomogeneous.prod (range (μ.rowLen 0))
    (fun m ↦ flagMinor R (T.colFinset m))
    (fun m ↦ if (c : ℕ) < #(T.colFinset m) then 1 else 0)
    fun m _ ↦ isWeightedHomogeneous_flagColWeight_flagMinor R (T.colFinset m) c
  convert h using 1
  simp only [T.card_colFinset, sum_boole]
  -- `(c, m) ∈ μ` holds both as `c < μ.colLen m` and as `m < μ.rowLen c`.
  have hset : {m ∈ range (μ.rowLen 0) | (c : ℕ) < μ.colLen m} = range (μ.rowLen c) := by
    ext m
    simp only [mem_filter, mem_range, ← YoungDiagram.mem_iff_lt_colLen,
      YoungDiagram.mem_iff_lt_rowLen]
    have hle := μ.rowLen_anti 0 c (Nat.zero_le _)
    omega
  rw [hset]
  exact (card_range _).symm

end BoundedSSYT

end TauCeti

