/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Tableau
public import TauCeti.RingTheory.MvPolynomial.FlagMinor.Homogeneous

/-!
# Tableau products of flag minors and their multigradings

A bounded semistandard Young tableau `T : BoundedSSYT n μ` of shape `μ` with entries in
`{0, …, n - 1}` has strictly increasing columns, so its `m`-th column determines a set
`T.colFinset m` of `μ.colLen m` rows of the generic `n × n` matrix. Multiplying the corresponding
flag minors across the nonempty columns `m < μ.rowLen 0` produces the **tableau product**
`T.flagMinorProd R`. Conversely, any `FlagTableauLe`-chain of nonempty row subsets arises as the
columns of a bounded tableau whose tableau product is the product of those flag minors
(`TauCeti.exists_boundedSSYT_flagMinorProd_eq`).

Under the row-major lexicographic order on the matrix variables, each `T.flagMinorProd R` is monic
over every commutative ring `R`. Over any nontrivial commutative ring `R`, the partial column sums
of its leading exponent form the Gelfand-Tsetlin pattern
`SemistandardYoungTableau.toGTPattern T.1 n` attached to `T`. Since
`TauCeti.GTPattern.nonnegEquivBoundedSSYT` identifies the additive monoid
`AddSubmonoid.nonneg (GTPattern n)` of polynomial Gelfand-Tsetlin patterns with the sigma type of
bounded semistandard tableaux over all shapes `μ` with at most `n` rows, over `[Nontrivial R]` the
tableau products have pairwise distinct leading exponents whose range is the diagonal-exponent
monoid `AddSubmonoid.closure (Set.range flagDiagonalExponent)`.

Finally, `T.flagMinorProd R` is doubly multihomogeneous:
* for the **row multigrading** `MvPolynomial.IsMultiHomogeneous`, its multidegree is the content
  `⇑T.weight` of the tableau (`TauCeti.BoundedSSYT.isMultiHomogeneous_flagMinorProd`);
* for the **fundamental column multigrading** `TauCeti.flagColWeight`, its degree in column `c` of
  the generic matrix is `μ.rowLen c`, so each `T.flagMinorProd R` has column multidegree the shape
  `μ` (`TauCeti.BoundedSSYT.isWeightedHomogeneous_flagColWeight_flagMinorProd`).

## Main definitions

* `TauCeti.BoundedSSYT.flagMinorProd`: the product of the flag minors of the columns of a bounded
  semistandard tableau.

## Main results

* `TauCeti.exists_boundedSSYT_flagMinorProd_eq`: reconstruction of a tableau product from a
  `FlagTableauLe`-chain of nonempty row subsets.
* `TauCeti.BoundedSSYT.monic_rename_toLex_flagMinorProd`: `T.flagMinorProd R` is monic over every
  `CommRing R`.
* `TauCeti.BoundedSSYT.degree_rename_toLex_flagMinorProd`,
  `TauCeti.BoundedSSYT.exponentEntries_degree_rename_toLex_flagMinorProd`, and
  `TauCeti.BoundedSSYT.degree_rename_toLex_flagMinorProd_eq_coe_flagExponentEquiv_symm`: over
  `[Nontrivial R]`, the leading exponent of `T.flagMinorProd R` is the sum of its column diagonal
  exponents, records `toGTPattern T.1 n`, and matches `flagExponentEquiv.symm` via
  `nonnegEquivBoundedSSYT.symm`.
* `TauCeti.BoundedSSYT.degree_rename_toLex_flagMinorProd_injective` and
  `TauCeti.BoundedSSYT.range_degree_rename_toLex_flagMinorProd`: over `[Nontrivial R]`, the leading
  exponents of the tableau products biject onto
  `AddSubmonoid.closure (Set.range flagDiagonalExponent)`.
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

/-- Every tableau product of flag minors lies in `flagMinorAlgebra n R`. -/
theorem flagMinorProd_mem_flagMinorAlgebra (R : Type*) [CommRing R] (T : BoundedSSYT n μ) :
    T.flagMinorProd R ∈ flagMinorAlgebra n R := by
  rw [T.flagMinorProd_def R]
  exact prod_mem fun _ _ ↦ flagMinor_mem_flagMinorAlgebra R _

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
      ⇑(SemistandardYoungTableau.toGTPattern T.val n) := by
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

/-- **Equivalence compatibility for tableau leading exponents.** Over `[Nontrivial R]`, the
row-major lexicographic leading exponent of `s.snd.flagMinorProd R` is the underlying exponent of
`GTPattern.flagExponentEquiv.symm ((GTPattern.nonnegEquivBoundedSSYT n).symm s)`. -/
theorem degree_rename_toLex_flagMinorProd_eq_coe_flagExponentEquiv_symm (R : Type*) [CommRing R]
    [Nontrivial R] (s : Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.val) :
    lex.degree (rename toLex (s.snd.flagMinorProd R)) =
      (GTPattern.flagExponentEquiv.symm ((GTPattern.nonnegEquivBoundedSSYT n).symm s) :
        Fin n ×ₗ Fin n →₀ ℕ) := by
  refine GTPattern.exponentEntries_injective ?_
  rw [s.snd.exponentEntries_degree_rename_toLex_flagMinorProd R,
    ← GTPattern.coe_nonnegEquivBoundedSSYT_symm_apply s,
    ← GTPattern.coe_flagExponentEquiv_apply, AddEquiv.apply_symm_apply]

/-- **Distinct bounded tableaux have distinct leading exponents**, across all shapes `μ` with at
most `n` rows. -/
theorem degree_rename_toLex_flagMinorProd_injective (R : Type*) [CommRing R] [Nontrivial R] :
    Function.Injective
      (fun s : (Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.val) ↦
        lex.degree (rename toLex (s.snd.flagMinorProd R))) := by
  intro s₁ s₂ h
  simp only [degree_rename_toLex_flagMinorProd_eq_coe_flagExponentEquiv_symm] at h
  exact (GTPattern.nonnegEquivBoundedSSYT n).symm.injective
    (GTPattern.flagExponentEquiv.symm.injective (Subtype.ext h))

/-- **The leading exponents of the tableau products exhaust the diagonal-exponent monoid.** -/
theorem range_degree_rename_toLex_flagMinorProd (R : Type*) [CommRing R] [Nontrivial R] :
    Set.range
      (fun s : (Σ μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}, BoundedSSYT n μ.val) ↦
        lex.degree (rename toLex (s.snd.flagMinorProd R))) =
      (AddSubmonoid.closure (Set.range (flagDiagonalExponent (n := n))) :
        Set (Fin n ×ₗ Fin n →₀ ℕ)) := by
  ext e
  simp only [Set.mem_range, degree_rename_toLex_flagMinorProd_eq_coe_flagExponentEquiv_symm,
    SetLike.mem_coe]
  refine ⟨?_, fun he ↦ ?_⟩
  · rintro ⟨s, rfl⟩
    exact (GTPattern.flagExponentEquiv.symm _).property
  · refine ⟨GTPattern.nonnegEquivBoundedSSYT n (GTPattern.flagExponentEquiv ⟨e, he⟩), ?_⟩
    simp

end BoundedSSYT

/-- Every `FlagTableauLe`-chain of nonempty subsets of `Fin n` is the sequence of nonempty columns
of a bounded semistandard Young tableau of width `k` and shape with at most `n` rows, whose
tableau product equals the product of the corresponding flag minors. -/
theorem exists_boundedSSYT_flagMinorProd_eq {k : ℕ} (R : Type*) [CommRing R]
    (I : Fin k → Finset (Fin n)) (hne : ∀ m, (I m).Nonempty)
    (hchain : ∀ m₁ m₂, m₁ ≤ m₂ → FlagTableauLe (I m₁) (I m₂)) :
    ∃ (μ : {μ : YoungDiagram // μ.colLen 0 ≤ n}) (T : BoundedSSYT n μ.val),
      μ.val.rowLen 0 = k ∧ (∀ m : Fin k, T.colFinset m = I m) ∧
        T.flagMinorProd R = ∏ m : Fin k, flagMinor R (I m) := by
  obtain ⟨μ, T, hrow0, hcol⟩ := exists_boundedSSYT_colFinset_eq I hne hchain
  refine ⟨μ, T, hrow0, hcol, ?_⟩
  rw [T.flagMinorProd_def R, hrow0, ← Fin.prod_univ_eq_prod_range]
  exact Fintype.prod_congr _ _ fun m ↦ congrArg (flagMinor R) (hcol m)

/-! ### Row-content and fundamental column-shape multigradings -/

namespace BoundedSSYT

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
