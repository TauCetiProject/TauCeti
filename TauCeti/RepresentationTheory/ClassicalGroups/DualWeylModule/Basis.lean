/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import TauCeti.Combinatorics.Young.Interlacing
public import TauCeti.RepresentationTheory.ClassicalGroups.DualWeylModule.LeadingTerm
import TauCeti.Combinatorics.Young.Diagram
import TauCeti.Combinatorics.Young.OfRowLens
import TauCeti.RingTheory.MvPolynomial.DeterminantalIdeal
import TauCeti.RingTheory.MvPolynomial.MonomialOrder

/-!
# The standard bideterminant basis of the dual Weyl module

Let `R` be a commutative ring and `μ` a Young diagram with at most `n` rows. The bideterminants
of the semistandard tableaux of shape `μ` with entries smaller than `N`
(`TauCeti.BoundedSSYT N μ`) form an `R`-basis of the dual Weyl module of the `N × n` matrix of
variables with column degrees the row lengths of `μ` (`TauCeti.DualWeylModule.standardBasis`).
The bideterminant of a filling `T` is the product over the columns `j` of `μ` of the minor of `x`
on the rows `T (0, j), …, T (μ.colLen j - 1, j)` and the first `μ.colLen j` columns.

The proof is an induction on `N`, through the branching of tableaux
(`TauCeti.BoundedSSYT.fiberEquiv`): a tableau of shape `μ` in `N + 1` letters is a tableau of a
shape `ν` interlacing `μ` in `N` letters, with the top letter `N` filling the horizontal strip
`μ / ν`. Expanded in the last row, its bideterminant has leading term `y ^ (μ - ν)` times the
bideterminant of the smaller tableau (`TauCeti.DualWeylModule.hasLeadingTerm_bideterminant_extend`):
in each column the top letter sits at the bottom, and the minor expanded along its last row is
led by the variable of its last column. Distinct `ν` give distinct exponents, so the standard
bideterminants are linearly independent over every ring. Conversely, the leading coefficient of
a nonzero dual Weyl vector `f` lies in the dual Weyl module of a shape `ν` interlacing `μ`
(`TauCeti.DualWeylModule.leadingCoeff_lastRowEquiv_mem`,
`TauCeti.DualWeylModule.degree_lastRowEquiv_add_le`), hence is a combination of standard
bideterminants of shape `ν`; subtracting the same combination of the bordered bideterminants
lowers the leading exponent of `f`, and induction on it shows that the standard bideterminants
span. Every subtraction keeps the coefficients in `R`, which is the saturation of the basis.

## Main definitions

* `TauCeti.DualWeylModule.ssytFilling`: a bounded semistandard tableau as a filling by rows.
* `TauCeti.DualWeylModule.standardBasis`: the standard bideterminant basis.

## Main results

* `TauCeti.DualWeylModule.linearIndependent_bideterminant_ssytFilling` and
  `TauCeti.DualWeylModule.dualWeylModule_le_span_bideterminant_ssytFilling`: the standard
  bideterminants are linearly independent and span the dual Weyl module, over every commutative
  ring.
* `TauCeti.DualWeylModule.span_range_bideterminant_eq`: the bideterminants of all fillings span the
  dual Weyl module.
* `TauCeti.DualWeylModule.finrank_dualWeylModule`: its rank is the number of semistandard
  tableaux.
* `TauCeti.DualWeylModule.span_map_dualWeylModule`: base change, `∇_S` is the `S`-span of the
  image of `∇_R`.
* `TauCeti.DualWeylModule.mem_span_bideterminant_ssytFilling_of_map`: saturation, for an
  injective change of coefficients (for instance a domain in its field of fractions).

## References

* C. De Concini, D. Eisenbud, C. Procesi, *Young diagrams and determinantal varieties*,
  Invent. Math. **56** (1980), 129-165.
* K. Akin, D. A. Buchsbaum, J. Weyman, *Schur functors and Schur complexes*, Adv. Math. **44**
  (1982), 207-278, II.2.16.

The induction by bordering is adapted from grh-lean (https://github.com/lsernau/grh-lean,
Apache 2.0, Copyright 2026 Anthropic PBC), `src/Lib/GLn/SchurModule/MinorBasis.lean`
(`New.GL.exists_bordering`, `New.GL.nabla_le_span_of_hasLeadingTerm` and
`New.GL.exists_isStdMinorFamily`). grh-lean only shows that some family of fillings is a basis;
here the bordering is chosen to be the branching of semistandard tableaux, so the basis is indexed
by them.
-/

public section

namespace TauCeti

open MvPolynomial Finset

open scoped _root_.MonomialOrder

open TauCeti.MonomialOrder (colex)

namespace DualWeylModule

variable {R : Type*} [CommRing R] {N n : ℕ}

/-! ### Minors in the last-row expansion -/

/-- A minor on rows other than the last does not involve the variables of the last row. -/
theorem lastRowEquiv_mvPolynomialMinor_castSucc {k : Type*} [Fintype k] [DecidableEq k]
    (r : k → Fin N) (c : k → Fin n) :
    lastRowEquiv R N n (Matrix.mvPolynomialMinor R (fun a => (r a).castSucc) c) =
      C (Matrix.mvPolynomialMinor R r c) := by
  rw [Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.mvPolynomialMinor_eq_det_submatrix,
    ← AlgEquiv.coe_toAlgHom, AlgHom.map_det, RingHom.map_det]
  congr 1
  ext a b
  simp

/-- The expansion along the last row of a minor on `k` rows other than the last, bordered by the
last row, on the first `k + 1` columns. -/
theorem lastRowEquiv_mvPolynomialMinor_snoc {k : ℕ} (hk : k + 1 ≤ n) (r : Fin k → Fin N) :
    lastRowEquiv R N n (Matrix.mvPolynomialMinor R
        (Fin.snoc (fun a => (r a).castSucc) (Fin.last N)) (Fin.castLE hk)) =
      ∑ b : Fin (k + 1), monomial (Finsupp.single (Fin.castLE hk b) 1)
        ((-1) ^ (k + (b : ℕ)) * Matrix.mvPolynomialMinor R r (Fin.castLE hk ∘ b.succAbove)) := by
  rw [Matrix.mvPolynomialMinor_eq_det_submatrix, Matrix.det_succ_row _ (Fin.last k), map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h_sub : ((Matrix.mvPolynomialX (Fin (N + 1)) (Fin n) R).submatrix
      (Fin.snoc (fun a => (r a).castSucc) (Fin.last N)) (Fin.castLE hk)).submatrix
        (Fin.last k).succAbove b.succAbove =
      (Matrix.mvPolynomialX (Fin (N + 1)) (Fin n) R).submatrix (fun a => (r a).castSucc)
        (Fin.castLE hk ∘ b.succAbove) := by
    ext a c
    simp [Fin.succAbove_last]
  rw [h_sub, ← Matrix.mvPolynomialMinor_eq_det_submatrix, map_mul, map_mul,
    lastRowEquiv_mvPolynomialMinor_castSucc, ← C_mul_X_eq_monomial]
  simp
  ring

/-- **Bordering a minor by the last row.** The expansion in the last row of the minor on `k` rows
other than the last, bordered by the last row, on the first `k + 1` columns, has leading term the
variable `y_k` of the last row times the minor on the `k` rows and the first `k` columns. -/
theorem hasLeadingTerm_lastRowEquiv_mvPolynomialMinor_snoc {k : ℕ} (hk : k + 1 ≤ n)
    (r : Fin k → Fin N) :
    colex.HasLeadingTerm (lastRowEquiv R N n (Matrix.mvPolynomialMinor R
        (Fin.snoc (fun a => (r a).castSucc) (Fin.last N)) (Fin.castLE hk)))
      (Finsupp.single ⟨k, hk⟩ 1)
      (Matrix.mvPolynomialMinor R r (Fin.castLE (k.le_succ.trans hk))) := by
  rw [lastRowEquiv_mvPolynomialMinor_snoc]
  have h_last : Fin.castLE hk ∘ (Fin.last k).succAbove = Fin.castLE (k.le_succ.trans hk) := by
    ext a
    simp [Fin.succAbove_last]
  have := MonomialOrder.HasLeadingTerm.sum (m := colex) (s := univ)
    (F := fun b : Fin (k + 1) => monomial (Finsupp.single (Fin.castLE hk b) 1)
      ((-1) ^ (k + (b : ℕ)) * Matrix.mvPolynomialMinor R r (Fin.castLE hk ∘ b.succAbove)))
    (fun b => colex.hasLeadingTerm_monomial _ _) (Fin.last k) (fun b _ hb => ?_)
    (absurd (mem_univ _))
  · have h_k : Fin.castLE hk (Fin.last k) = ⟨k, hk⟩ := rfl
    simpa [h_last, ← two_mul, pow_mul, h_k] using this
  · rw [MonomialOrder.colex_single_lt_iff, Fin.lt_def]
    simpa [Fin.lt_def] using Fin.lt_last_iff_ne_last.mpr hb

/-! ### Bordering the bideterminant of a tableau -/

section Tableau

variable {μ ν : YoungDiagram}

/-- A semistandard tableau of shape `μ` in the letters `0, …, N - 1`, read as a filling of `μ` by
the rows of the `N × n` matrix of variables. -/
def ssytFilling (T : BoundedSSYT N μ) (i j : ℕ) (h : (i, j) ∈ μ) : Fin N :=
  ⟨T.val i j, T.entry_lt h⟩

@[simp]
theorem val_ssytFilling (T : BoundedSSYT N μ) (i j : ℕ) (h : (i, j) ∈ μ) :
    (ssytFilling T i j h : ℕ) = T.val i j :=
  (rfl)

/-- The exponent of the last row contributed by the column `j` of a tableau of shape `μ` whose
top letter fills `μ / ν`: the variable `y_k`, `k = ν.colLen j`, if the column `j` of `μ / ν` holds
a cell, and nothing otherwise. -/
noncomputable def borderExponent (μ ν : YoungDiagram) (hμ : μ.colLen 0 ≤ n) (j : ℕ) :
    Fin n →₀ ℕ :=
  if hlt : ν.colLen j < μ.colLen j then
    Finsupp.single ⟨ν.colLen j, hlt.trans_le ((μ.colLen_anti 0 j (Nat.zero_le j)).trans hμ)⟩ 1
  else 0

theorem borderExponent_of_lt (hμ : μ.colLen 0 ≤ n) {j : ℕ} (hlt : ν.colLen j < μ.colLen j) :
    borderExponent μ ν hμ j =
      Finsupp.single ⟨ν.colLen j, hlt.trans_le ((μ.colLen_anti 0 j (Nat.zero_le j)).trans hμ)⟩ 1 :=
  dite_eq_left hlt

theorem borderExponent_of_not_lt (hμ : μ.colLen 0 ≤ n) {j : ℕ} (hlt : ¬ν.colLen j < μ.colLen j) :
    borderExponent μ ν hμ j = 0 :=
  dite_eq_right hlt

/-- **Bordering a column.** Let `T` be a tableau of shape `ν` in `N` letters, `ν` interlacing
`μ`, and `extend h T` the tableau of shape `μ` in `N + 1` letters obtained by writing the top
letter `N` in the cells of `μ / ν`. The expansion in the last row of the minor of `extend h T` at
the column `j` has leading term `y ^ borderExponent j` times the minor of `T` at the column `j`. -/
theorem hasLeadingTerm_columnMinor_extend (h : μ.InterlacedBy ν) (hμ : μ.colLen 0 ≤ n)
    (T : BoundedSSYT N ν) (j : ℕ) :
    colex.HasLeadingTerm
      (lastRowEquiv R N n (columnMinor R μ hμ (ssytFilling (BoundedSSYT.extend h T)) j))
      (borderExponent μ ν hμ j)
      (columnMinor R ν ((YoungDiagram.colLen_le_of_le h.le 0).trans hμ) (ssytFilling T) j) := by
  have h₁ := YoungDiagram.colLen_le_of_le h.le j
  have h₂ := h.colLen_le_colLen_add_one j
  -- Reindexing the first `μ.colLen j` columns along `μ.colLen j = k` gives the first `k` columns.
  have h_cols {k : ℕ} (heq : μ.colLen j = k) :
      Fin.castLE ((μ.colLen_anti 0 j (Nat.zero_le j)).trans hμ) ∘ finCongr heq.symm =
        Fin.castLE (heq ▸ ((μ.colLen_anti 0 j (Nat.zero_le j)).trans hμ)) := by
    ext
    simp
  rw [columnMinor_def, columnMinor_def]
  by_cases hlt : ν.colLen j < μ.colLen j
  · have heq : μ.colLen j = ν.colLen j + 1 := by omega
    rw [borderExponent_of_lt hμ hlt,
      ← Matrix.mvPolynomialMinor_comp_equiv R (finCongr heq.symm)]
    have h_rows : (fun a : Fin (μ.colLen j) => ssytFilling (BoundedSSYT.extend h T) a j
        (YoungDiagram.mem_iff_lt_colLen.mpr a.isLt)) ∘ finCongr heq.symm =
        Fin.snoc (fun a : Fin (ν.colLen j) => (ssytFilling T a j
          (YoungDiagram.mem_iff_lt_colLen.mpr a.isLt)).castSucc) (Fin.last N) := by
      funext a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · have h_notMem : ((ν.colLen j : ℕ), j) ∉ ν := fun hm =>
          lt_irrefl _ (YoungDiagram.mem_iff_lt_colLen.mp hm)
        have h_mem : ((ν.colLen j : ℕ), j) ∈ μ := YoungDiagram.mem_iff_lt_colLen.mpr hlt
        ext
        simp [h_notMem, h_mem]
      · have h_mem : ((a : ℕ), j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr a.isLt
        ext
        simp [h_mem]
    rw [h_rows, h_cols heq]
    exact hasLeadingTerm_lastRowEquiv_mvPolynomialMinor_snoc _ _
  · have heq : μ.colLen j = ν.colLen j := by omega
    rw [borderExponent_of_not_lt hμ hlt,
      ← Matrix.mvPolynomialMinor_comp_equiv R (finCongr heq.symm)]
    have h_rows : (fun a : Fin (μ.colLen j) => ssytFilling (BoundedSSYT.extend h T) a j
        (YoungDiagram.mem_iff_lt_colLen.mpr a.isLt)) ∘ finCongr heq.symm =
        fun a : Fin (ν.colLen j) => (ssytFilling T a j
          (YoungDiagram.mem_iff_lt_colLen.mpr a.isLt)).castSucc := by
      funext a
      have h_mem : ((a : ℕ), j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr a.isLt
      ext
      simp [h_mem]
    rw [h_rows, h_cols heq, lastRowEquiv_mvPolynomialMinor_castSucc, C_apply]
    exact colex.hasLeadingTerm_monomial _ _

/-- The cells of the horizontal strip `μ / ν` in the row `s` are counted by `μ.rowLen s -
ν.rowLen s`, and each lies at the bottom of its column. -/
theorem sum_borderExponent (h : μ.InterlacedBy ν) (hμ : μ.colLen 0 ≤ n) :
    ∑ j ∈ range (μ.rowLen 0), borderExponent μ ν hμ j = YoungDiagram.rowLenDiff μ ν := by
  classical
  ext s
  have h_apply (j : ℕ) : borderExponent μ ν hμ j s =
      if ν.colLen j < μ.colLen j ∧ (s : ℕ) = ν.colLen j then 1 else 0 := by
    by_cases h₁ : ν.colLen j < μ.colLen j
    · simp [borderExponent_of_lt hμ h₁, h₁, Finsupp.single_apply, Fin.ext_iff, eq_comm]
    · simp [borderExponent_of_not_lt hμ h₁, h₁]
  -- The column `j` holds a cell of `μ / ν` in the row `s` exactly for `ν.rowLen s ≤ j <
  -- μ.rowLen s`.
  have h_filter : (range (μ.rowLen 0)).filter
      (fun j => ν.colLen j < μ.colLen j ∧ (s : ℕ) = ν.colLen j) =
        Ico (ν.rowLen s) (μ.rowLen s) := by
    ext j
    have h₂ := h.colLen_le_colLen_add_one j
    have hμs := μ.rowLen_anti 0 s (Nat.zero_le _)
    have hA : j < μ.rowLen s ↔ (s : ℕ) < μ.colLen j := by
      rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    have hB : j < ν.rowLen s ↔ (s : ℕ) < ν.colLen j := by
      rw [← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨-, hlt, hs⟩
      exact ⟨not_lt.mp fun h' => by have := hB.mp h'; omega, hA.mpr (by omega)⟩
    · rintro ⟨hν, hμ'⟩
      have h₃ := hA.mp hμ'
      have h₄ : ¬ (s : ℕ) < ν.colLen j := fun h' => absurd (hB.mpr h') (not_lt.mpr hν)
      exact ⟨hμ'.trans_le hμs, by omega, by omega⟩
  simp only [Finsupp.finsetSum_apply, h_apply, Finset.sum_boole, h_filter, Nat.card_Ico,
    YoungDiagram.rowLenDiff_apply, Nat.cast_id]

/-- **Bordering a bideterminant.** Let `T` be a tableau of shape `ν` in `N` letters, `ν`
interlacing `μ`, and `extend h T` the tableau of shape `μ` in `N + 1` letters obtained by writing
the top letter `N` in the cells of `μ / ν`. The expansion in the last row of the bideterminant of
`extend h T` has leading term `y ^ (μ - ν)` times the bideterminant of `T`, where `(μ - ν) s =
μ.rowLen s - ν.rowLen s`. -/
theorem hasLeadingTerm_bideterminant_extend (h : μ.InterlacedBy ν) (hμ : μ.colLen 0 ≤ n)
    (T : BoundedSSYT N ν) :
    colex.HasLeadingTerm
      (lastRowEquiv R N n (bideterminant R μ hμ (ssytFilling (BoundedSSYT.extend h T))))
      (YoungDiagram.rowLenDiff μ ν)
      (bideterminant R ν ((YoungDiagram.colLen_le_of_le h.le 0).trans hμ) (ssytFilling T)) := by
  rw [bideterminant_eq_prod_range R μ _ _ le_rfl, map_prod,
    bideterminant_eq_prod_range R ν _ _ (h.rowLen_le 0),
    ← sum_borderExponent h hμ]
  exact MonomialOrder.HasLeadingTerm.prod fun j _ => hasLeadingTerm_columnMinor_extend h hμ T j

/-- Counted column by column, the cells of a tableau carrying the letter `a` are its content. -/
private theorem sum_card_column_eq_content (T : BoundedSSYT N μ) (a : Fin N) :
    ∑ j ∈ range (μ.rowLen 0), (univ.filter fun i : Fin (μ.colLen j) =>
      ssytFilling T i j (YoungDiagram.mem_iff_lt_colLen.mpr i.isLt) = a).card =
        SemistandardYoungTableau.content T.val a := by
  classical
  rw [SemistandardYoungTableau.content_apply, Finset.card_eq_sum_card_fiberwise
    (f := Prod.snd) (t := range (μ.rowLen 0)) fun c hc => Finset.mem_range.mpr
      (YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (Nat.zero_le _) le_rfl
        ((YoungDiagram.mem_cells _).mp (Finset.mem_filter.mp hc).1)))]
  refine Finset.sum_congr rfl fun j _ => Finset.card_bij (fun i _ => ((i : ℕ), j))
    (fun i hi => ?_) (fun i _ i' _ h => Fin.ext (Prod.mk.inj h).1) fun c hc => ?_
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, and_true]
    exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr i.isLt, by simpa [Fin.ext_iff] using hi⟩
  · simp only [Finset.mem_filter, YoungDiagram.mem_cells] at hc
    obtain ⟨⟨hc, ha⟩, rfl⟩ := hc
    refine ⟨⟨c.1, YoungDiagram.mem_iff_lt_colLen.mp hc⟩, ?_, rfl⟩
    simp [Fin.ext_iff, ha]

/-- **Standard bideterminants are weight vectors.** The bideterminant of a tableau `T` has degree
`content T a` in the row `a`, the number of entries of `T` equal to `a`. -/
theorem isWeightedHomogeneous_bideterminant (hμ : μ.colLen 0 ≤ n) (T : BoundedSSYT N μ)
    (a : Fin N) :
    IsWeightedHomogeneous (rowWeight a) (bideterminant R μ hμ (ssytFilling T))
      (SemistandardYoungTableau.content T.val a) := by
  rw [bideterminant_eq_prod_range R μ hμ _ le_rfl, ← sum_card_column_eq_content T a]
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ => by
    rw [columnMinor_def]
    exact isWeightedHomogeneous_mvPolynomialMinor R a _ _

end Tableau

/-! ### Linear independence -/

section Independence

variable (R) in
/-- **The standard bideterminants are linearly independent** over every commutative ring: the
bideterminants of the semistandard tableaux of shape `μ` in the letters `0, …, N - 1`. -/
theorem linearIndependent_bideterminant_ssytFilling (N : ℕ) (μ : YoungDiagram)
    (hμ : μ.colLen 0 ≤ n) :
    LinearIndependent R fun T : BoundedSSYT N μ => bideterminant R μ hμ (ssytFilling T) := by
  induction N generalizing μ with
  | zero =>
    rw [Fintype.linearIndependent_iff]
    intro g hg T
    -- With no letters, the only tableau is the empty one, whose bideterminant is `1`.
    obtain rfl : μ = ⊥ := by
      refine le_bot_iff.mp fun c hc => ?_
      have hmem : (0, 0) ∈ μ := μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hc
      exact absurd (BoundedSSYT.entry_lt T hmem) (Nat.not_lt_zero _)
    rw [Fintype.sum_unique, bideterminant_eq_prod_range R _ _ _ (by simp : _ ≤ 0),
      Finset.prod_range_zero, smul_eq_C_mul, mul_one, C_eq_zero] at hg
    rwa [Subsingleton.elim T default]
  | succ N ih =>
    rw [← linearIndependent_equiv (BoundedSSYT.sigmaEquiv N μ)]
    refine LinearIndependent.of_comp (lastRowEquiv R N n).toLinearMap ?_
    have hν (ν : YoungDiagram.interlacingShapes N μ) : ν.val.colLen 0 ≤ n :=
      (YoungDiagram.colLen_le_of_le
        (YoungDiagram.mem_interlacingShapes.mp ν.property).1.le 0).trans hμ
    refine MonomialOrder.linearIndependent_of_hasLeadingTerm (m := colex)
      (YoungDiagram.rowLenDiff_injective hμ)
      (q := fun ν T => bideterminant R ν.val (hν ν) (ssytFilling T)) (fun i => ?_)
      fun ν => ih ν.val (hν ν)
    rw [Function.comp_apply, Function.comp_apply, BoundedSSYT.sigmaEquiv_apply]
    exact hasLeadingTerm_bideterminant_extend _ hμ i.2

end Independence

/-! ### Spanning -/

section Spanning

variable {μ : YoungDiagram}

/-- The span of the standard bideterminants lies in the dual Weyl module. -/
theorem span_bideterminant_ssytFilling_le (hμ : μ.colLen 0 ≤ n) :
    Submodule.span R (Set.range fun T : BoundedSSYT N μ => bideterminant R μ hμ (ssytFilling T)) ≤
      dualWeylModule R N fun s : Fin n => μ.rowLen s :=
  Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun T =>
    bideterminant_mem_dualWeylModule R μ hμ (ssytFilling T)

/-- The shape of the leading coefficient in the last row: the column degrees `μ - γ` of the
leading coefficient, `γ` the leading exponent, are the row lengths of a Young diagram interlacing
`μ`. -/
private theorem exists_interlacedBy {f : MvPolynomial (Fin (N + 1) × Fin n) R}
    (hμ : μ.colLen 0 ≤ n) (hf : f ∈ dualWeylModule R (N + 1) fun s : Fin n => μ.rowLen s)
    (hf0 : f ≠ 0) :
    ∃ ν : YoungDiagram, μ.InterlacedBy ν ∧ ν.colLen 0 ≤ n ∧
      (fun s : Fin n => μ.rowLen s - colex.degree (lastRowEquiv R N n f) s) =
        (fun s : Fin n => ν.rowLen s) ∧
      YoungDiagram.rowLenDiff μ ν = colex.degree (lastRowEquiv R N n f) := by
  have hγ := degree_lastRowEquiv_le hf
  have h_int (i j : Fin n) (hij : (j : ℕ) = i + 1) := degree_lastRowEquiv_add_le hf hf0 hij
  have hanti : Antitone fun s : Fin n =>
      μ.rowLen s - colex.degree (lastRowEquiv R N n f) s := by
    intro a b hab
    rcases hab.lt_or_eq with hab | rfl
    · have h₁ := h_int a ⟨a + 1, by omega⟩ rfl
      have h₂ := μ.rowLen_anti (a + 1) b (by rw [Fin.lt_def] at hab; omega)
      simp only at h₁ ⊢
      omega
    · exact le_rfl
  let ν := YoungDiagram.ofRowLensFin _ hanti
  have hν (s : Fin n) : ν.rowLen s = μ.rowLen s - colex.degree (lastRowEquiv R N n f) s :=
    YoungDiagram.rowLen_ofRowLensFin _ _ s
  have hμ_zero {s : ℕ} (hs : n ≤ s) : μ.rowLen s = 0 :=
    YoungDiagram.rowLen_eq_zero_iff.mpr (hμ.trans hs)
  refine ⟨ν, YoungDiagram.interlacedBy_iff.mpr fun i => ?_,
    YoungDiagram.colLen_zero_ofRowLensFin_le _ _, funext fun s => (hν s).symm,
    Finsupp.ext fun s => by rw [YoungDiagram.rowLenDiff_apply, hν]; have := hγ s; omega⟩
  rcases lt_or_ge i n with hi | hi
  · have h₁ := hν ⟨i, hi⟩
    have h₂ := hγ ⟨i, hi⟩
    simp only at h₁ h₂
    refine ⟨?_, by omega⟩
    rcases lt_or_ge (i + 1) n with hi' | hi'
    · have := h_int ⟨i, hi⟩ ⟨i + 1, hi'⟩ rfl
      simp only at this
      omega
    · rw [hμ_zero hi']
      exact Nat.zero_le _
  · rw [hμ_zero (hi.trans (Nat.le_succ i)), YoungDiagram.rowLen_ofRowLensFin_eq_zero_of_le _ _ hi]
    exact ⟨le_rfl, Nat.zero_le _⟩

/-- **The inductive step of spanning.** If the standard bideterminants span the dual Weyl modules
in `N` rows, then every nonzero `f` in the dual Weyl module of `μ` in `N + 1` rows agrees, up to
a combination of standard bideterminants, with a polynomial whose last-row expansion has a
smaller leading exponent, or with `0`. -/
private theorem exists_sub_degree_lt
    (ih : ∀ (ν : YoungDiagram) (hν : ν.colLen 0 ≤ n),
      dualWeylModule R N (fun s : Fin n => ν.rowLen s) ≤ Submodule.span R
        (Set.range fun T : BoundedSSYT N ν => bideterminant R ν hν (ssytFilling T)))
    (hμ : μ.colLen 0 ≤ n) {f : MvPolynomial (Fin (N + 1) × Fin n) R}
    (hf : f ∈ dualWeylModule R (N + 1) fun s : Fin n => μ.rowLen s) (hf0 : f ≠ 0) :
    ∃ g ∈ Submodule.span R (Set.range fun T : BoundedSSYT (N + 1) μ =>
        bideterminant R μ hμ (ssytFilling T)),
      f - g = 0 ∨ colex.degree (lastRowEquiv R N n (f - g)) ≺[colex]
        colex.degree (lastRowEquiv R N n f) := by
  set E := lastRowEquiv R N n f
  obtain ⟨ν, hint, hνn, hdeg, hdiff⟩ := exists_interlacedBy hμ hf hf0
  -- The leading coefficient is a combination of the standard bideterminants of shape `ν`.
  have hG := ih ν hνn (hdeg ▸ leadingCoeff_lastRowEquiv_mem hf)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hG
  -- The same combination of the bordered bideterminants has the same leading term as `f`.
  refine ⟨∑ T, c T • bideterminant R μ hμ (ssytFilling (BoundedSSYT.extend hint T)),
    Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩), ?_⟩
  have h_lead := MonomialOrder.HasLeadingTerm.sum_smul univ
    (fun T _ => hasLeadingTerm_bideterminant_extend (R := R) hint hμ T) c
  have h_map : lastRowEquiv R N n (∑ T, c T • bideterminant R μ hμ
      (ssytFilling (BoundedSSYT.extend hint T))) = ∑ T, c T • lastRowEquiv R N n
        (bideterminant R μ hμ (ssytFilling (BoundedSSYT.extend hint T))) := by
    simp [map_sum, map_smul]
  rw [hc, hdiff, ← h_map] at h_lead
  rw [or_iff_not_imp_left, map_sub]
  intro h_ne
  exact colex.degree_sub_lt (by rwa [← map_sub, Ne, EmbeddingLike.map_eq_zero_iff])
    h_lead.degree_le h_lead.coeff_eq

variable (R) in
/-- **The standard bideterminants span the dual Weyl module** over every commutative ring. -/
theorem dualWeylModule_le_span_bideterminant_ssytFilling (N : ℕ) (μ : YoungDiagram)
    (hμ : μ.colLen 0 ≤ n) :
    dualWeylModule R N (fun s : Fin n => μ.rowLen s) ≤
      Submodule.span R (Set.range fun T : BoundedSSYT N μ =>
        bideterminant R μ hμ (ssytFilling T)) := by
  induction N generalizing μ with
  | zero =>
    intro f hf
    by_cases hμ0 : μ.colLen 0 = 0
    · -- The empty shape: `f` is a constant multiple of the empty bideterminant `1`.
      obtain rfl : μ = ⊥ := le_bot_iff.mp fun c hc => absurd
        (YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem (Nat.zero_le _) (Nat.zero_le _) hc))
        (by omega)
      rw [f.eq_C_of_isEmpty, ← mul_one (C _), ← smul_eq_C_mul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, ?_⟩)
      simp [bideterminant_eq_prod_range R _ _ _ (by simp : (⊥ : YoungDiagram).rowLen 0 ≤ 0)]
    · -- A nonempty shape: there are no monomials of positive degree in no variables.
      have hn : 0 < n := (Nat.pos_of_ne_zero hμ0).trans_le hμ
      have hrow : 0 < μ.rowLen 0 := YoungDiagram.mem_iff_lt_rowLen.mp
        (YoungDiagram.mem_iff_lt_colLen.mpr (Nat.pos_of_ne_zero hμ0))
      obtain rfl : f = 0 := by
        refine MvPolynomial.ext _ _ fun m => by_contra fun hm => ?_
        have := sum_apply_eq_of_mem_support hf (mem_support_iff.mpr hm) ⟨0, hn⟩
        simp at this
        omega
      exact zero_mem _
  | succ N ih =>
    -- Strong induction on the leading exponent of the last-row expansion.
    suffices h : ∀ a, ∀ f ∈ dualWeylModule R (N + 1) (fun s : Fin n => μ.rowLen s),
        colex.toSyn (colex.degree (lastRowEquiv R N n f)) = a →
          f ∈ Submodule.span R (Set.range fun T : BoundedSSYT (N + 1) μ =>
            bideterminant R μ hμ (ssytFilling T)) from fun f hf => h _ f hf rfl
    intro a
    induction a using WellFoundedLT.induction with
    | _ a IH =>
      rintro f hf rfl
      rcases eq_or_ne f 0 with rfl | hf0
      · exact zero_mem _
      obtain ⟨g, hg, hfg⟩ := exists_sub_degree_lt ih hμ hf hf0
      rw [← sub_add_cancel f g]
      refine add_mem ?_ hg
      rcases hfg with h0 | hlt
      · rw [h0]
        exact zero_mem _
      · exact IH _ hlt (f - g) (sub_mem hf (span_bideterminant_ssytFilling_le hμ hg)) rfl

end Spanning

/-! ### The standard basis -/

section StandardBasis

variable (R) (N : ℕ) {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ n)

/-- The standard bideterminants span the dual Weyl module. -/
theorem span_bideterminant_ssytFilling_eq :
    Submodule.span R (Set.range fun T : BoundedSSYT N μ => bideterminant R μ hμ (ssytFilling T)) =
      dualWeylModule R N fun s : Fin n => μ.rowLen s :=
  le_antisymm (span_bideterminant_ssytFilling_le hμ)
    (dualWeylModule_le_span_bideterminant_ssytFilling R N μ hμ)

/-- **The span of all bideterminants.** Over every commutative ring, the bideterminants of all
fillings of the Young diagram `μ` by rows of the `N × n` matrix of variables span the dual Weyl
module of the column degrees given by the row lengths of `μ`. -/
theorem span_range_bideterminant_eq :
    Submodule.span R (Set.range (bideterminant (N := N) R μ hμ)) =
      dualWeylModule R N fun s : Fin n => μ.rowLen s :=
  le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr
      (bideterminant_mem_dualWeylModule R μ hμ)))
    ((span_bideterminant_ssytFilling_eq R N hμ).symm.le.trans
      (Submodule.span_mono (Set.range_comp_subset_range ssytFilling _)))

/-- **The standard bideterminant basis** of the dual Weyl module over a commutative ring `R`:
the bideterminants of the semistandard tableaux of shape `μ` with entries smaller than `N`. -/
noncomputable def standardBasis :
    Module.Basis (BoundedSSYT N μ) R (dualWeylModule R N fun s : Fin n => μ.rowLen s) :=
  (Module.Basis.span (linearIndependent_bideterminant_ssytFilling R N μ hμ)).map
    (LinearEquiv.ofEq _ _ (span_bideterminant_ssytFilling_eq R N hμ))

@[simp]
theorem coe_standardBasis (T : BoundedSSYT N μ) :
    (standardBasis R N hμ T : MvPolynomial (Fin N × Fin n) R) =
      bideterminant R μ hμ (ssytFilling T) := by
  simp [standardBasis, Module.Basis.span_apply]

include hμ in
/-- **The rank of the dual Weyl module** is the number of semistandard tableaux of shape `μ` with
entries smaller than `N`. -/
theorem finrank_dualWeylModule [StrongRankCondition R] :
    Module.finrank R (dualWeylModule R N fun s : Fin n => μ.rowLen s) =
      Fintype.card (BoundedSSYT N μ) :=
  Module.finrank_eq_card_basis (standardBasis R N hμ)

include hμ in
/-- **Base change.** For a homomorphism of commutative rings `φ : R → S`, the image of the dual
Weyl module over `R` spans the dual Weyl module over `S`; the standard basis is sent to the
standard basis (`TauCeti.DualWeylModule.map_bideterminant`). -/
theorem span_map_dualWeylModule {S : Type*} [CommRing S] (φ : R →+* S) :
    Submodule.span S (map φ '' (dualWeylModule R N fun s : Fin n => μ.rowLen s)) =
      dualWeylModule S N fun s : Fin n => μ.rowLen s := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact map_mem_dualWeylModule φ hf
  · rw [← span_bideterminant_ssytFilling_eq S N hμ]
    refine Submodule.span_mono (Set.range_subset_iff.mpr fun T => ⟨_,
      bideterminant_mem_dualWeylModule R μ hμ (ssytFilling T), map_bideterminant R φ μ hμ _⟩)

include hμ in
/-- **Saturation of the span of the standard bideterminants.** For an injective homomorphism of
commutative rings `φ : R → S` (for instance a domain in its field of fractions), a polynomial over
`R` whose image is a combination over `S` of the standard bideterminants is a combination over
`R` of them. -/
theorem mem_span_bideterminant_ssytFilling_of_map {S : Type*} [CommRing S] {φ : R →+* S}
    (hφ : Function.Injective φ) {f : MvPolynomial (Fin N × Fin n) R}
    (hf : map φ f ∈ Submodule.span S
      (Set.range fun T : BoundedSSYT N μ => bideterminant S μ hμ (ssytFilling T))) :
    f ∈ Submodule.span R
      (Set.range fun T : BoundedSSYT N μ => bideterminant R μ hμ (ssytFilling T)) := by
  rw [span_bideterminant_ssytFilling_eq] at hf ⊢
  exact (map_mem_dualWeylModule_iff hφ).mp hf

end StandardBasis

end DualWeylModule

end TauCeti
