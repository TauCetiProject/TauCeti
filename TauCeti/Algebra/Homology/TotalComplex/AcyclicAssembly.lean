/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import TauCeti.Algebra.Homology.Embedding.StupidTrunc
public import TauCeti.Algebra.Homology.HomologicalComplex.Basic
public import TauCeti.Algebra.Homology.HomotopyCategory.ShiftSequence
public import TauCeti.CategoryTheory.Limits.Shapes.Products

/-!
# The acyclic assembly lemma for finite antidiagonals

Let `K` be a double complex indexed by `ℤ × ℤ` in an abelian category, a complex (in `p`) of
cochain complexes `K.X p` (the columns), with total differential `d₁ + (-1)ᵖ d₂` on `(K.X p).X q`.
If each antidiagonal `p + q = n` has only finitely many nonzero terms, the direct-sum total complex
exists (`HomologicalComplex₂.hasTotal_of_finite_antidiagonals`), and it is acyclic as soon as all
columns, or all rows, are exact (`HomologicalComplex₂.acyclic_total_of_finite_antidiagonals`).
No boundedness of the double complex as a whole is assumed: for instance the double complex with
`(K.X p).X p = (K.X p).X (p + 1) = ℤ` for every `p ∈ ℤ`, joined by the identity, has one nonzero
term on each antidiagonal, exact columns and infinitely many nonzero columns.

The truncations `σ^{≥ p} K` of `K`, as a complex of columns, give the column filtration of the
total complex. The short complex `σ^{≥ p + 1} K ⟶ K ⟶ σ^{≤ p} K` is split in each bidegree, so it
induces a short exact sequence of total complexes
(`HomologicalComplex₂.totalShortComplex_shortExact`). A double complex concentrated in the column
`p` has as total complex that column shifted by `-p`
(`HomologicalComplex₂.shiftIsoTotalOfIsZero`). An induction over the columns then shows that a
double complex with finitely many nonzero columns, all exact, has an acyclic total complex. In
general the cohomology of the total complex in degree `n` only involves the antidiagonals
`n - 1`, `n` and `n + 1`, which meet finitely many columns, and truncating `K` to those columns
does not change the total complex in these degrees.

## Main definitions and results

* `HomologicalComplex₂.isIso_total_map_f`: a morphism of double complexes which is an
  isomorphism on every term of an antidiagonal induces an isomorphism of total complexes in that
  degree.
* `HomologicalComplex₂.totalShortComplex`, `HomologicalComplex₂.totalShortComplexSplitting`: the
  short complex of total complexes of a short complex of double complexes, split in each degree
  when the latter is split in each bidegree.
* `HomologicalComplex₂.shiftIsoTotalOfIsZero`, `HomologicalComplex₂.acyclic_total_of_isZero`: the
  total complex of a double complex concentrated in one column is that column, shifted, so it is
  acyclic when that column is.
* `HomologicalComplex₂.isIso_total_map_ιStupidTrunc_f`,
  `HomologicalComplex₂.isIso_total_map_πStupidTrunc_f`: brutally truncating a double complex in
  its columns does not change its total complex in the degrees whose antidiagonal vanishes in the
  removed columns.
* `HomologicalComplex₂.hasTotal_of_finite_antidiagonals`,
  `HomologicalComplex₂.hasTotal_of_isZero_X`: the total complex exists when every antidiagonal
  has finitely many nonzero terms, for instance when only finitely many columns are nonzero.
* `HomologicalComplex₂.acyclic_total_of_finite_antidiagonals`: the acyclic assembly lemma.

## References

* The Stacks Project, Tag 0133 (Homological Algebra, Lemma 25.4), which proves this through the
  spectral sequences of the double complex.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Lemma 2.7.3, the forms of the acyclic assembly lemma for half-plane double complexes of modules.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex₂

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] {I₁ I₂ I₁₂ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]

/-- A morphism of double complexes which is an isomorphism on every term `(i₁, i₂)` of the
antidiagonal `n` induces an isomorphism of total complexes in degree `n`. -/
lemma isIso_total_map_f {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c₁₂] [L.HasTotal c₁₂]
    (φ : K ⟶ L) (n : I₁₂)
    (h : ∀ i₁ i₂, ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n → IsIso ((φ.f i₁).f i₂)) :
    IsIso ((total.map φ c₁₂).f n) := by
  refine ⟨L.totalDesc fun i₁ i₂ h' ↦
    have := h i₁ i₂ h'
    inv ((φ.f i₁).f i₂) ≫ K.ιTotal c₁₂ i₁ i₂ n h', ?_, ?_⟩
  · refine total.hom_ext _ fun i₁ i₂ h' ↦ ?_
    have := h i₁ i₂ h'
    simp [ιTotal_map_assoc]
  · refine total.hom_ext _ fun i₁ i₂ h' ↦ ?_
    have := h i₁ i₂ h'
    simp

variable (S : ShortComplex (HomologicalComplex₂ C c₁ c₂))
  [S.X₁.HasTotal c₁₂] [S.X₂.HasTotal c₁₂] [S.X₃.HasTotal c₁₂]

/-- The short complex of total complexes of a short complex of double complexes. -/
noncomputable abbrev totalShortComplex : ShortComplex (HomologicalComplex C c₁₂) :=
  ShortComplex.mk (total.map S.f c₁₂) (total.map S.g c₁₂) (by
    rw [← total.map_comp, S.zero]
    ext
    simp)

/-- If a short complex of double complexes is split in each bidegree, the short complex of their
total complexes is split in each degree: the retraction and the section are the sums of those of
the terms on the antidiagonal. -/
noncomputable def totalShortComplexSplitting
    (σ : ∀ i₁ i₂, ((S.map (HomologicalComplex.eval _ c₁ i₁)).map
      (HomologicalComplex.eval C c₂ i₂)).Splitting) (n : I₁₂) :
    ((totalShortComplex c₁₂ S).map (HomologicalComplex.eval C c₁₂ n)).Splitting where
  r := S.X₂.totalDesc fun i₁ i₂ h ↦ (σ i₁ i₂).r ≫ S.X₁.ιTotal c₁₂ i₁ i₂ n h
  s := S.X₃.totalDesc fun i₁ i₂ h ↦ (σ i₁ i₂).s ≫ S.X₂.ιTotal c₁₂ i₁ i₂ n h
  f_r := total.hom_ext _ fun i₁ i₂ h ↦ by
    simpa [ιTotal_map_assoc] using (σ i₁ i₂).f_r =≫ S.X₁.ιTotal c₁₂ i₁ i₂ n h
  s_g := total.hom_ext _ fun i₁ i₂ h ↦ by
    simpa [ιTotal_map] using (σ i₁ i₂).s_g =≫ S.X₃.ιTotal c₁₂ i₁ i₂ n h
  id := total.hom_ext _ fun i₁ i₂ h ↦ by
    simpa [ιTotal_map, ιTotal_map_assoc] using (σ i₁ i₂).id =≫ S.X₂.ιTotal c₁₂ i₁ i₂ n h

end Preadditive

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {I₁ I₂ I₁₂ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} (c₁₂ : ComplexShape I₁₂)
  [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂] (S : ShortComplex (HomologicalComplex₂ C c₁ c₂))
  [S.X₁.HasTotal c₁₂] [S.X₂.HasTotal c₁₂] [S.X₃.HasTotal c₁₂]

/-- A short complex of double complexes which is split in each bidegree induces a short exact
sequence of total complexes. -/
lemma totalShortComplex_shortExact
    (σ : ∀ i₁ i₂, ((S.map (HomologicalComplex.eval _ c₁ i₁)).map
      (HomologicalComplex.eval C c₂ i₂)).Splitting) :
    (totalShortComplex c₁₂ S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    (totalShortComplexSplitting c₁₂ S σ n).shortExact

end Abelian

section Int

variable {C : Type*} [Category* C]

/-- The total complex of a double complex indexed by `ℤ × ℤ` exists in a category with finite
coproducts as soon as every antidiagonal has only finitely many nonzero terms. -/
lemma hasTotal_of_finite_antidiagonals [Preadditive C] [HasFiniteCoproducts C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (hK : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((K.X p).X (n - p))}.Finite) :
    K.HasTotal (ComplexShape.up ℤ) := fun n ↦
  TauCeti.hasCoproduct_of_finite_setOf_not_isZero _ <| by
    refine ((hK n).preimage (f := fun x : ComplexShape.π (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) ⁻¹' {n} ↦ x.val.fst) ?_).subset ?_
    · rintro ⟨⟨p, q⟩, hpq⟩ - ⟨⟨p', q'⟩, hpq'⟩ - (rfl : p = p')
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_def] at hpq hpq'
      obtain rfl : q = q' := by omega
      rfl
    · rintro ⟨⟨p, q⟩, hpq⟩ h
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_def] at hpq
      obtain rfl : q = n - p := by omega
      exact h

/-- The total complex of a double complex indexed by `ℤ × ℤ` exists in a category with finite
coproducts when its columns vanish outside `[a, b]`. -/
lemma hasTotal_of_isZero_X [Preadditive C] [HasFiniteCoproducts C]
    (L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a b : ℤ)
    (hL : ∀ p, p < a ∨ b < p → IsZero (L.X p)) : L.HasTotal (ComplexShape.up ℤ) :=
  hasTotal_of_finite_antidiagonals L fun _ ↦ (Set.finite_Icc a b).subset fun p hp ↦ by
    by_contra h
    exact hp ((HomologicalComplex.eval C _ _).map_isZero
      (hL p (by simp only [Set.mem_Icc, not_and_or, not_le] at h; exact h)))

variable [Preadditive C] (L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
  [L.HasTotal (ComplexShape.up ℤ)] (c : ℤ) (hL : ∀ p, p ≠ c → IsZero (L.X p))

include hL in
/-- In a double complex concentrated in the column `c`, the inclusion of the term `(c, q)` into the
total complex in degree `c + q` is an isomorphism. -/
lemma isIso_ιTotal_of_isZero {q n : ℤ}
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (c, q) = n) :
    IsIso (L.ιTotal (ComplexShape.up ℤ) c q n h) :=
  Cofan.IsColimit.isIso_inj_of_isInitial (L.toGradedObject.isColimitCofanMapObj _ n) _
    fun ⟨⟨p, q'⟩, hpq⟩ hne ↦ by
      have hp : p ≠ c := by
        rintro rfl
        simp only [Set.mem_preimage, Set.mem_singleton_iff, ComplexShape.π_def] at h hpq
        exact hne (Subtype.ext (Prod.ext rfl (by dsimp; omega)))
      exact ((HomologicalComplex.eval C _ q').map_isZero (hL p hp)).isInitial

/-- The total complex of a double complex concentrated in the column `c` is that column shifted by
`-c`: in degree `n` the isomorphism is the inclusion of the term `(c, n - c)`. The sign `(-1)ᶜ` of
the total differential on the column `c` is the sign of the differential of the shift by `-c`. -/
noncomputable def shiftIsoTotalOfIsZero :
    (L.X c)⟦-c⟧ ≅ L.total (ComplexShape.up ℤ) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦
      have := L.isIso_ιTotal_of_isZero c hL (q := n + -c) (n := n) (by simp)
      asIso (L.ιTotal (ComplexShape.up ℤ) c (n + -c) n _))
    (by
      rintro n _ rfl
      have hc : IsZero ((L.X (c + 1)).X (n + -c)) :=
        (HomologicalComplex.eval C _ _).map_isZero (hL _ (by omega))
      have h₁ : (ComplexShape.up ℤ).Rel c (c + 1) := rfl
      have h₁' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (c + 1, n + -c) = n + 1 := by simp only [ComplexShape.π_def]; omega
      have h₂ : (ComplexShape.up ℤ).Rel (n + -c) (n + 1 + -c) := by
        simp only [ComplexShape.up_Rel]; omega
      have h₂' : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (c, n + 1 + -c) = n + 1 := by simp only [ComplexShape.π_def]; omega
      simp [total_d, d₁_eq L _ h₁ _ _ h₁', hc.eq_of_tgt ((L.d c (c + 1)).f (n + -c)) 0,
        d₂_eq L _ c h₂ _ h₂', Int.negOnePow_neg])

/-- In degree `n`, the isomorphism `shiftIsoTotalOfIsZero` is the inclusion of the term
`(c, n - c)` into the total complex. -/
@[simp]
lemma shiftIsoTotalOfIsZero_hom_f (n : ℤ) :
    (L.shiftIsoTotalOfIsZero c hL).hom.f n =
      L.ιTotal (ComplexShape.up ℤ) c (n + -c) n (by simp) := by
  simp [shiftIsoTotalOfIsZero]

include hL in
/-- The total complex of a double complex concentrated in the column `c` is acyclic when that
column is. -/
lemma acyclic_total_of_isZero (hc : (L.X c).Acyclic) :
    (L.total (ComplexShape.up ℤ)).Acyclic := fun n ↦
  ((CochainComplex.acyclic_shift_iff _ (-c)).2 hc n).of_iso (L.shiftIsoTotalOfIsZero c hL)

/-- The inclusion of the brutal truncation of a double complex in the columns `≥ a` induces an
isomorphism of total complexes in a degree `m` whose antidiagonal vanishes in the columns `< a`. -/
lemma isIso_total_map_ιStupidTrunc_f [HasZeroObject C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a m : ℤ)
    [K.HasTotal (ComplexShape.up ℤ)]
    [HasTotal (K.stupidTrunc (ComplexShape.embeddingUpIntGE a)) (ComplexShape.up ℤ)]
    (h : ∀ p, p < a → IsZero ((K.X p).X (m - p))) :
    IsIso ((total.map (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)) (ComplexShape.up ℤ)).f
      m) :=
  isIso_total_map_f _ _ _ fun p q hpq ↦ by
    simp only [ComplexShape.π_def] at hpq
    obtain rfl : q = m - p := by omega
    by_cases hp : a ≤ p
    · have := K.isIso_ιStupidTrunc_f (ComplexShape.embeddingUpIntGE a) (i' := p)
        (i := (p - a).toNat) (by simp; omega)
      infer_instance
    · exact isIso_of_source_target_iso_zero _
        ((HomologicalComplex.eval C _ _).map_isZero
          (CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X K a (by omega))).isoZero
        (h p (by omega)).isoZero

/-- The projection of a double complex onto its brutal truncation in the columns `≤ b` induces an
isomorphism of total complexes in a degree `m` whose antidiagonal vanishes in the columns `> b`. -/
lemma isIso_total_map_πStupidTrunc_f [HasZeroObject C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (b m : ℤ)
    [K.HasTotal (ComplexShape.up ℤ)]
    [HasTotal (K.stupidTrunc (ComplexShape.embeddingUpIntLE b)) (ComplexShape.up ℤ)]
    (h : ∀ p, b < p → IsZero ((K.X p).X (m - p))) :
    IsIso ((total.map (K.πStupidTrunc (ComplexShape.embeddingUpIntLE b)) (ComplexShape.up ℤ)).f
      m) :=
  isIso_total_map_f _ _ _ fun p q hpq ↦ by
    simp only [ComplexShape.π_def] at hpq
    obtain rfl : q = m - p := by omega
    by_cases hp : p ≤ b
    · have := K.isIso_πStupidTrunc_f (ComplexShape.embeddingUpIntLE b) (i' := p)
        (i := (b - p).toNat) (by simp; omega)
      infer_instance
    · exact isIso_of_source_target_iso_zero _ (h p (by omega)).isoZero
        ((HomologicalComplex.eval C _ _).map_isZero
          (CochainComplex.isZero_stupidTrunc_embeddingUpIntLE_X K b (by omega))).isoZero

end Int

section Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- A double complex with exact columns, which vanish outside `[a, a + k)`, has an acyclic total
complex. -/
private lemma acyclic_total_of_isZero_X (k : ℕ) :
    ∀ (a : ℤ) (L : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
      [L.HasTotal (ComplexShape.up ℤ)], (∀ p, p < a ∨ a + k ≤ p → IsZero (L.X p)) →
      (∀ p, (L.X p).Acyclic) → (L.total (ComplexShape.up ℤ)).Acyclic := by
  induction k with
  | zero =>
    intro a L _ hL _ n
    refine ShortComplex.exact_of_isZero_X₂ _ ?_
    rw [IsZero.iff_id_eq_zero]
    exact total.hom_ext _ fun p q h ↦
      ((HomologicalComplex.eval C _ q).map_isZero (hL p (by omega))).eq_of_src _ _
  | succ k ih =>
    -- Split off the column `a` by the short exact sequence `σ^{≥ a + 1} L ⟶ L ⟶ σ^{≤ a} L`.
    intro a L _ hL hc
    have h₁ : ∀ p, p < a + 1 ∨ a + 1 + k ≤ p →
        IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntGE (a + 1))).X p) := by
      rintro p (hp | hp)
      · exact CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X L (a + 1) hp
      · exact L.isZero_stupidTrunc_X_of_isZero _ (hL p (by omega))
    have h₃ : ∀ p, p ≠ a → IsZero ((L.stupidTrunc (ComplexShape.embeddingUpIntLE a)).X p) := by
      intro p hp
      rcases lt_or_gt_of_ne hp with hp | hp
      · exact L.isZero_stupidTrunc_X_of_isZero _ (hL p (by omega))
      · exact CochainComplex.isZero_stupidTrunc_embeddingUpIntLE_X L a hp
    have := hasTotal_of_isZero_X _ (a + 1) (a + k) fun p hp ↦ h₁ p (by omega)
    have := hasTotal_of_isZero_X _ a a fun p hp ↦ h₃ p (by omega)
    exact (totalShortComplex_shortExact (ComplexShape.up ℤ)
      (CochainComplex.stupidTruncShortComplex L a)
      fun p q ↦ (CochainComplex.stupidTruncShortComplexSplitting L a p).map _).acyclic_X₂
      (ih (a + 1) _ h₁ (L.acyclic_stupidTrunc_X _ hc))
      (acyclic_total_of_isZero _ a h₃ (L.acyclic_stupidTrunc_X _ hc a))

/-- The acyclic assembly lemma for finite antidiagonals and exact columns. -/
private lemma acyclic_total_of_finite_antidiagonals_of_columns
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (hfin : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((K.X p).X (n - p))}.Finite)
    (hK : ∀ p, (K.X p).Acyclic) : (K.total (ComplexShape.up ℤ)).Acyclic := by
  intro n
  -- In degree `n`, `K` is compared with its truncation to the finitely many columns `[a, b]`
  -- meeting the antidiagonals `n - 1`, `n` and `n + 1`, whose total complex is acyclic.
  have hS := (hfin (n - 1)).union ((hfin n).union (hfin (n + 1)))
  obtain ⟨a, ha⟩ := hS.bddBelow
  obtain ⟨b, hb⟩ := hS.bddAbove
  have hab (m : ℤ) (h₁ : n - 1 ≤ m) (h₂ : m ≤ n + 1) (p : ℤ) (hp : p < a ∨ b < p) :
      IsZero ((K.X p).X (m - p)) := by
    by_contra h
    have hm : p ∈ {p : ℤ | ¬ IsZero ((K.X p).X (n - 1 - p))} ∪
        ({p : ℤ | ¬ IsZero ((K.X p).X (n - p))} ∪
          {p : ℤ | ¬ IsZero ((K.X p).X (n + 1 - p))}) := by
      obtain rfl | rfl | rfl : m = n - 1 ∨ m = n ∨ m = n + 1 := by omega
      exacts [.inl h, .inr (.inl h), .inr (.inr h)]
    rcases hp with hp | hp
    exacts [absurd (ha hm) (by omega), absurd (hb hm) (by omega)]
  let K₁ : HomologicalComplex₂ C _ _ := K.stupidTrunc (ComplexShape.embeddingUpIntGE a)
  let K₂ : HomologicalComplex₂ C _ _ := K₁.stupidTrunc (ComplexShape.embeddingUpIntLE b)
  have : K₁.HasTotal (ComplexShape.up ℤ) := hasTotal_of_finite_antidiagonals K₁ fun m ↦
    (hfin m).subset fun p hp h ↦ hp (K.isZero_stupidTrunc_X_X _ h)
  have hK₂ (p : ℤ) (hp : p < a ∨ b < p) : IsZero (K₂.X p) := by
    rcases hp with hp | hp
    · exact K₁.isZero_stupidTrunc_X_of_isZero _
        (CochainComplex.isZero_stupidTrunc_embeddingUpIntGE_X K a hp)
    · exact CochainComplex.isZero_stupidTrunc_embeddingUpIntLE_X K₁ b hp
  have : K₂.HasTotal (ComplexShape.up ℤ) := hasTotal_of_isZero_X K₂ a b hK₂
  have hι (m : ℤ) (h₁ : n - 1 ≤ m) (h₂ : m ≤ n + 1) :=
    isIso_total_map_ιStupidTrunc_f K a m fun p hp ↦ hab m h₁ h₂ p (.inl hp)
  have hπ (m : ℤ) (h₁ : n - 1 ≤ m) (h₂ : m ≤ n + 1) :=
    isIso_total_map_πStupidTrunc_f K₁ b m fun p hp ↦
      K.isZero_stupidTrunc_X_X _ (hab m h₁ h₂ p (.inr hp))
  have := hι (n - 1) le_rfl (by omega)
  have := hι n (by omega) (by omega)
  have := hι (n + 1) (by omega) le_rfl
  have := hπ (n - 1) le_rfl (by omega)
  have := hπ n (by omega) (by omega)
  have := hπ (n + 1) (by omega) le_rfl
  rw [← HomologicalComplex.exactAt_iff_of_isIso_f
    (total.map (K.ιStupidTrunc (ComplexShape.embeddingUpIntGE a)) _) (n - 1) n (n + 1) (by simp)
    (by simp), HomologicalComplex.exactAt_iff_of_isIso_f
    (total.map (K₁.πStupidTrunc (ComplexShape.embeddingUpIntLE b)) _) (n - 1) n (n + 1) (by simp)
    (by simp)]
  exact acyclic_total_of_isZero_X (b + 1 - a).toNat a K₂ (fun p hp ↦ hK₂ p (by omega))
    (K₁.acyclic_stupidTrunc_X _ (K.acyclic_stupidTrunc_X _ hK)) n

/-- **The acyclic assembly lemma for finite antidiagonals.** In an abelian category, let `K` be a
double complex indexed by `ℤ × ℤ` such that each antidiagonal `p + q = n` has only finitely many
nonzero terms `(K.X p).X q`. If all columns `K.X p`, or all rows `K.flip.X q`, are exact, then the
total complex of `K` is acyclic. -/
theorem acyclic_total_of_finite_antidiagonals
    (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (hfin : ∀ n : ℤ, {p : ℤ | ¬ IsZero ((K.X p).X (n - p))}.Finite)
    (hexact : (∀ p, (K.X p).Acyclic) ∨ (∀ q, (K.flip.X q).Acyclic)) :
    (K.total (ComplexShape.up ℤ)).Acyclic := by
  rcases hexact with h | h
  · exact acyclic_total_of_finite_antidiagonals_of_columns K hfin h
  · -- The rows of `K` are the columns of `K.flip`, whose antidiagonals are those of `K` reversed.
    have hflip := acyclic_total_of_finite_antidiagonals_of_columns K.flip
      (fun n ↦ ((hfin n).image (n - ·)).subset fun q hq ↦ ⟨n - q, by simpa using hq, by simp⟩) h
    exact fun n ↦ (hflip n).of_iso (K.totalFlipIso (ComplexShape.up ℤ))

end Abelian

end HomologicalComplex₂
