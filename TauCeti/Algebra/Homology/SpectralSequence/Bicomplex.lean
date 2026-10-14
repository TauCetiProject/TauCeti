/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Sequence
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Convergence
public import TauCeti.Algebra.Homology.TotalComplex

/-!
# The spectral sequence of a first-quadrant bicomplex filtered by rows

Let `K` be a first-quadrant bicomplex, with homological differentials, in an abelian category.
Its row `q` is the complex `⋯ ⟶ (K.X 1).X q ⟶ (K.X 0).X q` formed by the horizontal
differentials. The vertical differentials lower the row index, so the rows `< q` span a subcomplex
of the total complex, and these subcomplexes form an increasing filtration
(`HomologicalComplex₂.rowFiltration`) whose graded pieces are the rows. This file constructs the
spectral sequence of that filtration (`HomologicalComplex₂.rowFiltrationSpectralSequence`): its
first page is the homology of the rows, and it converges to the homology of the total complex.
Applied to the flipped bicomplex `K.flip`, whose rows are the columns `K.X p` of `K`, it gives a
spectral sequence whose first page is the vertical homology of `K` and which converges to the
homology of the total complex of `K.flip`.

The quotient of the total complex by the rows `< s` is built by induction on `s`: it is the total
complex of the rows `≥ s` (`HomologicalComplex₂.totalRowsGE`), obtained by dropping the row `0` of
the bicomplex `HomologicalComplex₂.rowsSucc K` of the rows `≥ 1` of `K` and placing the result one
degree higher. The degreewise split short exact sequences `row s ⟶ Tot (rows ≥ s) ⟶
Tot (rows ≥ s + 1)` (`HomologicalComplex₂.totalRowShortComplex_shortExact`) come from
`HomologicalComplex₂.rowZeroShortComplex_shortExact`, and identify the graded pieces of the
filtration with the rows (`HomologicalComplex₂.rowFiltrationGradedIso`).

## Indexing

The spectral sequences of filtered complexes in `TauCeti.Algebra.Homology.SpectralSequence.Filtered`
are those of cochain complexes indexed by `ℤ`, with Mathlib's numbering `coreE₂Cohomological`, in
which the first page is numbered `2`. The total complex is therefore regarded as a cochain complex,
the chain degree `n` being placed in degree `-n`. The object at `(p, q)` on the first page is then
the homology of the row `q` in degree `k`, where `p + 2q + k = 0`
(`HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso`), and it vanishes outside this
range. The abutment in degree `-n` is the homology of the total complex in degree `n`
(`HomologicalComplex₂.rowFiltrationAbutmentIso`). The filtration is finite in each degree, so each
object stabilizes after finitely many pages to the corresponding graded piece of the abutment
(`HomologicalComplex₂.rowFiltrationSpectralSequencePageXIsoEInfty`).

## Main definitions and results

* `HomologicalComplex₂.rowFiltration`: the filtration of the total complex by rows.
* `HomologicalComplex₂.ιTotalRowsGE`: the summand inclusions of the total complex of the rows
  `≥ s`, which describe the projection `HomologicalComplex₂.toTotalRowsGE` onto it.
* `HomologicalComplex₂.rowFiltrationGradedIso`: the graded pieces of the row filtration are the
  rows.
* `HomologicalComplex₂.rowFiltrationSpectralSequence`: its spectral sequence.
* `HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso`: the first page is the homology
  of the rows.
* `HomologicalComplex₂.isZero_rowFiltrationSpectralSequence_page_two_X_of_pos`,
  `HomologicalComplex₂.isZero_rowFiltrationSpectralSequence_page_two_X_of_neg`: the first page
  vanishes outside the range of the rows.
* `HomologicalComplex₂.rowFiltrationAbutmentIso`,
  `HomologicalComplex₂.rowFiltrationSpectralSequencePageXIsoEInfty`,
  `HomologicalComplex₂.isZero_rowFiltration_abutmentFiltration`,
  `HomologicalComplex₂.isIso_rowFiltration_abutmentFiltrationι`: convergence to the homology of the
  total complex.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 5.6.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Theorem 2.15.
-/

public section

noncomputable section

open CategoryTheory Limits ComplexShape

namespace HomologicalComplex₂

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasFiniteCoproducts C] [HasZeroObject C]

/-- The total complex of the rows `≥ s` of `K`, placed in the degrees they occupy in the total
complex of `K`. It is the quotient of the total complex of `K` by its rows `< s`. It is an
abbreviation so that, for `s + 1`, it is reducibly the extension of the total complex of the rows
`≥ s` of `K.rowsSucc`, which lets `simp` compose the maps into it. -/
abbrev totalRowsGE (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) : ℕ → ChainComplex C ℕ
  | 0 => K.total (down ℕ)
  | s + 1 => (totalRowsGE K.rowsSucc s).extend embeddingDownNatSucc

/-- The projection of the total complex of `K` onto the total complex of its rows `≥ s`. -/
def toTotalRowsGE (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) :
    (s : ℕ) → K.total (down ℕ) ⟶ K.totalRowsGE s
  | 0 => 𝟙 _
  | s + 1 => K.dropRowZero ≫
      HomologicalComplex.extendMap (toTotalRowsGE K.rowsSucc s) embeddingDownNatSucc

/-- The projection of the total complex of the rows `≥ s` onto that of the rows `≥ s + 1`. -/
def totalRowsGEMap (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) :
    (s : ℕ) → K.totalRowsGE s ⟶ K.totalRowsGE (s + 1)
  | 0 => K.dropRowZero
  | s + 1 => HomologicalComplex.extendMap (totalRowsGEMap K.rowsSucc s) embeddingDownNatSucc

/-- The row `s` of `K`, placed in the degrees it occupies in the total complex of `K`: its term
in degree `p + s` is `(K.X p).X s`. It is an abbreviation for the same reason as
`HomologicalComplex₂.totalRowsGE`. -/
abbrev totalRow (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) : ℕ → ChainComplex C ℕ
  | 0 => ((HomologicalComplex.eval C (down ℕ) 0).mapHomologicalComplex (down ℕ)).obj K
  | s + 1 => (totalRow K.rowsSucc s).extend embeddingDownNatSucc

/-- The inclusion of the row `s` into the total complex of the rows `≥ s`, as its bottom row. -/
def totalRowι (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) :
    (s : ℕ) → K.totalRow s ⟶ K.totalRowsGE s
  | 0 => K.rowZeroι
  | s + 1 => HomologicalComplex.extendMap (totalRowι K.rowsSucc s) embeddingDownNatSucc

/-- The term of the row `s` placed in the degrees of the total complex, in degree `p + s`, is
`(K.X p).X s`. -/
def totalRowXIso (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) :
    (s p : ℕ) → (K.totalRow s).X (p + s) ≅ (K.X p).X s
  | 0, _ => Iso.refl _
  | s + 1, p =>
    -- The term `(K.rowsSucc.X p).X s` is `(K.X p).X (s + 1)` by definition.
    (K.rowsSucc.totalRow s).extendXIso embeddingDownNatSucc (i := p + s) rfl ≪≫
      totalRowXIso K.rowsSucc s p

/-- The inclusion of the summand `(K.X p).X q`, for `s ≤ q`, into the total complex of the rows
`≥ s` in degree `n = p + q`. -/
def ιTotalRowsGE (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) :
    (s p q n : ℕ) → s ≤ q → p + q = n → ((K.X p).X q ⟶ (K.totalRowsGE s).X n)
  | 0, p, q, n, _, h => K.ιTotal (down ℕ) p q n h
  | s + 1, p, q + 1, n + 1, _, h =>
    -- The summand `(K.rowsSucc.X p).X q` is `(K.X p).X (q + 1)` by definition.
    K.rowsSucc.ιTotalRowsGE s p q n (by omega) (by omega) ≫
      ((K.rowsSucc.totalRowsGE s).extendXIso embeddingDownNatSucc (i := n) rfl).inv
  | _ + 1, _, 0, _, hs, _ => absurd hs (by omega)
  | _ + 1, _, _ + 1, 0, _, h => absurd h (by omega)

variable (K : HomologicalComplex₂ C (down ℕ) (down ℕ))

/-- The projection onto the total complex of the rows `≥ 0` is the identity. -/
@[simp]
lemma toTotalRowsGE_zero : K.toTotalRowsGE 0 = 𝟙 _ := (rfl)

/-- The projection onto the total complex of the rows `≥ s` is the identity on the summands of the
rows `≥ s`. -/
@[reassoc (attr := simp)]
lemma ιTotal_toTotalRowsGE_f (s p q n : ℕ) (hs : s ≤ q) (h : p + q = n) :
    K.ιTotal (down ℕ) p q n h ≫ (K.toTotalRowsGE s).f n = K.ιTotalRowsGE s p q n hs h := by
  induction s generalizing K q n with
  | zero => simp [ιTotalRowsGE]
  | succ s ih =>
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp [toTotalRowsGE, ιTotalRowsGE,
      HomologicalComplex.extendMap_f _ embeddingDownNatSucc (embeddingDownNatSucc_f n),
      reassoc_of% (ih K.rowsSucc q n (by omega) (by omega))]

/-- The projection onto the total complex of the rows `≥ s` vanishes on the rows `< s`. -/
@[reassoc (attr := simp)]
lemma ιTotal_toTotalRowsGE_f_of_lt (s p q n : ℕ) (hq : q < s) (h : p + q = n) :
    K.ιTotal (down ℕ) p q n h ≫ (K.toTotalRowsGE s).f n = 0 := by
  induction s generalizing K q n with
  | zero => omega
  | succ s ih =>
    rcases q with _ | q
    · simp [toTotalRowsGE]
    · obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      simp [toTotalRowsGE,
        HomologicalComplex.extendMap_f _ embeddingDownNatSucc (embeddingDownNatSucc_f n),
        reassoc_of% (ih K.rowsSucc q n (by omega) (by omega))]

/-- The inclusion of the row `s` into the total complex of the rows `≥ s` is the inclusion of the
summands `(K.X p).X s`. -/
@[reassoc (attr := simp)]
lemma totalRowXIso_inv_totalRowι_f (s p : ℕ) :
    (K.totalRowXIso s p).inv ≫ (K.totalRowι s).f (p + s) =
      K.ιTotalRowsGE s p s (p + s) le_rfl rfl := by
  induction s generalizing K with
  | zero => simp [totalRowXIso, totalRowι, ιTotalRowsGE]
  | succ s ih =>
    simp [totalRowXIso, totalRowι, ιTotalRowsGE,
      HomologicalComplex.extendMap_f _ embeddingDownNatSucc (i := p + s) (i' := p + (s + 1)) rfl,
      reassoc_of% (ih K.rowsSucc)]

/-- The projections onto the total complexes of the rows `≥ s` and `≥ s + 1` are compatible. -/
@[reassoc (attr := simp)]
lemma toTotalRowsGE_comp_totalRowsGEMap (s : ℕ) :
    K.toTotalRowsGE s ≫ K.totalRowsGEMap s = K.toTotalRowsGE (s + 1) := by
  induction s generalizing K with
  | zero => simp [toTotalRowsGE, totalRowsGEMap]
  | succ s ih =>
    simp [toTotalRowsGE, totalRowsGEMap, ← HomologicalComplex.extendMap_comp, ih]

/-- The projection of the total complex of the rows `≥ s` onto that of the rows `≥ s + 1` is the
identity on the summands of the rows `≥ s + 1`. -/
@[reassoc (attr := simp)]
lemma ιTotalRowsGE_totalRowsGEMap_f (s p q n : ℕ) (hs : s + 1 ≤ q) (h : p + q = n) :
    K.ιTotalRowsGE s p q n (by omega) h ≫ (K.totalRowsGEMap s).f n =
      K.ιTotalRowsGE (s + 1) p q n hs h := by
  simp only [← K.ιTotal_toTotalRowsGE_f, Category.assoc, ← HomologicalComplex.comp_f,
    toTotalRowsGE_comp_totalRowsGEMap]

/-- The projection of the total complex of the rows `≥ s` onto that of the rows `≥ s + 1` vanishes
on the summands of the row `s`. -/
@[reassoc (attr := simp)]
lemma ιTotalRowsGE_self_totalRowsGEMap_f (s p n : ℕ) (h : p + s = n) :
    K.ιTotalRowsGE s p s n le_rfl h ≫ (K.totalRowsGEMap s).f n = 0 := by
  simp only [← K.ιTotal_toTotalRowsGE_f, Category.assoc, ← HomologicalComplex.comp_f,
    toTotalRowsGE_comp_totalRowsGEMap, K.ιTotal_toTotalRowsGE_f_of_lt (s + 1) p s n (by omega)]

/-- The row `s` is killed by the projection onto the total complex of the rows `≥ s + 1`. -/
@[reassoc (attr := simp)]
lemma totalRowι_comp_totalRowsGEMap (s : ℕ) :
    K.totalRowι s ≫ K.totalRowsGEMap s = 0 := by
  induction s generalizing K with
  | zero => exact K.rowZeroι_dropRowZero
  | succ s ih => simp [totalRowι, totalRowsGEMap, ← HomologicalComplex.extendMap_comp, ih]

/-- The total complex of the rows `≥ s` vanishes below degree `s`. -/
lemma isZero_totalRowsGE_X (s n : ℕ) (hn : n < s) : IsZero ((K.totalRowsGE s).X n) := by
  induction s generalizing K n with
  | zero => omega
  | succ s ih =>
    rcases n with _ | n
    · exact (K.rowsSucc.totalRowsGE s).isZero_extend_X embeddingDownNatSucc 0 (fun _ ↦ by simp)
    · exact (ih K.rowsSucc n (by omega)).of_iso
        ((K.rowsSucc.totalRowsGE s).extendXIso embeddingDownNatSucc rfl)

/-- The short complex `row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)`. -/
abbrev totalRowShortComplex (s : ℕ) : ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (K.totalRowι s) (K.totalRowsGEMap s) (K.totalRowι_comp_totalRowsGEMap s)

end Preadditive

section Abelian

variable {C : Type*} [Category* C] [Abelian C] (K : HomologicalComplex₂ C (down ℕ) (down ℕ))

/-- The short complex `row s ⟶ Tot (rows ≥ s) ⟶ Tot (rows ≥ s + 1)` is short exact; it is split
in each degree. -/
lemma totalRowShortComplex_shortExact (s : ℕ) : (K.totalRowShortComplex s).ShortExact := by
  induction s generalizing K with
  | zero => exact K.rowZeroShortComplex_shortExact
  | succ s ih => exact (ih K.rowsSucc).extend embeddingDownNatSucc

/-- The total complex of the rows `≥ s` is a quotient of the total complex. -/
instance epi_toTotalRowsGE (s : ℕ) : Epi (K.toTotalRowsGE s) := by
  induction s with
  | zero => rw [toTotalRowsGE_zero]; infer_instance
  | succ s ih =>
    have := (K.totalRowShortComplex_shortExact s).epi_g
    rw [← toTotalRowsGE_comp_totalRowsGEMap]
    infer_instance

/-- The homology of the row `s` placed in the degrees of the total complex: in degree `k + s` it
is the homology of the row `s` in degree `k`. -/
def totalRowHomologyIso (K : HomologicalComplex₂ C (down ℕ) (down ℕ)) : (s k : ℕ) →
    (K.totalRow s).homology (k + s) ≅
      (((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex (down ℕ)).obj K).homology k
  | 0, _ => Iso.refl _
  | s + 1, k =>
    -- The row `s` of `K.rowsSucc` is the row `s + 1` of `K` by definition.
    (K.rowsSucc.totalRow s).extendHomologyIso embeddingDownNatSucc (j := k + s) rfl ≪≫
      totalRowHomologyIso K.rowsSucc s k

/-- The row `s` placed in the degrees of the total complex has no homology below degree `s`. -/
lemma isZero_totalRow_homology (s n : ℕ) (hn : n < s) : IsZero ((K.totalRow s).homology n) := by
  induction s generalizing K n with
  | zero => omega
  | succ s ih =>
    rcases n with _ | n
    · exact ((K.rowsSucc.totalRow s).extend_exactAt embeddingDownNatSucc 0
        (fun _ ↦ by simp)).isZero_homology
    · exact (ih K.rowsSucc n (by omega)).of_iso
        ((K.rowsSucc.totalRow s).extendHomologyIso embeddingDownNatSucc (j := n) rfl)

/-! ### The row filtration of the total complex -/

/-- The filtration of the total complex of `K` by its rows `< q`, a subcomplex since the vertical
differentials lower the row index. The total complex is regarded as a cochain complex indexed by
`ℤ`, the chain degree `n` being placed in degree `-n`, as the spectral sequences of filtered
complexes are cohomological. -/
def rowFiltration (q : ℤ) : Subobject ((K.total (down ℕ)).extend embeddingDownNat) :=
  kernelSubobject (HomologicalComplex.extendMap (K.toTotalRowsGE q.toNat) embeddingDownNat)

/-- The rows `< s` form the kernel of the projection onto the total complex of the rows `≥ s`. -/
lemma rowFiltration_natCast (s : ℕ) :
    K.rowFiltration s =
      kernelSubobject (HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat) := by
  simp [rowFiltration]

/-- The rows `< s + 1` form the kernel of the projection onto the total complex of the rows
`≥ s + 1`, which factors through that onto the rows `≥ s`. -/
lemma rowFiltration_natCast_add_one (s : ℕ) :
    K.rowFiltration (s + 1) =
      kernelSubobject (HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat ≫
        HomologicalComplex.extendMap (K.totalRowsGEMap s) embeddingDownNat) := by
  rw [← HomologicalComplex.extendMap_comp, toTotalRowsGE_comp_totalRowsGEMap,
    ← rowFiltration_natCast]
  simp

/-- The row filtration is increasing. -/
lemma monotone_rowFiltration : Monotone K.rowFiltration := by
  have : Monotone fun s : ℕ ↦
      kernelSubobject (HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat) :=
    monotone_nat_of_le_succ fun s ↦ (kernelSubobject_comp_le _
      (HomologicalComplex.extendMap (K.totalRowsGEMap s) embeddingDownNat)).trans_eq (by
        rw [← HomologicalComplex.extendMap_comp, toTotalRowsGE_comp_totalRowsGEMap])
  exact this.comp fun _ _ h ↦ Int.toNat_le_toNat h

/-- The row filtration at `q` only depends on `q.toNat`. -/
lemma rowFiltration_toNat (q : ℤ) : K.rowFiltration q = K.rowFiltration q.toNat := by
  simp [rowFiltration]

/-- The kernel of the projection of the total complex of the rows `≥ s` onto that of the rows
`≥ s + 1` is the row `s`, placed in the degrees it occupies in the total complex. -/
def kernelTotalRowsGEMapIso (s : ℕ) :
    kernel (HomologicalComplex.extendMap (K.totalRowsGEMap s) embeddingDownNat) ≅
      (K.totalRow s).extend embeddingDownNat :=
  (kernelIsKernel _).conePointUniqueUpToIso
    ((K.totalRowShortComplex_shortExact s).extend embeddingDownNat).fIsKernel

/-- The isomorphism `HomologicalComplex₂.kernelTotalRowsGEMapIso` is compatible with the inclusion
of the row `s`. -/
@[reassoc (attr := simp)]
lemma kernelTotalRowsGEMapIso_hom_totalRowι (s : ℕ) :
    (K.kernelTotalRowsGEMapIso s).hom ≫
      HomologicalComplex.extendMap (K.totalRowι s) embeddingDownNat = kernel.ι _ :=
  (kernelIsKernel _).conePointUniqueUpToIso_hom_comp _ WalkingParallelPair.zero

/-- The quotient of the rows `< s + 1` by the rows `< s` of the total complex of `K` is the row
`s`, placed in the degrees it occupies in the total complex
(`HomologicalComplex₂.π_rowFiltrationGradedIso_hom_totalRowι`). -/
def rowFiltrationGradedIso (s : ℕ) :
    cokernel ((CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration).map
      (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : (s : ℤ) = s) rfl))) ≅
      (K.totalRow s).extend embeddingDownNat :=
  CochainComplex.cokernelFiltrationFunctorMapIso _ _ _ ≪≫
    TauCeti.cokernelOfLEKernelSubobjectIso
      (HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat)
      (HomologicalComplex.extendMap (K.totalRowsGEMap s) embeddingDownNat)
      (by rw [CochainComplex.filtrationEInt_coe, rowFiltration_natCast])
      (by rw [CochainComplex.filtrationEInt_coe, rowFiltration_natCast_add_one]) _ ≪≫
    K.kernelTotalRowsGEMapIso s

/-- The identification `HomologicalComplex₂.rowFiltrationGradedIso` of the graded piece with the
row `s` is induced by the projection of the rows `< s + 1` onto the total complex of the rows
`≥ s`. -/
@[reassoc (attr := simp)]
lemma π_rowFiltrationGradedIso_hom_totalRowι (s : ℕ) :
    cokernel.π _ ≫ (K.rowFiltrationGradedIso s).hom ≫
      HomologicalComplex.extendMap (K.totalRowι s) embeddingDownNat =
    (CochainComplex.filtrationFunctorObjIso K.rowFiltration K.monotone_rowFiltration
        ((s + 1 : ℤ) : EInt)).hom ≫
      (CochainComplex.filtrationEInt K.rowFiltration ((s + 1 : ℤ) : EInt)).arrow ≫
      HomologicalComplex.extendMap (K.toTotalRowsGE s) embeddingDownNat := by
  simp [rowFiltrationGradedIso]

/-- The row filtration is trivial in the rows `≤ 0`. -/
lemma rowFiltration_eq_bot (q : ℤ) (hq : q ≤ 0) : K.rowFiltration q = ⊥ := by
  rw [rowFiltration_toNat, show q.toNat = 0 by omega, rowFiltration_natCast, toTotalRowsGE_zero,
    HomologicalComplex.extendMap_id]
  exact Subobject.mk_eq_bot_iff_zero.2 (kernel.ι_of_mono _)

/-- The summand `(K.X p).X q` of the total complex in degree `n`, placed in degree `-n`, lies in
the rows `< b` when `q < b`. -/
lemma exists_lift_ιTotal_rowFiltration (b : ℤ) (p q n : ℕ) (hq : (q : ℤ) < b) (h : p + q = n) :
    ∃ g : (K.X p).X q ⟶ (K.rowFiltration b : CochainComplex C ℤ).X (-n),
      g ≫ (K.rowFiltration b).arrow.f (-n) = K.ιTotal (down ℕ) p q n h ≫
        ((K.total (down ℕ)).extendXIso embeddingDownNat (by simp)).inv := by
  let a := HomologicalComplex.extendMap (K.toTotalRowsGE b.toNat) embeddingDownNat
  rw [show K.rowFiltration b = kernelSubobject a by rw [rowFiltration_toNat, rowFiltration_natCast]]
  -- Kernels of complexes are computed degreewise.
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift'
    (KernelFork.mapIsLimit _ (kernelIsKernel a) (HomologicalComplex.eval C (up ℤ) (-n)))
    (K.ιTotal (down ℕ) p q n h ≫ ((K.total (down ℕ)).extendXIso embeddingDownNat (by simp)).inv)
    (by simp [a, HomologicalComplex.extendMap_f _ embeddingDownNat (i := n) (i' := -n) (by simp),
      K.ιTotal_toTotalRowsGE_f_of_lt_assoc b.toNat p q n (by omega) h])
  refine ⟨l ≫ (kernelSubobjectIso a).inv.f (-n), ?_⟩
  simpa [← HomologicalComplex.comp_f] using hl

/-- The quotient of the total complex of `K` by its rows `< b` has no cohomology in degrees
`> -b`: it is the total complex of the rows `≥ b`, which lives in the chain degrees `≥ b`. -/
lemma isZero_homology_cokernel_rowFiltration_arrow (b m : ℤ) (hm : -b < m) :
    IsZero ((cokernel (K.rowFiltration b).arrow).homology m) := by
  have hX : IsZero (((K.totalRowsGE b.toNat).extend embeddingDownNat).X m) := by
    by_cases hm' : 0 < m
    · exact (K.totalRowsGE b.toNat).isZero_extend_X embeddingDownNat m
        (fun n hn ↦ by simp at hn; omega)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -n := ⟨(-m).toNat, by omega⟩
      exact (K.isZero_totalRowsGE_X b.toNat n (by omega)).of_iso
        ((K.totalRowsGE b.toNat).extendXIso embeddingDownNat (by simp))
  exact ((HomologicalComplex.homologyFunctor C (up ℤ) m).mapIso
    (TauCeti.cokernelKernelSubobjectArrowIso _
      (by rw [rowFiltration_toNat, rowFiltration_natCast]))).symm.isZero_iff.1
    (ShortComplex.isZero_homology_of_isZero_X₂ _ hX)

/-! ### The spectral sequence -/

/-- The spectral sequence of the filtration of the total complex of `K` by its rows. It uses
Mathlib's cohomological indexing, in which the first page is numbered `2`: its object at `(p, q)`
is `H_k` of the row `q` with `p = -(k + 2q)`
(`HomologicalComplex₂.rowFiltrationSpectralSequenceFirstPageXIso`). -/
abbrev rowFiltrationSpectralSequence :=
  CochainComplex.spectralSequence
    (CochainComplex.filtrationFunctor K.rowFiltration K.monotone_rowFiltration)

/-- The object at `(p, s)` on the first page (numbered `2`) of the spectral sequence of the row
filtration is the cohomology in degree `p + s` of the row `s`, placed in the degrees it occupies
in the total complex. -/
def rowFiltrationSpectralSequenceFirstPageXIsoTotalRow (p : ℤ) (s : ℕ) :
    (K.rowFiltrationSpectralSequence.page 2).X (p, s) ≅
      ((K.totalRow s).extend embeddingDownNat).homology (p + s) :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ (p, s) s (s + 1) rfl rfl (p + s) rfl ≪≫
    (HomologicalComplex.homologyFunctor C (up ℤ) (p + s)).mapIso (K.rowFiltrationGradedIso s)

/-- **The first page of the spectral sequence of the row filtration** is the homology of the rows:
its object at `(p, s)`, with `p + 2s + k = 0`, is the homology in degree `k` of the row `s`
`⋯ ⟶ (K.X 1).X s ⟶ (K.X 0).X s` of `K`, formed by the horizontal differentials. -/
def rowFiltrationSpectralSequenceFirstPageXIso (p : ℤ) (s k : ℕ) (hp : p + 2 * s + k = 0) :
    (K.rowFiltrationSpectralSequence.page 2).X (p, s) ≅
      (((HomologicalComplex.eval C (down ℕ) s).mapHomologicalComplex (down ℕ)).obj K).homology k :=
  K.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow p s ≪≫
    (K.totalRow s).extendHomologyIso embeddingDownNat (j := k + s) (by simp; omega) ≪≫
    K.totalRowHomologyIso s k

/-- The first page of the spectral sequence of the row filtration vanishes at `(p, s)` when
`p + 2s > 0`: the row `s` contributes nothing in total degree `-(p + s) < s`. -/
lemma isZero_rowFiltrationSpectralSequence_page_two_X_of_pos (p : ℤ) (s : ℕ)
    (h : 0 < p + 2 * s) : IsZero ((K.rowFiltrationSpectralSequence.page 2).X (p, s)) := by
  refine IsZero.of_iso ?_ (K.rowFiltrationSpectralSequenceFirstPageXIsoTotalRow p s)
  by_cases hps : 0 < p + s
  · exact ((K.totalRow s).extend_exactAt embeddingDownNat _
      (fun n hn ↦ by simp at hn; omega)).isZero_homology
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, p + s = -n := ⟨(-(p + s)).toNat, by omega⟩
    exact (K.isZero_totalRow_homology s n (by omega)).of_iso
      ((K.totalRow s).extendHomologyIso embeddingDownNat (by simp [hn]))

/-- The first page of the spectral sequence of the row filtration vanishes in negative rows. -/
lemma isZero_rowFiltrationSpectralSequence_page_two_X_of_neg (p q : ℤ) (hq : q < 0) :
    IsZero ((K.rowFiltrationSpectralSequence.page 2).X (p, q)) := by
  refine ((HomologicalComplex.homologyFunctor C (up ℤ) (p + q)).map_isZero
    ((IsZero.of_epi (cokernel.π _) ?_).of_iso
      (CochainComplex.cokernelFiltrationFunctorMapIso _ _ _))).of_iso
    (CochainComplex.spectralSequenceFirstPageXIsoCokernel _ (p, q) q (q + 1) rfl rfl (p + q) rfl)
  rw [CochainComplex.filtrationEInt_coe, K.rowFiltration_eq_bot _ (by omega)]
  exact IsZero.of_iso (isZero_zero _) Subobject.botCoeIsoZero

/-- The abutment of the spectral sequence of the row filtration in degree `-n` is the homology of
the total complex of `K` in degree `n`. -/
def rowFiltrationAbutmentIso (n : ℕ) :
    (CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltration
      K.monotone_rowFiltration)).abutment (-n) ≅ (K.total (down ℕ)).homology n :=
  CochainComplex.filtrationAbutmentIso _ _ _ ≪≫
    (K.total (down ℕ)).extendHomologyIso embeddingDownNat (by simp)

/-! ### Convergence -/

/-- **Convergence of the spectral sequence of the row filtration.** On every page `r ≥ 2` with
`q + 2 ≤ r` and `p + 2q + r > 2`, the object at `(p, q)` is the limit object
`E^{p+q}(⊥ ≤ q ≤ q + 1 ≤ ⊤)`, which is the `q`th graded piece of the filtration of the abutment
(`CategoryTheory.Abelian.SpectralObject.EInftyIsoCokernel`). In particular the object at a
fixed position stabilizes after finitely many pages. -/
def rowFiltrationSpectralSequencePageXIsoEInfty (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ)
    (h₀ : pq.2 + 2 ≤ r) (h₃ : 2 < pq.1 + 2 * pq.2 + r) :
    (K.rowFiltrationSpectralSequence.page r).X pq ≅
      (CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltration
        K.monotone_rowFiltration)).EInfty pq.2 (pq.1 + pq.2) :=
  CochainComplex.filtrationSpectralSequencePageXIsoEInfty _ _ r hr pq _ rfl
    (Subobject.isZero_homology_of_eq_bot _ (K.rowFiltration_eq_bot _ (by omega)) _)
    (K.isZero_homology_cokernel_rowFiltration_arrow _ _ (by omega))

/-- The filtration of the abutment of the spectral sequence of the row filtration vanishes at
`0`. -/
lemma isZero_rowFiltration_abutmentFiltration (n : ℤ) :
    IsZero ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltration
      K.monotone_rowFiltration)).abutmentFiltration 0 n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration _ _ (K.rowFiltration_eq_bot 0 le_rfl) n

/-- The filtration of the abutment of the spectral sequence of the row filtration is exhaustive
in each degree: its `b`th piece in degree `n` is everything when `-b < n`. -/
lemma isIso_rowFiltration_abutmentFiltrationι (b n : ℤ) (h : -b < n) :
    IsIso ((CochainComplex.spectralObject (CochainComplex.filtrationFunctor K.rowFiltration
      K.monotone_rowFiltration)).abutmentFiltrationι b n) :=
  Abelian.SpectralObject.isIso_abutmentFiltrationι _
    (CochainComplex.isZero_spectralObject_H_top _ _ b n
      (K.isZero_homology_cokernel_rowFiltration_arrow b n h))

end Abelian

end HomologicalComplex₂
