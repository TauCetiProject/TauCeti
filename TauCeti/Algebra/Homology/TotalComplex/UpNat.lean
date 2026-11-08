/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import TauCeti.Algebra.Homology.ComplexShape.Signs
public import TauCeti.Algebra.Homology.Embedding.ExtendHomology.Basic
public import TauCeti.Algebra.Homology.Embedding.UpNatAdd
public import TauCeti.Algebra.Homology.HomologySequenceLemmas

/-!
# Total complexes of first-quadrant bicomplexes with cohomological differentials

A bicomplex indexed by `ℕ × ℕ` with cohomological differentials (both of shape
`ComplexShape.up ℕ`) has only finitely many terms `(K.X p).X q` with `p + q = n`, so its total
complex exists in any preadditive category with finite coproducts. Its differential is
`d₁ + (-1)ᵖ d₂` on the summand `(K.X p).X q`, by the tensor signs of `ComplexShape.up ℕ` from
`TauCeti.Algebra.Homology.ComplexShape.Signs`. This is the cohomological counterpart of
`TauCeti.Algebra.Homology.TotalComplex`, the form taken by Čech double complexes `Čᵖ(U, Kᵠ)` of
complexes of sheaves.

A coaugmentation `η : E ⟶ K.X 0` of the column `0` by a cochain complex `E`, that is a cochain map
killed by the horizontal differential `K.d 0 1`, induces a cochain map
`HomologicalComplex₂.totalCoaugmentation` from `E` to the total complex. For the bicomplex whose
only column is `E`, in degree `0`, this map is an isomorphism.

When `C` is abelian, a map of such bicomplexes which is a quasi-isomorphism on every row
`(K.X 0).X q ⟶ (K.X 1).X q ⟶ ⋯` induces a quasi-isomorphism of total complexes. Applied to a map
from the bicomplex with the single column `E`, this says that exactness of the coaugmented rows
`0 ⟶ E.X q ⟶ (K.X 0).X q ⟶ (K.X 1).X q ⟶ ⋯` makes the coaugmentation of the total complex a
quasi-isomorphism, as for the Čech complexes of the terms of an injective resolution. The proof
filters the total complex by rows: the rows `≥ 1` form a subcomplex, the total complex of the
bicomplex `HomologicalComplex₂.rowsSuccUp K` placed one degree higher, the quotient is row `0`, and
an induction on the degree compares the homology sequences of these short exact sequences.

## Main definitions and results

* `HomologicalComplex₂.hasTotal_up_nat`: first-quadrant bicomplexes have total complexes.
* `HomologicalComplex₂.totalCoaugmentation`: the cochain map to the total complex induced by a
  coaugmentation of the column `0`.
* `HomologicalComplex₂.totalCoaugmentation_total_map`: naturality of the coaugmentation under maps
  of bicomplexes.
* `HomologicalComplex₂.isIso_totalCoaugmentation_single`: the total complex of a bicomplex with a
  single column is that column.
* `HomologicalComplex₂.rowsSuccUpShortComplex`: the degreewise split short exact sequence
  `Tot (rowsSuccUp K)[-1] ⟶ Tot K ⟶ row 0`.
* `HomologicalComplex₂.quasiIso_total_map_of_rows_up`: a map of bicomplexes which is a
  quasi-isomorphism on every row induces a quasi-isomorphism of total complexes.
* `HomologicalComplex₂.quasiIso_totalCoaugmentation_of_rows`: exact coaugmented rows make the
  coaugmentation of the total complex a quasi-isomorphism.

## References

* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Section 2.7, for the acyclic assembly lemma, of which the statement on rows is the relative form.
-/

public section

noncomputable section

open CategoryTheory Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A first-quadrant bicomplex with cohomological differentials has a total complex as soon as
finite coproducts exist. -/
instance hasTotal_up_nat [HasFiniteCoproducts C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    K.HasTotal (ComplexShape.up ℕ) := fun n ↦
  have : Finite (ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (ComplexShape.up ℕ) ⁻¹' {n}) :=
    inferInstanceAs (Finite ((fun i : ℕ × ℕ ↦ i.1 + i.2) ⁻¹' {n}))
  inferInstance

variable (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
  [K.HasTotal (ComplexShape.up ℕ)] {E : CochainComplex C ℕ} (η : E ⟶ K.X 0)
  (hη : η ≫ K.d 0 1 = 0)

/-- The cochain map from a cochain complex `E` to the total complex of a first-quadrant bicomplex
`K` induced by a coaugmentation `η : E ⟶ K.X 0` of the column `0` killed by the horizontal
differential: it is `η` followed by the inclusion of the summands `(K.X 0).X q`. -/
def totalCoaugmentation : E ⟶ K.total (ComplexShape.up ℕ) where
  f n := η.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (zero_add n)
  comm' := by
    rintro n _ rfl
    rw [Category.assoc, total_d, Preadditive.comp_add, ι_D₁, ι_D₂,
      d₁_eq K _ (ComplexShape.up_mk 0 1 rfl) n (n + 1) (by simp [add_comm]),
      d₂_eq K _ 0 (ComplexShape.up_mk n (n + 1) rfl) (n + 1) (by simp)]
    -- The horizontal term vanishes as `η ≫ K.d 0 1 = 0`, and the vertical term has sign `1`.
    have h₁ : η.f n ≫ (K.d 0 1).f n = 0 := by
      rw [← HomologicalComplex.comp_f, hη, HomologicalComplex.zero_f]
    simp [reassoc_of% h₁]

@[simp]
lemma totalCoaugmentation_f (n : ℕ) :
    (K.totalCoaugmentation η hη).f n =
      η.f n ≫ K.ιTotal (ComplexShape.up ℕ) 0 n n (zero_add n) :=
  (rfl)

/-- Precomposing the coaugmentation of the total complex with a cochain map `g` gives the
coaugmentation induced by `g ≫ η`. -/
lemma comp_totalCoaugmentation {E' : CochainComplex C ℕ} (g : E' ⟶ E) :
    g ≫ K.totalCoaugmentation η hη =
      K.totalCoaugmentation (g ≫ η) (by rw [Category.assoc, hη, comp_zero]) := by
  ext n
  simp

/-- Taking total complexes commutes with pushing a coaugmentation forward along a bicomplex map. -/
@[reassoc (attr := simp)]
lemma totalCoaugmentation_total_map
    {L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    [L.HasTotal (ComplexShape.up ℕ)] (φ : K ⟶ L) :
    K.totalCoaugmentation η hη ≫ total.map φ (ComplexShape.up ℕ) =
      L.totalCoaugmentation (η ≫ φ.f 0)
        (by rw [Category.assoc, φ.comm, ← Category.assoc, hη, zero_comp]) := by
  ext n
  simp

section Single

variable [HasZeroObject C] (E : CochainComplex C ℕ)

/-- The identity of `E` is a coaugmentation of the bicomplex with the single column `E`. -/
lemma singleObjXSelf_inv_comp_single_d :
    (HomologicalComplex.singleObjXSelf _ 0 E).inv ≫
      ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E).d 0 1 = 0 := by
  rw [HomologicalComplex.single_obj_d, comp_zero]

variable [HasTotal ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E)
  (ComplexShape.up ℕ)]

/-- The components of the inverse of the coaugmentation of the single column `E`: the identity on
the column `0`, and zero on the other columns, which are zero. -/
private def singleTotalInvAux (n p q : ℕ)
    (h : ComplexShape.π (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ)
      (p, q) = n) :
    (((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E).X p).X q ⟶ E.X n :=
  match p, h with
  | 0, h => (HomologicalComplex.singleObjXSelf _ 0 E).hom.f q ≫ (E.XIsoOfEq (by simpa using h)).hom
  | _ + 1, _ => 0

/-- The total complex of the bicomplex with the single column `E` in degree `0` is `E`: its
coaugmentation by the identity of `E` is an isomorphism. -/
lemma isIso_totalCoaugmentation_single :
    IsIso (totalCoaugmentation ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E)
      (HomologicalComplex.singleObjXSelf _ 0 E).inv (singleObjXSelf_inv_comp_single_d E)) := by
  -- The inverse in degree `n` is the projection onto the summand of the column `0`.
  have (n : ℕ) : IsIso ((totalCoaugmentation _ _ (singleObjXSelf_inv_comp_single_d E)).f n) := by
    refine ⟨totalDesc _ (singleTotalInvAux E n), ?_, ?_⟩
    · rw [totalCoaugmentation_f, Category.assoc, ι_totalDesc]
      simp [singleTotalInvAux]
    · refine total.hom_ext _ fun p q h ↦ ?_
      rcases p with _ | p
      · obtain rfl : q = n := by simpa using h
        rw [ι_totalDesc_assoc, Category.comp_id]
        simp only [singleTotalInvAux, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
          Category.comp_id, totalCoaugmentation_f]
        rw [← HomologicalComplex.comp_f_assoc, Iso.hom_inv_id, HomologicalComplex.id_f,
          Category.id_comp]
      · exact ((HomologicalComplex.eval C _ q).map_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp))).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

variable {E}

omit [K.HasTotal (ComplexShape.up ℕ)]
  [HasTotal ((HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E)
    (ComplexShape.up ℕ)] in
/-- The column `0` of a map `φ` to `K` from the bicomplex with the single column `E` is a
coaugmentation of `K`: it is killed by the horizontal differential `K.d 0 1`. -/
lemma singleObjXSelf_inv_comp_f_zero_d
    (φ : (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E ⟶ K) :
    ((HomologicalComplex.singleObjXSelf _ 0 E).inv ≫ φ.f 0) ≫ K.d 0 1 = 0 := by
  rw [Category.assoc, φ.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]

end Single

end HomologicalComplex₂

/-! ### Rows and quasi-isomorphisms

Let `φ : K ⟶ L` be a map of first-quadrant bicomplexes with cohomological differentials in an
abelian category which is a quasi-isomorphism on every row. The rows `≥ 1` span a subcomplex of the
total complex: the total complex of the rows `≥ 1`, reindexed and placed one degree higher. The
quotient is row `0`. The short exact sequence `Tot K⁺[-1] ⟶ Tot K ⟶ row 0` is split in each degree
and natural in `φ`, and the reindexed bicomplex `K⁺` again satisfies the hypothesis. Comparing the
homology sequences shows, by induction on `Q`, that `Tot φ` is an isomorphism in cohomology below
`Q` and a monomorphism in degree `Q`: the monomorphism in degree `Q` on the subcomplex, that is in
degree `Q - 1` for `K⁺`, is what the five lemma needs in degree `Q - 1`. -/

namespace HomologicalComplex₂

open HomologicalComplex
open ComplexShape (embeddingUpNatAdd embeddingUpNatAdd_f)

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]

variable (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))

omit [HasFiniteCoproducts C] in
/-- The rows `≥ 1` of `K`, reindexed so that row `q + 1` of `K` is row `q`. The summands are
`(K.X p).X (q + 1)` up to reducible unfolding, which lets rewriting identify them with those of
`K`. -/
abbrev rowsSuccUp : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ) where
  X p :=
    { X q := (K.X p).X (q + 1)
      d q q' := (K.X p).d (q + 1) (q' + 1)
      shape q q' h := (K.X p).shape _ _ (by simp at h ⊢; omega) }
  d p p' := { f q := (K.d p p').f (q + 1) }
  shape p p' h := by ext q; exact HomologicalComplex.congr_hom (K.shape _ _ h) (q + 1)
  d_comp_d' p p' p'' _ _ := by
    ext q; exact HomologicalComplex.congr_hom (K.d_comp_d p p' p'') (q + 1)

/-- The inclusion of the total complex of the rows `≥ 1` in degree `n` into the total complex in
degree `n + 1`. -/
private def rowsSuccUpιX (n : ℕ) :
    ((rowsSuccUp K).total (ComplexShape.up ℕ)).X n ⟶ (K.total (ComplexShape.up ℕ)).X (n + 1) :=
  (rowsSuccUp K).totalDesc fun p q h ↦ K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1)
    (by simp at h ⊢; omega)

@[reassoc (attr := simp)]
private lemma ιTotal_rowsSuccUpιX (p q n : ℕ) (h) :
    (rowsSuccUp K).ιTotal (ComplexShape.up ℕ) p q n h ≫ rowsSuccUpιX K n =
      K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) (by simp at h ⊢; omega) := by
  simp [rowsSuccUpιX]

private lemma ιTotalOrZero_rowsSuccUpιX (p q n : ℕ) :
    (rowsSuccUp K).ιTotalOrZero (ComplexShape.up ℕ) p q n ≫ rowsSuccUpιX K n =
      K.ιTotalOrZero (ComplexShape.up ℕ) p (q + 1) (n + 1) := by
  by_cases h : p + q = n
  · rw [ιTotalOrZero_eq _ _ _ _ _ (by simpa using h), ιTotal_rowsSuccUpιX,
      K.ιTotalOrZero_eq _ _ _ _ (by simp; omega)]
  · rw [ιTotalOrZero_eq_zero _ _ _ _ _ (by simpa using h), zero_comp,
      K.ιTotalOrZero_eq_zero _ _ _ _ (by simp; omega)]

private lemma d₁_rowsSuccUpιX (p q n : ℕ) :
    (rowsSuccUp K).d₁ (ComplexShape.up ℕ) p q (n + 1) ≫ rowsSuccUpιX K (n + 1) =
      K.d₁ (ComplexShape.up ℕ) p (q + 1) (n + 1 + 1) := by
  rw [d₁_eq' _ _ (ComplexShape.up_mk p (p + 1) rfl),
    d₁_eq' K _ (ComplexShape.up_mk p (p + 1) rfl), Linear.units_smul_comp, Category.assoc,
    ιTotalOrZero_rowsSuccUpιX]
  -- Both signs `ε₁` are `1`, and the horizontal differentials of `rowsSuccUp K` are those of `K`
  -- by definition.
  rfl

private lemma d₂_rowsSuccUpιX (p q n : ℕ) :
    (rowsSuccUp K).d₂ (ComplexShape.up ℕ) p q (n + 1) ≫ rowsSuccUpιX K (n + 1) =
      K.d₂ (ComplexShape.up ℕ) p (q + 1) (n + 1 + 1) := by
  rw [d₂_eq' _ _ _ (ComplexShape.up_mk q (q + 1) rfl),
    d₂_eq' K _ _ (ComplexShape.up_mk (q + 1) (q + 2) rfl), Linear.units_smul_comp,
    Category.assoc, ιTotalOrZero_rowsSuccUpιX]
  simp

@[reassoc]
private lemma rowsSuccUpιX_comm (n : ℕ) :
    ((rowsSuccUp K).total (ComplexShape.up ℕ)).d n (n + 1) ≫ rowsSuccUpιX K (n + 1) =
      rowsSuccUpιX K n ≫ (K.total (ComplexShape.up ℕ)).d (n + 1) (n + 1 + 1) := by
  refine total.hom_ext _ fun p q h ↦ ?_
  simp only [total_d, Preadditive.add_comp, Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc,
    ιTotal_rowsSuccUpιX_assoc, ι_D₁, ι_D₂, d₁_rowsSuccUpιX, d₂_rowsSuccUpιX]

section HasZeroObject

variable [HasZeroObject C]

/-- The inclusion of the total complex of the rows `≥ 1`, placed one degree higher, into the total
complex. -/
def rowsSuccUpι :
    ((rowsSuccUp K).total (ComplexShape.up ℕ)).extend (embeddingUpNatAdd 1) ⟶
      K.total (ComplexShape.up ℕ) where
  f n := match n with
    | 0 => 0
    | n + 1 => (((rowsSuccUp K).total (ComplexShape.up ℕ)).extendXIso (embeddingUpNatAdd 1)
        (embeddingUpNatAdd_f 1 n)).hom ≫ rowsSuccUpιX K n
  comm' := by
    rintro n _ rfl
    rcases n with _ | n
    · exact (isZero_extend_X _ _ 0 fun i ↦ by simp).eq_of_src _ _
    · dsimp only
      rw [extend_d_eq _ _ (embeddingUpNatAdd_f 1 n) (embeddingUpNatAdd_f 1 (n + 1))]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, rowsSuccUpιX_comm]

/-- The inclusion of the rows `≥ 1` sends the summand `(K.X p).X (q + 1)` of the total complex of
`rowsSuccUp K` in degree `n` to the same summand of the total complex in degree `n + 1`. -/
@[reassoc (attr := simp)]
lemma ιTotal_rowsSuccUpι_f (p q n : ℕ) (h) :
    (rowsSuccUp K).ιTotal (ComplexShape.up ℕ) p q n h ≫
        (((rowsSuccUp K).total (ComplexShape.up ℕ)).extendXIso (embeddingUpNatAdd 1)
          (embeddingUpNatAdd_f 1 n)).inv ≫ (rowsSuccUpι K).f (n + 1) =
      K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) (by simp at h ⊢; omega) := by
  simp [rowsSuccUpι]

end HasZeroObject

/-- The projection of the total complex onto row `0` in degree `n`. -/
private def rowZeroUpπX (n : ℕ) : (K.total (ComplexShape.up ℕ)).X n ⟶ (K.X n).X 0 :=
  K.totalDesc fun p q h ↦ match q, h with
    | 0, h => (K.XXIsoOfEq _ _ _ (by simpa using h) rfl).hom
    | _ + 1, _ => 0

@[reassoc (attr := simp)]
private lemma ιTotal_rowZeroUpπX_zero (p n : ℕ) (h) :
    K.ιTotal (ComplexShape.up ℕ) p 0 n h ≫ rowZeroUpπX K n =
      (K.XXIsoOfEq _ _ _ (by simpa using h) rfl).hom := by
  simp [rowZeroUpπX]

@[reassoc (attr := simp)]
private lemma ιTotal_rowZeroUpπX_succ (p q n : ℕ) (h) :
    K.ιTotal (ComplexShape.up ℕ) p (q + 1) n h ≫ rowZeroUpπX K n = 0 := by
  simp [rowZeroUpπX]

private lemma ιTotalOrZero_rowZeroUpπX_succ (p q n : ℕ) :
    K.ιTotalOrZero (ComplexShape.up ℕ) p (q + 1) n ≫ rowZeroUpπX K n = 0 := by
  by_cases h : p + (q + 1) = n
  · rw [K.ιTotalOrZero_eq _ _ _ _ (by simpa using h), ιTotal_rowZeroUpπX_succ]
  · rw [K.ιTotalOrZero_eq_zero _ _ _ _ (by simpa using h), zero_comp]

/-- The projection of the total complex onto row `0`. -/
def rowZeroUpπ :
    K.total (ComplexShape.up ℕ) ⟶
      ((eval C (ComplexShape.up ℕ) 0).mapHomologicalComplex (ComplexShape.up ℕ)).obj K where
  f n := rowZeroUpπX K n
  comm' := by
    rintro n _ rfl
    refine total.hom_ext _ fun p q h ↦ ?_
    rw [total_d, Preadditive.add_comp, Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc,
      d₁_eq' K _ (ComplexShape.up_mk p (p + 1) rfl),
      d₂_eq' K _ _ (ComplexShape.up_mk q (q + 1) rfl), Linear.units_smul_comp,
      Linear.units_smul_comp, Category.assoc, Category.assoc,
      ιTotalOrZero_rowZeroUpπX_succ, comp_zero, smul_zero, add_zero]
    rcases q with _ | q
    · obtain rfl : p = n := by simpa using h
      rw [K.ιTotalOrZero_eq _ _ _ _ (by simp), ιTotal_rowZeroUpπX_zero_assoc,
        ιTotal_rowZeroUpπX_zero]
      simp
    · rw [ιTotalOrZero_rowZeroUpπX_succ, comp_zero, smul_zero, ιTotal_rowZeroUpπX_succ_assoc,
        zero_comp]

@[reassoc (attr := simp)]
lemma ιTotal_rowZeroUpπ_f_zero (p n : ℕ) (h) :
    K.ιTotal (ComplexShape.up ℕ) p 0 n h ≫ (rowZeroUpπ K).f n =
      (K.XXIsoOfEq _ _ _ (by simpa using h) rfl).hom :=
  ιTotal_rowZeroUpπX_zero K p n h

@[reassoc (attr := simp)]
lemma ιTotal_rowZeroUpπ_f_succ (p q n : ℕ) (h) :
    K.ιTotal (ComplexShape.up ℕ) p (q + 1) n h ≫ (rowZeroUpπ K).f n = 0 :=
  ιTotal_rowZeroUpπX_succ K p q n h

/-- The retraction of `rowsSuccUpιX K n`, killing row `0`. -/
private def rowsSuccUpDropX (n : ℕ) :
    (K.total (ComplexShape.up ℕ)).X (n + 1) ⟶ ((rowsSuccUp K).total (ComplexShape.up ℕ)).X n :=
  K.totalDesc fun p q h ↦ match q, h with
    | 0, _ => 0
    | q + 1, h => (rowsSuccUp K).ιTotal (ComplexShape.up ℕ) p q n (by simp at h ⊢; omega)

@[reassoc (attr := simp)]
private lemma ιTotal_rowsSuccUpDropX_zero (p n : ℕ) (h) :
    K.ιTotal (ComplexShape.up ℕ) p 0 (n + 1) h ≫ rowsSuccUpDropX K n = 0 := by
  simp [rowsSuccUpDropX]

@[reassoc (attr := simp)]
private lemma ιTotal_rowsSuccUpDropX_succ (p q n : ℕ) (h) :
    K.ιTotal (ComplexShape.up ℕ) p (q + 1) (n + 1) h ≫ rowsSuccUpDropX K n =
      (rowsSuccUp K).ιTotal (ComplexShape.up ℕ) p q n (by simp at h ⊢; omega) := by
  simp only [rowsSuccUpDropX, ι_totalDesc]

@[reassoc (attr := simp)]
private lemma rowsSuccUpιX_rowsSuccUpDropX (n : ℕ) :
    rowsSuccUpιX K n ≫ rowsSuccUpDropX K n = 𝟙 _ := by
  ext p q h
  simp

variable [HasZeroObject C]

@[reassoc (attr := simp)]
lemma rowsSuccUpι_rowZeroUpπ : rowsSuccUpι K ≫ rowZeroUpπ K = 0 := by
  ext (_ | n)
  · exact (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_src _ _
  · rw [← cancel_epi (((rowsSuccUp K).total (ComplexShape.up ℕ)).extendXIso
      (embeddingUpNatAdd 1) (embeddingUpNatAdd_f 1 n)).inv]
    refine total.hom_ext _ fun p q h ↦ ?_
    simp

/-- The short complex `Tot (rowsSuccUp K)[-1] ⟶ Tot K ⟶ row 0`. It is an abbreviation so that its
objects are reducibly those of `K`. -/
abbrev rowsSuccUpShortComplex : ShortComplex (HomologicalComplex C (ComplexShape.up ℕ)) :=
  ShortComplex.mk (rowsSuccUpι K) (rowZeroUpπ K) (rowsSuccUpι_rowZeroUpπ K)

/-- The short complex `rowsSuccUpShortComplex K` in degree `n`, as a short complex in `C`. -/
private abbrev rowsSuccUpShortComplexX (n : ℕ) : ShortComplex C :=
  ShortComplex.mk ((rowsSuccUpι K).f n) ((rowZeroUpπ K).f n)
    (by rw [← HomologicalComplex.comp_f, rowsSuccUpι_rowZeroUpπ, HomologicalComplex.zero_f])

/-- The splitting of `rowsSuccUpShortComplex K` in degree `n`: the inclusion of row `0` and, in
positive degrees, the retraction onto the rows `≥ 1`. -/
private def rowsSuccUpShortComplexXSplitting (n : ℕ) :
    (rowsSuccUpShortComplexX K n).Splitting :=
  match n with
  | 0 =>
    { r := 0
      s := K.ιTotal (ComplexShape.up ℕ) 0 0 0 rfl
      f_r := (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_src _ _
      s_g := by simp
      id := by
        refine total.hom_ext _ fun p q h ↦ ?_
        obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by simp at h; omega
        simp }
  | n + 1 =>
    { r := rowsSuccUpDropX K n ≫ (((rowsSuccUp K).total (ComplexShape.up ℕ)).extendXIso
        (embeddingUpNatAdd 1) (embeddingUpNatAdd_f 1 n)).inv
      s := K.ιTotal (ComplexShape.up ℕ) (n + 1) 0 (n + 1) rfl
      f_r := by simp [rowsSuccUpι]
      s_g := by simp
      id := by
        refine total.hom_ext _ fun p q h ↦ ?_
        rcases q with _ | q
        · obtain rfl : p = n + 1 := by simpa using h
          simp
        · simp [rowsSuccUpι] }

variable {K} {L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)} (φ : K ⟶ L)

omit [HasFiniteCoproducts C] [HasZeroObject C] in
/-- The map of the bicomplexes of rows `≥ 1` induced by `φ`. -/
private abbrev rowsSuccUpMap : rowsSuccUp K ⟶ rowsSuccUp L where
  f p := { f q := (φ.f p).f (q + 1) }

omit [HasZeroObject C] in
@[reassoc]
private lemma rowsSuccUpιX_naturality (n : ℕ) :
    rowsSuccUpιX K n ≫ (total.map φ (ComplexShape.up ℕ)).f (n + 1) =
      (total.map (rowsSuccUpMap φ) (ComplexShape.up ℕ)).f n ≫ rowsSuccUpιX L n := by
  refine total.hom_ext _ fun p q h ↦ ?_
  simp only [ιTotal_rowsSuccUpιX_assoc, ιTotal_map, ιTotal_map_assoc, ιTotal_rowsSuccUpιX]

/-- The map of short complexes induced by `φ`. -/
private def rowsSuccUpShortComplexMap :
    rowsSuccUpShortComplex K ⟶ rowsSuccUpShortComplex L where
  τ₁ := extendMap (total.map (rowsSuccUpMap φ) (ComplexShape.up ℕ)) (embeddingUpNatAdd 1)
  τ₂ := total.map φ (ComplexShape.up ℕ)
  τ₃ := ((eval C (ComplexShape.up ℕ) 0).mapHomologicalComplex _).map φ
  comm₁₂ := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
    rcases n with _ | n
    · exact (isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_src _ _
    · simp only [HomologicalComplex.comp_f, rowsSuccUpι,
        extendMap_f _ (embeddingUpNatAdd 1) (embeddingUpNatAdd_f 1 n), Category.assoc,
        Iso.inv_hom_id_assoc, rowsSuccUpιX_naturality]
  comm₂₃ := by
    ext n p q h
    rcases q with _ | q
    · obtain rfl : p = n := by simpa using h
      simp
    · simp

end Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The short complex `Tot (rowsSuccUp K)[-1] ⟶ Tot K ⟶ row 0` is short exact; it is split in each
degree. -/
lemma rowsSuccUpShortComplex_shortExact
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    (rowsSuccUpShortComplex K).ShortExact :=
  shortExact_of_degreewise_shortExact _ fun n ↦ (rowsSuccUpShortComplexXSplitting K n).shortExact

open HomologySequence in
/-- If `φ` is a quasi-isomorphism on every row, then `Tot φ` is an isomorphism in cohomology below
`Q` and a monomorphism in degree `Q`. -/
private lemma total_map_up_aux (Q : ℕ) :
    ∀ {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)} (φ : K ⟶ L),
      (∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) →
        (∀ m < Q, IsIso (homologyMap (total.map φ (ComplexShape.up ℕ)) m)) ∧
          Mono (homologyMap (total.map φ (ComplexShape.up ℕ)) Q) := by
  induction Q with
  | zero =>
    intro K L φ hφ
    have : QuasiIso (rowsSuccUpShortComplexMap φ).τ₃ := hφ 0
    refine ⟨fun m hm ↦ (Nat.not_lt_zero m hm).elim, ?_⟩
    have : IsIso (homologyMap (rowsSuccUpShortComplexMap φ).τ₁ 0) :=
      isIso_homologyMap_extendMap_of_forall_ne _ fun _ ↦ by simp
    exact mono_homologyMap_τ₂ (rowsSuccUpShortComplexMap φ) (rowsSuccUpShortComplex_shortExact K)
      (rowsSuccUpShortComplex_shortExact L) 0 (fun k hk ↦ by simp at hk) inferInstance
      inferInstance
  | succ Q ih =>
    intro K L φ hφ
    have : QuasiIso (rowsSuccUpShortComplexMap φ).τ₃ := hφ 0
    -- The rows of `rowsSuccUp K` are the rows `≥ 1` of `K`.
    obtain ⟨ih₁, ih₂⟩ := ih (rowsSuccUpMap φ) fun q ↦ hφ (q + 1)
    have hmono (m : ℕ) (hm : m ≤ Q) :
        Mono (homologyMap (total.map (rowsSuccUpMap φ) (ComplexShape.up ℕ)) m) := by
      rcases hm.lt_or_eq with hm | rfl
      · have := ih₁ m hm
        infer_instance
      · exact ih₂
    refine ⟨fun m hm ↦ ?_, ?_⟩
    · refine isIso_homologyMap_τ₂ (rowsSuccUpShortComplexMap φ)
        (rowsSuccUpShortComplex_shortExact K) (rowsSuccUpShortComplex_shortExact L) m
        (fun _ _ ↦ inferInstance) ?_ inferInstance ?_
      · rcases m with _ | m
        · exact isIso_homologyMap_extendMap_of_forall_ne _ fun _ ↦ by simp
        · have := ih₁ m (by omega)
          rw [← quasiIsoAt_iff_isIso_homologyMap] at this ⊢
          exact (quasiIsoAt_extendMap_iff _ (embeddingUpNatAdd 1) (embeddingUpNatAdd_f 1 m)).2
            this
      · rintro k rfl
        exact (mono_homologyMap_extendMap_iff _ (embeddingUpNatAdd_f 1 m)).2 (hmono m (by omega))
    · exact mono_homologyMap_τ₂ (rowsSuccUpShortComplexMap φ)
        (rowsSuccUpShortComplex_shortExact K) (rowsSuccUpShortComplex_shortExact L) (Q + 1)
        (fun _ _ ↦ inferInstance)
        ((mono_homologyMap_extendMap_iff _ (embeddingUpNatAdd_f 1 Q)).2 ih₂) inferInstance

variable {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)} (φ : K ⟶ L)

/-- **A map of first-quadrant bicomplexes with cohomological differentials which is a
quasi-isomorphism on every row induces a quasi-isomorphism of total complexes.** Here the row `q`
of a bicomplex `K` is the complex `(K.X 0).X q ⟶ (K.X 1).X q ⟶ ⋯` formed by the horizontal
differentials. -/
theorem quasiIso_total_map_of_rows_up
    (hφ : ∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) :
    QuasiIso (total.map φ (ComplexShape.up ℕ)) := by
  rw [quasiIso_iff]
  intro m
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (total_map_up_aux (m + 1) φ hφ).1 m (Nat.lt_succ_self m)

variable {E : CochainComplex C ℕ}

/-- **Exact coaugmented rows give a quasi-isomorphism to the total complex.** Let `φ` be a map
to a first-quadrant bicomplex `K` with cohomological differentials from the bicomplex with the
single column `E`, that is a coaugmentation `E ⟶ K.X 0` killed by `K.d 0 1`. If on every row `q`
the map from `E.X q` to `(K.X 0).X q ⟶ (K.X 1).X q ⟶ ⋯` is a quasi-isomorphism, equivalently the
coaugmented row `0 ⟶ E.X q ⟶ (K.X 0).X q ⟶ ⋯` is exact, then the induced coaugmentation of the
total complex is a quasi-isomorphism. -/
theorem quasiIso_totalCoaugmentation_of_rows
    (φ : (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E ⟶ K)
    (hφ : ∀ q, QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ)) :
    QuasiIso (K.totalCoaugmentation ((HomologicalComplex.singleObjXSelf _ 0 E).inv ≫ φ.f 0)
      (singleObjXSelf_inv_comp_f_zero_d K φ)) := by
  have := quasiIso_total_map_of_rows_up φ hφ
  have := isIso_totalCoaugmentation_single E
  rw [← totalCoaugmentation_total_map _ _ (singleObjXSelf_inv_comp_single_d E)]
  infer_instance

/-! ### Coaugmented rows -/

section RowCoaugmentation

variable (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) (η : E ⟶ K.X 0)
  (hη : η ≫ K.d 0 1 = 0)

/-- The coaugmentation of the row `q` induced by a coaugmentation `η : E ⟶ K.X 0` of the column
`0`: the cochain map from `E.X q`, placed in degree `0`, to the row
`(K.X 0).X q ⟶ (K.X 1).X q ⟶ ⋯`, given by the component of `η` in degree `q`. -/
def rowCoaugmentation (q : ℕ) :
    (CochainComplex.single₀ C).obj (E.X q) ⟶ ((eval C _ q).mapHomologicalComplex _).obj K :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨η.f q, by
    simpa using HomologicalComplex.congr_hom hη q⟩

@[simp]
lemma rowCoaugmentation_f_zero (q : ℕ) : (K.rowCoaugmentation η hη q).f 0 = η.f q :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- **Exact coaugmented rows give a quasi-isomorphism to the total complex.** If for every `q`
the coaugmented row `0 ⟶ E.X q ⟶ (K.X 0).X q ⟶ (K.X 1).X q ⟶ ⋯` is exact, that is
`K.rowCoaugmentation η hη q` is a quasi-isomorphism, then so is the coaugmentation
`E ⟶ Tot K`. -/
theorem quasiIso_totalCoaugmentation (h : ∀ q, QuasiIso (K.rowCoaugmentation η hη q)) :
    QuasiIso (K.totalCoaugmentation η hη) := by
  let φ : (HomologicalComplex.single _ (ComplexShape.up ℕ) 0).obj E ⟶ K :=
    HomologicalComplex.mkHomFromSingle η fun k hk ↦ by
      obtain rfl : k = 1 := by simpa using hk.symm
      exact hη
  have hφ : (HomologicalComplex.singleObjXSelf _ 0 E).inv ≫ φ.f 0 = η := by
    simp [φ, HomologicalComplex.mkHomFromSingle_f]
  have hrows (q : ℕ) : QuasiIso (((eval C _ q).mapHomologicalComplex _).map φ) := by
    -- The row `q` of the bicomplex with the single column `E` is `E.X q` placed in degree `0`.
    let e := (HomologicalComplex.singleMapHomologicalComplex (eval C (ComplexShape.up ℕ) q)
      (ComplexShape.up ℕ) 0).app E
    have he : K.rowCoaugmentation η hη q =
        e.inv ≫ ((eval C _ q).mapHomologicalComplex _).map φ := by
      refine HomologicalComplex.from_single_hom_ext ?_
      simp [e, φ, HomologicalComplex.mkHomFromSingle_f]
    have := h q
    rw [he] at this
    exact (quasiIso_iff_comp_left e.inv _).1 this
  have := quasiIso_totalCoaugmentation_of_rows φ hrows
  have he : K.totalCoaugmentation η hη = K.totalCoaugmentation
      ((HomologicalComplex.singleObjXSelf _ 0 E).inv ≫ φ.f 0)
      (singleObjXSelf_inv_comp_f_zero_d K φ) := by
    ext n
    simp only [totalCoaugmentation_f, hφ]
  rw [he]
  infer_instance

end RowCoaugmentation

end HomologicalComplex₂
